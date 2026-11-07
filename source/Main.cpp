#include "plugin.h"
#include "CTxdStore.h"
#include "CStreaming.h"
#include "CStreamingInfo.h"

#include <windows.h>
#include <cstdio>
#include <cstddef>
#include <cstdarg>
#include <cstring>
#include <cctype>
#include <unordered_map>
#include <vector>

using namespace plugin;

#ifndef PLUGIN_SGV_10EN
#error "This plugin uses GTA III 1.0 addresses. Define PLUGIN_SGV_10EN."
#endif

// ---- GTA III 1.0 addresses (from plugin-sdk plugin_III / SkyGfx) -----------
static constexpr uintptr_t ADDR_RwTextureRead = 0x5A7580;
// `call RwTextureRead` inside RwTextureStreamRead: reads every texture of a DFF
// material. Also patched by SkyGfx (RwTextureRead_generic).
static constexpr uintptr_t ADDR_TexStreamReadCall = 0x5AAE1B;
static constexpr uintptr_t ADDR_RequestModel = 0x407EA0; // CStreaming::RequestModel
static constexpr uintptr_t ADDR_RemoveModel = 0x408830; // CStreaming::RemoveModel
static constexpr uintptr_t ADDR_ConvertBuffer = 0x409740; // CStreaming::ConvertBufferToObject
static constexpr uintptr_t ADDR_LoadLine = 0x4761D0; // CFileLoader::LoadLine
static constexpr uintptr_t ADDR_LoadTxd = 0x527700; // CTxdStore::LoadTxd(int, RwStream*)
static constexpr uintptr_t ADDR_StartLoadTxd = 0x527770;
static constexpr uintptr_t ADDR_FinishLoadTxd = 0x5277E0;
static constexpr uintptr_t ADDR_TxdRemoveRef = 0x527970; // used to verify the TXD stream offset

// Stream flags in III (re3, Streaming.h): 0x01 DONT_REMOVE ... 0x08 PRIORITY.
// plugin-sdk's KEEP_IN_MEMORY (0x8) is wrong for III. RequestModelStream()
// drops queued TXDs without bits 0x07, so the parent needs DONT_REMOVE.
static constexpr int SF_DONT_REMOVE = 0x01;
static constexpr unsigned char SS_LOADED = 1; // stream load state "loaded"

// Streaming id of a TXD = STREAM_OFFSET_TXD + txd slot (5500 in III, verified at startup).
static int  g_txdStreamOffset = 5500;
static bool g_streamingOk = false;

// child txd slot -> parent txd slot
static std::unordered_map<int, int> g_parent;

// ---- log & settings --------------------------------------------------------
// Both files live next to the plugin (.asi) and share its name:
//   txdp.asi -> txdp.ini (settings, created automatically if missing),
//               txdp.log (log, only if Log=1 in the ini).
static char g_logPath[MAX_PATH] = "";
static bool g_logEnabled = false;

static void InitSettings() {
    HMODULE self = nullptr;
    GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
        reinterpret_cast<LPCSTR>(&InitSettings), &self);
    char base[MAX_PATH] = "";
    if (!self || !GetModuleFileNameA(self, base, MAX_PATH)) return;

    // cut the extension (".asi"), keeping dots in folder names
    char* dot = strrchr(base, '.');
    char* slash = strrchr(base, '\\');
    if (dot && (!slash || dot > slash)) *dot = 0;

    char iniPath[MAX_PATH];
    snprintf(iniPath, sizeof(iniPath), "%s.ini", base);
    snprintf(g_logPath, sizeof(g_logPath), "%s.log", base);

    // Create the ini with defaults if it does not exist yet (silently skipped if the
    // folder is not writable; the defaults below are used then).
    if (GetFileAttributesA(iniPath) == INVALID_FILE_ATTRIBUTES) {
        if (FILE* f = fopen(iniPath, "w")) {
            fputs("[Main]\n"
                "; 1 = write txdp.log next to the plugin (for diagnostics), 0 = no log at all\n"
                "Log=0\n", f);
            fclose(f);
        }
    }
    else if (GetPrivateProfileIntA("Main", "Log", -1, iniPath) == -1) {
        // ini exists but has no Log key (e.g. edited by hand): add it, keep the rest
        WritePrivateProfileStringA("Main", "Log", "0", iniPath);
    }

    g_logEnabled = GetPrivateProfileIntA("Main", "Log", 0, iniPath) != 0;
    if (g_logEnabled) remove(g_logPath); // fresh log on every start
}

static void Log(const char* fmt, ...) {
    if (!g_logEnabled) return;
    FILE* f = fopen(g_logPath, "a");
    if (!f) return;
    va_list va; va_start(va, fmt);
    vfprintf(f, fmt, va);
    va_end(va);
    fputc('\n', f);
    fclose(f);
}

// ---- helpers ---------------------------------------------------------------

// Finds every `call rel32` in the exe's code sections that targets `target`.
static std::vector<uintptr_t> FindCallsTo(uintptr_t target) {
    std::vector<uintptr_t> out;
    auto base = reinterpret_cast<uint8_t*>(GetModuleHandleA(nullptr));
    auto dos = reinterpret_cast<IMAGE_DOS_HEADER*>(base);
    auto nt = reinterpret_cast<IMAGE_NT_HEADERS*>(base + dos->e_lfanew);
    auto sec = IMAGE_FIRST_SECTION(nt);
    for (unsigned i = 0; i < nt->FileHeader.NumberOfSections; ++i, ++sec) {
        if (!(sec->Characteristics & IMAGE_SCN_CNT_CODE)) continue;
        uint8_t* p = base + sec->VirtualAddress;
        uint8_t* end = p + sec->Misc.VirtualSize - 5;
        for (; p < end; ++p) {
            if (*p != 0xE8) continue;
            int32_t rel = *reinterpret_cast<int32_t*>(p + 1);
            if (reinterpret_cast<uintptr_t>(p) + 5 + rel == target)
                out.push_back(reinterpret_cast<uintptr_t>(p));
        }
    }
    return out;
}

static int HookAllCalls(uintptr_t target, void* hook, const char* name) {
    auto sites = FindCallsTo(target);
    for (auto a : sites) patch::RedirectCall(a, hook);
    Log("%s: redirected %zu call site(s)", name, sites.size());
    return (int)sites.size();
}

// Target of a `call rel32` at `site`, or 0 if there is no such call.
static uintptr_t CallTarget(uintptr_t site) {
    auto p = reinterpret_cast<uint8_t*>(site);
    if (*p != 0xE8) return 0;
    return site + 5 + *reinterpret_cast<int32_t*>(p + 1);
}

// CTxdStore::RemoveRef does `RemoveModel(slot + STREAM_OFFSET_TXD)`, so the
// offset appears there as an imm32. Check our assumption against the real code.
static bool VerifyTxdStreamOffset() {
    auto p = reinterpret_cast<uint8_t*>(ADDR_TxdRemoveRef);
    for (int i = 0; i < 0x50 - 4; ++i)
        if (*reinterpret_cast<int32_t*>(p + i) == g_txdStreamOffset)
            return true;
    return false;
}

static int SlotOfDict(RwTexDictionary* dict) {
    auto pool = CTxdStore::ms_pTxdPool;
    if (!pool || !dict) return -1;
    for (int i = 0; i < pool->m_nSize; ++i) {
        TxdDef* t = pool->GetAt(i);
        if (t && t->m_pRwDictionary == dict) return i;
    }
    return -1;
}

// ms_aInfoForModel may be relocated by limit adjusters after our static init,
// so read the pointer from the game code each time (same source plugin-sdk uses).
static CStreamingInfo* StreamInfo(int id) {
    return &(*reinterpret_cast<CStreamingInfo**>(0x40A4AD))[id];
}

// Parent that really lives in an IMG (i.e. not "generic", which is loaded from a file).
static bool IsStreamedTxd(int slot) {
    return StreamInfo(slot + g_txdStreamOffset)->m_nCdSize != 0;
}

static RwTexture* FindInDict(RwTexDictionary* d, const char* name) {
    if (!d || !name) return nullptr;
    RwLLLink* end = &d->texturesInDict.link;
    for (RwLLLink* l = end->next; l != end; l = l->next) {
        RwTexture* t = reinterpret_cast<RwTexture*>(reinterpret_cast<char*>(l) - offsetof(RwTexture, lInDictionary));
        if (!_strnicmp(t->name, name, 32)) return t;
    }
    return nullptr;
}

static void DumpDict(const char* what, RwTexDictionary* d) {
    char line[512];
    int n = 0, len = snprintf(line, sizeof(line), "  %s contains:", what);
    RwLLLink* end = &d->texturesInDict.link;
    for (RwLLLink* l = end->next; l != end && len < (int)sizeof(line) - 40; l = l->next, ++n) {
        RwTexture* t = reinterpret_cast<RwTexture*>(reinterpret_cast<char*>(l) - offsetof(RwTexture, lInDictionary));
        len += snprintf(line + len, sizeof(line) - len, " '%s'", t->name);
    }
    if (n == 0) snprintf(line + len, sizeof(line) - len, " (EMPTY)");
    Log("%s", line);
}

// ---- 1) IDE parsing: intercept CFileLoader::LoadLine -----------------------
// The game reads IDE line by line through LoadLine. We swallow the whole
// "txdp ... end" block here, so the original parser never sees it (it could
// otherwise mistake a TXD name like "cars_x" for a section keyword).

static void ParseTxdpLine(const char* line) {
    char buf[128];
    strncpy(buf, line, sizeof(buf) - 1);
    buf[sizeof(buf) - 1] = 0;
    for (char* c = buf; *c; ++c) if (*c == ',') *c = ' ';

    char child[32], parent[32];
    if (sscanf(buf, "%31s %31s", child, parent) != 2) {
        Log("txdp: cannot parse line \"%s\"", line);
        return;
    }

    auto slotOf = [](const char* n) {
        int s = CTxdStore::FindTxdSlot(n);
        return s >= 0 ? s : CTxdStore::AddTxdSlot(n);
        };
    int c = slotOf(child), p = slotOf(parent);
    g_parent[c] = p;
    if (_stricmp(parent, "generic")) // "-> generic" pairs are not interesting
        Log("txdp: %s (%d) -> %s (%d)", child, c, parent, p);
}

static char* __cdecl Hook_LoadLine(int fd) {
    auto orig = reinterpret_cast<char* (__cdecl*)(int)>(ADDR_LoadLine);
    char* line = orig(fd);
    while (line && !_strnicmp(line, "txdp", 4) && (line[4] == 0 || isspace((unsigned char)line[4]))) {
        while ((line = orig(fd)) != nullptr && _strnicmp(line, "end", 3))
            ParseTxdpLine(line);
        Log("txdp: section read, %zu pair(s) total", g_parent.size());
        if (line) line = orig(fd); // first line after "end"
    }
    return line;
}

// ---- 2) texture lookup: fall back to parent TXDs ---------------------------
// Only the call that reads the textures of DFF materials is hooked
// (RwTextureStreamRead -> RwTextureRead, 0x5AAE1B). `g_readChain` is what that
// call went to before us: the original RwTextureRead, or e.g. SkyGfx's
// RwTextureRead_generic. On a miss we walk the parent chain.

static uintptr_t g_readChain = ADDR_RwTextureRead;

static RwTexture* __cdecl Hook_RwTextureRead(const RwChar* name, const RwChar* mask) {
    auto chain = reinterpret_cast<RwTexture * (__cdecl*)(const RwChar*, const RwChar*)>(g_readChain);
    RwTexture* tex = chain(name, mask);
    if (tex || g_parent.empty()) return tex;

    static int logged = 0;
    int curSlot = SlotOfDict(RwTexDictionaryGetCurrent());
    int slot = curSlot;
    for (int depth = 0; slot >= 0 && depth < 8; ++depth) {
        auto it = g_parent.find(slot);
        if (it == g_parent.end()) break;
        slot = it->second;
        TxdDef* p = CTxdStore::ms_pTxdPool->GetAt(slot);
        bool streamed = IsStreamedTxd(slot);
        if (p && p->m_pRwDictionary) {
            tex = FindInDict(p->m_pRwDictionary, name);
            if (tex) {
                tex->refCount++; // RwTextureRead adds a reference for a found texture
                if (logged < 100) {
                    ++logged;
                    Log("texture '%s' (txd '%s'): found in parent '%s'", name,
                        CTxdStore::GetTxdName(curSlot), CTxdStore::GetTxdName(slot));
                }
                return tex;
            }
            if (streamed && logged < 100) {
                ++logged;
                Log("texture '%s' (txd '%s'): parent '%s' is loaded but has NO such texture",
                    name, CTxdStore::GetTxdName(curSlot), CTxdStore::GetTxdName(slot));
                DumpDict(CTxdStore::GetTxdName(slot), p->m_pRwDictionary);
            }
        }
        else if (streamed && logged < 100) {
            ++logged;
            Log("texture '%s' (txd '%s'): parent '%s' is NOT LOADED yet", name,
                CTxdStore::GetTxdName(curSlot), CTxdStore::GetTxdName(slot));
        }
    }
    return nullptr;
}

// Makes sure 0x5AAE1B calls our hook, even if another plugin (SkyGfx) patched
// it before or after us. Called at startup and before every model/TXD build.
static void EnsureTextureReadHook() {
    uintptr_t target = CallTarget(ADDR_TexStreamReadCall);
    if (!target || target == reinterpret_cast<uintptr_t>(&Hook_RwTextureRead)) return;
    if (target != g_readChain) {
        g_readChain = target;
        if (target == ADDR_RwTextureRead)
            Log("texture read: hooked 0x%X (vanilla RwTextureRead)", (unsigned)ADDR_TexStreamReadCall);
        else
            Log("texture read: 0x%X already patched by another plugin (target 0x%X, e.g. SkyGfx): chaining",
                (unsigned)ADDR_TexStreamReadCall, (unsigned)target);
    }
    patch::RedirectCall(ADDR_TexStreamReadCall, (void*)Hook_RwTextureRead);
}

// ---- 3) streaming: request the parent together with the child --------------
static void __cdecl Hook_RequestModel(int id, int flags) {
    static int depth = 0;
    static int logged = 0;
    auto orig = reinterpret_cast<void(__cdecl*)(int, int)>(ADDR_RequestModel);

    auto pool = CTxdStore::ms_pTxdPool;
    if (depth < 8 && pool && id >= g_txdStreamOffset && id < g_txdStreamOffset + pool->m_nSize) {
        auto it = g_parent.find(id - g_txdStreamOffset);
        if (it != g_parent.end() && IsStreamedTxd(it->second)) {
            if (logged < 100) {
                ++logged;
                Log("request txd '%s': parent '%s' (flags 0x%X)", CTxdStore::GetTxdName(id - g_txdStreamOffset),
                    CTxdStore::GetTxdName(it->second), flags);
            }
            ++depth;
            Hook_RequestModel(it->second + g_txdStreamOffset, flags | SF_DONT_REMOVE); // parent first
            --depth;
        }
    }
    orig(id, flags);
}

// GetNextFileOnCd() picks files by position in the image, not by request order,
// and a model only waits for ITS OWN txd. As in SA, we postpone converting the
// child TXD until the parent is loaded: the child is removed from the channel
// and re-requested (what the game itself does when a model's TXD is missing).
static std::unordered_map<int, int> g_deferCount;

// ---- 4) TXDs that cannot be loaded make III hang ---------------------------
// When a TXD cannot be read, ConvertBufferToObject / FinishLoadingLargeFile call
// RemoveModel + ReRequestModel and return false, so the request fails again
// forever and the loading screen spins with no crash. Typical cause: a TXD saved
// in the wrong format (e.g. "Windows" = D3D9 platform instead of GTA III = D3D8).
// III reads TXDs in two ways: LoadTxd (files up to 200 sectors) and
// StartLoadTxd + FinishLoadTxd (bigger files); all three are covered here.
// A TXD that is known to be bad gets an EMPTY dictionary instead (its textures
// are missing, but the game keeps running). Reasons for "bad":
//   a) the first texture is clearly not a D3D8 one (checked before RW sees it,
//      which also protects from hangs inside RW itself),
//   b) any of the load functions failed 3 times,
//   c) ConvertBufferToObject failed 20 times in a row for it.
static std::unordered_map<int, int>  g_loadFail;
static std::unordered_map<int, bool> g_badTxd;
static std::unordered_map<int, int>  g_convTries;

static bool GiveEmptyDict(int slot) {
    TxdDef* t = CTxdStore::ms_pTxdPool->GetAt(slot);
    if (!t) return false;
    if (!t->m_pRwDictionary) t->m_pRwDictionary = RwTexDictionaryCreate();
    return t->m_pRwDictionary != nullptr;
}

// Looks only at the first texture's platform id (inside the first sector, so
// always readable). Returns a description if it is clearly not a GTA III
// texture, nullptr otherwise (also when the layout is unusual: then RW decides).
// Layout: TEXDICTIONARY(0x16) { STRUCT(0x01) {count,device}, TEXTURENATIVE(0x15) { STRUCT(0x01) { platform, ... } } }
static const char* CheckTxdFormat(const uint8_t* b) {
    auto u32 = [&](int o) { return *reinterpret_cast<const uint32_t*>(b + o); };
    if (u32(0) != 0x16 || u32(12) != 0x01) return nullptr;
    uint32_t structSize = u32(16);
    if (structSize != 4) return nullptr;
    int tex = 12 + 12 + structSize;           // first TEXTURENATIVE chunk
    if (u32(tex) != 0x15 || u32(tex + 12) != 0x01) return nullptr;
    uint32_t platform = u32(tex + 24);
    if (platform == 9)        return "D3D9 platform (Windows/SA format)";
    if (platform == 5)        return "Xbox platform";
    if (platform == 0x325350) return "PS2 platform";
    return nullptr;
}

// Called when one of the load functions failed. True = substituted an empty dictionary.
static bool HandleLoadFailure(int slot, const char* what) {
    int n = ++g_loadFail[slot];
    if (n <= 5)
        Log("FAILED (%s) to load TXD '%s' (slot %d), attempt %d", what, CTxdStore::GetTxdName(slot), slot, n);
    if (n < 3) return false;
    g_badTxd[slot] = true;
    if (!GiveEmptyDict(slot)) return false;
    Log("TXD '%s' replaced by an EMPTY dictionary to avoid a hang", CTxdStore::GetTxdName(slot));
    return true;
}

static bool __cdecl Hook_ConvertBufferToObject(char* buf, int streamId) {
    auto orig = reinterpret_cast<bool(__cdecl*)(char*, int)>(ADDR_ConvertBuffer);
    auto removeModel = reinterpret_cast<void(__cdecl*)(int)>(ADDR_RemoveModel);

    EnsureTextureReadHook(); // cheap: reads 5 bytes

    auto pool = CTxdStore::ms_pTxdPool;
    bool isTxd = g_streamingOk && pool && streamId >= g_txdStreamOffset && streamId < g_txdStreamOffset + pool->m_nSize;
    int slot = streamId - g_txdStreamOffset;
    if (isTxd) {
        // (a) wrong platform: do not even let RW read it
        if (!g_badTxd.count(slot)) {
            if (const char* why = CheckTxdFormat(reinterpret_cast<const uint8_t*>(buf))) {
                g_badTxd[slot] = true;
                Log("TXD '%s' has the wrong format: %s. It will be replaced by an EMPTY dictionary. "
                    "Re-save it in the GTA III (D3D8) format.", CTxdStore::GetTxdName(slot), why);
            }
        }

        // child waits for its parent
        auto it = g_parent.find(slot);
        if (it != g_parent.end() && IsStreamedTxd(it->second)) {
            int parentId = it->second + g_txdStreamOffset;
            if (StreamInfo(parentId)->m_nLoadState != SS_LOADED) {
                int& n = g_deferCount[streamId];
                if (++n <= 2000) { // safety valve: never loop forever
                    if (n == 1)
                        Log("defer txd '%s': waiting for parent '%s'",
                            CTxdStore::GetTxdName(slot), CTxdStore::GetTxdName(it->second));
                    Hook_RequestModel(parentId, SF_DONT_REMOVE);
                    removeModel(streamId);
                    Hook_RequestModel(streamId, StreamInfo(streamId)->m_nFlags);
                    return false;
                }
                Log("GAVE UP waiting for parent '%s' of txd '%s'", CTxdStore::GetTxdName(it->second),
                    CTxdStore::GetTxdName(slot));
            }
            g_deferCount.erase(streamId);
        }
    }

    bool result = orig(buf, streamId);

    if (isTxd) {
        if (result) g_convTries.erase(streamId);
        else if (++g_convTries[streamId] >= 20 && !g_badTxd.count(slot)) { // (c)
            g_badTxd[slot] = true;
            Log("TXD '%s' failed to load 20 times in a row, it will be replaced by an EMPTY dictionary",
                CTxdStore::GetTxdName(slot));
        }
    }
    return result;
}

static bool __cdecl Hook_LoadTxd(int slot, RwStream* stream) {
    if (g_badTxd.count(slot) && GiveEmptyDict(slot)) return true; // do not read the broken stream
    bool ok = reinterpret_cast<bool(__cdecl*)(int, RwStream*)>(ADDR_LoadTxd)(slot, stream);
    if (!ok && HandleLoadFailure(slot, "LoadTxd")) return true;
    return ok;
}

static bool __cdecl Hook_StartLoadTxd(int slot, RwStream* stream) {
    if (g_badTxd.count(slot) && GiveEmptyDict(slot)) return true; // FinishLoadTxd will skip it too
    bool ok = reinterpret_cast<bool(__cdecl*)(int, RwStream*)>(ADDR_StartLoadTxd)(slot, stream);
    if (!ok && HandleLoadFailure(slot, "StartLoadTxd")) return true;
    return ok;
}

static bool __cdecl Hook_FinishLoadTxd(int slot, RwStream* stream) {
    if (g_badTxd.count(slot) && GiveEmptyDict(slot)) return true;
    bool ok = reinterpret_cast<bool(__cdecl*)(int, RwStream*)>(ADDR_FinishLoadTxd)(slot, stream);
    if (!ok && HandleLoadFailure(slot, "FinishLoadTxd")) return true;
    return ok;
}

// ---- init ------------------------------------------------------------------
struct TxdpPlugin {
    TxdpPlugin() {
        InitSettings();
        if (reinterpret_cast<uintptr_t>(GetModuleHandleA(nullptr)) != 0x400000) {
            Log("unexpected image base, plugin disabled");
            return;
        }
        // Version check: the known call sites must exist, otherwise this is not GTA III 1.0.
        uintptr_t t = CallTarget(ADDR_TexStreamReadCall);
        if (!t || !HookAllCalls(ADDR_LoadLine, (void*)Hook_LoadLine, "LoadLine")) {
            Log("not GTA III 1.0 (known call sites not found), plugin disabled");
            return;
        }
        EnsureTextureReadHook();

        g_streamingOk = VerifyTxdStreamOffset();
        HookAllCalls(ADDR_ConvertBuffer, (void*)Hook_ConvertBufferToObject, "ConvertBufferToObject");
        HookAllCalls(ADDR_LoadTxd, (void*)Hook_LoadTxd, "LoadTxd");
        HookAllCalls(ADDR_StartLoadTxd, (void*)Hook_StartLoadTxd, "StartLoadTxd");
        HookAllCalls(ADDR_FinishLoadTxd, (void*)Hook_FinishLoadTxd, "FinishLoadTxd");
        if (g_streamingOk)
            HookAllCalls(ADDR_RequestModel, (void*)Hook_RequestModel, "RequestModel");
        else
            Log("TXD stream offset %d not confirmed, parent streaming disabled", g_txdStreamOffset);
    }
} g_txdp;