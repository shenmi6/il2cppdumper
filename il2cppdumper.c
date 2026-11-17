/*
 * icdump_static.c - il2cpp 静态 dumper（纯 C，单文件）
 *   输入：libil2cpp.so + global-metadata.dat
 *   输出：dump.cs
 *
 *   gcc -O2 -o icdump_static icdump_static.c
 *   ./icdump_static
 *
 * 路径在 main() 顶部填。
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

/* ======================= 配置 ======================= */
static const char *SO_PATH  = "/sdcard/DUMP/libil2cpp.so";
static const char *MD_PATH  = "/sdcard/DUMP/global-metadata.dat";
static const char *OUT_PATH = "/sdcard/DUMP/dump.cs";

/* ======================= 基础 ======================= */
static uint8_t *g_so, *g_md;
static size_t   g_so_sz, g_md_sz;

static int32_t  R32(const void *p) { int32_t v; memcpy(&v, p, 4); return v; }
static uint32_t RU32(const void *p) { uint32_t v; memcpy(&v, p, 4); return v; }
static uint16_t RU16(const void *p) { uint16_t v; memcpy(&v, p, 2); return v; }

static void *xmalloc(size_t n) {
    void *p = malloc(n);
    if (!p) { fprintf(stderr, "[!] OOM %zu\n", n); exit(1); }
    return p;
}

static uint8_t *read_all(const char *path, size_t *out_sz) {
    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "[!] 打不开 %s\n", path); return NULL; }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *b = xmalloc((size_t)n + 1);
    if (fread(b, 1, (size_t)n, f) != (size_t)n) {
        fprintf(stderr, "[!] 读取失败 %s\n", path);
        fclose(f); free(b); return NULL;
    }
    fclose(f);
    b[n] = 0;
    *out_sz = (size_t)n;
    return b;
}

/* ======================= ELF ======================= */
typedef struct {
    uint64_t vaddr, off, filesz, memsz;
    uint32_t flags, type;
} Phdr;
static Phdr *g_ph; static int g_phn;

static int elf_load(void) {
    if (g_so_sz < 64 || memcmp(g_so, "\x7f" "ELF", 4)) {
        fprintf(stderr, "[!] 不是 ELF\n"); return -1;
    }
    if (g_so[4] != 2) { fprintf(stderr, "[!] 只支持 ELF64\n"); return -1; }
    uint64_t phoff = *(uint64_t *)(g_so + 0x20);
    uint16_t phentsize = *(uint16_t *)(g_so + 0x36);
    uint16_t phnum = *(uint16_t *)(g_so + 0x38);
    g_ph = xmalloc(sizeof(Phdr) * phnum);
    g_phn = phnum;
    for (int i = 0; i < phnum; i++) {
        uint8_t *p = g_so + phoff + (uint64_t)i * phentsize;
        g_ph[i].type   = RU32(p + 0x00);
        g_ph[i].flags  = RU32(p + 0x04);
        g_ph[i].off    = *(uint64_t *)(p + 0x08);
        g_ph[i].vaddr  = *(uint64_t *)(p + 0x10);
        g_ph[i].filesz = *(uint64_t *)(p + 0x20);
        g_ph[i].memsz  = *(uint64_t *)(p + 0x28);
    }
    fprintf(stderr, "[*] ELF64, %d program headers\n", phnum);
    return 0;
}

/* vaddr -> 文件偏移 */
static uint64_t va2off(uint64_t va) {
    uint64_t best = (uint64_t)-1;
    int64_t  bestd = 0;
    for (int i = 0; i < g_phn; i++) {
        if (va < g_ph[i].vaddr || va >= g_ph[i].vaddr + g_ph[i].filesz) continue;
        int64_t d = (int64_t)g_ph[i].vaddr - (int64_t)g_ph[i].off;
        if (d < 0) d = -d;
        if (best == (uint64_t)-1 || d < bestd) {
            best = g_ph[i].off + (va - g_ph[i].vaddr);
            bestd = d;
        }
    }
    return best;
}
/* vaddr 是否落在任何可装载段内 */
static int va_ok(uint64_t va) {
    for (int i = 0; i < g_phn; i++)
        if (va >= g_ph[i].vaddr && va < g_ph[i].vaddr + g_ph[i].memsz) return 1;
    return 0;
}
/* 可写段（.data 区）范围 */
static int rw_segments(uint64_t **outs, uint64_t **oute, int *outn) {
    int n = 0;
    for (int i = 0; i < g_phn; i++)
        if ((g_ph[i].flags & 2) && g_ph[i].filesz > 0) n++;
    uint64_t *s = xmalloc(sizeof(uint64_t) * n);
    uint64_t *e = xmalloc(sizeof(uint64_t) * n);
    int k = 0;
    for (int i = 0; i < g_phn; i++)
        if ((g_ph[i].flags & 2) && g_ph[i].filesz > 0) {
            s[k] = g_ph[i].off;
            e[k] = g_ph[i].off + g_ph[i].filesz;
            k++;
        }
    *outs = s; *oute = e; *outn = n;
    return 0;
}

/* ======================= metadata ======================= */
static uint8_t *g_hdr;      /* header 起始（== g_md） */
static int32_t  g_mdver;
static int g_v31;   /* metadata >= 31: MethodDefinition 多 returnParameterToken */

#define H(i) R32(g_hdr + (i) * 4)

/* header 索引（v24.0 ~ v31 通用前缀） */
enum {
    H_SANITY = 0, H_VERSION,
    H_STRLIT_OFF, H_STRLIT_SZ,
    H_STRLITDATA_OFF, H_STRLITDATA_SZ,
    H_STRING_OFF, H_STRING_SZ,
    H_EVENTS_OFF, H_EVENTS_SZ,
    H_PROPS_OFF, H_PROPS_SZ,
    H_METHODS_OFF, H_METHODS_SZ,
    H_PDEFVAL_OFF, H_PDEFVAL_SZ,
    H_FDEFVAL_OFF, H_FDEFVAL_SZ,
    H_FDEFDATA_OFF, H_FDEFDATA_SZ,
    H_FMARSH_OFF, H_FMARSH_SZ,
    H_PARAMS_OFF, H_PARAMS_SZ,
    H_FIELDS_OFF, H_FIELDS_SZ,
    H_GPARAMS_OFF, H_GPARAMS_SZ,
    H_GCONSTR_OFF, H_GCONSTR_SZ,
    H_GCONT_OFF, H_GCONT_SZ,
    H_NESTED_OFF, H_NESTED_SZ,
    H_IFACES_OFF, H_IFACES_SZ,
    H_VTABLE_OFF, H_VTABLE_SZ,
    H_IFOFF_OFF, H_IFOFF_SZ,
    H_TDEFS_OFF, H_TDEFS_SZ,
    H_IMAGES_OFF, H_IMAGES_SZ,
    H_ASMS_OFF, H_ASMS_SZ,
    H_FREFS_OFF, H_FREFS_SZ,
    H_RASMS_OFF, H_RASMS_SZ
};

static uint8_t *g_strings; static int32_t g_strings_n;
static uint8_t *g_tdefs;   static int32_t g_tdefs_n, g_tdef_stride;
static uint8_t *g_methods; static int32_t g_methods_n, g_method_stride;
static uint8_t *g_fields;  static int32_t g_fields_n, g_field_stride;
static uint8_t *g_params;  static int32_t g_params_n, g_param_stride;
static uint8_t *g_props;   static int32_t g_props_n, g_prop_stride;
static uint8_t *g_events; static int32_t g_events_n, g_event_stride;
static uint8_t *g_images;  static int32_t g_images_n, g_image_stride;
static uint8_t *g_asms;    static int32_t g_asms_n, g_asm_stride;
static uint8_t *g_ifaces;  static int32_t g_ifaces_n;
static uint8_t *g_nested;  static int32_t g_nested_n;

static uint64_t *g_types;  static int32_t g_types_n;   /* Il2CppType** */

static const char *S(int32_t idx) {
    static char sb[8][640];
    static int  st = 0;
    if (idx < 0 || idx >= g_strings_n) return "";
    const char *p = (const char *)(g_strings + idx);
    size_t n = strnlen(p, (size_t)(g_strings_n - idx));
    if (n > 639) n = 639;
    memcpy(sb[st], p, n);
    sb[st][n] = 0;
    const char *r = sb[st];
    st = (st + 1) & 7;
    return r;
}

static int md_load(void) {
    if (g_md_sz < 8) { fprintf(stderr, "[!] metadata 太小\n"); return -1; }
    uint32_t sanity = RU32(g_md);
    if (sanity != 0xFAB11BAFu) {
        fprintf(stderr, "[!] metadata magic 错误: 0x%08X（可能已加密）\n", sanity);
        return -1;
    }
    g_hdr = g_md;
    g_mdver = H(H_VERSION);
    g_v31 = (g_mdver >= 31);
    fprintf(stderr, "[*] metadata version = %d\n", g_mdver);

    /* 表定位 */
    g_strings   = g_md + H(H_STRING_OFF);
    g_strings_n = H(H_STRING_SZ);
    g_tdefs     = g_md + H(H_TDEFS_OFF);
    g_methods   = g_md + H(H_METHODS_OFF);
    g_fields    = g_md + H(H_FIELDS_OFF);
    g_params    = g_md + H(H_PARAMS_OFF);
    g_props     = g_md + H(H_PROPS_OFF);
    g_events    = g_md + H(H_EVENTS_OFF);
    g_event_stride = 0x18;
    g_events_n  = H(H_EVENTS_SZ) / g_event_stride;
    g_images    = g_md + H(H_IMAGES_OFF);
    g_asms      = g_md + H(H_ASMS_OFF);
    g_ifaces    = g_md + H(H_IFACES_OFF);
    g_nested    = g_md + H(H_NESTED_OFF);
    g_nested_n  = H(H_NESTED_SZ) / 4;

    /* header 给的是每表的字节 size，不是 count；用步长推算 count。
       methods/fields/params/props/images 的结构尺寸在各版本间稳定，
       typeDefinitions 有变化，下面用整除性自动探测。 */
    int32_t tdb = H(H_TDEFS_SZ);

    /* 先解析 images，它们的 typeStart+typeCount 最大值 == typeDefinitions count，
       用这个硬约束锁定 typeDefinitions 的步长。 */
    g_image_stride = 0x28;
    g_images_n     = H(H_IMAGES_SZ) / g_image_stride;
    int32_t maxEnd = 0;
    for (int32_t i = 0; i < g_images_n; i++) {
        uint8_t *im = g_images + (uint64_t)i * g_image_stride;
        int32_t e = R32(im + 0x08) + (int32_t)RU32(im + 0x0C);
        if (e > maxEnd) maxEnd = e;
    }

    g_tdef_stride = 0;
    for (int st = 0x80; st >= 0x30; st -= 4) {
        if (tdb % st) continue;
        if (tdb / st != maxEnd) continue;
        g_tdef_stride = st;
        break;
    }
    if (!g_tdef_stride) {
        /* 退而求其次：任何能整除且名字索引合法的步长 */
        for (int st = 0x80; st >= 0x30; st -= 4) {
            if (tdb % st) continue;
            int32_t nm = R32(g_md + H(H_TDEFS_OFF));
            if (nm < 0 || nm >= H(H_STRING_SZ)) continue;
            g_tdef_stride = st;
            break;
        }
    }
    if (!g_tdef_stride) {
        fprintf(stderr, "[!] 无法推断 typeDefinitions 步长 (bytes=%d, maxEnd=%d)\n", tdb, maxEnd);
        return -1;
    }
    g_tdefs_n = tdb / g_tdef_stride;

    g_method_stride = 0x20;
    g_method_stride = g_v31 ? 0x24 : 0x20;
    g_methods_n    = H(H_METHODS_SZ) / g_method_stride;
    g_field_stride  = 0x0C;
    g_fields_n      = H(H_FIELDS_SZ) / g_field_stride;
    g_param_stride  = 0x0C;
    g_params_n      = H(H_PARAMS_SZ) / g_param_stride;
    g_prop_stride   = 0x14;
    g_props_n       = H(H_PROPS_SZ) / g_prop_stride;
    {   /* assembly 结构 0x40~0x58 之间，用整除探测 */
        int32_t ab = H(H_ASMS_SZ);
        g_asm_stride = 0;
        for (int st = 0x38; st <= 0x60; st += 4)
            if (ab % st == 0) { int c = ab / st; if (c > 0 && c < 5000) { g_asm_stride = st; break; } }
        if (!g_asm_stride) g_asm_stride = 0x50;
        g_asms_n = ab / g_asm_stride;
    }

    fprintf(stderr, "[*] tdefs=%d(stride %d) methods=%d(%d) fields=%d(%d)\n",
            g_tdefs_n, g_tdef_stride, g_methods_n, g_method_stride,
            g_fields_n, g_field_stride);
    fprintf(stderr, "[*] params=%d(%d) props=%d(%d) images=%d(%d) asms=%d(%d)\n",
            g_params_n, g_param_stride, g_props_n, g_prop_stride,
            g_images_n, g_image_stride, g_asms_n, g_asm_stride);
    return 0;
}

/* ======================= 定位 types 数组 ======================= */
/*
 * metadata 文件里没有 types 表的 offset（它由 .so 里的
 * Il2CppMetadataRegistration 指向）。这里用特征扫描：
 *   .data 里出现 <count(4B)> + <pad> + <va(8B)>，且 va 指向的区域
 *   连续 16 项 Il2CppType 的 type 字段都在合法枚举内。
 */
static int type_enum_ok(uint32_t bits) {
    uint32_t t = (bits >> 16) & 0xFF;
    return (t >= 0x01 && t <= 0x21);
}

static int bits_ok_at(uint64_t off);

/*
 * 对应 Perfare SectionHelper.FindMetadataRegistrationV21()
 * 双锚点：data 段里连续两个 long 都等于 typeDefinitionsCount
 *   +0x50 fieldOffsetsCount           == tdefCount
 *   +0x58 fieldOffsets        (ptr)
 *   +0x60 typeDefinitionsSizesCount   == tdefCount    ← addr 即此处
 *   +0x68 typeDefinitionsSizes (ptr)
 * 命中后 metadataRegistration = addr - 0x50
 */
static uint64_t g_mr = (uint64_t)-1;
static int find_types(void) {
    uint64_t *rs, *re; int rn;
    rw_segments(&rs, &re, &rn);
    uint64_t need = (uint64_t)g_tdefs_n;
    int hit = 0;
    for (int k = 0; k < rn && !hit; k++) {
        for (uint64_t o = rs[k]; o + 24 <= re[k]; o += 8) {
            if (*(uint64_t *)(g_so + o) != need) continue;
            if (*(uint64_t *)(g_so + o + 16) != need) continue;
            if (o < 0x50) continue;
            uint64_t mr = o - 0x50;
            uint64_t tcnt = *(uint64_t *)(g_so + mr + 0x30);
            uint64_t tva  = *(uint64_t *)(g_so + mr + 0x38);
            if (tcnt < 100 || tcnt > 4000000) continue;
            uint64_t toff = va2off(tva);
            if (toff == (uint64_t)-1 || toff + 64 > g_so_sz) continue;
            int bad = 0;
            for (int q = 0; q < 8; q++) {
                uint64_t e  = *(uint64_t *)(g_so + toff + (uint64_t)q * 8);
                if (!e) { bad = 1; break; }
                uint64_t eo = va2off(e);
                if (eo == (uint64_t)-1 || eo + 12 > g_so_sz) { bad = 1; break; }
                if (!type_enum_ok(*(uint32_t *)(g_so + eo + 8))) { bad = 1; break; }
            }
            if (bad) continue;
            g_mr = mr;
            g_types = (uint64_t *)(g_so + toff);
            g_types_n = (int32_t)tcnt;
            hit = 1;
            break;
        }
    }
    free(rs); free(re);
    if (hit) {
        fprintf(stderr, "[*] MetadataRegistration @ so+0x%llx (双锟点)\n",
                (unsigned long long)g_mr);
        fprintf(stderr, "[*] types=%d @ so+0x%llx\n", g_types_n,
                (unsigned long long)((uint8_t *)g_types - g_so));
        return 0;
    }
    fprintf(stderr, "[!] 双锟点未命中，回退到启发式扫描\n");

    /* ---- 回退：旧启发式（非 v27 布局）---- */
    uint64_t best_cnt = 0, best_va = 0;
    rw_segments(&rs, &re, &rn);
    for (int k = 0; k < rn; k++) {
        for (uint64_t o = rs[k]; o + 16 <= re[k]; o += 8) {
            uint32_t cnt = *(uint32_t *)(g_so + o);
            if (cnt < 5000 || cnt > 500000) continue;
            uint64_t va = *(uint64_t *)(g_so + o + 8);
            if (!va_ok(va)) continue;
            uint64_t foff = va2off(va);
            if (foff == (uint64_t)-1 || foff + 256 > g_so_sz) continue;
            int ok = 0; uint64_t prev = 0;
            for (int q = 0; q < 24; q++) {
                uint64_t e = *(uint64_t *)(g_so + foff + (uint64_t)q * 8);
                if (!e || e <= prev) break;
                uint64_t eo = va2off(e);
                if (eo == (uint64_t)-1 || eo + 12 > g_so_sz) break;
                if (!type_enum_ok(*(uint32_t *)(g_so + eo + 8))) break;
                prev = e; ok++;
            }
            if (ok < 24) continue;
            if (cnt > best_cnt) { best_cnt = cnt; best_va = va; }
        }
    }
    free(rs); free(re);
    if (!best_va) { fprintf(stderr, "[!] 找不到 types 数组\n"); return -1; }
    g_types = (uint64_t *)(g_so + va2off(best_va));
    g_types_n = (int32_t)best_cnt;
    return 0;
}

/* ============ 字段偏移（Il2CppMetadataRegistration.fieldOffsets） ============
 * v22+ 有两种形态：
 *   direct  : fieldOffsets[globalFieldIndex] = offset
 *   pointer : fieldOffsets[typeDefIndex] -> uint32[fieldCount]  ← arm64 常见
 */
static int g_fo_ptr = -1;

static int field_offsets_are_pointers(void) {
    if (g_fo_ptr >= 0) return g_fo_ptr;
    g_fo_ptr = 0;
    if (g_mr == (uint64_t)-1) return 0;
    uint64_t cnt = *(uint64_t *)(g_so + g_mr + 0x50);
    uint64_t ptr = *(uint64_t *)(g_so + g_mr + 0x58);
    if (!cnt || cnt > 1000000) return 0;
    uint64_t po = va2off(ptr);
    if (po == (uint64_t)-1 || po + 24 > g_so_sz) return 0;
    /* pointer 模式的特征：数组里出现「像 vaddr」的值（>0x10000 且可映射） */
    int has_addr = 0, has_small = 0;
    uint64_t lim = cnt < 64 ? cnt : 64;
    for (uint64_t q = 0; q < lim; q++) {
        uint64_t v = *(uint64_t *)(g_so + po + q * 8);
        if (!v) continue;
        if (v > 0x10000 && va2off(v) != (uint64_t)-1) has_addr = 1;
        else if (v < 0x10000) has_small = 1;
    }
    /* direct 模式的取值都是小整数（字段偏移），一旦出现可映射的地址即 pointer */
    if (has_addr) g_fo_ptr = 1;
    return g_fo_ptr;
}

/* 返回字段在托管对象内的偏移，失败 -1 */
static int32_t field_offset(int32_t tdi, int in_type, int is_valuetype, int is_static) {
    if (g_mr == (uint64_t)-1) return -1;
    uint64_t cnt = *(uint64_t *)(g_so + g_mr + 0x50);
    uint64_t ptr = *(uint64_t *)(g_so + g_mr + 0x58);
    if (!cnt) return -1;
    uint64_t po = va2off(ptr);
    if (po == (uint64_t)-1) return -1;
    int32_t off = -1;
    if (field_offsets_are_pointers()) {
        if (tdi < 0 || (uint64_t)tdi >= cnt) return -1;
        uint64_t sub = *(uint64_t *)(g_so + po + (uint64_t)tdi * 8);
        uint64_t so = va2off(sub);
        if (so == (uint64_t)-1 || so + 4ULL * (uint64_t)(in_type + 1) > g_so_sz) return -1;
        off = *(int32_t *)(g_so + so + 4ULL * (uint64_t)in_type);
    } else {
        /* direct：索引是全局字段序号 */
        uint64_t gi = (uint64_t)in_type;
        if (gi >= cnt) return -1;
        off = (int32_t)(*(const uint32_t *)(g_so + po + 4ULL * gi));
    }
    if (off > 0) {
        int ptrsz = 8;   /* ELF64 */
        if (is_static) off -= ptrsz;
        else if (is_valuetype) off -= ptrsz * 2;
    }
    return off;
}

/* ================= CodeRegistration / method RVA ================= */
typedef struct { uint64_t off, offend, addr, addrend; } Sec;
static Sec g_secx[16], g_secd[16];
static int g_nx, g_nd;
static uint64_t g_cr = 0;
static int g_dbg_dll_found = 0;
static int g_nmod = 0;
static struct { const char *name; uint64_t cnt, ptrs; } g_mod[256];

static void classify_segments(void) {
    g_nx = g_nd = 0;
    for (int i = 0; i < g_phn; i++) {
        Sec s;
        s.off    = g_ph[i].off;
        s.offend = g_ph[i].off + g_ph[i].filesz;
        s.addr   = g_ph[i].vaddr;
        s.addrend= g_ph[i].vaddr + g_ph[i].memsz;
        if ((g_ph[i].flags & 1) && g_nx < 16) g_secx[g_nx++] = s;
        if ((g_ph[i].flags & 2) && g_nd < 16) g_secd[g_nd++] = s;
    }
}

/* Perfare SectionHelper.FindReference：data 段里找值==addr 的位置 */
static uint64_t find_ref(uint64_t addr) {
    for (int k = 0; k < g_nd; k++) {
        uint64_t e = g_secd[k].offend;
        if (e > g_so_sz) e = g_so_sz;
        if (e < 8) continue;
        for (uint64_t o = g_secd[k].off; o + 8 <= e; o += 8)
            if (*(uint64_t *)(g_so + o) == addr)
                return o - g_secd[k].off + g_secd[k].addr;
    }
    return 0;
}

/* Perfare FindCodeRegistration2019（v24.2+）
 * "mscorlib.dll" -> 反查 CodeGenModule.name
 *                -> 反查 modules[i]
 *                -> 反查 codeGenModules，*(r3-8)==imageCount
 *                -> codeRegistration = r3 - 0x68
 */
static int find_code_registration(void) {
    static const char needle[] = "mscorlib.dll";
    const uint64_t nlen = sizeof(needle) - 1;
    for (int pass = 0; pass < g_phn; pass++) {
        if (g_ph[pass].type != 1) continue;          /* PT_LOAD，含只读 .rodata */
        uint64_t soff  = g_ph[pass].off;
        uint64_t send  = g_ph[pass].off + g_ph[pass].filesz;
        uint64_t saddr = g_ph[pass].vaddr;
        if (send > g_so_sz) send = g_so_sz;
        if (send < nlen) continue;
        for (uint64_t o = soff; o + nlen <= send; o++) {
            if (memcmp(g_so + o, needle, nlen)) continue;
            uint64_t dllva = o - soff + saddr;
            uint64_t r1 = find_ref(dllva);
            if (!r1) continue;
            uint64_t r2 = find_ref(r1);
            if (!r2) continue;
            for (int i = g_images_n - 1; i >= 0; i--) {
                uint64_t r3 = find_ref(r2 - (uint64_t)i * 8);
                if (!r3) continue;
                uint64_t r3o = va2off(r3 - 8);
                if (r3o == (uint64_t)-1 || r3o + 8 > g_so_sz) continue;
                if (*(uint64_t *)(g_so + r3o) != (uint64_t)g_images_n) continue;
                g_cr = r3 - ((g_mdver >= 29) ? 0x70 : 0x68);
                return 1;
            }
        }
    }
    return 0;
}

/* Il2CppCodeGenModule: name@0 / methodPointerCount@8 / methodPointers@0x10 */
static int load_code_modules(void) {
    if (!g_cr) return 0;
    uint64_t co = va2off(g_cr);
    if (co == (uint64_t)-1 || co + 0x70 > g_so_sz) return 0;
    uint64_t nmod = *(uint64_t *)(g_so + co + (g_v31 ? 0x68 : 0x60));
    uint64_t mods = *(uint64_t *)(g_so + co + (g_v31 ? 0x70 : 0x68));
    if (nmod == 0 || nmod > 4096) return 0;
    uint64_t mo = va2off(mods);
    if (mo == (uint64_t)-1 || mo + nmod * 8 > g_so_sz) return 0;
    g_nmod = (int)nmod;
    for (uint64_t i = 0; i < nmod && i < 256; i++) {
        uint64_t mv = *(uint64_t *)(g_so + mo + i * 8);
        uint64_t mm = va2off(mv);
        g_mod[i].name = ""; g_mod[i].cnt = 0; g_mod[i].ptrs = 0;
        if (mm == (uint64_t)-1 || mm + 0x18 > g_so_sz) continue;
        uint64_t nv = *(uint64_t *)(g_so + mm + 0x00);
        g_mod[i].cnt  = *(uint64_t *)(g_so + mm + 0x08);
        g_mod[i].ptrs = *(uint64_t *)(g_so + mm + 0x10);
        uint64_t no = va2off(nv);
        if (no != (uint64_t)-1 && no < g_so_sz) g_mod[i].name = (const char *)(g_so + no);
    }
    return 1;
}

/* v24.2+：methodPointer = module.methodPointers[(token & 0xFFFFFF) - 1] */
static uint64_t method_ptr(const char *dll, uint32_t token) {
    if (!dll || !*dll || !g_nmod) return 0;
    int k = -1;
    for (int i = 0; i < g_nmod && i < 256; i++)
        if (g_mod[i].name && !strcmp(g_mod[i].name, dll)) { k = i; break; }
    if (k < 0) {
        static int dn = 0;
        if (dn < 3) { dn++; fprintf(stderr, "[dbg] method_ptr 找不到模块 '%s'\n", dll); }
        return 0;
    }
    uint32_t idx = token & 0x00FFFFFFu;
    if (idx == 0 || (uint64_t)idx > g_mod[k].cnt) return 0;
    uint64_t po = va2off(g_mod[k].ptrs);
    if (po == (uint64_t)-1 || po + (uint64_t)idx * 8 > g_so_sz) return 0;
    return *(uint64_t *)(g_so + po + (uint64_t)(idx - 1) * 8);
}

/* ======================= 类型 ======================= */
enum {
    T_END=0, T_VOID=1, T_BOOLEAN=2, T_CHAR=3, T_I1=4, T_U1=5,
    T_I2=6, T_U2=7, T_I4=8, T_U4=9, T_I8=10, T_U8=11,
    T_R4=12, T_R8=13, T_STRING=14, T_PTR=15, T_BYREF=16,
    T_VALUETYPE=17, T_CLASS=18, T_VAR=19, T_ARRAY=20,
    T_GENERICINST=21, T_TYPEDBYREF=22, T_I=24, T_U=25,
    T_FNPTR=27, T_OBJECT=28, T_SZARRAY=29, T_MVAR=30
};

typedef struct {
    int32_t  data;      /* union 低 32 位（klassIndex / typeIndex） */
    uint32_t pad0;
    uint32_t bits;      /* attrs:16 type:8 num_mods:6 byref:1 pinned:1 */
    uint32_t pad1;
} Il2CppType;

/* Il2CppType 的 bits 在 +8，type 字段必须是合法枚举 */
/* ============ 重定位（未 dump 的 so，指针全在 .rela.dyn 的 addend 里） ============
 * 对应 Perfare Elf64.RelocationProcessing()
 * R_AARCH64_RELATIVE(1027) / R_X86_64_RELATIVE(8) / R_ARM_RELATIVE(3)
 *   -> *r_offset = r_addend
 */
static int g_reloc_applied = 0;

static int apply_relocations(void) {
    uint64_t rela_va = 0, rela_sz = 0;
    for (int i = 0; i < g_phn; i++) {
        if (g_ph[i].type != 2) continue;              /* PT_DYNAMIC */
        uint64_t off = g_ph[i].off, end = off + g_ph[i].filesz;
        if (end > g_so_sz) end = g_so_sz;
        for (uint64_t p = off; p + 16 <= end; p += 16) {
            int64_t  tag = *(int64_t *)(g_so + p);
            uint64_t val = *(uint64_t *)(g_so + p + 8);
            if (tag == 0) break;                      /* DT_NULL */
            if (tag == 7)  rela_va = val;             /* DT_RELA */
            if (tag == 8)  rela_sz = val;             /* DT_RELASZ */
        }
    }
    if (!rela_va || !rela_sz || rela_sz > 64ULL * 1024 * 1024) return 0;
    uint64_t ro = va2off(rela_va);
    if (ro == (uint64_t)-1) return 0;
    uint64_t n = rela_sz / 24;
    int applied = 0;
    for (uint64_t i = 0; i < n; i++) {
        uint64_t p = ro + i * 24;
        if (p + 24 > g_so_sz) break;
        uint64_t r_off  = *(uint64_t *)(g_so + p);
        uint64_t r_info = *(uint64_t *)(g_so + p + 8);
        uint64_t r_add  = *(uint64_t *)(g_so + p + 16);
        uint32_t rtype  = (uint32_t)(r_info & 0xFFFFFFFFu);
        uint64_t val = 0;
        int ok = 0;
        if (rtype == 1027 || rtype == 8 || rtype == 3) { val = r_add; ok = 1; }
        if (!ok) continue;
        uint64_t dst = va2off(r_off);
        if (dst == (uint64_t)-1 || dst + 8 > g_so_sz) continue;
        *(uint64_t *)(g_so + dst) = val;
        applied++;
    }
    g_reloc_applied = applied;
    fprintf(stderr, "[*] 重定位: %d / %llu 条\n", applied, (unsigned long long)n);
    return applied;
}


static int bits_ok_at(uint64_t off) {
    if (off + 12 > g_so_sz) return 0;
    uint32_t b = RU32(g_so + off + 8);
    uint32_t t = (b >> 16) & 0xFF;
    return (t >= 0x01 && t <= 0x21);
}

static Il2CppType *ty(int32_t idx) {
    if (idx < 0 || idx >= g_types_n) return NULL;
    uint64_t va = g_types[idx];
    if (!va) return NULL;
    uint64_t off = va2off(va);
    if (off != (uint64_t)-1 && bits_ok_at(off))
        return (Il2CppType *)(g_so + off);
    if (va < g_so_sz && bits_ok_at(va))       /* 兜底：offset==vaddr 的 so */
        return (Il2CppType *)(g_so + va);
    return NULL;
}

/* 按 vaddr 取 Il2CppType（ARRAY/PTR/SZARRAY 的 data 存的是指针） */
static Il2CppType *tptr(uint64_t va) {
    if (!va) return NULL;
    uint64_t off = va2off(va);
    if (off == (uint64_t)-1) return NULL;
    if (off + 16 > g_so_sz) return NULL;
    return (Il2CppType *)(g_so + off);
}
static int tdef_ok(int32_t i) { return i >= 0 && i < g_tdefs_n; }
static uint8_t *tdef(int32_t i) { return g_tdefs + (uint64_t)i * g_tdef_stride; }

/* Il2CppTypeDefinition 字段偏移（v24~v31 前缀一致） */
#define TD_NAME(i)     R32(tdef(i) + 0x00)
#define TD_NS(i)       R32(tdef(i) + 0x04)
#define TD_BYVAL(i)    R32(tdef(i) + 0x08)
#define TD_DECLARING(i) R32(tdef(i) + 0x0C)
#define TD_PARENT(i)   R32(tdef(i) + 0x10)
#define TD_FLAGS(i)    RU32(tdef(i) + 0x1C)
#define TD_FSTART(i)   R32(tdef(i) + 0x20)
#define TD_MSTART(i)   R32(tdef(i) + 0x24)
#define TD_PSTART(i)   R32(tdef(i) + 0x2C)
#define TD_IFSTART(i)  R32(tdef(i) + 0x34)
#define TD_MCNT(i)     RU16(tdef(i) + 0x40)
#define TD_PCNT(i)     RU16(tdef(i) + 0x42)
#define TD_FCNT(i)     RU16(tdef(i) + 0x44)
#define TD_ESTART(i)   R32(tdef(i) + 0x28)
#define TD_NSTART(i)   R32(tdef(i) + 0x30)
#define TD_ISTART(i)   R32(tdef(i) + 0x34)
#define TD_ECNT(i)     RU16(tdef(i) + 0x46)
#define TD_NCNT(i)     RU16(tdef(i) + 0x48)
#define TD_ICNT(i)     RU16(tdef(i) + 0x4C)

static const char *class_name(int32_t tdi) {
    if (!tdef_ok(tdi)) return "";
    return S(TD_NAME(tdi));
}
static const char *class_ns(int32_t tdi) {
    if (!tdef_ok(tdi)) return "";
    return S(TD_NS(tdi));
}

/* 递归解析类型名 */
static Il2CppType *tptr(uint64_t va);
static void tname_core(Il2CppType *t, char *out, size_t cap, int depth);

static void tname_p(uint64_t va, char *out, size_t cap, int depth) {
    tname_core(tptr(va), out, cap, depth);
}
static void tname(int32_t typeIndex, char *out, size_t cap, int depth) {
    tname_core(ty(typeIndex), out, cap, depth);
}

/* 泛型实例展开 */
static void gen_inst(uint64_t gcva, char *out, size_t cap, int depth) {
    out[0] = 0;
    uint64_t o = va2off(gcva);
    if (o == (uint64_t)-1 || o + 16 > g_so_sz) return;
    int32_t def = *(int32_t *)(g_so + o);
    uint64_t instva = *(uint64_t *)(g_so + o + 8);
    const char *nm = class_name(def);
    size_t n = (size_t)snprintf(out, cap, "%s", nm && *nm ? nm : "?");

    uint64_t io = va2off(instva);
    if (io == (uint64_t)-1 || io + 16 > g_so_sz) return;
    uint64_t argc = *(uint64_t *)(g_so + io);
    uint64_t argv = *(uint64_t *)(g_so + io + 8);
    if (argc == 0 || argc > 8) return;
    uint64_t ao = va2off(argv);
    if (ao == (uint64_t)-1) return;

    if (n < cap - 2) out[n++] = '<';
    for (uint64_t k = 0; k < argc && n < cap - 2; k++) {
        if (k) { out[n++] = ','; }
        uint64_t pa = *(uint64_t *)(g_so + ao + k * 8);
        char a[200];
        tname_p(pa, a, sizeof a, depth + 1);
        n += (size_t)snprintf(out + n, cap - n, "%s", a);
    }
    if (n < cap - 1) out[n++] = '>';
    out[n] = 0;
}

static void tname_core(Il2CppType *t, char *out, size_t cap, int depth) {
    if (depth > 6 || !t) { snprintf(out, cap, "?"); return; }
    uint32_t ty_ = (uint32_t)((t->bits >> 16) & 0xFF);
    switch (ty_) {
        case T_VOID:   snprintf(out, cap, "void"); return;
        case T_BOOLEAN:snprintf(out, cap, "bool"); return;
        case T_CHAR:   snprintf(out, cap, "char"); return;
        case T_I1:     snprintf(out, cap, "sbyte"); return;
        case T_U1:     snprintf(out, cap, "byte"); return;
        case T_I2:     snprintf(out, cap, "short"); return;
        case T_U2:     snprintf(out, cap, "ushort"); return;
        case T_I4:     snprintf(out, cap, "int"); return;
        case T_U4:     snprintf(out, cap, "uint"); return;
        case T_I8:     snprintf(out, cap, "long"); return;
        case T_U8:     snprintf(out, cap, "ulong"); return;
        case T_R4:     snprintf(out, cap, "float"); return;
        case T_R8:     snprintf(out, cap, "double"); return;
        case T_STRING: snprintf(out, cap, "string"); return;
        case T_OBJECT: snprintf(out, cap, "object"); return;
        case T_I:      snprintf(out, cap, "IntPtr"); return;
        case T_U:      snprintf(out, cap, "UIntPtr"); return;
        case T_TYPEDBYREF: snprintf(out, cap, "TypedReference"); return;
        case T_VAR: case T_MVAR: snprintf(out, cap, "T"); return;
        case T_FNPTR:  snprintf(out, cap, "fnptr"); return;
    }
    if (ty_ == T_CLASS || ty_ == T_VALUETYPE) {
        const char *nm = class_name((int32_t)t->data);
        snprintf(out, cap, "%s", nm && *nm ? nm : (ty_ == T_VALUETYPE ? "valuetype" : "class"));
        return;
    }
    if (ty_ == T_SZARRAY || ty_ == T_PTR || ty_ == T_BYREF) {
        char e[256];
        tname_p((uint64_t)t->data, e, sizeof e, depth + 1);
        snprintf(out, cap, "%s%s", e,
                 ty_ == T_SZARRAY ? "[]" : (ty_ == T_PTR ? "*" : "&"));
        return;
    }
    if (ty_ == T_ARRAY) {
        /* data -> Il2CppArrayType { const Il2CppType* etype; uint8_t rank; ... } */
        uint64_t ao = va2off((uint64_t)t->data);
        if (ao != (uint64_t)-1 && ao + 16 <= g_so_sz) {
            uint64_t eva = *(uint64_t *)(g_so + ao);
            uint32_t rank = *(uint8_t *)(g_so + ao + 8);
            char e[256];
            tname_p(eva, e, sizeof e, depth + 1);
            char rb[16] = "";
            if (rank == 0) rank = 1;
            for (uint32_t k = 0; k < rank && k < 8; k++) strcat(rb, ",");
            snprintf(out, cap, "%s[%s]", e, rb);
            return;
        }
        snprintf(out, cap, "[]");
        return;
    }
    if (ty_ == T_GENERICINST) {
        char g[900];
        gen_inst((uint64_t)t->data, g, sizeof g, depth);
        snprintf(out, cap, "%s", g[0] ? g : "Generic");
        return;
    }
    snprintf(out, cap, "?");
}

/* Il2CppMethodDefinition 字段偏移（v31 有 returnParameterToken，整体后移 4） */
#define MD_RET(mp)   R32((mp) + 0x08)
#define MD_PS(mp)    R32((mp) + (g_v31 ? 0x10 : 0x0C))
#define MD_TOK(mp)   RU32((mp) + (g_v31 ? 0x18 : 0x14))
#define MD_FLG(mp)   RU16((mp) + (g_v31 ? 0x1C : 0x18))
#define MD_SLOT(mp)  RU16((mp) + (g_v31 ? 0x20 : 0x1C))
#define MD_PCNT(mp)  RU16((mp) + (g_v31 ? 0x22 : 0x1E))

/* ======================= 修饰符 ======================= */
#define FIELD_ATTR_FIELD_ACCESS_MASK 0x0007
#define FIELD_ATTR_PRIVATE   0x0001
#define FIELD_ATTR_FAMILY    0x0004
#define FIELD_ATTR_ASSEMBLY  0x0003
#define FIELD_ATTR_FAM_AND_ASSEM 0x0002
#define FIELD_ATTR_FAM_OR_ASSEM  0x0005
#define FIELD_ATTR_PUBLIC    0x0006
#define FIELD_ATTR_STATIC    0x0010
#define FIELD_ATTR_INIT_ONLY 0x0020
#define FIELD_ATTR_LITERAL   0x0040

#define METHOD_ATTR_ACCESS_MASK 0x0007
#define METHOD_ATTR_PRIVATE   0x0001
#define METHOD_ATTR_FAMILY    0x0004
#define METHOD_ATTR_ASSEM     0x0003
#define METHOD_ATTR_FAM_AND_ASSEM 0x0002
#define METHOD_ATTR_FAM_OR_ASSEM  0x0005
#define METHOD_ATTR_PUBLIC    0x0006
#define METHOD_ATTR_STATIC    0x0010
#define METHOD_ATTR_FINAL     0x0020
#define METHOD_ATTR_VIRTUAL   0x0040
#define METHOD_ATTR_VTABLE_MASK 0x0100
#define METHOD_ATTR_NEW_SLOT  0x0100
#define METHOD_ATTR_ABSTRACT  0x0400
#define METHOD_ATTR_PINVOKE   0x2000

#define TYPE_ATTR_VISIBILITY_MASK 0x00000007
#define TYPE_ATTR_NOT_PUBLIC   0x00000000
#define TYPE_ATTR_PUBLIC       0x00000001
#define TYPE_ATTR_NESTED_PUBLIC 0x00000002
#define TYPE_ATTR_NESTED_PRIVATE 0x00000003
#define TYPE_ATTR_NESTED_FAMILY 0x00000004
#define TYPE_ATTR_NESTED_ASSEMBLY 0x00000005
#define TYPE_ATTR_NESTED_FAM_AND_ASSEM 0x00000006
#define TYPE_ATTR_NESTED_FAM_OR_ASSEM  0x00000007
#define TYPE_ATTR_SERIALIZABLE 0x00002000
#define TYPE_ATTR_ABSTRACT     0x00000080
#define TYPE_ATTR_SEALED       0x00000100
#define TYPE_ATTR_INTERFACE    0x00000020

static void field_mod(char *o, size_t cap, uint32_t a) {
    o[0] = 0;
    switch (a & FIELD_ATTR_FIELD_ACCESS_MASK) {
        case FIELD_ATTR_PRIVATE:    strncat(o, "private ", cap-1); break;
        case FIELD_ATTR_FAMILY:     strncat(o, "protected ", cap-1); break;
        case FIELD_ATTR_ASSEMBLY:
        case FIELD_ATTR_FAM_AND_ASSEM: strncat(o, "internal ", cap-1); break;
        case FIELD_ATTR_FAM_OR_ASSEM:  strncat(o, "protected internal ", cap-1); break;
        case FIELD_ATTR_PUBLIC:     strncat(o, "public ", cap-1); break;
    }
    if (a & FIELD_ATTR_LITERAL) strncat(o, "const ", cap-1);
    else {
        if (a & FIELD_ATTR_STATIC)    strncat(o, "static ", cap-1);
        if (a & FIELD_ATTR_INIT_ONLY) strncat(o, "readonly ", cap-1);
    }
}

static void method_mod(char *o, size_t cap, uint32_t f) {
    o[0] = 0;
    switch (f & METHOD_ATTR_ACCESS_MASK) {
        case METHOD_ATTR_PRIVATE:   strncat(o, "private ", cap-1); break;
        case METHOD_ATTR_FAMILY:    strncat(o, "protected ", cap-1); break;
        case METHOD_ATTR_ASSEM:
        case METHOD_ATTR_FAM_AND_ASSEM: strncat(o, "internal ", cap-1); break;
        case METHOD_ATTR_FAM_OR_ASSEM:  strncat(o, "protected internal ", cap-1); break;
        case METHOD_ATTR_PUBLIC:    strncat(o, "public ", cap-1); break;
    }
    if (f & METHOD_ATTR_STATIC) strncat(o, "static ", cap-1);
    if (f & METHOD_ATTR_ABSTRACT) {
        strncat(o, "abstract ", cap-1);
        if ((f & METHOD_ATTR_VTABLE_MASK) == 0) strncat(o, "override ", cap-1);
    } else if (f & METHOD_ATTR_FINAL) {
        if ((f & METHOD_ATTR_VTABLE_MASK) == 0) strncat(o, "sealed override ", cap-1);
    } else if (f & METHOD_ATTR_VIRTUAL) {
        strncat(o, (f & METHOD_ATTR_VTABLE_MASK) == METHOD_ATTR_NEW_SLOT
                   ? "virtual " : "override ", cap-1);
    }
    if (f & METHOD_ATTR_PINVOKE) strncat(o, "extern ", cap-1);
}

/* ======================= 输出 ======================= */
static void dump_fields(FILE *o, int32_t tdi) {
    fprintf(o, "\n\t// Fields\n");
    int32_t start = TD_FSTART(tdi), cnt = TD_FCNT(tdi);
    for (int32_t i = 0; i < cnt; i++) {
        int32_t fi = start + i;
        if (fi < 0 || fi >= g_fields_n) break;
        uint8_t *fd = g_fields + (uint64_t)fi * g_field_stride;
        int32_t nameIdx = R32(fd + 0x00);
        int32_t typeIdx = R32(fd + 0x04);

        /* 字段 flags 只能从 Il2CppType.attrs 拿到 */
        Il2CppType *ft = ty(typeIdx);
        uint32_t attrs = ft ? (ft->bits & 0xFFFF) : 0;
        char mod[64]; field_mod(mod, sizeof mod, attrs);
        char tn[300]; tname(typeIdx, tn, sizeof tn, 0);
        {
            Il2CppType *bv = ty(TD_BYVAL(tdi));
            int is_vt = bv && (((bv->bits >> 16) & 0xFF) == T_VALUETYPE);
            int is_st = (attrs & 0x0010) != 0;   /* FieldAttributes.Static */
            int32_t fo = field_offset(tdi, i, is_vt, is_st);
            if (fo >= 0)
                fprintf(o, "\t%s%s %s; // 0x%x\n", mod, tn, S(nameIdx), fo);
            else
                fprintf(o, "\t%s%s %s;\n", mod, tn, S(nameIdx));
        }
    }
}

/* Il2CppEventDefinition: name@0 type@4 add@8 remove@0xC raise@0x10 token@0x14 */
static void dump_events(FILE *o, int32_t tdi) {
    int32_t start = TD_ESTART(tdi), cnt = TD_ECNT(tdi);
    if (cnt <= 0) return;
    fprintf(o, "\n\t// Events\n");
    for (int32_t i = 0; i < cnt; i++) {
        int32_t ei = start + i;
        if (ei < 0 || ei >= g_events_n) break;
        uint8_t *ed = g_events + (uint64_t)ei * g_event_stride;
        int32_t nameIdx = R32(ed + 0x00);
        int32_t typeIdx = R32(ed + 0x04);
        int32_t addRel  = R32(ed + 0x08);
        int32_t remRel  = R32(ed + 0x0C);
        char tn[300]; tname(typeIdx, tn, sizeof tn, 0);
        char mod[64]; mod[0] = 0;
        int32_t mi = TD_MSTART(tdi) + (addRel >= 0 ? addRel : remRel);
        if (mi >= 0 && mi < g_methods_n) {
            uint8_t *mp = g_methods + (uint64_t)mi * g_method_stride;
            method_mod(mod, sizeof mod, MD_FLG(mp));
        }
        fprintf(o, "\t%sevent %s %s { %s%s}\n", mod, tn, S(nameIdx),
                addRel >= 0 ? "add; " : "", remRel >= 0 ? "remove; " : "");
    }
}

/* nestedTypes: int32 tdef 索引数组 */
static void dump_nested(FILE *o, int32_t tdi) {
    int32_t start = TD_NSTART(tdi), cnt = TD_NCNT(tdi);
    if (cnt <= 0) return;
    fprintf(o, "\n\t// Nested Types\n");
    for (int32_t i = 0; i < cnt; i++) {
        int32_t ni = start + i;
        int32_t nt = R32(g_nested + (uint64_t)ni * 4);
        if (nt < 0 || nt >= g_tdefs_n) continue;
        uint32_t f = TD_FLAGS(nt);
        const char *nm = class_name(nt);
        const char *vis = "public ";
        switch (f & TYPE_ATTR_VISIBILITY_MASK) {
            case TYPE_ATTR_NESTED_PRIVATE: vis = "private "; break;
            case TYPE_ATTR_NESTED_FAMILY:  vis = "protected "; break;
            case TYPE_ATTR_NESTED_FAM_OR_ASSEM: vis = "protected internal "; break;
            case TYPE_ATTR_PUBLIC:
            case TYPE_ATTR_NESTED_PUBLIC:  vis = "public "; break;
            default: vis = "internal "; break;
        }
        fprintf(o, "\t%s%s %s\n", vis,
                (f & TYPE_ATTR_INTERFACE) ? "interface" : "class", nm && *nm ? nm : "?");
    }
}

/* interfaces: int32 typeIndex 数组 */
static void dump_interfaces(FILE *o, int32_t tdi) {
    int32_t start = TD_ISTART(tdi), cnt = TD_ICNT(tdi);
    if (cnt <= 0) return;
    fprintf(o, "\n\t// Interfaces\n");
    for (int32_t i = 0; i < cnt; i++) {
        int32_t ii = start + i;
        int32_t ti = R32(g_ifaces + (uint64_t)ii * 4);
        char tn[300]; tname(ti, tn, sizeof tn, 0);
        fprintf(o, "\t// %s\n", tn);
    }
}

static void dump_props(FILE *o, int32_t tdi) {
    fprintf(o, "\n\t// Properties\n");
    int32_t start = TD_PSTART(tdi), cnt = TD_PCNT(tdi);
    for (int32_t i = 0; i < cnt; i++) {
        int32_t pi = start + i;
        if (pi < 0 || pi >= g_props_n) break;
        uint8_t *pd = g_props + (uint64_t)pi * g_prop_stride;
        int32_t nameIdx = R32(pd + 0x00);
        int32_t getIdx  = R32(pd + 0x04);
        int32_t setIdx  = R32(pd + 0x08);

        int32_t rel = (getIdx >= 0) ? getIdx : setIdx;
        if (rel < 0) continue;
        int32_t mi = TD_MSTART(tdi) + rel;      /* get/set 是类内相对索引 */
        if (mi < 0 || mi >= g_methods_n) continue;
        uint8_t *mp = g_methods + (uint64_t)mi * g_method_stride;

        uint32_t mflags = MD_FLG(mp);
        char mod[64]; method_mod(mod, sizeof mod, mflags);

        char tn[300];
        if (getIdx >= 0) {
            int32_t rt = MD_RET(mp);
            tname(rt, tn, sizeof tn, 0);
        } else {
            int32_t pstart = MD_PS(mp);
            int32_t pt = -1;
            if (pstart >= 0 && pstart < g_params_n) {
                uint8_t *pp = g_params + (uint64_t)pstart * g_param_stride;
                pt = R32(pp + 0x08);
            }
            tname(pt, tn, sizeof tn, 0);
        }
        fprintf(o, "\t%s%s %s { %s%s}\n", mod, tn, S(nameIdx),
                getIdx >= 0 ? "get; " : "", setIdx >= 0 ? "set; " : "");
    }
}

static void dump_methods(FILE *o, int32_t tdi, const char *dll) {
    fprintf(o, "\n\t// Methods\n");
    int32_t start = TD_MSTART(tdi), cnt = TD_MCNT(tdi);
    for (int32_t i = 0; i < cnt; i++) {
        int32_t mi = start + i;
        if (mi < 0 || mi >= g_methods_n) break;
        uint8_t *mp = g_methods + (uint64_t)mi * g_method_stride;

        int32_t nameIdx  = R32(mp + 0x00);
        int32_t retType  = MD_RET(mp);
        int32_t pstart   = MD_PS(mp);
        uint32_t mflags  = MD_FLG(mp);
        uint16_t pcnt    = MD_PCNT(mp);

        char mod[64]; method_mod(mod, sizeof mod, mflags);
        char rt[300]; tname(retType, rt, sizeof rt, 0);

        /* 返回类型是 byref 时加 ref */
        Il2CppType *rtt = ty(retType);
        if (rtt && ((rtt->bits >> 30) & 1)) {
            char t2[320]; snprintf(t2, sizeof t2, "ref %s", rt);
            strncpy(rt, t2, sizeof rt - 1); rt[sizeof rt - 1] = 0;
        }

        {
            uint32_t tok = MD_TOK(mp);
            uint64_t mpv = method_ptr(dll, tok);
            if (mpv > 0) {
                uint64_t moff = va2off(mpv);
                fprintf(o, "\t// RVA: 0x%llx Offset: 0x%llx VA: 0x%llx\n",
                        (unsigned long long)mpv,
                        (unsigned long long)(moff == (uint64_t)-1 ? 0 : moff),
                        (unsigned long long)mpv);
            } else {
                fprintf(o, "\t// RVA: -1 Offset: -1\n");
            }
        }
        fprintf(o, "\t%s%s %s(", mod, rt, S(nameIdx));
        for (uint16_t p = 0; p < pcnt; p++) {
            int32_t pi = pstart + p;
            if (pi < 0 || pi >= g_params_n) break;
            uint8_t *pp = g_params + (uint64_t)pi * g_param_stride;
            int32_t pn = R32(pp + 0x00);
            int32_t ptIdx = R32(pp + 0x08);
            char tn[300]; tname(ptIdx, tn, sizeof tn, 0);
            Il2CppType *pt = ty(ptIdx);
            if (pt && ((pt->bits >> 30) & 1)) {
                char t2[320]; snprintf(t2, sizeof t2, "ref %s", tn);
                strncpy(tn, t2, sizeof tn - 1); tn[sizeof tn - 1] = 0;
            }
            fprintf(o, "%s%s %s", p ? ", " : "", tn, S(pn));
        }
        {
            uint16_t slot = MD_SLOT(mp);
            if (slot != 0xFFFF) fprintf(o, ") { } // Slot: %u\n", (unsigned)slot);
            else fprintf(o, ") { }\n");
        }
    }
}

static void dump_class(FILE *o, int32_t tdi, const char *dll_in) {
    char dllbuf[256];
    strncpy(dllbuf, dll_in ? dll_in : "", sizeof dllbuf - 1);
    dllbuf[sizeof dllbuf - 1] = 0;
    const char *dll = dllbuf;
    uint32_t flags = TD_FLAGS(tdi);
    const char *name = class_name(tdi);
    const char *ns   = class_ns(tdi);

    (void)dll;
    fprintf(o, "\n// Namespace: %s\n", ns);
    if (flags & TYPE_ATTR_SERIALIZABLE) fprintf(o, "[Serializable]\n");

    switch (flags & TYPE_ATTR_VISIBILITY_MASK) {
        case TYPE_ATTR_PUBLIC:
        case TYPE_ATTR_NESTED_PUBLIC:  fprintf(o, "public "); break;
        case TYPE_ATTR_NESTED_PRIVATE: fprintf(o, "private "); break;
        case TYPE_ATTR_NESTED_FAMILY:  fprintf(o, "protected "); break;
        case TYPE_ATTR_NESTED_FAM_OR_ASSEM: fprintf(o, "protected internal "); break;
        default: fprintf(o, "internal "); break;
    }
    {
        Il2CppType *bvc = ty(TD_BYVAL(tdi));
        int bvtc = bvc ? (int)((bvc->bits >> 16) & 0xFF) : -1;
        uint32_t bitf = RU32(tdef(tdi) + 0x54);        /* bitfield: bit1 = enumtype */
        int is_struct = (bvtc == 17);
        int is_enum   = is_struct && ((bitf >> 1) & 1);
        if (!is_struct) {
            if ((flags & TYPE_ATTR_ABSTRACT) && (flags & TYPE_ATTR_SEALED)) fprintf(o, "static ");
            else if (!(flags & TYPE_ATTR_INTERFACE) && (flags & TYPE_ATTR_ABSTRACT)) fprintf(o, "abstract ");
            else if (flags & TYPE_ATTR_SEALED) fprintf(o, "sealed ");
        }
        if (flags & TYPE_ATTR_INTERFACE)      fprintf(o, "interface ");
        else if (is_enum)                     fprintf(o, "enum ");
        else if (is_struct)                   fprintf(o, "struct ");
        else                                  fprintf(o, "class ");
    }

    fprintf(o, "%s // TypeDefIndex: %d", (*name ? name : "cls_?"), tdi);

    /* 父类 */
    int32_t par = TD_PARENT(tdi);
    if (par >= 0 && tdef_ok(par) && !(flags & TYPE_ATTR_INTERFACE)) {
        const char *pn = class_name(par);
        if (pn && *pn && strcmp(pn, "Object") && strcmp(pn, "<Module>"))
            fprintf(o, " : %s", pn);
    }
    fprintf(o, "\n{");
    dump_fields(o, tdi);
    dump_props(o, tdi);
    dump_events(o, tdi);
    dump_nested(o, tdi);
    dump_interfaces(o, tdi);
    dump_methods(o, tdi, dll);
    fprintf(o, "}\n");
}

/* ======================= 主流程 ======================= */
int main(void) {
    fprintf(stderr, "=== icdump_static ===\n");

    g_so = read_all(SO_PATH, &g_so_sz);
    if (!g_so) return 1;
    g_md = read_all(MD_PATH, &g_md_sz);
    if (!g_md) return 1;
    fprintf(stderr, "[*] so=%zu bytes  metadata=%zu bytes\n", g_so_sz, g_md_sz);

    if (elf_load()) return 1;
    apply_relocations();          /* 未 dump 的 so 必须先做重定位 */

    /* ---- 特征自检 ---- */
    {
        int cnt_msc = 0, cnt_il2cpp = 0;
        for (size_t i = 0; i + 12 <= g_so_sz; i++) {
            if (!memcmp(g_so + i, "mscorlib.dll", 12)) cnt_msc++;
            if (!memcmp(g_so + i, "il2cpp", 6)) cnt_il2cpp++;
        }
        fprintf(stderr, "[*] 特征: \"mscorlib.dll\" x%d  \"il2cpp\" x%d\n", cnt_msc, cnt_il2cpp);
        int nsec = 0;
        for (int i = 0; i < g_phn; i++) if (g_ph[i].type == 2) nsec++;
        fprintf(stderr, "[*] PT_DYNAMIC 段数=%d\n", nsec);
    }
    if (md_load()) return 1;
    if (find_types()) return 1;
    classify_segments();
    if (find_code_registration()) {
        fprintf(stderr, "[*] CodeRegistration @ so+0x%llx",
                (unsigned long long)va2off(g_cr));
        if (load_code_modules()) {
            fprintf(stderr, "  modules=%d\n", g_nmod);
            /* ---- 配对校验：metadata.images 与 so.codeGenModules 逐名比对 ---- */
            int mt = 0, miss = 0;
            for (int32_t ii = 0; ii < g_images_n; ii++) {
                uint8_t *im = g_images + (uint64_t)ii * g_image_stride;
                char iname[256];
                strncpy(iname, S(R32(im + 0x00)), sizeof iname - 1);
                iname[sizeof iname - 1] = 0;
                int found = 0;
                for (int q = 0; q < g_nmod; q++)
                    if (g_mod[q].name && !strcmp(g_mod[q].name, iname)) { found = 1; break; }
                if (found) mt++;
                else {
                    if (miss < 5) fprintf(stderr, "  [x] image 无对应模块: %s\n", iname);
                    miss++;
                }
            }
            fprintf(stderr, "[*] 配对校验: images=%d modules=%d 匹配=%d 缺失=%d -> %s\n",
                    g_images_n, g_nmod, mt, miss,
                    miss == 0 ? "配对正确" : "!! so 与 metadata 不匹配 !!");
        }
        else
            fprintf(stderr, "  [模块表读取失败]\n");
    } else {
        fprintf(stderr, "[!] CodeRegistration 未找到，RVA 不可用\n");
    }

    /* 内嵌名称去重：直接用 images 表遍历 */
    FILE *o = fopen(OUT_PATH, "w");
    if (!o) { fprintf(stderr, "[!] 无法写 %s\n", OUT_PATH); return 1; }

    uint64_t total = 0;
    /* 头部：所有 image 的起始 TypeDefIndex */
    for (int32_t i = 0; i < g_images_n; i++) {
        uint8_t *im = g_images + (uint64_t)i * g_image_stride;
        int32_t nameIdx   = R32(im + 0x00);
        int32_t typeStart = R32(im + 0x08);
        fprintf(o, "// Image %d: %s - %d\n", i, S(nameIdx), typeStart);
    }
    for (int32_t i = 0; i < g_images_n; i++) {
        uint8_t *im = g_images + (uint64_t)i * g_image_stride;
        int32_t nameIdx   = R32(im + 0x00);
        int32_t typeStart = R32(im + 0x08);
        uint32_t typeCount = RU32(im + 0x0C);
        char dllbuf[256];
        strncpy(dllbuf, S(nameIdx), sizeof dllbuf - 1);
        dllbuf[sizeof dllbuf - 1] = 0;
        const char *dll = dllbuf;

        /* 类头由 dump_class 输出 */
        fprintf(stderr, "    %-40s %u\n", dll, typeCount);

        for (uint32_t j = 0; j < typeCount; j++) {
            int32_t tdi = typeStart + (int32_t)j;
            if (!tdef_ok(tdi)) break;
            dump_class(o, tdi, dll);
            total++;
            if ((total & 0x1FF) == 0 && ftell(o) > (long)(192L * 1024 * 1024)) {
                fprintf(stderr, "[!] 输出超过 192MB，疑似索引异常，中止\n");
                goto dump_done;
            }
        }
    }
dump_done:
    fclose(o);

    fprintf(stderr, "[+] 完成: %llu 个类型 -> %s\n",
            (unsigned long long)total, OUT_PATH);
    free(g_so); free(g_md); free(g_ph);
    return 0;
}