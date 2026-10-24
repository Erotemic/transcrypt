/*
 * A fixed-width symbolic proof of the RFC 4648 Base64 byte/sextet core.
 *
 * The unaltered bit expressions correspond to production Rust functions
 * split_triple and join_quartet in rust/.../src/base64_bits.rs.
 * This harness uses Z3's QF_BV solver to establish UNSAT of each negated
 * theorem for ALL bytes / valid sextets, not random test inputs.
 *
 * This proves the mathematical core under Z3's bit-vector semantics.
 * It does NOT establish compiler/translator correctness or the full Rust
 * parser's behavior, nor does it establish any cryptographic security.
 *
 * Minimal stable declarations from the Z3 C API permit compilation on
 * developer systems that have libz3.so but not the optional z3.h header.
 * In CI libz3-dev is installed and this file is also compiled with warnings
 * treated as errors. No libz3 runtime dependency is added to Transcrypt.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct _Z3_config *Z3_config;
typedef struct _Z3_context *Z3_context;
typedef struct _Z3_sort *Z3_sort;
typedef struct _Z3_symbol *Z3_symbol;
typedef struct _Z3_ast *Z3_ast;
typedef struct _Z3_solver *Z3_solver;
typedef enum { Z3_L_FALSE = -1, Z3_L_UNDEF = 0, Z3_L_TRUE = 1 } Z3_lbool;
extern Z3_config Z3_mk_config(void);
extern void Z3_del_config(Z3_config);
extern Z3_context Z3_mk_context(Z3_config);
extern void Z3_del_context(Z3_context);
extern Z3_sort Z3_mk_bv_sort(Z3_context, unsigned);
extern Z3_symbol Z3_mk_string_symbol(Z3_context, const char *);
extern Z3_ast Z3_mk_const(Z3_context, Z3_symbol, Z3_sort);
extern Z3_ast Z3_mk_numeral(Z3_context, const char *, Z3_sort);
extern Z3_ast Z3_mk_concat(Z3_context, Z3_ast, Z3_ast);
extern Z3_ast Z3_mk_bvand(Z3_context, Z3_ast, Z3_ast);
extern Z3_ast Z3_mk_bvor(Z3_context, Z3_ast, Z3_ast);
extern Z3_ast Z3_mk_bvshl(Z3_context, Z3_ast, Z3_ast);
extern Z3_ast Z3_mk_bvlshr(Z3_context, Z3_ast, Z3_ast);
extern Z3_ast Z3_mk_zero_ext(Z3_context, unsigned, Z3_ast);
extern Z3_ast Z3_mk_extract(Z3_context, unsigned, unsigned, Z3_ast);
extern Z3_ast Z3_mk_eq(Z3_context, Z3_ast, Z3_ast);
extern Z3_ast Z3_mk_not(Z3_context, Z3_ast);
extern Z3_solver Z3_mk_solver(Z3_context);
extern void Z3_solver_inc_ref(Z3_context, Z3_solver);
extern void Z3_solver_dec_ref(Z3_context, Z3_solver);
extern void Z3_solver_reset(Z3_context, Z3_solver);
extern void Z3_solver_assert(Z3_context, Z3_solver, Z3_ast);
extern Z3_lbool Z3_solver_check(Z3_context, Z3_solver);
extern const char *Z3_solver_get_reason_unknown(Z3_context, Z3_solver);
extern void Z3_get_version(unsigned *, unsigned *, unsigned *, unsigned *);

static Z3_context ctx;
static Z3_solver solver;
static unsigned proved;

static Z3_ast bits(const char *name, unsigned width) {
    return Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name),
                       Z3_mk_bv_sort(ctx, width));
}
static Z3_ast constant(unsigned width, unsigned value) {
    char decimal[32];
    snprintf(decimal, sizeof(decimal), "%u", value);
    return Z3_mk_numeral(ctx, decimal, Z3_mk_bv_sort(ctx, width));
}
static Z3_ast zero(unsigned width) { return constant(width, 0); }
static Z3_ast band(Z3_ast a, Z3_ast b) { return Z3_mk_bvand(ctx, a, b); }
static Z3_ast bor(Z3_ast a, Z3_ast b) { return Z3_mk_bvor(ctx, a, b); }
static Z3_ast shl(Z3_ast a, unsigned n) {
    return Z3_mk_bvshl(ctx, a, constant(8, n));
}
static Z3_ast shr(Z3_ast a, unsigned n) {
    return Z3_mk_bvlshr(ctx, a, constant(8, n));
}
static Z3_ast take(Z3_ast value, unsigned hi, unsigned lo) {
    return Z3_mk_extract(ctx, hi, lo, value);
}
static Z3_ast cat(Z3_ast a, Z3_ast b) {
    return Z3_mk_concat(ctx, a, b);
}
static Z3_ast eq(Z3_ast a, Z3_ast b) { return Z3_mk_eq(ctx, a, b); }
static void assume(Z3_ast condition) {
    Z3_solver_assert(ctx, solver, condition);
}
static void not_equal(Z3_ast a, Z3_ast b) {
    assume(Z3_mk_not(ctx, eq(a, b)));
}
static void finish(const char *name) {
    Z3_lbool result = Z3_solver_check(ctx, solver);
    if (result != Z3_L_FALSE) {
        fprintf(stderr, "FAIL: %s: expected UNSAT, got %s\n", name,
                result == Z3_L_TRUE ? "SAT (counterexample)" :
                Z3_solver_get_reason_unknown(ctx, solver));
        exit(1);
    }
    ++proved;
    printf("PROVED (UNSAT): %s\n", name);
    Z3_solver_reset(ctx, solver);
}

static Z3_ast triple(Z3_ast a, Z3_ast b, Z3_ast c) {
    return cat(a, cat(b, c));
}
static Z3_ast quartet(Z3_ast s0, Z3_ast s1, Z3_ast s2, Z3_ast s3) {
    return cat(s0, cat(s1, cat(s2, s3)));
}
/* Model split_triple: (a>>2), ((a&3)<<4)|(b>>4),
 * ((b&15)<<2)|(c>>6), (c&63). These expressions are equivalently
 * bit-slices of a || b || c. Their correspondence to the Rust source
 * is a separately reviewable (currently manual) source-to-model step.
 */
static Z3_ast split(Z3_ast a, Z3_ast b, Z3_ast c) {
    Z3_ast abc = triple(a, b, c);
    return quartet(take(abc, 23, 18), take(abc, 17, 12),
                   take(abc, 11, 6), take(abc, 5, 0));
}
/* Model join_quartet, with no alphabet or padding handling. */
static Z3_ast join(Z3_ast s0, Z3_ast s1, Z3_ast s2, Z3_ast s3) {
    Z3_ast a = cat(s0, take(s1, 5, 4));
    Z3_ast b = cat(take(s1, 3, 0), take(s2, 5, 2));
    Z3_ast c = cat(take(s2, 1, 0), s3);
    return triple(a, b, c);
}

int main(void) {
    unsigned maj, min, patch, rev;
    Z3_get_version(&maj, &min, &patch, &rev);
    printf("Z3 %u.%u.%u (rev %u)\n", maj, min, patch, rev);
    Z3_config cfg = Z3_mk_config();
    ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);

    Z3_ast a = bits("a", 8), b = bits("b", 8), c = bits("c", 8);
    Z3_ast packed = triple(a, b, c);
    Z3_ast s0 = take(packed, 23, 18);
    Z3_ast s1 = take(packed, 17, 12);
    Z3_ast s2 = take(packed, 11, 6);
    Z3_ast s3 = take(packed, 5, 0);

    /* 2^24 possible triples, covered symbolically, not sampled. */
    not_equal(join(s0, s1, s2, s3), packed);
    finish("all 3-byte triples decode(encode(bytes)) = bytes");

    /* These 8-bit BV expressions are transliterations of actual Rust
     * source in split_triple. Establish that bit slicing is a faithful
     * model, including the left shifts and ORs in Rust's u8 domain. */
    Z3_ast r0 = shr(a, 2);
    Z3_ast r1 = bor(shl(band(a, constant(8, 3)), 4), shr(b, 4));
    Z3_ast r2 = bor(shl(band(b, constant(8, 15)), 2), shr(c, 6));
    Z3_ast r3 = band(c, constant(8, 63));
    Z3_ast rust_split = quartet(take(r0, 5, 0), take(r1, 5, 0),
                                take(r2, 5, 0), take(r3, 5, 0));
    not_equal(rust_split, split(a, b, c));
    finish("Rust split_triple bit expressions = independent bit-slice spec");

    /* The high two bits of every stored Rust sextet are always zero. */
    Z3_ast high_zero = cat(take(r0, 7, 6), cat(take(r1, 7, 6),
                              cat(take(r2, 7, 6), take(r3, 7, 6))));
    not_equal(high_zero, zero(8));
    finish("Rust split_triple sextets have range [0, 63]");

    /* All 2^24 four-sextet tuples are canonical (un-padded). */
    Z3_ast t0 = bits("t0", 6), t1 = bits("t1", 6);
    Z3_ast t2 = bits("t2", 6), t3 = bits("t3", 6);
    Z3_ast decoded = join(t0, t1, t2, t3);
    not_equal(split(take(decoded, 23, 16), take(decoded, 15, 8),
                    take(decoded, 7, 0)), quartet(t0, t1, t2, t3));
    finish("all full quartets encode(decode(sextets)) = sextets");

    /* As above, compare the literal Rust join_quartet u8 shifts/ORs
     * against the byte-concatenation specification. */
    Z3_ast q0 = Z3_mk_zero_ext(ctx, 2, t0);
    Z3_ast q1 = Z3_mk_zero_ext(ctx, 2, t1);
    Z3_ast q2 = Z3_mk_zero_ext(ctx, 2, t2);
    Z3_ast q3 = Z3_mk_zero_ext(ctx, 2, t3);
    Z3_ast d0 = bor(shl(q0, 2), shr(q1, 4));
    Z3_ast d1 = bor(shl(q1, 4), shr(q2, 2));
    Z3_ast d2 = bor(shl(q2, 6), q3);
    not_equal(triple(d0, d1, d2), decoded);
    finish("Rust join_quartet bit expressions = independent bit-slice spec");

    /* For 1 byte only the first two sextets are data; lower 4 bits of
     * s1 MUST be zero. Show no two canonical encodings share a byte. */
    Z3_ast u0 = bits("u0", 6), u1 = bits("u1", 6);
    assume(eq(take(u1, 3, 0), zero(4)));
    Z3_ast byte1 = cat(u0, take(u1, 5, 4));
    Z3_ast canonical1 = cat(take(byte1, 7, 2),
                            cat(take(byte1, 1, 0), zero(4)));
    not_equal(canonical1, cat(u0, u1));
    finish("1-byte Base64 padding: canonical symbols uniquely determined");

    /* For 2 bytes the third sextet must have zero low 2 bits. */
    Z3_ast v0 = bits("v0", 6), v1 = bits("v1", 6), v2 = bits("v2", 6);
    assume(eq(take(v2, 1, 0), zero(2)));
    Z3_ast byte2a = cat(v0, take(v1, 5, 4));
    Z3_ast byte2b = cat(take(v1, 3, 0), take(v2, 5, 2));
    Z3_ast pair = cat(byte2a, byte2b);
    /* Third sextet must end in two zero residual bits. */
    Z3_ast canonical2 = cat(take(pair, 15, 10),
                     cat(take(pair, 9, 4), cat(take(pair, 3, 0), zero(2))));
    not_equal(canonical2, cat(v0, cat(v1, v2)));
    finish("2-byte Base64 padding: canonical symbols uniquely determined");

    /* Directly verify 1-/2-byte tails produced by zero-fill split. */
    Z3_ast one = split(a, zero(8), zero(8));
    Z3_ast oneDecoded = join(take(one, 23, 18), take(one, 17, 12),
                             take(one, 11, 6), take(one, 5, 0));
    not_equal(take(oneDecoded, 23, 16), a);
    finish("all 1-byte tails roundtrip");
    Z3_ast two = split(a, b, zero(8));
    Z3_ast twoDecoded = join(take(two, 23, 18), take(two, 17, 12),
                             take(two, 11, 6), take(two, 5, 0));
    not_equal(take(twoDecoded, 23, 8), cat(a, b));
    finish("all 2-byte tails roundtrip");

    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);
    printf("SUCCESS: %u universal bit-vector obligations discharged\n", proved);
    return 0;
}
