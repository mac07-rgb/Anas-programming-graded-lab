// Mohammad Anas 251ADB003
// Resources and AI tools: ChatGPT (OpenAI), used for assistance
// understanding the arithmetic parser, debugging, and testing.
// Conversation history: https://chatgpt.com/share/6adee758-76bc-83eb-bff6-7ff088434788

#define _XOPEN_SOURCE 700

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

// ---- EDIT THESE: used to build output file / folder names (lowercase) ----
#define STUDENT_FIRST "Mohammad"
#define STUDENT_LAST  "Anas"
#define STUDENT_ID    "251ADB003"

// A value is either a 64-bit integer or a double. We keep the tag so that
// integer arithmetic stays exact (truncating division, integer powers) and
// switches to double only when a float is involved.
typedef struct {
    int is_float;
    long long i;
    double d;
} Value;

// The parser works directly on the whole-file buffer (no copying per line).
// Keeping the buffer start lets us compute absolute 1-based error positions
// as (pointer - buf) + 1, which counts every char including '\n' and comments.
typedef struct {
    char *buf;
    char *end;
    char *p;
    long err;   // 0 = no error yet, else 1-based position of the FIRST error
} Parser;

static void die_oom(void) {
    fprintf(stderr, "calc: out of memory\n");
    exit(1);
}

// Only the first error matters, so later calls are ignored once err is set.
static void fail(Parser *ps, const char *q) {
    if (!ps->err) ps->err = (long)(q - ps->buf) + 1;
}

// Spaces and tabs may appear anywhere between tokens.
static void skip_ws(Parser *ps) {
    while (ps->p < ps->end && (*ps->p == ' ' || *ps->p == '\t')) ps->p++;
}

// End of line = '\n' or end of file. In both cases the "position" of the end
// is the pointer itself, which gives file length + 1 when there is no final '\n'.
static int at_eol(const Parser *ps) {
    return ps->p >= ps->end || *ps->p == '\n';
}

static double as_double(Value v) {
    return v.is_float ? v.d : (double)v.i;
}

static Value make_int(long long i) {
    Value v = {0, i, 0.0};
    return v;
}

static Value make_float(double d) {
    Value v = {1, 0, d};
    return v;
}

// Float results must be finite; otherwise the error is reported at the operator.
static Value check_float(Parser *ps, double d, const char *op_pos) {
    if (!isfinite(d)) {
        fail(ps, op_pos);
        return make_int(0);
    }
    return make_float(d);
}

// ---------------------------------------------------------------- numbers
// NUMBER := digits | digits '.' digits
// The spec says ".5", "5." and "1.5e3" are NOT valid: a '.' needs at least one
// digit on BOTH sides, otherwise the error is at the '.'. There is no exponent
// notation, so an 'e' after a number is simply an invalid character that the
// caller reports at the 'e'. A number with a '.' is a float.
static Value parse_number(Parser *ps) {
    char *start = ps->p, *q = start;
    int int_digits = 0, is_float = 0;

    while (q < ps->end && isdigit((unsigned char)*q)) { q++; int_digits++; }

    if (q < ps->end && *q == '.') {
        char *dot = q;
        int frac_digits = 0;
        is_float = 1;
        q++;
        while (q < ps->end && isdigit((unsigned char)*q)) { q++; frac_digits++; }
        if (int_digits == 0 || frac_digits == 0) {
            fail(ps, dot);
            return make_int(0);
        }
    }

    ps->p = q;

    if (!is_float) {
        // Plain digit loop (no strtoll) so nothing but digits is ever accepted.
        long long v = 0;
        for (char *c = start; c < q; c++) v = v * 10 + (*c - '0');
        return make_int(v);
    }

    // strtod would happily read things like "0x1p3" or "inf" if we gave it the
    // rest of the buffer, so we cut the buffer at the end of OUR token first.
    char saved = *q;
    *q = '\0';
    double d = strtod(start, NULL);
    *q = saved;
    return check_float(ps, d, start);
}

// ------------------------------------------------------------ operations
// Integer power by squaring (O(log exp)), so huge exponents like 1 ** 10^12
// are fast. We only square the base while bits remain, so the base is never
// squared "one time too many" (which could overflow although the result fits).
static long long int_pow(long long base, long long exp) {
    long long result = 1;
    while (exp > 0) {
        if (exp & 1) result *= base;
        exp >>= 1;
        if (exp) base *= base;
    }
    return result;
}

static Value apply_pow(Parser *ps, Value a, Value b, const char *op_pos, const char *exp_pos) {
    if (!a.is_float && !b.is_float) {
        if (b.i < 0) {              // int ** negative int is not allowed
            fail(ps, exp_pos);
            return make_int(0);
        }
        return make_int(int_pow(a.i, b.i));
    }
    return check_float(ps, pow(as_double(a), as_double(b)), op_pos);
}

static Value apply_arith(Parser *ps, char op, Value a, Value b,
                         const char *op_pos, const char *rhs_pos) {
    if (op == '/') {
        // Division by zero (int or float) is reported at the start of the right operand.
        int zero = b.is_float ? (b.d == 0.0) : (b.i == 0);
        if (zero) {
            fail(ps, rhs_pos);
            return make_int(0);
        }
    }
    if (!a.is_float && !b.is_float) {
        switch (op) {
            case '+': return make_int(a.i + b.i);
            case '-': return make_int(a.i - b.i);
            case '*': return make_int(a.i * b.i);
            default:  return make_int(a.i / b.i);   // C truncation toward zero
        }
    }
    double x = as_double(a), y = as_double(b), r;
    switch (op) {
        case '+': r = x + y; break;
        case '-': r = x - y; break;
        case '*': r = x * y; break;
        default:  r = x / y; break;
    }
    return check_float(ps, r, op_pos);
}

// ---------------------------------------------------------------- grammar
//   expr    := term  { ('+'|'-') term }     left-associative
//   term    := power { ('*'|'/') power }    left-associative
//   power   := primary [ '**' power ]       RIGHT-associative: the right side
//                                           calls power again, so 2**3**2 is 2**(3**2)
//   primary := NUMBER | '(' expr ')'        no unary minus anywhere
// One function per precedence level gives the right precedence for free.
static Value parse_expr(Parser *ps);

static Value parse_primary(Parser *ps) {
    skip_ws(ps);
    if (at_eol(ps)) {                 // missing operand at end of line
        fail(ps, ps->p);
        return make_int(0);
    }
    char c = *ps->p;
    if (isdigit((unsigned char)c) || c == '.') return parse_number(ps);
    if (c == '(') {
        ps->p++;
        Value v = parse_expr(ps);
        if (ps->err) return v;
        skip_ws(ps);
        if (at_eol(ps) || *ps->p != ')') {   // missing ')' or junk inside parens
            fail(ps, ps->p);
            return make_int(0);
        }
        ps->p++;
        return v;
    }
    // Invalid character, or an operator where an operand was expected
    // ("7 + * 3": the second operator is where we cannot continue).
    fail(ps, ps->p);
    return make_int(0);
}

static Value parse_power(Parser *ps) {
    Value base = parse_primary(ps);
    if (ps->err) return base;
    skip_ws(ps);
    if (ps->p + 1 < ps->end && ps->p[0] == '*' && ps->p[1] == '*') {
        char *op_pos = ps->p;
        ps->p += 2;
        skip_ws(ps);
        char *exp_pos = ps->p;       // errors about the exponent point here
        Value e = parse_power(ps);   // recursion = right associativity
        if (ps->err) return e;
        return apply_pow(ps, base, e, op_pos, exp_pos);
    }
    return base;
}

static Value parse_term(Parser *ps) {
    Value left = parse_power(ps);
    while (!ps->err) {
        skip_ws(ps);
        if (ps->p >= ps->end) break;
        char c = *ps->p;
        // A single '*' is multiplication; "**" was already consumed by parse_power.
        int is_mul = (c == '*') && !(ps->p + 1 < ps->end && ps->p[1] == '*');
        if (!is_mul && c != '/') break;
        char *op_pos = ps->p;
        ps->p++;
        skip_ws(ps);
        char *rhs_pos = ps->p;
        Value right = parse_power(ps);
        if (ps->err) break;
        left = apply_arith(ps, c, left, right, op_pos, rhs_pos);
    }
    return left;
}

static Value parse_expr(Parser *ps) {
    Value left = parse_term(ps);
    while (!ps->err) {
        skip_ws(ps);
        if (ps->p >= ps->end) break;
        char c = *ps->p;
        if (c != '+' && c != '-') break;
        char *op_pos = ps->p;
        ps->p++;
        Value right = parse_term(ps);
        if (ps->err) break;
        left = apply_arith(ps, c, left, right, op_pos, op_pos);
    }
    return left;
}

// ------------------------------------------------------------ evaluation
// Growing output buffer (capacity doubles, so appending is amortised O(1) and
// big inputs are never copied repeatedly). We keep results in memory because
// if ANY error occurs the file must contain only that error, no partial results.
typedef struct {
    char *data;
    size_t len, cap;
} Buf;

static void buf_append(Buf *b, const char *s, size_t n) {
    if (b->len + n + 1 > b->cap) {
        size_t cap = b->cap ? b->cap : 4096;
        while (b->len + n + 1 > cap) cap *= 2;
        char *nd = realloc(b->data, cap);
        if (!nd) die_oom();
        b->data = nd;
        b->cap = cap;
    }
    memcpy(b->data + b->len, s, n);
    b->len += n;
    b->data[b->len] = '\0';
}

// Evaluate a whole file buffer (NUL-terminated at buf[len]). Result in *out.
static void evaluate(char *buf, size_t len, Buf *out) {
    Parser ps = {buf, buf + len, buf, 0};
    char tmp[64];

    while (ps.p < ps.end) {
        skip_ws(&ps);
        if (ps.p >= ps.end) break;
        if (*ps.p == '\n') { ps.p++; continue; }          // blank line: no output
        if (*ps.p == '#') {                               // comment only if '#' is the
            while (ps.p < ps.end && *ps.p != '\n') ps.p++; // first non-blank character
            continue;
        }

        Value v = parse_expr(&ps);
        if (!ps.err) {
            // Whatever is left on the line must be nothing. A stray ')' is the
            // "extra )" error; any other leftover (incl. a '#') is invalid.
            skip_ws(&ps);
            if (!at_eol(&ps)) fail(&ps, ps.p);
        }
        if (ps.err) {
            out->len = 0;                                 // drop partial results
            if (out->data) out->data[0] = '\0';
            int n = snprintf(tmp, sizeof tmp, "ERROR:%ld\n", ps.err);
            buf_append(out, tmp, (size_t)n);
            return;
        }

        int n;
        if (v.is_float) n = snprintf(tmp, sizeof tmp, "%.15g\n", v.d);
        else            n = snprintf(tmp, sizeof tmp, "%lld\n", v.i);
        buf_append(out, tmp, (size_t)n);
    }
}

// ------------------------------------------------------------- file helpers
// Read a whole file by doubling the buffer: we don't know the size in advance
// and doubling keeps the total copying work linear.
static int read_file(const char *path, char **data, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return -1;
    size_t cap = 65536, n = 0;
    char *b = malloc(cap + 1);
    if (!b) die_oom();
    for (;;) {
        size_t r = fread(b + n, 1, cap - n, f);
        n += r;
        if (n < cap) break;             // short read = EOF or error
        cap *= 2;
        char *nb = realloc(b, cap + 1);
        if (!nb) die_oom();
        b = nb;
    }
    int bad = ferror(f);
    fclose(f);
    if (bad) { free(b); return -1; }
    b[n] = '\0';                        // sentinel so look-ahead never leaves the buffer
    *data = b;
    *len = n;
    return 0;
}

static char *xstrdup(const char *s) {
    char *r = strdup(s);
    if (!r) die_oom();
    return r;
}

// Like `mkdir -p`: create every missing component. Existing folders are fine.
static int make_dirs(const char *path) {
    char *tmp = xstrdup(path);
    size_t n = strlen(tmp);
    while (n > 1 && tmp[n - 1] == '/') tmp[--n] = '\0';
    for (char *c = tmp + 1; *c; c++) {
        if (*c == '/') {
            *c = '\0';
            if (mkdir(tmp, 0777) != 0 && errno != EEXIST) { free(tmp); return -1; }
            *c = '/';
        }
    }
    int rc = 0;
    if (mkdir(tmp, 0777) != 0) {
        struct stat st;
        if (errno != EEXIST || stat(tmp, &st) != 0 || !S_ISDIR(st.st_mode)) rc = -1;
    }
    free(tmp);
    return rc;
}

// Last path component without trailing '/'. For "." / ".." we resolve the real
// folder name so the default output folder gets a meaningful name.
static char *base_name(const char *path) {
    char *copy = xstrdup(path);
    size_t n = strlen(copy);
    while (n > 1 && copy[n - 1] == '/') copy[--n] = '\0';
    char *slash = strrchr(copy, '/');
    char *base = (slash && n > 1) ? slash + 1 : copy;
    if (strcmp(base, ".") == 0 || strcmp(base, "..") == 0) {
        char *real = realpath(path, NULL);
        if (real) {
            free(copy);
            copy = real;
            slash = strrchr(copy, '/');
            base = (slash && slash[1]) ? slash + 1 : copy;
        }
    }
    char *r = xstrdup(base);
    free(copy);
    return r;
}

// Remove a trailing ".txt" (in place).
static void strip_txt(char *s) {
    size_t n = strlen(s);
    if (n > 4 && strcmp(s + n - 4, ".txt") == 0) s[n - 4] = '\0';
}

static char *join3(const char *a, const char *b, const char *c) {
    char *r = malloc(strlen(a) + strlen(b) + strlen(c) + 1);
    if (!r) die_oom();
    strcpy(r, a);
    strcat(r, b);
    strcat(r, c);
    return r;
}

// Evaluate one input file and write <outdir>/<stem>_<first>_<last>_<id>.txt
static int process_file(const char *in_path, const char *stem, const char *outdir) {
    char *data;
    size_t len;
    if (read_file(in_path, &data, &len) != 0) {
        fprintf(stderr, "calc: cannot read input file '%s': %s\n", in_path, strerror(errno));
        return -1;
    }
    Buf out = {NULL, 0, 0};
    evaluate(data, len, &out);
    free(data);

    if (make_dirs(outdir) != 0) {
        fprintf(stderr, "calc: cannot create output folder '%s': %s\n", outdir, strerror(errno));
        free(out.data);
        return -1;
    }
    char *name = join3(stem, "_" STUDENT_FIRST "_" STUDENT_LAST "_" STUDENT_ID, ".txt");
    char *dir_slash = join3(outdir, "/", name);
    FILE *f = fopen(dir_slash, "wb");
    int rc = 0;
    if (!f) {
        fprintf(stderr, "calc: cannot write '%s': %s\n", dir_slash, strerror(errno));
        rc = -1;
    } else {
        if (out.len && fwrite(out.data, 1, out.len, f) != out.len) rc = -1;
        if (fclose(f) != 0) rc = -1;
        if (rc) fprintf(stderr, "calc: write error on '%s'\n", dir_slash);
    }
    free(name);
    free(dir_slash);
    free(out.data);
    return rc;
}

static int cmp_str(const void *a, const void *b) {
    return strcmp(*(char *const *)a, *(char *const *)b);
}

// Process every *.txt FILE directly inside dir (no subfolders, other files ignored).
static int process_dir(const char *dir, const char *outdir) {
    DIR *d = opendir(dir);
    if (!d) {
        fprintf(stderr, "calc: cannot open folder '%s': %s\n", dir, strerror(errno));
        return -1;
    }
    char **names = NULL;
    size_t count = 0, cap = 0;
    struct dirent *e;
    while ((e = readdir(d)) != NULL) {
        size_t n = strlen(e->d_name);
        if (n <= 4 || strcmp(e->d_name + n - 4, ".txt") != 0) continue;
        char *full = join3(dir, "/", e->d_name);
        struct stat st;
        int ok = (stat(full, &st) == 0 && S_ISREG(st.st_mode));
        free(full);
        if (!ok) continue;
        if (count == cap) {
            cap = cap ? cap * 2 : 16;
            char **nn = realloc(names, cap * sizeof *names);
            if (!nn) die_oom();
            names = nn;
        }
        names[count++] = xstrdup(e->d_name);
    }
    closedir(d);
    qsort(names, count, sizeof *names, cmp_str);   // deterministic order

    int rc = 0;
    for (size_t k = 0; k < count && rc == 0; k++) {
        char *full = join3(dir, "/", names[k]);
        char *stem = xstrdup(names[k]);
        strip_txt(stem);
        rc = process_file(full, stem, outdir);
        free(full);
        free(stem);
    }
    for (size_t k = 0; k < count; k++) free(names[k]);
    free(names);
    return rc;
}

// ------------------------------------------------------------------- main
static int usage(const char *msg) {
    if (msg) fprintf(stderr, "calc: %s\n", msg);
    fprintf(stderr, "usage: calc [-d DIR | --dir DIR] [-o OUTDIR | --output-dir OUTDIR] [input.txt]\n");
    return 1;
}

int main(int argc, char **argv) {
    const char *dir = NULL, *outdir = NULL, *input = NULL;

    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        if (strcmp(a, "-d") == 0 || strcmp(a, "--dir") == 0) {
            if (i + 1 >= argc) return usage("option needs an argument: -d");
            if (dir) return usage("-d given twice");
            dir = argv[++i];
        } else if (strncmp(a, "--dir=", 6) == 0) {
            if (dir) return usage("-d given twice");
            dir = a + 6;
        } else if (strcmp(a, "-o") == 0 || strcmp(a, "--output-dir") == 0) {
            if (i + 1 >= argc) return usage("option needs an argument: -o");
            if (outdir) return usage("-o given twice");
            outdir = argv[++i];
        } else if (strncmp(a, "--output-dir=", 13) == 0) {
            if (outdir) return usage("-o given twice");
            outdir = a + 13;
        } else if (a[0] == '-') {
            fprintf(stderr, "calc: unknown option '%s'\n", a);
            return usage(NULL);
        } else {
            if (input) return usage("only one input file is allowed");
            input = a;
        }
    }
    if (!dir && !input) return usage("no input given");
    if (dir && input) return usage("use either -d DIR or an input file, not both");

    // Default output folder: <input_base>_<first>_<id>, in the current folder.
    char *base = base_name(dir ? dir : input);
    if (!dir) strip_txt(base);
    char *default_out = NULL;
    if (!outdir) {
        default_out = join3(base, "_" STUDENT_FIRST "_" STUDENT_ID, "");
        outdir = default_out;
    }

    int rc;
    if (dir) {
        rc = process_dir(dir, outdir);
    } else {
        rc = process_file(input, base, outdir);
    }

    free(base);
    free(default_out);
    return rc == 0 ? 0 : 1;
}