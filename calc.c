
#define _POSIX_C_SOURCE 200809L

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <limits.h>

#define LINE_CAP 8192
#define PATH_CAP 4096

typedef struct {
    double v;
    int is_float;
} Value;

typedef struct {
    const char *s;
    size_t i;
    size_t len;
    size_t err;
    int failed;
} Parser;

static void skipws(Parser *p)
{
    while (p->i < p->len &&
           (p->s[p->i] == ' ' ||
            p->s[p->i] == '\t' ||
            p->s[p->i] == '\r')) {
        p->i++;
    }
}

static void fail(Parser *p, size_t pos)
{
    if (!p->failed) {
        p->failed = 1;
        p->err = pos;
    }
}

static Value parse_expr(Parser *p);
static Value parse_power(Parser *p);

static Value zero_value(void)
{
    Value v = {0, 0};
    return v;
}

static Value parse_primary(Parser *p)
{
    skipws(p);
    size_t start = p->i;

    if (p->i >= p->len) {
        fail(p, p->len + 1);
        return zero_value();
    }

    if (p->s[p->i] == '(') {
        p->i++;
        Value v = parse_expr(p);
        skipws(p);

        if (p->i >= p->len || p->s[p->i] != ')') {
            fail(p, p->len + 1);
            return v;
        }

        p->i++;
        return v;
    }

    if (!isdigit((unsigned char)p->s[p->i])) {
        fail(p, start + 1);
        return zero_value();
    }

    double n = 0;
    int is_float = 0;

    while (p->i < p->len &&
           isdigit((unsigned char)p->s[p->i])) {
        n = n * 10 + (p->s[p->i] - '0');
        p->i++;
    }

    if (p->i < p->len && p->s[p->i] == '.') {
        is_float = 1;
        size_t dot = p->i++;
        if (p->i >= p->len ||
            !isdigit((unsigned char)p->s[p->i])) {
            fail(p, dot + 1);
            return zero_value();
        }

        double place = 0.1;

        while (p->i < p->len &&
               isdigit((unsigned char)p->s[p->i])) {
            n += (p->s[p->i] - '0') * place;
            place *= 0.1;
            p->i++;
        }
    }

    if (!isfinite(n)) {
        fail(p, start + 1);
        return zero_value();
    }

    Value v = {n, is_float};
    return v;
}

static Value parse_power(Parser *p)
{
    Value base = parse_primary(p);
    skipws(p);

    if (p->i + 1 < p->len &&
        p->s[p->i] == '*' &&
        p->s[p->i + 1] == '*') {

        size_t op = p->i;
        p->i += 2;
        skipws(p);

        if (p->i < p->len && p->s[p->i] == '-') {
            fail(p, p->i + 1);
            return zero_value();
        }

        if (p->i < p->len && p->s[p->i] == '+') {
            fail(p, p->i + 1);
            return zero_value();
        }

        size_t exp_start = p->i;
        Value exp = parse_power(p);

        if (p->failed) {
            return zero_value();
        }

        if (exp.v < 0) {
            fail(p, exp_start + 1);
            return zero_value();
        }

        double r = pow(base.v, exp.v);

        if (!isfinite(r) ||
            (base.v < 0 && floor(exp.v) != exp.v)) {
            fail(p, op + 1);
            return zero_value();
        }

        int fl = base.is_float || exp.is_float;

        if (!fl) {
            r = trunc(r);
        }

        Value out = {r, fl};
        return out;
    }

    return base;
}

static Value parse_term(Parser *p)
{
    Value v = parse_power(p);

    while (!p->failed) {
        skipws(p);

        if (p->i >= p->len ||
            (p->s[p->i] != '*' && p->s[p->i] != '/')) {
            break;
        }

        if (p->s[p->i] == '*' &&
            p->i + 1 < p->len &&
            p->s[p->i + 1] == '*') {
            break;
        }

        char op = p->s[p->i++];
        skipws(p);
        size_t rhspos = p->i;

        Value b = parse_power(p);

        if (p->failed) {
            return zero_value();
        }

        if (op == '/' && b.v == 0.0) {
            fail(p, rhspos + 1);
            return zero_value();
        }

        double r = op == '*' ? v.v * b.v : v.v / b.v;
        int fl = v.is_float || b.is_float;

        if (!fl) {
            r = trunc(r);
        }

        if (!isfinite(r)) {
            fail(p, rhspos + 1);
            return zero_value();
        }

        v.v = r;
        v.is_float = fl;
    }

    return v;
}

static Value parse_expr(Parser *p)
{
    Value v = parse_term(p);

    while (!p->failed) {
        skipws(p);

        if (p->i >= p->len ||
            (p->s[p->i] != '+' && p->s[p->i] != '-')) {
            break;
        }

        char op = p->s[p->i++];
        skipws(p);

        Value b = parse_term(p);

        if (p->failed) {
            return zero_value();
        }

        double r = op == '+' ? v.v + b.v : v.v - b.v;
        int fl = v.is_float || b.is_float;

        if (!fl) {
            r = trunc(r);
        }

        if (!isfinite(r)) {
            fail(p, p->i + 1);
            return zero_value();
        }

        v.v = r;
        v.is_float = fl;
    }

    return v;
}

static int eval_line(const char *s, size_t len,
                     Value *out, size_t *err)
{
    Parser p = {s, 0, len, 0, 0};
    size_t first = 0;

    while (first < len &&
           (s[first] == ' ' ||
            s[first] == '\t' ||
            s[first] == '\r')) {
        first++;
    }

    if (first == len || s[first] == '#') {
        return 0;
    }

    p.i = 0;
    *out = parse_expr(&p);
    skipws(&p);

    if (!p.failed && p.i < len) {
        fail(&p, p.i + 1);
    }

    if (p.failed) {
        *err = p.err ? p.err : 1;
        return -1;
    }

    *err = 0;
    return 1;
}

static int evaluate_file(const char *input, const char *output)
{
    FILE *in = fopen(input, "rb");

    if (!in) {
        fprintf(stderr, "Cannot open input: %s\n", input);
        return -1;
    }

    FILE *out = fopen(output, "w");

    if (!out) {
        fprintf(stderr, "Cannot write output: %s\n", output);
        fclose(in);
        return -1;
    }

    FILE *buffer = tmpfile();

    if (!buffer) {
        fprintf(stderr, "Cannot create temporary output\n");
        fclose(in);
        fclose(out);
        return -1;
    }

    char *line = NULL;
    size_t cap = 0;
    ssize_t n;
    size_t offset = 0;
    int bad = 0;
    size_t file_error = 0;

    while ((n = getline(&line, &cap, in)) != -1) {
        size_t len = (size_t)n;

        if (len && line[len - 1] == '\n') {
            len--;
        }

        Value v;
        size_t err = 0;
        int st = eval_line(line, len, &v, &err);

        if (st < 0) {
            file_error = offset + err;
            bad = 1;
            break;
        }

        if (st > 0) {
            if (v.is_float) {
                fprintf(buffer, "%.15g\n", v.v);
            } else {
                fprintf(buffer, "%.0f\n", v.v);
            }
        }

        offset += (size_t)n;
    }

    if (ferror(in)) {
        fprintf(stderr, "Error reading input: %s\n", input);
        bad = 1;
    }

    if (bad) {
        fprintf(out, "ERROR:%zu\n",
                file_error ? file_error : offset + 1);
    } else {
        rewind(buffer);
        int c;

        while ((c = fgetc(buffer)) != EOF) {
            fputc(c, out);
        }
    }

    free(line);
    fclose(buffer);
    fclose(in);
    fclose(out);

    return bad ? 1 : 0;
}

static int mkdir_p(const char *path)
{
    char tmp[PATH_CAP];
    size_t n = strlen(path);

    if (n == 0 || n >= sizeof tmp) {
        return -1;
    }

    memcpy(tmp, path, n + 1);

    if (tmp[n - 1] == '/') {
        tmp[n - 1] = '\0';
    }

    for (char *p = tmp + 1; *p; p++) {
        if (*p == '/') {
            *p = '\0';

            if (mkdir(tmp, 0777) && errno != EEXIST) {
                return -1;
            }

            *p = '/';
        }
    }

    if (mkdir(tmp, 0777) && errno != EEXIST) {
        return -1;
    }

    struct stat st;

    return stat(tmp, &st) == 0 && S_ISDIR(st.st_mode) ? 0 : -1;
}

static const char *base_name(const char *p)
{
    const char *s = strrchr(p, '/');
    return s ? s + 1 : p;
}

static int process_one(const char *input, const char *outdir)
{
    const char *bn = base_name(input);
    char base[PATH_CAP];

    if (strlen(bn) >= sizeof base) {
        fprintf(stderr, "Input name too long\n");
        return -1;
    }

    strcpy(base, bn);

    char *dot = strrchr(base, '.');

    if (dot) {
        *dot = '\0';
    }

    char dir[PATH_CAP];
    char out[PATH_CAP];
    int n;

    if (outdir) {
        n = snprintf(dir, sizeof dir, "%s", outdir);
    } else {
        n = snprintf(dir, sizeof dir,
                     "%.*s_Mohammad_251adb003",
                     4000, base);
    }

    if (n < 0 || (size_t)n >= sizeof dir) {
        fprintf(stderr, "Output directory name is too long\n");
        return -1;
    }

    if (mkdir_p(dir)) {
        fprintf(stderr, "Cannot create output directory: %s\n", dir);
        return -1;
    }

    n = snprintf(out, sizeof out,
                 "%s/%.*s_Mohammad_Anas_251adb003.txt",
                 dir, 4000, base);

    if (n < 0 || (size_t)n >= sizeof out) {
        fprintf(stderr, "Output path too long\n");
        return -1;
    }

    int rc = evaluate_file(input, out);

    return rc < 0 ? -1 : 0;
}

static int process_dir(const char *indir, const char *outdir)
{
    DIR *d = opendir(indir);

    if (!d) {
        fprintf(stderr, "Cannot open directory: %s\n", indir);
        return -1;
    }

    int status = 0;
    struct dirent *e;

    while ((e = readdir(d)) != NULL) {
        size_t n = strlen(e->d_name);

        if (n < 4 || strcmp(e->d_name + n - 4, ".txt") != 0) {
            continue;
        }

        char in[PATH_CAP];
        int k = snprintf(in, sizeof in, "%s/%s",
                         indir, e->d_name);

        if (k < 0 || (size_t)k >= sizeof in) {
            status = -1;
            continue;
        }

        struct stat st;

        if (stat(in, &st) || !S_ISREG(st.st_mode)) {
            continue;
        }

        if (process_one(in, outdir) < 0) {
            status = -1;
        }
    }

    closedir(d);
    return status;
}

int main(int argc, char **argv)
{
    const char *outdir = NULL;
    const char *input = NULL;
    const char *indir = NULL;

    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-o") ||
            !strcmp(argv[i], "--output-dir")) {

            if (i + 1 >= argc) {
                fprintf(stderr, "Missing output directory\n");
                return 1;
            }

            outdir = argv[++i];

        } else if (!strcmp(argv[i], "-d") ||
                   !strcmp(argv[i], "--dir")) {

            if (i + 1 >= argc) {
                fprintf(stderr, "Missing input directory\n");
                return 1;
            }

            indir = argv[++i];

        } else if (argv[i][0] == '-') {
            fprintf(stderr, "Unknown option: %s\n", argv[i]);
            return 1;

        } else if (input) {
            fprintf(stderr, "Too many input paths\n");
            return 1;

        } else {
            input = argv[i];
        }
    }

    if ((indir && input) || (!indir && !input)) {
        fprintf(stderr,
                "Usage: calc [-o output-dir] input.txt | "
                "calc -d input-dir [-o output-dir]\n");
        return 1;
    }

    if (indir) {
        if (!outdir) {
            const char *b = base_name(indir);
            char tmp[PATH_CAP];

            int n = snprintf(tmp, sizeof tmp,
                             "%.*s_Mohammad_251adb003",
                             4000, b);

            if (n < 0 || (size_t)n >= sizeof tmp) {
                fprintf(stderr, "Path too long\n");
                return 1;
            }

            if (process_dir(indir, tmp) < 0) {
                return 1;
            }

        } else if (process_dir(indir, outdir) < 0) {
            return 1;
        }

    } else if (process_one(input, outdir) < 0) {
        return 1;
    }

    return 0;
}
