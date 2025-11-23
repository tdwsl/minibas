#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <termios.h>
#include <signal.h>

#define MAXDIM 5
#define MAXR 256
#define MEMSZ (65536*4)
#define BUKSZ 4

int var[26];

int i1[26], fln[26];
int fi[26];

int ri[MAXR];
int rln[MAXR];
int rp = 0;

int ndim[26];
int dims[26*MAXDIM];
int *dima[26] = {0};

char mem[MEMSZ];
int memsz = 0;

char **lines;
int *lkeys;
int lsz;

unsigned char *data;
int ndata, di;
int dsz;

char zer[20] = {0};

int err = 0;
int maxln = 0;

int lineno; char *l; char *l0;

FILE *out, *inp = 0;

int digitp(char c) {
  return c >= '0' && c <= '9';
}

void errs(const char *s) {
  if(!err) {
    printf("\r");
    if(lineno) printf("%d ", lineno);
    printf("%s\n", s); err = 1; l = zer;
  }
}

int asz(int v) {
  if(!dima[v]) return 0;
  int *d = &dims[v*MAXDIM];
  int n = d[0];
  for(int i = 1; i < MAXDIM; i++) n *= d[i];
  return n;
}

void collect() {
  char alt[MEMSZ];
  char *altp = alt;
  char *alkeys = altp;
  memcpy(altp, lkeys, sizeof(int)*lsz);
  altp += sizeof(int)*lsz;
  char **lns = (char**)altp;
  altp += sizeof(char**)*lsz;
  for(int i = 0; i < lsz; i++) {
    if(!lines[i]) { lns[i] = 0; continue; }
    lns[i] = altp;
    strcpy(altp, lines[i]); altp += strlen(lines[i])+1;
  }
  char *dma[26];
  for(int i = 0; i < 26; i++) {
    if(!dima[i]) dma[i] = 0;
    else {
      int n = asz(i)*sizeof(int);
      dma[i] = altp;
      memcpy(altp, dima[i], n);
      altp += n;
    }
  }
  memcpy(mem, alt, altp-alt);
  memsz = altp-alt;
  lkeys = (int*)(alkeys-alt+mem);
  lines = (char**)((char*)lns-alt+mem);
  for(int i = 0; i < 26; i++)
    if(dma[i]) dima[i] = (int*)((char*)dma[i]-alt+mem);
}

void *alloc(int n) {
  if(memsz+n >= MEMSZ) collect();
  if(memsz+n >= MEMSZ) { errs("out of memory"); return 0; }
  char *p = &mem[memsz]; memsz += n;
  return (void*)p;
}

void *zalloc(int n) {
  char *s = alloc(n);
  if(!s) return 0;
  for(int i = 0; i < n; i++) s[i] = 0;
  return s;
}

void *grow(void *d, int n, int n1) {
  void *b = alloc(n1);
  if(!b) return 0;
  memcpy(b, d, n);
  return b;
}

int hash(int n, int lsz) {
  while(n < 0) n += lsz/BUKSZ;
  return n%(lsz/BUKSZ)+1;
}

char *getLine(int n) {
  int k = hash(n, lsz);
  for(int i = 0; i < BUKSZ && lkeys[k*BUKSZ+i]; i++)
    if(lkeys[k*BUKSZ+i] == n) return lines[k*BUKSZ+i];
  return zer;
}

void setLine(int n, char *l) {
  int k = hash(n, lsz);
  int i;
  for(i = 0; i < BUKSZ && lkeys[k*BUKSZ+i]; i++)
    if(lkeys[k*BUKSZ+i] == n) {
      if(l) lines[k*BUKSZ+i] = l;
      else {
        for(i++; i < BUKSZ; i++) {
          lines[k*BUKSZ+i-1] = lines[k*BUKSZ+i];
          lkeys[k*BUKSZ+i-1] = lkeys[k*BUKSZ+i];
        }
        lkeys[k*BUKSZ+BUKSZ-1] = 0;
        lines[k*BUKSZ+BUKSZ-1] = 0;
      }
    }
  if(i < BUKSZ) { lkeys[k*BUKSZ+i] = n; lines[k*BUKSZ+i] = l; }
  else {
    int *nk = zalloc(sizeof(int)*lsz*2+sizeof(char**)*lsz*2);
    if(!nk) return;
    char **nl = (char**)(nk+lsz*2);
    for(int i = 0; i < lsz; i++) {
      if(!lkeys[i]) continue;
      int j;
      k = hash(lkeys[i], lsz*2);
      for(int j = 0; j < BUKSZ && nk[k*BUKSZ+j]; j++);
      nk[k*BUKSZ+j] = lkeys[i];
      nl[k*BUKSZ+j] = lines[i];
    }
    lkeys = nk;
    lines = nl;
    lsz *= 2;
    setLine(n, l);
  }
}

void syntax() { errs("syntax error"); }

int evalUna();

int notzero() {
  int n = evalUna();
  if(!n) errs("division by zero");
  return n;
}

void inderr() { errs("index error"); }
void dimerr() { errs("dimension error"); }
void overflow() { errs("return stack overflow"); }
void underflow() { errs("return stack underflow"); }
void ood() { errs("out of data"); }
void fileerr() { errs("failed to open file"); }

void req(char c) {
  if(*l == c) l++;
  else syntax();
}

int eval();

int *lval() {
  if(*l >= 'A' && *l <= 'Z') {
    int a = *l++-'A';
    if(*l == '(') {
      l++; int dim[MAXDIM];
      int n = 0;
      for(;;) {
        dim[n++] = eval();
        if(*l == ')' || err) break;
        req(',');
      }
      l++;
      if(ndim[a] != n) inderr();
      for(int i = 0; i < n; i++)
        if(dim[i] < 1 || dim[i] > dims[a*MAXDIM+i]) {
          inderr(); return 0;
        }
      int i = dim[0]-1;
      for(int j = 1; j < n; j++)
        i = i * dims[a*MAXDIM+j-1] + dim[j] - 1;
      return &dima[a][i];
    } else return &var[a];
  } else return 0;
}

int evalUna() {
  int a;
  switch(*l) {
  case '-': l++; return -evalUna();
  case '(': l++; a = eval(); req(')'); return a;
  }
  if(*l == '?') { l++; return rand()%notzero(); }
  if(digitp(*l)) {
    a = 0;
    do a = a*10+*l-'0'; while(digitp(*++l));
  } else if(*l == '"') {
    a = *++l;
    if(*++l != '"') syntax();
    l++;
  } else {
    int *p = lval();
    if(!p) syntax();
    else a = *p;
  }
  return a;
}

int evalMul() {
  int a = evalUna();
  for(;;) {
    if(*l == '*') { l++; a *= evalUna(); }
    else if(*l == '/') { l++; a /= notzero(); }
    else if(*l == '%') { l++; a %= notzero(); }
    else return a;
  }
}

int evalAdd() {
  int a = evalMul();
  for(;;) {
    if(*l == '+') { l++; a += evalMul(); }
    else if(*l == '-') { l++; a -= evalMul(); }
    else return a;
  }
}

int eval() {
  int a = evalAdd();
  for(;;) {
    if(*l == '=') { l++; a = a == evalAdd(); }
    else if(*l == '#') { l++; a = a != evalAdd(); }
    else if(*l == '<') { l++; a = a < evalAdd(); }
    else if(*l == '>') { l++; a = a > evalAdd(); }
    else return a;
  }
}

int check(const char *s) {
  if(strstr(l, s) == l) {
    l += strlen(s);
    return 1;
  }
  return 0;
}

int termp() {
  if(*l == ':') return 1;
  if(!*l) return 1;
  return 0;
}

int getvar() {
  int c = *l;
  if(c >= 'A' && c <= 'Z') { l++; return c-'A'; }
  syntax();
  return 0;
}

void go(int a) {
  l = zer;
  for(; !*l && a <= maxln; a++) l = getLine(a);
  lineno = a;
}

int getkey() {
  if(inp) return fgetc(inp);
  struct termios term, old;
  tcgetattr(0, &old);
  memcpy(&term, &old, sizeof(struct termios));
  term.c_lflag &= ~(ICANON|ECHO);
  tcsetattr(0, TCSANOW, &term);
  int k = getchar();
  tcsetattr(0, TCSANOW, &old);
  return k;
}

void pos(int x, int y) {
  printf("\x1b[%d;%dH", y, x);
}

void clearscr() {
  printf("\x1b[H\x1b[J");
}

int readLine(FILE *f);

void db(unsigned char b) {
  if(ndata+1 >= dsz) {
    unsigned char *d = grow(data, dsz, dsz*2);
    if(!d) return; data = d; dsz *= 2;
  }
  data[ndata++] = b;
}

void clear() {
  data = alloc(256); dsz = 256;
  lsz = 200*BUKSZ;
  lines = zalloc(lsz*sizeof(char**));
  lkeys = zalloc(lsz*sizeof(int));
}

void runLine() {
  while(!err) {
    if(!*l || *l == ':');
    else if(check("IF")) {
      if(!eval()) l = zer; else req(';'); continue;
    }
    else if(check("PRINT")) {
      if(termp()) printf("\n");
      else while(!err) {
        if(termp() || err) break;
        else if(*l == '"') {
          l++; *strchr(l, '"') = 0; fprintf(out, "%s", l); l += strlen(l)+1; l[-1] = '"';
        } else {
          int n = eval(); if(err) break;
          fprintf(out, "%d", n);
        }
        if(termp()) { fprintf(out, "\n"); break; }
        if(*l == ',') fprintf(out, "\t");
        else if(*l == ';');
        else syntax();
        l++;
      }
      continue;
    }
    else if(check("END")) {
      if(!termp()) syntax();
      return;
    }
    else if(check("PUT")) {
      int c = eval();
      if(!err) fprintf(out, "%c", c);
    }
    else if(check("INPUT")) {
      if(*l == '"') {
        if(inp) l = strchr(l, '"')+1;
        else { l++; *strchr(l, '"') = 0; printf("%s", l); l += strlen(l)+1; l[-1] = '"'; }
        req(','); if(err) break;
      }
      else if(!inp) printf("? ");
      int *p = lval(); if(err) break;
      *p = 0;
      int n = 0;
      while(!feof(out)) {
        int c = getkey();
        if(c == 10 || c == 13 || inp && n && !digitp(c)) { if(n) break; }
        else if(c == 127) { if(n) { n--; printf("\b \b"); *p /= 10; } }
        else if(digitp(c) && n < 9) {
          if(!inp) printf("%c", c);
          *p = *p * 10 + c - '0'; n++;
        }
      }
      if(!inp) printf("\n");
    }
    else if(check("GET")) {
      int *p = lval(); if(err) break;
      *p = getkey();
    }
    else if(check("OPEN")) {
      if(inp) fclose(inp);
      req('"'); if(err) break;
      char *s = l; l = strchr(l, '"')+1; l[-1] = 0;
      inp = fopen(s, "r"); l[-1] = '"';
      if(!inp) { fileerr(); break; }
    }
    else if(check("CLOSE")) {
      if(inp) { fclose(inp); inp = 0; }
    }
    else if(check("OUTPUT")) {
      if(out != stdout) fclose(out);
      req('"'); if(err) break;
      char *s = l; l = strchr(l, '"')+1; l[-1] = 0;
      out = fopen(s, "w"); l[-1] = '"';
      if(!out) { out = stdout; fileerr(); break; }
    }
    else if(check("WRITE")) {
      if(out != stdout) { fclose(out); out = stdout; }
    }
    else if(check("CLS")) {
      clearscr();
    }
    else if(check("POS")) {
      int x = eval(); req(','); int y = eval();
      if(!err) pos(x, y);
    }
    else if(check("DIM")) {
      int c = getvar();
      req('(');
      int dim[MAXDIM], n = 0;
      while(!err) {
        int d = eval();
        if(d < 1 || n+1 >= MAXDIM) dimerr();
        else dim[n++] = d;
        if(*l == ')') break;
        req(',');
      }
      if(err) break;
      l++;
      int sz = dim[0];
      for(int i = 1; i < n; i++) sz *= dim[i];
      int *a = alloc(sz*sizeof(int));
      if(!a) break;
      dima[c] = a;
      int *dim1 = &dims[c*MAXDIM];
      for(int i = 0; i < n; i++) dim1[i] = dim[i];
      ndim[c] = n;
    }
    else if(check("FOR")) {
      int c = getvar();
      req('='); var[c] = eval();
      req(';'); i1[c] = eval();
      fln[c] = lineno; fi[c] = l-getLine(lineno);
    }
    else if(check("NEXT")) {
      int c = getvar();
      if(!fln[c]) { inderr(); break; }
      var[c]++;
      if(var[c] <= i1[c]) {
        lineno = fln[c]; l = fi[c]+getLine(lineno);
      }
    }
    else if(check("RUN")) {
      if(*l) syntax();
      else {
        rp = di = ndata = 0;
        go(1);
        continue;
      }
    }
    else if(check("GOTO")) {
      int a = eval(); if(!err) go(a);
      continue;
    }
    else if(check("GOSUB")) {
      if(rp >= MAXR) { overflow(); break; }
      int a = eval();
      if(err) break;
      rln[rp] = lineno; ri[rp++] = l-getLine(lineno);
      go(a);
      continue;
    }
    else if(check("RETURN")) {
      if(!rp) { underflow(); break; }
      lineno = rln[--rp]; l = ri[rp]+getLine(lineno);
      continue;
    }
    else if(check("REM")) {
      l = zer;
    }
    else if(check("LIST")) {
      int i = 1, b = maxln;
      if(digitp(*l)) {
        i = 0; do i=i*10+*l-'0'; while(digitp(*++l));
        if(!i) { syntax(); break; }
        b = i;
        if(*l == '-') {
          l++; if(!digitp(*l)) { syntax(); break; }
          b = 0; do b=b*10+*l-'0'; while(digitp(*++l));
          if(!b) { syntax(); break; }
        }
        if(!termp()) { syntax(); break; }
      }
      for(; i <= b; i++) {
        char *s = getLine(i);
        if(*s) printf("%d %s\n", i, s);
      }
    }
    else if(check("DATA")) {
      while(!err) {
        if(*l == '"') {
          while(*++l != '"') db(*l); l++;
        } else {
          int n = eval(); if(err) break;
          db(n);
        }
        if(termp()) break;
        req(',');
      }
    }
    else if(check("READ")) {
      while(!err) {
        if(di >= ndata) { ood(); break; }
        int *p = lval(); if(err) break;
        *p = data[di++]; if(err) break;
        if(termp()) break;
        req(',');
      }
    }
    else if(check("RESTORE")) {
      di = 0;
    }
    else if(check("COLLECT")) {
      collect();
    }
    else if(check("SAVE")) {
      req('"'); if(err) break;
      char *s = l; l = strchr(l, '"')+1; l[-1] = 0;
      FILE *fp = fopen(s, "w"); l[-1] = '"';
      if(!fp) { fileerr(); break; }
      for(int i = 1; i <= maxln; i++) {
        char *s = getLine(i);
        if(*s) fprintf(fp, "%d %s\n", i, s);
      }
      fclose(fp);
    }
    else if(check("LOAD")) {
      req('"'); if(err) break;
      char *s = l; l = strchr(l, '"')+1; l[-1] = 0;
      FILE *fp = fopen(s, "r"); l[-1] = '"';
      if(!fp) { fileerr(); break; }
      clear();
      while(!feof(fp)) readLine(fp);
      fclose(fp);
      break;
    }
    else {
      int *p = lval();
      if(!p) syntax();
      else { req('='); *p = eval(); }
    }
    if(*l) req(':');
    else {
      if(!lineno) break;
      l = getLine(++lineno);
      if(lineno > maxln) break;
    }
  }
}

int readLine(FILE *f) {
  /* init vars */
  ndata = 0;
  di = 0;
  rp = 0;

  char c;
  while((c = fgetc(f)) <= 32 && c != EOF);
  if(c == EOF) return 0;
  int n = 0;
  if(digitp(c)) {
    do n = n*10+c-'0'; while(digitp(c = fgetc(f)));
  }
  if(n > maxln) maxln = n;

  int q = 0;
  int i;
  char buf[256];
  for(i = 0; i < 254; i++) {
    if(c == 10 || c == EOF) break;
    if(c == '"') q = !q;
    if(!q && c <= 32) i--;
    else {
      if(!q && c >= 'a' && c <= 'z') c -= 32;
      buf[i] = c;
    }
    c = fgetc(f);
  }
  if(q) buf[i++] = '"';
  buf[i] = 0;
  l = alloc(i+1);
  if(!l) return 1;
  strcpy(l, buf);

  lineno = n;
  if(!n) runLine();
  else setLine(lineno, l);

  /* clean up */
  if(err) {
    if(out != stdout) fclose(out); if(inp) fclose(inp);
    out = stdout; inp = 0;
  }
  err = 0;
  lineno = 0;

  return 1;
}

void sig(int sig) {
  errs("caught interrupt");
  lineno = 0;
}

int main(int argc, char **args) {
  srand(time(0));
  clear();
  out = stdout;
  signal(SIGINT, sig);

  for(int i = 1; i < argc; i++) {
    FILE *fp = fopen(args[i], "r");
    if(!fp) { printf("failed to open %s\n", args[i]); continue; }
    while(!feof(fp)) readLine(fp);
    fclose(fp);
  }

  while(readLine(stdin));
  return 0;
}
