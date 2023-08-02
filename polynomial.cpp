#include <bits/stdc++.h>
using namespace std;
#define re register
#define int long long
namespace IO {
char _buf[1 << 21], *_p1 = _buf, *_p2 = _buf;
#define ch()                                                                 \
  (_p1 == _p2 &&                                                             \
           (_p2 = (_p1 = _buf) + fread(_buf, 1, 1 << 21, stdin), _p1 == _p2) \
       ? EOF                                                                 \
       : *_p1++)
inline int in() {
  int s = 0, f = 1;
  char x = ch();
  while (x < '0' || x > '9') {
    if (x == '-') f = -1;
    x = ch();
  }
  while (x >= '0' && x <= '9') {
    s = (s * 10) + (x & 15);
    x = ch();
  }
  return f = 1 ? s : -s;
}
char _buf_[1 << 21];
int _p1_ = -1;
inline void flush() {
  fwrite(_buf_, 1, _p1_ + 1, stdout);
  _p1_ = -1;
}
inline void pc(char x) {
  if (_p1_ == (1 << 21) - 1) flush();
  _buf_[++_p1_] = x;
}
inline void out(int x) {
  char k[20];
  int tot = 0;
  if (!x) {
    pc('0');
    return;
  }
  if (x < 0) {
    pc('-');
    x = -x;
  }
  while (x) {
    k[++tot] = (x % 10) | 48;
    x /= 10;
  }
  for (int i = tot; i; i--) pc(k[i]);
  return;
}
}  // namespace IO
using namespace IO;
typedef vector<int> poly;
const int A = 3e5 + 5;
const int logA = 18;
const int mod = 998244353;
inline int add(int a, int b) { return a + b >= mod ? a + b - mod : a + b; }
inline int dec(int a, int b) { return a - b < 0 ? a - b + mod : a - b; }
inline int mul(int a, int b) { return a * b % mod; }
inline void Add(int &a, int b) {
  a = add(a, b);
  return;
}
inline void Dec(int &a, int b) {
  a = dec(a, b);
  return;
}
inline void Mul(int &a, int b) {
  a = mul(a, b);
  return;
}
inline int power(int s, int c) {
  int ans = 1;
  while (c) {
    if (c & 1) Mul(ans, s);
    s = mul(s, s);
    c >>= 1;
  }
  return ans;
}
inline void print(poly a) {
  for (int i = 0; i < a.size(); i++) out(a[i]), pc(' ');
  pc('\n');
  return;
}
int _r[A], _lim;
inline void init(int len) {
  _lim = 1;
  while (_lim < len) _lim <<= 1;
  for (int i = 1; i < _lim; i++)
    _r[i] = (_r[i >> 1] >> 1) | ((i & 1) ? _lim >> 1 : 0);
  return;
}
inline poly operator+(poly a, poly b) {
  if (a.size() < b.size()) a.resize(b.size());
  for (int i = 0; i < b.size(); i++) Add(a[i], b[i]);
  return a;
}
inline poly operator-(poly a, poly b) {
  if (a.size() < b.size()) a.resize(b.size());
  for (int i = 0; i < b.size(); i++) Dec(a[i], b[i]);
  return a;
}
inline poly Divx(poly a) {
  for (int i = 0; i < a.size(); i++) a[i] = a[i + 1];
  a.pop_back();
  return a;
}
int *_wn[logA + 1], inv[A], fact[A];
inline void pre_ntt() {
  for (int i = 1; i <= logA; i++) _wn[i] = new int[1 << (i - 1)];
  int k = power(3, (mod - 1) / (1 << logA));
  _wn[logA][0] = 1;
  for (int i = 1; i < (1 << (logA - 1)); i++)
    _wn[logA][i] = mul(_wn[logA][i - 1], k);
  for (int i = logA - 1; i; i--)
    for (int j = 0; j < (1 << (i - 1)); j++) _wn[i][j] = _wn[i + 1][j << 1];
  inv[0] = inv[1] = 1;
  for (int i = 2; i <= (1 << logA); i++)
    inv[i] = mul(mod - mod / i, inv[mod % i]);
  fact[0] = 1;
  for (int i = 1; i <= (1 << logA); i++) fact[i] = mul(fact[i - 1], i);
  return;
}
inline void ntt(poly &Q, int pos) {
  for (int i = 0; i < _lim; i++)
    if (i < _r[i]) swap(Q[_r[i]], Q[i]);
  for (int mid = 1, c = 1; mid < _lim; mid <<= 1, c++)
    for (int i = 0; i < _lim; i += (mid << 1))
      for (int j = 0; j < mid; j++) {
        int x = Q[i + j], y = mul(Q[i + j + mid], _wn[c][j]);
        Q[i + j] = add(x, y);
        Q[i + j + mid] = dec(x, y);
      }
  if (pos) return;
  int k = power(_lim, mod - 2);
  reverse(Q.begin() + 1, Q.end());
  for (int i = 0; i < _lim; i++) Mul(Q[i], k);
  return;
}
inline poly operator*(poly a, poly b) {
  int len = a.size() + b.size() - 1;
  if (a.size() < 32 || b.size() < 32) {
    poly c(len, 0);
    for (int i = 0; i < a.size(); i++)
      for (int j = 0; j < b.size(); j++) Add(c[i + j], mul(a[i], b[j]));
    return c;
  }
  init(len);
  a.resize(_lim), b.resize(_lim);
  ntt(a, 1), ntt(b, 1);
  for (int i = 0; i < _lim; i++) Mul(a[i], b[i]);
  ntt(a, 0);
  a.resize(len);
  return a;
}
inline poly Inv(poly a, int len) {
  poly b(1, power(a[0], mod - 2)), c;
  for (int deg = 2; (deg >> 1) < len; deg <<= 1) {
    c.resize(deg);
    init(deg << 1);
    for (int i = 0; i < deg; i++) c[i] = i < a.size() ? a[i] : 0;
    c.resize(_lim), b.resize(_lim);
    ntt(c, 1), ntt(b, 1);
    for (int i = 0; i < _lim; i++) Mul(b[i], dec(2, mul(b[i], c[i])));
    ntt(b, 0);
    b.resize(deg);
  }
  b.resize(len);
  return b;
}
inline poly Der(poly a) {
  for (int i = 0; i < a.size(); i++) a[i] = mul(a[i + 1], i + 1);
  a.pop_back();
  return a;
}
inline poly Ing(poly a) {
  a.push_back(0);
  for (int i = a.size() - 1; i; i--) a[i] = mul(inv[i], a[i - 1]);
  a[0] = 0;
  return a;
}
inline poly Ln(poly a, int len) {
  a = Ing(Der(a) * Inv(a, len));
  a.resize(len);
  return a;
}
inline poly Exp(poly a, int len) {
  poly b(1, 1), c;
  for (int deg = 2; deg < (len << 1); deg <<= 1) {
    c = Ln(b, deg);
    Dec(c[0], 1);
    for (int i = 0; i < deg; i++) c[i] = dec(i < a.size() ? a[i] : 0, c[i]);
    b = b * c;
    b.resize(deg);
  }
  b.resize(len);
  return b;
}
inline poly Power(poly a, int c, int len) {
  a = Ln(a, len);
  for (int i = 0; i < a.size(); i++) Mul(a[i], c);
  return Exp(a, len);
}
inline poly Sqrt(poly a, int len) {
  poly b(1, 1), c;
  for (int deg = 2; deg < (len << 1); deg <<= 1) {
    b = a * Inv(b, deg) + b;
    for (int i = 0; i < deg; i++) b[i] = mul(b[i], inv[2]);
    b.resize(deg);
  }
  b.resize(len);
  return b;
}
inline void operator-=(poly &a, const poly &b) {
  if (a.size() < b.size()) a.resize(b.size());
  for (int i = 0; i < b.size(); i++) Dec(a[i], b[i]);
  return;
}
inline poly operator/(poly a, poly b) {
  int len = a.size() - b.size() + 1;
  reverse(a.begin(), a.end());
  a.resize(len);
  reverse(b.begin(), b.end());
  a = a * Inv(b, len);
  a.resize(len);
  reverse(a.begin(), a.end());
  return a;
}
inline poly operator%(poly a, poly b) {
  if (a.size() < b.size()) return a;
  a -= b * (a / b);
  a.resize(b.size() - 1);
  return a;
}
poly _f[A];
#define lch p << 1
#define rch p << 1 | 1
inline void pre_val(int p, int l, int r, int *x) {
  if (l == r) {
    _f[p].push_back(dec(0, x[l]));
    _f[p].push_back(1);
    return;
  }
  int mid = (l + r) >> 1;
  pre_val(lch, l, mid, x), pre_val(rch, mid + 1, r, x);
  _f[p] = _f[lch] * _f[rch];
  return;
}
inline void Val(int p, int l, int r, poly F, int *v) {
  if (l == r) {
    v[l] = F[0];
    return;
  }
  int mid = (l + r) >> 1;
  Val(lch, l, mid, F % _f[lch], v), Val(rch, mid + 1, r, F % _f[rch], v);
  return;
}
#undef lch
#undef rch
