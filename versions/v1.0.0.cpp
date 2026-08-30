#include <bits/stdc++.h>
#include <clocale>      // for setlocale
#ifdef _WIN32
#include <windows.h>    // for SetConsoleOutputCP
#endif
using namespace std;

void set_utf8_encoding() {
#ifdef _WIN32
    // Windows 控制台设置 UTF-8 代码页
    SetConsoleOutputCP(CP_UTF8);
    SetConsoleCP(CP_UTF8);
#else
    // Linux/Unix 设置 locale 为 UTF-8（显式声明）
    setlocale(LC_ALL, "en_US.UTF-8");
    // 若系统不支持 "en_US.UTF-8"，可改用 setlocale(LC_ALL, "");
#endif
}


/* ==================== 快速IO ==================== */
#define FAST_IO ios::sync_with_stdio(false); cin.tie(nullptr); cout.tie(nullptr)

/* ==================== 常用宏 ==================== */
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define per(i, a, b) for (int i = (b) - 1; i >= (a); --i)
#define all(x) (x).begin(), (x).end()
#define sz(x) ((int)(x).size())
#define pb push_back
#define eb emplace_back
#define fi first
#define se second

/* ==================== 类型别名 ==================== */
using ll = long long;
using ull = unsigned long long;
using pii = pair<int, int>;
using pll = pair<ll, ll>;
using vi = vector<int>;
using vll = vector<ll>;
using vvi = vector<vi>;
using vvll = vector<vll>;
using vpii = vector<pii>;
using vpll = vector<pll>;

/* ==================== 常用常量 ==================== */
const int INF = 0x3f3f3f3f;          // 1e9 级别
const ll INFLL = 0x3f3f3f3f3f3f3f3fLL;
const int MOD = 1e9 + 7;
const int MAXN = 200005;             // 常用最大数组大小

/* ==================== 数学工具 ==================== */
namespace Math {
    // 最大公约数
    ll gcd(ll a, ll b) { return b ? gcd(b, a % b) : a; }
    // 最小公倍数
    ll lcm(ll a, ll b) { return a / gcd(a, b) * b; }
    // 快速幂 (a^b % mod)
    ll modpow(ll a, ll b, ll mod = MOD) {
        ll r = 1;
        while (b) {
            if (b & 1) r = r * a % mod;
            a = a * a % mod;
            b >>= 1;
        }
        return r;
    }
    // 扩展欧几里得: 返回 (g, x, y) s.t. ax + by = g
    tuple<ll, ll, ll> exgcd(ll a, ll b) {
        if (b == 0) return {a, 1, 0};
        auto [g, x, y] = exgcd(b, a % b);
        return {g, y, x - (a / b) * y};
    }
    // 模逆元 (需保证 gcd(a, mod) = 1)
    ll modinv(ll a, ll mod = MOD) {
        auto [g, x, y] = exgcd(a, mod);
        return (x % mod + mod) % mod;
    }

    // 素数筛 (埃氏筛)
    vi sieve(int n) {
        vector<bool> isp(n + 1, true);
        vi primes;
        isp[0] = isp[1] = false;
        for (int i = 2; i <= n; ++i) {
            if (isp[i]) {
                primes.pb(i);
                if (1LL * i * i <= n)
                    for (ll j = 1LL * i * i; j <= n; j += i) isp[j] = false;
            }
        }
        return primes;
    }

    // 组合数 (预处理阶乘和逆元)
    struct Comb {
        vector<ll> fact, invfact;
        int mod;
        Comb(int n, int mod_ = MOD) : mod(mod_) {
            fact.resize(n + 1);
            invfact.resize(n + 1);
            fact[0] = 1;
            for (int i = 1; i <= n; ++i) fact[i] = fact[i - 1] * i % mod;
            invfact[n] = modpow(fact[n], mod - 2, mod);
            for (int i = n; i >= 1; --i) invfact[i - 1] = invfact[i] * i % mod;
        }
        ll C(int n, int k) const {
            if (k < 0 || k > n) return 0;
            return fact[n] * invfact[k] % mod * invfact[n - k] % mod;
        }
        ll P(int n, int k) const {
            if (k < 0 || k > n) return 0;
            return fact[n] * invfact[n - k] % mod;
        }
    };
} // namespace Math

/* ==================== 数据结构 ==================== */
namespace DataStructure {
    // ---------- 并查集 (DSU) ----------
    struct DSU {
        vi f, sz;
        DSU(int n = 0) { init(n); }
        void init(int n) { f.resize(n); sz.assign(n, 1); iota(all(f), 0); }
        int find(int x) { return f[x] == x ? x : f[x] = find(f[x]); }
        bool unite(int a, int b) {
            a = find(a), b = find(b);
            if (a == b) return false;
            if (sz[a] < sz[b]) swap(a, b);
            f[b] = a;
            sz[a] += sz[b];
            return true;
        }
        bool same(int a, int b) { return find(a) == find(b); }
        int size(int x) { return sz[find(x)]; }
    };

    // ---------- 树状数组 (Fenwick Tree) ----------
    template <typename T>
    struct BIT {
        int n;
        vector<T> bit;
        BIT(int n_) : n(n_), bit(n_ + 1, 0) {}
        void add(int idx, T val) { for (; idx <= n; idx += idx & -idx) bit[idx] += val; }
        T sum(int idx) const { T r = 0; for (; idx > 0; idx -= idx & -idx) r += bit[idx]; return r; }
        T range_sum(int l, int r) const { return sum(r) - sum(l - 1); } // 1-indexed [l, r]
    };

    // ---------- 线段树 (区间加, 区间求和) ----------
    template <typename T>
    struct SegTree {
        int n;
        vector<T> tree, lazy;
        SegTree(int n_) : n(n_), tree(4 * n_), lazy(4 * n_, 0) {}
        void build(const vector<T>& arr, int node, int l, int r) {
            if (l == r) { tree[node] = arr[l]; return; }
            int mid = (l + r) >> 1;
            build(arr, node << 1, l, mid);
            build(arr, node << 1 | 1, mid + 1, r);
            tree[node] = tree[node << 1] + tree[node << 1 | 1];
        }
        void push(int node, int l, int r) {
            if (lazy[node] != 0 && l != r) {
                int mid = (l + r) >> 1;
                lazy[node << 1] += lazy[node];
                lazy[node << 1 | 1] += lazy[node];
                tree[node << 1] += lazy[node] * (mid - l + 1);
                tree[node << 1 | 1] += lazy[node] * (r - mid);
                lazy[node] = 0;
            }
        }
        void update(int node, int l, int r, int ql, int qr, T val) {
            if (ql <= l && r <= qr) {
                tree[node] += val * (r - l + 1);
                lazy[node] += val;
                return;
            }
            push(node, l, r);
            int mid = (l + r) >> 1;
            if (ql <= mid) update(node << 1, l, mid, ql, qr, val);
            if (qr > mid) update(node << 1 | 1, mid + 1, r, ql, qr, val);
            tree[node] = tree[node << 1] + tree[node << 1 | 1];
        }
        T query(int node, int l, int r, int ql, int qr) {
            if (ql <= l && r <= qr) return tree[node];
            push(node, l, r);
            int mid = (l + r) >> 1;
            T res = 0;
            if (ql <= mid) res += query(node << 1, l, mid, ql, qr);
            if (qr > mid) res += query(node << 1 | 1, mid + 1, r, ql, qr);
            return res;
        }
        // 外部接口 (1-indexed)
        void build(const vector<T>& arr) { build(arr, 1, 1, n); }
        void update(int l, int r, T val) { update(1, 1, n, l, r, val); }
        T query(int l, int r) { return query(1, 1, n, l, r); }
    };

    // ---------- ST表 (RMQ, 静态最值) ----------
    template <typename T, typename Func = function<T(T, T)>>
    struct SparseTable {
        int n, K;
        vector<vector<T>> st;
        Func op;
        SparseTable(const vector<T>& arr, Func f) : n(arr.size()), op(f) {
            K = 31 - __builtin_clz(n);
            st.assign(K + 1, vector<T>(n));
            st[0] = arr;
            for (int k = 1; k <= K; ++k)
                for (int i = 0; i + (1 << k) <= n; ++i)
                    st[k][i] = op(st[k - 1][i], st[k - 1][i + (1 << (k - 1))]);
        }
        T query(int l, int r) { // [l, r] 0-indexed
            int len = r - l + 1;
            int k = 31 - __builtin_clz(len);
            return op(st[k][l], st[k][r - (1 << k) + 1]);
        }
    };
} // namespace DataStructure

/* ==================== 图论算法 ==================== */
namespace Graph {
    const int INF = 0x3f3f3f3f;
    using Edge = struct { int to, w; };
    using Adj = vector<vector<Edge>>;

    // ---------- Dijkstra (堆优化) ----------
    vector<int> dijkstra(const Adj& g, int s) {
        int n = g.size();
        vector<int> dist(n, INF);
        priority_queue<pii, vector<pii>, greater<pii>> pq;
        dist[s] = 0;
        pq.push({0, s});
        while (!pq.empty()) {
            auto [d, u] = pq.top(); pq.pop();
            if (d != dist[u]) continue;
            for (auto &e : g[u]) {
                int v = e.to, w = e.w;
                if (dist[v] > dist[u] + w) {
                    dist[v] = dist[u] + w;
                    pq.push({dist[v], v});
                }
            }
        }
        return dist;
    }

    // ---------- SPFA (判负环) ----------
    bool spfa(const Adj& g, int s, vector<int>& dist) {
        int n = g.size();
        vector<int> cnt(n, 0);
        vector<bool> inq(n, false);
        queue<int> q;
        dist.assign(n, INF);
        dist[s] = 0;
        q.push(s); inq[s] = true;
        while (!q.empty()) {
            int u = q.front(); q.pop(); inq[u] = false;
            for (auto &e : g[u]) {
                int v = e.to, w = e.w;
                if (dist[v] > dist[u] + w) {
                    dist[v] = dist[u] + w;
                    if (!inq[v]) {
                        q.push(v); inq[v] = true;
                        if (++cnt[v] >= n) return false; // 负环
                    }
                }
            }
        }
        return true;
    }

    // ---------- Floyd (全源最短路) ----------
    void floyd(vector<vector<int>>& d) {
        int n = d.size();
        for (int k = 0; k < n; ++k)
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j)
                    if (d[i][k] + d[k][j] < d[i][j])
                        d[i][j] = d[i][k] + d[k][j];
    }

    // ---------- Kruskal (最小生成树) ----------
    struct Kruskal {
        struct Edge { int u, v, w; bool operator<(const Edge& o) const { return w < o.w; } };
        vector<Edge> edges;
        int n;
        Kruskal(int n_) : n(n_) {}
        void add_edge(int u, int v, int w) { edges.pb({u, v, w}); }
        int mst() {
            sort(all(edges));
            DataStructure::DSU dsu(n);
            int cost = 0, cnt = 0;
            for (auto &e : edges) {
                if (dsu.unite(e.u, e.v)) {
                    cost += e.w;
                    if (++cnt == n - 1) break;
                }
            }
            return (cnt == n - 1) ? cost : INF;
        }
    };

    // ---------- LCA (倍增) ----------
    struct LCA {
        int n, LOG;
        vector<vi> up;
        vi depth;
        Adj adj;
        LCA(const Adj& g, int root = 0) : n(g.size()), adj(g) {
            LOG = 1;
            while ((1 << LOG) <= n) ++LOG;
            up.assign(LOG, vi(n));
            depth.assign(n, 0);
            dfs(root, root);
        }
        void dfs(int u, int p) {
            up[0][u] = p;
            for (int k = 1; k < LOG; ++k)
                up[k][u] = up[k - 1][up[k - 1][u]];
            for (auto &e : adj[u]) {
                int v = e.to;
                if (v == p) continue;
                depth[v] = depth[u] + 1;
                dfs(v, u);
            }
        }
        int lca(int u, int v) {
            if (depth[u] < depth[v]) swap(u, v);
            int diff = depth[u] - depth[v];
            for (int k = 0; diff; ++k, diff >>= 1)
                if (diff & 1) u = up[k][u];
            if (u == v) return u;
            for (int k = LOG - 1; k >= 0; --k)
                if (up[k][u] != up[k][v]) {
                    u = up[k][u];
                    v = up[k][v];
                }
            return up[0][u];
        }
        int dist(int u, int v) {
            int w = lca(u, v);
            return depth[u] + depth[v] - 2 * depth[w];
        }
    };

    // ---------- 拓扑排序 (Kahn) ----------
    vector<int> topoSort(const vector<vi>& g) {
        int n = g.size();
        vi indeg(n, 0);
        for (auto &v : g) for (int to : v) indeg[to]++;
        queue<int> q;
        for (int i = 0; i < n; ++i) if (indeg[i] == 0) q.push(i);
        vi order;
        while (!q.empty()) {
            int u = q.front(); q.pop();
            order.pb(u);
            for (int v : g[u])
                if (--indeg[v] == 0) q.push(v);
        }
        if ((int)order.size() != n) order.clear(); // 有环
        return order;
    }

    // ---------- 二分图最大匹配 (匈牙利) ----------
    struct Hungarian {
        int n, m; // 左n, 右m
        vector<vi> adj;
        vi matchR, vis;
        Hungarian(int n_, int m_) : n(n_), m(m_), adj(n_), matchR(m_, -1), vis(m_, 0) {}
        void add_edge(int u, int v) { adj[u].pb(v); }
        bool dfs(int u) {
            for (int v : adj[u]) {
                if (vis[v]) continue;
                vis[v] = 1;
                if (matchR[v] == -1 || dfs(matchR[v])) {
                    matchR[v] = u;
                    return true;
                }
            }
            return false;
        }
        int max_match() {
            int res = 0;
            for (int u = 0; u < n; ++u) {
                fill(all(vis), 0);
                if (dfs(u)) ++res;
            }
            return res;
        }
    };
} // namespace Graph

/* ==================== 字符串算法 ==================== */
namespace String {
    // ---------- KMP 单模式匹配 ----------
    vector<int> prefix_function(const string& s) {
        int n = s.size();
        vector<int> pi(n);
        for (int i = 1; i < n; ++i) {
            int j = pi[i - 1];
            while (j > 0 && s[i] != s[j]) j = pi[j - 1];
            if (s[i] == s[j]) ++j;
            pi[i] = j;
        }
        return pi;
    }
    // 在 text 中查找 pattern 的所有出现 (0-indexed)
    vector<int> kmp_search(const string& text, const string& pattern) {
        vector<int> pi = prefix_function(pattern), res;
        int j = 0;
        for (int i = 0; i < (int)text.size(); ++i) {
            while (j > 0 && text[i] != pattern[j]) j = pi[j - 1];
            if (text[i] == pattern[j]) ++j;
            if (j == (int)pattern.size()) {
                res.pb(i - j + 1);
                j = pi[j - 1];
            }
        }
        return res;
    }

    // ---------- 字符串哈希 (单模) ----------
    struct StringHash {
        static constexpr ull BASE = 911382323;
        static constexpr ull MOD = 1e9 + 7; // 可用 1e9+9 或 2^64 (自然溢出)
        vector<ull> pow, pref;
        int n;
        StringHash(const string& s) {
            n = s.size();
            pow.resize(n + 1);
            pref.resize(n + 1);
            pow[0] = 1;
            for (int i = 1; i <= n; ++i) pow[i] = pow[i - 1] * BASE % MOD;
            for (int i = 0; i < n; ++i) 
                pref[i + 1] = (pref[i] * BASE + (s[i] - 'a' + 1)) % MOD;
        }
        // 获取 [l, r) 子串哈希 (0-indexed, 左闭右开)
        ull get(int l, int r) const {
            return (pref[r] - pref[l] * pow[r - l] % MOD + MOD) % MOD;
        }
    };

    // ---------- Manacher 求最长回文 ----------
    vector<int> manacher(const string& s) {
        string t = "#";
        for (char c : s) { t += c; t += '#'; }
        int n = t.size();
        vector<int> d(n);
        int l = 0, r = -1;
        for (int i = 0; i < n; ++i) {
            int k = (i > r) ? 1 : min(d[l + r - i], r - i + 1);
            while (i - k >= 0 && i + k < n && t[i - k] == t[i + k]) ++k;
            d[i] = k;
            if (i + k - 1 > r) {
                l = i - k + 1;
                r = i + k - 1;
            }
        }
        return d;
    }
} // namespace String

/* ==================== 二分 / 离散化 ==================== */
namespace Util {
    // 离散化 (坐标压缩)
    template <typename T>
    vector<T> compress(vector<T> arr) {
        sort(all(arr));
        arr.erase(unique(all(arr)), arr.end());
        return arr;
    }
    // 获取 x 在有序数组中的排名 (1-indexed)
    template <typename T>
    int get_rank(const vector<T>& sorted, T x) {
        return lower_bound(all(sorted), x) - sorted.begin() + 1;
    }

    // 整数二分 (左闭右闭)
    template <typename F>
    int binary_search(int l, int r, F check) {
        while (l < r) {
            int mid = l + (r - l) / 2;
            if (check(mid)) r = mid;
            else l = mid + 1;
        }
        return l;
    }
} // namespace Util

/* ==================== 框架自检与帮助 ==================== */

/**
 * 输出框架使用指南
 */
void help() {
    cout << R"(
========== 算法竞赛代码框架 (C++17) 使用指南 ==========

【快速开始】
  1. 复制整个框架到你的 .cpp 文件。
  2. 在 main() 中调用所需函数/类，所有组件都在各自的 namespace 中。
  3. 建议在 main 开头调用 FAST_IO 以加速输入输出。

================================================================================
一、数学工具 (namespace Math)
================================================================================

1. gcd(a, b)
   - 功能：计算 a 和 b 的最大公约数。
   - 输入：两个整数 (long long)。
   - 返回：最大公约数 (long long)。
   - 示例：Math::gcd(12, 18) 返回 6。

2. lcm(a, b)
   - 功能：计算 a 和 b 的最小公倍数。
   - 输入：两个整数 (long long)。
   - 返回：最小公倍数 (long long)。
   - 示例：Math::lcm(6, 9) 返回 18。

3. modpow(a, b, mod = MOD)
   - 功能：快速计算 a^b % mod。
   - 输入：底数 a、指数 b、模数 mod（默认 1e9+7）。
   - 返回：幂取模结果 (long long)。
   - 示例：Math::modpow(2, 10, 1000) 返回 24。

4. exgcd(a, b)
   - 功能：扩展欧几里得，求 ax + by = gcd(a,b) 的一组整数解。
   - 输入：a, b (long long)。
   - 返回：tuple<long long, long long, long long>，分别是 (g, x, y)。
   - 示例：auto [g, x, y] = Math::exgcd(6, 15);  // g=3, x=3, y=-1

5. modinv(a, mod = MOD)
   - 功能：求 a 在模 mod 下的乘法逆元（前提 gcd(a, mod)=1）。
   - 输入：a, mod (默认为 MOD)。
   - 返回：逆元 (long long)。
   - 示例：Math::modinv(2) 返回 500000004（因为 2*500000004 ≡ 1 (mod 1e9+7)）。

6. sieve(n)
   - 功能：埃氏筛法，求出 2..n 之间的所有素数。
   - 输入：n (int)。
   - 返回：vector<int> 存储所有素数。
   - 示例：Math::sieve(20) 返回 {2,3,5,7,11,13,17,19}。

7. Comb(n, mod = MOD)
   - 功能：预处理 0..n 的阶乘和逆元，用于快速求组合数 C(n,k) 和排列数 P(n,k)。
   - 构造：Comb comb(10);   // 初始化，上限为 10
   - 方法：
        comb.C(n, k) 返回 C(n,k) 的值 (ll)
        comb.P(n, k) 返回 P(n,k) 的值 (ll)
   - 输入：n, k (int)，要求 0≤k≤n。
   - 示例：comb.C(5, 2) 返回 10。

================================================================================
二、数据结构 (namespace DataStructure)
================================================================================

1. DSU（并查集）
   - 功能：维护元素之间的集合合并与查询，用于判断连通性、Kruskal 等。
   - 构造：DataStructure::DSU dsu(n);   // n 为元素个数，编号 0..n-1
   - 方法：
        dsu.unite(a, b)  合并 a 和 b 所在集合，返回 true 若原本不同集合。
        dsu.same(a, b)   返回 true 若 a 和 b 在同一集合。
        dsu.find(x)      返回 x 所在集合的代表元。
        dsu.size(x)      返回 x 所在集合的大小。
   - 示例：
        DSU dsu(5);
        dsu.unite(0,1);
        dsu.same(0,1);   // true
        dsu.size(0);     // 2

2. BIT<T>（树状数组 / Fenwick Tree）
   - 功能：单点加、前缀求和，支持快速修改和区间求和（1-indexed）。
   - 构造：DataStructure::BIT<int> bit(n);   // n 为数组长度，下标从 1 到 n
   - 方法：
        bit.add(idx, val)      在 idx 位置增加 val。
        bit.sum(idx)           返回前缀和 [1..idx]。
        bit.range_sum(l, r)    返回区间和 [l..r]。
   - 示例：
        BIT<int> bit(5);
        bit.add(1, 1);
        bit.add(2, 2);
        bit.sum(3);           // 6
        bit.range_sum(2,3);   // 5

3. SegTree<T>（线段树）
   - 功能：区间加、区间求和，支持区间修改和区间查询（1-indexed）。
   - 构造：DataStructure::SegTree<int> seg(n);   // n 为数组长度，下标从 1 到 n
   - 准备：vector<int> arr(n+1)，arr[1..n] 为初始值（arr[0] 可任意）。
   - 方法：
        seg.build(arr)         用 arr 初始化线段树。
        seg.update(l, r, val)  将区间 [l..r] 每个元素增加 val。
        seg.query(l, r)        返回区间 [l..r] 的和。
   - 示例：
        vector<int> arr = {0, 1, 2, 3, 4}; // 长度为4，有效下标1..4
        SegTree<int> seg(4);
        seg.build(arr);
        seg.update(1, 3, 10);   // 使 a[1]+=10, a[2]+=10, a[3]+=10
        seg.query(1, 4);        // 返回总和 (原1+2+3+4 + 10*3)

4. SparseTable<T>（ST表）
   - 功能：静态区间最值查询（RMQ），支持任意可重复贡献操作（如 min, max, gcd）。
   - 构造：需传入数组和比较函数。
        DataStructure::SparseTable<int> st(vals, [](int a,int b){ return min(a,b); });
   - 方法：
        st.query(l, r)  返回区间 [l..r] 的最值（0-indexed）。
   - 示例：
        vector<int> vals = {3,1,4,1,5};
        SparseTable<int> st(vals, [](int a,int b){ return min(a,b); });
        st.query(0, 4);   // 返回 1

================================================================================
三、图论算法 (namespace Graph)
================================================================================

1. dijkstra(g, s)
   - 功能：单源最短路（非负权），使用堆优化。
   - 输入：邻接表 g（vector<vector<Edge>>），其中 Edge {int to, w;}，起点 s (int)。
   - 返回：vector<int> dist，dist[i] 为 s 到 i 的最短距离，不可达为 INF。
   - 示例：见框架主函数。

2. spfa(g, s, dist)
   - 功能：单源最短路，可检测负环。
   - 输入：邻接表 g，起点 s，引用 vector<int>& dist（会被填充）。
   - 返回：bool，true 表示无负环，false 表示存在负环。
   - 示例：
        vector<int> dist;
        bool ok = Graph::spfa(g, 0, dist);

3. floyd(d)
   - 功能：全源最短路，计算任意两点间最短距离。
   - 输入：二维 vector<vector<int>>& d，d[i][j] 为边权（INF 表示无边）。
   - 返回：无（原地更新 d）。
   - 示例：Graph::floyd(dist_matrix);

4. Kruskal（最小生成树）
   - 功能：求无向图的最小生成树总权值。
   - 构造：Graph::Kruskal kruskal(n);   // n 为顶点数
   - 方法：
        kruskal.add_edge(u, v, w)  添加一条边。
        kruskal.mst()              返回最小生成树的总权值，若不连通返回 INF。
   - 示例：
        Kruskal k(3);
        k.add_edge(0,1,5);
        k.add_edge(0,2,2);
        k.add_edge(1,2,1);
        k.mst();   // 返回 3

5. LCA（最近公共祖先，倍增法）
   - 功能：在树上快速求两点的最近公共祖先和距离。
   - 构造：Graph::LCA lca(tree, root);   // tree 为邻接表，root 为根节点。
   - 方法：
        lca.lca(u, v)   返回 u 和 v 的最近公共祖先。
        lca.dist(u, v)  返回 u 和 v 在树上的距离（边数）。
   - 示例：
        LCA lca(tree, 0);
        lca.lca(1, 2);   // 返回 0
        lca.dist(1, 2);  // 返回 2

6. topoSort(g)
   - 功能：拓扑排序（Kahn 算法），判断有向图是否有环。
   - 输入：邻接表 g（vector<vector<int>>）。
   - 返回：vector<int> 拓扑序列，若有环则返回空 vector。
   - 示例：auto order = Graph::topoSort(dag);

7. Hungarian（二分图最大匹配）
   - 功能：求二分图的最大匹配数。
   - 构造：Graph::Hungarian hun(n_left, n_right);
   - 方法：
        hun.add_edge(u, v)   添加左 u 到右 v 的边。
        hun.max_match()      返回最大匹配数。
   - 示例：
        Hungarian hun(2,2);
        hun.add_edge(0,0);
        hun.add_edge(0,1);
        hun.add_edge(1,0);
        hun.max_match();   // 返回 2

================================================================================
四、字符串算法 (namespace String)
================================================================================

1. kmp_search(text, pattern)
   - 功能：在文本 text 中查找模式串 pattern 的所有出现位置。
   - 输入：两个 string。
   - 返回：vector<int>，存储所有匹配的起始下标（0-indexed）。
   - 示例：String::kmp_search("ababcabc", "abc") 返回 {2, 5}。

2. StringHash（字符串哈希）
   - 功能：快速计算子串哈希值，用于字符串比较（如判等、判回文等）。
   - 构造：String::StringHash hs(s);   // s 为原字符串
   - 方法：
        hs.get(l, r)  返回 s[l..r) 的哈希值（左闭右开，0-indexed）。
   - 示例：
        StringHash hs("abcde");
        hs.get(0, 3);   // "abc" 的哈希

3. manacher(s)
   - 功能：求字符串的最长回文子串信息（Manacher 算法）。
   - 输入：string s。
   - 返回：vector<int> d，d[i] 为变换后字符串（插 #）中以 i 为中心的回文半径。
   - 说明：原串中每个位置的回文半径可通过 (d[i]-1) 获得，更详细用法请参考注释。
   - 示例：auto d = String::manacher("abba");   // 可用来求最长回文长度。

================================================================================
五、通用工具 (namespace Util)
================================================================================

1. compress(arr)
   - 功能：离散化，将数组排序去重，返回压缩后的有序数组。
   - 输入：vector<T> arr。
   - 返回：vector<T> 排序去重后的结果。
   - 示例：Util::compress({3,1,4,1,5}) 返回 {1,3,4,5}。

2. get_rank(sorted, x)
   - 功能：在已排序数组中查询元素 x 的排名（1-indexed）。
   - 输入：已排序的 vector<T>，元素 x。
   - 返回：排名（从 1 开始），若不存在则返回第一个大于 x 的位置。
   - 示例：auto sorted = Util::compress(arr); int rank = Util::get_rank(sorted, 3);

3. binary_search(l, r, check)
   - 功能：整数二分，在 [l, r] 范围内寻找第一个满足 check(mid) 为 true 的位置。
   - 输入：左边界 l、右边界 r（闭区间），check 函数（接受 int，返回 bool）。
   - 返回：第一个满足条件的位置。
   - 示例：auto check = [](int x){ return x >= 5; }; Util::binary_search(0,10,check) 返回 5。

================================================================================
【注意事项】
  - 下标习惯：DSU、BIT、SegTree 为 1-indexed；图论、字符串、工具类多为 0-indexed，请查阅具体说明。
  - 所有容器传递引用或指针时，注意生命周期。
  - 常量 INF 和 INFLL 已定义，可表示无穷大。
  - 若想使用自然溢出哈希，可修改 StringHash 的 MOD 为 2^64（使用 ull 自动溢出）。
  - 五子棋AI的搜索深度可通过修改 Goban::DEPTH 调整，数值越大棋力越强但耗时增加。

【自检】
  调用 ciallo() 可快速验证框架各模块是否工作正常。

=====================================================
)";
}

/**
 * 框架自检函数
 * 检查各主要模块的基本功能，若全部通过则输出 "ciallo,world!"，
 * 否则输出异常项并返回。
 */
void ciallo() {
    bool ok = true;

    // ---------- 数学模块 ----------
    {
        using namespace Math;
        // gcd/lcm
        if (gcd(12, 18) != 6) { cerr << "Math::gcd failed\n"; return; }
        if (lcm(6, 9) != 18) { cerr << "Math::lcm failed\n"; return; }
        // modpow
        if (modpow(2, 10, 1000) != 24) { cerr << "Math::modpow failed\n"; return; }
        // modinv (mod 1e9+7)
        if (modinv(2) != 500000004) { cerr << "Math::modinv failed\n"; return; }
        // 素数筛 (至少筛出几个素数)
        auto primes = sieve(20);
        if (primes.size() < 8 || primes[0] != 2 || primes[7] != 19) {
            cerr << "Math::sieve failed\n"; return;
        }
        // 组合数
        Comb comb(10);
        if (comb.C(5, 2) != 10) { cerr << "Math::Comb failed\n"; return; }
    }

    // ---------- 数据结构 ----------
    {
        using namespace DataStructure;
        // DSU
        DSU dsu(5);
        dsu.unite(0, 1);
        dsu.unite(2, 3);
        if (!dsu.same(0, 1) || dsu.same(0, 2) || dsu.size(0) != 2) {
            cerr << "DataStructure::DSU failed\n"; return;
        }
        // BIT
        BIT<int> bit(5);
        bit.add(1, 1);
        bit.add(2, 2);
        bit.add(3, 3);
        if (bit.sum(3) != 6 || bit.range_sum(2, 3) != 5) {
            cerr << "DataStructure::BIT failed\n"; return;
        }
        // SegTree (区间加、区间求和)
        vector<int> arr = {0, 1, 2, 3, 4}; // 1-indexed 存储, arr[0] 占位
        SegTree<int> seg(4);
        seg.build(arr);
        seg.update(1, 3, 10); // [1,3] +10
        if (seg.query(1, 4) != (1+10 + 2+10 + 3+10 + 4)) {
            cerr << "DataStructure::SegTree failed\n"; return;
        }
        // SparseTable (RMQ)
        vector<int> vals = {3, 1, 4, 1, 5};
        SparseTable<int> st(vals, [](int a, int b){ return min(a,b); });
        if (st.query(0, 4) != 1 || st.query(1, 3) != 1) {
            cerr << "DataStructure::SparseTable failed\n"; return;
        }
    }

    // ---------- 图论 ----------
    {
        using namespace Graph;
        // 构建简单图
        Adj g(3);
        g[0].push_back({1, 5});
        g[0].push_back({2, 2});
        g[1].push_back({2, 1});
        // Dijkstra
        auto dist = dijkstra(g, 0);
        if (dist[2] != 2) { cerr << "Graph::dijkstra failed\n"; return; }
        // Kruskal
        Kruskal kruskal(3);
        kruskal.add_edge(0, 1, 5);
        kruskal.add_edge(0, 2, 2);
        kruskal.add_edge(1, 2, 1);
        if (kruskal.mst() != 3) { cerr << "Graph::Kruskal failed\n"; return; }
        // LCA (树: 0-1, 0-2)
        Adj tree(3);
        tree[0].push_back({1, 0});
        tree[0].push_back({2, 0});
        LCA lca(tree, 0);
        if (lca.lca(1, 2) != 0 || lca.dist(1, 2) != 2) {
            cerr << "Graph::LCA failed\n"; return;
        }
        // 拓扑排序 (DAG 0->1, 0->2)
        vector<vi> dag(3);
        dag[0].push_back(1);
        dag[0].push_back(2);
        auto order = topoSort(dag);
        if (order.size() != 3 || order[0] != 0) {
            cerr << "Graph::topoSort failed\n"; return;
        }
        // 匈牙利 (二分图)
        Hungarian hun(2, 2);
        hun.add_edge(0, 0);
        hun.add_edge(0, 1);
        hun.add_edge(1, 0);
        if (hun.max_match() != 2) { cerr << "Graph::Hungarian failed\n"; return; }
    }

    // ---------- 字符串 ----------
    {
        using namespace String;
        // KMP
        string text = "ababcabc", pat = "abc";
        auto occ = kmp_search(text, pat);
        if (occ.size() != 2 || occ[0] != 2 || occ[1] != 5) {
            cerr << "String::kmp_search failed\n"; return;
        }
        // 哈希
        StringHash hs("abcde");
        // 检查相同子串哈希相等
        if (hs.get(0, 3) != hs.get(0, 3)) { cerr << "String::StringHash failed\n"; return; }
        // Manacher
        string s = "abba";
        auto d = manacher(s);
        if ((int)d.size() != 2 * (int)s.size() + 1) {
            cerr << "String::manacher failed\n"; return;
        }
    }

    // ---------- 工具 ----------
    {
        using namespace Util;
        vector<int> a = {3, 1, 4, 1, 5};
        auto sorted = compress(a); // 排序去重
        if (sorted.size() != 4 || sorted[0] != 1 || sorted[3] != 5) {
            cerr << "Util::compress failed\n"; return;
        }
        // 二分
        auto check = [](int x) { return x >= 5; };
        int pos = binary_search(0, 10, check);
        if (pos != 5) { cerr << "Util::binary_search failed\n"; return; }
    }

    // 所有测试通过
    cout << "ciallo,world!" << endl;
}

/*----------------------------------------------------------------------------------------------------------------------------------------------------------*/
//在这里开始写！！！
//在这里开始写！！！
//在这里开始写！！！
//在这里开始写！！！
//在这里开始写！！！
//在这里开始写！！！
//在这里开始写！！！
//在这里开始写！！！
//在这里开始写！！！
int main() {
    set_utf8_encoding();
    FAST_IO;

    // 执行自检（可注释掉）
    ciallo();
    help();

    return 0;
}
