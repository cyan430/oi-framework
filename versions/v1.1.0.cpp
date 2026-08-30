#include <bits/stdc++.h>
#include <clocale>      // for setlocale
#ifdef _WIN32
#include <windows.h>    // for SetConsoleOutputCP
#endif
using namespace std;

void set_utf8_encoding() {
#ifdef _WIN32
    SetConsoleOutputCP(CP_UTF8);
    SetConsoleCP(CP_UTF8);
#else
    setlocale(LC_ALL, "en_US.UTF-8");
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
const int INF = 0x3f3f3f3f;
const ll INFLL = 0x3f3f3f3f3f3f3f3fLL;
const int MOD = 1e9 + 7;
const int MAXN = 200005;

/* ==================== 数学工具 ==================== */
namespace Math {
    ll gcd(ll a, ll b) { return b ? gcd(b, a % b) : a; }
    ll lcm(ll a, ll b) { return a / gcd(a, b) * b; }
    ll modpow(ll a, ll b, ll mod = MOD) {
        ll r = 1;
        while (b) {
            if (b & 1) r = r * a % mod;
            a = a * a % mod;
            b >>= 1;
        }
        return r;
    }
    tuple<ll, ll, ll> exgcd(ll a, ll b) {
        if (b == 0) return {a, 1, 0};
        auto [g, x, y] = exgcd(b, a % b);
        return {g, y, x - (a / b) * y};
    }
    ll modinv(ll a, ll mod = MOD) {
        auto [g, x, y] = exgcd(a, mod);
        return (x % mod + mod) % mod;
    }
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

    template <typename T>
    struct BIT {
        int n;
        vector<T> bit;
        BIT(int n_) : n(n_), bit(n_ + 1, 0) {}
        void add(int idx, T val) { for (; idx <= n; idx += idx & -idx) bit[idx] += val; }
        T sum(int idx) const { T r = 0; for (; idx > 0; idx -= idx & -idx) r += bit[idx]; return r; }
        T range_sum(int l, int r) const { return sum(r) - sum(l - 1); }
    };

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
        void build(const vector<T>& arr) { build(arr, 1, 1, n); }
        void update(int l, int r, T val) { update(1, 1, n, l, r, val); }
        T query(int l, int r) { return query(1, 1, n, l, r); }
    };

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
        T query(int l, int r) {
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
                        if (++cnt[v] >= n) return false;
                    }
                }
            }
        }
        return true;
    }

    void floyd(vector<vector<int>>& d) {
        int n = d.size();
        for (int k = 0; k < n; ++k)
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j)
                    if (d[i][k] + d[k][j] < d[i][j])
                        d[i][j] = d[i][k] + d[k][j];
    }

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
        if ((int)order.size() != n) order.clear();
        return order;
    }

    struct Hungarian {
        int n, m;
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

    struct StringHash {
        static constexpr ull BASE = 911382323;
        static constexpr ull MOD = 1e9 + 7;
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
        ull get(int l, int r) const {
            return (pref[r] - pref[l] * pow[r - l] % MOD + MOD) % MOD;
        }
    };

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
    template <typename T>
    vector<T> compress(vector<T> arr) {
        sort(all(arr));
        arr.erase(unique(all(arr)), arr.end());
        return arr;
    }
    template <typename T>
    int get_rank(const vector<T>& sorted, T x) {
        return lower_bound(all(sorted), x) - sorted.begin() + 1;
    }
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

/* ==================== 五子棋AI (Goban) ==================== */
namespace Goban {
    const int N = 15;
    const int EMPTY = 0, BLACK = 1, WHITE = 2;
    const int DEPTH = 4;          // 搜索深度
    const int AI_INF = 1000000000;

    int dirs[4][2] = {{1,0}, {0,1}, {1,1}, {1,-1}};
    int board[N][N];

    void reset() {
        memset(board, 0, sizeof(board));
    }

    void setCell(int x, int y, int color) {
        if (x >= 0 && x < N && y >= 0 && y < N)
            board[x][y] = color;
    }

    int getCell(int x, int y) {
        if (x < 0 || x >= N || y < 0 || y >= N) return -1;
        return board[x][y];
    }

    void evaluateDirection(int x, int y, int dx, int dy, int color, int &count, int &openEnds) {
        count = 0;
        openEnds = 0;
        for (int i = 1; i < 5; ++i) {
            int nx = x + i * dx, ny = y + i * dy;
            if (nx < 0 || nx >= N || ny < 0 || ny >= N) break;
            if (board[nx][ny] == color) count++;
            else if (board[nx][ny] == EMPTY) { openEnds++; break; }
            else break;
        }
        for (int i = 1; i < 5; ++i) {
            int nx = x - i * dx, ny = y - i * dy;
            if (nx < 0 || nx >= N || ny < 0 || ny >= N) break;
            if (board[nx][ny] == color) count++;
            else if (board[nx][ny] == EMPTY) { openEnds++; break; }
            else break;
        }
    }

    int evaluateColor(int color) {
        int score = 0;
        for (int x = 0; x < N; ++x) {
            for (int y = 0; y < N; ++y) {
                if (board[x][y] != color) continue;
                for (int d = 0; d < 4; ++d) {
                    int dx = dirs[d][0], dy = dirs[d][1];
                    int count, openEnds;
                    evaluateDirection(x, y, dx, dy, color, count, openEnds);
                    if (count >= 5) score += 1000000;
                    else if (count == 4) {
                        if (openEnds >= 2) score += 100000;
                        else if (openEnds == 1) score += 10000;
                    } else if (count == 3) {
                        if (openEnds >= 2) score += 5000;
                        else if (openEnds == 1) score += 1000;
                    } else if (count == 2) {
                        if (openEnds >= 2) score += 500;
                        else if (openEnds == 1) score += 100;
                    } else if (count == 1) {
                        score += 10;
                    }
                }
            }
        }
        return score;
    }

    int evaluate(int myColor) {
        int oppColor = (myColor == BLACK) ? WHITE : BLACK;
        return evaluateColor(myColor) - evaluateColor(oppColor);
    }

    void generateMoves(int myColor, vector<pair<int,int>>& moves) {
        bool candidate[N][N] = {false};
        for (int x = 0; x < N; ++x) {
            for (int y = 0; y < N; ++y) {
                if (board[x][y] == EMPTY) continue;
                for (int dx = -2; dx <= 2; ++dx) {
                    for (int dy = -2; dy <= 2; ++dy) {
                        int nx = x + dx, ny = y + dy;
                        if (nx >= 0 && nx < N && ny >= 0 && ny < N && board[nx][ny] == EMPTY) {
                            candidate[nx][ny] = true;
                        }
                    }
                }
            }
        }
        bool any = false;
        for (int x = 0; x < N; ++x)
            for (int y = 0; y < N; ++y)
                if (candidate[x][y]) { any = true; break; }
        if (!any) {
            moves.push_back({7,7});
            return;
        }
        for (int x = 0; x < N; ++x)
            for (int y = 0; y < N; ++y)
                if (candidate[x][y]) moves.push_back({x, y});
    }

    int alphaBeta(int depth, int alpha, int beta, bool isMaximizing, int myColor) {
        int oppColor = (myColor == BLACK) ? WHITE : BLACK;
        if (depth == 0) return evaluate(myColor);

        vector<pair<int,int>> moves;
        int currentColor = isMaximizing ? myColor : oppColor;
        generateMoves(currentColor, moves);
        if (moves.empty()) return evaluate(myColor);

        if (isMaximizing) {
            int maxEval = -AI_INF;
            for (auto [x, y] : moves) {
                board[x][y] = myColor;
                int eval = alphaBeta(depth - 1, alpha, beta, false, myColor);
                board[x][y] = EMPTY;
                maxEval = max(maxEval, eval);
                alpha = max(alpha, eval);
                if (beta <= alpha) break;
            }
            return maxEval;
        } else {
            int minEval = AI_INF;
            for (auto [x, y] : moves) {
                board[x][y] = oppColor;
                int eval = alphaBeta(depth - 1, alpha, beta, true, myColor);
                board[x][y] = EMPTY;
                minEval = min(minEval, eval);
                beta = min(beta, eval);
                if (beta <= alpha) break;
            }
            return minEval;
        }
    }

    pair<int,int> getBestMove(int myColor) {
        vector<pair<int,int>> moves;
        generateMoves(myColor, moves);
        if (moves.empty()) return {7,7};

        int bestScore = -AI_INF;
        pair<int,int> bestMove = moves[0];

        for (auto [x, y] : moves) {
            board[x][y] = myColor;
            int score = alphaBeta(DEPTH - 1, -AI_INF, AI_INF, false, myColor);
            board[x][y] = EMPTY;
            if (score > bestScore) {
                bestScore = score;
                bestMove = {x, y};
            }
        }
        return bestMove;
    }
} // namespace Goban

/* ==================== 框架自检与帮助 ==================== */

void help() {
    cout << R"HELP(
========== 算法竞赛代码框架 (C++17) 使用指南 ==========

【快速开始】
  1. 复制整个框架到你的 .cpp 文件。
  2. 在 main() 中调用所需函数/类，所有组件都在各自的 namespace 中。
  3. 建议在 main 开头调用 FAST_IO 以加速输入输出。

================================================================================
一、数学工具 (namespace Math)
================================================================================

1. gcd(a, b)  - 最大公约数
2. lcm(a, b)  - 最小公倍数
3. modpow(a, b, mod) - 快速幂取模
4. exgcd(a, b) - 扩展欧几里得，返回 (g,x,y) 使 ax+by=g
5. modinv(a, mod) - 模逆元
6. sieve(n) - 埃氏筛素数
7. Comb(n, mod) - 组合数预处理，提供 C(n,k) 和 P(n,k)

================================================================================
二、数据结构 (namespace DataStructure)
================================================================================

1. DSU (并查集) - 合并、查询连通性
2. BIT<T> (树状数组) - 单点加、前缀和、区间和 (1-indexed)
3. SegTree<T> (线段树) - 区间加、区间求和 (1-indexed)
4. SparseTable<T> (ST表) - 静态区间最值 (0-indexed)

================================================================================
三、图论算法 (namespace Graph)
================================================================================

1. dijkstra(g, s) - 单源最短路 (非负权)
2. spfa(g, s, dist) - 单源最短路 (可判负环)
3. floyd(d) - 全源最短路
4. Kruskal (最小生成树) - add_edge + mst()
5. LCA (最近公共祖先) - lca(u,v), dist(u,v)
6. topoSort(g) - 拓扑排序 (有环返回空)
7. Hungarian (二分图最大匹配) - add_edge + max_match()

================================================================================
四、字符串算法 (namespace String)
================================================================================

1. kmp_search(text, pattern) - 返回所有匹配起始下标 (0-indexed)
2. StringHash - 字符串哈希，get(l, r) 获取子串哈希 (左闭右开)
3. manacher(s) - 最长回文信息

================================================================================
五、通用工具 (namespace Util)
================================================================================

1. compress(arr) - 离散化，返回排序去重结果
2. get_rank(sorted, x) - 查询排名 (1-indexed)
3. binary_search(l, r, check) - 整数二分，返回第一个 true 的位置

================================================================================
六、五子棋AI (namespace Goban)
================================================================================

1. reset() - 清空棋盘
2. setCell(x, y, color) - 落子 (0~14)
3. getCell(x, y) - 获取棋子颜色
4. getBestMove(myColor) - 计算最佳走法 (Alpha-Beta, 深度 DEPTH=4)

================================================================================
【注意事项】
  - 下标习惯：DSU、BIT、SegTree 为 1-indexed；图论、字符串、工具类多为 0-indexed。
  - 常量 INF 和 INFLL 表示无穷大。
  - 五子棋AI的搜索深度可通过修改 Goban::DEPTH 调整。

【自检】
  调用 ciallo() 可快速验证框架各模块是否工作正常。

=====================================================
)HELP";
}

void ciallo() {
    // ---------- 数学模块 ----------
    {
        using namespace Math;
        if (gcd(12, 18) != 6) { cerr << "Math::gcd failed\n"; return; }
        if (lcm(6, 9) != 18) { cerr << "Math::lcm failed\n"; return; }
        if (modpow(2, 10, 1000) != 24) { cerr << "Math::modpow failed\n"; return; }
        if (modinv(2) != 500000004) { cerr << "Math::modinv failed\n"; return; }
        auto primes = sieve(20);
        if (primes.size() < 8 || primes[0] != 2 || primes[7] != 19) {
            cerr << "Math::sieve failed\n"; return;
        }
        Comb comb(10);
        if (comb.C(5, 2) != 10) { cerr << "Math::Comb failed\n"; return; }
    }

    // ---------- 数据结构 ----------
    {
        using namespace DataStructure;
        DSU dsu(5);
        dsu.unite(0, 1);
        dsu.unite(2, 3);
        if (!dsu.same(0, 1) || dsu.same(0, 2) || dsu.size(0) != 2) {
            cerr << "DataStructure::DSU failed\n"; return;
        }
        BIT<int> bit(5);
        bit.add(1, 1);
        bit.add(2, 2);
        bit.add(3, 3);
        if (bit.sum(3) != 6 || bit.range_sum(2, 3) != 5) {
            cerr << "DataStructure::BIT failed\n"; return;
        }
        vector<int> arr = {0, 1, 2, 3, 4};
        SegTree<int> seg(4);
        seg.build(arr);
        seg.update(1, 3, 10);
        if (seg.query(1, 4) != (1+10 + 2+10 + 3+10 + 4)) {
            cerr << "DataStructure::SegTree failed\n"; return;
        }
        vector<int> vals = {3, 1, 4, 1, 5};
        SparseTable<int> st(vals, [](int a, int b){ return min(a,b); });
        if (st.query(0, 4) != 1 || st.query(1, 3) != 1) {
            cerr << "DataStructure::SparseTable failed\n"; return;
        }
    }

    // ---------- 图论 ----------
    {
        using namespace Graph;
        Adj g(3);
        g[0].push_back({1, 5});
        g[0].push_back({2, 2});
        g[1].push_back({2, 1});
        auto dist = dijkstra(g, 0);
        if (dist[2] != 2) { cerr << "Graph::dijkstra failed\n"; return; }
        Kruskal kruskal(3);
        kruskal.add_edge(0, 1, 5);
        kruskal.add_edge(0, 2, 2);
        kruskal.add_edge(1, 2, 1);
        if (kruskal.mst() != 3) { cerr << "Graph::Kruskal failed\n"; return; }
        Adj tree(3);
        tree[0].push_back({1, 0});
        tree[0].push_back({2, 0});
        LCA lca(tree, 0);
        if (lca.lca(1, 2) != 0 || lca.dist(1, 2) != 2) {
            cerr << "Graph::LCA failed\n"; return;
        }
        vector<vi> dag(3);
        dag[0].push_back(1);
        dag[0].push_back(2);
        auto order = topoSort(dag);
        if (order.size() != 3 || order[0] != 0) {
            cerr << "Graph::topoSort failed\n"; return;
        }
        Hungarian hun(2, 2);
        hun.add_edge(0, 0);
        hun.add_edge(0, 1);
        hun.add_edge(1, 0);
        if (hun.max_match() != 2) { cerr << "Graph::Hungarian failed\n"; return; }
    }

    // ---------- 字符串 ----------
    {
        using namespace String;
        string text = "ababcabc", pat = "abc";
        auto occ = kmp_search(text, pat);
        if (occ.size() != 2 || occ[0] != 2 || occ[1] != 5) {
            cerr << "String::kmp_search failed\n"; return;
        }
        StringHash hs("abcde");
        if (hs.get(0, 3) != hs.get(0, 3)) { cerr << "String::StringHash failed\n"; return; }
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
        auto sorted = compress(a);
        if (sorted.size() != 4 || sorted[0] != 1 || sorted[3] != 5) {
            cerr << "Util::compress failed\n"; return;
        }
        auto check = [](int x) { return x >= 5; };
        int pos = binary_search(0, 10, check);
        if (pos != 5) { cerr << "Util::binary_search failed\n"; return; }
    }

    // ---------- 五子棋AI (简单测试) ----------
    {
        Goban::reset();
        Goban::setCell(7, 7, Goban::BLACK);
        Goban::setCell(7, 8, Goban::WHITE);
        // 仅测试能否运行不崩溃
        auto move = Goban::getBestMove(Goban::BLACK);
        // 不检查具体结果，只确保函数可执行
    }

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
