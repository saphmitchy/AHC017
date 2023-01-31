#ifdef ONLINE_JUDGE
#define NDEBUG
#endif

#include <algorithm>
#include <bitset>
#include <cassert>
#include <climits>
#include <cmath>
#include <complex>
#include <ctime>
#include <functional>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <valarray>
#include <vector>

#define rep(i, n) for (int i = 0; i < int(n); i++)
#define per(i, n) for (int i = (n)-1; i >= 0; i--)
#define rep2(i, n, s) for (int i = (s); i < int(n); i++)
#define per2(i, n, s) for (int i = (n)-1; i >= int(s); i--)
#define MM << " " <<
#define all(x) begin(x), end(x)
#define rall(x) rbegin(x), rend(x)

template<class T>
using MinHeap = std::priority_queue<T, std::vector<T>, std::greater<T>>;
template<class T>
using MaxHeap = std::priority_queue<T>;

using ll  = long long;
using pii = std::pair<int, int>;
using pll = std::pair<ll, ll>;
using pdd = std::pair<double, double>;

template<class T>
bool chmin(T &a, const T b) {
    if (b < a) {
        a = b;
        return true;
    } else {
        return false;
    }
}

template<class T>
bool chmax(T &a, const T b) {
    if (a < b) {
        a = b;
        return true;
    } else {
        return false;
    }
}

struct is_container {
    template<class C>
    static auto check(C *)
        -> decltype(std::begin(std::declval<C>()), std::true_type());
    template<class C>
    static auto check(...) -> std::false_type;

   public:
    template<class C>
    using type = decltype(check<std::remove_reference_t<C>>(nullptr));
};

template<class T>
void vdeb(T &val);

void make_index(int i, std::true_type) {
    std::cout << i << "| ";
}
void make_index(int, std::false_type) {
}

template<class T>
auto vdeb_impl(T &val, std::false_type) {
    std::cout << val << " ";
}

template<class T, class U>
auto vdeb_impl(std::pair<T, U> &val, std::false_type) {
    vdeb(val.first);
    std::cout << ":";
    vdeb(val.second);
}

template<class T>
void vdeb_impl(T &val, std::true_type) {
    int idx = 0;
    for (auto &i : val) {
        make_index(idx++, is_container::type<decltype(i)>());
        vdeb(i);
    }
    std::cout << std::endl;
}

template<class T, class U>
void vdeb_impl(std::map<T, U> &val, std::true_type) {
    for (auto &i : val) {
        vdeb(i);
        std::cout << ", ";
    }
    std::cout << std::endl;
}

template<class T>
void vdeb(T &val) {
    vdeb_impl(val, is_container::type<T>());
}

class UnionFind {
    int              _n;
    int              _size;
    std::vector<int> par_size;

   public:
    UnionFind() : _n(0), _size(0) {
    }
    UnionFind(int n) : _n(n), _size(n), par_size(n, -1) {
    }

    int unite(int a, int b) {
        assert(0 <= a && a < _n);
        assert(0 <= b && b < _n);
        a = root(a), b = root(b);
        if (a == b) return a;
        _size--;
        if (-par_size[a] < -par_size[b]) {
            par_size[b] += par_size[a];
            return par_size[a] = b;
        } else {
            par_size[a] += par_size[b];
            return par_size[b] = a;
        }
    }

    int root(int a) {
        assert(0 <= a && a < _n);
        if (par_size[a] < 0) return a;
        return par_size[a] = root(par_size[a]);
    }

    bool same(int a, int b) {
        assert(0 <= a && a < _n);
        assert(0 <= b && b < _n);
        return root(a) == root(b);
    }

    int size(int a) {
        assert(0 <= a && a < _n);
        return -par_size[root(a)];
    }

    int size() {
        return _size;
    }

    std::vector<std::vector<int>> groups() {
        std::vector<int> leader_buf(_n), group_size(_n);
        for (int i = 0; i < _n; i++) {
            leader_buf[i] = root(i);
            group_size[leader_buf[i]]++;
        }
        std::vector<std::vector<int>> result(_n);
        for (int i = 0; i < _n; i++) {
            result[i].reserve(group_size[i]);
        }
        for (int i = 0; i < _n; i++) {
            result[leader_buf[i]].push_back(i);
        }
        result.erase(std::remove_if(
                         result.begin(),
                         result.end(),
                         [&](const std::vector<int> &v) { return v.empty(); }),
                     result.end());
        return result;
    }
};

using namespace std;

using vertex_t  = int;
using edge_idx  = size_t;
using weight_t  = ll;
using ans_vec_t = bitset<3008>;

const ll      MAX_PENA = 1'000'000'000;
random_device seed_gen;
mt19937       mt(seed_gen());
clock_t       begin_time;

struct Edge {
    vertex_t v0;
    vertex_t v1;
    weight_t w;
    edge_idx id;
    Edge(vertex_t _v0, vertex_t _v1, weight_t _w, edge_idx _id)
        : v0(_v0), v1(_v1), w(_w), id(_id) {
    }
    Edge() : v0(-1), v1(-1), w(-1), id(-1) {
    }
};

bool operator<(const Edge &lhs, const Edge &rhs) {
    return lhs.w > rhs.w;
    // if (lhs.v0 == rhs.v0)
    //     return lhs.v1 < rhs.v1;
    // else
    //     return lhs.v0 < rhs.v0;
}

struct DEdge {
    const vertex_t to;
    const weight_t w;
    const edge_idx id;
    DEdge(vertex_t _to, weight_t _w, edge_idx _id) : to(_to), w(_w), id(_id) {
    }
};

struct Point {
    int x, y;
};

struct Solver {
    const int                          N, M, D, K;
    vector<Edge>                       edge;
    vector<Edge>                       sorted_edge;
    vector<Point>                      p;
    vector<ans_vec_t>                  ans;
    vector<vector<DEdge>>              gph;
    uniform_int_distribution<edge_idx> randM;
    uniform_int_distribution<edge_idx> randD_1;

    void input_edge() {
        rep(i, M) {
            int v0, v1, w;
            cin >> v0 >> v1 >> w;
            --v0;
            --v1;
            edge[i] = Edge(v0, v1, w, i);
            gph[v0].emplace_back(v1, w, i);
            gph[v1].emplace_back(v0, w, i);
        }
        sorted_edge = edge;
        sort(all(sorted_edge));
    }

    void input_point() {
        for (auto &i : p) {
            cin >> i.x >> i.y;
        }
    }

    pair<ll, double> connection_and_degree(int day) const {
        UnionFind   uf(N);
        int         disconnect = N * (N - 1) / 2;
        vector<int> degree(N);
        for (auto &e : edge) {
            if (ans[day][e.id]) continue;
            vertex_t a = e.v0;
            vertex_t b = e.v1;
            degree[a]++;
            degree[b]++;
            if (uf.same(a, b)) continue;
            disconnect -= uf.size(a) * uf.size(b);
            uf.unite(a, b);
        }
        double degereeSum = 0.0;
        for (auto &i : gph) {
            int ncnt = 0, mcnt = 0;
            for (auto &j : i) {
                mcnt += gph[j.to].size() - 1;
                if (ans[day][j.id]) continue;
                ncnt += degree[j.to] - 1;
            }
            auto tmp = 1.0 - (double)ncnt / mcnt;
            degereeSum += tmp * tmp;
        }
        return {disconnect, degereeSum};
    }

    ll connection(int day) {
        UnionFind uf(N);
        int       disconnect = N * (N - 1) / 2;
        for (auto &e : edge) {
            if (ans[day][e.id]) continue;
            vertex_t a = e.v0;
            vertex_t b = e.v1;
            if (uf.same(a, b)) continue;
            disconnect -= uf.size(a) * uf.size(b);
            uf.unite(a, b);
        }
        return disconnect;
    }

    void init_ans() {
        for (auto &e : sorted_edge) {
            using score_type =
                decltype(connection_and_degree(declval<edge_idx>()));
            score_type now = {N * N, LLONG_MAX / 2};
            int        id  = -1;
            rep(d, D) {
                ans[d].set(e.id);
                if ((int)ans[d].count() < K &&
                    chmin(now, connection_and_degree(d)))
                    id = d;
                ans[d].reset(e.id);
            }
            ans[id].set(e.id);
        }
    }

    auto check_diff(edge_idx eid, int day) {
        ans[day].flip(eid);
        auto res =
            shortest_path(edge[eid].v0, day) + shortest_path(edge[eid].v1, day);
        ans[day].flip(eid);
        res -=
            shortest_path(edge[eid].v0, day) + shortest_path(edge[eid].v1, day);
        return res;
    }

    void output() const {
        vector<int> out(M);
        rep(i, M) {
            rep(j, D) {
                if (ans[j][i]) out[i] = j + 1;
            }
        }
        vdeb(out);
    }

    weight_t twopoint_shortest_path(vertex_t s, vertex_t t, int day) {
        assert(0 <= day && day < D);
        vector<bool> used(M, false);
        using heapNode = pair<weight_t, vertex_t>;
        MinHeap<heapNode> que;
        que.push({0, s});
        while (!que.empty()) {
            auto [w, v] = que.top();
            que.pop();
            if (used[v]) continue;
            if (v == t) return w;
            used[v] = true;
            for (auto &e : gph[v]) {
                if (!used[e.to] && !ans[day][e.id]) {
                    que.push({w + e.w, e.to});
                }
            }
        }
        return MAX_PENA;
    }

    weight_t shortest_path(vertex_t s) const {
        vector<weight_t> dist(M, MAX_PENA);
        using heapNode = pair<weight_t, vertex_t>;
        MinHeap<heapNode> que;
        que.push({0, s});
        while (!que.empty()) {
            auto [w, v] = que.top();
            que.pop();
            if (dist[v] != MAX_PENA) continue;
            dist[v] = w;
            for (auto &e : gph[v]) {
                if (dist[e.to] == MAX_PENA) {
                    que.push({w + e.w, e.to});
                }
            }
        }
        return accumulate(all(dist), 0LL);
    }

    weight_t shortest_path(vertex_t s, int day) const {
        assert(0 <= day && day < D);
        vector<weight_t> dist(M, MAX_PENA);
        using heapNode = pair<weight_t, vertex_t>;
        MinHeap<heapNode> que;
        que.push({0, s});
        while (!que.empty()) {
            auto [w, v] = que.top();
            que.pop();
            if (dist[v] != MAX_PENA) continue;
            dist[v] = w;
            for (auto &e : gph[v]) {
                if (dist[e.to] == MAX_PENA && !ans[day][e.id]) {
                    que.push({w + e.w, e.to});
                }
            }
        }
        return accumulate(all(dist), 0LL);
    }

    // day = -1 のとき全部使える
    double calc_score(int day) const {
        ll res = 0;
        rep(i, N) res -= shortest_path(i);
        rep(i, N) res += shortest_path(i, day);
        return (double)res / (N * (N - 1));
    }

    ll calc_score_all() const {
        double res = 0;
        rep(i, D) res += calc_score(i);
        return round(res / D * 1000);
    }

    void anneal() {
        while ((clock() - begin_time) < 5.7 * CLOCKS_PER_SEC) {
            auto crr_edge   = randM(mt);
            auto crr_offset = randD_1(mt);
            int  a = -1, b = -1;
            rep(d, D) {
                if (ans[d][crr_edge]) {
                    a = d;
                    b = a + crr_offset;
                    if (D <= b) b -= D;
                    break;
                }
            }
            if((int)ans[b].count() == K) continue;
            auto connect1 = connection(b);
            ans[b].flip(crr_edge);
            auto connect2 = connection(b);
            ans[b].flip(crr_edge);
            if (connect2 <= connect1 &&
                check_diff(crr_edge, a) + check_diff(crr_edge, b) < 0) {
                ans[a].flip(crr_edge);
                ans[b].flip(crr_edge);
            }
        }
    }

    Solver(int n, int m, int d, int k)
        : N(n),
          M(m),
          D(d),
          K(k),
          edge(m),
          p(n),
          ans(d),
          gph(n),
          randM(0, M - 1),
          randD_1(0, D - 2) {
        input_edge();
        input_point();
        init_ans();
        anneal();
    }
};

int main() {
    begin_time = clock();
    ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    int n, m, d, k;
    cin >> n >> m >> d >> k;
    Solver solve(n, m, d, k);
    solve.output();
}