#include <algorithm>
#include <bitset>
#include <cassert>
#include <climits>
#include <cmath>
#include <complex>
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

const ll MAX_PENA = 1'000'000'000;

struct Edge {
    vertex_t v[2];
    weight_t w;
    edge_idx id;
};

bool operator<(const Edge &lhs, const Edge &rhs) {
    return lhs.w < rhs.w;
}

struct DEdge {
    vertex_t to;
    weight_t w;
    edge_idx id;
    DEdge(vertex_t _to, weight_t _w, edge_idx _id) : to(_to), w(_w), id(_id) {
    }
};

struct Point {
    int x, y;
};

struct Solver {
    const int             N, M, D, K;
    vector<Edge>          edge;
    vector<Edge>          sorted_edge;
    vector<Point>         p;
    vector<ans_vec_t>     ans;
    vector<vector<DEdge>> gph;

    void input_edge() {
        rep(i, M) {
            int v0, v1, w;
            cin >> v0 >> v1 >> w;
            --v0;
            --v1;
            edge[i].v[0] = v0;
            edge[i].v[1] = v1;
            edge[i].w    = w;
            edge[i].id   = i;
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

    pair<int, ll> connection(int day) {
        UnionFind uf(N);
        int       disconnect = N * (N - 1) / 2;
        ll        w_sum      = 0;
        for (auto &e : edge) {
            if (ans[day][e.id]) continue;
            w_sum += e.w;
            vertex_t a = e.v[0];
            vertex_t b = e.v[1];
            if (uf.same(a, b)) continue;
            disconnect -= uf.size(a) * uf.size(b);
            uf.unite(a, b);
        }
        return {disconnect, -w_sum};
    }

    void init_ans() {
        rep(i, M) {
            int           id  = -1;
            pair<int, ll> now = {N * N, LLONG_MAX / 2};
            rep(d, D) {
                ans[d].set(i);
                if ((int)ans[d].count() < K && chmin(now, connection(d)))
                    id = d;
                ans[d].reset(i);
            }
            ans[id].set(i);
        }
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

    weight_t shortest_path(vertex_t s) {
        vector<weight_t>                  dist(M, MAX_PENA);
        MinHeap<pair<weight_t, vertex_t>> que;
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

    weight_t shortest_path(vertex_t s, int day) {
        assert(0 <= day && day < D);
        vector<weight_t>                  dist(M, MAX_PENA);
        MinHeap<pair<weight_t, vertex_t>> que;
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
    double calc_score(int day) {
        ll res = 0;
        rep(i, N) res -= shortest_path(i);
        rep(i, N) res += shortest_path(i, day);
        return (double)res / (N * (N - 1));
    }

    ll calc_score_all() {
        double res = 0;
        rep(i, D) res += calc_score(i);
        return round(res / D * 1000);
    }

    Solver(int n, int m, int d, int k)
        : N(n), M(m), D(d), K(k), edge(m), p(n), ans(d), gph(n) {
        input_edge();
        input_point();
        init_ans();
    }
};

int main() {
    ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    int n, m, d, k;
    cin >> n >> m >> d >> k;
    Solver solve(n, m, d, k);
    solve.output();
}