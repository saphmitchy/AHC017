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

using vertex_t    = int;
using edge_idx    = size_t;
using weight_t    = ll;
using ans_vec_t   = bitset<3008>;
using vertex_mask = bitset<1024>;

const weight_t MAX_PENA   = 1'000'000'000;
const vertex_t NONE       = -1;
const double   TIME_LIMIT = 5.7;
random_device  seed_gen;
mt19937        mt(seed_gen());
clock_t        begin_time;

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

struct Schedule {
    const int   M;
    const int   D;
    vector<int> ans;
    vector<int> counter;

    Schedule(const int m, const int d) : M(m), D(d), ans(m, -1), counter(d) {
    }

    bool is_avalable(const vertex_t eid, const int day) const {
        return ans[eid] != day;
    }

    void set_day(const vertex_t eid, const int day) {
        if (ans[eid] != NONE) counter[ans[eid]]--;
        ans[eid] = day;
        if (day != NONE) counter[day]++;
    }

    int count(int day) const {
        return counter[day];
    }

    int get(vertex_t eid) const {
        return ans[eid];
    }
};

#define TRY_FLIP(schedule, eid, day, ...) \
    auto tmp_day = schedule.ans[eid];     \
    if (tmp_day == day) {                 \
        schedule.ans[eid] = -1;           \
    } else {                              \
        schedule.ans[eid] = day;          \
    }                                     \
    schedule.counter[tmp_day]--;          \
    __VA_ARGS__                           \
    schedule.counter[tmp_day]++;          \
    schedule.ans[eid] = tmp_day;

struct MiniGraph {
    static const int loop_count = 100;
    const int        N;
    const int        D;
    const int        K;

    vector<vector<DEdge>>         gph;
    vector<vector<vector<DEdge>>> dgph;
    map<vertex_t, vertex_t>       global2local;
    vector<vertex_t>              local2global;
    edge_idx                      edge_count;
    vector<Edge>                  edge;
    vector<ans_vec_t>             ans;

    MiniGraph(int d, int k, const vector<vertex_t> &g)
        : N(g.size()),
          D(d),
          K(k),
          gph(g.size()),
          dgph(D, vector<vector<DEdge>>(N)),
          edge_count(0),
          ans(d) {
        local2global.reserve(g.size());
        int cnt = 0;
        for (auto &i : g) {
            global2local[cnt] = i;
            local2global.emplace_back(i);
            ++cnt;
        }
    }

    ll connection(const int day) {
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

    auto check_diff(const edge_idx eid, const int day) {
        ans[day].flip(eid);
        auto res =
            shortest_path(edge[eid].v0, day) + shortest_path(edge[eid].v1, day);
        ans[day].flip(eid);
        res -=
            shortest_path(edge[eid].v0, day) + shortest_path(edge[eid].v1, day);
        return res;
    }

    weight_t shortest_path(const vertex_t s, const int day) const {
        assert(0 <= day && day < D);
        vector<weight_t> dist(edge_count, MAX_PENA);
        using heapNode = pair<weight_t, vertex_t>;
        MinHeap<heapNode> que;
        que.push({0, s});
        while (!que.empty()) {
            const auto [w, v] = que.top();
            que.pop();
            if (dist[v] != MAX_PENA) continue;
            dist[v] = w;
            for (const auto &e : gph[v]) {
                if (dist[e.to] == MAX_PENA && !ans[day][e.id]) {
                    que.push({w + e.w, e.to});
                }
            }
            for (const auto &e : dgph[day][v]) {
                if (dist[e.to] == MAX_PENA && !ans[day][e.id]) {
                    que.push({w + e.w, e.to});
                }
            }
        }
        return accumulate(all(dist), 0LL);
    }

    edge_idx add_edge(const vertex_t from,
                      const vertex_t to,
                      const weight_t w,
                      const int      unused_day) {
        edge.emplace_back(from, to, w, edge_count);
        gph[global2local[from]].emplace_back(local2global[to], w, edge_count);
        ans[unused_day].set(edge_count);
        return edge_count++;
    }

    void add_day_edge(const vertex_t from,
                      const vertex_t to,
                      const weight_t w,
                      const int      day) {
        edge.emplace_back(from, to, w, edge_count);
        dgph[day][global2local[from]].emplace_back(
            local2global[to], w, edge_count);
        // ++edge_count;
    }

    bool thermo(long long diff) {
        return diff < 0;
        // return exp(-diff/2e12*(clock() - begin_time)) * mt19937::max() >
        // mt();
    }

    void anneal() {
        uniform_int_distribution<edge_idx> select_edge(0, edge_count - 1);
        uniform_int_distribution<int>      select_day(0, D - 1);
        rep(i, 100) {
            const auto crr_edge   = select_edge(mt);
            const auto crr_offset = select_day(mt);
            int        a = -1, b = -1;
            rep(d, D) {
                if (ans[d][crr_edge]) {
                    a = b;
                    b = a + crr_offset;
                    if (D <= b) b -= D;
                    break;
                }
            }
            if ((int)ans[b].count() == K) continue;
            const auto connect1 = connection(b);
            ans[b].flip(crr_edge);
            const auto connect2 = connection(b);
            ans[b].flip(crr_edge);
            const auto diff = check_diff(crr_edge, a) + check_diff(crr_edge, b);
            if (connect2 <= connect1 && thermo(diff)) {
                ans[a].flip(crr_edge);
                ans[b].flip(crr_edge);
            }
        }
    }
};

struct Solver {
    const int                          N, M, D, K;
    vector<Edge>                       edge;
    vector<Edge>                       sorted_edge;
    vector<Point>                      points;
    Schedule                           ans;
    vector<vector<DEdge>>              gph;
    uniform_int_distribution<edge_idx> randM;
    uniform_int_distribution<int>      randD_1;

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
        for (auto &i : points) {
            cin >> i.x >> i.y;
        }
    }

    pair<ll, double> connection_and_degree(const int day) const {
        UnionFind   uf(N);
        int         disconnect = N * (N - 1) / 2;
        vector<int> degree(N);
        for (auto &e : edge) {
            if (!ans.is_avalable(e.id, day)) continue;
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
                if (!ans.is_avalable(j.id, day)) continue;
                ncnt += degree[j.to] - 1;
            }
            const auto tmp = 1.0 - (double)ncnt / mcnt;
            degereeSum += tmp * tmp;
        }
        return {disconnect, degereeSum};
    }

    ll connection(const int day) {
        UnionFind uf(N);
        int       disconnect = N * (N - 1) / 2;
        for (auto &e : edge) {
            if (!ans.is_avalable(e.id, day)) continue;
            vertex_t a = e.v0;
            vertex_t b = e.v1;
            if (uf.same(a, b)) continue;
            disconnect -= uf.size(a) * uf.size(b);
            uf.unite(a, b);
        }
        return disconnect;
    }

    void init_ans() {
        for (const auto &e : sorted_edge) {
            using score_type =
                decltype(connection_and_degree(declval<edge_idx>()));
            score_type now     = {N * N, LLONG_MAX / 2};
            int        crr_day = -1;
            rep(d, D) {
                ans.set_day(e.id, d);
                if (ans.count(d) < K && chmin(now, connection_and_degree(d)))
                    crr_day = d;
                ans.set_day(e.id, NONE);
            }
            ans.set_day(e.id, crr_day);
            // cout << crr_day << " "; vdeb(ans.counter);
        }
    }

    auto check_diff(edge_idx eid, int day) {
        TRY_FLIP(ans,
                 eid,
                 day,
                 auto res = shortest_path(edge[eid].v0, day) +
                            shortest_path(edge[eid].v1, day);)
        res -=
            shortest_path(edge[eid].v0, day) + shortest_path(edge[eid].v1, day);
        return res;
    }

    void output() const {
        vector<int> out(M);
        rep(i, M) {
            out[i] = ans.get(i) + 1;
        }
        vdeb(out);
    }

    weight_t shortest_path(const vertex_t s) const {
        vector<weight_t> dist(M, MAX_PENA);
        using heapNode = pair<weight_t, vertex_t>;
        MinHeap<heapNode> que;
        que.push({0, s});
        while (!que.empty()) {
            const auto [w, v] = que.top();
            que.pop();
            if (dist[v] != MAX_PENA) continue;
            dist[v] = w;
            for (const auto &e : gph[v]) {
                if (dist[e.to] == MAX_PENA) {
                    que.push({w + e.w, e.to});
                }
            }
        }
        return accumulate(all(dist), 0LL);
    }

    weight_t shortest_path(const vertex_t s, const int day) const {
        assert(0 <= day && day < D);
        vector<weight_t> dist(M, MAX_PENA);
        using heapNode = pair<weight_t, vertex_t>;
        MinHeap<heapNode> que;
        que.push({0, s});
        while (!que.empty()) {
            const auto [w, v] = que.top();
            que.pop();
            if (dist[v] != MAX_PENA) continue;
            dist[v] = w;
            for (const auto &e : gph[v]) {
                if (dist[e.to] == MAX_PENA && ans.is_avalable(e.id, day)) {
                    que.push({w + e.w, e.to});
                }
            }
        }
        return accumulate(all(dist), 0LL);
    }

    // day = -1 のとき全部使える
    double calc_score(const int day) const {
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

    vector<vertex_t> accumulate_near(const Point &center, double dist) const {
        const double     sqdist = dist * 2;
        vector<vertex_t> res;
        res.reserve(30);
        rep(i, N) {
            int dx = center.x - points[i].x;
            int dy = center.y - points[i].y;
            if (dx * dx + dy * dy < sqdist) {
                res.emplace_back(i);
            }
        }
        return res;
    }

    pair<vertex_t, weight_t> shortest_element(const vertex_t   from,
                                              const DEdge     &e,
                                              const ans_vec_t &target_bit,
                                              const int        day) {
        vector<bool> used(N);
        used[from]     = true;
        using heapNode = pair<weight_t, vertex_t>;
        MinHeap<heapNode> que;
        que.push({0, e.to});
        while (!que.empty()) {
            const auto [w, v] = que.top();
            que.pop();
            if (used[v]) continue;
            if (target_bit[v]) return {v, w};
            used[v] = true;
            for (const auto &e : gph[v]) {
                if (!used[e.to] && ans.is_avalable(e.id, day)) {
                    que.push({w + e.w, e.to});
                }
            }
        }
        return {NONE, MAX_PENA};
    }

    void partial_update(const Point &center, double dist) {
        auto      target_v = accumulate_near(center, dist);
        ans_vec_t target_bit;
        for (auto &v : target_v) target_bit.set(v);
        MiniGraph mini(D, K, target_v);
        for (auto &v : target_v) {
            for (auto &e : gph[v]) {
                if (target_bit[e.to]) {
                    mini.add_edge(v, e.to, e.w, ans.get(e.id));
                }
            }
        }
    }

    bool thermo(long long diff) {
        // return true;
        return diff < 0;
        // return exp(-diff/2e12*(clock() - begin_time)) * mt19937::max() >
        // mt();
    }

    void anneal() {
        while ((clock() - begin_time) < TIME_LIMIT * CLOCKS_PER_SEC) {
            const auto crr_edge   = randM(mt);
            const auto crr_offset = randD_1(mt);
            int        a          = ans.get(crr_edge);
            int        b          = a + crr_offset;
            if (D <= b) b -= D;
            if (ans.count(b) == K) continue;
            const auto diff = check_diff(crr_edge, a) + check_diff(crr_edge, b);
            if (thermo(diff)) {
                ans.set_day(crr_edge, b);
            }
        }
    }

    Solver(int n, int m, int d, int k)
        : N(n),
          M(m),
          D(d),
          K(k),
          edge(m),
          points(n),
          ans(m, d),
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