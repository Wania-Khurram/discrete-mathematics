#include <iostream>
#include <vector>
#include <algorithm> // For sort, unique, set_union, etc.
#include <functional> // For std::function (Lambda support)
#include <cmath>     // For pow() used in Power Set
#include <string>
#include <utility>   // For std::pair
#include <climits>   // For INT_MAX
#include <iomanip>
#include <sstream>
#include <queue>     // For Priority Queue (Dijkstra)

// ==========================================
// UTILITY FOR MENU INPUT
// ==========================================
void clear_cin() {
    std::cin.clear(); // Reset error flags
    std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n'); // Discard bad input
}

// ==========================================
// MODULE 1.1: ENHANCED SET DATA STRUCTURE
// ==========================================
// A custom Set class since std::set doesn't support random access
// needed for some specific discrete math algorithms easily.
template <typename T>
class DiscreteSet {
private:
    std::vector<T> data;

    // Helper to enforce Set properties:
    // 1. No duplicates
    // 2. Elements are ordered (for easier comparison)
    void sort_and_unique() {
        std::sort(data.begin(), data.end());
        data.erase(std::unique(data.begin(), data.end()), data.end());
    }

public:
    DiscreteSet() {}
    DiscreteSet(std::initializer_list<T> list) : data(list) { sort_and_unique(); }
    DiscreteSet(const std::vector<T>& vec) : data(vec) { sort_and_unique(); }

    // Adds element only if it's not already in the set
    void add(T element) {
        if (!member(element)) {
            data.push_back(element);
            sort_and_unique();
        }
    }

    void delete_element(T element) {
        auto it = std::remove(data.begin(), data.end(), element);
        if (it != data.end()) {
            data.erase(it, data.end());
        }
    }

    // Binary search is O(log n), faster than linear search
    bool member(T element) const {
        return std::binary_search(data.begin(), data.end(), element);
    }

    int size() const { return data.size(); }
    bool empty() const { return data.empty(); }
    void clear_all() { data.clear(); }

    // Iterators for range-based for loops
    typename std::vector<T>::const_iterator begin() const { return data.begin(); }
    typename std::vector<T>::const_iterator end() const { return data.end(); }
    const std::vector<T>& get_data() const { return data; }

    // --- Set Operations (Using STL algorithms) ---

    DiscreteSet<T> set_union(const DiscreteSet<T>& other) const {
        DiscreteSet<T> result;
        std::vector<T> res_vec;
        // Standard merge of two sorted ranges
        std::set_union(data.begin(), data.end(), other.begin(), other.end(), std::back_inserter(res_vec));
        result.data = res_vec;
        return result;
    }

    DiscreteSet<T> set_intersection(const DiscreteSet<T>& other) const {
        DiscreteSet<T> result;
        std::vector<T> res_vec;
        // Elements present in BOTH sets
        std::set_intersection(data.begin(), data.end(), other.begin(), other.end(), std::back_inserter(res_vec));
        result.data = res_vec;
        return result;
    }

    DiscreteSet<T> set_difference(const DiscreteSet<T>& other) const {
        DiscreteSet<T> result;
        std::vector<T> res_vec;
        // Elements in A but NOT in B
        std::set_difference(data.begin(), data.end(), other.begin(), other.end(), std::back_inserter(res_vec));
        result.data = res_vec;
        return result;
    }

    DiscreteSet<T> symmetric_diff(const DiscreteSet<T>& other) const {
        DiscreteSet<T> result;
        std::vector<T> res_vec;
        // Elements in A OR B, but NOT both (XOR equivalent)
        std::set_symmetric_difference(data.begin(), data.end(), other.begin(), other.end(), std::back_inserter(res_vec));
        result.data = res_vec;
        return result;
    }

    bool is_subset(const DiscreteSet<T>& other) const {
        // Checks if all elements of 'this' are found in 'other'
        return std::includes(other.begin(), other.end(), data.begin(), data.end());
    }

    // Generates the Power Set (Set of all subsets)
    // Uses Bitwise Logic: Iterate from 0 to 2^n - 1
    DiscreteSet<DiscreteSet<T>> powerset() const {
        DiscreteSet<DiscreteSet<T>> result;
        int pow_set_size = pow(2, size());

        // Loop through all binary representations
        for (int i = 0; i < pow_set_size; i++) {
            DiscreteSet<T> subset;
            for (int j = 0; j < size(); j++) {
                // Check if j-th bit is set in counter i
                if (i & (1 << j)) subset.add(data[j]);
            }
            result.add(subset);
        }
        return result;
    }

    // Cartesian Product: A x B
    std::vector<std::pair<T, T>> cartesian_prod(const DiscreteSet<T>& other) const {
        std::vector<std::pair<T, T>> result;
        for (const auto& a : data) {
            for (const auto& b : other) {
                result.push_back({ a, b });
            }
        }
        return result;
    }

    // Operator overloads for printing and comparison
    bool operator<(const DiscreteSet<T>& other) const { return data < other.data; }
    bool operator==(const DiscreteSet<T>& other) const { return data == other.data; }

    friend std::ostream& operator<<(std::ostream& os, const DiscreteSet<T>& s) {
        os << "{";
        for (size_t i = 0; i < s.data.size(); ++i) {
            os << s.data[i];
            if (i < s.data.size() - 1) os << ",";
        }
        os << "}";
        return os;
    }
};

// ==========================================
// MODULE 1.2: PREDICATE ENGINE 
// ==========================================
// Handles Quantifiers (For All, Exists) using Lambdas

template<typename T>
using LogicalPredicate = std::function<bool(const T&)>;

class PredicateEngine {
public:
    // 1. FOR ALL (Universal Quantifier)
    // Returns true if P(x) is true for EVERY x in Universe
    template<typename T>
    static bool forall(const DiscreteSet<T>& universe, LogicalPredicate<T> P) {
        for (const auto& x : universe) {
            if (!P(x)) {
                return false; // Found a counter-example
            }
        }
        return true;
    }

    // 2. EXISTS (Existential Quantifier)
    // Returns true if P(x) is true for AT LEAST ONE x
    template <typename T>
    static bool exists(const DiscreteSet<T>& universe, LogicalPredicate<T> P) {
        for (const auto& x : universe) {
            if (P(x)) {
                return true; // Found a witness
            }
        }
        return false;
    }

    // 3. EXISTS UNIQUE (Uniqueness Quantifier)
    // Returns true if EXACTLY ONE element satisfies P(x)
    template <typename T>
    static bool exists_unique(const DiscreteSet<T>& universe, LogicalPredicate<T> P) {
        int count = 0;
        for (const auto& x : universe) {
            if (P(x)) {
                count++;
                if (count > 1) return false; // More than one found
            }
        }
        return count == 1;
    }

    // 4. VERIFY De Morgan's Law for Quantifiers
    // ~(Forall x, P(x)) <==> Exists x, ~P(x)
    template <typename T>
    static bool verify_not_forall_equals_exists_not(
        const DiscreteSet<T>& universe,
        LogicalPredicate<T> P
    ) {
        // LHS: Not For All
        bool lhs = !forall<T>(universe, P);

        // RHS: Exists Not (Lambda negates P(x))
        bool rhs = exists<T>(universe, [&](const T& x) { return !P(x); });

        return lhs == rhs;
    }

    // 5. VERIFY De Morgan's Law 2
    // ~(Exists x, P(x)) <==> Forall x, ~P(x)
    template <typename T>
    static bool verify_not_exists_equals_forall_not(
        const DiscreteSet<T>& universe,
        LogicalPredicate<T> P
    ) {
        // LHS: Not Exists
        bool lhs = !exists<T>(universe, P);

        // RHS: For All Not
        bool rhs = forall<T>(universe, [&](const T& x) { return !P(x); });

        return lhs == rhs;
    }
};

// ==========================================
// MODULE 2.1: NETWORK GRAPH
// ==========================================
// Hybrid Representation: 
// 1. Adjacency Matrix (for O(1) edge lookups)
// 2. Adjacency Lists (for O(degree) traversal)

class NetworkGraph {
private:
    int vertex_count;
    std::vector<std::vector<int>> matrix;
    std::vector<std::vector<std::pair<int, int>>> lists;
    bool is_directed;

    // Helper for Hamiltonian Cycle (Backtracking)
    bool isSafe(int v, int pos, std::vector<int>& path) const {
        if (!matrix[path[pos - 1]][v]) return false; // No edge
        for (int i = 0; i < pos; i++) if (path[i] == v) return false; // Already visited
        return true;
    }

    // Recursive utility to find Hamiltonian Cycle
    bool hamCycleUtil(std::vector<int>& path, int pos) const {
        // Base case: If all vertices are included in path
        if (pos == vertex_count) return matrix[path[pos - 1]][path[0]] > 0;

        for (int v = 1; v < vertex_count; v++) {
            if (isSafe(v, pos, path)) {
                path[pos] = v;
                if (hamCycleUtil(path, pos + 1)) return true;
                path[pos] = -1; // Backtrack
            }
        }
        return false;
    }

    // Depth First Search for Connectivity Check
    void dfs(int v, std::vector<bool>& visited) const {
        visited[v] = true;
        for (auto& edge : lists[v]) if (!visited[edge.first]) dfs(edge.first, visited);
    }

public:
    NetworkGraph(int n, bool directed = false) : vertex_count(n), is_directed(directed) {
        matrix.resize(n, std::vector<int>(n, 0));
        lists.resize(n);
    }

    // Updates both Matrix and List simultaneously
    void insert_edge(int from, int to, int weight) {
        if (from >= vertex_count || to >= vertex_count) return;
        matrix[from][to] = weight;
        if (!is_directed) matrix[to][from] = weight;

        lists[from].push_back({ to, weight });
        if (!is_directed) lists[to].push_back({ from, weight });
    }

    int edge_weight(int from, int to) const { return (from < vertex_count && to < vertex_count) ? matrix[from][to] : 0; }
    int get_vertex_count() const { return vertex_count; }
    const std::vector<std::vector<int>>& get_matrix() const { return matrix; }
    const std::vector<std::vector<std::pair<int, int>>>& get_lists() const { return lists; }

    // Counts connected components using DFS
    int connected_component_count() const {
        int count = 0;
        std::vector<bool> visited(vertex_count, false);
        for (int i = 0; i < vertex_count; i++) {
            if (!visited[i]) {
                dfs(i, visited);
                count++;
            }
        }
        return count;
    }

    bool is_connected() const { return connected_component_count() == 1; }

    // Euler Circuit Theorem: Connected + All vertices have EVEN degree
    bool has_euler_circuit() const {
        if (!is_connected()) return false;
        for (int i = 0; i < vertex_count; ++i) if (lists[i].size() % 2 != 0) return false;
        return true;
    }

    bool contains_hamiltonian_cycle() const {
        std::vector<int> path(vertex_count, -1);
        path[0] = 0;
        return hamCycleUtil(path, 1);
    }
};

// ==========================================
// MODULE 2.2 & 2.3: ALGORITHMS
// ==========================================

// Disjoint Set Union (DSU) structure for Kruskal's Algorithm
// Handles cycle detection efficiently
struct DSU {
    std::vector<int> parent;
    DSU(int n) {
        parent.resize(n);
        for (int i = 0; i < n; i++) parent[i] = i;
    }
    int find(int i) {
        if (parent[i] == i) return i;
        return parent[i] = find(parent[i]); // Path compression
    }
    void unite(int i, int j) {
        int root_i = find(i);
        int root_j = find(j);
        if (root_i != root_j) parent[root_i] = root_j;
    }
};

// MST: Kruskal's Algorithm (Greedy strategy using Edges)
void kruskals_mst(const NetworkGraph& network) {
    int V = network.get_vertex_count();
    auto matrix = network.get_matrix();
    std::vector<std::pair<int, std::pair<int, int>>> edges;

    // 1. Extract all edges
    for (int i = 0; i < V; i++) {
        for (int j = i + 1; j < V; j++) {
            if (matrix[i][j] != 0) edges.push_back({ matrix[i][j], {i, j} });
        }
    }
    // 2. Sort edges by weight (Ascending)
    std::sort(edges.begin(), edges.end());

    DSU dsu(V);
    int cost = 0;
    std::cout << "\n--- MST Edges (Kruskal's) ---\n";

    // 3. Iterate and add edge if it doesn't form a cycle
    for (auto& edge : edges) {
        int u = edge.second.first;
        int v = edge.second.second;
        if (dsu.find(u) != dsu.find(v)) {
            dsu.unite(u, v);
            cost += edge.first;
            std::cout << "Edge (" << u << " - " << v << ") Cost: " << edge.first << "\n";
        }
    }
    std::cout << "Total MST Cost: " << cost << "\n";
}

// Shortest Path: Dijkstra's Algorithm (Greedy strategy using Priority Queue)
void dijkstra(const NetworkGraph& network, int src, int dest) {
    int V = network.get_vertex_count();
    std::vector<int> dist(V, INT_MAX);
    std::vector<int> parent(V, -1);

    // Min-Heap priority queue: Stores {distance, vertex}
    std::priority_queue<std::pair<int, int>, std::vector<std::pair<int, int>>, std::greater<std::pair<int, int>>> pq;

    dist[src] = 0;
    pq.push({ 0, src });
    auto adj = network.get_lists();

    while (!pq.empty()) {
        int u = pq.top().second;
        int d = pq.top().first;
        pq.pop();

        if (d > dist[u]) continue; // Skip stale updates
        if (u == dest) break;      // Optimization: Stop if dest reached

        // Relaxation step
        for (auto& edge : adj[u]) {
            int v = edge.first;
            int weight = edge.second;
            if (dist[u] != INT_MAX && dist[u] + weight < dist[v]) {
                dist[v] = dist[u] + weight;
                parent[v] = u; // Track path
                pq.push({ dist[v], v });
            }
        }
    }

    if (dist[dest] == INT_MAX) {
        std::cout << "No path exists from " << src << " to " << dest << ".\n";
    }
    else {
        std::cout << "Shortest Path Cost: " << dist[dest] << "\nPath: ";
        std::vector<int> path;
        for (int v = dest; v != -1; v = parent[v]) path.push_back(v);
        for (int i = path.size() - 1; i >= 0; i--) std::cout << path[i] << (i > 0 ? " -> " : "");
        std::cout << "\n";
    }
}

// ==========================================
// MODULE 3: BINARY RELATION
// ==========================================
// Analyzes ordered pairs over a base set

class BinaryRelation {
    DiscreteSet<int> base;
    std::vector<std::pair<int, int>> pairs;
public:
    BinaryRelation(DiscreteSet<int> b) : base(b) {}
    void add_pair(int x, int y) { pairs.push_back({ x, y }); }

    bool has_pair(int x, int y) const {
        for (auto& p : pairs) if (p.first == x && p.second == y) return true;
        return false;
    }

    // 1. Reflexive: (a,a) must exist for all a in Set
    bool is_reflexive() const {
        for (auto x : base) if (!has_pair(x, x)) return false;
        return true;
    }
    // 2. Symmetric: If (a,b) exists, (b,a) must exist
    bool is_symmetric() const {
        for (auto& p : pairs) if (!has_pair(p.second, p.first)) return false;
        return true;
    }
    // 3. Transitive: If (a,b) and (b,c) exist, (a,c) must exist
    bool is_transitive() const {
        for (auto& p1 : pairs)
            for (auto& p2 : pairs)
                if (p1.second == p2.first && !has_pair(p1.first, p2.second)) return false;
        return true;
    }

    void report() {
        std::cout << "\n--- Relation Properties ---\n";
        std::cout << "Reflexive: " << (is_reflexive() ? "Yes" : "No") << "\n";
        std::cout << "Symmetric: " << (is_symmetric() ? "Yes" : "No") << "\n";
        std::cout << "Transitive: " << (is_transitive() ? "Yes" : "No") << "\n";
        // Equivalence Relation = Reflexive + Symmetric + Transitive
        std::cout << "Equivalence: " << (is_reflexive() && is_symmetric() && is_transitive() ? "Yes" : "No") << "\n";
    }
};

// ==========================================
// MENU FUNCTIONS
// ==========================================
// These functions handle user interaction and input parsing

DiscreteSet<int> get_user_set(std::string name) {
    DiscreteSet<int> s;
    int n, val;
    std::cout << "How many elements in Set " << name << "? ";
    std::cin >> n;
    std::cout << "Enter " << n << " integers: ";
    for (int i = 0; i < n; i++) {
        std::cin >> val;
        s.add(val);
    }
    return s;
}

void menu_sets() {
    std::cout << "\n--- SET OPERATIONS ---\n";
    DiscreteSet<int> A = get_user_set("A");
    DiscreteSet<int> B = get_user_set("B");

    std::cout << "\nSet A: " << A << "\nSet B: " << B << "\n";

    std::cout << "Union: " << A.set_union(B) << "\n";
    std::cout << "Intersection: " << A.set_intersection(B) << "\n";
    std::cout << "Difference (A - B): " << A.set_difference(B) << "\n";
    std::cout << "Symmetric Diff: " << A.symmetric_diff(B) << "\n";
    std::cout << "Is A subset of B? " << (A.is_subset(B) ? "Yes" : "No") << "\n";

    std::cout << "Cartesian Product (A x B): {";
    auto cart = A.cartesian_prod(B);
    for (size_t i = 0; i < cart.size(); i++) {
        std::cout << "(" << cart[i].first << "," << cart[i].second << ")";
        if (i < cart.size() - 1) std::cout << ",";
    }
    std::cout << "}\n";

    std::cout << "Powerset of A: " << A.powerset() << "\n";
}

void menu_graph() {
    int v, e, src, dest, w;
    std::cout << "\n--- GRAPH WIZARD ---\n";
    std::cout << "Enter number of vertices (0 to N-1): ";
    std::cin >> v;
    std::cout << "Is the graph directed? (1=Yes, 0=No): ";
    bool directed; std::cin >> directed;

    NetworkGraph g(v, directed);

    std::cout << "Enter number of edges: ";
    std::cin >> e;
    std::cout << "Enter edges (format: source destination weight):\n";
    for (int i = 0; i < e; i++) {
        std::cin >> src >> dest >> w;
        g.insert_edge(src, dest, w);
    }

    // Properties
    std::cout << "\n--- Graph Properties ---\n";
    std::cout << "Connected Components: " << g.connected_component_count() << "\n";
    std::cout << "Has Euler Circuit: " << (g.has_euler_circuit() ? "Yes" : "No") << "\n";
    std::cout << "Has Hamiltonian Cycle: " << (g.contains_hamiltonian_cycle() ? "Yes" : "No") << "\n";

    // Algorithms
    kruskals_mst(g);

    std::cout << "\n--- Shortest Path (Dijkstra) ---\n";
    std::cout << "Enter Start Node: "; std::cin >> src;
    std::cout << "Enter End Node: "; std::cin >> dest;
    dijkstra(g, src, dest);
}

void menu_relations() {
    std::cout << "\n--- RELATIONS ANALYZER ---\n";
    DiscreteSet<int> base = get_user_set("Base");
    BinaryRelation rel(base);

    int n, x, y;
    std::cout << "How many pairs in the relation? ";
    std::cin >> n;
    std::cout << "Enter pairs (x y):\n";
    for (int i = 0; i < n; i++) {
        std::cin >> x >> y;
        rel.add_pair(x, y);
    }
    rel.report();
}

// -----------------------------------------------------
// UPDATED MENU MODULE 4: PREDICATES & LOGIC
// -----------------------------------------------------
void menu_predicates() {
    std::cout << "\n--- PREDICATE LOGIC & QUANTIFIERS ---\n";

    // 1. Get Universe
    DiscreteSet<int> U = get_user_set("Universe (U)");

    // 2. Select Predicate P(x)
    std::cout << "\nStep 2: Define your Predicate P(x)\n";
    std::cout << "1. P(x): x is Even\n";
    std::cout << "2. P(x): x is Odd\n";
    std::cout << "3. P(x): x > 10\n";
    std::cout << "4. P(x): x is Prime (Basic check)\n";
    std::cout << "Select Predicate (1-4): ";
    int p_choice; std::cin >> p_choice;

    // Lambda setup based on user choice
    std::function<bool(const int&)> P;

    switch (p_choice) {
    case 1: P = [](const int& x) { return x % 2 == 0; }; break;
    case 2: P = [](const int& x) { return x % 2 != 0; }; break;
    case 3: P = [](const int& x) { return x > 10; }; break;
    case 4: P = [](const int& x) { // Basic prime check
        if (x <= 1) return false;
        for (int i = 2; i * i <= x; ++i) if (x % i == 0) return false;
        return true;
        }; break;
    default:
        std::cout << "Invalid choice, defaulting to Even.\n";
        P = [](const int& x) { return x % 2 == 0; };
    }

    // 3. Select Operation
    std::cout << "\nStep 3: Choose Quantification or Verification\n";
    std::cout << "1. Check For All (Forall x, P(x))\n";
    std::cout << "2. Check Exists (Exists x, P(x))\n";
    std::cout << "3. Check Exists Unique (Exists! x, P(x))\n";
    std::cout << "4. Verify: ~(Forall) <==> Exists(~)\n";
    std::cout << "5. Verify: ~(Exists) <==> Forall(~)\n";
    std::cout << "Choice: ";
    int op_choice; std::cin >> op_choice;

    std::cout << "\n--- RESULT ---\n";
    if (op_choice == 1) {
        bool res = PredicateEngine::forall(U, P);
        std::cout << "Statement (Forall x, P(x)) is: " << (res ? "TRUE" : "FALSE") << "\n";
    }
    else if (op_choice == 2) {
        bool res = PredicateEngine::exists(U, P);
        std::cout << "Statement (Exists x, P(x)) is: " << (res ? "TRUE" : "FALSE") << "\n";
    }
    else if (op_choice == 3) {
        bool res = PredicateEngine::exists_unique(U, P);
        std::cout << "Statement (Exists! x, P(x)) is: " << (res ? "TRUE" : "FALSE") << "\n";
        if (res) std::cout << "(Only ONE element satisfies P(x))\n";
    }
    else if (op_choice == 4) {
        std::cout << "Verifying De Morgan's Law 1...\n";
        bool valid = PredicateEngine::verify_not_forall_equals_exists_not(U, P);
        std::cout << "Verification: " << (valid ? "SUCCESS (Laws Hold)" : "FAILED (Logic Broken??)") << "\n";
    }
    else if (op_choice == 5) {
        std::cout << "Verifying De Morgan's Law 2...\n";
        bool valid = PredicateEngine::verify_not_exists_equals_forall_not(U, P);
        std::cout << "Verification: " << (valid ? "SUCCESS (Laws Hold)" : "FAILED (Logic Broken??)") << "\n";
    }
    else {
        std::cout << "Invalid operation.\n";
    }
}

// ==========================================
// MAIN MENU LOOP
// ==========================================

int main() {
    int choice;
    do {


        std::cout << "\n============================================\n";
        std::cout << "   Computational Discrete Analysis Framework \n";
        std::cout << "==============================================\n";
        std::cout << "1. Set Operations (Union, Inter, Cartesian...)\n";
        std::cout << "2. Graph Theory (Euler, Hamilton, MST, SP)\n";
        std::cout << "3. Binary Relations (Reflexive, Transitive...)\n";
        std::cout << "4. Logic & Quantifiers\n";
        std::cout << "0. Exit\n";
        std::cout << "Enter choice: ";
        std::cin >> choice;

        switch (choice) {
        case 1: menu_sets(); break;
        case 2: menu_graph(); break;
        case 3: menu_relations(); break;
        case 4: menu_predicates(); break;
        case 0: std::cout << "peace out!\n"; break;
        default: std::cout << "Invalid choice, try again.\n";
        }
    } while (choice != 0);

    return 0;
}
