# Computational Discrete Analysis Framework (CDAF) 

> A high-performance C++ toolset for solving and visualizing complex Discrete Structures problems.

##  What is this?
CDAF is a CLI-based engine designed to automate the heavy lifting in Discrete Mathematics. Instead of manually calculating Power Sets or tracing Dijkstra's algorithm by hand, this framework provides a menu-driven interface to handle Set Theory, Graph Algorithms, Binary Relations, and Predicate Logic verification instantly.

It acts as a "computational companion" for CS students dealing with discrete structures.

##  Features

### 1. Advanced Set Operations
Custom `DiscreteSet` class implemented with generic templates.
* **Basic Ops:** Union, Intersection, Difference, Symmetric Difference.
* **Complex Ops:** Generates **Power Sets** (using bitwise logic) and **Cartesian Products**.
* **Checks:** Subset verification and membership testing ($O(\log n)$ via binary search).

### 2. Graph Theory Wizard
A hybrid network graph implementation (Adjacency Matrix + Adjacency Lists).
* **Algorithms:** * **Kruskal’s MST:** Minimum Spanning Tree using Disjoint Set Union (DSU).
    * **Dijkstra’s:** Shortest Path algorithm using Priority Queues.
* **Analysis:** Detects Euler Circuits, Hamiltonian Cycles (Backtracking), and Connected Components (DFS).

### 3. Logic & Quantifiers Engine
A modern C++ implementation of predicate logic.
* **Quantifiers:** Validates `For All` ($\forall$) and `Exists` ($\exists$) over a universe.
* **De Morgan's Laws:** Verifies logical equivalences programmatically.
* **Tech:** Uses **C++ Lambdas** (`std::function`) to pass predicates dynamically.

### 4. Binary Relation Analyzer
* Analyzes ordered pairs to determine properties:
    * **Reflexive**
    * **Symmetric**
    * **Transitive**
    * **Equivalence Relation** check.

---

##  Installation & Usage

### Prerequisites
* A C++ compiler (GCC/G++, Clang, or MSVC)
* Standard Template Library (STL) support

### Compile and Run
You can compile this using `g++` in your terminal:

```bash
# Compile
g++ main.cpp -o cdaf

# Run
./cdaf
