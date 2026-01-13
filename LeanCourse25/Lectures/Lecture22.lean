import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Data.List.Basic

open Function NNReal
set_option linter.unusedVariables false







/-
# Announcement

Next week, there is an online conference, *Lean Together*.
If you want to learn about the new things going
on in the Lean community, you can attend some of the talks:
https://leanprover-community.github.io/lt2026/schedule.html

# Last time

Clean code and formalisation best practices

- Code style: a coherent style increases readability
- Linters: automatic checkers for style and other issues
  - syntax linters run as you type
  - environment linters run when you write `#lint`
    (at the bottom of your file)
- Golfing: making proofs shorter
  (which can make proofs more readable, but not if you overdo it)
- Profiling to identify slow parts of your proof

# Today: graph theory in Lean
-/


/-!
**What is a graph?**

A graph has a collection of vertices and
a set of edges between these vertices.

There are many variations on graphs.
Questions:
1. Are the edges directed?
2. Can there be multiple edges between two vertices?
3. Can there be loops?



Mathlib has multiple notions of graphs:
* A `Quiver` is a directed multigraph
  (answers "yes" to all questions)
* A `Digraph` is a directed graph
  ("no" to question 2, "yes" to 1 and 3)
* A `SimpleGraph` answers "no" to all questions.

How do we define these notions?
-/

structure MyQuiver (V : Type*) where
  Hom : V → V → Sort*

#check MyQuiver
#check MyQuiver.Hom

structure MyDigraph (V : Type*) where
  Adj : V → V → Prop

#check SimpleGraph

example : SimpleGraph ℕ where
  Adj u v := u ≠ v
  -- `aesop_graph` was able to automatically prove symmetry and irreflexivity



/-
Note that `SimpleGraph` is a structure, not a class.
This makes it easier to talk about
multiple simple graphs on the same type.
-/


namespace SimpleGraph
variable {α V : Type*} (G : SimpleGraph V)
/-!
Let's focus on simple graphs.

Set-theoretically, undirected graphs are most easily defined
using unordered pairs `{x, y}` as edges.

In Lean, we can define unordered pairs in `α`
as a quotient of `α × α`.
-/

inductive UnorderedPair.Rel (α : Type*) : α × α → α × α → Prop
  | refl (x y : α) : Rel α (x, y) (x, y)
  | swap (x y : α) : Rel α (x, y) (y, x)

def UnorderedPair.setoid (α : Type*) : Setoid (α × α) :=
  ⟨UnorderedPair.Rel α, sorry⟩

def UnorderedPair (α : Type*) := Quotient (UnorderedPair.setoid α)

/-! The following definition is equivalent,
and is called `Sym2` in Mathlib -/
def UnorderedPair' (α : Type*) := Quot (UnorderedPair.Rel α)

/-! The notation for an unordered pair is `s(x, y)`
(instead of `{x, y}`). -/
example (x y : α) : Sym2 α := s(x, y)

example {x y : α} : s(x, y) = s(y, x) :=
  Sym2.eq_swap

example {x y u v : α} : s(x, y) = s(u, v) ↔
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) :=
  Sym2.eq_iff


/-! A `SimpleGraph` can equivalently be defined as
a collection of unordered pairs without singletons
`s(x, x)`. -/
example (S : Set (Sym2 V)) : SimpleGraph V :=
  fromEdgeSet S

example (G : SimpleGraph V) : Set (Sym2 V) :=
  edgeSet G

/-- A *dart* or *oriented edge* is
a pair of adjacent vertices in the graph `G`. -/
structure MyDart (G : SimpleGraph V) extends V × V where
  adj : G.Adj fst snd

/-- A *walk* (sometimes also called *path*)
is a sequence of adjacent vertices. -/
inductive MyWalk (G : SimpleGraph V) : V → V → Type _
  | nil {u : V} : MyWalk G u u
  | cons {u v w : V} (h : G.Adj u v) (p : MyWalk G v w) : MyWalk G u w


/-! Given a walk, we can define the vertices,
darts and edges it visits in order, as a list. -/
def MyWalk.support {u v : V} : G.MyWalk u v → List V
  | nil (u := u) => [u]
  | cons _ p => u :: p.support

def MyWalk.darts {u v : V} : G.MyWalk u v → List G.Dart
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts

def edges {u v : V} (p : G.MyWalk u v) : List (Sym2 V) := p.darts.map Dart.edge

/-- A walk is a *path* if no vertex is visited twice. -/
structure MyWalk.IsPath {u v : V} (p : G.MyWalk u v) : Prop where
  support_nodup : p.support.Nodup

/-- A walk is a *cycle* if it ends at the starting point, and if we
  remove the last edge from the walk, we get a path. -/
structure MyWalk.IsCycle {u : V} (p : G.MyWalk u u) : Prop where
  ne_nil : p ≠ nil
  support_nodup : p.support.tail.Nodup


/-- Subgraphs might want to restrict both
the vertex set and the edge set.
-/
structure MySubgraph (G : SimpleGraph V) where
  /-- Vertices of the subgraph -/
  verts : Set V
  /-- Edges of the subgraph -/
  Adj : V → V → Prop
  adj_sub : ∀ {v w : V}, Adj v w → G.Adj v w
  edge_vert : ∀ {v w : V}, Adj v w → v ∈ verts
  symm : Symmetric Adj

end SimpleGraph

/-
# Algorithms on graphs

As an example, we will discuss Dijkstra's algorithm.
It takes a graph where every vertex `(u, v)` has a weight `w(u, v)`
and a starting vertex,
and computes the shortest path from the starting vertex
to any other vertex.

We do this by keeping track of a computed distance `d(v)` for each edge `v`.
Initially, the computed distance is 0 for the starting vertex and `∞`
for all others.
At each step:
- we visit an unvisited vertex `u` with minimal computed distance
- we iterate over all `u`'s neighbors `v`
- we set `d(v)` to the minimum of `d(v)` and `d(u) + w(u, v)`
-/

structure WeightedGraph (V : Type*) extends SimpleGraph V where
  weight : V × V → ℚ≥0
  weight_symm (v w : V) : weight (v, w) = weight (w, v)

variable
  {V : Type} [Fintype V] [Encodable V] [DecidableEq V]
  {G : WeightedGraph V} {u v : V} [DecidableRel G.Adj]

/-- The length of a walk is the sum of the length of its edges. -/
def pathLength (p : G.Walk u v) : ℚ≥0 :=
  List.sum (p.darts.map (fun d ↦ G.weight d.toProd))

namespace Dijkstra
open Encodable

structure State (G : WeightedGraph V) where
  /-- starting node -/
  start : V
  /-- computed distance to the starting node -/
  dist : V → WithTop ℚ≥0
  /-- unvisited edges -/
  unvisited : List V
deriving Inhabited

def State.initial (start : V) : State G where
  start := start
  dist v := if v = start then 0 else ⊤
  unvisited := Encodable.sortedUniv V

def dijkstraStep (S : State G) : Option (State G) := do
  -- We find the unvisted vertex with the minimal distance
  -- (and halt if there is no unvisited vertex)
  let some (v : V) := S.unvisited.argmin S.dist | failure
  if S.dist v = ⊤ then
    failure
  let newDist (w : V) : WithTop ℚ≥0 :=
    if G.Adj v w then min (S.dist w) (S.dist v + G.weight (v, w)) else S.dist w
  let newState : State G := {
    start := S.start
    dist := newDist
    unvisited := S.unvisited.filter (· ≠ v)
  }
  return newState


/- Now we iterate this |V| many steps. -/
variable (G) in
def dijkstra (start : V) : State G := Id.run do
  let mut S : State G := State.initial start
  for _ in List.range (Fintype.card V) do
    match dijkstraStep S with
    | none    => break
    | some S' => S := S'
  return S


/- Let's try this on an example graph, where the graph is just a chain. -/

abbrev finNGraph (n : ℕ) : WeightedGraph (Fin n) where
  Adj u v := |(u : ℤ) - (v : ℤ)| = 1
  symm := sorry
  loopless := sorry
  weight := fun (u, v) ↦ ⟨(1 : ℚ) / max u v, sorry⟩
  weight_symm := sorry

#eval! ((dijkstra (finNGraph 5) 0).dist 4).get!


/- We could now prove correctness of this algorithm. -/
lemma dijkstra_correct (start v : V) :
    IsGLB (Set.range (fun p ↦ pathLength p : G.Walk start v → WithTop ℚ≥0))
      ((dijkstra G start).dist v) := by
  sorry

end Dijkstra
