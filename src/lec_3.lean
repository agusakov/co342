/-
Copyright (c) 2022 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.connectivity
import .lec_2
import data.list
/-!

# Graph Vertex and Edge Connectivity

In a simple graph, blah blah

-/

universes u v

namespace simple_graph
variables {V : Type u} {V' : Type v} [decidable_eq V] [fintype V] [nonempty V]
variables (G : simple_graph V) (G' : simple_graph V') [decidable_rel G.adj]

/--
For a setS⊆V(G), thecut induced byS(or justa cut) is the set of all edges with one end inSand one end not inS, denoted bycutG(S)orcut(S).  A cut isnontrivialifS̸=∅andS̸=V(G).
-/


end simple_graph
