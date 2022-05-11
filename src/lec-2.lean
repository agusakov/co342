/-
Copyright (c) 2022 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.connectivity
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
A graph G is k-edge-connected if G−F is connected for every F⊆E(G) where |F|< k.
-/
def is_k_edge_connected (k : ℕ) : Prop := ∀ (F : finset (sym2 V)), F ⊆ G.edge_finset → F.card < k → 
  connected (G.delete_edges F)

/--
A graph G that is k-edge-connected where 0 < k is connected.
-/
lemma k_edge_connected_is_connected (k : ℕ) (h : 0 < k) (h2 : G.is_k_edge_connected k) : G.connected :=
begin
  unfold is_k_edge_connected at h2,
  specialize h2 ∅,
  simp at h2,
  specialize h2 h,
  exact h2,
end

lemma min_deg_ne_zero_of_connected (h : G.connected) (h2 : 1 < fintype.card V): G.min_degree ≠ 0 :=
begin
  -- again we have the weird situation where a single vertex is the exception
  -- some kind of nonempty E declaration perhaps?
  have hv := G.exists_minimal_degree_vertex,
  cases hv with v hv,
  rw fintype.one_lt_card_iff at h2,
  rcases h2 with ⟨a, ⟨b, hb⟩⟩,
  
  sorry,
end

-- exists_eq_cons_of_ne?
lemma delete_incident_edges_disconnected (u v : V) (h : u ≠ v) : ¬ (G.delete_edges (G.incidence_finset u)).reachable u v :=
begin
  unfold reachable,
  simp only [not_nonempty_iff],
  fconstructor,
  intros p,
  have w := p.get_vert 1,
  have h2 := walk.adj_get_vert_succ p,
  have h3 : 0 < p.length,
  by_contra h4,
  push_neg at h4,
  simp at h4,
  have h5 := walk.eq_of_length_eq_zero h4,
  apply h,
  exact h5,
  specialize h2 h3,
  rw walk.get_vert_zero at h2,
  rw delete_edges_adj at h2,
  cases h2 with h5 h6,
  apply h6,
  simp at *,
  exact h5,
end

lemma delete_incident_edges_not_preconnected (u : V) (h : 0 < G.degree u) : ¬ (G.delete_edges (G.incidence_finset u)).preconnected :=
begin
  unfold preconnected,
  push_neg,
  use u,
  have h3 := G.degree_pos_iff_exists_adj u,
  cases h3 with h3 h5,
  specialize h3 h,
  cases h3 with w hw,
  use w,
  apply delete_incident_edges_disconnected,
  apply G.ne_of_adj hw,
end

lemma edge_conn_le_min_deg (k : ℕ) (h2 : G.is_k_edge_connected k) : k ≤ G.min_degree := 
begin
  have hv := G.exists_minimal_degree_vertex,
  cases hv with v hv,
  have h : ¬ connected (G.delete_edges (G.incidence_finset v)),
  -- v has no neighbors when you delete its incidence set
  cases (G.min_degree),
  { 
    by_contra h3,
    sorry },
  { -- unfold degree at hv,
    have h3 := G.degree_pos_iff_exists_adj v,
    cases h3 with h3 h5,
    specialize h3 sorry,
    cases h3 with w hw,
    
    sorry },
  specialize h2 (G.incidence_finset v),
  specialize h2 sorry,
  contrapose h2,
  push_neg at h2,
  push_neg,
  rw ← G.card_incidence_finset_eq_degree at hv,
  rw hv at h2,
  exact ⟨h2, h⟩,
end



end simple_graph