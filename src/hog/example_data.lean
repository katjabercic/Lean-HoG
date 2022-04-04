import .tactic
import .graph
import .path
import .connected_component
import .tree_representation
import .tree_set

namespace hog

open tree_set

def example_1: stree Edge (by { trivial } : bounded.bottom < bounded.top) :=
  stree.node { edge := (0,2) }
    (stree.leaf { edge := (0,1) } true.intro (by bool_reflect))
    (stree.leaf { edge := (1,2) } (by bool_reflect) true.intro)


def example_2 : tset Edge := example_1
#eval example_2.size
#eval stree.size (tset.add {Edge . edge := (1,3)} example_2)
#eval (tset.add {Edge . edge := (1,3)} example_2).elem { Edge . edge := (1,3)}

def g : simple_irreflexive_graph := 
{ vertex_size := 3,
  edges := example_2,
  edge_size := 3,
  edge_size_correct := by refl 
}

def cc : ℕ → fin 1 := λ (v : ℕ), 
  match v with
  | 0 := 0
  | 1 := 0
  | 2 := 0
  | _ := 0
  end


def gccw : num_components_witness := { 
  G := g,
  num_components := 1,
  c := cc,
  h := λ v, 
    match v with
    | 0 := 0
    | 1 := 1
    | 2 := 2
    | _ := 0
    end,
  connect_edges := 
    begin 
      let p : Edge → Prop := λ e, cc e.edge.fst = cc e.edge.snd,
      have dp : decidable_pred p := begin apply_instance end,
      intros e h,
      apply iff.mp,
      apply to_bool_iff,
      sorry -- we tried
    end,
  root := _,
  is_root := _,
  uniqueness_of_roots := _,
  next := _,
  height_cond := _ }

end hog

