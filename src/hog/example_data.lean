import .tactic
import .graph
import .path
import .component
import .tree_representation
import .tree_set
import .tactic

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

def example_graph : simple_irreflexive_graph := 
{ vertex_size := 3,
  edge := example_2,
  edge_size := 3,
  edge_size_correct := by refl 
}

end hog

