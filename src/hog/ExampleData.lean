import Graph
import EdgeSize

namespace ExampleData

def piglet1 : Graph :=
  { vertexSize := 3,
    edgeTree := .node Edge[2,0] (.leaf Edge[1,0]) (.leaf Edge[2,1]) }

instance : EdgeSize piglet1 where val := 3

example : piglet1.edgeSize + 2 = 5 := by
  simp [piglet1.edgeSize_is] 


end ExampleData