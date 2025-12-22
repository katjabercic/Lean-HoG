import LeanHoG.Graph
import LeanHoG.Graph

namespace LeanHoG

class G6 (G : Graph) : Type :=
  val : String

def Graph.g6 {G : Graph} [g6 : G6 G] : String := g6.val

end LeanHoG

