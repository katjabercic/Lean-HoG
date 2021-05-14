import .hog

namespace hog

def database := [
  { hog .
    chromatic_number := 2,
    genus := 0,
    girth := 0,
    graph6 := "DgC",
    is_eulerian := ff,
    is_hamiltonian := ff,
    maximum_degree := 2,
    minimum_degree := 1,
    number_of_vertices := 5
  },
  { hog . chromatic_number := 0,
    genus := 0,
    girth := 0,
    graph6 := "?",
    is_eulerian := tt,
    is_hamiltonian := tt,
    maximum_degree := 0,
    minimum_degree := 0,
    number_of_vertices := 0
  }
]

end hog
