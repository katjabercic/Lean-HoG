import .tactic
import .graph
import .planar
import .perm_cycles
namespace hog
open hypermap
open euler_characteristic
def cycle3 : simple_irreflexive_graph :=
  { simple_irreflexive_graph .
    vertex_size := 3,
    edge :=
      (λ (i : fin 3) (j : fin 3),
        (match i.val, j.val with
        | 0, 1 := tt | 1, 0 := tt
        | 1, 2 := tt | 2, 1 := tt
        | 2, 0 := tt | 0, 2 := tt
        | _, _ := ff -- catch all case for false
        end : bool))     
  }
def edge := 
      (λ (i : fin 6), 
        (match i.val with
        | 0 := 1 | 1 := 0
        | 2 := 3 | 3 := 2
        | 4 := 5 | 5 := 4
        | _ := 0
        end : (fin 6)))
def node := 
      (λ (i : fin 6), 
      (match i.val with 
      | 0 := 5 | 5 := 0
      | 1 := 2 | 2 := 1
      | 3 := 4 | 4 := 3
      | _ := 0
      end : (fin 6)))
def face :=
      (λ (i : fin 6), 
        (match i.val with
        | 0 := 2 | 1 := 5
        | 2 := 4 | 3 := 1
        | 4 := 0 | 5 := 3
        | _ := 0
        end : (fin 6)))

def hypermap_of_cycle3 : hypermap := 
  { hypermap.
    dart_size := 6,
    edge := 
      (λ (i : fin 6), 
        (match i.val with
        | 0 := 1 | 1 := 0
        | 2 := 3 | 3 := 2
        | 4 := 5 | 5 := 4
        | _ := 0
        end : (fin 6))),
    node := 
      (λ (i : fin 6), 
      (match i.val with 
      | 0 := 5 | 5 := 0
      | 1 := 2 | 2 := 1
      | 3 := 4 | 4 := 3
      | _ := 0
      end : (fin 6))),
    face :=
      (λ (i : fin 6), 
        (match i.val with
        | 0 := 2 | 1 := 5
        | 2 := 4 | 3 := 1
        | 4 := 0 | 5 := 3
        | _ := 0
        end : (fin 6))),
}
def cycle3_euler : euler_char hypermap_of_cycle3 2 := {}

instance: hog_edge_size cycle3 := ⟨ 3, rfl ⟩

instance: hog_max_degree cycle3 := ⟨ 2, rfl ⟩

instance: hog_min_degree cycle3 := ⟨ 2, rfl ⟩

instance: hog_regular cycle3 := ⟨ rfl ⟩


end hog

