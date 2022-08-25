import tactic data.vector data.vector.zip 

universes u v

def vorspiel : ℕ := 9

namespace vector
variables {α : Type u} {n : ℕ}

def concat : vector α n → α → vector α n.succ
| ⟨l, h⟩ a := ⟨l.concat a, by simp[h]⟩



end vector

#check vector.concat
