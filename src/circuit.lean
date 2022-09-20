import vorspiel

-- circuit : fun-in → fun-out → Type
inductive circuit : ℕ → ℕ → Type
| and {n} : fin n → fin n → circuit n 1 -- AND conjunction
| or  {n} : fin n → fin n → circuit n 1 -- OR disjunction
| not {n} : fin n → circuit n 1 -- NOT disjunction
| id  {n} : fin n → circuit n 1 -- id gate
| add {n m k} : circuit n m → circuit n k → circuit n (m + k)
| comp {n m k} : circuit n m → circuit m k → circuit n k

abbreviation circuit₁ (n) := circuit n 1

namespace circuit

@[simp] def size : ∀ {n m}, circuit n m → ℕ
| _ _ (and i j)    := 1
| _ _ (or i j)     := 1
| _ _ (not i)      := 1
| _ _ (id i)       := 0
| _ _ (add c₁ c₂)  := c₁.size + c₂.size
| _ _ (comp c₁ c₂) := c₁.size + c₂.size

@[simp] def depth : ∀  {n m}, circuit n m → ℕ
| _ _ (and i j)    := 1
| _ _ (or i j)     := 1
| _ _ (not i)      := 1
| _ _ (id i)       := 1
| _ _ (add c₁ c₂)  := max c₁.depth c₂.depth
| _ _ (comp c₁ c₂) := c₁.depth + c₂.depth

@[simp] def val : Π {n m}, circuit n m → vector bool n → vector bool m
| n _ (and i j)    v := ⟨[band (v.nth i) (v.nth j)], by simp⟩
| n _ (or i j)     v := ⟨[bor (v.nth i) (v.nth j)], by simp⟩
| n _ (not i)      v := ⟨[bnot (v.nth i)], by simp⟩
| n _ (id i)       v := ⟨[v.nth i], by simp⟩
| n _ (add c₁ c₂)  v := (c₁.val v).append (c₂.val v)
| n _ (comp c₁ c₂) v := c₂.val (c₁.val v)

end circuit