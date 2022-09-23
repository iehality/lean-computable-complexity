import vorspiel boolean_logic

universes u v

-- gate : 自由変数 → ゲートの数 → Type
inductive gate : ℕ → ℕ → Type
| atom {n m} : fin n → gate n m
| ctn {n m}  : fin m → gate n m -- continue
| not {n m}  : fin m → gate n m -- NOT gate
| and {n m}  : finset (fin m) → gate n m -- AND conjunction
| or  {n m}  : finset (fin m) → gate n m -- OR disjunction

namespace gate

@[simp] def shift : Π {n m} (k), gate n m → gate k (n + m)
| _ _ _ (atom i) := ctn ⟨i, nat.lt_add_right _ _ _ i.property⟩
| n _ _ (ctn j)  := ctn ⟨n + j, by simpa using j.property⟩
| n _ _ (not j)  := not ⟨n + j, by by simpa using j.property⟩
| n m _ (and s)  := and (s.image (λ i, ⟨n + i, by simpa using i.property⟩))
| n m _ (or s)   := or (s.image (λ i, ⟨n + i, by simpa using i.property⟩))

@[simp] def val : Π {n m}, gate n m → vector bool n → vector bool m → bool
| _ _ (atom i) v _ := v.nth i
| _ _ (ctn j)  _ w := w.nth j
| _ _ (not j)  _ w := bnot (w.nth j)
| _ _ (and s)  _ w := s.inf w.nth
| _ _ (or s)   _ w := s.sup w.nth

inductive bounded (b : ℕ) : ∀ {n m}, gate n m → Prop
| atom : ∀ {n m : ℕ} (i : fin n), bounded (@atom n m i)
| ctn  : ∀ {n m : ℕ} (j : fin m), bounded (@ctn n m j)
| not  : ∀ {n m : ℕ} (j : fin m), bounded (@ctn n m j)
| and  : ∀ {n m : ℕ} (s : finset (fin m)) (h : s.card ≤ b), bounded (@and n m s)
| or   : ∀ {n m : ℕ} (s : finset (fin m)) (h : s.card ≤ b), bounded (@or n m s)

@[simp] def map_fun_in : Π {n n' m : ℕ} (f : fin n → fin n'), gate n m → gate n' m
| _ _ _ f (atom i) := atom (f i)
| _ _ _ f (ctn j)  := ctn j
| _ _ _ f (not j)  := not j
| _ _ _ f (and s)  := and s
| _ _ _ f (or s)   := or s

end gate

-- circuit : fun-in → gateの数 → Type
inductive circuit : ℕ → ℕ → Type u
| nil (n) : circuit n 0
| cons {n m} : gate n m → circuit n m → circuit n m.succ

namespace circuit
open gate
variables {G : ℕ → Type u}

inductive bounded (b : ℕ) : Π {n m}, circuit n m → Prop
| nil  : ∀ n, bounded (nil n)
| atom : ∀ {n m} {c : circuit n m} {g : gate n m}, g.bounded b → bounded (cons g c)

def eval : Π {n m}, circuit n m → vector bool n → vector bool m
| _ _ (nil n)     _ := vector.nil
| _ _ (cons g c)  v := g.val v (c.eval v) ::ᵥ c.eval v

@[simp] def val {n m : ℕ} (c : circuit n m.succ) (v : vector bool n) : bool := (c.eval v).head

def depth_vec : Π {n m}, circuit n m → vector ℕ m
| _ _ (nil n)           := vector.nil
| _ _ (cons (atom i) c) := 0 ::ᵥ depth_vec c
| _ _ (cons (ctn i) c)  := let ih := depth_vec c in (ih.nth i).succ ::ᵥ ih
| _ _ (cons (not i) c)  := let ih := depth_vec c in (ih.nth i).succ ::ᵥ ih
| _ _ (cons (and s) c)  := let ih := depth_vec c in (s.sup ih.nth).succ ::ᵥ ih
| _ _ (cons (or s) c)   := let ih := depth_vec c in (s.sup ih.nth).succ ::ᵥ ih

def depth {n m} (c : circuit n m) : ℕ := (depth_vec c).val.sup

def comp : Π {n m k}, circuit n m → circuit m k → circuit n (m + k)
| _ _ _ c  (nil n)     := c
| n _ _ c₁ (cons g c₂) := cons (g.shift n) (c₁.comp c₂)

def bounded_And : Π n, circuit n (2*n)
| 0 := nil 0
| (n + 1) := 

end circuit

structure SIZE (T : ℕ → ℕ) (f : 𝔹 → bool)
(circuit_family : Π n, circuit₁ n)
(bounded : ∀ n, (circuit_family n).size ≤ T n)
(ch : ∀ n v, (circuit_family n).val v = vector.singleton (f v.val))


namespace CNF
variables {m n : ℕ}
def to_circuit : CNF m n → circuit₁ n := by {  }
end CNF