import vorspiel boolean_logic

universes u v

-- gate : 自由変数 → ゲートの数 → Type
inductive gate : ℕ → Type
| ctn {m}  : fin m → gate m -- continue
| not {m}  : fin m → gate m -- NOT gate
| and {m}  : finset (fin m) → gate m -- AND conjunction
| or  {m}  : finset (fin m) → gate m -- OR disjunction

namespace gate

@[simp] def map : Π {m m' : ℕ} (f : fin m → fin m'), gate m → gate m'
| _ _ f (ctn j)  := ctn (f j)
| _ _ f (not j)  := not (f j)
| _ _ f (and s)  := and (s.image f)
| _ _ f (or s)   := or (s.image f)

def shift {m m' : ℕ} (h : m ≤ m') (g : gate m) : gate m' := g.map (λ i, ⟨i, lt_of_lt_of_le i.property h⟩)

@[simp] def val : Π {m}, gate m → vector bool m → bool
| _ (ctn j)  w := w.nth j
| _ (not j)  w := bnot (w.nth j)
| _ (and s)  w := s.inf w.nth
| _ (or s)   w := s.sup w.nth

inductive bounded (b : ℕ) : ∀ {m}, gate m → Prop
| ctn  : ∀ {m : ℕ} (j : fin m), bounded (@ctn m j)
| not  : ∀ {m : ℕ} (j : fin m), bounded (@not m j)
| and  : ∀ {m : ℕ} {s : finset (fin m)} (h : s.card ≤ b), bounded (@and m s)
| or   : ∀ {m : ℕ} {s : finset (fin m)} (h : s.card ≤ b), bounded (@or m s)

attribute [simp] bounded.ctn bounded.not

def and₂ {m} (i j : fin m) : gate m := and {i, j}

infix ` ∧ᵍ `:80 := and₂

def or₂ {m} (i j : fin m) : gate m := or {i, j}

infix ` ∨ᵍ `:80 := or₂

lemma and₂_bounded {m} (i j : fin m) : (and₂ i j).bounded 2 :=
bounded.and (by simpa using finset.card_insert_le i {j})

lemma or₂_bounded {m} (i j : fin m) : (or₂ i j).bounded 2 :=
bounded.or (by simpa using finset.card_insert_le i {j})

end gate

-- circuit : fun-in → gateの数 → Type
inductive circuit : ℕ → ℕ → Type u
| nil (n) : circuit n 0
| atom {n m} : fin n → circuit n m → circuit n m.succ
| cons {n m} : gate m → circuit n m → circuit n m.succ

structure Circuit (n : ℕ) :=
(size : ℕ)
(val : circuit n size)

namespace circuit
open gate

inductive bounded (b : ℕ) : Π {n m}, circuit n m → Prop
| nil  : ∀ n, bounded (nil n)
| atom : ∀ {n m} {c : circuit n m} {i}, bounded c → bounded (atom i c)
| cons : ∀ {n m} {c : circuit n m} {g : gate m}, g.bounded b → bounded c → bounded (cons g c)

def eval : Π {n m}, circuit n m → vector bool n → vector bool m
| _ _ (nil n)     _ := vector.nil
| _ _ (atom i c)  v := v.nth i ::ᵥ c.eval v
| _ _ (cons g c)  v := g.val (c.eval v) ::ᵥ c.eval v

@[simp] def val {n m : ℕ} (c : circuit n m.succ) (v : vector bool n) : bool := (c.eval v).head

def depth_vec : Π {n m}, circuit n m → vector ℕ m
| _ _ (nil n)           := vector.nil
| _ _ (atom i c) := 0 ::ᵥ depth_vec c
| _ _ (cons (ctn i) c)  := let ih := depth_vec c in (ih.nth i).succ ::ᵥ ih
| _ _ (cons (not i) c)  := let ih := depth_vec c in (ih.nth i).succ ::ᵥ ih
| _ _ (cons (and s) c)  := let ih := depth_vec c in (s.sup ih.nth).succ ::ᵥ ih
| _ _ (cons (or s) c)   := let ih := depth_vec c in (s.sup ih.nth).succ ::ᵥ ih

def depth {n m} (c : circuit n m) : ℕ := (depth_vec c).val.sup

def comp : Π {n m k}, circuit n m → circuit m k → circuit n (m + k)
| _ _ _ c  (nil n)     := c
| n _ _ c₁ (atom i c₂) := cons (ctn ⟨i, nat.lt_add_right _ _ _ i.property⟩) (c₁.comp c₂)
| n _ _ c₁ (cons g c₂) := cons (g.shift (by simp)) (c₁.comp c₂)

lemma comp_depth : ∀ {n m k} (c₁ : circuit n m) (c₂ : circuit m k), (c₁.comp c₂).depth ≤ c₁.depth + c₂.depth
| _ _ _ c₁ (nil n) := by simp[comp]
| _ _ _ c₁ (atom i c₂) := by { simp[comp], sorry }

def map_fun_in : Π {n n' m} (f : fin n → fin n'), circuit n m → circuit n' m
| _ _ _ f (nil n) := nil _
| _ _ _ f (atom i c) := atom (f i) (map_fun_in f c)
| _ _ _ f (cons g c) := cons g (c.map_fun_in f)

def shift {n n' m : ℕ} (h : n ≤ n') (c : circuit n m) : circuit n' m := c.map_fun_in (λ i, ⟨i, lt_of_lt_of_le i.property h⟩)

end circuit

namespace Circuit

abbreviation depth {n} (c : Circuit n) := c.2.depth

def nil (n : ℕ) : Circuit n := ⟨0, circuit.nil n⟩

def atom {n} (c : Circuit n) (i : fin n) : Circuit n := ⟨c.size.succ, circuit.atom i c.val⟩

def cons {n} (c : Circuit n) (g : gate c.size) : Circuit n := ⟨c.size.succ, c.val.cons g⟩

def bounded_And : Π n, Circuit n
| 0 := ⟨0, nil 0⟩
| (n + 1) := cons (by { }) ((bounded_And n).shift (by {  }))

end Circuit

structure SIZE (T : ℕ → ℕ) (f : 𝔹 → bool)
(circuit_family : Π n, circuit₁ n)
(bounded : ∀ n, (circuit_family n).size ≤ T n)
(ch : ∀ n v, (circuit_family n).val v = vector.singleton (f v.val))


namespace CNF
variables {m n : ℕ}
def to_circuit : CNF m n → circuit₁ n := by {  }
end CNF