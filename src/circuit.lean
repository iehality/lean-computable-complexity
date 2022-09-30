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

@[simp] def map : Π {n n' m m' : ℕ} (f : fin n → fin n') (g : fin m → fin m'), gate n m → gate n' m'
| _ _ _ _ f g (atom i) := atom (f i)
| _ _ _ _ f g (ctn j)  := ctn (g j)
| _ _ _ _ f g (not j)  := not (g j)
| _ _ _ _ f g (and s)  := and (s.image g)
| _ _ _ _ f g (or s)   := or (s.image g)

def shift {n n' m m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') (g : gate n m) : gate n' m' :=
g.map (λ i, ⟨i, lt_of_lt_of_le i.property hn⟩) (λ j, ⟨j, lt_of_lt_of_le j.property hm⟩)

@[simp] def lift : Π {n m} (k), gate n m → gate k (n + m)
| _ _ _ (atom i) := ctn ⟨i, nat.lt_add_right _ _ _ i.property⟩
| n _ _ (ctn j)  := ctn ⟨n + j, by simpa using j.property⟩
| n _ _ (not j)  := not ⟨n + j, by simpa using j.property⟩
| n _ _ (and s)  := and (s.image (λ j, ⟨n + j, by simpa using j.property⟩))
| n _ _ (or s)   := or (s.image (λ j, ⟨n + j, by simpa using j.property⟩))

@[simp] def val : Π {n m}, gate n m → 𝕓 n → 𝕓 m → bool
| _ _ (atom i) v w := v.nth i
| _ _ (ctn j)  v w := w.nth j
| _ _ (not j)  v w := bnot (w.nth j)
| _ _ (and s)  v w := s.inf w.nth
| _ _ (or s)   v w := s.sup w.nth

lemma lift_val : ∀ {n m k : ℕ} (g : gate n m) (v : 𝕓 n) (w : 𝕓 m) (u : 𝕓 k),
  (g.lift k).val u (v.append w) = g.val v w
| _ _ _ (atom i) v w u := by simp
| _ _ _ (ctn j)  v w u := by simp
| _ _ _ (not j)  v w u := by simp
| _ _ _ (and s)  v w u := by simp[finset.inf_image]; refine congr_arg _ (by ext; simp)
| _ _ _ (or s)   v w u := by simp[finset.sup_image]; refine congr_arg _ (by ext; simp)

inductive bounded (b : ℕ) : ∀ {n m}, gate n m → Prop
| atom : ∀ {n m : ℕ} (i : fin n), bounded (@atom n m i)
| ctn  : ∀ {n m : ℕ} (j : fin m), bounded (@ctn n m j)
| not  : ∀ {n m : ℕ} (j : fin m), bounded (@not n m j)
| and  : ∀ {n m : ℕ} {s : finset (fin m)} (h : s.card ≤ b), bounded (@and n m s)
| or   : ∀ {n m : ℕ} {s : finset (fin m)} (h : s.card ≤ b), bounded (@or n m s)

attribute [simp] bounded.atom bounded.ctn bounded.not

def and₂ {n m} (i j : fin m) : gate n m := and {i, j}

infix ` ∧ᵍ `:80 := and₂

def or₂ {n m} (i j : fin m) : gate n m := or {i, j}

infix ` ∨ᵍ `:80 := or₂

lemma and₂_bounded {n m} (i j : fin m) : (i ∧ᵍ j : gate n m).bounded 2 :=
bounded.and (by simpa using finset.card_insert_le i {j})

lemma or₂_bounded {n m} (i j : fin m) : (i ∨ᵍ j : gate n m).bounded 2 :=
bounded.or (by simpa using finset.card_insert_le i {j})

end gate

-- circuit : fun-in → gateの数 → Type
inductive circuit : ℕ → ℕ → Type u
| nil (n) : circuit n 0
| cons {n m} : gate n m → circuit n m → circuit n m.succ

structure Circuit (n : ℕ) :=
(size : ℕ)
(val : circuit n size.succ)

namespace circuit
open gate

inductive bounded (b : ℕ) : Π {n m}, circuit n m → Prop
| nil  : ∀ n, bounded (nil n)
| cons : ∀ {n m} {c : circuit n m} {g : gate n m}, g.bounded b → bounded c → bounded (cons g c)

def eval : Π {n m}, circuit n m → 𝕓 n → 𝕓 m
| _ _ (nil n)     _ := vector.nil
| _ _ (cons g c)  v := g.val v (c.eval v) ::ᵥ c.eval v

@[simp] def val {n m : ℕ} (c : circuit n m.succ) (v : 𝕓 n) : bool := (c.eval v).head

@[simp] def depth_vec : Π {n m}, circuit n m → vector ℕ m
| _ _ (nil n)           := vector.nil
| _ _ (cons (atom i) c) := 1 ::ᵥ depth_vec c
| _ _ (cons (ctn i) c)  := let ih := depth_vec c in (ih.nth i + 1) ::ᵥ ih
| _ _ (cons (not i) c)  := let ih := depth_vec c in (ih.nth i + 1) ::ᵥ ih
| _ _ (cons (and s) c)  := let ih := depth_vec c in (s.sup ih.nth + 1) ::ᵥ ih
| _ _ (cons (or s) c)   := let ih := depth_vec c in (s.sup ih.nth + 1) ::ᵥ ih

def depth {n m} (c : circuit n m) : ℕ := (depth_vec c).to_list.sup

def comp : Π {n m k}, circuit n m → circuit m k → circuit n (m + k)
| _ _ _ c₁ (nil n)     := c₁
| n m k c₁ (cons g c₂) := cons (g.lift n) (c₁.comp c₂)

lemma cons_depth {n m} (g : gate n m) (c : circuit n m) : (cons g c).depth ≤ c.depth + 1 :=
by rcases g; simp[depth]

lemma comp_depth : ∀ {n m k} (c₁ : circuit n m) (c₂ : circuit m k), (c₁.comp c₂).depth ≤ c₁.depth + c₂.depth
| _ _ _ c₁ (nil n) := by simp[comp]
| n _ _ (c₁ : circuit n m) (@cons m k g c₂) := by { simp[comp], sorry }

end circuit

namespace Circuit

abbreviation depth {n} (c : Circuit n) := c.2.depth

-- def nil (n : ℕ) : Circuit n := ⟨0, circuit.nil n⟩

-- def cons {n} (c : Circuit n) (g : gate n c.size) : Circuit n := ⟨c.size.succ, c.val.cons g⟩

end Circuit

structure SIZE (T : ℕ → ℕ) (f : 𝔹 → bool)
(circuit_family : Π n, Circuit n)
(bounded : ∀ n, (circuit_family n).size ≤ T n)
(ch : ∀ n v, (circuit_family n).val.val v = f v.val)


namespace CNF
variables {m n : ℕ}

end CNF