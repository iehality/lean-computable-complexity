import vorspiel boolean_logic binary_recursion

universes u v

inductive circuit : ℕ → ℕ → Type
| relay    {n}     : fin n → circuit n 1 -- id gate
| not      {n}     : fin n → circuit n 1 -- NOT disjunction
| and      {n}     : finset (fin n) → circuit n 1 -- AND conjunction
| or       {n}     : finset (fin n) → circuit n 1 -- OR disjunction
| parallel {n m k} : circuit n m → circuit n k → circuit n (k + m)
| serial   {n m k} : circuit n m → circuit m k → circuit n k

infixl ` ∥ `: 70 := circuit.parallel

infixl ` ▷ `: 70 := circuit.serial

namespace circuit

@[simp] def size : ∀ {n m}, circuit n m → ℕ
| _ _ (relay i) := 0
| _ _ (not i)   := 1
| _ _ (and s)   := 1
| _ _ (or s)    := 1
| _ _ (c₁ ∥ c₂) := c₁.size + c₂.size
| _ _ (c₁ ▷ c₂) := c₁.size + c₂.size

@[simp] def depth : ∀ {n m}, circuit n m → ℕ
| _ _ (relay i) := 0
| _ _ (not i)   := 1
| _ _ (and s)   := 1
| _ _ (or s)    := 1
| _ _ (c₁ ∥ c₂) := max c₁.depth c₂.depth
| _ _ (c₁ ▷ c₂) := c₁.depth + c₂.depth

lemma depth_le_size : ∀ {n m} (c : circuit n m), c.depth ≤ c.size
| _ _ (relay i) := by simp
| _ _ (not i)   := by simp
| _ _ (and s)   := by simp
| _ _ (or s)    := by simp
| _ _ (c₁ ∥ c₂) := by simp; exact ⟨le_add_right (depth_le_size c₁), le_add_left (depth_le_size c₂)⟩
| _ _ (c₁ ▷ c₂) := by simp; exact add_le_add (depth_le_size c₁) (depth_le_size c₂)

@[simp] def eval : Π {n m}, circuit n m → 𝕓 n → 𝕓 m
| _ _ (relay i) d := d.nth i
| _ _ (not i)   d := bnot (d.nth i)
| _ _ (and s)   d := ↑(s.inf d.nth)
| _ _ (or s)    d := ↑(s.sup d.nth)
| _ _ (c₁ ∥ c₂) d := (c₁.eval d) ++ᵥ (c₂.eval d)
| _ _ (c₁ ▷ c₂) d := c₂.eval (c₁.eval d)

def val {n} (c : circuit n 1) (v : 𝕓 n) : bool := (c.eval v).head

@[simp] def bounded (b : ℕ) : ∀ {n m}, circuit n m → Prop
| _ _ (relay i) := true
| _ _ (not i)   := true
| _ _ (and s)   := s.card ≤ b
| _ _ (or s)    := s.card ≤ b
| _ _ (c₁ ∥ c₂) := c₁.bounded ∧ c₂.bounded
| _ _ (c₁ ▷ c₂) := c₁.bounded ∧ c₂.bounded

section map

@[simp] def map : ∀ {n n' m} (f : fin n → fin n'), circuit n m → circuit n' m
| _ _ _ f (relay i) := relay (f i)
| _ _ _ f (not i)   := not (f i)
| _ _ _ f (and s)   := and (s.image f)
| _ _ _ f (or s)    := or (s.image f)
| _ _ _ f (c₁ ∥ c₂) := parallel (c₁.map f) (c₂.map f)
| _ _ _ f (c₁ ▷ c₂) := serial (c₁.map f) c₂

@[simp] lemma map_size : ∀ {n n' m} (f : fin n → fin n') (c : circuit n m), (c.map f).size = c.size
| _ _ _ f (relay i) := by simp
| _ _ _ f (not i)   := by simp
| _ _ _ f (and s)   := by simp
| _ _ _ f (or s)    := by simp
| _ _ _ f (c₁ ∥ c₂) := by simp[map_size f c₁, map_size f c₂]
| _ _ _ f (c₁ ▷ c₂) := by simp[map_size f c₁]

@[simp] lemma map_depth : ∀ {n n' m} (f : fin n → fin n') (c : circuit n m), (c.map f).depth = c.depth
| _ _ _ f (relay i) := by simp
| _ _ _ f (not i)   := by simp
| _ _ _ f (and s)   := by simp
| _ _ _ f (or s)    := by simp
| _ _ _ f (c₁ ∥ c₂) := by simp[map_depth f c₁, map_depth f c₂]
| _ _ _ f (c₁ ▷ c₂) := by simp[map_depth f c₁]

lemma map_eval : ∀ {n n' m} (f : fin n → fin n') (c : circuit n m) (v),
  (c.map f).eval v = c.eval (vector.of_fn $ λ i, v.nth (f i))
| _ _ _ f (relay i) v := by simp
| _ _ _ f (not i)   v := by simp
| _ _ _ f (and s)   v := by simp[finset.inf_image]; refine congr_arg _ (funext $ by simp)
| _ _ _ f (or s)    v := by simp[finset.sup_image]; refine congr_arg _ (funext $ by simp)
| _ _ _ f (c₁ ∥ c₂) v := by simp[map_eval f c₁, map_eval f c₂]
| _ _ _ f (c₁ ▷ c₂) v := by simp[map_eval f c₁]

@[simp] lemma map_bounded (b) : ∀ {n n' m} (f : fin n → fin n') (c : circuit n m), c.bounded b → (c.map f).bounded b
| _ _ _ f (relay i) h := by simp
| _ _ _ f (not i)   h := by simp
| _ _ _ f (and s)   h := le_trans finset.card_image_le h
| _ _ _ f (or s)    h := le_trans finset.card_image_le h
| _ _ _ f (c₁ ∥ c₂) h := ⟨map_bounded f c₁ h.1, map_bounded f c₂ h.2⟩
| _ _ _ f (c₁ ▷ c₂) h := ⟨map_bounded f c₁ h.1, h.2⟩

end map

section disjoint_parallel
variables {n₁ n₂ m₁ m₂ : ℕ} (c₁ : circuit n₁ m₁) (c₂ : circuit n₂ m₂)

def disjoint_parallel : circuit (n₂ + n₁) (m₂ + m₁) :=
let c'₁ : circuit (n₂ + n₁) m₁ := c₁.map (λ i, ⟨i, nat.lt_add_left _ _ _ i.property⟩),
    c'₂ : circuit (n₂ + n₁) m₂ := c₂.map (λ i, ⟨n₁ + i, by simp[add_comm]⟩) in
c'₁ ∥ c'₂

infixl ` |+| `:65 := disjoint_parallel

@[simp] lemma disjoint_parallel_size : (c₁ |+| c₂).size = c₁.size + c₂.size := by simp[(|+|)]

@[simp] lemma disjoint_parallel_depth : (c₁ |+| c₂).depth = max c₁.depth c₂.depth := by simp[(|+|)]

@[simp] lemma disjoint_parallel_eval_append (v₁ : 𝕓 n₁) (v₂ : 𝕓 n₂) : 
  (c₁ |+| c₂).eval (v₁ ++ᵥ v₂) = c₁.eval v₁ ++ᵥ c₂.eval v₂ :=
by simp[(|+|), map_eval]

@[simp] lemma disjoint_parallel_eval_cons {n} (c₁ : circuit 1 m₁) (c₂ : circuit n m₂) (b : bool) (v : 𝕓 n) :
  (c₁ |+| c₂).eval (b ::ᵥ v) = c₁.eval b ++ᵥ c₂.eval v :=
by { have : b ::ᵥ v = (b : 𝕓 1) ++ᵥ v, by simp[vector.coe_succ],
     simp[this] }

end disjoint_parallel

section gate
variables {n : ℕ}

section

def andl (i j : fin n) : circuit n 1 := and {i, j}

def orl (i j : fin n) : circuit n 1 := or {i, j}

@[simp] lemma andl_bounded {i j : fin n} : bounded 2 (andl i j) := by simpa using finset.card_insert_le i {j}

@[simp] lemma orl_bounded {i j : fin n} : bounded 2 (orl i j) := by simpa using finset.card_insert_le i {j}

@[simp] lemma andl_eval (i j : fin n) (v) : (andl i j).eval v = v.nth i && v.nth j := by simp[andl]

@[simp] lemma orl_eval (i j : fin n) (v) : (orl i j).eval v = v.nth i || v.nth j := by simp[orl]

@[simp] lemma andl_size (i j : fin n) : (andl i j).size = 1 := by simp[andl]

@[simp] lemma orl_size (i j : fin n) : (orl i j).size = 1 := by simp[orl]

@[simp] lemma andl_depth (i j : fin n) : (andl i j).depth = 1 := by simp[andl]

@[simp] lemma orl_depth (i j : fin n) : (orl i j).depth = 1 := by simp[orl]

end

section conj 

def conj : circuit 2 1 := and {0, 1}

@[simp] lemma conj_size : (conj : circuit 2 1).size = 1 := by simp[conj]

@[simp] lemma conj_depth : (conj : circuit 2 1).depth = 1 := by simp[conj]

@[simp] lemma conj_eval (v) : (conj : circuit 2 1).eval v = v.inf := by simp[conj]

end conj

section relay'

def relay' : circuit 1 1 := relay 0

@[simp] lemma relay'_size : (relay' : circuit 1 1).size = 0 := by simp[relay']

@[simp] lemma relay'_depth : (relay' : circuit 1 1).depth = 0 := by simp[relay']

@[simp] lemma relay'_eval (v) : (relay' : circuit 1 1).eval v = v := by simp[relay']

end relay'

section

def zero_tt (n : ℕ) : circuit n 1 := and ∅

instance : has_top (circuit n 1) := ⟨zero_tt n⟩

def zero_ff (n : ℕ) : circuit n 1 := or ∅

instance : has_bot (circuit n 1) := ⟨zero_ff n⟩

@[simp] lemma top_bounded (k) : (⊤ : circuit n 1).bounded k := by unfold has_top.top; simp[zero_tt]

@[simp] lemma bot_bounded (k) : (⊥ : circuit n 1).bounded k := by unfold has_bot.bot; simp[zero_ff]

@[simp] lemma top_eval (v) : (⊤ : circuit n 1).eval v = tt := by unfold has_top.top; simp[zero_tt]

@[simp] lemma bot_eval (v) : (⊥ : circuit n 1).eval v = ff := by unfold has_bot.bot; simp[zero_ff]

@[simp] lemma top_size : (⊤ : circuit n 1).size = 1 := by unfold has_top.top; simp[zero_tt]

@[simp] lemma bot_size : (⊥ : circuit n 1).size = 1 := by unfold has_bot.bot; simp[zero_ff]

@[simp] lemma top_depth : (⊤ : circuit n 1).depth = 1 := by unfold has_top.top; simp[zero_tt]

@[simp] lemma bot_depth : (⊥ : circuit n 1).depth = 1 := by unfold has_bot.bot; simp[zero_ff]

end

section bounded_and

def bounded_and : Π n, circuit n 1 := nat.binary_recursion ⊤
  (λ n hn c, (c |+| c) ▷ conj)
  (λ n c, (relay' |+| (c |+| c) ▷ conj) ▷ conj)

lemma bounded_and_bit0 {n : ℕ} (h : n ≠ 0) : bounded_and (bit0 n) = (bounded_and n |+| bounded_and n) ▷ conj :=
nat.binary_recursion_bit0_eq h

lemma bounded_and_bit1 (n) : bounded_and (bit1 n) = (relay' |+| (bounded_and n |+| bounded_and n) ▷ conj) ▷ conj:=
nat.binary_recursion_bit1_eq n

lemma bounden_and_eval : ∀ n (v : 𝕓 n), (bounded_and n).eval v = v.inf := 
nat.binary_recursion (by simp[bounded_and])
  (λ n hn IH v, by { 
    rw ←vector.append'_half_even v,
    simp[bounded_and_bit0 hn, IH, vector.coe_succ] })
  (λ n IH v, by { 
    rw [←vector.append'_half_odd v, bounded_and_bit1 n],
    simp[bounded_and_bit1, IH] })

lemma bounded_and_size : ∀ n, (bounded_and n).size ≤ n - 1 :=
nat.binary_recursion (by { simp[bounded_and], })
  (λ n h IH, by { simp[bounded_and_bit0 h], sorry })
  (λ n IH, by { simp[bounded_and_bit1 n], })

end bounded_and

end gate

end circuit



