import vorspiel binary_recursion init.algebra.order tactic.omega.main

universes u v

attribute [simp] pi.smul_apply

namespace landau_notation

variables (α : Type u) [has_mul α] [linear_order α]

def eventually (p : ℕ → Prop) : Prop := ∃ n : ℕ, ∀ m ≥ n, p m

local notation `Eventually` binders `, ` r:(scoped p, eventually p) := r

def frequently (p : ℕ → Prop) : Prop := ∀ n : ℕ, ∃ m ≥ n, p m

local notation `Frequently` binders `, ` r:(scoped p, frequently p) := r

lemma eventually_def (p : ℕ → Prop) : (Eventually x, p x) ↔ (∃ n : ℕ, ∀ m ≥ n, p m) := by refl

@[simp] lemma eventually_true : Eventually x, true :=
⟨0, by simp⟩

lemma eventually_of_all (p : ℕ → Prop) (h : ∀ x, p x) : Eventually x, p x := ⟨0, λ m _, h m⟩

lemma eventually_and {p q : ℕ → Prop} : (Eventually x, p x ∧ q x) ↔ (Eventually x, p x) ∧ (Eventually x, q x) :=
⟨by { rintros ⟨M, h⟩, refine ⟨⟨M, λ m le, (h m le).left⟩, ⟨M, λ m le, (h m le).right⟩⟩ },
 by { rintros ⟨⟨M₁, h₁⟩, ⟨M₂, h₂⟩⟩, refine ⟨max M₁ M₂, _⟩, simp, intros m le₁ le₂, exact ⟨h₁ m le₁, h₂ m le₂⟩ }⟩

lemma eventually_imply {p q : ℕ → Prop} (I : ∀ x, p x → q x) : (Eventually x, p x) → (Eventually x, q x) :=
by rintros ⟨c, h⟩; refine ⟨c, λ m le, I _ (h m le)⟩

lemma frequently_def (p : ℕ → Prop) : (Frequently x, p x) ↔ (∀ n : ℕ, ∃ m ≥ n, p m) := by refl

def bigO (f g : ℕ → ℕ) : Prop := ∃ c, c ≠ 0 ∧ Eventually x, f x ≤ c * g x

infix ` ≤ᴼ `:50 := bigO

def littleo (f g : ℕ → ℕ) : Prop := ∀ e, e ≠ 0 ∧ Eventually x, f x ≤ g x / e

infix ` ≤ₒ `:50 := littleo

def bigΘ (f g : ℕ → ℕ) : Prop := f ≤ᴼ g ∧ g ≤ᴼ f

infix ` ≃Θ `:60 := bigΘ

namespace bigO
variables {f g h : ℕ → ℕ}

@[refl, simp] protected lemma refl : f ≤ᴼ f :=
⟨1, one_ne_zero, 0, λ m _, by simp⟩

@[trans] lemma trans : f ≤ᴼ g → g ≤ᴼ h → f ≤ᴼ h :=
begin
  rintros ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩,
  refine ⟨c₁ * c₂, by simp[hc₁, hc₂], _⟩,
  have : (Eventually x, f x ≤ c₁ * g x ∧ g x ≤ c₂ * h x), refine eventually_and.mpr ⟨h₁, h₂⟩,
  refine eventually_imply _ this,
  { rintros x ⟨le₁, le₂⟩, 
    have : c₁ * g x ≤ c₁ * c₂ * h x, by simpa[mul_assoc] using mul_le_mul_left' le₂ c₁,
    exact le_trans le₁ this }
end

@[simp] lemma zero_le : 0 ≤ᴼ f := ⟨1, by simp, by simp⟩

lemma of_beq (n : ℕ) (h : ∀ m ≥ n, f m = g m) : f ≃Θ g :=
⟨⟨1, by simp, n, λ m hm, by simp[h m hm]⟩, ⟨1, by simp, n, λ m hm, by simp[h m hm]⟩⟩ 

end bigO

namespace bigΘ
variables {f g h : ℕ → ℕ}

@[refl, simp] protected lemma refl (f) : f ≃Θ f := ⟨by refl, by refl⟩

@[symm] protected lemma symm : f ≃Θ g → g ≃Θ f := λ ⟨h₁, h₂⟩, ⟨h₂, h₁⟩ 

@[trans] protected lemma trans : f ≃Θ g → g ≃Θ h → f ≃Θ h :=
λ ⟨hf₁, hf₂⟩ ⟨hg₁, hg₂⟩, ⟨hf₁.trans hg₁, hg₂.trans hf₂⟩ 

theorem equivalence : equivalence (≃Θ) :=
⟨landau_notation.bigΘ.refl, @landau_notation.bigΘ.symm, @landau_notation.bigΘ.trans⟩

def setoid : setoid (ℕ → ℕ) := ⟨_, equivalence⟩

def quo := quotient setoid

def bigO_class (f : ℕ → ℕ) : quo := quotient.mk' f

notation `O[` f `]` := bigO_class f

def log := O[Log]

def linear := O[id]

def exp := O[(^) 2]

@[elab_as_eliminator]
protected lemma ind_on {C : quo → Prop} (q : quo) (h : ∀ f, C O[f]) : C q := quotient.induction_on' q h

@[elab_as_eliminator, reducible]
protected def lift_on {φ : Sort*} (q : quo) (F : (ℕ → ℕ) → φ)
  (h : ∀ f g, f ≃Θ g → F f = F g) : φ := quotient.lift_on' q F h

@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ : Sort*} (q₁ q₂ : quo) (F : (ℕ → ℕ) → (ℕ → ℕ) → φ)
  (h : ∀ f₁ f₂ g₁ g₂, f₁ ≃Θ g₁ → f₂ ≃Θ g₂ → F f₁ f₂ = F g₁ g₂) : φ :=
quotient.lift_on₂' q₁ q₂ F h

@[simp] protected lemma lift_on₂_eq {φ : Sort*} (f g : ℕ → ℕ) (F : (ℕ → ℕ) → (ℕ → ℕ) → φ) (h) :
  bigΘ.lift_on₂ O[f] O[g] F h = F f g := rfl

lemma of_eq_of {f g : ℕ → ℕ} : O[f] = O[g] ↔ f ≃Θ g := quotient.eq'

lemma of_eq {f g : ℕ → ℕ} (h : f = g) : O[f] = O[g] := by rw h

lemma nat_fun_maximum (f : ℕ → ℕ) (n : ℕ) : ∃ m, ∀ n' < n, f n' ≤ m :=
by { induction n with n IH,
     { simp }, { rcases IH with ⟨m, IH⟩, refine ⟨max m (f n), _⟩,
     intros n' hn',
     have : n' < n ∨ n' = n, from nat.lt_succ_iff_lt_or_eq.mp hn',
     rcases this with (hn' | rfl),
     { simp[IH n' hn'] }, { simp } } }

section arith

instance : has_add quo :=
⟨λ q₁ q₂, bigΘ.lift_on₂ q₁ q₂ (λ f g, O[f + g])
  (by { rintros f₁ f₂ g₁ g₂ ⟨hfg₁, hgf₁⟩ ⟨hfg₂, hgf₂⟩,
        refine of_eq_of.mpr ⟨_, _⟩,
        { rcases hfg₁ with ⟨c₁, hc₁, n₁, h₁⟩, rcases hfg₂ with ⟨c₂, hc₂, n₂, h₂⟩,
          refine ⟨max c₁ c₂, by simp[hc₁, hc₂], max n₁ n₂, _⟩, simp[mul_add],
          intros m hm₁ hm₂,
          refine add_le_add
            ((h₁ m hm₁).trans (nat.mul_le_mul_right _ (by simp)))
            ((h₂ m hm₂).trans (nat.mul_le_mul_right _ (by simp))) },
        { rcases hgf₁ with ⟨c₁, hc₁, n₁, h₁⟩, rcases hgf₂ with ⟨c₂, hc₂, n₂, h₂⟩,
          refine ⟨max c₁ c₂, by simp[hc₁, hc₂], max n₁ n₂, _⟩, simp[mul_add],
          intros m hm₁ hm₂,
          refine add_le_add
            ((h₁ m hm₁).trans (nat.mul_le_mul_right _ (by simp)))
            ((h₂ m hm₂).trans (nat.mul_le_mul_right _ (by simp))) } })⟩

instance : has_mul quo :=
⟨λ q₁ q₂, bigΘ.lift_on₂ q₁ q₂ (λ f g, O[f * g])
  (by { rintros f₁ f₂ g₁ g₂ ⟨hfg₁, hgf₁⟩ ⟨hfg₂, hgf₂⟩,
        refine of_eq_of.mpr ⟨_, _⟩,
        { rcases hfg₁ with ⟨c₁, hc₁, n₁, h₁⟩, rcases hfg₂ with ⟨c₂, hc₂, n₂, h₂⟩,
          refine ⟨c₁ * c₂, by simp[hc₁, hc₂], max n₁ n₂, _⟩, simp[mul_add],
          intros m hm₁ hm₂,
          calc f₁ m * f₂ m ≤ (c₁ * g₁ m) * (c₂ * g₂ m) : nat.mul_le_mul (h₁ m hm₁) (h₂ m hm₂)
                       ... = c₁ * c₂ * (g₁ m * g₂ m)   : by ring },
        { rcases hgf₁ with ⟨c₁, hc₁, n₁, h₁⟩, rcases hgf₂ with ⟨c₂, hc₂, n₂, h₂⟩,
          refine ⟨c₁ * c₂, by simp[hc₁, hc₂], max n₁ n₂, _⟩, simp[mul_add],
          intros m hm₁ hm₂, 
          calc g₁ m * g₂ m ≤ (c₁ * f₁ m) * (c₂ * f₂ m) : nat.mul_le_mul (h₁ m hm₁) (h₂ m hm₂)
                       ... = c₁ * c₂ * (f₁ m * f₂ m)   : by ring } })⟩

variables (f g)

lemma of_add_of : O[f + g] = O[f] + O[g] := by refl

lemma of_mul_of : O[f * g] = O[f] * O[g] := by refl

@[simp] lemma smul_eq {c} (h : c ≠ 0) : O[c • f] = O[f] :=
of_eq_of.mpr ⟨⟨c, h, 0, by simp⟩, by { refine ⟨1, by simp, 0, λ m _, by { simp; exact nat.le_mul_of_pos_left (pos_iff_ne_zero.mpr h) }⟩ }⟩ 

variables {f g}

instance : add_comm_monoid quo :=
{ add_assoc := λ q₁ q₂ q₃,
  by { 
    induction q₁ using landau_notation.bigΘ.ind_on with f,
    induction q₂ using landau_notation.bigΘ.ind_on with g,
    induction q₃ using landau_notation.bigΘ.ind_on with h,
    simp[←of_add_of, add_assoc] },
  zero := O[0],
  zero_add := λ q, by { 
    induction q using landau_notation.bigΘ.ind_on with f,
    simp[←of_add_of] },
  add_zero := λ q, by { 
    induction q using landau_notation.bigΘ.ind_on with f,
    simp[←of_add_of] },
  add_comm := λ q₁ q₂, by { 
    induction q₁ using landau_notation.bigΘ.ind_on with f,
    induction q₂ using landau_notation.bigΘ.ind_on with g,
    simp[←of_add_of, add_comm] },
  ..quo.has_add }

lemma zero_def : 0 = O[0] := rfl

instance : comm_monoid quo :=
{ mul_assoc := λ q₁ q₂ q₃,
  by { 
    induction q₁ using landau_notation.bigΘ.ind_on with f,
    induction q₂ using landau_notation.bigΘ.ind_on with g,
    induction q₃ using landau_notation.bigΘ.ind_on with h,
    simp[←of_mul_of, mul_assoc] },
  one := O[1],
  one_mul := λ q, by { 
    induction q using landau_notation.bigΘ.ind_on with f,
    simp[←of_mul_of] },
  mul_one := λ q, by { 
    induction q using landau_notation.bigΘ.ind_on with f,
    simp[←of_mul_of] },
  mul_comm := λ q₁ q₂, by { 
    induction q₁ using landau_notation.bigΘ.ind_on with f,
    induction q₂ using landau_notation.bigΘ.ind_on with g,
    simp[←of_mul_of, mul_comm] },
  ..quo.has_mul }

instance : monoid_with_zero quo :=
{ zero_mul := λ q, by { 
    induction q using landau_notation.bigΘ.ind_on with f,
    simp[show add_comm_monoid.zero = O[0], by refl], unfold comm_monoid.mul,
    simp[←of_mul_of] },
  mul_zero := λ q, by { 
    induction q using landau_notation.bigΘ.ind_on with f,
    simp[show add_comm_monoid.zero = O[0], by refl], unfold comm_monoid.mul,
    simp[←of_mul_of] },
  .. quo.add_comm_monoid, ..quo.comm_monoid }

lemma one_def : 1 = O[1] := rfl

instance : distrib quo :=
{ left_distrib := λ q₁ q₂ q₃, by { 
    induction q₁ using landau_notation.bigΘ.ind_on with f,
    induction q₂ using landau_notation.bigΘ.ind_on with g,
    induction q₃ using landau_notation.bigΘ.ind_on with h,
    simp[←of_add_of, ←of_mul_of],
    refine of_eq (funext $ λ x, by simp[mul_add]) },
  right_distrib := λ q₁ q₂ q₃, by { 
    induction q₁ using landau_notation.bigΘ.ind_on with f,
    induction q₂ using landau_notation.bigΘ.ind_on with g,
    induction q₃ using landau_notation.bigΘ.ind_on with h,
    simp[←of_add_of, ←of_mul_of],
    refine of_eq (funext $ λ x, by simp[add_mul]) },
  ..quo.has_add, ..quo.has_mul }

end arith

section order

instance : partial_order quo :=
{ le := λ q₁ q₂, bigΘ.lift_on₂ q₁ q₂ (λ f g, f ≤ᴼ g)
    (by { rintros f₁ f₂ g₁ g₂ ⟨hfg₁, hgf₁⟩ ⟨hfg₂, hgf₂⟩, simp,
          refine ⟨λ h, (hgf₁.trans h).trans hfg₂, λ h, (hfg₁.trans h).trans hgf₂⟩ }),
  le_refl := λ q, by { induction q using landau_notation.bigΘ.ind_on with f, simp },
  le_trans := λ q₁ q₂ q₃,
    by { induction q₁ using landau_notation.bigΘ.ind_on with f,
         induction q₂ using landau_notation.bigΘ.ind_on with g,
         induction q₃ using landau_notation.bigΘ.ind_on with h, simp, exact bigO.trans },
  le_antisymm := λ q₁ q₂,
    by { induction q₁ using landau_notation.bigΘ.ind_on with f,
         induction q₂ using landau_notation.bigΘ.ind_on with g, simp[has_le.le, preorder.le, of_eq_of],
         intros h₁ h₂, refine ⟨h₁, h₂⟩ } }

lemma of_le_of : O[f] ≤ O[g] ↔ f ≤ᴼ g := by simp[(≤), preorder.le, partial_order.le]

instance : semilattice_sup quo :=
{ sup := (+),
  le_sup_left := λ q₁ q₂,
    by{ induction q₁ using landau_notation.bigΘ.ind_on with f,
        induction q₂ using landau_notation.bigΘ.ind_on with g,
        simp[←of_add_of, of_eq_of, of_le_of],
        refine ⟨1, by simp, 0, λ m _, by simp⟩ },
  le_sup_right := λ q₁ q₂,
    by{ induction q₁ using landau_notation.bigΘ.ind_on with f,
        induction q₂ using landau_notation.bigΘ.ind_on with g,
        simp[←of_add_of, of_eq_of, of_le_of],
        refine ⟨1, by simp, 0, λ m _, by simp⟩ },
  sup_le := λ q₁ q₂ q₃,
    by{ induction q₁ using landau_notation.bigΘ.ind_on with f,
        induction q₂ using landau_notation.bigΘ.ind_on with g,
        induction q₃ using landau_notation.bigΘ.ind_on with h,
        simp[←of_add_of, of_le_of],
        rintros ⟨c₁, hc₁, m₁, h₁⟩ ⟨c₂, hc₂, m₂, h₂⟩,
        refine ⟨c₁ + c₂, by simp[hc₁, hc₂], max m₁ m₂,
          by{ simp, intros m le₁ le₂,
              calc f m + g m ≤ c₁ * h m + c₂ * h m : add_le_add (h₁ m le₁) (h₂ m le₂)
                         ... = (c₁ + c₂) * h m     : by simp[add_mul] }⟩ },
  .. quo.partial_order }

lemma sup_def {q₁ q₂ : quo} : q₁ ⊔ q₂ = q₁ + q₂ := rfl

instance : order_bot quo := ⟨0, λ q, by { induction q using landau_notation.bigΘ.ind_on with f, simp[zero_def, of_le_of] }⟩

lemma bot_def : (⊥ : quo) = 0 := rfl

@[simp] lemma smul_le {c : ℕ} (f) : O[c • f] ≤ O[f] :=
by { by_cases C : c = 0, { simp[C, ←zero_def, ←bot_def] }, { rw[smul_eq f C] } }

end order

section const
variables {f}

lemma eq_zero : O[f] = 0 ↔ Eventually n, f n = 0 :=
by { simp [zero_def, of_eq_of, (≃Θ)], split,
     { rintros ⟨c, hc, h⟩, simpa using h }, { intros h, refine ⟨1, by simp, by simpa using h⟩ } }

lemma le_one_iff : O[f] ≤ 1 ↔ ∃ M, ∀ n, f n ≤ M :=
begin 
  simp[one_def, of_eq_of], split,
  { rintros ⟨c, hc, n, h⟩, simp at h,
    have :  ∃ m, ∀ n' < n, f n' ≤ m, from nat_fun_maximum f n,
    rcases this with ⟨m, hm⟩,
    refine ⟨max m c, λ n', _⟩,
    have : n' < n ∨ n ≤ n', from lt_or_ge n' n,
    rcases this with (hn' | hn'),
    { simp [hm n' hn'] }, { simp[h n' hn'] } },
  { rintros ⟨M, hM⟩,
    refine ⟨M + 1, by simp, 0, λ m _, _⟩, simp,
    exact le_add_right (hM m) }
end

lemma one_le_iff : 1 ≤ O[f] ↔ Eventually n, f n ≠ 0 :=
by { simp[one_def, of_le_of], split,
     { rintros ⟨c, hc, b, h⟩, simp at h, refine ⟨b, λ m hm A, _⟩, have : 1 ≤ c * f m, from h m hm, rw[A] at this, simpa using this },
     { rintros ⟨b, h⟩, refine ⟨1, by simp, b, _⟩, simpa[nat.one_le_iff_ne_zero] using h } }

lemma eq_one_of : O[f] = 1 ↔ (∃ M, ∀ n, f n ≤ M) ∧ (Eventually n, f n ≠ 0) :=
by rw[le_antisymm_iff, le_one_iff, one_le_iff] 

@[simp] lemma const_eq_one {c : ℕ} (h : c ≠ 0) : O[λ _, c] = 1 := by simp[eq_one_of, h]; refine ⟨c, by refl⟩

end const

section pow

lemma pow_eq (n : ℕ) (f) : O[f]^n = O[f^n] :=
begin
  induction n with n IH,
  { simp[one_def] },
  { calc
      O[f] ^ n.succ = O[f] * O[f^n] : by simp[pow_succ, IH]
                ... = O[f ^ n.succ] : by simp[pow_succ, of_mul_of] }
end

lemma poly_mono {n m : ℕ} (h : n ≤ m) : linear^n ≤ linear^m :=
by{ simp[linear, pow_eq, of_le_of], refine ⟨1, by simp, 1, λ x hx, by { simp, refine pow_mono hx h}⟩ }

lemma log_mono {n m : ℕ} (h : n ≤ m) : log^n ≤ log^m :=
by{ simp[log, pow_eq, of_le_of],
    refine ⟨1, by simp, 1, λ x hx, by { simp, refine pow_mono (by simpa using Log_monotone hx) h}⟩ }

end pow

section Log
variables {f}

@[simp] lemma zero_le (q : quo) : 0 ≤ q := by simp[←bot_def]

@[simp] lemma one_le_Log : 1 ≤ log :=
by { simp[log, one_def, of_le_of], refine ⟨1, by simp, 1, λ m hm, by simpa using Log_monotone hm⟩ }

lemma log_le_of_le {n m : ℕ} (h : n ≤ m) : log^n ≤ log^m :=
by { simp[log, pow_eq, of_le_of], refine ⟨1, by simp, 1, λ x hx, by { simp, exact pow_mono (by simpa using Log_monotone hx) h}⟩ }

end Log

section linear
variables {f}

lemma linear_le_of_le {n m : ℕ} (h : n ≤ m) : linear^n ≤ linear^m :=
by { simp[linear, pow_eq, of_le_of], refine ⟨1, by simp, 1, λ x hx, by { simp, exact pow_mono hx h}⟩ }

@[simp] lemma log_le_linear : log ≤ linear :=
by { simp[linear, one_def, of_le_of], refine ⟨1, by simp, 1, by simp⟩ }

@[simp] lemma log_poly_le_linear (k : ℕ) : log^k ≤ linear :=
by { simp[log, pow_eq, linear, one_def, of_le_of],
     refine ⟨(k.pow_le_two_mul_pow_of_le_bound + 1)^k, by { simp,
     suffices : 1 ≤ (k.pow_le_two_mul_pow_of_le_bound + 1)^k, exact ne_zero.ne _,
     refine nat.one_le_pow' _ _ }, 2^k.pow_le_two_mul_pow_of_le_bound, _⟩, 
     simpa using Log_pow_le_linear k }

end linear

section exp
variables {f}

@[simp] lemma linear_le_exp : linear ≤ exp :=
by { simp[linear, exp, of_le_of], refine ⟨1, by simp, 0, _⟩, simp, sorry }

end exp

section lambda


@[simp] lemma lambda_add : O[λ x, f x + g x] = O[f] + O[g] := (of_add_of f g).symm

@[simp] lemma lambda_add_const {c : ℕ} (h : c ≠ 0) : O[λ x, f x + c] = O[f] + 1 :=
by { show O[f + λ _, c] = O[f] + 1, rw [of_add_of, const_eq_one h] }

@[simp] lemma lambda_smul {c : ℕ} (h : c ≠ 0) : O[λ x, c * f x] = O[f] := smul_eq f h

@[simp] lemma lambda_le_smul {c : ℕ} : O[λ x, c * f x] ≤ O[f] := smul_le f

@[simp] lemma lambda_smul_poly1 {c : ℕ} (h : c ≠ 0) : O[(*) c] = linear :=
by simpa[show c • id = (*) c, from funext (by simp)] using smul_eq id h

@[simp] lemma lambda_smul_le_poly1 {c : ℕ} : O[(*) c] ≤ linear :=
by simpa[show c • id = (*) c, from funext (by simp)] using smul_le id

end lambda

end bigΘ


section
open nat
variables (f : ℕ → ℕ)

lemma le_poly1_of_binary_rec (c : ℕ) (h : ∀ b n, f (bit b n) ≤ 2 * f n + c) : O[f] ≤ bigΘ.linear :=
begin
  have : f ≤ᴼ (λ n, (f 1 + c)*n),
  { have : ∀ n, n ≠ 0 → f n ≤ (f 1 + c) * n - c,
    from binary_recursion_nonzero
      (by simp[add_mul]; rw [mul_one, mul_one, tsub_eq_of_eq_add]; refl)
      (λ b n hn IH, by { 
        have : c ≤ 2 * (f 1 + c) * n - c,
          calc c = 2 * c - c
          : by rw[two_mul]; simp
             ... ≤ 2 * ((f 1 + c) * n) - c
          : tsub_le_tsub_right (by simp[hn]; refine le_mul_of_le_of_one_le (by simp) (one_le_iff_ne_zero.mpr hn)) c
             ... ≤ 2 * (f 1 + c) * n - c
          : by rw[mul_assoc],
        calc
          f (bit b n) ≤ 2 * f n + c                   : h b n
                  ... ≤ 2 * ((f 1 + c) * n - c) + c   : by simpa using IH
                  ... = 2 * (f 1 + c) * n - 2 * c + c : by simp[nat.mul_sub_left_distrib, mul_assoc]
                  ... = 2 * (f 1 + c) * n - c - c + c : by rw[two_mul c, tsub_add_eq_tsub_tsub]
                  ... = 2 * (f 1 + c) * n - c         : by rw nat.sub_add_cancel this
                  ... = (f 1 + c) * (2 * n) - c       : by rw[mul_comm 2 (f 1 + c), mul_assoc]
                  ... ≤ (f 1 + c) * bit b n - c       : tsub_le_tsub_right (mul_le_mul_left' (by simp[bit_val]) _) c }),
    refine ⟨1, by simp, 1,
      λ n hn, by simp; refine le_trans (this n (one_le_iff_ne_zero.mp hn)) (nat.sub_le _ _)⟩ },
  refine (bigΘ.of_le_of.mpr this).trans (by simp)
end


lemma le_Log_of_binary_rec (c : ℕ) (h : ∀ b n, f (bit b n) ≤ f n + c) : O[f] ≤ bigΘ.log :=
begin
  have : f ≤ᴼ (λ n, c * Log n + f 0),
  from ⟨1, by simp, 0, by { simp,
  refine nat.binary_rec (by simp)
    (λ b n IH, by { 
      by_cases C : bit b n = 0, { simp[C] },
      calc
        f (bit b n) ≤ f n + c                 : h b n
                ... ≤ c * Log n + f 0 + c     : by simpa using IH
                ... = c * (Log n + 1) + f 0   : by ring
                ... = c * Log (bit b n) + f 0 : by simp[Log_bit C] }) }⟩,
  have := bigΘ.of_le_of.mpr this,
  simp at this,
  sorry
end

end

end landau_notation