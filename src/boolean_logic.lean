import vorspiel


inductive bexpression : ℕ → Type
| atom {n} : fin n → bexpression n
| and  {n} : bexpression n → bexpression n → bexpression n
| or   {n} : bexpression n → bexpression n → bexpression n
| not  {n} : bexpression n → bexpression n

inductive literal (α : Type*)
| id  : α → literal
| not : α → literal

namespace literal

instance (α : Type*) [inhabited α] : inhabited (literal α) := ⟨id default⟩

@[simp] def val {n} (v : vector bool n) : literal (fin n) → bool
| (id i)  := v.nth i
| (not i) := bnot (v.nth i)

instance {α : Type*} [d : decidable_eq α] : decidable_eq (literal α)
| (id a)  (id b)  := by simp; exact d a b
| (id a)  (not b) := is_false (λ h, by simpa using h)
| (not a) (id b)  := is_false (λ h, by simpa using h)
| (not a) (not b) := by simp; exact d a b

section

@[simp] def pref {α : Type*} : bool → α → literal α
| tt a := id a 
| ff a := not a 

end

end literal

def CNF.clause (m n) := {s : finset (literal (fin n)) // s.card ≤ m}

-- conjunctive normal form
def CNF (m n) := finset (CNF.clause m n)

abbreviation CNF.clause3 := CNF.clause 3

abbreviation CNF3 := CNF 3

namespace CNF
open literal

section
variables {m n : ℕ} (v : vector bool n)

namespace clause

instance : inhabited (clause m n) := ⟨⟨∅, by simp⟩⟩

def val (c : clause m n) (v) : bool := c.val.sup (literal.val v)

def disj (l : fin m → literal (fin n)) : clause m n := ⟨finset.of_fn l, by simp⟩

notation `⋁` binders `, ` r:(scoped l, disj l) := r

variables (l : fin m → literal (fin n))

@[simp] lemma disj_val_ff : (⋁ i, l i).val v = ff ↔ ∀ i, (l i).val v = ff :=
begin 
  simp[val, disj],   
  suffices : (∀ s ∈ finset.of_fn l, literal.val v s = ⊥) ↔ (∀ i, literal.val v (l i) = ff),
  { have e := finset.sup_eq_bot_iff (literal.val v) (finset.of_fn l),
    exact e.trans this },
  split,
  { exact λ h i, h (l i) (by simp) },
  { intros h s hs,
    have : ∃ i, l i = s, from (finset.mem_of_fn_iff l).mp hs,
    rcases this with ⟨i, rfl⟩,
    exact h i }
end

@[simp] lemma disj_val_tt : (⋁ i, l i).val v = tt ↔ ∃ i, (l i).val v = tt :=
by simpa[-disj_val_ff] using iff.not (disj_val_ff v l)

end clause
open clause

instance : inhabited (CNF m n) := ⟨(∅ : finset _)⟩

def val (φ : CNF m n) (v) : bool := φ.inf (λ c, c.val v)

abbreviation size (φ : CNF m n) : ℕ := φ.card

section conjunction
variables {ι : Type*} [fintype ι] (c : ι → clause m n)

def conj (c : ι → clause m n) : CNF m n := finset.cod c

notation `⋀` binders `, ` r:(scoped l, conj l) := r

lemma conj_size : (⋀ i, c i).size ≤ fintype.card ι := finset.cod_card c

@[simp] lemma conj_val_tt : (⋀ i, c i).val v = tt ↔ ∀ i, (c i).val v = tt :=
begin
  simp[val, conj, finset.cod],
  simpa using finset.inf_eq_top_iff (λ c, clause.val c v) (finset.image c finset.univ)
end

@[simp] lemma conj_val_ff : (⋀ i, c i).val v = ff ↔ ∃ i, (c i).val v = ff :=
by simpa[-conj_val_tt] using iff.not (conj_val_tt v c)

end conjunction

end

section
variables {n : ℕ} (f : vector bool n → bool)

def to_CNF : CNF n n := ⋀ (v : {v : vector bool n // f v = ff}), ⋁ i, pref (!v.val.nth i) i

@[simp] lemma size_to_CNF_le_pow : (to_CNF f).size ≤ 2^n :=
begin
  have le₁ : (to_CNF f).size ≤ fintype.card {v // f v = ff}, from conj_size _, 
  have le₂ : fintype.card {v // f v = ff} ≤ 2^n, by simpa using @fintype.card_subtype_le (vector bool n) _ _ _,
  exact le₁.trans le₂
end

@[simp] lemma val_to_CNF (v) : (to_CNF f).val v = f v :=
begin
  cases C : f v; simp[to_CNF],
  { refine ⟨v, C, _⟩,
    intros i,
    cases Ci : v.nth i; simp[Ci] },
  { intros w hw, 
    have : v ≠ w, { rintros rfl, simp[hw] at C, contradiction },
    have : ∃ i, v.nth i ≠ w.nth i, by simpa using mt vector.ext this,
    rcases this with ⟨i, ne⟩,
    refine ⟨i, _⟩, 
    cases Ci : w.nth i,
    { have : v.nth i = tt, from bool.eq_tt_of_ne_ff (by { rintros A, simp[Ci, A] at ne, contradiction }),
      simp[this] },
    { have : v.nth i = ff, from bool.eq_ff_of_ne_tt (by { rintros A, simp[Ci, A] at ne, contradiction }),
      simp[this] } }
end

end

end CNF