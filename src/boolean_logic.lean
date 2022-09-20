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

def pref {α : Type*} : bool → α → literal α
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

def disj (l : fin m → literal (fin n)) : clause m n := ⟨finset.of_fn l, by simp⟩

notation `⋁` binders `, ` r:(scoped l, disj l) := r

def val (c : clause m n) : bool := c.val.sup (literal.val v)

end clause
open clause

instance : inhabited (CNF m n) := ⟨(∅ : finset _)⟩

def conj {k} (l : fin k → clause m n) : CNF m n := finset.of_fn l

notation `⋀` binders `, ` r:(scoped l, conj l) := r

def val (φ : CNF m n) : bool := φ.inf (clause.val v)

def size (φ : CNF m n) : ℕ := φ.card

end

section universality
variables {m n : ℕ} 

def equal.clause (v : vector bool n) : clause n n := ⋁ i, pref (v.nth i) i


end universality

end CNF