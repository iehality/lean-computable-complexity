import tactic data.vector.basic data.vector.zip algebra.big_operators.basic algebra.big_operators.norm_num
import vorspiel

open_locale big_operators

universes u v

namespace turing_machine

inductive language (Γ : Type u)
| blank : language
| start : language
| chr   : Γ → language

notation `␣` := language.blank 
notation `␤` := language.start

instance {Γ : Type u} : inhabited (language Γ) := ⟨␣⟩

class state_lang (Q : Type u) :=
(start : Q)
(halt : Q)

instance {Q R} [state_lang Q] [state_lang R] : state_lang (Q ⊕ R) := ⟨sum.inl state_lang.start, sum.inr state_lang.halt⟩

end turing_machine

namespace turing_machine
open state_lang

variables
  (Γ : Type u) -- 言語
  (Q : Type v) [state_lang Q] -- 状態
  (ι : ℕ) -- テープの数

inductive instruction
| stay  : instruction
| right : instruction
| left  : instruction

instance : inhabited instruction := ⟨instruction.stay⟩

@[simp] def instruction.apply : instruction → ℕ → ℕ
| instruction.stay  ι := ι
| instruction.right ι := ι + 1
| instruction.left  ι := ι - 1

@[simp] lemma instruction.apply_default (n) : instruction.apply default n = n := rfl

@[simp] lemma instruction.default_nth (ι : ℕ) (i) : (default : vector instruction ι).nth i = instruction.stay :=
by { unfold default, simp }

structure word :=
(c : Q)
(z : vector Γ ι)
(u : vector instruction ι)
(q : Q)
(x : vector Γ ι)

notation `⟮` c `, ` z `; ` u ` | ` q `, ` x `⟯`:80 := word.mk c z u q x

structure model :=
(state : Q) 
(tape : vector (ℕ → Γ) ι)
(head : vector ℕ ι)

notation `⟦` q `, ` T `, ` H `⟧` := model.mk q T H

structure sentence :=
(carrier : set (word Γ Q ι))
(proper' : ∀ c z u q x, ⟮c, z; u | q, x⟯ ∈ carrier → q ≠ state_lang.halt ∧ c ≠ state_lang.start)

namespace sentence
variables {Γ Q ι}
variables (σ : sentence Γ Q ι)

instance : set_like (sentence Γ Q ι) (word Γ Q ι) := ⟨sentence.carrier,by { rintros ⟨_, _⟩ ⟨_, _⟩, simp }⟩

lemma mem_def (w : word Γ Q ι) : w ∈ σ ↔ w ∈ σ.carrier := iff.rfl

lemma proper {c z u q x} : ⟮c, z; u | q, x⟯ ∈ σ → q ≠ state_lang.halt ∧ c ≠ state_lang.start := σ.proper' _ _ _ _ _

@[simp] lemma start_notin (c z u x) : ⟮c, z; u | halt, x⟯ ∉ σ := λ A, by simpa using σ.proper A

@[simp] lemma halt_notin (z u q x) : ⟮start, z; u | q, x⟯ ∉ σ := λ A, by simpa using σ.proper A 

end sentence

variables {Γ Q ι}

namespace model
variables (σ : sentence Γ Q ι)


@[ext] lemma ext : ∀ {m₁ m₂ : model Γ Q ι}
  (hs : m₁.state = m₂.state)
  (ht : m₁.tape = m₂.tape)
  (hh : m₁.head = m₂.head), m₁ = m₂
| ⟦q₁, T₁, H₁⟧ ⟦q₂, T₂, H₂⟧ hs ht hh :=
  by { simp at hs ht hh, simp[hs, ht, hh] }

def read (T : vector (ℕ → Γ) ι) (H : vector ℕ ι) : vector Γ ι := @vector.zip_with (ℕ → Γ) ℕ Γ ι (λ t h, t h) T H

@[simp] lemma read_nth (T : vector (ℕ → Γ) ι) (H : vector ℕ ι) (i) : (read T H).nth i = (T.nth i) (H.nth i) :=
by simp[read]

@[irreducible] def reduct_tape (T H) (x : vector Γ ι) : vector (ℕ → Γ) ι :=
  @vector.zip_with3 (ℕ → Γ) ℕ Γ (ℕ → Γ) ι (λ t h x, λ n, if n = h then x else t n) T H x

@[irreducible] def reduct_head (H) (u : vector instruction ι) : vector ℕ ι :=
  vector.zip_with instruction.apply u H

@[simp] lemma reduct_tape_nth (T H) (x : vector Γ ι) (i) :
  (reduct_tape T H x).nth i = (λ n, if n = H.nth i then x.nth i else T.nth i n) :=
by simp[reduct_tape]

@[simp] lemma reduct_head_nth  (H) (u : vector instruction ι) (i) :
  (reduct_head H u).nth i = (u.nth i).apply (H.nth i) :=
by simp[reduct_head]

inductive reduction : model Γ Q ι → model Γ Q ι → Prop
| intro : ∀ (q : Q) (T : vector (ℕ → Γ) ι) (H : vector ℕ ι) (c : Q) (z : vector Γ ι) (u : vector instruction ι),
    ⟮c, z; u | q, read T H⟯ ∈ σ → reduction ⟦q, T, H⟧ ⟦c, reduct_tape T H z, reduct_head H u⟧

notation m₀ ` ⟶¹[`:60  σ `] ` :0 m₁ := reduction σ m₀ m₁ 

def is_halt (m : model Γ Q ι) : Prop := ∀ m', ¬m ⟶¹[σ] m'

def time_reductions : ℕ → model Γ Q ι → model Γ Q ι → Prop := relation.power (reduction σ) 

notation m₀ ` ⟶^(`:80 s `)[`  σ `] ` :80 m₁ := time_reductions σ s m₀ m₁ 

def time_bounded_reductions : ℕ → model Γ Q ι → model Γ Q ι → Prop := relation.power_le (reduction σ)

notation m₀ ` ⟶^(≤ `:80 s `)[`  σ `] ` :80 m₁ := time_bounded_reductions σ s m₀ m₁ 

def time_bounded_reductions_halt (s : ℕ) (m m' : model Γ Q ι) : Prop := is_halt σ m' ∧ m ⟶^(≤ s)[σ] m'

notation m₀ ` ⟶^(≤ `:80 s `)[`  σ `]↓ ` :80 m₁ := time_bounded_reductions_halt σ s m₀ m₁ 

def is_halt_in_step (s : ℕ) (m : model Γ Q ι) : Prop := ∀ (m') (s' > s), ¬ m ⟶^(s')[σ] m' 

def reductions : model Γ Q ι → model Γ Q ι → Prop := relation.trans_gen (reduction σ) 

notation m₀ ` ⟶*[`:80  σ `] ` :0 m₁ := reductions σ m₀ m₁ 

end model

variables {Γ Q ι} 
def sentence.deterministic (σ : sentence Γ Q ι) : Prop :=
∀ ⦃q x c₁ c₂ z₁ z₂ u₁ u₂⦄, ⟮c₁, z₁; u₁ | q, x⟯ ∈ σ → ⟮c₂, z₂; u₂ | q, x⟯ ∈ σ → c₁ = c₂ ∧ z₁ = z₂ ∧ u₁ = u₂

namespace sentence

inductive of_fun_aux (δ : Q × vector Γ ι → option (Q × vector Γ ι × vector instruction ι)) : set (word Γ Q ι)
| intro : ∀ {q x c z u}, δ ⟨q, x⟩ = some ⟨c, z, u⟩ → of_fun_aux ⟮c, z; u | q, x⟯

def of_fun (δ : Q × vector Γ ι → option (Q × vector Γ ι × vector instruction ι))
  (H : ∀ {q x c z u}, δ ⟨q, x⟩ = some ⟨c, z, u⟩ → q ≠ halt ∧ c ≠ start) : sentence Γ Q ι :=
{ carrier := of_fun_aux δ,
  proper' := λ c z u q x, by { rintro ⟨_, _, _, _, _, h⟩, exact H h } }

namespace of_fun
variables (δ : Q × vector Γ ι → option (Q × vector Γ ι × vector instruction ι))

lemma carrier_eq {H} : (of_fun δ H).carrier = of_fun_aux δ := rfl

@[simp] lemma mem_iff {H} {c z u q x} : ⟮c, z; u | q, x⟯ ∈ of_fun δ H ↔ δ ⟨q, x⟩ = some ⟨c, z, u⟩ :=
by { simp[sentence.mem_def], split,
  { rintros ⟨_, _, _, _, _, h⟩, exact h }, { intros h, exact of_fun_aux.intro h } }

lemma of_fn.deterministic {H} : deterministic (of_fun δ H) :=
λ _ _ _ _ _ _ _ _, by { simp, intros h₁ h₂, simpa[h₁] using h₂ }

end of_fun

namespace deterministic
variables {σ : sentence Γ Q ι} {m₁ m₂ : model Γ Q ι}

lemma reduction (d : deterministic σ) : relation.deterministic (model.reduction σ) := λ m m₁ m₂ h₁ h₂,
begin
  rcases h₁ with ⟨q₁, T₁, H₁, c₁, z₁, u₁, mem₁⟩,
  rcases h₂ with ⟨q₂, T₂, H₂, c₂, z₂, u₂, mem₂⟩,
  rcases d mem₁ mem₂ with ⟨rfl, rfl, rfl⟩,
  refl
end

lemma time_reductions (d : deterministic σ) {n} : relation.deterministic (model.time_reductions σ n) :=
relation.power.deterministic (reduction @d)

end deterministic

end sentence

section TM

def tape_of (x : list Γ) : ℕ → language Γ
| 0       := ␤
| (n + 1) := if h : n < x.length then language.chr (x.nth_le n h) else ␣

-- ␤ x₁ x₂ ... xₙ ␣ ␣ ␣ ...

@[simp] lemma tape_of_of_zero {x : list Γ} : tape_of x 0 = ␤ := by simp[tape_of]

@[simp] lemma tape_of_of_lt {n} {x : list Γ} (gt : n > 0) (le : n ≤ x.length) :
  tape_of x n = language.chr (x.nth_le (n - 1) (by { cases n, { simp at gt, contradiction }, { simpa using nat.succ_le_iff.mp le} })) :=
by { cases n, { simp at gt, contradiction },
     { simp[tape_of, show n < x.length, from nat.succ_le_iff.mp le] } }

@[simp] lemma tape_of_list_of_ge {n} {x : list Γ} (h : n ≥ x.length + 1) : tape_of x n = ␣ :=
by { cases n, { simp at h, contradiction },
     { simp[tape_of], have : n ≥ x.length, exact nat.succ_le_succ_iff.mp h, exact nat.le_lt_antisymm this } }

structure time_bounded_computable_by_NDTM (f : list Γ → list Γ) (T : ℕ → ℕ) :=
(Q : Type*)
(Q_fin : finite Q)
(Q_state : state_lang Q)
(σ : sentence (language Γ) Q ι.succ.succ)
(reduction : ∀ (X : list Γ), 
  model.is_halt_in_step σ (T X.length) (⟦start, tape_of X ::ᵥ default, default⟧) ∧
  ⟦start, tape_of X ::ᵥ default, default⟧ ⟶^(≤ T X.length)[σ]↓ ⟦halt, vector.concat default (tape_of (f X)), default⟧)


structure time_bounded_computable_by_TM (f : list Γ → list Γ) (T : ℕ → ℕ) :=
(Q : Type*)
(Q_fin : finite Q)
(Q_state : state_lang Q)
(σ : sentence (language Γ) Q ι.succ.succ)
(deterministic : σ.deterministic)
(reduction : ∀ (X : list Γ), 
  ⟦start, tape_of X ::ᵥ default, default⟧ ⟶^(≤ T X.length)[σ]↓ ⟦halt, vector.concat default (tape_of (f X)), default⟧)

end TM

namespace sentence
open model sentence.deterministic relation
variables {R : Type*} [state_lang R] (f : Q → R) {σ : sentence Γ Q ι}

@[simp] def word.map_q : word Γ Q ι → word Γ R ι
| ⟮c, z; u | q, x⟯ := ⟮f c, z; u | f q, x⟯

@[simp] def map_q (σ : sentence Γ Q ι) (f : Q → R) (H : ∀ c z u q x, ⟮c, z; u | q, x⟯ ∈ σ → f q ≠ halt ∧ f c ≠ start) :
  sentence Γ R ι :=
{ carrier := word.map_q f '' σ,
  proper' := by { rintros c z u q x ⟨⟨c', z', u', q', x'⟩, h, eqn⟩,
                  simp at eqn, rcases eqn with ⟨rfl, rfl, rfl, rfl, rfl⟩, exact H _ _ _ _ _ h } }

end sentence

namespace model
open sentence sentence.deterministic relation
variables {m₁ m₂ m₃ : model Γ Q ι} {σ : sentence Γ Q ι}

@[simp] lemma reduct_tape_read {T : vector (ℕ → Γ) ι} {H : vector ℕ ι} : reduct_tape T H (read T H) = T :=
by { ext, simp, rintros rfl, refl }

@[simp] lemma reduct_head_default {H : vector ℕ ι} : reduct_head H default = H :=
by { ext, simp, }

lemma reduction.iff {q₁ q₂ : Q} {T₁ T₂ : vector (ℕ → Γ) ι} {H₁ H₂ : vector ℕ ι}  :
  (⟦q₁, T₁, H₁⟧ ⟶¹[σ] ⟦q₂, T₂, H₂⟧) ↔
  (∃ (z : vector Γ ι) (u : vector instruction ι), ⟮q₂, z; u | q₁, read T₁ H₁⟯ ∈ σ ∧ T₂ = reduct_tape T₁ H₁ z ∧ H₂ = reduct_head H₁ u) :=
⟨by { rintros ⟨_, _, _, _, z, u, mem⟩, refine ⟨z, u, mem, rfl, rfl⟩ },
 by { rintros ⟨z, u, mem, rfl, rfl⟩, refine ⟨_, _, _, _, z, u, mem⟩ }⟩

@[simp] lemma time_bounded_reductions.refl {s} : m₁ ⟶^(≤ s)[σ] m₁ := power_le.refl

@[simp] lemma time_reductions.refl : m₁ ⟶^(0)[σ] m₁ := power.zero _

lemma time_bounded_reductions.of_le {s₁ s₂} (le : s₁ ≤ s₂) (h : m₁ ⟶^(≤ s₁)[σ] m₂) :
  m₁ ⟶^(≤ s₂)[σ] m₂ := power_le.of_le le h

lemma time_reductions.add {s₁ s₂} (h₁ : m₁ ⟶^(s₁)[σ] m₂) (h₂ : m₂ ⟶^(s₂)[σ] m₃) :
  m₁ ⟶^(s₁ + s₂)[σ] m₃ := power.add h₁ h₂

lemma time_bounded_reductions.add {s₁ s₂} (h₁ : m₁ ⟶^(≤ s₁)[σ] m₂) (h₂ : m₂ ⟶^(≤ s₂)[σ] m₃) :
  m₁ ⟶^(≤ s₁ + s₂)[σ] m₃ := power_le.add h₁ h₂

lemma time_bounded_reductions.sum {m : ℕ → model Γ Q ι} {s : ℕ → ℕ}
  (h : ∀ k, m k ⟶^(≤ s k)[σ] m (k + 1)) (k : ℕ) : (m 0) ⟶^(≤ ∑ i in finset.range k, s i)[σ] (m k) :=
by { induction k with k IH, { simp }, { simpa[finset.sum_range_succ] using IH.add (h k) } }

lemma reduction.of_ss (r : m₁ ⟶¹[σ] m₂) {τ : sentence Γ Q ι} (ss : σ ≤ τ) : m₁ ⟶¹[τ] m₂ :=
by { rcases r with ⟨q, T, H, c, z, u, mem⟩, refine ⟨_, _, _, _, _, _, ss mem⟩ }

lemma time_reductions.of_ss {n} (r : m₁ ⟶^(n)[σ] m₂) {τ : sentence Γ Q ι} (ss : σ ≤ τ) : m₁ ⟶^(n)[τ] m₂ :=
by { induction n with n IH generalizing m₂, { rcases r, simp },
     { rcases r with (_ | ⟨_, _, m₁₁, _, r₁_₁₁, r₁₁_₂⟩), exact (IH r₁_₁₁).succ (r₁₁_₂.of_ss ss) } }

lemma time_bounded_reductions.of_ss {k} (r : m₁ ⟶^(≤ k)[σ] m₂) {τ : sentence Γ Q ι} (ss : σ ≤ τ) : m₁ ⟶^(≤ k)[τ] m₂ :=
by { rcases r with ⟨n, le, r⟩, refine ⟨n, le, time_reductions.of_ss r ss⟩ }

section
variables {R : Type*} [state_lang R] (f : Q → R)

@[simp] def map_q : model Γ Q ι → model Γ R ι
| ⟦q, T, H⟧ := ⟦f q, T, H⟧

instance [has_coe Q R] : has_coe (model Γ Q ι) (model Γ R ι) := ⟨λ m, m.map_q coe⟩ 

variables (m m' : model Γ Q ι) {f}

@[simp] lemma map_q_tape (m : model Γ Q ι) : (m.map_q f).tape = m.tape := by cases m; simp

@[simp] lemma map_q_head (m : model Γ Q ι) : (m.map_q f).head = m.head := by cases m; simp

@[simp] lemma map_q_state (m : model Γ Q ι) : (m.map_q f).state = f m.state := by cases m; simp

variables (f)

lemma reduction.map_q {H} (h : m₁ ⟶¹[σ] m₂) : m₁.map_q f ⟶¹[σ.map_q f H] m₂.map_q f :=
by { rcases h with ⟨q, T, H, c, z, u, mem⟩, simp, refine ⟨_, _, _, _, _, _, _⟩, simp[sentence.mem_def], refine ⟨_, mem, by simp⟩ }

lemma time_reductions.map_q {H} {n} (h : m₁ ⟶^(n)[σ] m₂) : m₁.map_q f ⟶^(n)[σ.map_q f H] m₂.map_q f :=
by { induction n with n IH generalizing m₂, { rcases h, simp },
     { rcases h with (_ | ⟨_, _, m₁₁, _, r₁_₁₁, r₁₁_₂⟩), refine (IH r₁_₁₁).succ (r₁₁_₂.map_q f) } }

lemma time_bounded_reduction.map_q {H} {k} (h : m₁ ⟶^(≤ k)[σ] m₂) : m₁.map_q f ⟶^(≤ k)[σ.map_q f H] m₂.map_q f :=
by { rcases h with ⟨n, le, r⟩, refine ⟨n, le, time_reductions.map_q f r⟩ }

variables {f}

lemma deterministic.map_q {H} (inj : function.injective f) (d : deterministic σ) : deterministic (σ.map_q f H) :=
begin
  rintros r x d₁ d₂ z₁ z₂ u₁ u₂ h₁ h₂,
  rcases h₁ with ⟨⟨c₁, z₁', u₁', q₁, x₁'⟩, mem₁, eq₁⟩,
  have : f c₁ = d₁ ∧ z₁ = z₁' ∧ u₁ = u₁' ∧ f q₁ = r ∧ x = x₁', { simp at eq₁, simp[eq₁] },
  rcases this with ⟨rfl, rfl, rfl, rfl, rfl⟩,
  rcases h₂ with ⟨⟨c₂, z₂', u₂', q₂, x₂'⟩, mem₂, eq₂⟩,
  have : f c₂ = d₂ ∧ z₂ = z₂' ∧ u₂ = u₂' ∧ f q₁ = f q₂ ∧ x = x₂', { simp at eq₂, simp[eq₂] },
  rcases this with ⟨rfl, rfl, rfl, eqn, rfl⟩,
  have : q₁ = q₂, from (inj eqn), rcases this with rfl,
  simp [d mem₁ mem₂]
end

end

variables {R : Type v} [state_lang R]

namespace sentence
variables {Q R} (q c : Q) (h : q ≠ halt ∧ c ≠ start) 

inductive fix_q_aux : word Γ Q ι → Prop
| intro : ∀ (z : vector Γ ι), fix_q_aux ⟮c, z; default | q, z⟯

def fix_q (q c : Q) (h : q ≠ halt ∧ c ≠ start) : sentence Γ Q ι :=
{ carrier := fix_q_aux q c,
  proper' := λ c' z u q' x, by { rintros ⟨⟩, exact h } } 

@[simp] lemma fix_q_mem (z : vector Γ ι) :
  ⟮c, z; default | q, z⟯ ∈ (fix_q q c h : sentence Γ Q ι) :=
fix_q_aux.intro _

lemma fix_q.deterministic : deterministic (fix_q q c h : sentence Γ Q ι) :=
by { rintros q' x c₁ c₂ z₁ z₂ u₁ u₂ h₁ h₂, rcases h₁, rcases h₂, simp }

@[simp] lemma fix_q_reduction (T : vector (ℕ → Γ) ι) (H : vector ℕ ι) : ⟦q, T, H⟧ ⟶¹[fix_q q c h] ⟦c, T, H⟧ :=
reduction.iff.mpr ⟨read T H, default, by simp, by simp⟩

instance : has_union (sentence Γ Q ι) := ⟨λ σ τ,
{ carrier := σ ∪ τ,
  proper' := by { rintros c z u q x (h | h), { exact σ.proper h }, { exact τ.proper h } } }⟩

def deterministic.union {σ τ : sentence Γ Q ι} (d₁ : deterministic σ) (d₂ : deterministic τ) 
  (h : ∀ {q x c₁ c₂ z₁ z₂ u₁ u₂}, ⟮c₁, z₁; u₁ | q, x⟯ ∈ σ → ⟮c₂, z₂; u₂ | q, x⟯ ∈ τ → c₁ = c₂ ∧ z₁ = z₂ ∧ u₁ = u₂) : deterministic (σ ∪ τ) :=
begin
  rintros q x c₁ c₂ z₁ z₂ u₁ u₂ (h₁ | h₁) (h₂ | h₂),
  { exact d₁ h₁ h₂ }, { exact h h₁ h₂ }, { simp [h h₂ h₁] }, { exact d₂ h₁ h₂ }
end

def dsum_suml (σ : sentence Γ Q ι) : sentence Γ (Q ⊕ R) ι := σ.map_q sum.inl (by { intros _ _ _ _ _ h, unfold halt start, simp[σ.proper h] })

def dsum_sumr (τ : sentence Γ R ι) : sentence Γ (Q ⊕ R) ι := τ.map_q sum.inr (by { intros _ _ _ _ _ h, unfold halt start, simp[τ.proper h] })

def dsum (σ : sentence Γ Q ι) (τ : sentence Γ R ι) : sentence Γ (Q ⊕ R) ι :=
(σ.map_q sum.inl (by { intros _ _ _ _ _ h, unfold halt start, simp[σ.proper h] })) ∪
(τ.map_q sum.inr (by { intros _ _ _ _ _ h, unfold halt start, simp[τ.proper h] })) ∪
(fix_q (sum.inl (halt : Q)) (sum.inr (start : R)) (by unfold halt start; simp))

infix ` ⨁ `:80 := dsum

lemma dsum.deterministic {σ : sentence Γ Q ι} {τ : sentence Γ R ι}
  (d₁ : deterministic σ) (d₂ : deterministic τ) : deterministic (σ ⨁ τ) :=
begin
  refine (deterministic.union (deterministic.union (deterministic.map_q sum.inl_injective d₁) (deterministic.map_q sum.inr_injective d₂) _)
           (fix_q.deterministic _ _ _) _),
  { rintros (q | r) _ _ _ _ _ _ _ ⟨⟨c₁, z₁, u₁, q, x⟩, mem₁, eqn₁⟩ ⟨⟨c₂, z₂, u₂, q', x'⟩, mem₂, eqn₂⟩,
    { simp at eqn₂, contradiction },
    { simp at eqn₁, contradiction } },
  { rintros _ _ _ _ _ _ _ _ (⟨⟨c, z, u, q, x⟩, mem, eqn⟩ | ⟨⟨c, z, u, q, x⟩, mem, eqn⟩) ⟨⟩,
    { simp at eqn, rcases eqn with ⟨rfl, rfl, rfl, rfl, rfl⟩, exfalso, simpa using mem },
    { simp at eqn, contradiction } }
end

end sentence

lemma time_reductions.dsum_aux  {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {n₁ n₂} {q r T₁ T₂ T₃ H₁ H₂ H₃}
  (h₁ : ⟦q, T₁, H₁⟧ ⟶^(n₁)[σ] ⟦halt, T₂, H₂⟧) (h₂ : ⟦start, T₂, H₂⟧ ⟶^(n₂)[τ] ⟦r, T₃, H₃⟧) :
  ⟦sum.inl q, T₁, H₁⟧ ⟶^(n₁ + n₂ + 1)[σ ⨁ τ] ⟦sum.inr r, T₃, H₃⟧ :=
begin
  have h₁ : ⟦sum.inl q, T₁, H₁⟧ ⟶^(n₁)[σ ⨁ τ] ⟦sum.inl halt, T₂, H₂⟧,
  from time_reductions.of_ss (time_reductions.map_q sum.inl h₁)
    (by { simp[(⨁)], refine set.subset_union_of_subset_left (set.subset_union_left _ _) _,
          { intros _ _ _ _ _ h, unfold halt start, simp[σ.proper h] } }),
  have h : ⟦sum.inl halt, T₂, H₂⟧ ⟶¹[σ ⨁ τ] ⟦sum.inr start, T₂, H₂⟧,
  from reduction.of_ss (sentence.fix_q_reduction _ _ _ _ _)
    (by { simp[(⨁)], refine set.subset_union_right _ _, { unfold halt start; simp } }),
  have h₂ : ⟦sum.inr start, T₂, H₂⟧ ⟶^(n₂)[σ ⨁ τ] ⟦sum.inr r, T₃, H₃⟧,
  from time_reductions.of_ss (time_reductions.map_q sum.inr h₂)
    (by { simp[(⨁)], refine set.subset_union_of_subset_left (set.subset_union_right _ _) _,
          { intros _ _ _ _ _ h, unfold halt start, simp[τ.proper h] } }),
  simpa[show n₁.succ + n₂ = n₁ + n₂ + 1, by omega] using (h₁.succ h).add h₂
end

lemma time_reductions.dsum  {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {n₁ n₂ : ℕ} {T₁ T₂ T₃ H₁ H₂ H₃}
  (h₁ : ⟦start, T₁, H₁⟧ ⟶^(n₁)[σ] ⟦halt, T₂, H₂⟧) (h₂ : ⟦start, T₂, H₂⟧ ⟶^(n₂)[τ] ⟦halt, T₃, H₃⟧) :
  ⟦start,  T₁, H₁⟧ ⟶^(n₁ + n₂ + 1)[σ ⨁ τ] ⟦halt, T₃, H₃⟧ :=
time_reductions.dsum_aux h₁ h₂

lemma time_bounded_reductions.dsum  {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {k₁ k₂ : ℕ} {T₁ T₂ T₃ H₁ H₂ H₃}
  (h₁ : ⟦start, T₁, H₁⟧ ⟶^(≤ k₁)[σ] ⟦halt, T₂, H₂⟧) (h₂ : ⟦start, T₂, H₂⟧ ⟶^(≤ k₂)[τ] ⟦halt, T₃, H₃⟧) :
  ⟦start,  T₁, H₁⟧ ⟶^(≤ k₁ + k₂ + 1)[σ ⨁ τ] ⟦halt, T₃, H₃⟧ :=
by { rcases h₁ with ⟨n₁, le₁, h₁⟩, rcases h₂ with ⟨n₂, le₂, h₂⟩, refine ⟨n₁ + n₂ + 1, by linarith, time_reductions.dsum h₁ h₂⟩ }


end model
/--/
namespace sentence

namespace delete

inductive srh
| start
| run
| halt

instance : state_lang srh := ⟨srh.start, srh.halt⟩

inductive main (i : fin ι) : sentence (language Γ) srh ι
| start : ∀ v, main (⟨start, v⟩ ▷ ⟨srh.run, ⟩)
| halt : main (⟨srh.run, vector.repeat ␤ ι⟩ ▷ ⟨halt, vector.repeat (␤, instruction.stay) ι⟩)

end delete

end sentence

end turing_machine