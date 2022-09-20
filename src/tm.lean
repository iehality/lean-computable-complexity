import tactic data.vector.basic data.vector.zip algebra.big_operators.basic algebra.big_operators.norm_num
 vorspiel lencodable

open_locale big_operators

universes u v

namespace turing_machine

inductive language (Γ : Type u)
| blank : language
| start : language
| chr   : Γ → language

notation `␣` := language.blank 
notation `␤` := language.start

namespace language
variables {Γ : Type u}

instance : inhabited (language Γ) := ⟨␣⟩

def language_equiv_option_sum_bool : language Γ ≃ bool ⊕ Γ :=
{ to_fun := λ l, match l with | ␣ := sum.inl ff | ␤ := sum.inl tt | chr x := sum.inr x end,
  inv_fun := λ l, match l with | (sum.inl ff) := ␣ | (sum.inl tt) := ␤ | sum.inr x := chr x end,
  left_inv := λ l, by rcases l; simp; refl,
  right_inv := λ l, by { rcases l; simp, { rcases l; refl }, refl } }

instance [fintype Γ] : fintype (language Γ) := fintype.of_equiv (bool ⊕ Γ) language_equiv_option_sum_bool.symm

end language

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

namespace instruction

instance : inhabited instruction := ⟨stay⟩

@[simp] def apply : instruction → ℕ → ℕ
| stay  ι := ι
| right ι := ι + 1
| left  ι := ι - 1

@[simp] lemma apply_default (n) : apply default n = n := rfl

@[simp] lemma default_nth (ι : ℕ) (i) : (default : vector instruction ι).nth i = stay :=
by { unfold default, simp }

def equiv_unit_sums : instruction ≃ unit ⊕ unit ⊕ unit :=
{ to_fun := λ i, match i with | stay := sum.inl () | right := sum.inr (sum.inl ()) | left := sum.inr (sum.inr ()) end,
  inv_fun := λ i, match i with | sum.inl () := stay | sum.inr (sum.inl ()) := right | sum.inr (sum.inr ()) := left end,
  left_inv := λ i, by rcases i; refl,
  right_inv := λ i, by { rcases i; simp, rcases i, refl, rcases i; rcases i; refl } }

instance : fintype instruction := fintype.of_equiv (unit ⊕ unit ⊕ unit) equiv_unit_sums.symm

@[simp] lemma card : fintype.card instruction = 3 := by simpa using fintype.card_congr equiv_unit_sums

variables {ι}

def Stay : vector instruction ι := vector.repeat stay ι

@[simp] lemma Stay_nth (i : fin ι) : Stay.nth i = stay := by simp[Stay]

def Right : vector instruction ι := vector.repeat right ι

@[simp] lemma Right_nth (i : fin ι) : Right.nth i = right := by simp[Right]

def Left : vector instruction ι := vector.repeat left ι

@[simp] lemma Left_nth (i : fin ι) : Left.nth i = left := by simp[Left]

end instruction

structure word :=
(c : Q)
(z : vector Γ ι)
(u : vector instruction ι)
(q : Q)
(x : vector Γ ι)

notation `⟮` c `, ` z `; ` u ` | ` q `, ` x `⟯`:80 := word.mk c z u q x

namespace word

def equiv_prod : word Γ Q ι ≃ Q × vector Γ ι × vector instruction ι × Q × vector Γ ι :=
{ to_fun := λ w, match w with ⟮c, z; u | q, x⟯ := (c, z, u, q, x) end,
  inv_fun := λ w, match w with (c, z, u, q, x) := ⟮c, z; u | q, x⟯ end,
  left_inv := λ w, by rcases w; refl,
  right_inv := λ w, by rcases w with ⟨_, w⟩; rcases w with ⟨_, w⟩; rcases w with ⟨_, w⟩; rcases w with ⟨_, w⟩; refl }

open fintype

instance [fintype Γ] [fintype Q] : fintype (word Γ Q ι) :=
fintype.of_equiv (Q × vector Γ ι × vector instruction ι × Q × vector Γ ι) (equiv_prod _ _ _).symm

lemma card [fintype Γ] [fintype Q] : card (word Γ Q ι) = card Q^2 * (3 * card Γ^2)^ι :=
calc card (word Γ Q ι) = card Q * card Γ^ι * 3^ι * card Q * card Γ^ι
  : by simpa[mul_assoc] using fintype.card_congr (equiv_prod Γ Q ι)
                   ... = card Q * card Q * 3^ι * card Γ^ι * card Γ^ι
  : by ring
                   ... = card Q^2 * (3 * card Γ^2)^ι
  : by simp[pow_two, mul_pow]; ring

end word

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

instance : set_like (sentence Γ Q ι) (word Γ Q ι) := ⟨sentence.carrier, λ ⟨_, _⟩ ⟨_, _⟩, by simp⟩

lemma mem_def (w : word Γ Q ι) : w ∈ σ ↔ w ∈ σ.carrier := iff.rfl

lemma proper {c z u q x} : ⟮c, z; u | q, x⟯ ∈ σ → q ≠ state_lang.halt ∧ c ≠ state_lang.start := σ.proper' _ _ _ _ _

@[simp] lemma start_notin (c z u x) : ⟮c, z; u | halt, x⟯ ∉ σ := λ A, by simpa using σ.proper A

@[simp] lemma halt_notin (z u q x) : ⟮start, z; u | q, x⟯ ∉ σ := λ A, by simpa using σ.proper A 

lemma carrier_finite [fintype Γ] [fintype Q] : σ.carrier.finite := set.to_finite _

noncomputable instance [fintype Γ] [fintype Q] : fintype (sentence Γ Q ι) := fintype.of_injective carrier (λ ⟨_, _⟩ ⟨_, _⟩, by simp)

def is_halt (q : Q) : Prop := ∀ ⦃c z u x⦄, ⟮c, z; u | q, x⟯ ∉ σ

def is_start (c : Q) : Prop := ∀ ⦃z u x q⦄, ⟮c, z; u | q, x⟯ ∉ σ

lemma coe_carrier : (σ : set (word Γ Q ι)) = σ.carrier := by refl

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

inductive of_fun_aux (δ : Q → vector Γ ι → option (Q × vector Γ ι × vector instruction ι)) : set (word Γ Q ι)
| intro : ∀ {q x c z u}, δ q x = some ⟨c, z, u⟩ → of_fun_aux ⟮c, z; u | q, x⟯

def of_fun (δ : Q → vector Γ ι → option (Q × vector Γ ι × vector instruction ι))
  (H : ∀ {q x c z u}, δ q x = some ⟨c, z, u⟩ → q ≠ halt ∧ c ≠ start) : sentence Γ Q ι :=
{ carrier := of_fun_aux δ,
  proper' := λ c z u q x, by { rintro ⟨_, _, _, _, _, h⟩, exact H h } }

namespace of_fun
variables (δ : Q → vector Γ ι → option (Q × vector Γ ι × vector instruction ι))

lemma carrier_eq {H} : (of_fun δ H).carrier = of_fun_aux δ := rfl

@[simp] lemma mem_iff {H} {c z u q x} : ⟮c, z; u | q, x⟯ ∈ of_fun δ H ↔ δ q x = some ⟨c, z, u⟩ :=
by { simp[sentence.mem_def], split,
  { rintros ⟨_, _, _, _, _, h⟩, exact h }, { intros h, exact of_fun_aux.intro h } }

lemma none_is_halt {q H} : (of_fun δ H).is_halt q ↔ ∀ x, δ q x = none :=
by { simp [is_halt, mem_iff, option.eq_none_iff_forall_not_mem], split,
  { rintros h x c ⟨z, u⟩ eqn, exact h eqn }, { rintros h c z u x, exact h x c (z, u) } }

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

structure fun_time_bounded_computable_by_NDTM (f : vector (list Γ) ι → vector (list Γ) ι) (T : ℕ → ℕ) :=
(Q : Type*)
(Q_fin : finite Q)
(Q_state : state_lang Q)
(σ : sentence (language Γ) Q ι)
(reduction : ∀ (X : vector (list Γ) ι), 
  model.is_halt_in_step σ (T X.length) (⟦start, X.map tape_of, default⟧) ∧
  ⟦start, X.map tape_of, default⟧ ⟶^(≤ T X.length)[σ]↓ ⟦halt, (f X).map tape_of, default⟧)

structure fun_time_bounded_computable_by_TM (f : vector (list Γ) ι → vector (list Γ) ι) (T : ℕ → ℕ)
  extends fun_time_bounded_computable_by_NDTM f T :=
(deterministic : σ.deterministic)

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

@[simp] lemma reduct_head_Stay {H : vector ℕ ι} : reduct_head H instruction.Stay = H :=
by { ext, simp, }

lemma reduction.iff {q₁ q₂ : Q} {T₁ T₂ : vector (ℕ → Γ) ι} {H₁ H₂ : vector ℕ ι}  :
  (⟦q₁, T₁, H₁⟧ ⟶¹[σ] ⟦q₂, T₂, H₂⟧) ↔
  (∃ (z : vector Γ ι) (u : vector instruction ι), ⟮q₂, z; u | q₁, read T₁ H₁⟯ ∈ σ ∧ T₂ = reduct_tape T₁ H₁ z ∧ H₂ = reduct_head H₁ u) :=
⟨by { rintros ⟨_, _, _, _, z, u, mem⟩, refine ⟨z, u, mem, rfl, rfl⟩ },
 by { rintros ⟨z, u, mem, rfl, rfl⟩, refine ⟨_, _, _, _, z, u, mem⟩ }⟩

@[simp] lemma time_bounded_reductions.refl {s} : m₁ ⟶^(≤ s)[σ] m₁ := power_le.refl

lemma time_reductions.refl : m₁ ⟶^(0)[σ] m₁ := power.zero _

@[simp] lemma time_reductions_zero_iff : (m₁ ⟶^(0)[σ] m₂) ↔ m₁ = m₂ := power.zero_iff

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
| intro : ∀ (z : vector Γ ι), fix_q_aux ⟮c, z; instruction.Stay | q, z⟯

def fix_q (q c : Q) (h : q ≠ halt ∧ c ≠ start) : sentence Γ Q ι :=
{ carrier := fix_q_aux q c,
  proper' := λ c' z u q' x, by { rintros ⟨⟩, exact h } } 

@[simp] lemma fix_q_mem (z : vector Γ ι) :
  ⟮c, z; instruction.Stay | q, z⟯ ∈ (fix_q q c h : sentence Γ Q ι) :=
fix_q_aux.intro _

lemma fix_q_mem_iff {c z u q x q₁ q₂ h} :
  ⟮c, z; u| q, x⟯ ∈ (fix_q q₁ q₂ h : sentence Γ Q ι) ↔ c = q₂ ∧ z = x ∧ q = q₁ ∧ u = instruction.Stay :=
⟨by { rintros ⟨⟩, simp; refl }, by { rintros ⟨rfl, rfl, rfl, rfl⟩, exact fix_q_aux.intro _ }⟩

lemma fix_q.deterministic : deterministic (fix_q q c h : sentence Γ Q ι) :=
by { rintros q' x c₁ c₂ z₁ z₂ u₁ u₂ h₁ h₂, rcases h₁, rcases h₂, simp }

@[simp] lemma fix_q_reduction (T : vector (ℕ → Γ) ι) (H : vector ℕ ι) : ⟦q, T, H⟧ ⟶¹[fix_q q c h] ⟦c, T, H⟧ :=
reduction.iff.mpr ⟨read T H, instruction.Stay, by simp, by simp⟩

instance : has_union (sentence Γ Q ι) := ⟨λ σ τ,
{ carrier := σ ∪ τ,
  proper' := by { rintros c z u q x (h | h), { exact σ.proper h }, { exact τ.proper h } } }⟩

def deterministic.union {σ τ : sentence Γ Q ι} (d₁ : deterministic σ) (d₂ : deterministic τ) 
  (h : ∀ {q x c₁ c₂ z₁ z₂ u₁ u₂}, ⟮c₁, z₁; u₁ | q, x⟯ ∈ σ → ⟮c₂, z₂; u₂ | q, x⟯ ∈ τ → c₁ = c₂ ∧ z₁ = z₂ ∧ u₁ = u₂) :
  deterministic (σ ∪ τ) :=
begin
  rintros q x c₁ c₂ z₁ z₂ u₁ u₂ (h₁ | h₁) (h₂ | h₂),
  { exact d₁ h₁ h₂ }, { exact h h₁ h₂ }, { simp [h h₂ h₁] }, { exact d₂ h₁ h₂ }
end

instance : has_Sup (sentence Γ Q ι) := ⟨λ s, 
{ carrier := ⋃₀ (carrier '' s),
  proper' := λ c z u q x h, by { simp at h, rcases h with ⟨σ, _, hσ⟩, exact σ.proper hσ } }⟩

lemma Sup_carrier (s : set (sentence Γ Q ι)) : ↑(Sup s) = ⋃₀ (carrier '' s) := by refl

lemma coe_supr {α : Sort*} {f : α → sentence Γ Q ι} : (↑(⨆ i, f i) : set (word Γ Q ι)) = ⋃ i, (f i) :=
by { unfold supr, rw [Sup_carrier], simp, refl }

def deterministic.Sup {s : set (sentence Γ Q ι)} (d : ∀ σ ∈ s, deterministic σ) 
  (h : ∀ (σ ∈ s) (τ ∈ s) {q x c₁ c₂ z₁ z₂ u₁ u₂},
    ⟮c₁, z₁; u₁ | q, x⟯ ∈ σ → ⟮c₂, z₂; u₂ | q, x⟯ ∈ τ → c₁ = c₂ ∧ z₁ = z₂ ∧ u₁ = u₂) :
  deterministic (Sup s) :=
begin
  rintros q x c₁ c₂ z₁ z₂ u₁ u₂ ⟨_, ⟨σ, hσs, rfl⟩, hσ⟩ ⟨_, ⟨τ, hτs, rfl⟩, hτ⟩, 
  refine h _ hσs _ hτs hσ hτ
end

def comp_suml (σ : sentence Γ Q ι) : sentence Γ (Q ⊕ R) ι := σ.map_q sum.inl (by { intros _ _ _ _ _ h, unfold halt start, simp[σ.proper h] })

def comp_sumr (τ : sentence Γ R ι) : sentence Γ (Q ⊕ R) ι := τ.map_q sum.inr (by { intros _ _ _ _ _ h, unfold halt start, simp[τ.proper h] })

def comp (σ : sentence Γ Q ι) (τ : sentence Γ R ι) : sentence Γ (Q ⊕ R) ι :=
(σ.map_q sum.inl (by { intros _ _ _ _ _ h, unfold halt start, simp[σ.proper h] })) ∪
(τ.map_q sum.inr (by { intros _ _ _ _ _ h, unfold halt start, simp[τ.proper h] })) ∪
(fix_q (sum.inl (halt : Q)) (sum.inr (start : R)) (by unfold halt start; simp))

infix ` ▷ `:80 := comp

lemma comp.deterministic {σ : sentence Γ Q ι} {τ : sentence Γ R ι}
  (d₁ : deterministic σ) (d₂ : deterministic τ) : deterministic (σ ▷ τ) :=
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

def dsum (σ : sentence Γ Q ι) (τ : sentence Γ R ι) (c : Q → R → Prop) : sentence Γ (Q ⊕ R) ι :=
(σ.map_q sum.inl (by { intros _ _ _ _ _ h, unfold halt start, simp[σ.proper h] })) ∪
(τ.map_q sum.inr (by { intros _ _ _ _ _ h, unfold halt start, simp[τ.proper h] })) ∪
(⨆ (q : Q) (r : R) (h : c q r), (fix_q (sum.inl q) (sum.inr r) (by unfold halt start; simp)))

lemma dsum.deterministic {σ : sentence Γ Q ι} {τ : sentence Γ R ι}
  (d₁ : deterministic σ) (d₂ : deterministic τ) (c : Q → R → Prop)
  (dc : ∀ q r₁ r₂, c q r₁ → c q r₂ → r₁ = r₂)
  (hc : ∀ q r, c q r → σ.is_halt q) : deterministic (dsum σ τ c) :=
begin
  refine (deterministic.union
    (deterministic.union (deterministic.map_q sum.inl_injective d₁) (deterministic.map_q sum.inr_injective d₂) _)
      (deterministic.Sup _ _) _),
  { rintros (q | r) _ _ _ _ _ _ _ ⟨⟨c₁, z₁, u₁, q, x⟩, mem₁, eqn₁⟩ ⟨⟨c₂, z₂, u₂, q', x'⟩, mem₂, eqn₂⟩,
    { simp at eqn₂, contradiction },
    { simp at eqn₁, contradiction } },
  { rintros σ ⟨q, rfl⟩, show (⨆ r (h : c q r), fix_q (sum.inl q) (sum.inr r) _).deterministic,
    refine deterministic.Sup _ _,
    { rintros _ ⟨r, rfl⟩, refine deterministic.Sup (by simpa using λ _, fix_q.deterministic _ _ _) _,
      { rintros _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ (q | r); { intros _ _ _ _ _ _ _ h₁ h₂, exact fix_q.deterministic _ _ _ h₁ h₂ } } },
    { rintros _ ⟨r₁, rfl⟩ _ ⟨r₂, rfl⟩ (q' | r');
      { rintros _ _ _ _ _ _ _ ⟨_, ⟨_, ⟨hc₁, rfl⟩, rfl⟩, h₁⟩ ⟨_, ⟨_, ⟨hc₂, rfl⟩, rfl⟩, h₂⟩,
        have : r₁ = r₂, from dc _ _ _ hc₁ hc₂, rcases this with rfl,
        exact fix_q.deterministic _ _ (by unfold halt start; simp) h₁ h₂ } } },
  { rintros _ ⟨q₁, rfl⟩ _ ⟨q₂, rfl⟩ (q | r),
    { rintros _ _ _ _ _ _ _
        ⟨_, ⟨_, ⟨r₁, rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨hc₁, rfl⟩, rfl⟩, h₁⟩⟩
        ⟨_, ⟨_, ⟨r₂, rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨hc₂, rfl⟩, rfl⟩, h₂⟩⟩,
      simp at h₁ h₂,
      have : c₁ = sum.inr r₁ ∧ z₁ = x ∧ q = q₁ ∧ u₁ = instruction.Stay,
      { simpa using fix_q_mem_iff.mp h₁, unfold halt start; simp },
      rcases this with ⟨rfl, rfl, rfl, rfl⟩,
      have : c₂ = sum.inr r₂ ∧ z₂ = z₁ ∧ q = q₂ ∧ u₂ = instruction.Stay,
      { simpa using fix_q_mem_iff.mp h₂, unfold halt start; simp },
      rcases this with ⟨rfl, rfl, rfl, rfl⟩,
      have : r₁ = r₂, from dc _ _ _ hc₁ hc₂, rcases this with rfl,
      simp },
    { simp,  rintros _ _ _ _ _ _ _
        ⟨_, ⟨_, ⟨r₁, rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨hc₁, rfl⟩, rfl⟩, h₁⟩⟩ _,
      have : false, { simpa using (fix_q_mem_iff.mp h₁), unfold start halt; simp },
      contradiction } },
  { rintros (q | r),
    { rintros x _ _ _ _ _ _ (⟨⟨c₁, z₁, u₁, q₁, x₁⟩, wmem, hw⟩ | ⟨⟨c₁, z₁, u₁, q₁, x₁⟩, wmem, hw⟩),
      { simp at hw, rcases hw with ⟨rfl, rfl, rfl, rfl, rfl⟩,
        rintros ⟨_, ⟨_, ⟨q', rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨r', rfl⟩, rfl⟩, H, ⟨_, ⟨hc', rfl⟩, rfl⟩, h₁⟩⟩,
        have : q₁ = q',
        { have := fix_q_mem_iff.mp h₁, simp at this, rcases this with ⟨rfl, rfl, rfl, rfl⟩; refl,
          unfold start halt; simp },
        rcases this with rfl,
        have : false := hc _ _ hc' wmem, contradiction },
      { simp at hw, contradiction } },
    { rintros x _ _ _ _ _ _ (⟨⟨c₁, z₁, u₁, q₁, x₁⟩, wmem, hw⟩ | ⟨⟨c₁, z₁, u₁, q₁, x₁⟩, wmem, hw⟩), 
      { simp at hw, contradiction },
      { simp at hw, rcases hw with ⟨rfl, rfl, rfl, rfl, rfl⟩,
        rintros ⟨_, ⟨_, ⟨q', rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨r', rfl⟩, rfl⟩, H, ⟨_, ⟨hc', rfl⟩, rfl⟩, h₁⟩⟩,
        have : false, { have := fix_q_mem_iff.mp h₁, simpa using this, unfold start halt; simp },
        contradiction } } }
end

end sentence

lemma time_reductions.comp_aux {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {n₁ n₂} {q r T₁ T₂ T₃ H₁ H₂ H₃}
  (h₁ : ⟦q, T₁, H₁⟧ ⟶^(n₁)[σ] ⟦halt, T₂, H₂⟧) (h₂ : ⟦start, T₂, H₂⟧ ⟶^(n₂)[τ] ⟦r, T₃, H₃⟧) :
  ⟦sum.inl q, T₁, H₁⟧ ⟶^(n₁ + n₂ + 1)[σ ▷ τ] ⟦sum.inr r, T₃, H₃⟧ :=
begin
  have h₁ : ⟦sum.inl q, T₁, H₁⟧ ⟶^(n₁)[σ ▷ τ] ⟦sum.inl halt, T₂, H₂⟧,
  from time_reductions.of_ss (time_reductions.map_q sum.inl h₁)
    (by { simp[(▷)], refine set.subset_union_of_subset_left (set.subset_union_left _ _) _,
          { intros _ _ _ _ _ h, unfold halt start, simp[σ.proper h] } }),
  have h : ⟦sum.inl halt, T₂, H₂⟧ ⟶¹[σ ▷ τ] ⟦sum.inr start, T₂, H₂⟧,
  from reduction.of_ss (sentence.fix_q_reduction _ _ _ _ _)
    (by { simp[(▷)], refine set.subset_union_right _ _, { unfold halt start; simp } }),
  have h₂ : ⟦sum.inr start, T₂, H₂⟧ ⟶^(n₂)[σ ▷ τ] ⟦sum.inr r, T₃, H₃⟧,
  from time_reductions.of_ss (time_reductions.map_q sum.inr h₂)
    (by { simp[(▷)], refine set.subset_union_of_subset_left (set.subset_union_right _ _) _,
          { intros _ _ _ _ _ h, unfold halt start, simp[τ.proper h] } }),
  simpa[show n₁.succ + n₂ = n₁ + n₂ + 1, by omega] using (h₁.succ h).add h₂
end

lemma time_reductions.comp {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {n₁ n₂ : ℕ} {T₁ T₂ T₃ H₁ H₂ H₃}
  (h₁ : ⟦start, T₁, H₁⟧ ⟶^(n₁)[σ] ⟦halt, T₂, H₂⟧) (h₂ : ⟦start, T₂, H₂⟧ ⟶^(n₂)[τ] ⟦halt, T₃, H₃⟧) :
  ⟦start,  T₁, H₁⟧ ⟶^(n₁ + n₂ + 1)[σ ▷ τ] ⟦halt, T₃, H₃⟧ :=
time_reductions.comp_aux h₁ h₂

lemma time_bounded_reductions.comp {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {k₁ k₂ : ℕ} {T₁ T₂ T₃ H₁ H₂ H₃}
  (h₁ : ⟦start, T₁, H₁⟧ ⟶^(≤ k₁)[σ] ⟦halt, T₂, H₂⟧) (h₂ : ⟦start, T₂, H₂⟧ ⟶^(≤ k₂)[τ] ⟦halt, T₃, H₃⟧) :
  ⟦start,  T₁, H₁⟧ ⟶^(≤ k₁ + k₂ + 1)[σ ▷ τ] ⟦halt, T₃, H₃⟧ :=
by { rcases h₁ with ⟨n₁, le₁, h₁⟩, rcases h₂ with ⟨n₂, le₂, h₂⟩, refine ⟨n₁ + n₂ + 1, by linarith, time_reductions.comp h₁ h₂⟩ }

lemma time_reductions.dsum_left {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {q₁ q₂ T₁ T₂ H₁ H₂} {n}
  (h : ⟦q₁, T₁, H₁⟧ ⟶^(n)[σ] ⟦q₂, T₂, H₂⟧) (φ : Q → R → Prop) :
  ⟦sum.inl q₁, T₁, H₁⟧ ⟶^(n)[sentence.dsum σ τ φ] ⟦sum.inl q₂, T₂, H₂⟧ :=
by exact time_reductions.of_ss (time_reductions.map_q sum.inl h)
    (by { simp, refine set.subset_union_of_subset_left (set.subset_union_left _ _) _,
          { intros _ _ _ _ _ h, unfold halt start, simp[σ.proper h] } })

lemma time_reductions.dsum_right {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {r₁ r₂ T₁ T₂ H₁ H₂} {n}
  (h : ⟦r₁, T₁, H₁⟧ ⟶^(n)[τ] ⟦r₂, T₂, H₂⟧) (φ : Q → R → Prop) :
  ⟦sum.inr r₁, T₁, H₁⟧ ⟶^(n)[sentence.dsum σ τ φ] ⟦sum.inr r₂, T₂, H₂⟧ :=
by exact time_reductions.of_ss (time_reductions.map_q sum.inr h)
    (by { simp, refine set.subset_union_of_subset_left (set.subset_union_right _ _) _,
          { intros _ _ _ _ _ h, unfold halt start, simp[τ.proper h] } })

lemma time_reductions.dsum {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {n₁ n₂} {q₁ q₂ r₂ r₃ T₁ T₂ T₃ H₁ H₂ H₃}
  (φ : Q → R → Prop) (h : φ q₂ r₂)
  (h₁ : ⟦q₁, T₁, H₁⟧ ⟶^(n₁)[σ] ⟦q₂, T₂, H₂⟧) (h₂ : ⟦r₂, T₂, H₂⟧ ⟶^(n₂)[τ] ⟦r₃, T₃, H₃⟧) :
  ⟦sum.inl q₁, T₁, H₁⟧ ⟶^(n₁ + n₂ + 1)[sentence.dsum σ τ φ] ⟦sum.inr r₃, T₃, H₃⟧ :=
begin
  have h₁ : ⟦sum.inl q₁, T₁, H₁⟧ ⟶^(n₁)[sentence.dsum σ τ φ] ⟦sum.inl q₂, T₂, H₂⟧,
  from time_reductions.dsum_left h₁ φ,
  have h : ⟦sum.inl q₂, T₂, H₂⟧ ⟶¹[sentence.dsum σ τ φ] ⟦sum.inr r₂, T₂, H₂⟧,
  from reduction.of_ss (sentence.fix_q_reduction _ _ _ _ _)
    (by { refine set.subset_union_of_subset_right _ _, { unfold halt start; simp },
      simp[sentence.coe_supr], refine set.subset_Union₃ q₂ r₂ h }),
  have h₂ : ⟦sum.inr r₂, T₂, H₂⟧ ⟶^(n₂)[sentence.dsum σ τ φ] ⟦sum.inr r₃, T₃, H₃⟧,
  from time_reductions.dsum_right h₂ φ,
  simpa[show n₁.succ + n₂ = n₁ + n₂ + 1, by omega] using (h₁.succ h).add h₂
end

lemma time_bounded_reductions.dsum {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {n₁ n₂} {q₁ q₂ r₂ r₃ T₁ T₂ T₃ H₁ H₂ H₃}
  (φ : Q → R → Prop) (h : φ q₂ r₂)
  (h₁ : ⟦q₁, T₁, H₁⟧ ⟶^(≤ n₁)[σ] ⟦q₂, T₂, H₂⟧) (h₂ : ⟦r₂, T₂, H₂⟧ ⟶^(≤ n₂)[τ] ⟦r₃, T₃, H₃⟧) :
  ⟦sum.inl q₁, T₁, H₁⟧ ⟶^(≤ n₁ + n₂ + 1)[sentence.dsum σ τ φ] ⟦sum.inr r₃, T₃, H₃⟧ :=
by{ rcases h₁ with ⟨n₁, le₁, h₁⟩, rcases h₂ with ⟨n₂, le₂, h₂⟩,
    refine ⟨n₁ + n₂ + 1, by linarith, time_reductions.dsum φ h h₁ h₂⟩ }

end model

namespace blang
open instruction model
variables (Γ Q ι) [inhabited Γ] [bfin Γ]

def list_less_than (k : ℕ) := {l : list (option bool) // l.length ≤ k}

instance (k : ℕ) : inhabited (list_less_than k) := ⟨⟨[], by simp⟩⟩

namespace read

inductive state
| intro (q : Q) (i : fin (bentropy Γ).succ) (v : vector (vector bool (bentropy Γ)) ι) : state

variables {Γ Q ι}

instance [state_lang Q] : state_lang (state Γ Q ι) :=
⟨state.intro start 0 default, state.intro halt ⊤ default⟩

def δ : state Γ Q ι → vector bool ι → option (state Γ Q ι × vector bool ι × vector instruction ι)
| ⟨q, i, v⟩ x := if h : i < ⊤ then 
    let newstate : state Γ Q ι :=
      ⟨q, ⟨i + 1, nat.succ_lt_succ (fin.lt_top_iff.mp h)⟩, (v.sim_update_nth (vector.rep ⟨i, fin.lt_top_iff.mp h⟩) x)⟩ in 
  some ⟨newstate, x, Right⟩ else none

@[simp] lemma δ_top {q v x} : δ (⟨q, ⊤, v⟩ : state Γ Q ι) x = none := by simp[δ]

def σ : sentence bool (state Γ Q ι) ι := sentence.of_fun δ
(by { unfold start halt,
      intros q x c z u eqn, split; rintros rfl,
      { simpa using eqn },
      { rcases q with ⟨q, i, v⟩, by_cases C : i < ⊤; simp[C, δ, fin.ext_iff] at eqn; contradiction } })

section
variables (v : vector (vector bool (bentropy Γ)) ι) (T : vector (ℕ → bool) ι) (H : vector ℕ ι)

lemma σ_reduction (q : Q) (i : fin (bentropy Γ).succ) (h : i < ⊤) :
  ⟦⟨q, i, v⟩, T, H⟧ ⟶¹[σ]
  ⟦⟨q, ⟨i + 1, nat.succ_lt_succ (fin.lt_top_iff.mp h)⟩, 
    v.sim_update_nth (vector.rep ⟨i, fin.lt_top_iff.mp h⟩) (read T H)⟩, T, H.map nat.succ⟧ :=
reduction.iff.mpr (⟨read T H, Right, by simp[σ, δ, h], by simp, by ext; simp⟩)

@[simp] lemma σ_is_halt (q : Q) (v : vector (vector bool (bentropy Γ)) ι) : σ.is_halt ⟨q, ⊤, v⟩ :=
by intros c z u x; simp[σ]

def memory :
  fin (bentropy Γ).succ → vector (vector bool (bentropy Γ)) ι
| ⟨0, _⟩      := v
| ⟨s + 1, hn⟩ := (memory ⟨s, by omega⟩).sim_update_nth (vector.rep ⟨s, by omega⟩) (read T (H.map ((+) s)))

@[simp] lemma memory_0 : memory v T H 0 = v := by unfold has_zero.zero; rw [memory]

lemma σ_time_reductions (q : Q) :
  ∀ (s : fin (bentropy Γ).succ), ⟦⟨q, 0, v⟩, T, H⟧ ⟶^(s)[σ] ⟦⟨q, s, memory v T H s⟩, T, H.map ((+) s)⟧
| ⟨0, _⟩      := by { simp, ext, simp, }
| ⟨s + 1, hs⟩ := by { 
    let s' : fin (bentropy Γ).succ := ⟨s, by omega⟩,
    have r : ⟦⟨q, 0, v⟩, T, H⟧ ⟶^(s)[σ] ⟦⟨q, ⟨s, _⟩, memory v T H ⟨s, _⟩⟩, T, H.map ((+) s)⟧,
    from σ_time_reductions ⟨s, by omega⟩,
    have : ⟦⟨q, ⟨s, _⟩, memory v T H ⟨s, _⟩⟩, T, H.map ((+) s)⟧ ⟶¹[σ] ⟦⟨q, ⟨s + 1, _⟩, memory v T H ⟨s + 1, _⟩⟩, T, _⟧,
    by simpa[memory] using
      σ_reduction (memory v T H s') T (H.map ((+) s)) q s' (by simp[fin.lt_top_iff]; exact nat.succ_lt_succ_iff.mp hs),
    rw [show (H.map ((+) s)).map nat.succ = H.map ((+) s.succ), by ext; simp[nat.succ_add]] at this,
    exact r.succ this }

lemma memory_nth_nth_of_lt : ∀ (s : fin (bentropy Γ).succ) k i (h : ↑i < s), 
  ((memory v T H s).nth k).nth i = T.nth k (i + H.nth k)
| ⟨0, _⟩ k i hi := by simp at hi; contradiction
| ⟨s + 1, hs⟩ k ⟨i, hi⟩ h := by { 
    have : i = s ∨ i < s, from eq_or_lt_of_le (nat.lt_succ_iff.mp (by simpa using h)),
    rcases this with (rfl | lt); simp[memory, vector.nth_sim_update_nth_if],
    { have : s ≠ i, from ne_of_gt lt,
      simp[this],
      simpa using memory_nth_nth_of_lt ⟨s, lt_trans (lt_add_one s) hs⟩ k ⟨i, hi⟩ (by simpa using lt) } }

lemma σ_time_reductions_top (q : Q) : ⟦⟨q, 0, v⟩, T, H⟧ ⟶^(bentropy Γ)[σ] ⟦⟨q, ⊤, memory v T H ⊤⟩, T, H.map ((+) (bentropy Γ))⟧ :=
σ_time_reductions v T H q ⊤

lemma memory_nth_nth (k i) : ((memory v T H ⊤).nth k).nth i = T.nth k (i + H.nth k) :=
memory_nth_nth_of_lt v T H ⊤ k i (by simp[fin.lt_top_iff]; exact fin.is_lt i)

end

end read

namespace write

inductive state
| intro (q : Q) (i : fin (bentropy Γ).succ) (v : vector (vector bool (bentropy Γ)) ι) (u : vector instruction ι) : state

variables {Γ Q ι}

instance [state_lang Q] : state_lang (state Γ Q ι) :=
⟨state.intro start ⊤ default Stay, state.intro halt 0 default Stay⟩

def δ : state Γ Q ι → vector bool ι → option (state Γ Q ι × vector bool ι × vector instruction ι)
| ⟨q, ⟨0, _⟩, v, u⟩      x := none
| ⟨q, ⟨i + 1, hi⟩, v, u⟩ x := 
    let newstate : state Γ Q ι := ⟨q, ⟨i, by omega⟩, v, u⟩,
        i' : fin (bentropy Γ)  := ⟨i, nat.succ_lt_succ_iff.mp hi⟩ in 
  some ⟨newstate, v.map (λ x, x.nth i'), Left⟩

@[simp] lemma δ_top {q v x u} : δ (⟨q, 0, v, u⟩ : state Γ Q ι) x = none := by unfold has_zero.zero; rw [δ]

def σ : sentence bool (state Γ Q ι) ι := sentence.of_fun δ
(by { unfold start halt,
      intros q x c z u eqn, split; rintros rfl,
      { simpa using eqn },
      { rcases q with ⟨q, ⟨i, hi⟩, v, u⟩, rcases i; simp[δ] at eqn,
        { contradiction },
        { have lt : i < bentropy Γ, from nat.succ_lt_succ_iff.mp hi,
          have eq : i = bentropy Γ, by simpa[fin.coe_top] using (fin.eq_iff_veq _ _).mp eqn.1.2.1,
          simp[eq] at lt, contradiction } } })

section
variables (v : vector (vector bool (bentropy Γ)) ι) (u : vector instruction ι) (T : vector (ℕ → bool) ι) (H : vector ℕ ι)

def σ_tape_reduct (i) :=
vector.zip_with3 (λ (t : ℕ → bool) h (x : vector bool (bentropy Γ)) n, if n = h then x.nth i else t n) T H v

lemma σ_reduction (q : Q) (i : ℕ) (hi) :
  ⟦⟨q, ⟨i + 1, hi⟩, v, u⟩, T, H⟧ ⟶¹[σ]
  ⟦⟨q, ⟨i, by omega⟩, v, u⟩, σ_tape_reduct v T H ⟨i, nat.succ_lt_succ_iff.mp hi⟩, H.map nat.pred⟧ :=
reduction.iff.mpr (⟨v.map (λ x, x.nth ⟨i, (by omega)⟩), Left, by simp[σ, δ]; refl,
  by { simp[reduct_tape, σ_tape_reduct], ext, simp }, by { ext, simp, exact nat.pred_eq_sub_one _ }⟩)

@[simp] lemma σ_is_halt (q : Q) : σ.is_halt ⟨q, 0, v, u⟩ :=
λ c z u x, by simp[σ]

def Tape : fin (bentropy Γ).succ → vector (vector bool (bentropy Γ)) ι → vector (ℕ → bool) ι → vector ℕ ι → vector (ℕ → bool) ι
| ⟨0, _⟩      v T H := T
| ⟨s + 1, hn⟩ v T H := Tape ⟨s, by omega⟩ v (σ_tape_reduct v T H ⟨s, nat.succ_lt_succ_iff.mp hn⟩) (H.map nat.pred)

@[simp] lemma Tape_0 : Tape 0 v T H = T := by unfold has_zero.zero; rw [Tape]

lemma σ_time_reductions (q : Q) :
  ∀ (s : fin (bentropy Γ).succ) (T H), ⟦⟨q, s, v, u⟩, T, H⟧ ⟶^(s)[σ] ⟦⟨q, 0, v, u⟩, Tape s v T H, (H.map (λ h, h - s))⟧
| ⟨0, _⟩      T H := by { simp, ext, simp }
| ⟨s + 1, hs⟩ T H := by { 
    let s' : fin (bentropy Γ).succ := ⟨s, by omega⟩,
    let s'' : fin (bentropy Γ) := ⟨s, by { exact nat.succ_lt_succ_iff.mp hs}⟩,
    have r : ⟦⟨q, ⟨s, _⟩, v, u⟩, _, H.map nat.pred⟧ ⟶^(s)[σ] ⟦⟨q, 0, v, u⟩, _, H.map (λ h, h - (s + 1))⟧,
    { have := σ_time_reductions ⟨s, by omega⟩ (σ_tape_reduct v T H ⟨s, by omega⟩) (H.map nat.pred), simp at this, 
      rw[show (H.map nat.pred).map (λ h, h - s) = H.map (λ h, h - (s + 1)),
         by { ext; simp;  rw[nat.pred_sub, nat.pred_eq_sub_one, tsub_tsub] }] at this,
      exact this },
    have : ⟦⟨q, ⟨s + 1, _⟩, v, u⟩, T, H⟧ ⟶¹[σ] ⟦⟨q, ⟨s, _⟩, v, u⟩, _, H.map nat.pred⟧,
    from σ_reduction v u T H q s hs,
    have : ⟦⟨q, ⟨s + 1, _⟩, v, u⟩, T, H⟧ ⟶^(s+1)[σ] ⟦⟨q, 0, v, u⟩, _, H.map (λ h, h - (s + 1))⟧,
    from relation.power.succ_inv this r,
    simpa[Tape, @sub_add_eq_sub_sub ℕ] using this }

end

end write

end blang


namespace universal_tm
variables {Γ Q ι}

abbreviation lang := word Γ Q ι ⊕ vector Γ ι



end universal_tm

end turing_machine