import tactic data.vector.zip algebra.big_operators.basic algebra.big_operators.norm_num
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

class state_lang (Q : Type u) :=
(start : Q)
(halt : Q)

instance {Q R} [state_lang Q] [state_lang R] : state_lang (Q ⊕ R) := ⟨sum.inl state_lang.start, sum.inr state_lang.halt⟩

end turing_machine

def option.to_language {Γ : Type u} : option Γ → turing_machine.language Γ
| none     := ␣
| (some x) := turing_machine.language.chr x

namespace turing_machine
open state_lang

namespace TM

inductive deg 
| stay  : deg
| right : deg
| left  : deg

end TM

class tape_class (α : Type u) := (input : α) (output : α)

variables
  (Γ : Type u) -- 言語
  (Q : Type v) -- 状態
  (ι : ℕ) -- テープの数

inductive instruction
| stay  : instruction
| right : instruction
| left  : instruction

@[simp] def instruction.apply : instruction → ℕ → ℕ
| instruction.stay  ι := ι
| instruction.right ι := ι + 1
| instruction.left  ι := ι - 1

structure word :=
(cond : Q × vector Γ ι)
(cons : Q × vector (Γ × instruction) ι)

infix ` ▷ `:80 := word.mk

structure line :=
(tape : ℕ → Γ)
(head : ℕ)

@[ext] lemma line.ext (l₁ l₂ : line Γ) (et : l₁.tape = l₂.tape) (eh : l₁.head = l₂.head) : l₁ = l₂ :=
by { rcases l₁; rcases l₂, simp at et eh, simp[eh, et] }

structure model :=
(state : Q) 
(lines : vector (line Γ) ι)


abbreviation sentence := set (word Γ Q ι)

variables {Γ Q ι}

namespace model
variables (σ : sentence Γ Q ι)

@[ext] lemma ext : ∀ {m₁ m₂ : model Γ Q ι}
  (input : m₁.lines = m₂.lines)
  (state : m₁.state = m₂.state), m₁ = m₂
| ⟨q₁, L₁⟩ ⟨q₂, L₂⟩ tape state :=
  by { simp, split, { exact state }, { funext, exact tape }  }

def read (m : model Γ Q ι) : vector Γ ι := m.lines.map (λ l, l.1 l.2)

def snapshot (m : model Γ Q ι) : Q × vector Γ ι := ⟨m.state, m.lines.map (λ ⟨T, n⟩, T n)⟩

def reduct (q : Q) (z : vector (Γ × instruction) ι) : model Γ Q ι → model Γ Q ι
| ⟨_, L⟩ :=
  { lines := @vector.zip_with (line Γ) (Γ × instruction) (line Γ) ι
      (λ ⟨T, h⟩ ⟨x, i⟩, ⟨λ n, if n = h then x else T n, i.apply h⟩) L z,
    state := q }

@[simp] lemma reduct_head (m : model Γ Q ι) (q : Q) (z : vector (Γ × instruction) ι) :
  (reduct q z m).state = q := by cases m; simp[reduct]

lemma reduct_lines_nth (m : model Γ Q ι) (q : Q) (z : vector (Γ × instruction) ι) (i : fin ι) :
  (reduct q z m).lines.nth i = ⟨λ n, if n = (m.lines.nth i).2 then (z.nth i).1 else (m.lines.nth i).1 n, (z.nth i).2.apply (m.lines.nth i).2⟩ :=
by { rcases m with ⟨_, L⟩, rcases eL : L.nth i with ⟨T, h⟩, rcases ez: z.nth i with ⟨x, ins⟩, simp[eL, ez, reduct] }


inductive reduction : model Γ Q ι → model Γ Q ι → Prop
| intro : ∀ (m : model Γ Q ι) (q : Q) (z : vector (Γ × instruction) ι),
    ⟨m.state, m.read⟩ ▷ ⟨q, z⟩ ∈ σ → reduction m (reduct q z m)
  
notation m₀ ` ⟶¹[`:60  σ `] ` :0 m₁ := reduction σ m₀ m₁ 

def is_halt (m : model Γ Q ι) : Prop := ∀ m', ¬m ⟶¹[σ] m'

inductive time_reductions : ℕ → model Γ Q ι → model Γ Q ι → Prop
| zero : ∀ m, time_reductions 0 m m
| succ : ∀ {ι m₀ m₁ m₂}, time_reductions ι m₀ m₁ → (m₁ ⟶¹[σ] m₂) → time_reductions ι.succ m₀ m₂

attribute [simp] time_reductions.zero

notation m₀ ` ⟶^(`:80 s `)[`:80  σ `] ` :0 m₁ := time_reductions σ s m₀ m₁ 

def time_bounded_reductions (s : ℕ) (m m' : model Γ Q ι) : Prop := ∃ s' ≤ s, m ⟶^(s')[σ] m'
notation m₀ ` ⟶^(≤ ` s `)[`:80  σ `] ` :0 m₁ := time_bounded_reductions σ s m₀ m₁ 

def time_bounded_reductions_halt (s : ℕ) (m m' : model Γ Q ι) : Prop := is_halt σ m' ∧ ∃ s' ≤ s, m ⟶^(s')[σ] m'
notation m₀ ` ⟶^(≤ ` s `)[`:80  σ `]↓ ` :0 m₁ := time_bounded_reductions_halt σ s m₀ m₁ 

def reductions (m m' : model Γ Q ι) : Prop := ∃ s : ℕ, m ⟶^(s)[σ] m' 

notation m₀ ` ⟶*[`:80  σ `] ` :0 m₁ := reductions σ m₀ m₁ 

def converge (m₀ m₁ : model Γ Q ι) : Prop := is_halt σ m₁ ∧ (m₀ ⟶*[σ] m₁)

notation m₀ ` ⟶ᵗ[`:80 σ `] ` :0 m₁ := converge m₀ m₁

end model

variables {Γ Q ι} 
def sentence.deterministic (σ : sentence Γ Q ι) : Prop := ∀ q q₁ q₂, q ▷ q₁ ∈ σ → q ▷ q₂ ∈ σ → q₁ = q₂

def sentence.proper [state_lang Q] (σ : sentence Γ Q ι) : Prop :=
  ∀ w₁ w₂, w₁ ▷ w₂ ∈ σ → w₁.1 ≠ state_lang.halt ∧ w₂.1 ≠ state_lang.start

namespace sentence

namespace deterministic
variables {σ : sentence Γ Q ι} {m₁ m₂ : model Γ Q ι}

lemma reduction (d : deterministic σ) {m m₁ m₂}
  (h₁ : m ⟶¹[σ] m₁) (h₂ : m ⟶¹[σ] m₂) : m₁ = m₂ :=
begin
  rcases h₁ with ⟨_, q₁, z₁, w₁⟩,
  rcases h₂ with ⟨_, q₂, z₂, w₂⟩,
  have : q₁ = q₂ ∧ z₁ = z₂, by simpa using d _ _ _ w₁ w₂,
  rcases this with ⟨rfl, rfl, rfl⟩,
  refl
end

lemma time_reductions (d : deterministic σ) {m m₁ m₂} {s} (h₁ : m ⟶^(s)[σ] m₁) (h₂ : m ⟶^(s)[σ] m₂) :
  m₁ = m₂ :=
begin
  induction s with s IH generalizing m₁ m₂,
  { rcases h₁, rcases h₂, refl },
  { rcases h₁ with (_ | ⟨_, _, m₁₁, _, h_₁₁, h₁₁_₁⟩),
    rcases h₂ with (_ | ⟨_, _, m₂₁, _, h_₂₁, h₂₁_₂⟩),
    have : m₁₁ = m₂₁, from IH h_₁₁ h_₂₁, rcases this with rfl,
    exact reduction @d h₁₁_₁ h₂₁_₂ }
end

end deterministic

end sentence

namespace model
open sentence sentence.deterministic
variables {m₁ m₂ m₃ : model Γ Q ι} {σ : sentence Γ Q ι}

@[simp] lemma time_bounded_reductions.refl {s} : m₁ ⟶^(≤ s)[σ] m₁ :=
⟨0, zero_le s, time_reductions.zero m₁⟩

lemma time_bounded_reductions.of_le {s₁ s₂} (h : m₁ ⟶^(≤ s₁)[σ] m₂) (le : s₁ ≤ s₂) :
  m₁ ⟶^(≤ s₂)[σ] m₂ := 
by rcases h with ⟨s, le_s, h⟩; refine ⟨s, le_trans le_s le, h⟩

lemma time_reductions.add {s₁ s₂} (h₁ : m₁ ⟶^(s₁)[σ] m₂) (h₂ : m₂ ⟶^(s₂)[σ] m₃) :
  m₁ ⟶^(s₁ + s₂)[σ] m₃ :=
begin
  induction s₂ with s₂ IH generalizing s₁ m₁ m₂ m₃,
  { rcases h₂, exact h₁ },
  { rcases h₂ with (_| ⟨_, _, m₂₁, _, h₂_₂₁, h₂₁_₃⟩),
  simpa using (IH h₁ h₂_₂₁).succ h₂₁_₃ }
end

lemma time_bounded_reductions.add {s₁ s₂} (h₁ : m₁ ⟶^(≤ s₁)[σ] m₂) (h₂ : m₂ ⟶^(≤ s₂)[σ] m₃) :
  m₁ ⟶^(≤ s₁ + s₂)[σ] m₃ :=
begin
  rcases h₁ with ⟨t₁, le₁, h₁⟩,
  rcases h₂ with ⟨t₂, le₂, h₂⟩,
  refine ⟨t₁ + t₂, add_le_add le₁ le₂, h₁.add h₂⟩,
end

lemma time_bounded_reductions.sum {m : ℕ → model Γ Q ι} {s : ℕ → ℕ}
  (h : ∀ k, m k ⟶^(≤ s k)[σ] m (k + 1)) (k : ℕ) : (m 0) ⟶^(≤ ∑ i in finset.range k, s i)[σ] (m k) :=
by { induction k with k IH, { simp }, { simpa[finset.sum_range_succ] using IH.add (h k) } }

lemma reduction.of_ss (r : m₁ ⟶¹[σ] m₂) {τ : sentence Γ Q ι} (ss : σ ⊆ τ) : m₁ ⟶¹[τ] m₂ :=
by { rcases r with ⟨_, q, z, mem⟩, refine ⟨_, _, _, _⟩, exact ss mem }

lemma time_reductions.of_ss {n} (r : m₁ ⟶^(n)[σ] m₂) {τ : sentence Γ Q ι} (ss : σ ⊆ τ) : m₁ ⟶^(n)[τ] m₂ :=
by { induction n with n IH generalizing m₂, { rcases r, simp },
     { rcases r with (_ | ⟨_, _, m₁₁, _, r₁_₁₁, r₁₁_₂⟩), exact (IH r₁_₁₁).succ (r₁₁_₂.of_ss ss) } }

lemma time_bounded_reductions.of_ss {k} (r : m₁ ⟶^(≤ k)[σ] m₂) {τ : sentence Γ Q ι} (ss : σ ⊆ τ) : m₁ ⟶^(≤ k)[τ] m₂ :=
by { rcases r with ⟨n, le, r⟩, refine ⟨n, le, r.of_ss ss⟩ }

section
variables {R : Type v} (f : Q → R)

@[simp] def map_q : model Γ Q ι → model Γ R ι
| ⟨q, L⟩ := ⟨f q, L⟩

instance [has_coe Q R] : has_coe (model Γ Q ι) (model Γ R ι) := ⟨λ m, m.map_q coe⟩ 

@[simp] def word.map_q : word Γ Q ι → word Γ R ι
| (⟨q, w⟩ ▷ ⟨q', w'⟩) :=  ⟨f q, w⟩ ▷ ⟨f q', w'⟩

variables (m m' : model Γ Q ι) {f}

@[simp] lemma map_q_lines (m : model Γ Q ι) : (m.map_q f).lines = m.lines := by cases m; simp

@[simp] lemma map_q_state (m : model Γ Q ι) : (m.map_q f).state = f m.state := by cases m; simp

@[simp] lemma map_q_reduct (q : Q) (z : vector (Γ × instruction) ι) :
  (reduct q z m).map_q f = reduct (f q) z (m.map_q f) := by cases m; simp[reduct]

@[simp] lemma map_q_snapshot : (m.map_q f).read = m.read :=  by cases m; simp[read]

variables (f)

lemma reduction.map_q (h : m₁ ⟶¹[σ] m₂) (f : Q → R) : m₁.map_q f ⟶¹[word.map_q f '' σ] m₂.map_q f :=
by { rcases h with ⟨_, q, w, mem⟩, simp, refine ⟨_, _, _, _⟩, simp, refine ⟨_, mem, by simp⟩ }

lemma time_reductions.map_q {n} (h : m₁ ⟶^(n)[σ] m₂) (f : Q → R) : m₁.map_q f ⟶^(n)[word.map_q f '' σ] m₂.map_q f :=
by { induction n with n IH generalizing m₂, { rcases h, simp },
     { rcases h with (_ | ⟨_, _, m₁₁, _, r₁_₁₁, r₁₁_₂⟩), refine (IH r₁_₁₁).succ (r₁₁_₂.map_q f) } }

lemma time_bounded_reduction.map_q {k} (h : m₁ ⟶^(≤ k)[σ] m₂) (f : Q → R) : m₁.map_q f ⟶^(≤ k)[word.map_q f '' σ] m₂.map_q f :=
by { rcases h with ⟨n, le, r⟩, refine ⟨n, le, r.map_q f⟩ }

variables {f}

lemma deterministic.map_q (inj : function.injective f) (d : deterministic σ) : deterministic (word.map_q f '' σ) :=
begin
  rintros ⟨r, w⟩ ⟨r₁, w₁⟩ ⟨r₂, w₂⟩ h₁ h₂,
  rcases h₁ with ⟨⟨⟨q, w'⟩, ⟨q₁, w₁'⟩⟩, mem₁, eq₁⟩,
  have : f q = r ∧ w = w' ∧ f q₁ = r₁ ∧ w₁ = w₁', { simp at eq₁, simp[eq₁] },
  rcases this with ⟨rfl, rfl, rfl, rfl⟩,
  rcases h₂ with ⟨⟨⟨q', w'⟩, ⟨q₂, w₂'⟩⟩, mem₂, eq₂⟩,
  have : f q' = f q ∧ w = w' ∧ f q₂ = r₂ ∧ w₂ = w₂', { simp at eq₂, simp[eq₂] },
  rcases this with ⟨eq, rfl, rfl, rfl⟩,
  have : q = q', from (inj eq).symm, rcases this with rfl,
  have : q₁ = q₂ ∧ w₁ = w₂, by simpa using d _ _ _ mem₁ mem₂,
  simp[this] 
end

end

variables {R : Type v}

inductive sentence.fix_q (q₁ q₂ : Q) : sentence Γ Q ι
| intro : ∀ v : vector Γ ι, sentence.fix_q ((q₁, v) ▷ (q₂, v.map (λ x, (x, instruction.stay))))

@[simp] lemma sentence.fix_q_mem (q₁ q₂ : Q) (v : vector Γ ι) :
   ((q₁, v) ▷ (q₂, v.map (λ x, (x, instruction.stay)))) ∈ (sentence.fix_q q₁ q₂ : sentence Γ Q ι) :=
sentence.fix_q.intro v

lemma sentence.fix_q.deterministic (q₁ q₂ : Q) : deterministic (sentence.fix_q q₁ q₂ : sentence Γ Q ι) :=
by { rintros w w₁ w₂ h₁ h₂, rcases h₁, rcases h₂, simp }

lemma sentence.fix_q_reduction (q₁ q₂ : Q) (L : vector (line Γ) ι) : ⟨q₁, L⟩ ⟶¹[sentence.fix_q q₁ q₂] ⟨q₂, L⟩ :=
begin
  let v := (⟨q₁, L⟩ : model Γ Q ι).read,
  let z := vector.map (λ (x : Γ), (x, instruction.stay)) v,
  suffices : ⟨q₁, L⟩ ⟶¹[fix_q q₁ q₂] reduct q₂ z ⟨q₁, L⟩,
  { have e: (⟨q₂, L⟩ : model Γ Q ι) = reduct q₂ z ⟨q₁, L⟩,
    { ext; simp[reduct_lines_nth, v, read], by_cases e : x = (L.nth m).head; simp[e] },
    simpa[e] using this },
  have : (q₁, v) ▷ (q₂, z) ∈ fix_q q₁ q₂, from sentence.fix_q_mem q₁ q₂ v,
  refine reduction.intro ⟨q₁, L⟩ q₂ z this
end

def deterministic.union {σ τ : sentence Γ Q ι} (dσ : deterministic σ) (dτ : deterministic τ)
  (h : ∀ (w₁ w₂ : word Γ Q ι), w₁ ∈ σ → w₂ ∈ τ → w₁.cond = w₂.cond → w₁.cons = w₂.cons) : deterministic (σ ∪ τ) :=
begin
    rintros w w₁ w₂ h₁ h₂,
   rcases h₁,
   { rcases h₂, { exact dσ _ _ _ h₁ h₂ }, { simpa using h _ _ h₁ h₂ (by simp) } },
   { rcases h₂, { simpa using (h _ _ h₂ h₁ (by simp)).symm }, { exact dτ _ _ _ h₁ h₂ } }
end

variables [state_lang Q] [state_lang R]

def sentence.dsum (σ : sentence Γ Q ι) (τ : sentence Γ R ι) : sentence Γ (Q ⊕ R) ι :=
(word.map_q sum.inl '' σ) ∪ (word.map_q sum.inr '' τ) ∪ (sentence.fix_q (sum.inl (halt : Q)) (sum.inr (start : R)))

infix ` ⨁ `:80 := sentence.dsum

lemma sentence.dsum.deterministic {σ : sentence Γ Q ι} {τ : sentence Γ R ι}
  (proper : proper σ) (d₁ : deterministic σ) (d₂ : deterministic τ) : deterministic (σ ⨁ τ) :=
begin
  have : deterministic ((word.map_q sum.inl '' σ) ∪ (word.map_q sum.inr '' τ) : sentence Γ (Q ⊕ R) ι),
  { refine deterministic.union (deterministic.map_q (sum.inl_injective) d₁) (deterministic.map_q (sum.inr_injective) d₂) _,
    simp, rintros ⟨v₁, w₁⟩ ⟨v₂, w₂⟩ ⟨⟨q₁, u₁⟩, q'₁, u'₁⟩ mem₁,
    simp, rintros rfl rfl ⟨⟨q₂, u₂⟩, q'₂, u'₂⟩ mem₂,
    simp, rintros rfl rfl, simp },
  refine deterministic.union this (sentence.fix_q.deterministic _ _) _,
  rintros w₁ w₂ (⟨⟨⟨q, w⟩, ⟨q', w'⟩⟩, mem, rfl⟩ | ⟨⟨⟨q, w⟩, ⟨q', w'⟩⟩, mem, rfl⟩) ⟨_, _⟩,
  { simp, rintros rfl, exfalso, simpa using proper _ _ mem },
  { simp }
end

lemma time_reductions.dsum_aux  {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {n₁ n₂ : ℕ} {m₁ : model Γ Q ι} {L : vector (line Γ) ι} {m₂ : model Γ R ι}
  (h₁ : m₁ ⟶^(n₁)[σ] ⟨halt, L⟩) (h₂ : ⟨start, L⟩ ⟶^(n₂)[τ] m₂) :
  m₁.map_q sum.inl ⟶^(n₁ + n₂ + 1)[σ ⨁ τ] m₂.map_q sum.inr :=
begin
  have h₁ : m₁.map_q sum.inl ⟶^(n₁)[σ ⨁ τ] ⟨sum.inl halt, L⟩,
  { have : m₁.map_q sum.inl ⟶^(n₁)[word.map_q (sum.inl : Q → Q ⊕ R) '' σ] ⟨sum.inl halt, L⟩,
      by simpa using h₁.map_q (sum.inl : Q → Q ⊕ R),
    refine this.of_ss (by { simp[sentence.dsum, -set.image_subset_iff], 
      refine set.subset_union_of_subset_left (set.subset_union_left _ _) _ }) },
  have h : ⟨sum.inl halt, L⟩ ⟶¹[σ ⨁ τ] ⟨sum.inr start, L⟩,
  { have : ⟨sum.inl halt, L⟩ ⟶¹[sentence.fix_q (sum.inl (halt : Q)) (sum.inr (start : R))] ⟨sum.inr start, L⟩,
      from sentence.fix_q_reduction (sum.inl halt) (sum.inr start) L,
    refine this.of_ss (by simp[sentence.dsum, -set.image_subset_iff]) },
  have h₂ :  ⟨sum.inr start, L⟩ ⟶^(n₂)[σ ⨁ τ] m₂.map_q sum.inr,
  { have : ⟨sum.inr start, L⟩ ⟶^(n₂)[word.map_q (sum.inr : R → Q ⊕ R) '' τ] m₂.map_q sum.inr,
      by simpa using h₂.map_q (sum.inr : R → Q ⊕ R),
    refine this.of_ss (by { simp[sentence.dsum, -set.image_subset_iff], 
      refine set.subset_union_of_subset_left (set.subset_union_right _ _) _ }) },
  simpa[show n₁.succ + n₂ = n₁ + n₂ + 1, by omega] using (h₁.succ h).add h₂,
end

lemma time_reductions.dsum  {σ : sentence Γ Q ι} {τ : sentence Γ R ι} {n₁ n₂ : ℕ} {L₁ L₂ L₃ : vector (line Γ) ι}
  (h₁ : ⟨start, L₁⟩ ⟶^(n₁)[σ] ⟨halt, L₂⟩) (h₂ : ⟨start, L₂⟩ ⟶^(n₂)[τ] ⟨halt, L₃⟩) :
  ⟨start, L₁⟩ ⟶^(n₁ + n₂ + 1)[σ ⨁ τ] ⟨halt, L₃⟩ :=
time_reductions.dsum_aux h₁ h₂


lemma reduction_of_fn 


end model
/--/
variables {Γ Q ι} 
def deterministic (σ : sentence Γ Q ι) : Prop := ∀ {q q₁ q₂}, q ▷ q₁ ∈ σ → q ▷ q₂ ∈ σ → q₁ = q₂

namespace deterministic
variables {σ : sentence Γ Q ι} {m₁ m₂ : model Γ Q ι}

lemma reduction (d : deterministic σ) {m m₁ m₂}
  (h₁ : m ⟶¹[σ] m₁) (h₂ : m ⟶¹[σ] m₂) : m₁ = m₂ :=
begin
  rcases h₁ with ⟨_, q₁, z₁, w₁⟩,
  rcases h₂ with ⟨_, q₂, z₂, w₂⟩,
  have : q₁ = q₂ ∧ z₁ = z₂, by simpa using d w₁ w₂,
  rcases this with ⟨rfl, rfl, rfl⟩,
  refl
end

lemma time_reductions (d : deterministic σ) {m m₁ m₂} {s} (h₁ : m ⟶^(s)[σ] m₁) (h₂ : m ⟶^(s)[σ] m₂) :
  m₁ = m₂ :=
begin
  induction s with s IH generalizing m₁ m₂,
  { rcases h₁, rcases h₂, refl },
  { rcases h₁ with (_ | ⟨_, _, m₁₁, _, h_₁₁, h₁₁_₁⟩),
    rcases h₂ with (_ | ⟨_, _, m₂₁, _, h_₂₁, h₂₁_₂⟩),
    have : m₁₁ = m₂₁, from IH h_₁₁ h_₂₁, rcases this with rfl,
    exact reduction @d h₁₁_₁ h₂₁_₂ }
end

end deterministic

namespace TM
variables [state Q] 

instance : inhabited (tape (language Γ)) := ⟨⟨λ n, match n with | 0 := ␤ | (n + 1) := ␣ end, 0⟩⟩

@[simp] lemma tape.default_head : (default : tape (language Γ)).head = 0 := rfl

@[simp] lemma tape.default_tape_0 : (default : tape (language Γ)).tape 0 = ␤ := rfl

@[simp] lemma tape.default_tape_gt0 {n} (h : n > 0) : (default : tape (language Γ)).tape n = ␣ :=
by { cases n, { simp at h, contradiction }, { refl } }

instance : inhabited (model (language Γ) Q ι) := ⟨⟨vector.repeat default ι, state.start⟩⟩

@[simp] lemma model.default_state : (default : model (language Γ) Q ι).state = state.start := rfl

@[simp] lemma model.default_lines : (default : model (language Γ) Q ι).lines = vector.repeat default ι := rfl

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
(Q_state : state Q)
(σ : sentence (language Γ) Q ι.succ.succ)
(reduction : ∀ (X : list Γ), 
  ⟨⟨tape_of X, 0⟩ ::ᵥ vector.repeat default ι.succ, state.start⟩ ⟶^(≤ T X.length)[σ]↓
  ⟨vector.concat (vector.repeat default ι.succ) ⟨tape_of (f X), 0⟩, state.halt⟩)

structure time_bounded_computable_by_TM (f : list Γ → list Γ) (T : ℕ → ℕ) :=
(Q : Type*)
(Q_fin : finite Q)
(Q_state : state Q)
(σ : sentence (language Γ) Q ι.succ.succ)
(deterministic : deterministic σ)
(reduction : ∀ (X : list Γ), 
  ⟨⟨tape_of X, 0⟩ ::ᵥ vector.repeat default ι.succ, state.start⟩ ⟶^(≤ T X.length)[σ]↓
  ⟨vector.concat (vector.repeat default ι.succ) ⟨tape_of (f X), 0⟩, state.halt⟩)




variables {σ : sentence (language Γ) Q ι.succ}
/--/



structure time_bounded_computable_by_TM (f : list Γ → list Γ) (T : ℕ → ℕ) :=
(Q : Type*)
(Q_fin : finite Q)
(Q_inhabited : inhabited Q)
(σ : sentence (language Γ) Q ι.succ)
(deterministic : deterministic σ)
(reduction : ∀ (X : list Γ), encode X ⟶^(≤ T X.length)[σ]↓ encode (f X))

def time_bounded_computable_by_TM (f : list Γ → list Γ) (T : ℕ → ℕ) : Prop :=
  ∃ (c : ℕ) (Q : Type*) [fintype Q] (σ : sentence (language Γ) (state Q) (indexical empty) TM.tape)
  deterministic σ ∧
  ∀ (X : list Γ), ∃ (m : model (language Γ) (state Q) (indexical empty) TM.tape),
  is_terminal (f X) m ∧ (initial X ⟶^(≤ c * T X.length)[σ]↓ m)

lemma constant_computable_by_c : time_bounded_computable_by_TM (λ x : list bool, []) (λ ι, 0) :=
begin
  refine ⟨1, empty, fintype_of_option, ∅, by { intros _, simp }, λ X, _⟩,
  simp, refine ⟨_, 0, by refl, _⟩,
  { intros _ h,
    exfalso,
    rcases h with ⟨_, _, _, _, _, h⟩,
    exact h },
  {  }
end

end TM

end turing_machine
8