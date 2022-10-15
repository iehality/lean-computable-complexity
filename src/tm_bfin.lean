import vorspiel lencodable tm

universes u v

open_locale big_operators

namespace turing_machine
variables
  (Γ : Type u) -- 言語
  (Q : Type v) [state_lang Q] -- 状態
  (ι : ℕ) -- テープの数

namespace blang
open instruction state_lang model
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

end turing_machine