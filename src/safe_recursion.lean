import tactic algebra.big_operators.fin

universes u v

open_locale big_operators



def fintype_sup {ι : Type*} [fintype ι] {α : Type*} [semilattice_sup α] [order_bot α] (f : ι → α) : α :=
  (finset.univ : finset ι).sup f

notation `⋁ ` binders `, ` r:(scoped f, fintype_sup f) := r

namespace fintype
variables {ι : Type*} [fintype ι] {α : Type*} [semilattice_sup α]  [order_bot α] (f : ι → α)

lemma le_fintype_sup {n} (f : fin n → α) (i : fin n) :
  f i ≤ ⋁ j, f j := @finset.le_sup _ _ _ _ _ f i (by simp)

@[simp] lemma fintype_fin {n} (f : fin (n + 1) → α) :
  (⋁ i : fin (n + 1), f i) = (f 0 ⊔ ⋁ i : fin n, f i.succ) :=
begin 
  refine le_antisymm_iff.mpr _, simp[fintype_sup], split,
  { intros m,
    have : m = 0 ∨ ∃ (j : fin n), m = j.succ, from fin.eq_zero_or_eq_succ m,
    rcases this with (rfl | ⟨j, rfl⟩); try {simp},
    refine le_sup_of_le_right
      (@finset.le_sup _ _ _ _ _ (λ (i : fin n), f i.succ) j (by simp)) },
  split,
  { refine le_fintype_sup f 0 },
  intros i,
  refine le_fintype_sup f _
end


end fintype


notation `𝔹` := list bool

def safe_case : vector 𝔹 3 → 𝔹
| ⟨[tt :: b, w, v], _⟩ := v
| ⟨[_, w, v], _⟩       := w


def fgegegeg (n : ℕ) : (fin n → ℕ) → vector ℕ n :=
by { exact vector.of_fn }

def safe_rec
  {m n i}
  (f  : fin i → (vector 𝔹 m → vector 𝔹 n → 𝔹))
  (g₀ : fin i → vector 𝔹 (m + 1) → vector 𝔹 (n + i) → 𝔹)
  (g₁ : fin i → vector 𝔹 (m + 1) → vector 𝔹 (n + i) → 𝔹)
   : fin i → vector 𝔹 (m + 1) → vector 𝔹 n → 𝔹
| j ⟨[]        :: w, p⟩ v := f j ⟨w, by simpa using p⟩ v
| j ⟨(ff :: x) :: w, p⟩ v := g₀ j ⟨x :: w, by simpa using p⟩
  (vector.append v (vector.of_fn $ λ k, safe_rec k ⟨x :: w, by simpa using p⟩ v : vector 𝔹 i))
| j ⟨(tt :: x) :: w, p⟩ v := g₁ j ⟨x :: w, by simpa using p⟩
  (vector.append v (vector.of_fn $ λ k, safe_rec k ⟨x :: w, by simpa using p⟩ v : vector 𝔹 i))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.2.1.head.length)⟩]}

-- f : (unsafeな引数) → (safeな引数) → 𝔹
inductive safe : Π {m n}, (vector 𝔹 m → vector 𝔹 n → 𝔹) → Prop
| const     : safe (λ (_ : vector 𝔹 0) (v : vector 𝔹 1), [])
| zero      : safe (λ (_ : vector 𝔹 0) (v : vector 𝔹 1), ff :: v.head)
| one       : safe (λ (_ : vector 𝔹 0) (v : vector 𝔹 1), tt :: v.head)
| tail      : safe (λ (_ : vector 𝔹 0) (v : vector 𝔹 1), v.head.tail)
| case      : safe (λ (_ : vector 𝔹 0) (v : vector 𝔹 3), safe_case v)
| nth (n m) : safe (λ (_ : vector 𝔹 0) (v : vector 𝔹 n), v.nth m)
| safe_comp :
  ∀ {m n} (f : vector 𝔹 m → vector 𝔹 n → 𝔹)
    {k} (g : fin m → vector 𝔹 k → vector 𝔹 0 → 𝔹)
    {l} (h : fin n → vector 𝔹 k → vector 𝔹 l → 𝔹),
    safe f → (∀ i, safe (g i)) → (∀ i, safe (h i)) →
    safe (λ (w : vector 𝔹 k) (v : vector 𝔹 l),
      f (vector.of_fn $ λ i, g i w vector.nil) (vector.of_fn $ λ i, h  i w v))
| safe_rec : 
  ∀ {m n i}
  (f  : fin i → vector 𝔹 m → vector 𝔹 n → 𝔹)
  (g₀ : fin i → vector 𝔹 (m + 1) → vector 𝔹 (n + i) → 𝔹)
  (g₁ : fin i → vector 𝔹 (m + 1) → vector 𝔹 (n + i) → 𝔹) {j},
  (∀ j, safe (f j)) → (∀ j, safe (g₀ j)) → (∀ j, safe (g₁ j)) → safe (safe_rec f g₀ g₁ j)
  

theorem bcs_poly {m n} (f : vector 𝔹 m → vector 𝔹 n → 𝔹) (H : safe f) :
  ∃ p q r : ℕ, ∀ (w : vector 𝔹 m) (v : vector 𝔹 n),
  (f w v).length ≤ p * (∑ i, (w.nth i).length)^q + (⋁ i, (v.nth i).length) + r :=
begin
  induction H,
  case const { refine ⟨0, 0, 0, _⟩, intros w v, simp },
  case zero { refine ⟨0, 0, 1, _⟩, intros w v, simp[fintype_sup] },
  case one  { refine ⟨0, 0, 1, _⟩, intros w v, simp[fintype_sup] },
  case tail { refine ⟨0, 0, 0, _⟩, intros w v, simp[fintype_sup] },
  case case { refine ⟨0, 0, 0, _⟩, intros w v,
    rcases v with ⟨(_ | ⟨b, l⟩), p⟩,
    { simp at p, contradiction },
    rcases l with (_ | ⟨w, l⟩), { simp at p, contradiction },
    rcases l with (_ | ⟨v, l⟩), { simp at p, exfalso, linarith },
    rcases l with (_ | _),
    { rcases b with (_ | ⟨B, b⟩),
      { simp[safe_case], right, left, refl },
      { rcases B; simp[safe_case],
        { right, left, refl }, { right, right, left, refl } } },
    { exfalso, simp at p, linarith } },
  case nth : n m { refine ⟨0, 0, 0, _⟩, intros w v, simp, refine fintype.le_fintype_sup _ m },
  case safe_comp : m n f k g l h safe_f safe_g safe_h IH_f IH_g IH_h
  { simp, simp at IH_g IH_h,
    rcases IH_f with ⟨p_f, q_f, r_f, IH_f⟩, refine ⟨0, 0, 0, _⟩, intros w v,
    have := IH_f (vector.of_fn $ λ i, g i w vector.nil) (vector.of_fn $ λ i, h  i w v),
    simp at this,
     }
end
  
  