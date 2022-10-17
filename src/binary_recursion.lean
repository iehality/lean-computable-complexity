import vorspiel

universes u v

namespace nat

section
variables {C : nat → Sort u}

def binary_recursion
  (z : C 0)
  (f₀ : ∀ n, n ≠ 0 → C n → C (bit0 n))
  (f₁ : ∀ n, C n → C (bit1 n)) : Π n, C n :=
binary_rec z 
  (λ b, bool.cases_on b (λ n IH, if hn : n = 0 then by convert z; simp[nat.bit_ff, hn] else f₀ n hn IH) f₁)

variables {z : C 0}
  {f₀ : ∀ n, n ≠ 0 → C n → C (bit0 n)}
  {f₁ : ∀ n, C n → C (bit1 n)}

@[simp] lemma binary_recursion_zero_eq : binary_recursion z f₀ f₁ 0 = z := by simp[binary_recursion]

@[simp] lemma binary_recursion_bit1_eq (n) : binary_recursion z f₀ f₁ (bit1 n) = f₁ n (binary_recursion z f₀ f₁ n) :=
binary_rec_eq' tt n (by simp)

lemma binary_recursion_bit0_eq {n} (h : n ≠ 0) : binary_recursion z f₀ f₁ (bit0 n) = f₀ n h (binary_recursion z f₀ f₁ n) :=
begin
  rw [binary_recursion, binary_rec],
  have : bit0 n ≠ 0, from nat.bit0_ne_zero h,
  simp[this, h],
  generalize_proofs e, revert e,
  rw [bodd_bit0, div2_bit0], simp[h]
end

end

section
variables {C : nat → Sort u}

def binary_recursion_nonzero_aux
  (i : C 1)
  (f : ∀ b n, n ≠ 0 → C n → C (bit b n)) : Π b n, (n ≠ 0 → C n) → bit b n ≠ 0 → C (bit b n) :=
  (λ b n IH,
    if hn : n = 0 then 
      bool.cases_on b
        (λ nonzero, by simp[bit, hn] at nonzero; contradiction)
        (λ _, by simpa[hn] using i)
    else (λ _, f b n hn (IH hn)))

def binary_recursion_nonzero
  (i : C 1)
  (f : ∀ b n, n ≠ 0 → C n → C (bit b n)) : Π n, n ≠ 0 → C n :=
binary_rec (λ A, by contradiction) (binary_recursion_nonzero_aux i f)

variables {i : C 1} {f : ∀ b n, n ≠ 0 → C n → C (bit b n)}

@[simp] lemma binary_recursion_nonzero_one_eq {h} : binary_recursion_nonzero i f 1 h = i :=
begin
  have : binary_recursion_nonzero i f 1 = λ _, i,
  { have : binary_recursion_nonzero i f 1 = binary_recursion_nonzero_aux i f tt 0 (λ A, by contradiction),
    from binary_rec_eq (by simp; refl) tt 0,
    simpa[binary_recursion_nonzero_aux] using this },
  exact congr_fun this h
end

lemma binary_recursion_nonzero_rec_eq {n} (hn : n ≠ 0) (b) {h} :
  binary_recursion_nonzero i f (bit b n) h = f b n hn (binary_recursion_nonzero i f n hn) :=
begin
  have : binary_recursion_nonzero i f (bit b n) = λ _, f b n hn (binary_recursion_nonzero i f n hn),
  { have : binary_recursion_nonzero i f (bit b n) = binary_recursion_nonzero_aux i f b n (binary_recursion_nonzero i f n),
    from binary_rec_eq (by refl) b n,
    simpa[binary_recursion_nonzero_aux, hn] using this },
  exact congr_fun this h
end
end

end nat

open nat

def Log : ℕ → ℕ := binary_rec 0 (λ_ _, succ)

@[simp] lemma Log_zero : Log 0 = 0 := by simp[Log]

lemma Log_bit {b} {n} (h : bit b n ≠ 0) : Log (bit b n) = Log n + 1 :=
nat.binary_rec_eq' b n (by { simp, rintros rfl, rcases b; simp at h, contradiction })

lemma div2_Log {n} (h : n ≠ 0) : Log n = Log n.div2 + 1 :=
calc
  Log n = Log (bit n.bodd n.div2) : by simp
    ... = Log n.div2 + 1          : by rw Log_bit; simp[h]

@[simp] lemma Log_one : Log 1 = 1 := by simp[div2_Log]

@[simp] lemma Log_two : Log 2 = 2 := by simp[div2_Log]

lemma Log_eq_log : ∀ {n}, n ≠ 0 → Log n = log 2 n + 1 :=
binary_rec (by simp)
(λ b n h ne_zero, by {
  suffices : Log n = log 2 (bit b n), by simpa[Log_bit ne_zero] using this,
  by_cases hn : n = 0,
  { have : b = tt, by rcases b; simp[hn] at ne_zero; contradiction,
    simp[hn, this, nat.bit_tt] },
  { calc
      Log n = log 2 n + 1
    : h hn
        ... = log 2 (bit b n / 2) + 1
    : by rw (show bit b n / 2 = n, by simpa[nat.div2_val] using div2_bit b n)
        ... = log 2 (bit b n)
    : by symmetry; refine nat.log_of_one_lt_of_le (by simp) (by rcases b; simp[bit, one_le_iff_ne_zero.mpr hn]) } }) 

lemma Log_monotone : monotone Log :=
λ n m h, by { by_cases hm : m = 0,
  { have : n = 0, by simpa[hm] using h, simp[this] },
  { by_cases hn : n = 0,
    { simp[hn] },
    { simp[Log_eq_log, hn, hm], exact log_monotone h } } }

lemma pow_Log_le_poly1 : ∀ {n}, n ≠ 0 → 2^Log n ≤ 2 * n :=
binary_recursion_nonzero (by simp)
  (λ b n nonzero IH, by { 
    have : bit b n ≠ 0, by simp[bit_eq_zero_iff, nonzero],
    calc
        2^Log (bit b n) ≤ 2 * 2^Log n : by simp[Log_bit this, pow_add, mul_comm]
                    ... ≤ 2 * (2 * n) : by simpa using IH
                    ... ≤ 2 * bit b n : by simp[bit_val] })

@[simp] lemma pow_Log_le_poly1' (n) : 2^Log n ≤ 2 * n + 1 :=
by { by_cases n = 0, { simp[h] }, { exact le_add_right (pow_Log_le_poly1 h)} }