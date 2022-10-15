import vorspiel

universes u v

class lencodable (Γ : Type*) (α : Type*) :=
(encode [] : α → list Γ)
(decode [] : list Γ → option α)
(encodek : ∀ a, decode (encode a) = some a)

--notation `⸤`x`⸥` := lencodable.encode bool x

attribute [simp] lencodable.encodek

namespace lencodable
variables {Γ : Type*} {α : Type*} [lencodable Γ α]

lemma encode_injective  : function.injective (@encode Γ α _)
| x y e := option.some.inj $ by rw [← @encodek Γ, e, encodek]

@[simp] lemma encode_inj {a b : α} : encode Γ a = encode Γ b ↔ a = b :=
encode_injective.eq_iff

@[simp] lemma decode_comp_encode : (decode α : list Γ → option α) ∘ (encode Γ : α → list Γ) = some :=
funext (by simp)

variables (Γ)

def length (a : α) : ℕ := (encode Γ a).length

--notation `∥`a`∥` := length bool a

instance refl : lencodable Γ Γ :=
{ encode := λ b, [b],
  decode := λ d, d.nth 0,
  encodek := by simp }

instance refll : lencodable Γ (list Γ) :=
{ encode := id,
  decode := some,
  encodek := by simp }

variables {Γ}

@[simp] lemma refl_encode (x : Γ) : encode Γ x = [x] := rfl

@[simp] lemma refl_decode_cons (x : Γ) (xs : list Γ) : decode Γ (x :: xs) = some x := rfl

@[simp] lemma refl_decode_nil : decode Γ (list.nil : list Γ) = none := rfl

instance : lencodable Γ pempty :=
{ encode := by rintros ⟨⟩,
  decode := λ _, none,
  encodek := by rintros ⟨⟩ }

end lencodable

class vencodable (Γ : Type*) (α : Type*) :=
(entropy [] : ℕ)
(encode [] : α → vector Γ entropy)
(decode [] : vector Γ entropy → option α)
(encodek : ∀ a, decode (encode a) = some a)

attribute [simp] vencodable.encodek

abbreviation bencodable := vencodable bool
abbreviation bentropy := vencodable.entropy bool

namespace vencodable
variables {Γ : Type*} {α : Type*} [vencodable Γ α]

notation `∥`α`∥` := entropy bool α

notation `⸤`x`⸥` := encode bool x

lemma encode_injective  : function.injective (@encode Γ α _)
| x y e := option.some.inj $ by rw [← @encodek Γ, e, encodek]

@[simp] lemma encode_inj {a b : α} : encode Γ a = encode Γ b ↔ a = b :=
encode_injective.eq_iff

@[simp] lemma decode_comp_encode :
  (decode : vector Γ (entropy Γ α)  → option α) ∘ (encode Γ : α → vector Γ (entropy Γ α)) = some :=
funext (by simp)

variables (Γ)

def length (a : α) : ℕ := (encode Γ a).length

instance refl : vencodable Γ Γ :=
{ entropy := 1,
  encode := λ b, ⟨[b], by simp⟩,
  decode := λ d, d.nth 0,
  encodek := λ b, by refl }

instance refll (k : ℕ) : vencodable Γ (vector Γ k) :=
{ entropy := k,
  encode := id,
  decode := some,
  encodek := by simp }

variables {Γ}

instance : vencodable Γ pempty :=
{ entropy := 0, 
  encode := by rintros ⟨⟩,
  decode := λ _, none,
  encodek := by rintros ⟨⟩ }

instance : vencodable Γ unit :=
{ entropy := 0, 
  encode := λ u, vector.nil,
  decode := λ x, some (),
  encodek := by rintros ⟨⟩; refl }

variables {α} {β : Type*} (e : β ≃ α)

def of_equiv : vencodable Γ β :=
{ entropy := entropy Γ α,
  encode := λ b, encode Γ (e.to_fun b),
  decode := λ d, (decode d).map e.inv_fun,
  encodek := λ b, by simp }

@[simp] lemma of_equiv_entropy_eq : (of_equiv e : vencodable Γ β).entropy = entropy Γ α := rfl

end vencodable

namespace nat
attribute [simp] bit_zero bodd_bit div2_bit nat.div2_one nat.div2_two
open lencodable

def dibit : ℕ → 𝔹 := binary_rec [] (λ b n d, b :: d)

namespace dibit

@[simp] lemma bit_tt_zero : bit tt 0 = 1 := rfl

-- 逆順の二進数表示
-- 注意 dibit 0 = []

def inv : 𝔹 → ℕ
| [] := 0
| (b :: d) := bit b (inv d)

@[simp] lemma bit_ff_two_mul (n : ℕ) : bit ff n = 2 * n := bit0_eq_two_mul n

@[simp] lemma bit_tt_two_mul_add_one (n : ℕ) : bit tt n = 2 * n + 1 := by simpa[bit, bit1] using bit0_eq_two_mul n

lemma inv_length_le : ∀ d : 𝔹, inv d + 1 ≤ 2^d.length
| [] := by simp[inv]
| (b :: d) := by { simp[inv],
    have IH : inv d + 1 ≤ 2^d.length, from inv_length_le d,
    calc
      bit b (inv d) + 1 ≤ 2 * (inv d) + 1 + 1 : by rcases b; simp
                    ... = 2 * (inv d + 1)     : by ring
                    ... ≤ 2 * (2^d.length)    : by simpa using IH
                    ... ≤ 2^(d.length + 1)    : by simp[pow_add, mul_comm] }

lemma inv_length_lt (d : 𝔹) : inv d < 2^d.length := succ_le_iff.mp (inv_length_le d)

@[simp] lemma bit_bodd {b n} : (bit b n).bodd = b :=
by cases b; simp[bit]

@[simp] lemma dibit_0 : dibit 0 = [] := by simp[dibit]

@[simp] lemma dibit_1 : dibit 1 = [tt] :=
by { unfold dibit binary_rec, simp, rw nat.div2_one, simp }

@[simp] lemma dibit_bit {b n} (h : bit b n ≠ 0) : dibit (bit b n) = b :: dibit n :=
begin
  suffices : dite (bit b n = 0) (λ _, []) _ = b :: dibit n,
  { unfold dibit binary_rec at this ⊢, exact this },
  simp[h], rw nat.div2_bit b n, refl
end

@[simp] lemma dibit_inv_to_divit : ∀ n, inv (dibit n) = n :=
binary_rec (by simp[dibit, inv])
(λ b n h, by { by_cases hn : bit b n = 0; simp[hn, inv, h] })

lemma dibit_length : ∀ n, n ≠ 0 → (dibit n).length = log 2 n + 1 :=
binary_rec (by simp)
(λ b n h, by {
  by_cases hn : n = 0; simp[lencodable.length, hn] at h ⊢,
  { rcases b; simp },
  { intros nezero, simp [dibit_bit nezero],
    have : log 2 n + 1 = log 2 (bit b n),
      calc log 2 n + 1 = log 2 (bit b n / 2) + 1
        : by rw (show bit b n / 2 = n, by simpa[nat.div2_val] using div2_bit b n)
                   ... = log 2 (bit b n)
        : by { symmetry, refine nat.log_of_one_lt_of_le (by simp) (by rcases b; simp[bit, one_le_iff_ne_zero.mpr hn]) },
    simpa[this] using h } }) 

@[simp] lemma dibit_length_le (n) : (dibit n).length ≤ log 2 n + 1 :=
by by_cases C : n = 0; simp[C, dibit_length]

example (n : ℕ) : bit1 n = 2* n + 1 := bit1_val n

lemma dibit_inv_append :
  ∀ d₁ d₂, inv (d₁ ++ d₂) = inv d₁ + 2^d₁.length * inv d₂
| []         d₂ := by simp[inv]
| (tt :: d₁) d₂ := by {
    have : inv (d₁ ++ d₂) = inv d₁ + 2^d₁.length * inv d₂ := dibit_inv_append d₁ d₂,
    simp[inv, this, bit, bit1_val],
    calc  2 * (inv d₁ + 2^d₁.length * inv d₂) + 1
        = 2 * inv d₁ + 2^(d₁.length + 1) * inv d₂ + 1
    : by simp[mul_add, pow_add, ←mul_assoc, mul_comm]
    ... = 2 * inv d₁ + 1 + 2^(d₁.length + 1) * inv d₂
    : by ring }
| (ff :: d₁) d₂ := by {
    have : inv (d₁ ++ d₂) = inv d₁ + 2^d₁.length * inv d₂ := dibit_inv_append d₁ d₂,
    simp[inv, this, bit, bit0_val (inv d₁ + _), bit0_val (inv d₁)], 
    show 2*(inv d₁ + 2^d₁.length * inv d₂)
       = 2*inv d₁ + 2^(d₁.length + 1) * inv d₂,
    by simp[mul_add, pow_add, ←mul_assoc, mul_comm] }

@[simp] lemma dibit_inv_repeat_ff : ∀ n, inv (list.repeat ff n) = 0
| 0       := by simp[inv]
| (n + 1) := by simp[inv, bit, dibit_inv_repeat_ff n]

@[simp] lemma dibit_inv_append_repeat (d) (n) : inv (d ++ list.repeat ff n) = inv d :=
by simp[dibit_inv_append]

def lift (d : 𝔹) {n : ℕ} (h : d.length ≤ n) : 𝕓 n := ⟨d ++ list.repeat ff (n - d.length), by simp[h]⟩

@[simp] def dibit_inv_dibit_lift (d : 𝔹) (n : ℕ) (h : d.length ≤ n) : inv (lift d h).val = inv d :=
by simp[lift]

end dibit

instance : lencodable bool ℕ :=
{ encode := dibit,
  decode := λ d, some (dibit.inv d),
  encodek := by simp }

def log2 : ℕ → ℕ := log 2

@[simp] lemma encode_0 : encode bool (0 : ℕ) = [] := dibit.dibit_0

@[simp] lemma encode_1 : encode bool (1 : ℕ) = [tt] := dibit.dibit_1

lemma dibit_length : ∀ n, n ≠ 0 → length bool n = log 2 n + 1 := dibit.dibit_length

end nat

namespace fin
open nat nat.dibit
variables {n : ℕ}

def bencode (i : fin n) : 𝕓 (log 2 n + 1) := 
lift (dibit i) (by {
  calc
    (dibit i).length ≤ log 2 i + 1 : dibit_length_le i
                 ... ≤ log 2 n + 1: by simp; exact log_monotone (le_of_lt i.property) })

def bdecode (d : 𝕓 (log 2 n + 1)) : option (fin n) := 
if h : inv d.val < n then some ⟨inv d.val, h⟩ else none

#eval dibit 0
#eval dibit 1
#eval dibit 2
#eval dibit 3
#eval log 2 3 + 1

instance : bencodable (fin n) :=
{ entropy := log 2 n + 1,
  encode := bencode,
  decode := bdecode,
  encodek := λ ⟨i, h⟩, by simp[bencode, bdecode, dibit.lift, h] }

@[simp] lemma entropy_eq : ∥fin n∥ = log 2 n + 1 := rfl

end fin

namespace vencodable
open nat
variables (α : Type*) [fintype α]

noncomputable def of_fin : bencodable α := of_equiv (fintype.equiv_fin α)

lemma of_fin_entropy_eq : (of_fin α : bencodable α).entropy = log 2 (fintype.card α) + 1 := rfl



end vencodable
