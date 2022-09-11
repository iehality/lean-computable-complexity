import vorspiel

universes u v

class lencodable (Γ : Type*) (α : Type*) :=
(encode [] : α → list Γ)
(decode [] : list Γ → option α)
(encodek : ∀ a, decode (encode a) = some a)

abbreviation bencodable := lencodable bool

notation `⸤`x`⸥` := lencodable.encode bool x

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

notation `∥`a`∥` := length bool a

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

class lfin (Γ : Type*) (α : Type*) extends lencodable Γ α :=
(entropy [] : ℕ)
(entropy_ne_zero : entropy ≠ 0)
(length : ∀ a : α, lencodable.length Γ a = entropy)

attribute [simp] lfin.length lfin.entropy_ne_zero

namespace lfin
variables {Γ : Type*} {α : Type*} [lfin Γ α]
@[simp] lemma length' : ∀ a : α, (lencodable.encode Γ a).length = lfin.entropy Γ α := lfin.length 

@[simp] lemma length_encode : list.length ∘ (lencodable.encode Γ : α → list Γ) = (λ _, lfin.entropy Γ α) := funext (by simp)

end lfin

namespace lencodable
open lfin
variables (Γ : Type*) (Δ : Type*) (E : Type*)

instance : lfin Γ Γ := ⟨1, by simp, by simp[length]⟩

def trans [lencodable Δ Γ] [lfin E Δ] : lencodable E Γ :=
{ encode := λ x, (encode Δ x).bind (encode E),
  decode := λ d, decode Γ ((d.to_chunks (lfin.entropy E Δ)).filter_map (decode Δ)),
  encodek := λ x, by { 
    have : ((encode Δ x).bind (encode E)).to_chunks (lfin.entropy E Δ) = (encode Δ x).map (encode E),
    from list.join_to_chunks (by simp) (by simp), 
    have : (list.map (encode E) (encode Δ x)).filter_map (decode Δ) = encode Δ x, by simp[list.filter_map_map],
    simp* } }

def trans_lfin [lfin Δ Γ] [lfin E Δ] : lfin E Γ :=
{ entropy := entropy E Δ * entropy Δ Γ,
  entropy_ne_zero := by simp,
  length := λ x, by { show ((encode Δ x).bind (encode E)).length = entropy E Δ * entropy Δ Γ, by simp },
  .. trans Γ Δ E }


end lencodable

namespace nat
attribute [simp] bit_zero bodd_bit div2_bit nat.div2_one nat.div2_two

@[simp] lemma bit_tt_zero : bit tt 0 = 1 := rfl

def to_dibit : ℕ → 𝔹 := binary_rec [] (λ b n d, b :: d)
-- 逆順の二進数表示
-- 注意 to_dibit 0 = []

def to_dibit_inv : 𝔹 → ℕ
| [] := 0
| (b :: d) := bit b (to_dibit_inv d)

@[simp] lemma bit_bodd {b n} : (bit b n).bodd = b :=
by cases b; simp[bit]

@[simp] lemma to_dibit_bit_0 : to_dibit 0 = [] := by simp[to_dibit]

@[simp] lemma to_dibit_bit_1 : to_dibit 1 = [tt] :=
by { unfold to_dibit binary_rec, simp, rw nat.div2_one, simp }

@[simp] lemma to_dibit_bit {b n} (h : bit b n ≠ 0) : to_dibit (bit b n) = b :: to_dibit n :=
begin
  suffices : dite (bit b n = 0) (λ _, []) _ = b :: to_dibit n,
  { unfold to_dibit binary_rec at this ⊢, exact this },
  simp[h], rw nat.div2_bit b n, refl
end

@[simp] lemma to_dibit_inv_to_divit : ∀ n, to_dibit_inv (to_dibit n) = n :=
binary_rec (by simp[to_dibit, to_dibit_inv])
(λ b n h, by { by_cases hn : bit b n = 0; simp[hn, to_dibit_inv, h] })

instance : bencodable ℕ :=
{ encode := to_dibit,
  decode := λ d, some (to_dibit_inv d),
  encodek := by simp }

def log2 : ℕ → ℕ := log 2

lemma encode_bit {b n} (h : bit b n ≠ 0) : ⸤bit b n⸥ = b :: ⸤n⸥ := to_dibit_bit h

@[simp] lemma encode_0 : ⸤(0 : ℕ)⸥ = [] := to_dibit_bit_0

@[simp] lemma encode_1 : ⸤(1 : ℕ)⸥ = [tt] := to_dibit_bit_1

lemma dibit_length : ∀ n, n ≠ 0 → ∥n∥ = log 2 n + 1 :=
binary_rec (by simp)
(λ b n h, by {
  by_cases hn : n = 0; simp[lencodable.length, hn] at h ⊢,
  { rcases b; simp },
  { intros nezero, simp [encode_bit nezero],
    have : log 2 n + 1 = log 2 (bit b n),
      calc log 2 n + 1 = log 2 (bit b n / 2) + 1
        : by rw (show bit b n / 2 = n, by simpa[nat.div2_val] using div2_bit b n)
                   ... = log 2 (bit b n)
        : by { symmetry, refine nat.log_of_one_lt_of_le (by simp) (by rcases b; simp[bit, one_le_iff_ne_zero.mpr hn]) },
    simpa[this] using h } }) 

end nat