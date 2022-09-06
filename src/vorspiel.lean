import tactic data.vector data.vector3 data.vector.zip init.data.nat.basic init.data.nat.div

universes u v

namespace vector
section
variables {α : Type*} {n : ℕ}

def concat : vector α n → α → vector α n.succ
| ⟨l, h⟩ a := ⟨l.concat a, by simp[h]⟩

end

section zip_with3

variables {α β γ δ : Type*} {n : ℕ} (f : α → β → γ → δ)

def zip_with3 (v₁ : vector α n) (v₂ : vector β n) (v₃ : vector γ n) : vector δ n :=
@vector.zip_with (α × β) γ δ n (λ p z, f p.1 p.2 z) (vector.zip_with (λ x y, (x, y)) v₁ v₂) v₃

@[simp] lemma zip_with3_nth (v₁ : vector α n) (v₂ : vector β n) (v₃ : vector γ n) (i) :
  (vector.zip_with3 f v₁ v₂ v₃).nth i = f (v₁.nth i) (v₂.nth i) (v₃.nth i) :=
by simp [vector.zip_with3]

end zip_with3

end vector

namespace relation
variables {α : Type u} (r : α → α → Prop) {x y z : α}

def deterministic : Prop := ∀ x y z, r x y → r x z → y = z

inductive transitive_closure : α → α → Prop
| refl : ∀ x, transitive_closure x x
| trans' : ∀ {x y z}, transitive_closure x y → r y z → transitive_closure x z

attribute [simp, refl] transitive_closure.refl

namespace transitive_closure
variables {r}

@[trans] lemma trans (hxy : transitive_closure r x y) (hyz : transitive_closure r y z) : transitive_closure r x z :=
begin
  induction hyz,
  case refl { exact hxy },
  case trans' : _ _ _ _ ry'z' IH { exact (IH hxy).trans' ry'z' }
end

lemma of_r (h : r x y) : transitive_closure r x y := (transitive_closure.refl x).trans' h

end transitive_closure

inductive power : ℕ → α → α → Prop
| zero : ∀ x, power 0 x x
| succ : ∀ {n x y z}, power n x y → r y z → power n.succ x z

attribute [simp, refl] power.zero

namespace power
variables {r}

lemma add {n m} (hn : power r n x y) (hm : power r m y z) : power r (n + m) x z :=
by { induction m with m IH generalizing z, { rcases hm, simpa using hn },
     { rcases hm with (_ | ⟨_, _, v, _, hyv, rvz⟩), simpa using (IH hyv).succ rvz } }

lemma to_trcl {n} (h : power r n x y) : transitive_closure r x y :=
by { induction n with n IH generalizing y, { rcases h, refl }, { rcases h with (_ | ⟨_, _, v, _, hxv, rvy⟩), exact (IH hxv).trans' rvy } }

@[simp] lemma zero_iff : power r 0 x y ↔ x = y :=
⟨by { rintros ⟨⟩, refl }, by { rintros rfl, simp }⟩

lemma deterministic {n} (d : deterministic r) : deterministic (power r n) :=
by { induction n with n IH, { rintros x y z ⟨⟩ ⟨⟩, refl },
     { rintros x y z (_ | ⟨_, _, v, _, hxv, rvy⟩) (_ | ⟨_, _, w, _, hxw, rwz⟩),
     have : v = w, from IH x v w hxv hxw, rcases this with rfl,
     refine d v y z rvy rwz } }

end power

lemma trans_iff_epower : transitive_closure r x y ↔ ∃ n, power r n x y :=
⟨λ h, by { induction h with _ x y z hxy ryz IH, { refine ⟨0, by refl⟩ }, 
           { rcases IH with ⟨n, IH⟩, refine ⟨n.succ, IH.succ ryz⟩ } },
 by { rintros ⟨n, h⟩, refine h.to_trcl }⟩

def power_le (k : ℕ) (x y : α) : Prop := ∃ n ≤ k, power r n x y

namespace power_le
variables {r}

@[refl, simp] lemma refl {k : ℕ} : power_le r k x x := ⟨0, by simp⟩

lemma of_le {k l : ℕ} (le : k ≤ l) : power_le r k x y → power_le r l x y :=
by { rintros ⟨n, len, h⟩, refine ⟨n, le_trans len le, h⟩ }

lemma succ {k : ℕ} : power_le r k x y → r y z → power_le r k.succ x z :=
by { rintros ⟨n, len, hn⟩ ryz, refine ⟨n.succ, nat.succ_le_succ len, hn.succ ryz⟩ }

@[trans] lemma add {k l : ℕ} : power_le r k x y → power_le r l y z → power_le r (k + l) x z :=
by { rintros ⟨n, len, hn⟩ ⟨m, lem, hm⟩, refine ⟨ n + m, add_le_add len lem, hn.add hm⟩ }

end power_le

end relation

namespace list

notation `𝔹` := list bool

variables {α : Type*} {β : Type*}

lemma join_to_chunks {l : list (list α)} {n : ℕ} (hn : n ≠ 0) (hl : ∀ x ∈ l, length x = n) : l.join.to_chunks n = l :=
begin
  induction l with x l IH; simp,
  have : n = x.length, from (hl x (by simp)).symm,
  rcases this with rfl,
  calc to_chunks x.length (x ++ l.join) = x :: to_chunks x.length l.join
  : by simpa using list.to_chunks_eq_cons hn (by { show x ++ l.join ≠ nil, simp, rintros rfl, exfalso, simpa using hn })
                                    ... = x :: l
  : by rw show to_chunks x.length l.join = l, from IH (λ y hy, hl y (by simp[hy])),
end

end list