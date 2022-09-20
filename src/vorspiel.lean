import tactic data.vector data.vector3 data.vector.zip init.data.nat.basic init.data.nat.div

universes u v

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

lemma reverse_nth (l : list α) {i j} (h : i + j + 1 = l.length) : l.reverse.nth i = l.nth j :=
by { induction l with a l IH generalizing i j, { simp },
  { simp, rcases j,
    { simp, rw[show i = l.reverse.length, by simpa using h, list.nth_concat_length] },
    { simp at h ⊢, rw list.nth_append, exact IH (by omega), { simp, omega } } } }

lemma reverse_nth_le (l : list α) {i j hi hj} (h : i + j + 1 = l.length) : l.reverse.nth_le i hi = l.nth_le j hj :=
option.some_inj.mp (by { rw [←list.nth_le_nth, ←list.nth_le_nth], exact reverse_nth l h })

end list

namespace vector
variables {α β γ δ : Type*}

section
variables {α} {n : ℕ}

def concat : vector α n → α → vector α n.succ
| ⟨l, h⟩ a := ⟨l.concat a, by simp[h]⟩

end

section zip_with3

variables {α β γ δ} {n : ℕ} (f : α → β → γ → δ)

def zip_with3 (v₁ : vector α n) (v₂ : vector β n) (v₃ : vector γ n) : vector δ n :=
@vector.zip_with (α × β) γ δ n (λ p z, f p.1 p.2 z) (vector.zip_with (λ x y, (x, y)) v₁ v₂) v₃

@[simp] lemma zip_with3_nth (v₁ : vector α n) (v₂ : vector β n) (v₃ : vector γ n) (i) :
  (vector.zip_with3 f v₁ v₂ v₃).nth i = f (v₁.nth i) (v₂.nth i) (v₃.nth i) :=
by simp [vector.zip_with3]

end zip_with3

section sim_update_nth
variables {α} {n m : ℕ}

def sim_update_nth (v : vector (vector α n) m) (i : vector (fin n) m) (a : vector α m) : vector (vector α n) m :=
vector.zip_with3 (λ d i b, vector.update_nth d i b) v i a 

@[simp] lemma nth_sim_update_nth {V : vector (vector α n) m} {I : vector (fin n) m} {A : vector α m} {i} :
  ((sim_update_nth V I A).nth i).nth (I.nth i) = A.nth i :=
by simp[sim_update_nth]

lemma nth_sim_update_nth_of_ne {V : vector (vector α n) m} {I : vector (fin n) m} {A : vector α m} (i) {k} (h : I.nth i ≠ k) :
  ((sim_update_nth V I A).nth i).nth k = (V.nth i).nth k :=
by simp[sim_update_nth]; exact nth_update_nth_of_ne h _

lemma nth_sim_update_nth_if {V : vector (vector α n) m} {I : vector (fin n) m} {A : vector α m} (i) {k} :
  ((sim_update_nth V I A).nth i).nth k = if I.nth i = k then A.nth i else (V.nth i).nth k :=
by { by_cases C : I.nth i = k, { simp[←C] }, { simp[C, nth_sim_update_nth_of_ne] } }

end sim_update_nth

section rep
variables {α} (n : ℕ)

abbreviation rep (a : α) {n} : vector α n := repeat a n

end rep

lemma reverse_nth {n} (v : vector α n) {i j : fin n} (h : ↑i + ↑j + 1 = n) : v.reverse.nth i = v.nth j :=
by { rcases v with ⟨v, hv⟩, simp[reverse, nth], refine v.reverse_nth_le (by simp[hv, h]) }

end vector

namespace fin
variables (n : ℕ)

def max : fin n.succ := ⟨n, lt_add_one n⟩

def succ' : fin n → fin n
| ⟨i, hi⟩ := if h : i.succ < n then ⟨i.succ, h⟩ else ⟨i, hi⟩

variables {n}

lemma max_succ_top : (n : fin n.succ) = ⊤ :=
by { ext, rw fin.coe_coe_of_lt, { refl }, { exact lt_add_one n } }

lemma coe_top : ((⊤ : fin n.succ) : ℕ) = n := by refl

lemma lt_top_iff {i : fin n.succ} : i < ⊤ ↔ ↑i < n :=
by rcases i; simp[fin.lt_def]; refl

end fin

namespace finset
variables {α : Type*}

section
variables [decidable_eq α] {n : ℕ} (s : fin n → α)

def of_fn : finset α := (list.of_fn s).to_finset

@[simp] lemma of_fun_card : (of_fn s).card ≤ n :=
by simpa[of_fn] using list.to_finset_card_le (list.of_fn s)

end

section
variables [decidable_eq α] {ι : Type*} [fintype ι] (s : ι → α)

def cod (s : ι → α) : finset α := (univ : finset ι).image s

lemma mem_cod_iff {x} : x ∈ cod s ↔ ∃ i, s i = x := by simp[cod]

@[simp] lemma codomain_mem_cod {x} : s x ∈ cod s := by simp[cod]

lemma cod_card : (cod s).card ≤ fintype.card ι := by { simp[cod], sorry }

end 
end finset

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

lemma one_iff : power r 1 x y ↔ r x y :=
⟨by { rintros (_|⟨_, _, z, _, ⟨⟩, h⟩), exact h }, by { rintros h, exact (power.zero x).succ h }⟩

lemma deterministic {n} (d : deterministic r) : deterministic (power r n) :=
by { induction n with n IH, { rintros x y z ⟨⟩ ⟨⟩, refl },
     { rintros x y z (_ | ⟨_, _, v, _, hxv, rvy⟩) (_ | ⟨_, _, w, _, hxw, rwz⟩),
     have : v = w, from IH x v w hxv hxw, rcases this with rfl,
     refine d v y z rvy rwz } }

lemma succ_inv {k : ℕ} : r x y → power r k y z → power r k.succ x z := λ h hp,
by { have : power r 1 x y, by simp[one_iff, h],
     simpa[show 1 + k = k.succ, by omega] using this.add hp }

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

section complete_lattice
variables {ι₁ : Sort*} {ι₂ : Sort*} {κ : ι₁ → ι₂ → Sort*} {α : Type*} [complete_lattice α]

lemma le_supr₃ {f : Π i j, κ i j → α} (i : ι₁) (j : ι₂) (k : κ i j) : f i j k ≤ ⨆ i j k, f i j k :=
le_supr_of_le i $ le_supr_of_le j $ le_supr (f i j) k

end complete_lattice

namespace set
variables {ι₁ : Sort*} {ι₂ : Sort*} {κ : ι₁ → ι₂ → Sort*} {α : Type*}

lemma subset_Union₃ {f : Π i j, κ i j → set α} (i : ι₁) (j : ι₂) (k : κ i j) : f i j k ⊆ ⋃ i j k, f i j k :=
@le_supr₃ _ _ _ _ _ f i j k

end set


