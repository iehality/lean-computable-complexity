import tactic

universes u v

namespace turing_machine

structure graph :=
(vertices : Type u)
(edge : Type)
(map : edge → vertices → vertices → Prop)

@[notation_class] class language (α : Type u) := (blank : α) (start : α)

instance : language bool := ⟨ff, tt⟩

notation `␣` := language.blank 
notation `␤` := language.start 

class tape_class (α : Type u) := (input : α) (output : α)

variables
  (σ : Type) [language σ] -- 言語
  (κ : Type) [inhabited κ] -- 状態
  (η : Type) [tape_class η] -- ヘッド
  (π : graph) -- グラフ
  
inductive word
| mk : κ × (η → σ) → κ × (η → σ) × (η → π.edge) → word

infix ` ▷ `:80 := word.mk

structure model :=
(tape : η → π.vertices → σ)
(head : η → π.vertices)
(state : κ)

variables {σ κ η π} (p : set (word σ κ η π))

def model.read (m : model σ κ η π) (i : η) : σ :=
m.tape i (m.head i)

inductive reduction : model σ κ η π → model σ κ η π → Prop
| reduct : ∀ {x : η → π.edge} (m₀ m₁ : model σ κ η π), 
    (∀ i : η, π.map (x i) (m₀.head i) (m₁.head i)) →
     ⟨m₀.state, m₀.read⟩ ▷ ⟨m₁.state, λ i, m₁.tape i (m₀.head i), x⟩ ∈ p → reduction m₀ m₁
  
notation m₀ ` ⟶¹[`:60  p `]` :0 m₁ := reduction p m₀ m₁ 

def is_halt (m : model σ κ η π) : Prop := ∀ m', ¬m ⟶¹[p] m'

inductive time_bound_reduction : ℕ → model σ κ η π → model σ κ η π → Prop
| symm : ∀ m, time_bound_reduction 0 m m
| succ : ∀ {n m₀ m₁ m₂}, time_bound_reduction n m₀ m₁ → (m₁ ⟶¹[p] m₂) → time_bound_reduction (n + 1) m₀ m₂

notation m₀ ` ⟶^(` n `)[`:60  p `]` :0 m₁ := time_bound_reduction p n m₀ m₁ 

def termination (m₀ m₁ : model σ κ η π) : Prop := is_halt p m₁ ∧ (∃ n : ℕ, m₀ ⟶^(n)[p] m₁)

notation m₀ ` ⟶ᵗ ` m₁ := termination m₀ m₁

def initial (l : π.vertices → σ) : model σ κ η π :=
  { tape := λ i x, by {  },
    head := λ i, {  } }

end turing_machine
