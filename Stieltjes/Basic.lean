import Mathlib
import Mathlib.Tactic
import Mathlib.Data.Fintype.Prod

open Real Topology Interval NonemptyInterval BigOperators Fintype

noncomputable section


@[ext]
structure Partition (I : NonemptyInterval ℝ) where
  carrier : Set ℝ
  finite : carrier.Finite
  contained : carrier ⊆ I
  fst : I.fst ∈ carrier
  snd : I.snd ∈ carrier

instance (P : Partition I) : Finite P.carrier := P.finite

namespace Partition

@[ext]
structure Selection (I : NonemptyInterval ℝ) extends Partition I where
  sel : ℝ → ℝ → ℝ
  loc : ∀ {t₁ t₂ : ℝ}, t₁ ∈ carrier → t₂ ∈ carrier → t₁ ≤ t₂ →
    sel t₁ t₂ ∈ Set.Icc t₁ t₂

def TrivialPartition (I : NonemptyInterval ℝ) : Partition I where
  carrier := ({I.fst, I.snd} : Set ℝ)
  finite := by simp
  contained := by
    intro x hx
    simp at hx ⊢
    rcases hx with hx | hx <;>
    · rw [hx]
      simp [mem_def]
      exact I.fst_le_snd
  fst := by simp
  snd := by simp

def Adjacent (P : Partition I) (x y : P.carrier) := x < y ∧ (P.carrier ∩ Set.Ioo x y = ∅)

instance (P : Partition I) : Fintype {⟨t₁, t₂⟩ :P.carrier × P.carrier | P.Adjacent t₁ t₂} :=
  Fintype.ofFinite _

def Intervals (P : Partition I) : Finset (P.carrier × P.carrier) :=
  {⟨t₁, t₂⟩ : P.carrier × P.carrier | P.Adjacent t₁ t₂}.toFinset

def Darboux (f : ℝ → ℝ) (α : ℝ → ℝ) (S : Selection I) :=
  ∑ a in (S.Intervals), f (S.sel a.1 a.2) * (α (a.2) - α (a.1))

theorem Darboux_const (c : ℝ) (α : ℝ → ℝ) (S : Selection I) :
  Darboux (λ x : ℝ ↦ c) α S = c * (α I.snd - α I.fst) := by
  sorry
