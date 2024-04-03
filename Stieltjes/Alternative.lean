import Mathlib
import Mathlib.Tactic
import Mathlib.Data.Fintype.Prod

open Real Topology Interval NonemptyInterval BigOperators Fintype

set_option autoImplicit false

open scoped Classical
noncomputable section

/-- A nonempty interval -/
@[ext 990]
structure MyInterval where
  (lower upper : ℝ)
  (lower_lt_upper : lower < upper)

#check MyInterval
#check MyInterval.mk 2 3 (by linarith)

attribute [simp] MyInterval.lower_lt_upper

namespace MyInterval

variable (I J : MyInterval)

instance : Inhabited (MyInterval) :=
  ⟨⟨0, 1, zero_lt_one⟩⟩

instance : Membership ℝ (MyInterval) :=
⟨fun x I ↦ x ∈ Set.Ioc I.lower I.upper⟩

theorem mem_def (I : MyInterval) (x : ℝ) : x ∈ I ↔ x ∈ Set.Ioc I.lower I.upper := by rfl

instance CoeSet : Coe (MyInterval) (Set ℝ) := ⟨λ I ↦ {x | x ∈ I}⟩

--theorem eq_iff (I J : MyInterval) : I = J ↔ (I : Set ℝ) = J := by sorry

@[ext]
theorem eq_iff' (I J : MyInterval) (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J:= by
  simp [mem_def] at h
  sorry
  done

instance : LE (MyInterval) :=
  ⟨fun I J ↦ ∀ ⦃x⦄, x ∈ I → x ∈ J⟩

@[simp]
theorem le_def : I ≤ J ↔ ∀ x ∈ I, x ∈ J := Iff.rfl

instance partialOrder : PartialOrder (MyInterval) where
  le := (· ≤ ·)
  le_refl := by
    simp
    done
  le_trans := by
    intro I J K hIJ hJK
    simp at hIJ hJK
    tauto
  le_antisymm := by
    intro I J hIJ hJI
    simp at hIJ hJI
    ext x
    tauto


def Disjoint (I J : MyInterval) : Prop := (I : Set ℝ) ∩ J = ∅

def Closure (I: MyInterval) := Set.Icc I.lower I.upper

end MyInterval

structure Prepartition (I : MyInterval) where
  intervals : Finset MyInterval
  le_of_mem' : ∀ J ∈ intervals, J ≤ I
  pairwiseDisjoint : Set.Pairwise (↑intervals) (MyInterval.Disjoint)

namespace Prepartition

variable {I : MyInterval}

instance : Membership MyInterval (Prepartition I):=
  ⟨fun J P ↦ J ∈ P.intervals⟩

theorem injective_intervals : Function.Injective (intervals : Prepartition I → Finset (MyInterval)) := by
  rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂)
  rfl

@[simp]
def single (I J : MyInterval) (h : J ≤ I) : Prepartition I :=
  ⟨{J}, by simpa, by simp⟩

/--
A Prepartition of an interval I is a Partition if it covers all of I
-/
def isPartition (P : Prepartition I) : Prop :=
  ∀ x ∈ I, ∃ J ∈ P, x ∈ J

instance : LE (Prepartition I) :=
  ⟨fun P P' => ∀ ⦃I⦄, I ∈ P → ∃ I' ∈ P', I ≤ I'⟩

instance partialOrder : PartialOrder (Prepartition I) where
  le := (· ≤ ·)
  le_refl := by
    intro P
    intro I hI
    use I

  le_trans := sorry
  le_antisymm := sorry

instance : OrderTop (Prepartition I) where
  top := single I I (by tauto)
  le_top := by
    intro P
    intro J hJ
    use I
    constructor
    · simp
      constructor
      done
    · apply Prepartition.le_of_mem' P J hJ
      done


structure TaggedPrepartition (I : MyInterval) extends Prepartition I where
  tag : MyInterval → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ I.Closure

def Darboux (f : ℝ → ℝ) (α : ℝ → ℝ) (P : TaggedPrepartition I) :=
  ∑ I in P.intervals, f (P.tag I) * (I.upper - I.lower)

theorem Darboux_const (c : ℝ) (α : ℝ → ℝ) (P : TaggedPrepartition I) :
  Darboux (λ x : ℝ ↦ c) α P = c * (α I.upper - α I.lower) := by
  sorry
