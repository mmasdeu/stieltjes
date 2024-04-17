import Mathlib.Tactic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval

open Real Topology Interval NonemptyInterval BigOperators Fintype

set_option autoImplicit false

open scoped Classical
noncomputable section

/-- A nonempty interval -/
@[ext 990]
structure MyInterval where
  (lower upper : ℝ)
  (lower_lt_upper : lower < upper)

namespace MyInterval

variable (I J : MyInterval)

instance : Inhabited (MyInterval) :=
  ⟨⟨0, 1, zero_lt_one⟩⟩

instance : Membership ℝ (MyInterval) :=
⟨fun x I ↦ x ∈ Set.Ioc I.lower I.upper⟩

theorem mem_def (I : MyInterval) (x : ℝ) : x ∈ I ↔ x ∈ Set.Ioc I.lower I.upper := by rfl

theorem upper_mem (I : MyInterval) : I.upper ∈ I := by
  rw[mem_def, @Set.right_mem_Ioc]
  exact I.lower_lt_upper

theorem le_lower_non_mem (I : MyInterval) (x:ℝ) (h: x ≤ I.lower):
x ∉ I := by
  intro H
  rw [mem_def] at H
  exact ((lt_iff_not_ge I.lower x).mp H.1 ) h

theorem gt_upper_non_mem (I : MyInterval) (x:ℝ) (h: I.upper < x):
x ∉ I := by
  intro H
  rw [mem_def] at H
  exact ((lt_iff_not_ge I.upper x).mp h) H.2

instance CoeSet : Coe (MyInterval) (Set ℝ) := ⟨λ I ↦ {x | x ∈ I}⟩

instance : LE (MyInterval) :=
  ⟨fun I J ↦ ∀ {x}, x ∈ I → x ∈ J⟩

@[simp]
theorem le_def (I J : MyInterval) : I ≤ J ↔ ∀ x ∈ I, x ∈ J := Iff.rfl

theorem le_extr  (I J : MyInterval) : I ≤ J ↔ I.upper ≤ J.upper ∧ J.lower ≤ I.lower :=
  (Set.Ioc_subset_Ioc_iff (I.lower_lt_upper))

@[ext]
theorem eq_iff' (I J : MyInterval) (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J:= by
  rw [MyInterval.ext_iff I J ]
  have hh1 := (le_extr I J).mp (fun {x} ↦ (h x).mp)
  have hh2 := (le_extr J I).mp (fun {x} ↦ (h x).mpr )
  exact ⟨le_antisymm_iff.mpr ⟨hh2.2, hh1.2⟩,le_antisymm_iff.mpr ⟨hh1.1, hh2.1⟩⟩

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
