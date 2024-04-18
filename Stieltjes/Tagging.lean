import Stieltjes.Partition

open Real Topology Interval NonemptyInterval BigOperators Fintype Prepartition Finset
set_option autoImplicit false

open scoped Classical
noncomputable section

structure Tagging (I : MyInterval) extends Prepartition I where
  tag : MyInterval → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ J.Closure

namespace Tagging

variable {I : MyInterval}

def Darboux (f : ℝ → ℝ) (α : ℝ → ℝ) (P : Tagging I) :=
  ∑ J in P.intervals, f (P.tag J) * (α J.upper - α J.lower)

def isPartition (P : Tagging I) := P.toPrepartition.isPartition

lemma aux1 {P : Prepartition I} (f : ℝ → ℝ):
∑ x in P.intervals, f x.upper = ∑ u in P.upperset, f u := by
  simp [upperset,sum_image eq_if_eq_upper]

lemma aux2 {P : Prepartition I} (f : ℝ → ℝ):
∑ x in P.intervals, f x.lower = ∑ l in P.lowerset, f l := by
  simp [lowerset, sum_image eq_if_eq_lower]

lemma telescope {X Y : Finset ℝ} {f : ℝ → ℝ} :
∑ x in X, f x - ∑ x in Y, f x
= ∑ x in (X \ Y), f x - ∑ x in (Y \ X), f x := by
  suffices : ∑ x in X, f x +  ∑ x in (Y \ X), f x = ∑ x in (X \ Y), f x + ∑ x in Y, f x
  · linarith [this]
  simp [←sum_union disjoint_sdiff, add_comm, union_comm]

theorem Darboux_const (c : ℝ) (α : ℝ → ℝ) (P : Tagging I) (h : P.isPartition) :
  Darboux (λ _ : ℝ ↦ c) α P = c * (α I.upper - α I.lower) := by
  unfold Darboux
  simp
  calc
  _ = ∑ x in P.intervals, c * α x.upper - ∑ x in P.intervals, c * α x.lower := by
    {rw [← @Finset.sum_sub_distrib]; congr; ext t; ring}
  _ = ∑ x in P.intervals, ((c • α) ·  ) x.upper - ∑ x in P.intervals, ((c • α) · ) x.lower := by simp
  _ = ∑ u in P.upperset, c * α u - ∑ l in P.lowerset, c * α l := by {rw [aux1, aux2]; simp}
  _ = ∑ u in (P.upperset \ P.lowerset), c * α u - ∑ l in (P.lowerset \ P.upperset), c * α l := telescope
  _ = ∑ u in {I.upper}, c * α u - ∑ l in {I.lower}, c * α l := by rw [upper_minus_lower h, lower_minus_upper h]
  _ = c * (α I.upper - α I.lower) := by {simp; ring}

theorem Darboux_const' (c : ℝ) (f : ℝ → ℝ) (P : Tagging I) (h : P.isPartition) :
  Darboux f (λ _ : ℝ ↦ c) P = 0 := by sorry
