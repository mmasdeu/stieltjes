import Mathlib.Tactic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval

open Real Topology Interval NonemptyInterval BigOperators Fintype

set_option autoImplicit false

open scoped Classical
noncomputable section

example (a:ℝ)(h: a< a): False := by exact (lt_self_iff_false a).mp h 

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

theorem le_lower_non_mem (I : MyInterval) (x:ℝ) (h:x ≤ I.lower): x ∉ I := by 
  by_contra H 
  rw [mem_def] at H 
  exact ((lt_iff_not_ge I.lower x).mp H.1 ) h 

theorem gt_upper_non_mem (I : MyInterval) (x:ℝ) (h: I.upper < x): x ∉ I := by 
  by_contra H 
  rw [mem_def] at H 
  exact ((lt_iff_not_ge I.upper x).mp h) H.2  

instance CoeSet : Coe (MyInterval) (Set ℝ) := ⟨λ I ↦ {x | x ∈ I}⟩

--theorem eq_iff (I J : MyInterval) : I = J ↔ (I : Set ℝ) = J := by sorry

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

@[ext]
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

theorem lower_lt_upper (P : Prepartition I) (J: MyInterval)(h : J ∈ P.intervals): J.lower < I.upper := by
  have := ((MyInterval.le_extr J I).mp (P.le_of_mem' J h)).1
  exact gt_of_ge_of_gt this (J.lower_lt_upper)

section

variable (P : Prepartition I) (J1 J2 : MyInterval) (hJ1: J1 ∈ P.intervals)(hJ2: J2 ∈ P.intervals) 

theorem eq_if_common_point (x:ℝ) (hx1: x ∈ J1 )(hx2: x ∈ J2 ) : J1 = J2 := by 
  by_contra H 
  have ex : x∈ (J1 : Set ℝ)∩J2 := Set.mem_inter hx1 hx2 
  rw [ P.pairwiseDisjoint hJ1 hJ2 H ] at ex 
  exact ex 

theorem eq_if_le (h : J1 ≤ J2) : J1 = J2 := by 
  by_contra H 
  have ex1 : J1.upper ∈ J1 := MyInterval.upper_mem J1
  have ex :  J1.upper ∈ (J1 : Set ℝ) ∩ J2 :=Set.mem_inter ex1 (h ex1)
  rw [ P.pairwiseDisjoint hJ1 hJ2 H ] at ex 
  exact ex 

theorem eq_if_eq_lower (hl : J1.lower = J2.lower) : J1 = J2 := by 
  rcases le_or_gt J1.upper J2.upper with h | h
  · have: J1 ≤ J2:= (MyInterval.le_extr J1 J2).mpr ⟨h, le_of_eq hl.symm⟩
    exact eq_if_le P J1 J2 hJ1 hJ2 this 
  · have: J2 ≤ J1:= (MyInterval.le_extr J2 J1).mpr ⟨le_of_lt h, le_of_eq hl⟩
    exact (eq_if_le P J2 J1 hJ2 hJ1 this).symm 

theorem eq_if_lower_lt_upper (h1: J1.lower < J2.upper) (h2: J2.lower < J1.upper): J1 = J2 := by 
  rcases le_or_gt J1.upper J2.upper with h | h
  · have ex : J1.upper ∈ J2 := 
    (MyInterval.mem_def J2 J1.upper).mp ⟨ h2, h ⟩  
    exact (eq_if_common_point P J1 J2 hJ1 hJ2 J1.upper (MyInterval.upper_mem J1) ex)
  · have ex : J2.upper ∈ J1 :=  
      (MyInterval.mem_def J1 J2.upper).mp ⟨ h1, le_of_lt h ⟩  
    exact (eq_if_common_point P J2 J1 hJ2 hJ1 J2.upper (MyInterval.upper_mem J2) ex).symm

theorem lower_eq_upper_if_lower_in (hl : J1.lower ∈ J2): J1.lower = J2.upper := by 
  have hle : J1.lower ≤  J2.upper := ((MyInterval.mem_def J2 J1.lower).mp hl).2 
  have hge : J1.lower ≥ J2.upper := by 
    by_contra H
    rcases lt_or_ge J2.lower J1.upper with h | h
    · have ee := eq_if_lower_lt_upper P J2 J1 hJ2 hJ1 h (lt_of_le_not_le hle H)
      rw [ee] at hl 
      have cc := ((MyInterval.mem_def J1 J1.lower).mp hl).1 
      exact (lt_self_iff_false J1.lower).mp cc
    · have ll := le_of_lt (gt_of_ge_of_gt h J1.lower_lt_upper)
      exact (J2.le_lower_non_mem J1.lower ll) hl
  exact le_antisymm hle hge
  
end

@[simp]
def single (I J : MyInterval) (h : J ≤ I) : Prepartition I :=
  ⟨{J}, by simpa, by simp⟩

theorem eq (P P' : Prepartition I): P = P' ↔  ∀ ⦃I⦄, I ∈ P ↔ I ∈ P' := by
  constructor 
  · intro h I
    exact Eq.to_iff (congrArg (Membership.mem I) h)
  · intro h 
    rw [@Prepartition.ext_iff]
    exact Finset.ext_iff.mpr h


/--
A Prepartition of an interval I is a Partition if it covers all of I
-/
def isPartition (P : Prepartition I) : Prop :=
  ∀ x ∈ I, ∃ J ∈ P, x ∈ J

theorem isPartition_nonempty (P : Prepartition I)(h : P.isPartition):
    ∃ J: MyInterval, J ∈ P := by 
  let ⟨ J, hJ1, _⟩ := h I.upper (MyInterval.upper_mem I)
  use J 

instance : LE (Prepartition I) :=
  ⟨fun P P' => ∀ ⦃I⦄, I ∈ P → ∃ I' ∈ P', I ≤ I'⟩

lemma blah (P: Prepartition I)(Q: Prepartition I)(hPQ: P ≤ Q)(hQP: Q ≤ P)(J: MyInterval)(h: J∈ P): 
    J∈ Q:= by
  obtain ⟨I',hI1,hI2⟩ := hPQ h
  obtain ⟨J',hJ1,hJ2⟩ := hQP hI1 
  have hJJ' : J≤ J' := fun {x} a => hJ2 (hI2 a)
  have hJJ': J=J' := eq_if_le P J J' h hJ1 hJJ'
  have : I'= J := MyInterval.partialOrder.le_antisymm I' J (hJJ'▸ hJ2) hI2 
  exact (MyInterval.partialOrder.le_antisymm I' J (hJJ'▸ hJ2) hI2) ▸ hI1 

instance partialOrder : PartialOrder (Prepartition I) where
  le := (· ≤ ·)
  le_refl := by
    intro P
    intro I hI
    use I
  le_trans := by 
    intro a b c hab hbc 
    intro J hJ 
    obtain ⟨ I', hI1,hI2⟩ := hab hJ 
    obtain ⟨ J', hJ1,hJ2⟩ := hbc hI1 
    use J' 
    exact ⟨hJ1, fun a => hJ2 (hI2 a) ⟩   
  le_antisymm := by 
    intro a b hab hba 
    rw [eq]
    intro J 
    have blah (a b: Prepartition I)(hab: a ≤ b)(hba: b ≤ a)(hJ: J∈ a):  J∈ b:= by 
      obtain ⟨I',hI1,hI2⟩ := hab hJ
      obtain ⟨J',hJ1,hJ2⟩ := hba hI1 
      have hJJ' : J≤ J' := fun {x} a => hJ2 (hI2 a)
      have hJJ': J=J' := eq_if_le a J J' hJ hJ1 hJJ'
      have : I'= J := MyInterval.partialOrder.le_antisymm I' J (hJJ'▸ hJ2) hI2 
      exact (MyInterval.partialOrder.le_antisymm I' J (hJJ'▸ hJ2) hI2) ▸ hI1 
    constructor 
    · intro hJ
      exact blah a b hab hba hJ
    · intro hJ 
      exact blah b a hba hab hJ

instance : OrderTop (Prepartition I) where
  top := single I I (by tauto)
  le_top := by
    intro P
    intro J hJ
    use I
    constructor
    · exact  Finset.singleton_subset_iff.mp fun ⦃I⦄ I => I
    · exact P.le_of_mem' J hJ

theorem lower_in (P : Prepartition I)(J: MyInterval)(h: J ∈ P)(hN: I.lower< J.lower): 
    J.lower ∈ I  := by 
  have aux1 : J ≤ I:= P.le_of_mem' J h
  have aux2 : J.upper ≤ I.upper := ((MyInterval.le_extr J I).mp aux1).1 
  have aux3 : J.lower < I.upper := by exact gt_of_ge_of_gt aux2 (J.lower_lt_upper)
  rw [MyInterval.mem_def]
  exact ⟨ hN , le_of_lt aux3⟩ 




structure TaggedPrepartition (I : MyInterval) extends Prepartition I where
  tag : MyInterval → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ J.Closure

def TaggedPrepartition.isPartition (P : TaggedPrepartition I) := P.toPrepartition.isPartition

def upper : MyInterval → ℝ := fun J ↦ J.upper

def upperset (P : Prepartition I): Finset ℝ  := 
  Finset.image (Prepartition.upper) P.intervals 

theorem upperset_nonempty (P : Prepartition I)(h : P.isPartition): (upperset P).Nonempty:= by 
  rw [upperset]
  simp
  let ⟨J,hJ⟩ := isPartition_nonempty P h 
  use J 
  exact hJ 

theorem upperset_mem (P : Prepartition I) (x:ℝ)(h:x∈ (upperset P)): ∃ J ∈ P, J.upper=x :=
  Finset.mem_image.mp h

theorem upperset_mem_of_mem (P : Prepartition I) (J:MyInterval)(h:J∈ P): J.upper ∈ P.upperset:= 
  Finset.mem_image_of_mem upper h 
 
theorem upper_lower (P : Prepartition I) (J: MyInterval)(hJ: J ∈ P)(hN: J.upper< I.upper)(h : P.isPartition): 
    ∃ JJ ∈ P.intervals, J.upper = JJ.lower := sorry 

def lower : MyInterval → ℝ := fun J ↦ J.lower

def lowerset (P : Prepartition I): Finset ℝ  := 
  Finset.image (Prepartition.lower) P.intervals   

theorem lowerset_nonempty (P : Prepartition I)(h : P.isPartition): (lowerset P).Nonempty:= by 
  rw [lowerset]
  simp
  let ⟨J,hJ⟩ := isPartition_nonempty P h 
  use J 
  exact hJ 

theorem lowerset_mem (P : Prepartition I) (x : ℝ)(h : x ∈ (lowerset P)): ∃ J ∈ P, J.lower = x :=
  Finset.mem_image.mp h

theorem lowerset_lt (P : Prepartition I) (x : ℝ)(h : x ∈ (lowerset P)): x < I.lower := by 
   have (J: MyInterval)(h:J ∈ P): J.lower<I.lower := by exact?

theorem lowerset_mem_of_mem (P : Prepartition I) (J:MyInterval)(h:J∈ P): J.lower ∈ P.lowerset:= 
  Finset.mem_image_of_mem lower h 
 
theorem lower_upper (P : Prepartition I)(J: MyInterval)(hJ: J ∈ P)(hN: I.lower< J.lower)(h : P.isPartition): 
    ∃ JJ ∈ P.intervals, J.lower = JJ.upper := by 
  have hI : J.lower ∈ I  := lower_in P J hJ hN 
  let ⟨JJ, hJJ1, hJJ2⟩  := h (J.lower : ℝ) hI
  use JJ 
  exact ⟨hJJ1, lower_eq_upper_if_lower_in P J JJ hJ hJJ1 hJJ2⟩ 

theorem lower_I (P : Prepartition I)(h : P.isPartition): 
    ∃ J ∈ P, I.lower = J.lower := by 
  by_contra H 
  have HH :∀ J∈ P, I.lower< J.lower := by 
    intro J hJ 
    have h1 := ((MyInterval.le_extr J I).mp (P.le_of_mem' J hJ)).2 
    have h2: I.lower ≠ J.lower := not_and.mp (not_exists.mp H J) hJ  
    exact lt_of_le_of_ne h1 h2
  let l:=P.lowerset.min' (lowerset_nonempty P h)   
  have ex:∃ J ∈ P, J.lower = l := by 
    have :=  Finset.min'_mem (P.lowerset) (lowerset_nonempty P h)
    exact lowerset_mem P l this 
  have fo: ∀ J∈ P, l≤ J.lower:= by 
    intro J hJ 
    exact Finset.min'_le P.lowerset J.lower (lowerset_mem_of_mem P J hJ)
  have ne: ∀ J∈ P, l∉ J := fun J a => MyInterval.le_lower_non_mem J l (fo J a) 
  have HHH : ∀ J∈ P.intervals,  ∃ JJ ∈ P.intervals, J.lower = JJ.upper := 
    fun J a => lower_upper P J a (HH J a) h 
  have HHHH : ∀ J∈ P.intervals, J.lower ∈ I:= by 
    intro J hJ 
    let ⟨JJ,hJJ1,hJJ2⟩ :=HHH J hJ
    rw [hJJ2]
    exact (le_of_mem' P JJ hJJ1 ) ( MyInterval.upper_mem JJ)
  have linI : l∈ I:= by 
    let ⟨lJ,hlJ1,hlJ2⟩:= ex 
    rw [hlJ2.symm]
    exact HHHH lJ hlJ1 
  have : ¬∀ (x : MyInterval), x ∈ P →  ¬ (l ∈ x) := by 
    have:=not_forall_not.mpr (h l linI)
    simp_rw [not_and] at this 
    exact this
  exact this ne

def lower_list (P : Prepartition I):  List ℝ := (P.lowerset.sort (·≤·)) ++ [I.upper]

theorem lower_list_sorted (P : Prepartition I): P.lower_list.Sorted (·<·):= by sorry  

def upper_list (P : Prepartition I):  List ℝ := I.lower :: P.upperset.sort (·≤·)

theorem lower_list_eq_upper_list (P : Prepartition I): P.lower_list=P.upper_list := by sorry 

  


def Darboux (f : ℝ → ℝ) (α : ℝ → ℝ) (P : TaggedPrepartition I) :=
  ∑ J in P.intervals, f (P.tag J) * (α J.upper - α J.lower)

theorem Darboux_const (c : ℝ) (α : ℝ → ℝ) (P : TaggedPrepartition I) (h : P.isPartition) :
  Darboux (λ x : ℝ ↦ c) α P = c * (α I.upper - α I.lower) := by
  sorry

