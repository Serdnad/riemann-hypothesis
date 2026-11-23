module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubmodules

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_of_weighted {q : MRingOver S ι} {c : K → ℤ}
    (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) :
    IsMultiHomog q (fun k => (c k).toNat) := by
  by_cases h0 : q = 0
  · intro m hm
    simp [h0] at hm
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    refine (QuotPartGraded.isMultiHomog_iff q _).2 ?_
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rw [hcc]
    exact hq

theorem smul_mem_of_weighted {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    {c e : K → ℤ} (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) {m : M} (hm : m ∈ 𝓜 e) :
    q • m ∈ 𝓜 (e + c) := by
  by_cases h0 : q = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    have h := hM.2 _ e q m (isMultiHomog_of_weighted hq) hm
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open Classical in
theorem component_smul_eq_zero {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜)
    {f : MRingOver S ι} (hf : f ∈ Module.annihilator (MRingOver S ι) M) (i : K → ℤ) {e : K → ℤ} {m : M}
    (hm : m ∈ 𝓜 e) :
    ((DirectSum.decompose (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)) f i :
      MRingOver S ι)) • m = 0 := by
  set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
  set s := (DirectSum.decompose 𝒜 f).support
  have hsum : ∑ c ∈ s, ((DirectSum.decompose 𝒜 f c : MRingOver S ι)) • m = 0 := by
    rw [← Finset.sum_smul, DirectSum.sum_support_decompose 𝒜 f]
    exact Module.mem_annihilator.1 hf m
  obtain ⟨g, hg⟩ : ∃ g : (K → ℤ) → MRingOver S ι, ∀ c, g c = (DirectSum.decompose 𝒜 f c : MRingOver S ι) :=
    ⟨_, fun _ => rfl⟩
  have hgm : ∀ c, g c ∈ 𝒜 c := fun c => (hg c).symm ▸ (DirectSum.decompose 𝒜 f c).2
  simp only [← hg] at hsum
  suffices h : g i • m = 0 by rw [hg] at h; exact h
  by_cases hi : i ∈ s
  · have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero 𝓜).1 hM.1.submodule_iSupIndep
    have hinj : Set.InjOn (fun c : K → ℤ => e + c) s := fun a _ b _ h => add_left_cancel h
    have key := hind (s.image fun c => e + c)
      (fun d => g (d - e) • m)
      (by
        intro d hd
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hd
        rw [add_sub_cancel_left]
        exact smul_mem_of_weighted hM ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (hgm c)) hm)
      (by
        rw [Finset.sum_image hinj]
        simpa only [add_sub_cancel_left] using hsum)
      (e + i) (Finset.mem_image_of_mem _ hi)
    simpa only [add_sub_cancel_left] using key
  · rw [hg, DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero, zero_smul]

theorem mem_annihilator_of_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    (hq : ∀ e, ∀ m ∈ 𝓜 e, q • m = 0) : q ∈ Module.annihilator (MRingOver S ι) M := by
  refine Module.mem_annihilator.2 fun m => ?_
  have hm : m ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction 𝓜 (motive := fun x => q • x = 0) hm (fun e x hx => hq e x hx) (smul_zero q) ?_
  intro x y hx hy
  rw [smul_add, hx, hy, add_zero]

def prodSet (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) : Set M :=
  {y | ∃ (p : MRingOver S ι) (a : K → ℕ) (m : M) (c : K → ℤ), IsMultiHomog p a ∧ p ∈ P ∧ m ∈ 𝓜 c ∧ y = p • m}

theorem prodSet_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) :
    ∀ y ∈ prodSet 𝓜 P, ∃ c, y ∈ 𝓜 c := by
  rintro _ ⟨p, a, m, c, hp, -, hm, rfl⟩
  exact ⟨_, hM.2 a c p m hp hm⟩

theorem smul_top_eq_span {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)}
    (hP : IsMultiHomogIdeal P) :
    (P • ⊤ : Submodule (MRingOver S ι) M) = Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
  apply le_antisymm
  · obtain ⟨T, hT, hPT⟩ := hP
    rw [Submodule.smul_le]
    intro r hr n _
    rw [hPT] at hr
    induction hr using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha⟩ := hT t ht
      have htP : t ∈ P := hPT ▸ Ideal.subset_span ht
      have hn : n ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
      have h0 : t • (0 : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
        rw [smul_zero]
        exact Submodule.zero_mem _
      refine Submodule.iSup_induction 𝓜
        (motive := fun x => t • x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P))
        hn (fun e x hx => Submodule.subset_span ⟨t, a, x, e, ha, htP, hx, rfl⟩) h0 ?_
      intro x y hx hy
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_le]
    rintro _ ⟨p, a, m, c, -, hp, -, rfl⟩
    exact Submodule.smul_mem_smul hp Submodule.mem_top

theorem mem_iSup_span_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {x : M} (hx : x ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, (Submodule.span (MRingOver S ι) H).restrictScalars S ⊓ 𝓜 c := by
  have hx' := GradedSubquot.span_le_span_monTimes (S := S) (ι := ι) H hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := GradedSubquot.monTimes_homog hM hH hy
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.2 ⟨GradedSubquot.monTimes_subset_span H hy, hc⟩)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul s y _ hy => exact Submodule.smul_mem _ s hy

end GradedSubmodules


open GradedSubmodules in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in
open Classical in
theorem GradedSubmodules.proof : GradedSubmodules.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hM
  refine ⟨?_, fun P hP => ?_⟩
  ·
    set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
    refine ⟨{q | (∃ a, IsMultiHomog q a) ∧ q ∈ Module.annihilator (MRingOver S ι) M}, fun q hq => hq.1, ?_⟩
    apply le_antisymm
    · intro f hf
      rw [← DirectSum.sum_support_decompose 𝒜 f]
      refine Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨⟨_, isMultiHomog_of_weighted
        ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (DirectSum.decompose 𝒜 f i).2)⟩, ?_⟩
      exact mem_annihilator_of_homog hM fun e m hm => component_smul_eq_zero hM hf i hm
    · exact Ideal.span_le.2 fun q hq => hq.2
  · have hspan := smul_top_eq_span hM hP
    refine ⟨?_, ?_⟩
    · have hind1 : iSupIndep (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) :=
        GradedSubquot.iSupIndep_comap hM.1.submodule_iSupIndep
          ((P • ⊤ : Submodule (MRingOver S ι) M).subtype.restrictScalars S) (fun a b h => Subtype.ext h)
      have hsup1 : ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c = ⊤ := by
        refine eq_top_iff.mpr fun x _ => ?_
        have hx : (x : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ x.2
        have h := GradedSubquot.mem_iSup_inf hM (prodSet_homog hM P) hspan.ge x hx
        exact (show (⨆ c, ((Submodule.span (MRingOver S ι) (prodSet 𝓜 P)).comap
            (P • ⊤ : Submodule (MRingOver S ι) M).subtype).restrictScalars S ⊓
            subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c) ≤
              ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c from
          iSup_mono fun c => inf_le_right) h
      exact ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind1 hsup1,
        fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩
    · set L := (P • ⊤ : Submodule (MRingOver S ι) M) with hLdef
      set f := L.mkQ.restrictScalars S with hfdef
      have hker : LinearMap.ker f = L.restrictScalars S := by
        ext x
        simp [hfdef]
      have hind := hM.1.submodule_iSupIndep
      have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ 𝓜 c) := by
        rw [hker]
        intro x hx
        have hx' : x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ hx
        have := mem_iSup_span_inf hM (prodSet_homog hM P) hx'
        rwa [← hspan] at this
      have hind2 := GradedSubquot.iSupIndep_map_of_ker_le hind f hL
      have hsup2 : ⨆ c, quotGrading 𝓜 L c = ⊤ := by
        change ⨆ c, (𝓜 c).map f = ⊤
        rw [← Submodule.map_iSup, hM.1.submodule_iSup_eq_top, Submodule.map_top, LinearMap.range_eq_top]
        exact Submodule.mkQ_surjective L
      refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
      rintro a c p _ hp ⟨x, hx, rfl⟩
      exact ⟨p • x, hM.2 a c p x hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ClosedPtSkyscraper

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_notMem {P : Ideal (MRingOver S ι)} (hP : P.IsPrime) {J : ∀ k, Finset (ι k)}
    (hJ : ∀ k, ∀ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) {u : MRingOver S ι} (hu : u ∈ KH.cellMon S J) :
    u ∉ P := by
  induction hu using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    exact hJ k i hi
  | one => exact (Ideal.ne_top_iff_one P).mp hP.ne_top
  | mul f f' _ _ hf hf' => exact fun h => (hP.mem_or_mem h).elim hf hf'

theorem loc_eq_zero {N : Type} [AddCommGroup N] [Module (MRingOver S ι) N] {P : Ideal (MRingOver S ι)}
    (hkill : ∀ p ∈ P, ∀ n : N, p • n = 0) {J : ∀ k, Finset (ι k)}
    (hJ : ∃ k, ∃ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∈ P) (x : LocalizedModule (KH.cellMon S J) N) :
    x = 0 := by
  obtain ⟨k, i, hi, hX⟩ := hJ
  induction x using LocalizedModule.induction_on with
  | h n w =>
    rw [← LocalizedModule.zero_mk (1 : KH.cellMon S J), LocalizedModule.mk_eq]
    refine ⟨⟨X ⟨k, i⟩, Submonoid.subset_closure ⟨k, i, hi, rfl⟩⟩, ?_⟩
    simp only [one_smul, smul_zero]
    rw [Submonoid.smul_def]
    exact hkill _ hX n

end ClosedPtSkyscraper

theorem ClosedPtSkyscraper.proof (hU : ClosedPtChartUnit.Statement) : ClosedPtSkyscraper.Statement := by
  classical
  intro S _ K _ _ ι _ _ N _ _ _ _ 𝓝 P d h𝓝 hP hkill I hI y hy
  obtain ⟨m, s, a, hsa, hm, rfl⟩ := GenSESStep.locPart_normal h𝓝 hy
  have hsP : (s : MRingOver S ι) ∉ P := ClosedPtSkyscraper.cellMon_notMem hP.1.1 hI s.2

  have hcong : ∀ p q : MRingOver S ι, p - q ∈ P → ∀ n : N, p • n = q • n := fun p q h n =>
    sub_eq_zero.mp (by rw [← sub_smul]; exact hkill _ h n)

  have hinv : ∀ J : ∀ k, Finset (ι k), (∀ k, (J k).Nonempty) →
      (∀ k, ∀ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
      ∃ t ∈ KH.cellMon S J, ∃ (g : MRingOver S ι) (b : K → ℕ),
        IsMultiHomog t (a + b) ∧ IsMultiHomog g b ∧ t - g * s ∈ P :=
    fun J hne hJ => hU S K ι P hP J hne hJ s a hsa hsP
  choose t ht g b htb hgb htg using hinv
  let z : KH.CechC S ι N 0 := fun J =>
    if hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P then
      LocalizedModule.mk (g J.1 J.2.1 hJ • m) ⟨t J.1 J.2.1 hJ, ht J.1 J.2.1 hJ⟩
    else 0

  have hagree : ∀ (J : KH.Cell K ι 0) (hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P)
      (u h' t' : MRingOver S ι), u - h' * s ∈ P →
      (u * t' * g J.1 J.2.1 hJ) • m = (h' * t' * t J.1 J.2.1 hJ) • m := by
    intro J hJ u h' t' hu
    refine hcong _ _ ?_ m
    have := sub_mem (P.mul_mem_right (t' * g J.1 J.2.1 hJ) hu) (P.mul_mem_left (h' * t') (htg J.1 J.2.1 hJ))
    convert this using 1
    ring
  refine ⟨z, ⟨Submodule.mem_pi.mpr fun J _ => ?_, LinearMap.mem_ker.mpr (funext fun E => ?_)⟩, ?_⟩
  ·
    by_cases hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P
    · simp only [z, dif_pos hJ]
      refine GenSESStep.mk_mem_locPart _ _ (a + b J.1 J.2.1 hJ) (htb J.1 J.2.1 hJ) ?_
      have e : (d + fun k => ((a + b J.1 J.2.1 hJ) k : ℤ)) =
          (d + fun k => (a k : ℤ)) + fun k => (b J.1 J.2.1 hJ k : ℤ) := by
        funext k
        simp only [Pi.add_apply, Nat.cast_add]
        ring
      rw [e]
      exact h𝓝.2 _ _ _ _ (hgb J.1 J.2.1 hJ) hm
    · simp only [z, dif_neg hJ]
      exact zero_mem _
  ·
    obtain ⟨J₁, J₂, h₁, h₂, σ, -, hD⟩ := GenTwistGenerated.cechD_zero_apply (S := S) (M := N) E
    rw [Pi.zero_apply, hD z]
    by_cases hE : ∀ k, ∀ i ∈ E.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P
    · have hJ₁ : ∀ k, ∀ i ∈ J₁.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P := fun k i hi => hE k i (h₁ k hi)
      have hJ₂ : ∀ k, ∀ i ∈ J₂.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P := fun k i hi => hE k i (h₂ k hi)
      obtain ⟨u, hu, h', -, -, -, huP⟩ := hU S K ι P hP E.1 E.2.1 hE s a hsa hsP
      simp only [z, dif_pos hJ₁, dif_pos hJ₂]
      rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₁),
        GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₂)]
      have heq : LocalizedModule.mk (g J₁.1 J₁.2.1 hJ₁ • m)
            (⟨t J₁.1 J₁.2.1 hJ₁, GenTwistGenerated.cellMon_mono h₁ (ht J₁.1 J₁.2.1 hJ₁)⟩ : KH.cellMon S E.1) =
          LocalizedModule.mk (g J₂.1 J₂.2.1 hJ₂ • m)
            ⟨t J₂.1 J₂.2.1 hJ₂, GenTwistGenerated.cellMon_mono h₂ (ht J₂.1 J₂.2.1 hJ₂)⟩ := by
        refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
        simp only [Submonoid.smul_def, smul_smul]
        rw [← mul_assoc, ← mul_assoc, hagree J₁ hJ₁ u h' (t J₂.1 J₂.2.1 hJ₂) huP,
          hagree J₂ hJ₂ u h' (t J₁.1 J₁.2.1 hJ₁) huP]
        congr 1
        ring
      rw [heq, sub_self]
      exact zsmul_zero σ
    · push Not at hE
      exact ClosedPtSkyscraper.loc_eq_zero hkill hE _
  ·
    simp only [z, dif_pos hI]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_smul]
    exact (hcong _ _ (by rw [mul_comm]; exact htg I.1 I.2.1 hI) m).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace TopConstantTwistAlt

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem cxHessian_add_const (f : (Fin e → ℂ) → ℝ) (C : ℝ) (y : Fin e → ℂ) :
    cxHessian (fun y' => f y' + C) y = cxHessian f y := by
  have h : fderiv ℝ (fun y' => f y' + C) = fderiv ℝ f := funext fun _ => fderiv_add_const _
  unfold cxHessian
  rw [h]

theorem ptsIntegral_congr_add_const (P : Ideal (MRing ι)) (φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (C : Fin e → ℝ) (h : ∀ j z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → φ j z = φ' j z + C j)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral P φ g = ptsIntegral P φ' g := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      unfold maDensity
      congr 3
      funext j
      have hev : (fun y' => φ j (hγ.choose y')) =ᶠ[𝓝 y] (fun y' => φ' j (hγ.choose y') + C j) := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact h j _ hy'.2.1.1
      rw [cxHessian_congr hev, cxHessian_add_const]
    · rfl
  · rfl

theorem ptsIntegral_const_weight (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_congr fun w => ?_
    congr 1
    funext _
    unfold sheetDensity
    split_ifs <;> ring
  · ring

theorem ptsIntegral_twist_term (P : Ideal (MRing ι)) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (D i : ℕ) :
    ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (constLine c) else A) (fun _ => c) =
      c * geomDeg P A D := by
  rw [ptsIntegral_const_weight, geomDeg]
  congr 1
  refine ptsIntegral_congr_add_const P _ _ (fun j => if (j : ℕ) < i then -c else 0) (fun j z hz => ?_) _
  unfold pot
  dsimp only
  split_ifs
  · show Real.log (A.h z * Real.exp (-c)) = Real.log (A.h z) + -c
    rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]
  · simp

end TopConstantTwistAlt


open TopConstantTwistAlt in
theorem TopConstantTwist.proof : TopConstantTwist.Statement := by
  intro K _ ι _ P D A c II hII hP hA
  have h : II K ι P (D + 1) (fun _ => A.tensor (constLine c)) - II K ι P (D + 1) (fun _ => A) =
      -∑ i ∈ Finset.range (D + 1),
        ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (constLine c) else A) (fun _ => c) :=
    GroundTheory.Heights₂.Heights.Telescope.proof K ι (II K ι) (hII K ι) P D A (fun _ => c) (fun _ _ _ => rfl) hP hA
      contDiffOn_const
  simp only [ptsIntegral_twist_term, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h ⊢
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ModulePieceHilbert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J₁ J₂ : Ideal (MRing ι)) (N d : ℕ),
    IsMultiHomogIdeal J₁ → IsMultiHomogIdeal J₂ → J₂ ≤ J₁ → 0 < N →
    (∀ f ∈ J₁, (N : MRing ι) * f ∈ J₂) →
    (∀ W : Ideal (MRing ι), W.IsPrime → J₂ ≤ W → IsRelevant W →
      ringKrullDim (MRing ι ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∀ s : K → ℕ, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |Real.log (modPieceCard J₁ J₂ (a + s)) -
          (∑ᶠ W ∈ topComps J₂ d, ((multAt J₂ W : ℝ) - multAt J₁ W) * Real.log (charOf W) *
            (geoNum d W (fun _ k => (a k : ℤ)) : ℝ)) / (d.factorial : ℝ)| ≤
        C * ((∑ k, a k : ℕ) + 1 : ℝ) ^ d / ((∑ k, a k : ℕ) + 1 : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
