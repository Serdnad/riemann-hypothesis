module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsHomogOfMemQuotPartAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle036
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc cechZc cechBc cechCc locPart quotPart Cell cellMon)

noncomputable section

theorem quotPart_eq_gradedPiece {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (hm : ∀ k, 0 ≤ m k) :
    quotPart F V m = NumbersDVR.gradedPiece V (fun k => (m k).toNat) := by
  have hset : {p : MvPolynomial (Σ k, ι k) F | (∀ k, 0 ≤ m k) ∧ IsMultiHomog p (fun k => (m k).toNat)} =
      (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) (fun k => (m k).toNat) : Set _) := by
    ext p
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_weightedHomogeneousSubmodule, hm, implies_true, true_and]
    exact (Bridge.isMultiHomog_iff p _).symm
  rw [quotPart, hset, NumbersDVR.gradedPiece]
  conv_rhs => rw [← Submodule.span_eq (weightedHomogeneousSubmodule F _ _), Submodule.map_span]
  rfl

theorem isMultiHomog_one {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRingOver S ι) 0 := by
  intro d hd k
  classical
  rw [mem_support_iff, coeff_one] at hd
  split_ifs at hd with h
  · subst h
    simp
  · exact absurd rfl hd

theorem MultiSerre.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hI : SectionMapInj.Statement) :
    MultiSerre.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hV' : IsMultiHomogIdeal V := (Bridge.isMultiHomogIdeal_iff V).mp hV
  have hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.IsMGraded F ι (quotPart F V) :=
    HilbertSamuel.QuotPartGraded.proof F K ι V hV'
  obtain ⟨-, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩, -⟩ :=
    hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  obtain ⟨c₃, h₃⟩ := hI F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  filter_upwards [eventually_ge_atTop (fun _ : K => max (max c₁ c₂) (max c₃ 0))] with m hm
  have hk : ∀ k, max (max c₁ c₂) (max c₃ 0) ≤ m k := fun k => hm k
  refine ⟨fun i hi => h₁ m i hi fun k => le_trans (by omega) (hk k), ?_⟩

  let Z := cechZc ι (quotPart F V) m 0
  have hmem : ∀ x ∈ quotPart F V m, (fun _ => LocalizedModule.mk x 1 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechC F ι
      (MvPolynomial (Σ k, ι k) F ⧸ V) 0) ∈ Z := by
    intro x hx
    refine HilbertSamuel.GenTwistGenerated.mem_cechZc_zero (fun J => ?_)
      (HilbertSamuel.GenTwistGenerated.cechD_const x)
    refine Submodule.subset_span ⟨x, 1, 0, isMultiHomog_one, ?_, rfl⟩
    convert hx using 2
    ext k
    simp
  let φ : quotPart F V m →ₗ[F] Z :=
    { toFun := fun x => ⟨fun _ => LocalizedModule.mk x.1 1, hmem x.1 x.2⟩
      map_add' := fun x y => by
        ext I
        simp
      map_smul' := fun r x => by
        ext I
        simp [LocalizedModule.smul'_mk] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hsub : x.1 - y.1 = 0 := by
      refine h₃ m (fun k => le_trans (by omega) (hk k)) _ (Submodule.sub_mem _ x.2 y.2) fun I => ?_
      have h := congrFun (congrArg Subtype.val hxy) I
      change LocalizedModule.mk x.1 1 = LocalizedModule.mk y.1 1 at h
      change LocalizedModule.mkLinearMap (cellMon F I.1) _ (x.1 - y.1) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    exact Subtype.ext (sub_eq_zero.mp hsub)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hzx⟩ := h₂ m (fun k => le_trans (by omega) (hk k)) z hz
    exact ⟨⟨x, hx⟩, Subtype.ext (funext fun I => (hzx I).symm)⟩
  have hbot : (cechBc ι (quotPart F V) m 0).comap (cechZc ι (quotPart F V) m 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  have e2 : cechHc ι (quotPart F V) m 0 ≃ₗ[F] Z := Submodule.quotEquivOfEqBot _ hbot
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_trans (by omega) (hk k)
  rw [e2.finrank_eq, ← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, NumbersDVR.hilbFn, if_pos hm0,
    quotPart_eq_gradedPiece V m hm0]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem cellD_mul_left (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ) (r : Ω)
    (t : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :
    cellD S y n (fun I => r * t I) = fun J => r * cellD S y n t J := by
  classical
  funext J
  simp only [cellD, LinearMap.pi_apply]
  split_ifs with hJ
  · simp only [LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm]
      rfl
    · simp
  · simp

theorem CellLocGlue.proof : CellLocGlue.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y G R m f u hf hu hsum hR hloc q s hs hds
  classical
  have memC : ∀ (H : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) (x : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω),
      x ∈ cellCOf S H n ↔ ∀ I, x I ∈ H I.1 := fun H n x => by
    simp [cellCOf, Submodule.mem_pi]

  let J : Ideal R :=
    { carrier := {r | ∃ t ∈ cellCOf S G q, cellD S y q t = fun I => (r : Ω) * s I}
      add_mem' := by
        rintro a b ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        refine ⟨ta + tb, Submodule.add_mem _ hta htb, ?_⟩
        rw [map_add (f := _), ha, hb]
        funext I
        simp [add_mul]
      zero_mem' := ⟨0, Submodule.zero_mem _, by funext I; simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht, hdt⟩
        refine ⟨fun I => (c : Ω) * t I, (memC _ _ _).2 fun I => hR _ _ c.2 _ ((memC _ _ _).1 ht I), ?_⟩
        rw [cellD_mul_left, hdt]
        funext I
        simp [mul_assoc] }

  have hmono : ∀ l (I : ∀ k, Finset (ι k)),
      Monotone fun n : ℕ => (G I).comap (LinearMap.mulLeft S (f l ^ n)) := by
    intro l I n n' hnn' a ha
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at ha ⊢
    have : f l ^ n' * a = f l ^ (n' - n) * (f l ^ n * a) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnn']
    rw [this]
    exact hR _ _ (pow_mem (hf l) _) _ ha
  have key : ∀ l, ∃ N : ℕ, (⟨f l, hf l⟩ : R) ^ N ∈ J := by
    intro l
    have hsl : s ∈ cellCOf S (cellLocSys G (f l)) (q + 1) := by
      rw [memC] at hs ⊢
      intro I
      exact (le_iSup (fun n : ℕ => (G I.1).comap (LinearMap.mulLeft S (f l ^ n))) 0)
        (by simpa [Submodule.mem_comap] using hs I)
    obtain ⟨t, ht, hdt⟩ := hloc l q s hsl hds
    have hn : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q, ∃ n : ℕ, f l ^ n * t I ∈ G I.1 := by
      intro I
      have h := (memC _ _ _).1 ht I
      rw [cellLocSys, Submodule.mem_iSup_of_directed _ (hmono l I.1).directed_le] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by simpa [Submodule.mem_comap] using hn⟩
    choose n hn using hn
    have : Finite (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) := by unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell; infer_instance
    have : Fintype (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) := Fintype.ofFinite _
    refine ⟨Finset.univ.sup n, fun I => f l ^ Finset.univ.sup n * t I, (memC _ _ _).2 fun I => ?_, ?_⟩
    · have := hmono l I.1 (Finset.le_sup (Finset.mem_univ I) : n I ≤ Finset.univ.sup n)
      exact this (by simpa [Submodule.mem_comap] using hn I)
    · rw [cellD_mul_left, hdt]
      funext I
      simp
  have hone : (1 : R) ∈ J := by
    have hrad : J.radical = ⊤ := by
      rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
      have h1 : (1 : R) = ∑ l, (⟨u l, hu l⟩ : R) * ⟨f l, hf l⟩ :=
        Subtype.ext (by simpa using hsum.symm)
      rw [h1]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (key l)
    rw [Ideal.radical_eq_top] at hrad
    rw [hrad]
    exact Submodule.mem_top
  obtain ⟨t, ht, hdt⟩ := hone
  exact ⟨t, ht, by rw [hdt]; funext I; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver quotPart)

noncomputable section

namespace CellLocEval

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

theorem face_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]


open Classical in
theorem cechD_apply' {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) (f : CechC S ι M n)
    (I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1)) :
    cechD S ι M n f I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        faceSign I.1 k i • cellRes S M _ I.1 (f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  simp only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

theorem cechD_mem_locPart (γ : K → ℤ) (n : ℕ) {f : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hf : f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) (I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1)) :
    cechD S ι _ n f I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) γ := by
  rw [cechD_apply']
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hc
  · have hJ : f ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ ∈ locPart ι (quotPart S (mIdealOver S y))
        (cellMon S (Function.update I.1 k ((I.1 k).erase i))) γ :=
      Submodule.mem_pi.mp hf ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ (Set.mem_univ _)
    have hm := cellRes_mem_locPart (J := Function.update I.1 k ((I.1 k).erase i)) (I := I.1)
      (cellMon_mono (face_subset I.1 k i)) γ hJ
    exact zsmul_mem hm _
  · exact Submodule.zero_mem _

theorem cechD_mem_cechCc (γ : K → ℤ) (n : ℕ) {f : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hf : f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) :
    cechD S ι _ n f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ (n + 1) :=
  Submodule.mem_pi.mpr fun I _ => cechD_mem_locPart y γ n hf I

def evC (n : ℕ) : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n →ₗ[S] (_root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  LinearMap.pi fun I => (evMap y I.1).comp (LinearMap.proj (R := S)
    (φ := fun J : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n => LocalizedModule (cellMon S J.1) (MRingOver S ι ⧸ mIdealOver S y)) I)

theorem evC_apply (n : ℕ) (w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n) (I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n) :
    evC y n w I = evMap y I.1 (w I) := rfl

theorem evC_cechD (n : ℕ) (w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n) :
    evC y (n + 1) (cechD S ι _ n w) = cellD S y n (evC y n w) := by
  funext I
  rw [evC_apply]
  by_cases hI : CellMeets y I.1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [cechD_apply', map_sum]
    simp only [cellD, LinearMap.pi_apply, hI, if_true, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hc
    · rw [map_zsmul]
      exact congrArg _ (evMap_cellRes (face_subset I.1 k i) hI _)
    · simp
  · rw [evMap_of_not y hI]
    simp only [cellD, LinearMap.pi_apply, hI, if_false, LinearMap.zero_apply]

variable (γ : K → ℤ)

theorem evC_mem (n : ℕ) {w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hw : w ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) : evC y n w ∈ cellC S y γ n := by
  refine Submodule.mem_pi.mpr fun I _ => ?_
  rw [evC_apply]
  by_cases hI : CellMeets y I.1
  · rw [← map_evMap_locPart y hI γ]
    exact Submodule.mem_map_of_mem (Submodule.mem_pi.mp hw I (Set.mem_univ _))
  · rw [evMap_of_not y hI]
    exact Submodule.zero_mem _

theorem evC_lift (n : ℕ) {w' : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω} (hw' : w' ∈ cellC S y γ n) :
    ∃ w ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n, evC y n w = w' := by
  have h : ∀ I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, ∃ x ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) γ,
      evMap y I.1 x = w' I := by
    intro I
    have hI' : w' I ∈ cellSec S y γ I.1 := Submodule.mem_pi.mp hw' I (Set.mem_univ _)
    by_cases hI : CellMeets y I.1
    · rw [← map_evMap_locPart y hI γ] at hI'
      exact Submodule.mem_map.mp hI'
    · unfold cellSec at hI'
      rw [if_neg hI, Submodule.mem_bot] at hI'
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hI']⟩
  choose w hw hφw using h
  exact ⟨w, Submodule.mem_pi.mpr fun I _ => hw I, funext hφw⟩

theorem evC_injOn (n : ℕ) :
    Set.InjOn (evC (S := S) y n) (cechCc ι (quotPart S (mIdealOver S y)) γ n) := by
  intro w hw w' hw' h
  funext I
  have h' := congrFun h I
  rw [evC_apply, evC_apply] at h'
  by_cases hI : CellMeets y I.1
  · exact evMap_injOn y hI γ (Submodule.mem_pi.mp hw I (Set.mem_univ _))
      (Submodule.mem_pi.mp hw' I (Set.mem_univ _)) h'
  · have := subsingleton_of_not (S := S) y hI
    exact Subsingleton.elim _ _

theorem evC_mem_cellZ (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechZc ι (quotPart S (mIdealOver S y)) γ n) : evC y n z ∈ cellZ S y γ n := by
  obtain ⟨hC, hK⟩ := Submodule.mem_inf.mp hz
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hK
  refine Submodule.mem_inf.mpr ⟨evC_mem y γ n hC, ?_⟩
  rw [LinearMap.mem_ker, ← evC_cechD, hK, map_zero]

theorem evC_mem_cellB (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechBc ι (quotPart S (mIdealOver S y)) γ n) : evC y n z ∈ cellB S y γ n := by
  cases n with
  | zero =>
    change z ∈ (⊥ : Submodule S _) at hz
    change evC y 0 z ∈ (⊥ : Submodule S _)
    rw [Submodule.mem_bot] at hz ⊢
    rw [hz, map_zero]
  | succ n =>
    change z ∈ (cechCc ι (quotPart S (mIdealOver S y)) γ n).map
      ((cechD S ι (MRingOver S ι ⧸ mIdealOver S y) n).restrictScalars S) at hz
    change evC y (n + 1) z ∈ (cellC S y γ n).map (cellD S y n)
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    exact Submodule.mem_map.mpr ⟨evC y n w, evC_mem y γ n hw, (evC_cechD y n w).symm⟩

theorem mem_cechBc_of (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) (h : evC y n z ∈ cellB S y γ n) :
    z ∈ cechBc ι (quotPart S (mIdealOver S y)) γ n := by
  cases n with
  | zero =>
    change evC y 0 z ∈ (⊥ : Submodule S _) at h
    change z ∈ (⊥ : Submodule S _)
    rw [Submodule.mem_bot] at h ⊢
    exact evC_injOn y γ 0 hz (Submodule.zero_mem _) (h.trans (map_zero _).symm)
  | succ n =>
    change evC y (n + 1) z ∈ (cellC S y γ n).map (cellD S y n) at h
    change z ∈ (cechCc ι (quotPart S (mIdealOver S y)) γ n).map
      ((cechD S ι (MRingOver S ι ⧸ mIdealOver S y) n).restrictScalars S)
    obtain ⟨w', hw', hd⟩ := Submodule.mem_map.mp h
    obtain ⟨w, hw, rfl⟩ := evC_lift y γ n hw'
    refine Submodule.mem_map.mpr ⟨w, hw, ?_⟩
    exact evC_injOn y γ (n + 1) (cechD_mem_cechCc y γ n hw) hz ((evC_cechD y n w).trans hd)

def evZ (n : ℕ) : cechZc ι (quotPart S (mIdealOver S y)) γ n →ₗ[S] cellZ S y γ n :=
  (evC (S := S) y n).restrict fun _ hz => evC_mem_cellZ y γ n hz

def evH (n : ℕ) : cechHc ι (quotPart S (mIdealOver S y)) γ n →ₗ[S] cellH S y γ n :=
  Submodule.mapQ _ _ (evZ (S := S) y γ n) fun _ hz => evC_mem_cellB (S := S) y γ n hz

theorem evH_mk (n : ℕ) (z : cechZc ι (quotPart S (mIdealOver S y)) γ n) :
    evH (S := S) y γ n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (p := (cellB S y γ n).comap (cellZ S y γ n).subtype) (evZ y γ n z) := rfl

theorem evH_bijective (n : ℕ) : Function.Bijective (evH (S := S) y γ n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp ((evH_mk y γ n z).symm.trans hx)
    rw [Submodule.Quotient.mk_eq_zero]
    exact mem_cechBc_of y γ n (Submodule.mem_inf.mp z.2).1 hx'
  · intro q
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨hC, hK⟩ := Submodule.mem_inf.mp z'.2
    obtain ⟨w, hw, hwz⟩ := evC_lift y γ n hC
    have hdw : cechD S ι _ n w = 0 := by
      refine evC_injOn y γ (n + 1) (cechD_mem_cechCc y γ n hw) (Submodule.zero_mem _) ?_
      rw [evC_cechD, hwz, map_zero]
      exact LinearMap.mem_ker.mp hK
    have hwZ : w ∈ cechZc ι (quotPart S (mIdealOver S y)) γ n :=
      Submodule.mem_inf.mpr ⟨hw, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hdw⟩
    refine ⟨Submodule.Quotient.mk ⟨w, hwZ⟩, ?_⟩
    exact (evH_mk y γ n ⟨w, hwZ⟩).trans (congrArg Submodule.Quotient.mk (Subtype.ext hwz))

theorem proof : CellLocEval.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y γ n
  exact ⟨(LinearEquiv.ofBijective (evH (S := S) y γ n) (evH_bijective (S := S) y γ n)).symm⟩

end CellLocEval

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
