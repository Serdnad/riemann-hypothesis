module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle111
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle267
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem genericFibre_facts : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (D : ℕ), IsArithVar p D → ∃ (_ : IsIntegral G) (_ : IsLocallyNoetherian G), IsProjOver q ∧ topologicalKrullDim G = D ∧ j (genericPoint G) = genericPoint X ∧ Function.Injective j ∧ (∀ x, IsIso (j.stalkMap x)) ∧ (∀ x, Order.coheight (j x) = Order.coheight x) ∧ ∀ z : X, z ∉ Set.range j → ∀ σ : k →+* ℂ, IsEmpty (CxPts (closι z ≫ p) σ) := by
  intro k K _ _ _ _ X G _ p q j hp D h
  obtain ⟨hG, hd, hη⟩ := GenSmoothCover.genericFibre h hp
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ hp h.isProjOver
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have := h.isDomain
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback hp.flip this
  have := flat_specMap_localization (nonZeroDivisors k) K
  have : Flat j := MorphismProperty.of_isPullback hp.flip this
  have hs (x : G) : IsIso (j.stalkMap x) := GenSpread.isIso_stalkMap_of_flat j x
  refine ⟨hG, LocallyOfFiniteType.isLocallyNoetherian q, hq, hd, hη, j.isEmbedding.injective, hs,
    fun x => ?_, fun z hz σ => ⟨fun y => hz ?_⟩⟩
  · have := hs x
    have e := ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at e
    exact_mod_cast e
  · have hr : Set.range j = p ⁻¹' Set.range (spMap (algebraMap k K)) := by
      rw [← Scheme.Pullback.range_fst, ← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
        Function.Surjective.range_comp hp.isoPullback.hom.surjective]
    let c : Sp ℂ := IsLocalRing.closedPoint ℂ
    have hw : closι z (y.1 c) ∈ closure {z} := by
      have : closι z (y.1 c) ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι :=
        ⟨_, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι] at this
      simpa using this
    have h₁ : p z ⤳ p (closι z (y.1 c)) := (specializes_iff_mem_closure.2 hw).map p.continuous
    have h₂ : p (closι z (y.1 c)) = spMap σ c := by
      have := y.2
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun f : Sp ℂ ⟶ Sp k => f c) this
    have h₃ : (spMap σ c).asIdeal = ⊥ := by
      change Ideal.comap σ (IsLocalRing.maximalIdeal ℂ) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ (ChernNull.injective_of_arithVar h σ)
    rw [h₂] at h₁
    have h₄ : (p z).asIdeal ≤ (spMap σ c).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
    rw [h₃, le_bot_iff] at h₄
    rw [hr]
    refine ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h₄]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)

end GlobalTheory.Mix
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleFibre

theorem isAmpleLB_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  intro k _ X _ p D hX L A hL hA l _
  haveI := hX.finite
  have hc := GlobalTheory.NefFibPrime.isClosedImmersion_spMap_zmod l
  haveI : IsClosedImmersion (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip hc
  set f := Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hf
  set g := Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hg
  letI := GlobalTheory.algebraΓOfHom g
  have hproj : IsProjOver g := by
    have h := GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver l f
    rwa [GlobalTheory.strHom_eq (f := g) fun _ => rfl] at h
  have hN : IsNef (ZMod l) (L.B.pull f) :=
    GlobalTheory.FibreNef.isNef_pull_of_nefOver l f L ((GlobalTheory.VertForm.nefFib_iff L).1 hL l Fact.out)
  have hAf : IsAmpleLB (A.B.pull f) := hA.pull_of_isClosedImmersion f
  have hK := IsAmpleLB.tens_of_isNef GlobalTheory.nefNumerics_outright (ZMod l) _ g hproj _ _ hAf hN
  refine hK.of_lbIso (LB.isLB_pull (L.tens A).isLB f) ?_
  refine (CechPic.cls_eq_iff (LB.isLB_pull (L.tens A).isLB f)
    (CechPic.isLB_tens (LB.isLB_pull A.isLB f) (LB.isLB_pull L.isLB f))).1 ?_
  show CechPic.pull f (CechPic.cls L.B L.isLB + CechPic.cls A.B A.isLB) =
    CechPic.pull f (CechPic.cls A.B A.isLB) + CechPic.pull f (CechPic.cls L.B L.isLB)
  rw [map_add (f := _), add_comm]

end GlobalTheory.AmpleFibre
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.MixNull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.ChernNull

theorem chart_null_dom {k : Type} [CommRing k] [IsDomain k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (σ : k →+* ℂ) (hσ : Function.Injective σ) {D : ℕ} {Z : Set X} (hZ : IsClosed Z)
    (hgen : genericPoint X ∉ Z) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ hσ (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

theorem part_compl_null : ∀ (k : Type) [CommRing k] [IsDomain k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (U : X.Opens), genericPoint X ∈ U → part L ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ _ X _ p σ hσ _ D L ε U hU
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgen : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hU
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl
    fun c => by
      have e : (ptsIn p σ U)ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
        ext y
        simp [mem_ptsIn]
      rw [e]
      exact chart_null_dom σ hσ hZ hgen c

end GlobalTheory.MixNull
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.MixHt

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem divOfRatSec_congr {B : LB Y} (hB : B.IsLB) {t t' : B.ι → Y.functionFieldˣ} (ht : IsRatSec B t)
    (ht' : IsRatSec B t') (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) :
    divOfRatSec hB ht = divOfRatSec hB ht' :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨c, hc⟩ := exists_chart hB z
    refine ⟨t c, (presents_divOfRatSec hB ht).isEqn c z hc, ?_⟩
    rw [e c (gen_mem hc)]
    exact (presents_divOfRatSec hB ht').isEqn c z hc

theorem logNorm_congr {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B) {t t' : B.ι → Y.functionFieldˣ}
    (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) (y : CxPts q σ) : logNorm φ t y = logNorm φ t' y := by
  rw [logNorm, logNorm, e _ (gen_mem (mem_ptsIn.1 (mem_pick φ.isLB y)))]

theorem logNorm_tens_mul {σ : k →+* ℂ} (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (hu : IsRatSec A.B u) {y : CxPts q σ}
    (hyr : y ∈ offSupp q σ (M.div hr)) (hyu : y ∈ offSupp q σ (A.div hu)) :
    logNorm ((M.tens A).φ σ) (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) y =
      logNorm (M.φ σ) r y + logNorm (A.φ σ) u y := by
  obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 (mem_pick ((M.tens A).φ σ).isLB y)
  have hu₁ := hr.unitAt M.isLB hyr h₁
  have hu₂ := hu.unitAt A.isLB hyu h₂
  rw [logNorm_eq (M.φ σ) hr hyr h₁, logNorm_eq (A.φ σ) hu hyu h₂]
  change Real.log ‖ratVal ((r (pick ((M.tens A).φ σ).isLB y).1 * u (pick ((M.tens A).φ σ).isLB y).2 :
      Y.functionFieldˣ) : Y.functionField) y‖ - ((M.φ σ).φ (pick ((M.tens A).φ σ).isLB y).1 y +
      (A.φ σ).φ (pick ((M.tens A).φ σ).isLB y).2 y) / 2 = _
  rw [Units.val_mul, ratVal_mul hu₁.regAt hu₂.regAt, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hu₁)) (norm_ne_zero_iff.2 (ratVal_ne_zero hu₂))]
  ring

theorem chernInt_eq_of_null {D : ℕ} (hY : IsArithVar q D) {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B)
    {S S' : Set (CxPts q σ)} (hS : S ⊆ S') (Z : Set Y) (hZ : IsClosed Z) (hg : genericPoint Y ∉ Z)
    (hd : S' \ S ⊆ {y | under y ∈ Z}) (f : CxPts q σ → ℝ) : φ.chernInt D S' f = φ.chernInt D S f := by
  have h (ε : ℤˣ) : S' =ᵐ[φ.chernPart D ε] S := ae_eq_set.2
    ⟨measure_mono_null hd (ChernNull.chernPart_over_closed hY Z hZ hg σ φ ε), by
      rw [Set.diff_eq_empty.2 hS]; exact measure_empty⟩
  rw [Weight.chernInt, Weight.chernInt, setIntegral_congr_set (h 1), setIntegral_congr_set (h (-1))]

theorem chernInt_tens {D : ℕ} (hY : IsArithVar q D) (σ : k →+* ℂ) {B : LB Y} (φ : Weight q σ B)
    (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2)
    (h₁ : φ.ChernIntegrableOn D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r))
    (h₂ : φ.ChernIntegrableOn D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u)) :
    φ.chernInt D (offSupp q σ ((M.tens A).div ht)) (logNorm ((M.tens A).φ σ) t) =
      φ.chernInt D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r) +
        φ.chernInt D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u) := by
  let S := offSupp q σ (M.div hr) ∩ offSupp q σ (A.div hu) ∩ offSupp q σ ((M.tens A).div ht)
  let Z : Set Y := ((M.div hr).supp : Set Y) ∪ (A.div hu).supp ∪ ((M.tens A).div ht).supp
  have hZ : IsClosed Z :=
    ((M.div hr).supp.isClosed.union (A.div hu).supp.isClosed).union ((M.tens A).div ht).supp.isClosed
  have hg : genericPoint Y ∉ Z := by
    simp only [Z, Set.mem_union, SetLike.mem_coe, not_or]
    exact ⟨⟨CartierDiv.genericPoint_notMem_supp _, CartierDiv.genericPoint_notMem_supp _⟩,
      CartierDiv.genericPoint_notMem_supp _⟩
  have hd (T : Set (CxPts q σ)) : T \ S ⊆ {y | under y ∈ Z} := fun y hy => by
    by_contra hz
    simp only [Set.mem_setOf_eq, Z, Set.mem_union, SetLike.mem_coe, not_or] at hz
    exact hy.2 ⟨⟨mem_offSupp.2 hz.1.1, mem_offSupp.2 hz.1.2⟩, mem_offSupp.2 hz.2⟩
  have hSm : MeasurableSet S :=
    (((isOpen_offSupp _).inter (isOpen_offSupp _)).inter (isOpen_offSupp _)).measurableSet
  have hsT : S ⊆ offSupp q σ ((M.tens A).div ht) := fun _ h => h.2
  have hsM : S ⊆ offSupp q σ (M.div hr) := fun _ h => h.1.1
  have hsA : S ⊆ offSupp q σ (A.div hu) := fun _ h => h.1.2
  rw [chernInt_eq_of_null hY φ hsT Z hZ hg (hd _),
    chernInt_eq_of_null hY φ hsM Z hZ hg (hd _) (logNorm (M.φ σ) r),
    chernInt_eq_of_null hY φ hsA Z hZ hg (hd _) (logNorm (A.φ σ) u),
    Weight.chernInt_congr hSm (g := fun y => logNorm (M.φ σ) r y + logNorm (A.φ σ) u y) ?_]
  · exact Weight.chernInt_add ⟨h₁.1.mono_set fun _ h => h.1.1, h₁.2.mono_set fun _ h => h.1.1⟩
      ⟨h₂.1.mono_set fun _ h => h.1.2, h₂.2.mono_set fun _ h => h.1.2⟩
  · intro y hy
    rw [logNorm_congr _ htu y]
    exact logNorm_tens_mul M A hr hu hy.1.1 hy.1.2

theorem archInt_tens (hAI : ArchInteg) {e : ℕ} (hY : IsArithVar q e) (N M A : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2) :
    N.archInt (M.tens A) e ht = N.archInt M e hr + N.archInt A e hu := by
  have := hY.finite_emb
  unfold HermLB.archInt
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun σ => chernInt_tens hY σ (N.φ σ) M A hr hu ht htu
    (hAI k Y q e hY M N r hr σ) (hAI k Y q e hY A N u hu σ)

theorem archInt_of_isEmpty (hE : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (N M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (e : ℕ) : N.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine (finsum_congr fun σ => ?_).trans finsum_zero
  have := hE σ
  rw [Weight.chernInt, Set.eq_empty_of_isEmpty (offSupp q σ (M.div hr))]
  simp only [Measure.restrict_empty, integral_zero_measure, sub_zero]

theorem isArithVar_or_isEmpty (hq : IsAmb q) {e : ℕ} (he : topologicalKrullDim Y = (e + 1 : ℕ)) :
    IsArithVar q e ∨ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ) := by
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · refine .inr fun σ => ⟨fun y => ?_⟩
    let f : Γ(Y, ⊤) →+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp y.1.appTop.hom
    have h0 : (ℓ : ℂ) = 0 := by rw [← map_natCast f, CharP.cast_eq_zero, map_zero]
    exact hℓ.ne_zero (Nat.cast_eq_zero.1 h0)
  · have := CharP.charP_to_charZero Γ(Y, ⊤)
    exact .inl ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 this, he⟩

theorem pol_add {ι : Type} [Fintype ι] (a b : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => a n + b n) = FibreProj.pol a + FibreProj.pol b := by
  simp only [FibreProj.pol, mul_add, Finset.sum_add_distrib]

theorem finsum_mult_add [IsLocallyNoetherian Y] [CompactSpace Y] (D E : CartierDiv Y) (h : Y → ℝ) :
    ∑ᶠ z, ((D + E).mult z : ℝ) * h z = ∑ᶠ z, (D.mult z : ℝ) * h z + ∑ᶠ z, (E.mult z : ℝ) * h z := by
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * h z).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  exact finsum_add_distrib (hfin D) (hfin E)

theorem recVal_tens : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (h : Y → ℝ) (L : Fin e → HermLB q) (M A : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (u : A.B.ι → Y.functionFieldˣ) (hu : IsRatSec A.B u) (t : (M.tens A).B.ι → Y.functionFieldˣ) (ht : IsRatSec (M.tens A).B t), (∀ (i : M.B.ι) (j : A.B.ι), genericPoint Y ∈ M.B.U i → genericPoint Y ∈ A.B.U j → t (i, j) = r i * u j) → recVal h L (M.tens A) ht = recVal h L M hr + recVal h L A hu := by
  intro hAI k _ Y _ _ q hq e he h L M A r hr u hu t ht htu
  have := hq.isNoetherian
  have htu' : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2 :=
    fun c hc => htu c.1 c.2 hc.1 hc.2
  have hdiv : (M.tens A).div ht = M.div hr + A.div hu :=
    (divOfRatSec_congr _ ht (PtHtComb.isRatSec_tens hr hu) htu').trans (PtHtComb.div_tens M A hr hu)
  have hmix : mixArch L (M.tens A) ht = mixArch L M hr + mixArch L A hu := by
    rcases isArithVar_or_isEmpty hq he with hY | hE
    · unfold mixArch
      rw [← add_div, ← pol_add]
      congr 2
      funext n
      exact archInt_tens hAI hY (comb L n) M A hr hu ht htu'
    · have h0 (N' : HermLB q) {r' : N'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N'.B r') :
          mixArch L N' hr' = 0 := by
        simp [mixArch, archInt_of_isEmpty hE, FibreProj.pol]
      rw [h0, h0, h0, add_zero]
  unfold recVal
  rw [hdiv, finsum_mult_add, hmix]
  ring

end GlobalTheory.MixHt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem isEmpty_cxPts_of_algebra_zmod {k : Type} [CommRing k] {Y : Scheme.{0}} (q : Y ⟶ Sp k)
    (l : ℕ) [Fact l.Prime] (_ : Algebra (ZMod l) Γ(Y, ⊤)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : ZMod l →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp
    (y.1.appTop.hom.comp (algebraMap (ZMod l) Γ(Y, ⊤)))
  have h := map_natCast f l
  rw [ZMod.natCast_self, map_zero] at h
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h.symm

theorem amb_vertical_or_arithVar : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → (∃ (l : ℕ) (_ : Fact l.Prime), Nonempty (Algebra (ZMod l) Γ(Y, ⊤)) ∧ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) ∨ ∃ e : ℕ, d = e + 1 ∧ IsArithVar q e := by
  intro k _ Y _ q hq d hd
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    exact .inl ⟨ℓ, this, ⟨ZMod.algebra _ ℓ⟩, fun σ => isEmpty_cxPts_of_algebra_zmod q ℓ (ZMod.algebra _ ℓ) σ⟩
  · have hc := CharP.charP_to_charZero Γ(Y, ⊤)
    obtain _ | e := d
    · exact absurd (by simpa using hd) (dim_ne_zero_of_isProjOver q hq.isProjOver hq.finite hc)
    · exact .inr ⟨e, rfl, hq.isDomain, hq.finite, ‹_›, hq.isProjOver,
        (flat_int_iff_charZero _).2 hc, hd⟩

end GlobalTheory.MixHt
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isForm_evalF_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  intro F _ σ X ι _ m k E H h R
  exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (atlas X σ)).2.2.2.1 _ (chernF E H) R fun x =>
    (GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ (atlas X σ) _ _ _ (GlobalTheory.T.isGramConnectionPair_of_two_flagged_metrics F σ X ι m k E H H h h x.1) x.2).1).1

end GlobalTheory.ChernCalc
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.log_residue_dominant_cartier : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  first | exact @GlobalTheory.FieldPair.mult_lt_of_adjKlt | exact GlobalTheory.FieldPair.mult_lt_of_adjKlt | (intros; apply GlobalTheory.FieldPair.mult_lt_of_adjKlt <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem Trait.beta_pos : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F)
    (a : T.D.toPre.X), a ≠ 0 → 0 < T.β a a := by
  intro g n o _ ζ F T a ha
  obtain ⟨i, hi⟩ := T.mono.exists_pos (maximalIdeal.isMaximal T.V).ne_top ha
  fin_cases i
  simpa using hi

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.section_nonzero_fibres_unit_multiple_thetaSeries : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (σ : U.LG.L.Sec) (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), NzFib σ → (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) → (∀ e, U.ExpandsAt e 1 σ₁ f) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (ϑ : Fam D.toPre C 1) (c : C), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1) → ν.FamV ϑ (c • N.vth) → ‖c‖ = 1 := by
  first | exact @GlobalTheory.KeyEven.ThetaNorm.main | exact GlobalTheory.KeyEven.ThetaNorm.main | (intros; apply GlobalTheory.KeyEven.ThetaNorm.main <;> assumption)
end
