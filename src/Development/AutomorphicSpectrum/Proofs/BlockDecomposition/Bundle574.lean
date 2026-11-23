module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle559
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle566
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.SiegelGrowthForms.SiegelMult
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509

@[expose] public section

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.capelli_classification_of_action : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := by
  first | exact @GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU | exact GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU | (intros; apply GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

namespace GlobalTheory.CompanionTheory.EulerAsm

theorem exists_above {E : Type} [Field E] [NumberField E] [IsCMField E] (v : PlF E) :
    ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨Q, hQm.isPrime, hQ0⟩, ?_⟩
  apply HeightOneSpectrum.ext
  exact (hQo.over).symm

theorem eulerFinOf' : EulerFinOf' := by
  intro hC hR hG hL hH hI E _ _ _ hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  obtain ⟨hr, hth, hK, hKm⟩ := hR hC E a b
  have hKeq : (Kf E a).prod (Kf E b) = ⨅ v, (Kv (E := E) a b v).comap (pv a b v) := by
    ext x
    rw [Subgroup.mem_iInf]
    exact hKm x
  obtain ⟨H1, H2, H3, H4, H5⟩ := hH hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  set_option synthInstance.maxHeartbeats 200000 in
  have main := GlobalTheory.T.twistedOrbitalIntegral_restrictedProduct_finprod (pv (E := E) a b) (Kv a b) hr (thP E a b) (thv a b) hth hK
    (ratF E a δ₁, ratF E b δ₂) (finFn S φ₁ φ₂) (fv S φ₁ φ₂) (hG E a b S hS φ₁ φ₂ h1 h2) H1 H2 H3 H4 H5
  rw [hKeq, main, hI E S hS]
  refine finprod_congr fun v => ?_
  have key : ∀ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v →
      twOrb (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) =
        twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w) := by
    rintro w hw rfl
    exact hL hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2 w hw
  obtain ⟨w0, hw0⟩ := exists_above v
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v := by
    obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w0
    exact ⟨u, huS, hu.trans hw0⟩
  simp only [secPl, dif_pos h, Option.elim]
  exact key _ h.choose_spec.1 h.choose_spec.2

end GlobalTheory.CompanionTheory.EulerAsm
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecReindex

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_under (v : PlF E) : ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
    first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  refine ⟨⟨Q, hQmax.isPrime, ?_⟩, ?_⟩
  · rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  · ext1
    exact hQ

def secEquiv {S : Set (Pl E)} (hS : IsSection S) : S ≃ PlF E :=
  Equiv.ofBijective (fun w => w.1.under (𝓞 (maximalRealSubfield E))) (by
    constructor
    · rintro ⟨u, hu⟩ ⟨u', hu'⟩ h
      exact Subtype.ext ((hS u).unique ⟨hu, rfl⟩ ⟨hu', h.symm⟩)
    · intro v
      obtain ⟨w, rfl⟩ := exists_under v
      obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
      exact ⟨⟨u, hu⟩, huw⟩)

theorem secPl_eq {S : Set (Pl E)} (hS : IsSection S) (u : S) :
    secPl S (secEquiv hS u) = some u.1 := by
  have hv : secEquiv hS u = u.1.under (𝓞 (maximalRealSubfield E)) := rfl
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = secEquiv hS u := ⟨u.1, u.2, hv.symm⟩
  rw [secPl, dite_eq_left h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact congrArg some ((hS u.1).unique ⟨h1, h2.trans hv⟩ ⟨u.2, rfl⟩)

theorem reindex : Reindex := by
  intro E _ _ _ S hS g
  rw [show (∏ᶠ (w : Pl E) (_ : w ∈ S), g w) = ∏ᶠ u : S, g u from
    (finprod_set_coe_eq_finprod_mem S).symm]
  exact finprod_eq_of_bijective (secEquiv hS) (secEquiv hS).bijective
    (fun u => by rw [secPl_eq hS u] <;> rfl)

end GlobalTheory.CompanionTheory.SecReindex

end
end

section

namespace GlobalTheory.CompanionTheory.LocCompareHalves

open PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.UnitaryBC GlobalTheory.BCT

theorem locCompareOf : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  intro hI hS hC E _ _ _ hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw
  by_cases hs : IsSplitAt w
  · exact hS hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs
  · exact hI hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs

end GlobalTheory.CompanionTheory.LocCompareHalves
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSec

private theorem exists_heightOneSpectrum_under_maximalRealSubfield {E : Type} [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (Ideal.comap_bot_le_of_injective _ hinj)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  exact ⟨⟨Q, hQp, hQne⟩, HeightOneSpectrum.ext hQ⟩

theorem eventually_cofinite_of_section :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := by
  intro E _ _ _ S hS P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  refine (hP.image fun w : {w : Pl E // w ∈ S} => w.1.under (𝓞 (maximalRealSubfield E))).subset ?_
  intro v hv
  obtain ⟨w₀, hw₀⟩ := exists_heightOneSpectrum_under_maximalRealSubfield v
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w₀
  exact ⟨⟨u, huS⟩, show ¬P (u.under _) by rw [hu, hw₀]; exact hv, hu.trans hw₀⟩

end GlobalTheory.CompanionTheory.LocHypSec
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypAbove

theorem exists_above_mem_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)),
    IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := by
  intro E _ _ _ S hS v
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    rw [(show Ideal.under (𝓞 (maximalRealSubfield E)) (⊥ : Ideal (𝓞 E)) = ⊥ from
      Ideal.comap_bot_of_injective _ hinj)] at hQv
    exact v.ne_bot hQv.symm
  obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS (⟨Q, hQ, hQ0⟩ : Pl E)
  exact ⟨⟨u, huw.trans (HeightOneSpectrum.ext hQv)⟩, hu⟩

end GlobalTheory.CompanionTheory.LocHypAbove
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocInert

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

def glEquiv {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R ≃+* S) (hf : Continuous f) (hf' : Continuous f.symm) (n : ℕ) : GL (Fin n) R ≃ₜ* GL (Fin n) S where
  toFun := GeneralLinearGroup.map f.toRingHom
  invFun := GeneralLinearGroup.map f.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _
  continuous_toFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf', Units.continuous_coe_inv.matrix_map hf'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev aw (w : Pl E) : Above (w.under (𝓞 (maximalRealSubfield E))) := ⟨w, rfl⟩

theorem eq_aw {w : Pl E} (hw : ¬ IsSplitAt w) (u : Above (w.under (𝓞 (maximalRealSubfield E)))) : u = aw w := by
  by_contra h
  exact hw ⟨u.1, fun e => h (Subtype.ext e), u.2⟩

def uniq {w : Pl E} (hw : ¬ IsSplitAt w) : Unique (Above (w.under (𝓞 (maximalRealSubfield E)))) :=
  ⟨⟨aw w⟩, eq_aw hw⟩

def evR {w : Pl E} (hw : ¬ IsSplitAt w) : Av (w.under (𝓞 (maximalRealSubfield E))) ≃+* w.adicCompletion E :=
  letI := uniq hw
  RingEquiv.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E

theorem evR_apply {w : Pl E} (hw : ¬ IsSplitAt w) (x : Av (w.under (𝓞 (maximalRealSubfield E)))) :
    evR hw x = x (aw w) := rfl

theorem continuous_evR {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw) :=
  continuous_apply (aw w)

theorem continuous_evR_symm {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw).symm := by
  letI := uniq hw
  exact (Homeomorph.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E).symm.continuous

def evY {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) :
    Yv a b (w.under (𝓞 (maximalRealSubfield E))) ≃ₜ* GLw a w × GLw b w where
  toMulEquiv := MulEquiv.prodCongr (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).toMulEquiv
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).toMulEquiv
  continuous_toFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).continuous
  continuous_invFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).symm.continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).symm.continuous

theorem evY_apply {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b y = evw (aw w) y := rfl

theorem cjv_apply (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w)
    (x : Av (w.under (𝓞 (maximalRealSubfield E)))) : evR hw (cjv _ x) = cj w (evR hw x) := by
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hc' := (h4 hw).2.2.1
  have h := hC E (w.under (𝓞 (maximalRealSubfield E)))
  set X : Af E := sLoc E w (evR hw x) with hX
  have hp : pLoc E w X = evR hw x := by
    change (Pi.single w (evR hw x) : ∀ u : Pl E, u.adicCompletion E) w = _
    simp
  have hx : projv _ X = x := by
    funext u
    obtain rfl := eq_aw hw u
    exact hp
  have hs : cjv (w.under (𝓞 (maximalRealSubfield E))) = h.choose := by
    rw [cjv, dite_eq_left h]
  rw [← hx, hs, ← h.choose_spec.2 X]
  rw [evR_apply, evR_apply]
  exact hc' X

theorem evY_thv (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ)
    (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b (thv a b _ y) = ((thL a w).prodMap (thL b w)) (evY hw a b y) := by
  have h : ∀ n (g : GL (Fin n) (Av (w.under (𝓞 (maximalRealSubfield E))))),
      GeneralLinearGroup.map (evR hw).toRingHom (thetaGL n (cjv _) g) =
        thL n w (GeneralLinearGroup.map (evR hw).toRingHom g) := fun n g => by
    rw [thL, if_neg hw]
    exact GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_apply hC hU hw) g
  exact Prod.ext (h a y.1) (h b y.2)

theorem mem_Kv_iff {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    y ∈ Kv a b _ ↔ evY hw a b y ∈ K2 a b w := by
  rw [Kv, Subgroup.mem_iInf]
  constructor
  · intro h
    exact h (aw w)
  · intro h u
    obtain rfl := eq_aw hw u
    exact h

theorem evY_pv {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    evY hw a b (pv a b _ (ratF E a δ₁, ratF E b δ₂)) = (locEl a w δ₁, locEl b w δ₂) := by
  have h : ∀ n (δ : GL (Fin n) E), GeneralLinearGroup.map (evR hw).toRingHom
      (GeneralLinearGroup.map (projv (w.under (𝓞 (maximalRealSubfield E)))) (ratF E n δ)) = locEl n w δ := fun n δ => by
    rw [locEl, if_neg hw]
    ext i j
    rfl
  exact Prod.ext (h a δ₁) (h b δ₂)

theorem fv_eq {w : Pl E} (hw : ¬ IsSplitAt w) {a b : ℕ} {S : Set (Pl E)} (hS : w ∈ S)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    seen φ₁ φ₂ w (evY hw a b y) = fv S φ₁ φ₂ _ y := by
  letI := uniq hw
  rw [fv, finprod_unique]
  change _ = ∏ᶠ (_ : w ∈ S), φ₁ w (evw (aw w) y) * if IsSplitAt w then _ else 1
  rw [finprod_eq_if, if_pos hS, if_neg hw, mul_one, seen, if_neg hw, evY_apply]

theorem locCompareInert : LocCompareInert := by
  intro hC E _ _ _ hU a b S _ φ₁ φ₂ _ _ δ₁ δ₂ _ _ w hS hw
  rw [← evY_pv hw a b δ₁ δ₂]
  exact GlobalTheory.EulerTw.Transport.twOrb_transport _ _ (evY hw a b) _ _ _ _ _ _ _
    (evY_thv hC hU hw a b) (mem_Kv_iff hw a b) (fv_eq hw hS φ₁ φ₂)

end GlobalTheory.CompanionTheory.LocInert
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SepLocEl

theorem cj_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w) (x : E) :
    GlobalTheory.BCT.cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (GlobalTheory.SplitPts.conjE (E := E) k)) →
      GlobalTheory.BCT.cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
    rintro v rfl f hf h
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    rw [GlobalTheory.BCT.cj, dite_eq_left hex]
    exact hex.choose_spec.2 x
  have hinv : conjSrc (GlobalTheory.SplitPts.conjE (E := E))
      (conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w) = w := by
    apply (eq_conjSrc (fun x => ?_)).symm
    rw [← conjPl_conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w
      (GlobalTheory.SplitPts.conjE (E := E) x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)
  have hsrc : conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w = w := by
    by_contra hne
    apply hw
    refine ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2 ?_⟩
    right
    have h := conjPl_conjSrc (GlobalTheory.SplitPts.conjE (E := E))
      (conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w)
    rwa [hinv] at h
  exact key _ hsrc _
    (conjLoc_spec (GlobalTheory.SplitPts.conjE (E := E)) _).1 (conjLoc_spec (GlobalTheory.SplitPts.conjE (E := E)) _).2.1

theorem nrmL_locEl {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  by_cases h : IsSplitAt w
  · simp only [nrmL, locEl, if_pos h]
  · simp only [nrmL, locEl, if_neg h]
    rw [map_mul]
    congr 1
    exact (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) _ (GlobalTheory.BCT.cj w)
      (fun x => (cj_algebraMap h x).symm) δ).symm

theorem separable_charpoly_nrmL_locEl : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  intro _ E _ _ _ n w δ hδ
  rw [nrmL_locEl]
  have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)).val =
      (δ * thE E n δ).val.map (algebraMap E (w.adicCompletion E)) := rfl
  rw [e, Matrix.charpoly_map]
  exact Polynomial.Separable.map hδ.2.2.1

end GlobalTheory.CompanionTheory.SepLocEl

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CjEx

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjAbove {v : PlF E} (w : Above v) : Above v :=
  ⟨conjSrc (IsCMField.complexConj E).toRingEquiv w.1,
    (GlobalTheory.DefU.LocRet.under_conjSrc (E := E) w.1).trans w.2⟩

def cj (v : PlF E) : Av v →+* Av v :=
  RingHom.pi fun w => (conjLoc (IsCMField.complexConj E).toRingEquiv w.1 : _ →+* _).comp
    (Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) (conjAbove w))

theorem continuous_cj (v : PlF E) : Continuous (cj v) :=
  continuous_pi fun w => (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w.1).1.comp (continuous_apply (conjAbove w))

theorem projv_conjFin (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj v (projv v x) :=
  funext fun _ => pLoc_conjFin _ _ _

end GlobalTheory.CompanionTheory.CjEx

theorem GlobalTheory.CompanionTheory.CjEx.cjEx : PositivityTheory.Rg.BcB.G8.Fin.CjEx := fun _ _ _ _ v =>
  ⟨GlobalTheory.CompanionTheory.CjEx.cj v, GlobalTheory.CompanionTheory.CjEx.continuous_cj v, GlobalTheory.CompanionTheory.CjEx.projv_conjFin v⟩

end
end

section


theorem _root_.GlobalTheory.T.finite_half_of_twist : PositivityTheory.Rg.BcB.G8.Fin.FinHalfOf := by
  first | exact @GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf | exact GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf | (intros; apply GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf <;> assumption)
end

section


theorem _root_.GlobalTheory.T.siegel_eisenstein_multiplicativity : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.DictInf → PositivityTheory.RgEis.CMGood → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.SgAll → SiegelEisensteinSeries.BRoad.SiegelMult := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of | exact GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of <;> assumption)
end
