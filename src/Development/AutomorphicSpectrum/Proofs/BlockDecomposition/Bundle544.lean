module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle504
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle521
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundFromBoxVolumeGrowth
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle508
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle528
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle522
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
import Mathlib.Tactic.Basify
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_transform_invariance : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p)), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → ∀ A : Mx D ρ p × Mx D ρ p → ℂ, (∀ (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E) v, A (v + (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂)) = A v) → ∫ v in m.𝓕 ×ˢ m.𝓕, A (T v) ∂(m.μ.prod m.μ) = ∫ v in m.𝓕 ×ˢ m.𝓕, A v ∂(m.μ.prod m.μ) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.TransportInt.transport_int | exact GlobalTheory.CompanionTheory.FJE.TransportInt.transport_int | (intros; apply GlobalTheory.CompanionTheory.FJE.TransportInt.transport_int <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_box_radius_tail_lintegral_le_eps_mul : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.density_bound_from_box_volume_growth : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ), 0 < n → 2 * n < M → ∀ (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → (∀ (S : Set (Fin n → Fin M → K)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → K), s a = 0 → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q S C → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s '' S) C) → ∀ R : ℝ, 1 ≤ R → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) \ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK κ R ε) δ := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density <;> assumption)
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc GlobalTheory.CompanionTheory.TwY
open PositivityTheory.RgBcC (KMod lefE lefT phiOf infOf IsMult Inf GLs IsEig MultAlg)
open PositivityTheory.RgBcC.Real (IsLefK)
open PositivityTheory.RgBcC.RealD (invA flipA trOn hwSp harmSet kF gelA barF IsPair IsDerivK)
open PositivityTheory.RgTw (G Mat)
open scoped ContDiff InnerProductSpace
attribute [local instance] borelH Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TwY.ThInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def adjH : Lie E n →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᴴ
      map_add' := fun X Y => by
        rw [show Matrix.of (X + Y) = Matrix.of X + Matrix.of Y from rfl, Matrix.conjTranspose_add]; rfl
      map_smul' := fun t X => by
        rw [show Matrix.of (t • X) = t • Matrix.of X from rfl, Matrix.conjTranspose_smul, star_trivial]; rfl }

theorem adjH_apply (X : Lie E n) (i j : Fin n) : adjH X i j = star (X j i) := rfl

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map p g) := by
  ext i j
  change p (c ((g⁻¹ : GL (Fin n) R).val j i)) = c' (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S).val j i)
  rw [h, ← map_inv]
  rfl

theorem thetaA_infGL (y : GL (Fin n) (Cinf E)) :
    thetaA E n (infGL E n y) = infGL E n (thetaR (starRingEnd (Cinf E)) n y) :=
  ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_infGL, pInf_infGL])
    (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

theorem thetaA_finGL (k : GL (Fin n) (Af E)) : thetaA E n (finGL E n k) = finGL E n (thetaF E n k) :=
  ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
    (by rw [pFin_finGL]; rfl)

theorem thetaA_kAt (w : InfinitePlace E) (c : UU n) : thetaA E n (kAt w c) = kAt w c := by
  classical
  have e : kAt w c = infGL E n (locInf w (Unitary.toUnits c)) := rfl
  rw [e, thetaA_infGL]
  congr 1
  refine Units.ext ?_
  ext i j v
  rw [thetaR_val, ← map_inv, ← map_inv]
  change star ((locInf w (Unitary.toUnits c)⁻¹ : GL (Fin n) (Cinf E)).val j i v) = _
  rw [locInf_apply, locInf_apply]
  by_cases hv : v = w
  · simp only [hv, if_true]
    change star ((star c.1 : Matrix (Fin n) (Fin n) ℂ) j i) = c.1 i j
    simp [Matrix.star_apply]
  · simp only [hv, if_false]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem toL_thetaR (y : GL (Fin n) (Cinf E)) :
    toL (thetaR (starRingEnd (Cinf E)) n y).val = adjH (GlobalTheory.ThetaPull.invL (toL y.val)) := by
  rw [thetaR_val]
  ext i j : 2
  change starRingEnd (Cinf E) ((y⁻¹ : GL (Fin n) (Cinf E)).val j i) = star ((y.val)⁻¹ j i)
  rw [Matrix.coe_units_inv]
  rfl

theorem chart_theta (φ : GA E n → ℂ) (g : GA E n) {x : Lie E n} (hx : x ∈ invSet E n) :
    chart (fun g => φ (thetaA E n g)) g x = chart φ (thetaA E n g) (adjH (GlobalTheory.ThetaPull.invL x)) := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_thetaR, chart_val, chart_val, map_mul, thetaA_infGL]

theorem lieD_theta (X : Lie E n) {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g : GA E n) :
    lieD X (fun g => φ (thetaA E n g)) g = -lieD (adjH X) φ (thetaA E n g) := by
  have e : chart (fun g => φ (thetaA E n g)) g =ᶠ[nhds (oneL E n)]
      chart φ (thetaA E n g) ∘ adjH ∘ GlobalTheory.ThetaPull.invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_theta φ g hx
  have h1 : (adjH ∘ GlobalTheory.ThetaPull.invL) (oneL E n) = oneL E n :=
    (toL_thetaR 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E n) (f := adjH ∘ GlobalTheory.ThetaPull.invL)
    (by rw [h1]; exact (differentiableAt_chart hφ (thetaA E n g)).hasFDerivAt)
    ((adjH (E := E) (n := n)).hasFDerivAt.comp (oneL E n) GlobalTheory.ThetaPull.invL_smooth.2)
  unfold lieD
  rw [e.fderiv_eq, h2.fderiv]
  simp


open ComplexConjugate in
theorem atEmb_conjugate (w : InfinitePlace E) (z : ℂ) :
    atEmb (ComplexEmbedding.conjugate w.embedding) z = atEmb w.embedding (conj z) := by
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)
  unfold atEmb
  rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne, if_pos rfl]


open ComplexConjugate in
theorem star_atEmb (w : InfinitePlace E) (z : ℂ) : star (atEmb w.embedding z) = atEmb w.embedding (conj z) := by
  funext v
  simp only [atEmb, InfinitePlace.mk_embedding, if_true, Pi.star_apply]
  by_cases hv : v = w
  · subst hv; simp
  · classical
    rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, star_zero]

def sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : Lie E n := toL (Matrix.single a b (atEmb w.embedding z))

open ComplexConjugate in
theorem adjH_sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : adjH (sg w a b z) = sg w b a (conj z) := by
  funext i j
  rw [adjH_apply]
  change star (Matrix.single a b (atEmb w.embedding z) j i) = Matrix.single b a (atEmb w.embedding (conj z)) i j
  rw [Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos h.symm, star_atEmb]
  · rw [if_neg h, if_neg fun h' => h h'.symm, star_zero]

theorem Eop_apply (τ : E →+* ℂ) (a b : Fin n) (φ : Sm E n) (g : GA E n) :
    (Eop τ a b φ).1 g = (1 / 2 : ℂ) * (lieD (toL (Matrix.single a b (atEmb τ 1))) φ.1 g -
      Complex.I * lieD (toL (Matrix.single a b (atEmb τ Complex.I))) φ.1 g) := rfl

def thV (π : CuspSub E n) (h : ThetaFix π) : Module.End ℂ π.V where
  toFun ψ := ⟨(h.2 ψ.1 ψ.2).choose, (h.2 ψ.1 ψ.2).choose_spec.1⟩
  map_add' a b := Subtype.ext <| Subtype.ext <| funext fun x => by
    change (h.2 (a + b).1 (a + b).2).choose.1 x =
      (h.2 a.1 a.2).choose.1 x + (h.2 b.1 b.2).choose.1 x
    rw [(h.2 (a + b).1 (a + b).2).choose_spec.2, (h.2 a.1 a.2).choose_spec.2, (h.2 b.1 b.2).choose_spec.2]
    rfl
  map_smul' c a := Subtype.ext <| Subtype.ext <| funext fun x => by
    change (h.2 (c • a).1 (c • a).2).choose.1 x = c * (h.2 a.1 a.2).choose.1 x
    rw [(h.2 (c • a).1 (c • a).2).choose_spec.2, (h.2 a.1 a.2).choose_spec.2]
    rfl

theorem thV_apply (π : CuspSub E n) (h : ThetaFix π) (ψ : π.V) (x : GA E n) :
    ((thV π h ψ : π.V) : Sm E n).1 x = (ψ : Sm E n).1 (thetaA E n x) :=
  (h.2 ψ.1 ψ.2).choose_spec.2 x

end GlobalTheory.CompanionTheory.TwY.ThInv
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem isB_unique : ∀ {D : D7} {p : ℕ} {e : AE D} {g : G D p} {x x' : hermS D p e} (h : IsB e g x) (h' : IsB e g x'), x = x' := by
  intro D p e g x x' h h'
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  obtain ⟨-, hx'⟩ := h'
  have key : ∀ z : hermS D p e, mm (lowC g) z.1.1 = e • lowD g → z.1.1 = mm y (e • lowD g) := by
    intro z hz
    have hs : e • z.1.1 = z.1.1 := z.2
    rw [← hz]
    show z.1.1 = y * (lowC g * z.1.1)
    rw [← Matrix.mul_assoc]
    have hy' : y * lowC g = e • (1 : Mx D p p) := hy
    rw [hy', Matrix.smul_mul, Matrix.one_mul, hs]
  exact Subtype.ext (Subtype.ext ((key x hx).trans (key x' hx').symm))

end GlobalTheory.CompanionTheory.MuC
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mul_nBlock_inl {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inl j)) = A i (finSumFinEquiv (Sum.inl j)) := by
  simp [Matrix.mul_apply, blk4, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_nBlock_inr {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inr j)) =
      ∑ k, A i (finSumFinEquiv (Sum.inl k)) * y k j + A i (finSumFinEquiv (Sum.inr j)) := by
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂]
  simp [Matrix.one_apply]

theorem lowC_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowC (g * nb y) = lowC g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, Matrix.submatrix_apply, hm]
  exact mul_nBlock_inl _ _ _ _

theorem lowD_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowD (g * nb y) = lowC g * y.1 + lowD g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, lowD, Matrix.submatrix_apply, hm, Matrix.add_apply, Matrix.mul_apply]
  exact mul_nBlock_inr _ _ _ _

theorem isB_mul_nb {D : D7} {p : ℕ} {e : AE D} {nb : hermA D p → G D p} (hnb : IsNMap nb) {g : G D p}
    (y x : hermS D p e) : IsB e (g * nb y.1) (x + y) ↔ IsB e g x := by
  have hy : e • y.1.1 = y.1.1 := y.2
  have hc : e • (lowC g * y.1.1) = lowC g * y.1.1 := by rw [← Matrix.mul_smul, hy]
  have hs : (x + y).1.1 = x.1.1 + y.1.1 := rfl
  unfold IsB InCell
  rw [lowC_mul_nb hnb, lowD_mul_nb hnb, hs]
  refine and_congr_right fun _ => ?_
  simp only [mm]
  rw [mul_add, smul_add, hc, add_comm (lowC g * y.1.1) (e • lowD g), add_left_inj]

end GlobalTheory.CompanionTheory.MuC

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

open GlobalTheory.StdUnn.Gen GlobalTheory.StdUnn.Model

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem standard_symplectic_form_sq_neg_one :
    (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) R) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [Matrix.neg_apply, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

theorem flip_J {J M A : Matrix (Fin (n + n)) (Fin (n + n)) R} (h : A * J * M = J) (hJ : J * J = -1) :
    M * J * A = J := by
  have h1 : (-(J * A * J)) * M = 1 := by
    calc (-(J * A * J)) * M = -(J * (A * J * M)) := by simp only [neg_mul, mul_assoc]
      _ = 1 := by rw [h, hJ, neg_neg]
  have h2 : M * (-(J * A * J)) = 1 := mul_eq_one_comm.1 h1
  calc M * J * A = -((M * (-(J * A * J))) * J) * (J * J) * (-1) * (-1) * (-1) * 0 + M * J * A := by simp
    _ = J := by
      have h3 : M * J * A * (J * J) = -J := by
        calc M * J * A * (J * J) = (M * (J * A * J)) * J := by simp only [mul_assoc]
          _ = -J := by
            have : M * (J * A * J) = -1 := by
              have := congrArg Neg.neg h2
              simpa using this
            rw [this]; simp
      rw [hJ] at h3
      simpa using h3

theorem symplectic_lower_block_relation {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d * blk4 0 1 (-1) 0 * blk4 a' b' c' d' = blk4 0 1 (-1) 0) : c * d' = d * b' := by
  simp only [submatrix_fromBlocks_mul, mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h
  have h4 := (blockMatrixTwoByTwoFin_injective h).2.2.2
  exact (neg_add_eq_zero.1 h4).symm

theorem mul_smul_of_idem {e : R} (he : e * e = e) {y c : Matrix (Fin n) (Fin n) R}
    (hy : y * c = e • (1 : Matrix (Fin n) (Fin n) R)) : c * (e • y) = e • (1 : Matrix (Fin n) (Fin n) R) := by
  have he0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have he0' : (1 - e) * e = 0 := by rw [mul_comm, he0]
  have he1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, he0, sub_zero]
  have h1 : (e • y + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) *
      (e • c + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul, hy, smul_smul,
      he, he0, he0', he1, zero_smul, add_zero, zero_add]
    rw [← add_smul, add_sub_cancel, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  have h3 : e • (c * y) + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) = 1 := by
    simpa only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul, smul_smul,
      he, he0, he0', he1, zero_smul, add_zero, zero_add] using h2
  rw [Matrix.mul_smul, eq_sub_of_add_eq h3, sub_smul, one_smul]
  abel

end Ring

theorem herm_core {A : Type} [Ring A] {E w c d c' d' w' : A} (hwc : w * c = E) (hcw : c' * w' = E)
    (H : c * d' = d * c') (hw : w * E = w) (hw' : E * w' = w') (hd : E * d = d * E)
    (hd' : E * d' = d' * E) : d' * w' = w * d := by
  calc d' * w' = d' * (E * w') := by rw [hw']
    _ = (E * d') * w' := by rw [hd', mul_assoc]
    _ = w * (c * d') * w' := by rw [← hwc]; simp only [mul_assoc]
    _ = w * d * (c' * w') := by rw [H]; simp only [mul_assoc]
    _ = w * (E * d) := by rw [hcw, mul_assoc, ← hd]
    _ = w * d := by rw [← mul_assoc, hw]

theorem cell_core_ring {R : Type} [CommRing R] {n : ℕ} {s : R → R}
    (ad : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R)
    (ad_mul : ∀ x y, ad (x * y) = ad y * ad x) (ad_smul : ∀ (a : R) x, ad (a • x) = s a • ad x)
    (ad_one : ad 1 = 1) {e : R} (he : e * e = e) (hc : s e = e) {y c d : Matrix (Fin n) (Fin n) R}
    (hy : y * c = e • (1 : Matrix (Fin n) (Fin n) R)) (H : c * ad d = d * ad c) :
    e • ((e • y) * d) = (e • y) * d ∧ ad ((e • y) * d) = (e • y) * d ∧ c * ((e • y) * d) = e • d := by
  have hcw : c * (e • y) = e • (1 : Matrix (Fin n) (Fin n) R) := mul_smul_of_idem he hy
  have hwc : (e • y) * c = e • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.smul_mul, hy, smul_smul, he]
  have hw : e • (e • y) = e • y := by rw [smul_smul, he]
  have haw : e • ad (e • y) = ad (e • y) := by
    have := ad_smul e (e • y)
    rw [hw, hc] at this
    exact this.symm
  have hawc : ad c * ad (e • y) = e • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← ad_mul, hwc, ad_smul, ad_one, hc]
  have hidem : e • ((e • y) * d) = (e • y) * d := by rw [← Matrix.smul_mul, hw]
  have hcomm : ∀ z : Matrix (Fin n) (Fin n) R,
      (e • (1 : Matrix (Fin n) (Fin n) R)) * z = z * (e • (1 : Matrix (Fin n) (Fin n) R)) := fun z => by
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  refine ⟨hidem, ?_, ?_⟩
  · rw [ad_mul]
    refine herm_core hwc hawc H ?_ ?_ (hcomm d) (hcomm (ad d))
    · rw [Matrix.mul_smul, mul_one, hw]
    · rw [Matrix.smul_mul, one_mul, haw]
  · rw [← mul_assoc, hcw, Matrix.smul_mul, one_mul]

variable {D : D7} {p : ℕ}

theorem mat_J_adj (g : G D p) :
    mat g * blk4 0 1 (-1) 0 * adj (mat g) = (blk4 0 1 (-1) 0 : Mx D (p + p) (p + p)) := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D p) * mat g = JR (AF D.host.F) (Jst D p) := g.2
  rw [JR_Jst] at h
  exact flip_J h standard_symplectic_form_sq_neg_one

theorem lowC_mul_adj_lowD (g : G D p) : lowC g * adj (lowD g) = lowD g * adj (lowC g) := by
  obtain ⟨a, b, c, d, hM⟩ := exists_blockMatrixTwoByTwoFin_eq (mat g)
  have hc : lowC g = c := by
    ext i j
    simp only [lowC, hM, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]
  have hd : lowD g = d := by
    ext i j
    simp only [lowD, hM, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]
  have h := mat_J_adj g
  rw [hM, adelicConjTranspose_blockMatrixTwoByTwoFin] at h
  rw [hc, hd]
  exact symplectic_lower_block_relation h

theorem exists_isB : ∀ {D : D7} {p : ℕ} {e : AE D} (he : e * e = e) (hc : cA D e = e) {g : G D p}
    (hg : InCell e g), ∃ x, IsB e g x := by
  intro D p e he hc g hg
  obtain ⟨y, hy⟩ := id hg
  obtain ⟨h1, h2, h3⟩ := cell_core_ring (R := AE D) (n := p) (s := cA D) adj adj_mul adj_smul adj_one he hc
    (y := y) (c := lowC g) (d := lowD g) hy (lowC_mul_adj_lowD g)
  exact ⟨⟨⟨(e • y) * lowD g, h2⟩, h1⟩, hg, h3⟩

end GlobalTheory.CompanionTheory.MuC

end
end

section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.product_theta_of_schwartz_tensor : SchwTensor → ProdTh := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | exact GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor <;> assumption)
end
