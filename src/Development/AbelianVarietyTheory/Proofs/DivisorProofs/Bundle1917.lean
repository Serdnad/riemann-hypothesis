module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunFamiliesSameHeisenbergInnerEqSmul
import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle149
import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace


theorem _root_.GlobalTheory.T.thetaFun_families_same_heisenberg_inner_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ι : Type)
    (X Y : ι → Formalism.IndefR.Datum.WO S T → ℂ) (act : Formalism.IndefR.Datum.WO S T → ι → ι)
    (g : Formalism.IndefR.Datum.WO S T → Formalism.IndefR.Datum.WO S T), Function.Surjective g →
    (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (X i)) → (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (Y i)) →
    (∀ w i, X (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (X i)) →
    (∀ w i, Y (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (Y i)) →
    ∀ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), μ.IsAddHaarMeasure →
      MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕 μ →
      (∀ i j, ∫ x in 𝓕, X i x * star (X j x) ∂μ = ∫ x in 𝓕, Y i x * star (Y j x) ∂μ) →
      ∃ c : ℂ, ∀ i, X i = c • Y i := by
  first | exact @GlobalTheory.ThetaSchurFam.two_families_scalar | exact GlobalTheory.ThetaSchurFam.two_families_scalar | (intros; apply GlobalTheory.ThetaSchurFam.two_families_scalar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilUniq

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, om_om_inv, map_smul] at this

theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  refine ⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩
  unfold heisO
  rw [zero_add]
  refine mul_ne_zero ?_ hw
  exact (ψ.val_isUnit _).ne_zero

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 := by
  obtain ⟨x, hx⟩ := exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := exists_isDetAt he.1 T h
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.T.exists_split_place_half_heisenberg_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul] at e1
  have e2 : (c : ℂ) * r' = r := by
    apply mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)
    linear_combination e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')
  rw [e2, Circle.coe_one, one_mul]

theorem weilDatum_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  intro D ψ hψ S T χS χT om om' H H' p f hf
  by_cases h0 : f = 0
  · rw [h0, map_zero, map_zero]
  obtain ⟨f₀, hf₀, h00⟩ := exists_ne_zero_at_zero hψ hf h0
  have hne : ∀ q, om' q f₀ ≠ 0 := fun q hq => by
    have := om_inv_om om' q f₀
    rw [hq, map_zero] at this
    exact h00 (by rw [← this]; rfl)
  choose c hc using exists_scalar H H'
  have hmul : ∀ q q', c (q * q') = c q * c q' := fun q q' => by
    apply Circle.ext
    apply smul_left_injective ℂ (hne (q * q'))
    have := hc (q * q') f₀ hf₀
    dsimp only
    rw [← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul,
      hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]
  have hcont : Continuous c := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 (hne q)
    have h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q :=
      (H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw
    refine h1.congr ?_
    filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'
    rw [hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']
    rfl
  have hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1 := fun γ hγ γ' hγ' => by
    have h1 := congrFun (hc (γ, γ') f₀ hf₀) 0
    rw [Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul] at h1
    apply Circle.ext
    apply mul_right_cancel₀ h00
    rw [← h1, Circle.coe_one, one_mul]
  let ν : GA D S × GA D T →* Circle := MonoidHom.mk' c hmul
  have hS := GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _))
    (fun γ hγ => hrat γ hγ 1 (one_mem _))
    (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))
  have hT := GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _))
    (fun γ hγ => hrat 1 (one_mem _) γ hγ)
    (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))
  have h1 : c p = 1 := by
    have e : p = (p.1, 1) * (1, p.2) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]
  rw [hc p f hf, h1, Circle.coe_one, one_smul]

end GlobalTheory.WeilUniq
end

section

open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw)

noncomputable section

namespace GlobalTheory.SqTop.OneSqProof

theorem vw_ratio_le {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e p q e0 h0 : ℕ)
    (he : e0 + p = e + q) (hle : e0 ≤ h0) (rq ζ γ zA zA' : K) (tk : Fin (p + q) → K) (ρ : ℤ → K) (a n0 : ℤ → ℝ)
    (er dl B : ℝ)
    (heq : rq * ∏ k ∈ range q, ρ ((e : ℤ) + k + 1) = ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k))
    (hρ0 : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ (h0 : ℤ) + p + q → ρ s ≠ 0)
    (hζ : ζ ≠ 0 ∧ vw w ζ = 0) (ht : ∀ k, tk k ≠ 0 ∧ |(vw w (tk k) : ℝ)| ≤ B) (hγ : γ ≠ 0) (hzA : zA ≠ 0)
    (hγv : (vw w γ : ℝ) ≤ vw w (zA * ∏ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s) + vw w zA' + 6 * dl)
    (her : 0 ≤ er)
    (hs : ∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q →
      0 ≤ a s ∧ 0 ≤ n0 s ∧ (vw w (ρ s) : ℝ) ≤ a s + er ∧ -(vw w (ρ s) : ℝ) ≤ a s + n0 s)
    (hsym : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) :
    rq ≠ 0 ∧ (vw w rq : ℝ) ≤ |(vw w zA : ℝ)| + |(vw w zA' : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) +
      ((2 * (h0 + p + q) : ℕ) : ℝ) * er + 6 * dl + ((p + q : ℕ) : ℝ) * B := by
  have hq0 : ∀ k ∈ range q, ρ ((e : ℤ) + k + 1) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hp0 : ∀ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hI0 : ∀ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s ≠ 0 := fun s hs => by
    rw [mem_Icc] at hs; exact hρ0 _ hs.1 (by omega)
  have hT : ∀ k ∈ (univ : Finset (Fin (p + q))), tk k ≠ 0 := fun k _ => (ht k).1
  have hPq := prod_ne_zero_iff.2 hq0
  have hPp := prod_ne_zero_iff.2 hp0
  have hPT := prod_ne_zero_iff.2 hT
  have hPI := prod_ne_zero_iff.2 hI0
  have hR : ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp
  have hrq : rq ≠ 0 := by
    rintro rfl; rw [zero_mul] at heq; exact hR heq.symm
  refine ⟨hrq, ?_⟩
  have hv := congrArg (vw w) heq
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hrq hPq, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hq0,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hζ.1 hPT) hγ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hζ.1 hPT,
    Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hT, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hp0, hζ.2] at hv
  have hz := Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hzA hPI
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hI0] at hz
  rw [hz] at hγv
  have hc := GlobalTheory.Square.count_factors e p q e0 h0 he hle (fun s => (vw w (ρ s) : ℝ)) a n0 er her
    (fun s h1 h2 => hs s h1 h2) (fun s h1 h2 => by simp only [hsym s h1 h2])
  have hvR : (vw w rq : ℝ) + ∑ k ∈ range q, (vw w (ρ ((e : ℤ) + k + 1)) : ℝ) =
      (∑ k, (vw w (tk k) : ℝ)) + vw w γ + ∑ k ∈ range p, (vw w (ρ ((e : ℤ) + q - k)) : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hv
    push_cast at this
    linarith
  have hTB : (∑ k, (vw w (tk k) : ℝ)) ≤ ((p + q : ℕ) : ℝ) * B := by
    calc (∑ k, (vw w (tk k) : ℝ)) ≤ ∑ _k : Fin (p + q), B :=
          sum_le_sum fun k _ => (le_abs_self _).trans (ht k).2
      _ = ((p + q : ℕ) : ℝ) * B := by simp
  have hIc : ((∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), vw w (ρ s) : ℤ) : ℝ) =
      ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ) := by push_cast; rfl
  have hγv' : (vw w γ : ℝ) ≤ vw w zA + (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ)) + vw w zA' + 6 * dl := by
    have := hγv; push_cast at this; linarith
  have a1 := le_abs_self (vw w zA : ℝ)
  have a2 := le_abs_self (vw w zA' : ℝ)
  linarith

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem wt_at {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ} {l : ℕ}
    (hS : ∀ l' ∈ S, l'.Prime) (hl : l.Prime) (hw : (l : 𝓞 K) ∈ w.asIdeal) (hc : l ∉ S → c l = 0) :
    Formalism.PairingDivisionLocalBalance.wt S c w = c l * (vw w (l : K) : ℝ) := by
  unfold Formalism.PairingDivisionLocalBalance.wt
  by_cases h : l ∈ S
  · refine sum_eq_single_of_mem l h fun l' hl' hne => ?_
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp
  · rw [hc h, zero_mul]
    refine sum_eq_zero fun l' hl' => ?_
    have hne : l' ≠ l := fun e => h (e ▸ hl')
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp

theorem wt_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ}
    (hc : ∀ l ∈ S, 0 ≤ c l) : 0 ≤ Formalism.PairingDivisionLocalBalance.wt S c w :=
  sum_nonneg fun l hl => mul_nonneg (hc l hl) (GlobalTheory.Square.TwoStep.vw_natCast_nonneg w l)

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem exists_prime_mem' {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal := by
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ w.asIdeal), CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) _, ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ w.asIdeal) (ringChar _))

end GlobalTheory.SqTop.OneSqProof

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.SqTop

namespace GlobalTheory.SqTop.OneSqProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.SqTop.OneSqProof
end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem depth_lt_iff {r : ℕ} (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r) (d : Fin s → ℕ)
    (hd : ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) (i j : Fin s) :
    d j < d i ↔ ∃ k ∈ S, Fin.castLE hs j ≤ k ∧ k < Fin.castLE hs i := by
  rw [hd, hd]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_not_ge fun h' => absurd hk.2 (not_lt.2 (hne k hk.1 h'))⟩
  · rintro ⟨k, hk, h1, h2⟩
    refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
    · rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_of_lt_of_le hx.2 (h1.trans h2.le)⟩
    · have := h (Finset.mem_filter.2 ⟨hk, h2⟩)
      exact absurd (Finset.mem_filter.1 this).2 (not_lt.2 h1)

theorem cT_submatrix_mul {E : Type} [Field E] (σ : E →+* E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A B : Matrix (Fin n) (Fin r) E) (f g : Fin s → Fin r) :
    Formalism.UG.cT σ (A.submatrix id f) * J * B.submatrix id g = (Formalism.UG.cT σ A * J * B).submatrix f g := by
  ext i j
  simp [Formalism.UG.cT, Matrix.mul_apply]

end GlobalTheory.TieStd
end

section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LaurentAut

open scoped ContDiff

theorem hasDerivAt_integral_cpt {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 ℂ] [ProperSpace 𝕜] {H : Type} [TopologicalSpace H] [T2Space H]
    [MeasurableSpace H] [OpensMeasurableSpace H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {Φ Φ' : 𝕜 → H → ℂ} {x₀ : 𝕜}
    {C : Set H} (hC : IsCompact C) (hc : ∀ t, Continuous (Φ t)) (hc' : Continuous fun p : 𝕜 × H => Φ' p.1 p.2)
    (h0 : ∀ t ∈ Metric.closedBall x₀ 1, ∀ y ∉ C, Φ t y = 0 ∧ Φ' t y = 0)
    (hd : ∀ t y, HasDerivAt (Φ · y) (Φ' t y) t) :
    HasDerivAt (fun t => ∫ y, Φ t y ∂μ) (∫ y, Φ' x₀ y ∂μ) x₀ := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ 1).prod hC).exists_bound_of_continuousOn hc'.continuousOn
  have hx : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  have hc0 : Continuous (Φ' x₀) := hc'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := C.indicator fun _ => B)
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_
    ((hc x₀).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).1))
    (hc0.integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).2)).aestronglyMeasurable
    (.of_forall fun y t ht => ?_) ?_ (.of_forall fun y t _ => hd t y)).2
  · filter_upwards [Metric.closedBall_mem_nhds x₀ one_pos] with t ht
    exact ((hc t).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 t ht y hy).1)).aestronglyMeasurable
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy]; exact hB (t, y) ⟨ht, hy⟩
    · rw [Set.indicator_of_notMem hy, (h0 t ht y hy).2, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] {N : ℕ}
  {j : H →* G} {ι : H →* Matrix (Fin N) (Fin N) ℂ}

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1)
include hι h1

variable [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]


end Abstract

section Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {N : ℕ} {ι : GInf σ J →* Matrix (Fin N) (Fin N) ℂ}
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1) {f : Matrix (Fin N) (Fin N) ℂ → ℝ}
include hι h1

variable {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ}

end Unitary



end GlobalTheory.LaurentAut
end
end
