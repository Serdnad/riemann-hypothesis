module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMkTauE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle863
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle862
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle511
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem thetaKO_flip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (z : GA D V), z ∈ GfC V → ∀ (e e₂ : AE D) (M : ℕ) (O : Subring ℂ) (f f' : WO V W → ℂ) (a : ℂ), f ∈ trSp ψ V W ΛV ΛW f₀ e M O → f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ M O → om (z, 1) f' = a • f → ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), a * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z) g (stdF ψ θ V W sW BW f' Q) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP z hz e e₂ M O f f' a _ hf' hom BW Q s g
  have hw := hP.1.weil
  have hf₀ : IsThetaFunO ψ V W f₀ := hP.2.2.2.2.2.2.2.2.2.theta
  have hth : IsThetaFunO ψ V W f' := by
    clear hom
    induction hf' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, -, -, rfl⟩ := hx
      exact GlobalTheory.TwistFactorCompare.isTheta_heisO hw.std hf₀ y
    | zero => simpa using GlobalTheory.OrientedHeis.theta_smul (0 : ℂ) hf₀
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul (c : ℂ) hx
  have h1 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hw hP.1.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) sW sW BW BW z 1
    (fun τ => by simp only [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hz, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by simp only [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hz, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f' hth Q).2
  have hp : ((s * z, g) : GA D V × GA D W) = (s, g) * (z, 1) := by simp
  unfold thetaKO stdF
  rw [hp, map_mul, Module.End.mul_apply, h1, hom, GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.LevelSeries

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem phase_zpow_eq (z : ℂ) (hz : z ≠ 0) (b : ℤ) (r : ℕ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * b + (r : ℤ)) =
      z ^ (b + (r : ℤ)) * ((starRingEnd ℂ z) ^ b)⁻¹ * (((‖z‖ : ℝ) : ℂ) ^ r)⁻¹ := by
  have hN : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  have hsq : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have h2b : ((‖z‖ : ℝ) : ℂ) ^ (2 * b) = z ^ b * (starRingEnd ℂ z) ^ b := by
    rw [_root_.zpow_mul, show ((‖z‖ : ℝ) : ℂ) ^ (2 : ℤ) = ((‖z‖ : ℝ) : ℂ) ^ (2 : ℕ) from zpow_ofNat _ 2, hsq, mul_zpow]
  have hzn : z ^ (2 * b + (r : ℤ)) = z ^ b * z ^ (b + (r : ℤ)) := by
    rw [← zpow_add₀ hz]; congr 1; ring
  rw [div_zpow, zpow_add₀ hN, h2b, hzn, zpow_natCast]
  have h1 : z ^ b ≠ 0 := zpow_ne_zero _ hz
  have h2 : (starRingEnd ℂ z) ^ b ≠ 0 := zpow_ne_zero _ hc
  have h3 : ((‖z‖ : ℝ) : ℂ) ^ r ≠ 0 := pow_ne_zero _ hN
  field_simp

theorem prod_norm_inv_pow {ι : Type} [Fintype ι] (z : ι → ℂ) (r : ℕ) :
    ∏ i, (((‖z i‖ : ℝ) : ℂ) ^ r)⁻¹ = (((∏ i, ‖z i‖ ^ 2) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← Real.finsetProd_rpow _ _ (fun i _ => by positivity) _]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast_mul (norm_nonneg _)]
  rw [show ((2 : ℕ) : ℝ) * (-(r : ℝ) / 2) = -(r : ℝ) by push_cast; ring, Real.rpow_neg (norm_nonneg _),
    Real.rpow_natCast]
  push_cast
  rfl

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem conjugate_tauE_ne_tauE (D : D7) (τ τ' : D.what₂.Tau) :
    NumberField.ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, Formalism.L2.Theta.tauE_sqrtMinusD,
    Formalism.L2.Theta.tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  linarith

theorem mk_tauE_bij (D : D7) : Function.Bijective (fun τ : D.what₂.Tau => InfinitePlace.mk (tauE D τ)) := by
  refine ⟨fun τ τ' h => ?_, fun w => GlobalTheory.CharInfPlace.exists_mk_tauE D w⟩
  rcases InfinitePlace.mk_eq_iff.1 h with e | e
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  · exact absurd e (conjugate_tauE_ne_tauE D τ τ')

theorem mk_tauE_complex (D : D7) (τ : D.what₂.Tau) : ¬ (InfinitePlace.mk (tauE D τ)).IsReal := by
  rw [InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]
  exact conjugate_tauE_ne_tauE D τ τ

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem inf_eq_mul_normPow : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (χ : Formalism.L2.Host.HChar D.host.E), ChrEq χW χ → ∀ (k : Type) [Field k] (σ : k →+* ℂ), ConjIn D σ → ∀ a : D.host.Eˣ, ∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| ^ (-(W.rank : ℝ) / 2) : ℝ) : ℂ) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hvp χ hc k _ σ hσ a
  choose b hb using hvp.1.expW
  obtain ⟨n, hn, hinf⟩ := GlobalTheory.HeckeInfExp.hasInfQ_of_hasInfExp D χW χ _ hc hb
  have hn' : ∀ τ, n τ = 2 * b τ + (W.rank : ℤ) := fun τ => by
    have : (n τ : ℚ) = ((2 * b τ + (W.rank : ℤ) : ℤ) : ℚ) := by rw [hn]; push_cast; ring
    exact_mod_cast this
  have hnorm : ∏ τ, ‖tauE D τ (a : D.host.E)‖ ^ 2 = |((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (mk_tauE_complex D τ)]
    rfl
  have hA : ∏ τ, (tauE D τ (a : D.host.E) ^ ((b τ : ℤ) + (W.rank : ℤ)) *
      ((starRingEnd ℂ (tauE D τ (a : D.host.E))) ^ (b τ : ℤ))⁻¹) ∈ σ.fieldRange := by
    refine prod_mem fun τ _ => mul_mem (zpow_mem ?_ _) (inv_mem (zpow_mem ?_ _))
    · obtain ⟨y, hy⟩ := hσ (tauE D τ) a
      exact ⟨y, hy⟩
    · obtain ⟨y, hy⟩ := hσ ((starRingEnd ℂ).comp (tauE D τ)) a
      exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hA
  refine ⟨y, ?_⟩
  rw [hinf a, hy, ← hnorm, ← prod_norm_inv_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hn' τ]
  exact phase_zpow_eq _ ((map_ne_zero _).2 a.ne_zero) _ W.rank

end GlobalTheory.LevelSeries
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RapidKernelDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_inv (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_vecMul (x : Fin a → Ad E) (m : GA E a) :
    (fun i => pFin E ((x ᵥ* m.val) i)) = (fun i => pFin E (x i)) ᵥ* m.val.map (pFin E) := by
  funext i

  simp [vecMul, dotProduct, map_sum]

theorem norm_vecMul_infGL_le (y : GL (Fin a) (Cinf E)) (x : Fin a → Ad E) :
    ‖fun i => pInf E ((x ᵥ* (infGL E a y).val) i)‖ ≤ (a * height y) * ‖fun i => pInf E (x i)‖ := by
  have hy : ∀ j i, ‖pInf E ((infGL E a y).val j i)‖ ≤ height y := by
    intro j i
    have e : pInf E ((infGL E a y).val j i) = y.val j i :=
      congrArg (fun u : GL (Fin a) (Cinf E) => u.val j i) (pInf_infGL (E := E) y)
    rw [e]
    have : ‖y.val j i‖ ≤ ‖toL y.val‖ :=
      (norm_le_pi_norm (toL y.val j) i).trans (norm_le_pi_norm (toL y.val) j)
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h1 := one_le_height y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_

  simp only [vecMul, dotProduct, map_sum, map_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (height y * ‖fun i => pInf E (x i)‖)
    fun j _ => ?_).trans ?_)
  · rw [mul_comm (height y)]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm (fun i => pInf E (x i)) j) (hy j i)
      (norm_nonneg _) (norm_nonneg _))
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)

theorem ideleModule_det_infGL_le (z : GL (Fin a) (Cinf E)) :
    (ideleModule E (GeneralLinearGroup.det (infGL E a z)) : ℝ) ≤
      ((a.factorial : ℝ) * height z ^ a) ^ (2 * Fintype.card (InfinitePlace E)) := by
  set u := GeneralLinearGroup.det (infGL E a z) with hu
  have hB : 1 ≤ (a.factorial : ℝ) * height z ^ a :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast a.factorial_pos) (one_le_pow₀ (one_le_height z))
  have hinf : pInf E (u : Ad E) = (GeneralLinearGroup.det z : Cinf E) := by
    rw [hu, ← CuspRep.det_map, pInf_infGL]
  have hfin : pFin E (u : Ad E) = 1 := by
    rw [hu, ← CuspRep.det_map, pFin_infGL, map_one, Units.val_one]
  rw [ideleModule_eq]
  have h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(u : Ad E).2 v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      have : (u : Ad E).2 = 1 := hfin
      rw [this]
      exact norm_one
  rw [h2, mul_one, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => ?_
  have h1 : ‖(u : Ad E).1 w‖ ≤ a.factorial * height z ^ a := by
    rw [← norm_pInf_apply, hinf]
    exact (norm_le_pi_norm _ w).trans (norm_det_le _ (by unfold height; linarith [norm_nonneg (toL (z⁻¹).val)]))
  have hm : w.mult ≤ 2 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (pow_le_pow_right₀ hB hm)

end GlobalTheory.RapidKernelDecay

namespace GlobalTheory.RapidKernelDecay

theorem decays_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
    GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F →
      GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF L hL C₀ hC₀ N
  obtain ⟨-, -, hkI⟩ := hk
  obtain ⟨C, hC⟩ := hF L hL C₀ hC₀ N
  obtain ⟨M₁, hM₁, h₁⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀
  obtain ⟨M₂, hM₂, h₂⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀.inv
  set n := a * Module.finrank ℚ E with hn
  set p := 2 * Fintype.card (InfinitePlace E) with hp
  set K₀ : ℝ := (M₂ * a * M₁) ^ n * (a.factorial : ℝ) ^ p with hK₀
  set m := n + a * p with hm
  set I := ∫ x, ‖k x‖ * height (γ x) ^ (m * N) ∂ν with hI
  refine ⟨I * (|C| * K₀ ^ N), fun g c hc ξ hξ hξL => ?_⟩
  set v : Fin a → Ad E := fun j => algebraMap E (Ad E) (ξ j) with hv
  set Xn := ‖fun i => pInf E ((v ᵥ* g.val) i)‖ with hXn
  set G := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hG
  have hGpos : 0 < G := (ideleModule E _).2
  have key : ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * c * infGL E a y)‖ ≤ |C| * K₀ ^ N * height y ^ (m * N) * (Xn ^ n / G) ^ N := by
    intro y
    have hy1 := one_le_height y
    set g' := g * c * infGL E a y * c⁻¹ with hg'
    have eg : g * c * infGL E a y = g' * c := (inv_mul_cancel_right _ c).symm
    have hfin : (fun i => pFin E ((v ᵥ* g'.val) i)) = (fun i => pFin E ((v ᵥ* g.val) i)) := by
      rw [pFin_vecMul, pFin_vecMul]
      congr 1
      show (GeneralLinearGroup.map (pFin E) g').val = (GeneralLinearGroup.map (pFin E) g).val
      simp [hg', map_mul, map_inv, pFin_infGL]
    have hinf : ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ≤ M₂ * a * M₁ * height y * Xn := by
      have e : v ᵥ* g'.val = ((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) ᵥ* (c⁻¹ : GA E a).val := by
        simp only [hg', Units.val_mul, vecMul_vecMul]
      rw [e]
      calc _ ≤ M₂ * ‖fun i => pInf E (((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) i)‖ :=
            h₂ c⁻¹ (Set.inv_mem_inv.2 hc) _
        _ ≤ M₂ * ((a * height y) * ‖fun i => pInf E ((v ᵥ* g.val ᵥ* c.val) i)‖) :=
            mul_le_mul_of_nonneg_left (norm_vecMul_infGL_le y _) hM₂.le
        _ ≤ M₂ * ((a * height y) * (M₁ * Xn)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h₁ c hc _) (by positivity)) hM₂.le
        _ = _ := by ring
    set D := (ideleModule E (GeneralLinearGroup.det (infGL E a y)) : ℝ) with hD
    have hDpos : 0 < D := (ideleModule E _).2
    have hdet : (ideleModule E (GeneralLinearGroup.det g') : ℝ) = G * D := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det g * GeneralLinearGroup.det (infGL E a y) := by
        simp only [hg', map_mul, map_inv]
        rw [mul_right_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]
      rw [this, map_mul, Positive.val_mul]
    have hDinv : D⁻¹ ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by
      have h := ideleModule_det_infGL_le (E := E) y⁻¹
      rw [height_inv] at h
      have hDD : D * (ideleModule E (GeneralLinearGroup.det (infGL E a y⁻¹)) : ℝ) = 1 := by
        rw [hD, ← Positive.val_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one]
        rfl
      rw [eq_inv_of_mul_eq_one_right hDD] at h
      exact h
    have hq : (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ≤
        K₀ * height y ^ m * (Xn ^ n / G) := by
      rw [hdet]
      have hXn0 : 0 ≤ Xn := norm_nonneg _
      have hb0 : 0 ≤ M₂ * a * M₁ * height y * Xn := by
        have := hM₁.le; have := hM₂.le; positivity
      have hc0 : 0 ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by positivity
      calc _ = ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n * D⁻¹ / G := by ring
        _ ≤ (M₂ * a * M₁ * height y * Xn) ^ n * ((a.factorial : ℝ) * height y ^ a) ^ p / G :=
            div_le_div_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hinf n) hDinv
              (inv_nonneg.2 hDpos.le) (pow_nonneg hb0 _)) hGpos.le
        _ = _ := by rw [hK₀, hm, pow_add, pow_mul]; ring
    have hL' : (fun i => pFin E ((v ᵥ* g'.val) i)) ∈ L := hfin ▸ hξL
    have hF' := hC g' c hc ξ hξ hL'
    rw [eg]
    have hnn : 0 ≤ (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
      pow_nonneg (div_nonneg (pow_nonneg (norm_nonneg _) _) (ideleModule E _).2.le) _
    calc ‖F (g' * c)‖ ≤ |C| * (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n /
          (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
          hF'.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnn)
      _ ≤ |C| * (K₀ * height y ^ m * (Xn ^ n / G)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (pow_nonneg (norm_nonneg _) _)
            (ideleModule E _).2.le) hq N) (abs_nonneg C)
      _ = _ := by ring
  have hint : Integrable (fun x => ‖k x‖ * height (γ x) ^ (m * N)) ν := hkI (m * N)
  show ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖ ≤ I * (|C| * K₀ ^ N) * (Xn ^ n / G) ^ N
  calc ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖
      ≤ ∫ x, ‖k x‖ * height (γ x) ^ (m * N) * (|C| * K₀ ^ N * (Xn ^ n / G) ^ N) ∂ν :=
        norm_integral_le_of_norm_le (hint.mul_const _) (.of_forall fun x => by
          rw [norm_mul]
          calc ‖k x‖ * ‖F (g * c * infGL E a (γ x))‖
              ≤ ‖k x‖ * (|C| * K₀ ^ N * height (γ x) ^ (m * N) * (Xn ^ n / G) ^ N) :=
                mul_le_mul_of_nonneg_left (key _) (norm_nonneg _)
            _ = _ := by ring)
    _ = _ := by rw [integral_mul_const, hI]; ring

end GlobalTheory.RapidKernelDecay
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.contragredient_polynomialWeight_unique_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  first | exact @GlobalTheory.mtRatDual_hw | exact GlobalTheory.mtRatDual_hw | (intros; apply GlobalTheory.mtRatDual_hw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical




namespace GlobalTheory.HalfFrameLift

theorem exists_half_redM_frMapO : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP), ∃ u : WO S T, IsHalf e u ∧ IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ Q, redM PP (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) = y PP := by
  intro D S T βS βT Q e he ϖ hϖ y
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  subst hsum
  choose N hN hNe hNr using fun (i : Fin T.rank) (j : Fin S.rank) =>
    GlobalTheory.T.exists_integral_lift_residues_idempotentSum D Q es hes hc (fun PP => y PP i j)
  set e := ∑ PP ∈ Q, es PP with he_def
  let z : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of N
  let A : Matrix (Fin T.rank) (Fin S.rank) (EAf D) :=
    ((βT.val : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) * z : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) *
      ((βS⁻¹).val : Matrix (Fin S.rank) (Fin S.rank) (EAf D))
  choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) =>
    GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) (A i j)
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ
  have hinv : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hϖ', map_one]
  let u : WO S T := Matrix.of fun i j => e * incA D (ϖ : D.host.E)⁻¹ * w i j
  have key : frMapO S T βS βT (u.map fun v => incA D (ϖ : D.host.E) * v) = z := by
    have hmap : (u.map fun v => incA D (ϖ : D.host.E) * v).map (toEAf D) = toEAf D e • A := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, u, Matrix.of_apply]
      rw [← hw i j, ← map_mul]
      congr 1
      linear_combination (e * w i j) * hinv
    unfold frMapO
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, z, Matrix.of_apply]
    exact hNe i j
  refine ⟨u, fun i j => ?_, ?_, fun PP hPP => ?_⟩
  · show e * (e * incA D (ϖ : D.host.E)⁻¹ * w i j) = e * incA D (ϖ : D.host.E)⁻¹ * w i j
    rw [← mul_assoc, ← mul_assoc, hee]
  · rw [key]; exact fun i j => hN i j
  · rw [key]
    funext i j
    exact (dif_pos (hN i j)).trans (hNr i j PP hPP)

end GlobalTheory.HalfFrameLift
end

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist.BaseInhab

open GlobalTheory.ExportSeries

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (n : ℕ) (hn : 0 < n) :
    ChrEq (c ^ n) (χ ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n _ ih => rw [pow_succ, pow_succ]; exact GlobalTheory.TowerCharRead.chrEq_mul ih h

end GlobalTheory.ConjTwist.BaseInhab
end
end
