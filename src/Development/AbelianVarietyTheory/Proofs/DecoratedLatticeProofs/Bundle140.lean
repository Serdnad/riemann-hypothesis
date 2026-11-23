module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.VacRead

variable {D : D7}

theorem eq_of_comp {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (w w' : Mx D m n)
    (hw : w.map (finPart D) = 0) (hw' : w'.map (finPart D) = 0) (h : ∀ τ, compAt θ τ w = compAt θ τ w') : w = w' := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have e1 : finPart D (w i j) = 0 := congrFun (congrFun hw i) j
    have e2 : finPart D (w' i j) = 0 := congrFun (congrFun hw' i) j
    rw [RingHom.map_sub, e1, e2, sub_zero]
  · have e : θ τ (infPart D (w i j)) = θ τ (infPart D (w' i j)) := congrFun (congrFun (h τ) i) j
    rw [RingHom.map_sub, RingHom.map_sub, e, sub_self]

theorem realPt_eq {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (w : Mx D m n)
    (hw : w.map (finPart D) = 0) (hz : ∀ τ, compAt θ τ w = z τ) : realPt θ z = w := by
  have hs : (realPt θ z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (realPt θ z) = z τ := by
    unfold realPt
    exact Classical.epsilon_spec (p := fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ) ⟨w, hw, hz⟩
  exact eq_of_comp hθ _ _ hs.1 hw fun τ => (hs.2 τ).trans (hz τ).symm

theorem hAt_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (τ : D.what₂.Tau)
    (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.VacUnique.hAt S T τ x y = ∑ i, ∑ j, x i j * starRingEnd ℂ (y i j) := by
  have h1 : gramAt D S τ = 1 := by
    unfold gramAt; rw [hS]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : gramAt D T τ = 1 := by
    unfold gramAt; rw [hT]; exact Matrix.map_one _ (map_zero _) (map_one _)
  unfold GlobalTheory.VacUnique.hAt
  rw [h1, h2, inv_one, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead
variable {D : D7}

theorem xiN_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (δ : ℂ) (sc : ℝ) (hδ : δ ≠ 0) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (h0 : xiN θ S T hS hT δ sc f = 0) : f = 0 := by
  subst hS hT
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf fun w hw => ?_
  have h1 := congrFun h0 (fun τ i j => -(δ * compAt θ τ w i j))
  have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * (fun τ i j => -(δ * compAt θ τ w i j) :
      VCx D.what₂.Tau S.rank T.rank) τ (Fin.cast rfl i) (Fin.cast rfl j))) = w := by
    refine realPt_eq hθ _ w hw fun τ => ?_
    funext i j
    simp only [Matrix.of_apply, Fin.cast_eq_self]
    field_simp
  unfold xiN at h1
  rw [hp, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Complex.exp_ne_zero _)

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead

theorem key_sum {ι : Type} [Fintype ι] (r0 k : ℝ) (s : ι → ℂ) :
    ((∑ τ, 2 * (Complex.I * (r0 : ℂ) * (k : ℂ) * s τ).re : ℝ) : ℂ) +
      Complex.I * ((∑ τ, 2 * (Complex.I * (r0 : ℂ) * (k : ℂ) * (-Complex.I * s τ)).re : ℝ) : ℂ) =
      2 * Complex.I * ((r0 * k : ℝ) : ℂ) * ∑ τ, s τ := by
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem scale_eq (x y sc : ℝ) (hy : y ≠ 0) (h : sc * y = 2 * x) : x * y⁻¹ = sc / 2 := by
  field_simp
  linarith

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead
variable {D : D7}
open GlobalTheory.FockCompare

theorem xiN_differentiable (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (δ : ℂ) (sc : ℝ) (ψ : AddChar (AF D.host.F) ℂ) (hP : StdPair θ S T δ sc ψ) (f : WO S T → ℂ)
    (hf : IsHol θ S T ψ f) : Differentiable ℂ (xiN θ S T hS hT δ sc f) := by
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hP.inf
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hP.std S T (fun _ => 1) (fun _ => 1) f
    hf.1 hf.2
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set r : ℝ := sc / 2 with hr
  let L : RW T S →L[ℂ] RW T S := (-δ⁻¹) • ContinuousLinearMap.id ℂ (RW T S)
  have hL : ∀ Z τ i j, L Z τ i j = -(δ⁻¹ * Z τ i j) := fun Z τ i j => by simp [L]
  set E : RW T S → ℂ := fun Z => Complex.exp ((Real.pi * r * ∑ τ, ∑ i, ∑ j, ‖Z τ i j‖ ^ 2 : ℝ) : ℂ) with hE
  have hxi : xiN θ S T rfl rfl δ sc f = fun Z => F (L Z) * E Z := by
    funext Z
    unfold xiN
    have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * Z τ (Fin.cast rfl i) (Fin.cast rfl j))) =
        iotaW σ T S (L Z) := by
      refine realPt_eq hP.inf _ _ (by funext i j; exact hσ.fin _) fun τ => ?_
      funext i j
      show θ τ (infPart D (σ fun τ' => L Z τ' i j)) = _
      rw [hσ.comp]
      simp [hL]
    rw [hp, mul_comm]
    congr 2
    show (Real.pi : ℂ) / 2 * ((sc : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j)) = _
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hr]; push_cast; ring
  rw [hxi]
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (L Z)) Z Y = fderiv ℝ F (L Z) (L Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (L Z)) ((fderiv ℝ F (L Z)).comp (L.restrictScalars ℝ)) Z :=
      (hF (L Z)).hasFDerivAt.comp Z (L.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]; rfl
  refine GlobalTheory.FockPos.differentiable_mul_of_cr (fun Z => F (L Z)) E
    (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ))
    (hF.comp (L.restrictScalars ℝ).differentiable) (GlobalTheory.FockPos.gauss_cr r).1 (fun Z Y => ?_)
    (GlobalTheory.FockPos.gauss_cr r).2
  rw [hdG, hdG]
  have hj : GlobalTheory.VacUnique.jO S T (fun _ => 1) (fun _ => 1) (L Y) = L (Complex.I • Y) := by
    rw [L.map_smul]; funext τ; rw [GlobalTheory.VacUnique.jO_apply]
    change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (L Y τ) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
    rw [Matrix.one_mul, Matrix.mul_one]; rfl
  have h := hann (L Z) (L Y)
  rw [hj] at h
  have hdd : δ⁻¹ * starRingEnd ℂ δ⁻¹ = (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hom : ∀ Y' : RW T S, GlobalTheory.VacUnique.omO S T (L Z) (L Y') =
      ∑ τ, 2 * (Complex.I * (((Real.sqrt D.host.d)⁻¹ : ℝ) : ℂ) * (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j)).re := by
    intro Y'
    rw [GlobalTheory.VacUnique.omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (L Z τ) (L Y' τ)).re = _
    rw [hP.xi τ]
    erw [hAt_one S T hP.gS hP.gT τ (L Z τ) (L Y' τ)]
    have hs : ∑ i, ∑ j, L Z τ i j * starRingEnd ℂ (L Y' τ i j) =
        (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hL, hL, ← hdd]
      simp only [map_neg, map_mul]
      ring
    rw [hs]
    congr 2
    ring
  rw [hom, hom] at h
  have hs2 : ∀ τ, (∑ i, ∑ j, Z τ i j * starRingEnd ℂ ((Complex.I • Y) τ i j)) =
      -Complex.I * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) := fun τ => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hs2] at h
  have key := key_sum ((Real.sqrt D.host.d)⁻¹) ((‖δ‖ ^ 2)⁻¹) fun τ => ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)
  have hrk : (Real.sqrt D.host.d)⁻¹ * (‖δ‖ ^ 2)⁻¹ = r :=
    scale_eq _ _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hP.ne)) hP.scale
  rw [hrk] at key
  show _ = -((2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ) * F (L Z))
  linear_combination h + Real.pi * Complex.I * F (L Z) * key +
    2 * Real.pi * r * (∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)) * F (L Z) * Complex.I_sq

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead

theorem xiN_entire_and_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ)
    (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ →
    (∀ f, IsHol θ S T ψ f → Differentiable ℂ (xiN θ S T hS hT δ sc f)) ∧
      ∀ f, IsThetaFunO ψ S T f → xiN θ S T hS hT δ sc f = 0 → f = 0 := by
  intro D ψ θ S T a b hS hT δ sc hP
  exact ⟨fun f hf => xiN_differentiable θ S T hS hT δ sc ψ hP f hf,
    fun f hf h0 => xiN_eq_zero θ hP.inf S T hS hT δ sc hP.ne ψ f hf h0⟩

end GlobalTheory.AdForm.VacRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.HeisRead

variable {D : D7}


open GlobalTheory.FockCompare in
theorem realPt_eq_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (S T : HSp D) (Z : RW T S) :
    realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => Z τ i j) = iotaW σ T S Z := by
  have hex : ∃ w : Mx D T.rank S.rank, w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Matrix.of fun i j => Z τ i j :=
    ⟨iotaW σ T S Z, hσ.real_iota T S Z, fun τ => congrFun (hσ.pi_iota T S Z) τ⟩
  have hs := Classical.epsilon_spec hex
  exact hσ.real_ext hs.1 (hσ.real_iota T S Z) (funext fun τ => (hs.2 τ).trans (congrFun (hσ.pi_iota T S Z) τ).symm)

theorem embH_toHom_apply (S T : HSp D) (δ : ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (τ : D.what₂.Tau)
    (i : Fin T.rank) (j : Fin S.rank) :
    embH (tauE D) δ (toHom S T rfl rfl γ) τ i j = δ * tauE D τ (γ i j) := by
  simp [embH, toHom, Matrix.toLin'_apply]

end GlobalTheory.AdForm.HeisRead

namespace GlobalTheory.AdForm.HeisRead

theorem term_eq (k sc : ℝ) (δ w g : ℂ) (hδ : δ ≠ 0) (hsc : sc * ‖δ‖ ^ 2 = 2 * k) :
    2 * (Complex.I * (k : ℂ) * ((starRingEnd ℂ) g * -(δ⁻¹ * w))).re = ((sc : ℂ) * (w * (starRingEnd ℂ) (δ * g))).im := by
  have hn : Complex.normSq δ ≠ 0 := Complex.normSq_pos.2 hδ |>.ne'
  have hsc' : sc = 2 * k / Complex.normSq δ := by
    rw [Complex.normSq_eq_norm_sq, eq_div_iff (by rwa [← Complex.normSq_eq_norm_sq]), hsc]
  subst hsc'
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  rw [Complex.normSq_apply] at hn ⊢
  field_simp
  ring
end GlobalTheory.AdForm.HeisRead

namespace GlobalTheory.AdForm.HeisRead
variable {D : D7}

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = starRingEnd ℂ (HV sc z w) := by

  simp only [HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _


open GlobalTheory.OrientedHeis in
theorem omO_eq_im (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (δ : ℂ) (sc : ℝ) (hP : StdPair θ S T δ sc ψ)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : VCx D.what₂.Tau S.rank T.rank) :
    omO S T (fun τ i j => -(δ⁻¹ * z τ i j)) (fun τ i j => tauE D τ (γ i j)) =
      (HV sc z (embH (tauE D) δ (toHom S T rfl rfl γ))).im := by
  simp only [omO, LinearMap.mk₂_apply, HV, LinearMap.mk₂'ₛₗ_apply, embH_toHom_apply, formAt, hP.gS, hP.gT, inv_one,
    Matrix.one_apply, apply_ite (tauE D _), map_one, map_zero, hP.xi]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hin : ∀ τ (x1 : Fin S.rank), (∑ x2 : Fin S.rank, ∑ x3 : Fin T.rank, if x1 = x2 then (starRingEnd ℂ) ((tauE D τ) (γ x3 x2)) * -(δ⁻¹ * z τ x3 x1) else 0) =
      ∑ x3 : Fin T.rank, (starRingEnd ℂ) ((tauE D τ) (γ x3 x1)) * -(δ⁻¹ * z τ x3 x1) := fun τ x1 => by
    rw [Finset.sum_comm]; simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [hin]
  rw [Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact term_eq _ sc δ _ _ hP.ne hP.scale
end GlobalTheory.AdForm.HeisRead
namespace GlobalTheory.AdForm.HeisRead


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis in
theorem xiN_heisO_finOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ f, IsThetaFunO ψ S T f → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → xiN θ S T hS hT δ sc (heisO ψ S T v f) = Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT γ)) (xiN θ S T hS hT δ sc f) := by
  intro D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hP.inf
  funext z
  let G : RW T S := fun τ i j => tauE D τ (γ i j)
  let Z : RW T S := fun τ i j => -(δ⁻¹ * z τ i j)
  have hrat : ratW T S γ = v + iotaW σ T S G := by
    have h1 : ratW T S γ - v = iotaW σ T S G := by
      refine hσ.real_ext (x := ratW T S γ - v) ?_ (hσ.real_iota _ _ _) ?_
      · show (ratW T S γ - v).map (finPart D) = 0
        rw [Matrix.map_sub _ (finPart D).map_sub, hv.2, sub_self]
      · rw [hσ.pi_iota, map_sub]
        funext τ i j
        have h0 : piW θ T S v τ i j = 0 := by
          show θ τ (infPart D (v i j)) = 0
          rw [show infPart D (v i j) = 0 from congrFun (congrFun hv.1 i) j, map_zero]
        show θ τ (infPart D (incA D (γ i j))) - piW θ T S v τ i j = _
        rw [h0, sub_zero, comp_incA hP.inf]
    rw [← h1]; abel
  have hX : ∀ τ i j, embH (tauE D) δ (toHom S T rfl rfl γ) τ i j = δ * tauE D τ (γ i j) :=
    GlobalTheory.AdForm.HeisRead.embH_toHom_apply S T δ γ
  have hp : realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast rfl i) (Fin.cast rfl j))) = iotaW σ T S Z := by
    simpa using GlobalTheory.AdForm.HeisRead.realPt_eq_iota hσ S T Z
  have hp' : realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => -(δ⁻¹ * (z + embH (tauE D) δ (toHom S T rfl rfl γ)) τ (Fin.cast rfl i) (Fin.cast rfl j))) = iotaW σ T S (Z - G) := by
    rw [← GlobalTheory.AdForm.HeisRead.realPt_eq_iota hσ S T (Z - G)]
    congr 1
    funext τ i j
    simp only [Fin.cast_eq_self, Pi.add_apply, hX, Matrix.of_apply, Pi.sub_apply, Z, G]
    field_simp [hP.ne]
    ring
  unfold xiN Formalism.L2.Th1.H.opU heisO
  beta_reduce
  rw [hp, hp']
  have e0 : symplOH S T (iotaW σ T S Z) v = 0 := GlobalTheory.FinTranslate.symplOH_real_fin hv.1 (hσ.real_iota _ _ _)
  have e1 : iotaW σ T S Z + v = ratW T S γ + iotaW σ T S (Z - G) := by rw [hrat, map_sub]; abel
  have e2 : f (ratW T S γ + iotaW σ T S (Z - G)) = ψ (symplOH S T (iotaW σ T S (Z - G)) (iotaW σ T S G)) * f (iotaW σ T S (Z - G)) := by
    rw [hf.quasi, ← GlobalTheory.FinTranslate.symplOH_skew, hrat, symplOH_add_right,
      GlobalTheory.FinTranslate.symplOH_real_fin hv.1 (hσ.real_iota _ _ _), zero_add]
  have e3 : ψ (symplOH S T (iotaW σ T S (Z - G)) (iotaW σ T S G)) =
      Complex.exp (-(Real.pi * Complex.I) * ((HV sc z (embH (tauE D) δ (toHom S T rfl rfl γ))).im : ℂ)) := by
    rw [psi_symplOH hσ hP.std, hσ.pi_iota, LinearMap.map_sub₂, omO_self hσ, sub_zero]
    exact congrArg (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (t : ℂ)))
      (GlobalTheory.AdForm.HeisRead.omO_eq_im θ ψ S T δ sc hP γ z)
  rw [e0, AddChar.map_zero_eq_one, one_mul, e1, e2, e3]
  set X := embH (tauE D) δ (toHom S T rfl rfl γ)
  have hadd : HV sc (z + X) (z + X) = HV sc z z + HV sc z X + HV sc X z + HV sc X X := by
    simp only [map_add (f := _), LinearMap.add_apply]; ring
  have hc : HV sc X z = starRingEnd ℂ (HV sc z X) := GlobalTheory.AdForm.HeisRead.HV_conj sc z X
  have hcj : starRingEnd ℂ (HV sc z X) = HV sc z X - 2 * Complex.I * ((HV sc z X).im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [← mul_assoc, ← Complex.exp_add, mul_right_comm, ← Complex.exp_add]
  congr 2
  rw [hadd, hc, hcj]
  ring

end GlobalTheory.AdForm.HeisRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatPairMove

variable {D : D7}

def finGL (V : HSp D) (g : GA D V) : GL (Fin V.rank) (EAf D) where
  val := (mt V g).map (toEAf D)
  inv := (mt V g⁻¹).map (toEAf D)
  val_inv := by
    rw [← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  inv_val := by
    rw [← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mul (V : HSp D) (g h : GA D V) :
    (finGL V (g * h)).val = (mt V g).map (toEAf D) * (finGL V h).val := by
  change (mt V (g * h)).map (toEAf D) = _
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]
  rfl

theorem latFr_rfl (V : HSp D) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    GlobalTheory.AdForm.latFr V rfl N = (N : Set (Fin V.rank → D.host.E)) := by
  ext x
  exact Iff.rfl

theorem eq_lat_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hN : Moves V rfl g N) : N = GlobalTheory.NormSum.AdLattice.lat (finGL V g) := by
  ext x
  rw [GlobalTheory.NormSum.AdLattice.mem_lat, hN x]
  rfl

theorem latO_move : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (g s : GA D S) (h s' : GA D T) N N' N₁ N₁', Moves S hS g N → Moves T hT h N' → Moves S hS (s * g) N₁ → Moves T hT (s' * h) N₁' → ∀ u : WO S T, u ∈ (latO S T (latFr S hS N₁) (latFr T hT N₁') fun _ => True) ↔ ∃ u₀ ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), u = actO S T s s' u₀ := by
  intro D S T a b hS hT g s h s' N N' N₁ N₁' hN hN' hN₁ hN₁' u
  subst hS hT
  rw [latFr_rfl, latFr_rfl, latFr_rfl, latFr_rfl]
  obtain rfl := eq_lat_of_moves S g N hN
  obtain rfl := eq_lat_of_moves T h N' hN'
  obtain rfl := eq_lat_of_moves S (s * g) N₁ hN₁
  obtain rfl := eq_lat_of_moves T (s' * h) N₁' hN₁'
  exact GlobalTheory.AdelicLatMove.mem_latO_iff_exists_actO D S T s s' _ _ _ _ (finGL S g) (finGL S (s * g)) (finGL T h)
    (finGL T (s' * h)) (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.StdFrames.isFrame_lat _)
    (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice
    (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (finGL_mul S s g)
    (finGL_mul T s' h) u

end GlobalTheory.LatPairMove
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := by
  intro w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  exact (GlobalTheory.SmoothCyclic.sm_eq M τ).ge (h.2.2.1 w hw)

theorem tprod_eq_zero_of_kFin_off (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) (hΛ : SepCont M Λ)
    (h0 : ∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) (s : Finset D.what₂.Tau) :
    ∀ v : M.Vec, (∀ τ, τ ∉ s → IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)) → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  induction s using Finset.induction_on with
  | empty => exact fun v hv => h0 v fun τ => hv τ (Finset.notMem_empty τ)
  | insert a s ha ih =>
    intro v hv
    obtain ⟨ℓ, hℓ, hℓv⟩ := hΛ a v
    have hk : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M a, ℓ w = 0 := by
      intro w hw
      rw [hℓv ⟨w, kFin_le_sm hHC M a hw⟩]
      refine ih _ fun τ hτ => ?_
      by_cases e : τ = a
      · subst e
        rw [Function.update_self]
        exact hw
      · rw [Function.update_of_ne e]
        exact hv τ (by simp [e, hτ])
    have := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D V S M a ℓ hℓ hk (v a) (v a).2
    rw [hℓv (v a), Function.update_eq_self] at this
    exact this

theorem eq_zero_of_sepCont : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ), SepCont M Λ → (∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) → Λ = 0 := by
  intro hHC D V S M Λ hΛ h0
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
  exact tprod_eq_zero_of_kFin_off hHC M Λ hΛ h0 Finset.univ v fun τ hτ => absurd (Finset.mem_univ τ) hτ

end GlobalTheory.Core.Mi
end
