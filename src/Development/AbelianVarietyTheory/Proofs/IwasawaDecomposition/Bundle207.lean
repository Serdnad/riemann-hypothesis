module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle202
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle010
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def gauss (F : Fock (Ix P Q)) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) (x : Ix P Q → ℂ) : F.H :=
  (GlobalTheory.T.fock_existsUnique_gaussian_vector P Q F A x h).exists.choose

theorem hasCoeff_gauss (F : Fock (Ix P Q)) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) : HasCoeff F (gauss F h x) (expPS (gaussPoly A x)) :=
  (GlobalTheory.T.fock_existsUnique_gaussian_vector P Q F A x h).exists.choose_spec

theorem gauss_congr (F : Fock (Ix P Q)) {A B : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (h' : (1 - Bᴴ * B).PosDef) {x y : Ix P Q → ℂ} (e : A = B) (e' : x = y) : gauss F h x = gauss F h' y := by
  subst e e'; rfl

abbrev Par (P Q : ℕ) : Type :=
  ℂ × {Y : Matrix (Ix P Q) (Fin Q) ℂ // IsNeg Y} × (Ix P Q → ℂ) × (Ix P Q → ℂ)

def vec (F : Fock (Ix P Q)) (p : Par P Q) : F.H :=
  (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) • gauss F p.2.1.2.posDef (linX p.2.1.1 p.2.2.1 p.2.2.2)

def act (T0 : GrpData P Q) (g : T0.G) (p : Par P Q) : Par P Q :=
  ((T0.sq g : ℂˣ) * p.1, ⟨(T0.cov g : Mat P Q) * p.2.1.1, p.2.1.2.mul (T0.cov_mem g)⟩,
    (T0.cov g : Mat P Q) *ᵥ p.2.2.1, p.2.2.2 ᵥ* (T0.cov g⁻¹ : Mat P Q))

def base (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) (x : Ix P Q → ℂ) : Par P Q :=
  (c, ⟨baseY A, isNeg_baseY h⟩, baseV x, baseF x)

theorem vec_base (F : Fock (Ix P Q)) (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) : vec F (base c h x) = c • gauss F h x := by
  simp only [vec, base, scal_base, mul_one]
  rw [gauss_congr F _ h (matA_baseY A) (linX_base A x)]

theorem inner_vec (F : Fock (Ix P Q)) (p q : Par P Q) :
    inner ℂ (vec F p) (vec F q) = star p.1 * q.1 * ker p.2.1.1 p.2.2.1 p.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2 := by
  obtain ⟨c, ⟨Y, hY⟩, v, φ⟩ := p
  obtain ⟨c', ⟨Y', hY'⟩, v', φ'⟩ := q
  have h1 := GlobalTheory.T.inner_gaussianVectors_fockSpace P Q F _ _ _ _ hY.posDef hY'.posDef _ _
    (hasCoeff_gauss F hY.posDef (linX Y v φ)) (hasCoeff_gauss F hY'.posDef (linX Y' v' φ'))
  have h2 := GlobalTheory.T.gaussian_inner_eq_invariantKernel P Q Y Y' v φ v' φ' hY.isUnit hY'.isUnit (GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions P Q _ _ hY.posDef hY'.posDef)
  simp only at h1 h2 ⊢
  simp only [vec, inner_smul_left, inner_smul_right, h1, ← h2, map_mul, starRingEnd_apply]
  ring

theorem isUnit_form {Y Y' : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) (h' : IsNeg Y') :
    IsUnit (Yᴴ * Jm P Q * Y').det := by
  have h1 : IsUnit (-(Yᴴ * Jm P Q * Y')).det := by
    rw [form_factor Y Y' h.isUnit h'.isUnit, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact (h.isUnit.star.mul (GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions P Q _ _ h.posDef h'.posDef)).mul h'.isUnit
  rw [Matrix.det_neg] at h1
  exact isUnit_of_mul_isUnit_right h1

theorem dense_vec (F : Fock (Ix P Q)) : Dense (Submodule.span ℂ (Set.range (vec F)) : Set F.H) := by
  have h0 : (1 - (0 : Matrix (Fin P) (Fin Q) ℂ)ᴴ * (0 : Matrix (Fin P) (Fin Q) ℂ)).PosDef := by
    simpa using Matrix.PosDef.one
  refine (GlobalTheory.T.dense_span_coherent_vectors_fock P Q F (gauss F h0) (hasCoeff_gauss F h0)).mono (Submodule.span_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨base 1 h0 x, by rw [vec_base, one_smul]⟩

theorem exists_rep (T0 : GrpData P Q) (F : Fock (Ix P Q)) :
    ∃ π : T0.G →* (F.H →L[ℂ] F.H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧
      ∀ g p, π g (vec F p) = vec F (act T0 g p) := by
  have hc : Continuous fun g : T0.G => (T0.cov g : Mat P Q) :=
    Units.continuous_val.comp (continuous_fst.comp T0.emb.continuous)
  refine GlobalTheory.T.exists_unitaryRep_of_action_on_total_family T0.G (Par P Q) F.H (act T0) (vec F) (fun p => ?_) (fun g h p => ?_) (dense_vec F)
    (fun g p q => ?_) (fun p q => ?_)
  · simp [act]
  · simp [act, mul_assoc, Matrix.mul_assoc]
  · rw [inner_vec, inner_vec]
    simp only [act]
    rw [ker_mul (T0.cov_mem g) (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])]
    have h : star ((T0.sq g : ℂˣ) : ℂ) * (T0.sq g : ℂˣ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', RealPar.Cover.norm_sq]; simp
    rw [star_mul']
    linear_combination (star p.1 * q.1 * ker p.2.1.1 p.2.2.1 p.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2) * h
  · simp only [inner_vec]
    refine (continuous_const.mul (RealPar.Cover.continuous_sq.mul continuous_const)).mul
      (GlobalTheory.T.continuous_oscillatorGaussianKernel_right P Q T0.G _ _ _ _ _ _ ?_ ?_ ?_ fun g => isUnit_form q.2.1.2 (act T0 g p).2.1.2)
    · exact hc.matrix_mul continuous_const
    · exact hc.matrix_mulVec continuous_const
    · exact continuous_const.matrix_vecMul (hc.comp continuous_inv)

theorem hasDerivAt_exp_entry (X : Mat P Q) (a b : Ix P Q) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem expt_inv (T0 : GrpData P Q) {Z : Mat P Q} (hZ : Z ∈ upq P Q) (t : ℝ) :
    (T0.expt (t • Z))⁻¹ = T0.expt (t • -Z) := by
  rw [inv_eq_iff_mul_eq_one, smul_neg, ← neg_smul, ← T0.expt_add Z hZ, add_neg_cancel, zero_smul, T0.expt_zero]

theorem neg_mem_upq {Z : Mat P Q} (hZ : Z ∈ upq P Q) : -Z ∈ upq P Q := by
  simpa using RealPar.KStabLie.smul_mem_upq hZ (-1)

theorem adjZ_neg {Z : Mat P Q} (hZ : Z ∈ upq P Q) : adjZ (-Z) = Z := by
  have h : Zᴴ * Jm P Q = -(Jm P Q * Z) := eq_neg_of_add_eq_zero_left hZ
  rw [adjZ, Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg,
    ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

theorem hasDerivAt_inner_act (T0 : GrpData P Q) (F : Fock (Ix P Q)) {Z : Mat P Q} (hZ : Z ∈ upq P Q)
    (f : MvPolynomial (Ix P Q) ℂ) (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) :
    HasDerivAt (fun t : ℝ => inner ℂ (F.ι f) (vec F (act T0 (T0.expt (t • Z)) (base c h x))))
      (inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) (vec F (base c h x))) 0 := by
  set g : ℝ → Mat P Q := fun t => (T0.cov (T0.expt (t • Z)) : Mat P Q) with hg
  set g' : ℝ → Mat P Q := fun t => (T0.cov (T0.expt (t • Z))⁻¹ : Mat P Q) with hg'
  have g0 : g 0 = 1 := by simp [hg, T0.expt_zero]
  have g0' : g' 0 = 1 := by simp [hg', T0.expt_zero]
  obtain ⟨hA, hx, hs⟩ := GlobalTheory.T.hasDerivAt_gaussian_parameters_at_identity P Q A x Z g g' g0 g0'
    (fun a b => by
      simpa only [hg, T0.expt_cov _ (RealPar.KStabLie.smul_mem_upq hZ _)] using hasDerivAt_exp_entry Z a b)
    (fun a b => by
      simpa only [hg', expt_inv T0 hZ, T0.expt_cov _ (RealPar.KStabLie.smul_mem_upq (neg_mem_upq hZ) _), Matrix.neg_apply] using
        hasDerivAt_exp_entry (-Z) a b)
  have hn : ∀ t, IsNeg (g t * baseY A) := fun t => (isNeg_baseY h).mul (T0.cov_mem _)
  have hp := GlobalTheory.T.hasDerivAt_inner_polynomial_moving_gaussian P Q F _ _ (fun t => gauss F (hn t).posDef
    (linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t))) _ _ (fun t => hasCoeff_gauss F _ _) hA hx f
  have e0 : gauss F (hn 0).posDef (linX (g 0 * baseY A) (g 0 *ᵥ baseV x) (baseF x ᵥ* g' 0)) = gauss F h x :=
    gauss_congr F _ _ (by rw [g0, Matrix.one_mul, matA_baseY])
      (by rw [g0, g0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base])
  obtain ⟨a1, a2⟩ := GlobalTheory.T.gaussianVector_annihilator_equations P Q F A x _ (hasCoeff_gauss F h x)
  have h5 := ((((RealPar.Cover.hasDerivAt_sq (T := T0) hZ).mul_const c).fun_mul hs).fun_mul hp)
  simp only [vec_base, inner_smul_right, GlobalTheory.T.inner_lieAction_adjoint_gaussian_polynomial P Q F A x _ a1 a2 Z f]
  simp only [vec, inner_smul_right]
  refine h5.congr_deriv ?_
  simp only [e0]
  simp only [g0, g0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, scal_base, zero_smul, T0.expt_zero,
    map_one, Units.val_one]
  ring

theorem exists_isOsc (P Q : ℕ) (T0 : GrpData P Q) (F : Fock (Ix P Q)) :
    ∃ Om : T0.G →* (F.H →L[ℂ] F.H), IsOsc T0 F Om := by
  obtain ⟨π, h1, h2, h3⟩ := exists_rep T0 F
  refine ⟨π, h1, h2, fun Z hZ f => ?_⟩
  refine GlobalTheory.T.hasDerivAt_of_weak_deriv_on_invariant_total_set F.H (fun t => π (T0.expt (t • Z))) (Set.range (vec F)) _ _ ?_ (fun s t => ?_) (fun t => h1 _)
    (fun y => (h2 y).comp (T0.expt_cont.comp_continuous (by fun_prop)
      fun t => RealPar.KStabLie.smul_mem_upq hZ t)) (dense_vec F) ?_ ?_
  · simp [T0.expt_zero]
  · simp only [T0.expt_add Z hZ, map_mul]
  · rintro t _ ⟨p, rfl⟩
    exact ⟨_, (h3 _ p).symm⟩
  · rintro _ ⟨p, rfl⟩
    have e : vec F p = vec F (base (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) p.2.1.2.posDef
      (linX p.2.1.1 p.2.2.1 p.2.2.2)) := by rw [vec_base, vec]
    have h4 := hasDerivAt_inner_act T0 F (neg_mem_upq hZ) f (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) p.2.1.2.posDef
      (linX p.2.1.1 p.2.2.1 p.2.2.2)
    simp only [← h3, ← e, adjZ_neg hZ] at h4
    refine h4.congr_of_eventuallyEq (.of_forall fun t => ?_)
    have iso := (⟨(π (T0.expt (t • Z)) : F.H →ₗ[ℂ] F.H), h1 _⟩ : F.H →ₗᵢ[ℂ] F.H).inner_map_map (F.ι f)
      (π (T0.expt (t • -Z)) (vec F p))
    simp only [← iso]
    change _ = inner ℂ (π _ _) (π _ (π _ _))
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← expt_inv T0 hZ, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]

end GlobalTheory.OscGauss

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts
open scoped ContDiff ENNReal

namespace GlobalTheory.ChernTransfer

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k'}
  {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D : ℕ} {j : Y ⟶ X} {Φ : CxPts q σ' ≃ₜ CxPts p σ}
  (hΦ : ∀ z, (Φ z).1 = z.1 ≫ j) {B : LB X} {φ : Weight p σ B}

abbrev pullW (φ : Weight p σ B) : Weight q σ' (LB.LinComb B (K := PUnit) (fun _ => j) fun _ => 1) :=
  φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)

theorem pullW_φ (i : PUnit → B.ι) (z : CxPts q σ') :
    (pullW hΦ φ).φ i z = φ.φ (i PUnit.unit) (Φ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * φ.φ (i a) (Φ z)).trans (by simp)


include hΦ in
theorem ev_app' (W : X.Opens) (g : Γ(X, W)) (z : CxPts q σ') :
    ev q σ' (j ⁻¹ᵁ W) (j.app W g) z = ev p σ W g (Φ z) := by
  rw [ev, ev, hΦ]
  exact (valR_comp z.1 j W g).symm


include hΦ in
theorem mem_preimage_iff (W : X.Opens) (z : CxPts q σ') :
    z ∈ ptsIn q σ' (j ⁻¹ᵁ W) ↔ Φ z ∈ ptsIn p σ W := by
  change _ ↔ ⊤ ≤ (Φ z).1 ⁻¹ᵁ W
  rw [hΦ]
  rfl

theorem isCInf_pullW (h : φ.IsCInf) : (pullW hΦ φ).IsCInf := fun i z hz => by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h _ _
    (mem_of_mem_linComb (m := fun _ => Φ z) (fun _ => hΦ z) hz PUnit.unit)
  refine ⟨j ⁻¹ᵁ W, ι, inferInstance, fun a => j.app W (g a), F, O, (mem_preimage_iff hΦ W z).2 h₁,
    h₂, ?_, h₄, ?_⟩
  · simpa only [ev_app' hΦ] using h₃
  · simp only [ev_app' hΦ]
    filter_upwards [Φ.continuous.continuousAt.eventually h₅] with w hw
    exact (pullW_φ hΦ i w).trans hw


include hΦ in
theorem holo_trans (c : AlgChart p σ D) (c' : AlgChart q σ' D) :
    DifferentiableOn ℂ (Φ.transOpenPartialHomeomorph c.e ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' (Φ.transOpenPartialHomeomorph c.e).source) :=
  differentiableOn_euclidean.2 fun a => ((c'.holo _ (j.app c.U (c.x a))).mono fun _ (hv : _ ∈ c'.e.target ∩ c'.e.symm ⁻¹' (Φ.transOpenPartialHomeomorph c.e).source) =>
    ⟨hv.1, (mem_preimage_iff hΦ _ _).2 (c.source_subset hv.2)⟩).congr fun _ hv =>
      (c.apply_eq _ hv.2 a).trans (ev_app' hΦ _ _ _).symm

theorem chernDens_pullW (h : φ.IsCInf) (c : AlgChart p σ D) (c' : AlgChart q σ' D)
    {z : CxPts q σ'} (hz : z ∈ c'.e.source) (hz' : Φ z ∈ c.e.source) :
    c'.chernDens (pullW hΦ φ) z =
      ‖transDet c'.e (Φ.transOpenPartialHomeomorph c.e) z‖ ^ 2 * c.chernDens φ (Φ z) := by
  set e := Φ.transOpenPartialHomeomorph c.e with he
  have ho := isOpen_over c'.e e.open_source
  have hm := mem_over c'.e hz (S := e.source) hz'
  have hi : z ∈ ptsIn q σ' ((LB.LinComb B (K := PUnit) (fun _ => j) fun _ => 1).U
      fun _ => pick φ.isLB (Φ z)) :=
    ptsIn_mono (fun _ hx => mem_iInter.2 fun _ => hx)
      ((mem_preimage_iff hΦ _ z).2 (mem_pick φ.isLB (Φ z)))
  have e₁ : (fun v => ((pullW hΦ φ).φ (fun _ => pick φ.isLB (Φ z)) (c'.e.symm v) : ℂ))
      =ᶠ[𝓝 (c'.e z)] (fun v => (φ.φ (pick φ.isLB (Φ z)) (c.e.symm v) : ℂ)) ∘ e ∘ c'.e.symm :=
    eventually_of_mem (ho.mem_nhds hm) fun v hv => by
      have : c.e.symm (e (c'.e.symm v)) = Φ (c'.e.symm v) := c.e.left_inv hv.2
      simp only [Function.comp_apply, this, pullW_φ]
  have e₂ : (e ∘ c'.e.symm) (c'.e z) = c.e (Φ z) := congrArg e (c'.e.left_inv hz)
  rw [c'.chernDens_eq (isCInf_pullW hΦ h) hz hi, AlgChart.chernDens]
  have e₃ : c'.hess (pullW hΦ φ) (fun _ => pick φ.isLB (Φ z)) z = _ :=
    ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e₁
  rw [e₃, AlgChart.hess,
    ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (holo_trans hΦ c c') (e₂ ▸
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h.contDiffAt c hz' (mem_pick _ _))), e₂,
    Complex.re_ofReal_mul, transDet]
  ring

variable [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts q σ')]

theorem chernPart_pullW (R : AnRead p σ D) (R' : AnRead q σ' D) (h : φ.IsCInf) (ε : ℤˣ) :
    (pullW hΦ φ).chernPart D ε = (φ.chernPart D ε).map Φ.symm.toMeasurableEquiv := by
  refine ext_of_cover (fun a : R.ι × R'.ι => (R'.chart a.2).e.source ∩
    (Φ.transOpenPartialHomeomorph (R.chart a.1).e).source)
    (fun a => (R'.chart a.2).e.open_source.inter (OpenPartialHomeomorph.open_source _))
    (fun z => ?_) fun a A hA hs => ?_
  · obtain ⟨a, ha⟩ := R.cover (Φ z)
    obtain ⟨b, hb⟩ := R'.cover z
    exact ⟨(a, b), hb, ha⟩
  set c := R.chart a.1
  set c' := R'.chart a.2
  have h₁ : A ⊆ c'.e.source := hs.trans inter_subset_left
  have h₂ : A ⊆ (Φ.transOpenPartialHomeomorph c.e).source := hs.trans inter_subset_right
  have hA' : MeasurableSet (Φ.symm.toMeasurableEquiv ⁻¹' A) := Φ.symm.toMeasurableEquiv.measurable hA
  have h₃ : Φ.symm.toMeasurableEquiv ⁻¹' A ⊆ c.e.source := fun y hy => by
    have : Φ (Φ.symm y) ∈ c.e.source := h₂ hy
    rwa [Φ.apply_symm_apply] at this
  rw [MeasurableEquiv.map_apply, Weight.chernPart_apply (isCInf_pullW hΦ h) ε c' hA h₁,
    Weight.chernPart_apply h ε c hA' h₃,
    ← chartMeas_apply_of_subset c'.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * c'.chernDens (pullW hΦ φ) y)) hA h₁,
    chartMeas_eq c'.e (Φ.transOpenPartialHomeomorph c.e)
      (ρ' := fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (Φ y))) (holo_trans hΦ c c') hA h₁ h₂
      (fun y hy => by
        rw [chernDens_pullW hΦ h c c' (h₁ hy) (h₂ hy), mul_left_comm,
          ENNReal.ofReal_mul (sq_nonneg _)]),
    chartMeas_apply_of_subset _ _ hA h₂]
  have him : Φ.transOpenPartialHomeomorph c.e '' A = c.e '' (Φ.symm.toMeasurableEquiv ⁻¹' A) := by
    rw [show Φ.symm.toMeasurableEquiv ⁻¹' A = Φ '' A from (Φ.image_eq_preimage_symm A).symm,
      image_image]
    rfl
  rw [him]
  refine lintegral_congr fun v => ?_
  rw [show Φ ((Φ.transOpenPartialHomeomorph c.e).symm v) = c.e.symm v from Φ.apply_symm_apply _]

end GlobalTheory.ChernTransfer

end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem TwistConeVanishing.of_isZero {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {F : X.Modules} (hF : IsZero F) : TwistConeVanishing A N F :=
  ⟨0, fun j m _ _ p _ => cohOn.subsingleton_of_isZero
    ((isZero_twist_iff (isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m))).2 hF) ⊤ p⟩

theorem TwistConeVanishing.of_shortExact {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : TwistConeVanishing A N S.X₁)
    (h₃ : TwistConeVanishing A N S.X₃) : TwistConeVanishing A N S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨max a b, fun j m hj hm p hp => ?_⟩
  have hT := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  exact cohOn.subsingleton₂ (Twist.shortExact_map hT hS) ⊤ p
    (ha j m (le_of_max_le_left hj) hm p hp) (hb j m (le_of_max_le_right hj) hm p hp)

theorem TwistConeVanishing.of_generic (k : Type) [Field k] {V : Scheme.{0}} [IsIntegral V]
    (f : V ⟶ Sp k) (hf : IsProjOver f) (A N : LB V) (hA : IsAmpleLB A) (hN : IsPsEff N)
    (G : V.Modules) [IsFiniteQC G]
    (h : ∀ E : V.Modules, IsFiniteQC E → genericPoint V ∉ support E → TwistConeVanishing A N E) :
    TwistConeVanishing A N G := by
  have : AlgebraicGeometry.IsNoetherian V := isNoetherian_of_isProjOver hf
  obtain ⟨r, hr, s, hs⟩ := hN.exists_hasNonzeroSec hA (m := 2) (by norm_num)
  have hM : (lbPow (tens (lbPow N 2) A) r).IsLB :=
    isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB 2) hA.isLB) r
  have hgen : genericPoint V ∈ Out.nonzeroLocus s := (sec_ne_zero_iff s).1 hs
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_subsingleton_coh_twist_tens_lbPow' k f hf A N hA hN.isLB G (2 * r)
  have hCf : IsFiniteQC (cokernel (cutHom G hM s)) := ((cut_by_regular_section.{0} G hM).1 s).2.2.1
  have hCs : support (cokernel (cutHom G hM s)) = support G \ ↑(Out.nonzeroLocus s) :=
    ((cut_by_regular_section.{0} G hM).1 s).2.2.2.1
  haveI : IsFiniteQC (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1)) :=
    isFiniteQC_twist (isLB_lbZPow hM (-1))
  refine GlobalTheory.T.twistedPowerVanishing_induction_by_section_sq_tensor A N hA.isLB hN.isLB r hr hM s G ⟨j₁, hj₁⟩ (h _ inferInstance ?_)
    (h _ hCf ?_)
  · exact GlobalTheory.T.notMem_support_ker_mulSection_of_nonvanishing hM s G _ hgen
  · rw [hCs]
    exact fun h' => h'.2 hgen

end GlobalTheory

namespace GlobalTheory

theorem eventually_subsingleton_coh_ample_psEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → ∀ F : X.Modules, IsFiniteQC F → ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p → Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ X f hf A N hA hN hpe F hF
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  refine devissage X (TwistConeVanishing A N) (fun _ h => .of_isZero hA.isLB hN h)
    (fun _ hS _ _ h₁ h₃ => .of_shortExact hA.isLB hN hS h₁ h₃) ?_ F hF
  intro Z hZ hsmall G hG
  haveI := hG
  haveI := isIntegral_red hZ
  have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN G).1 ?_
  refine TwistConeVanishing.of_generic k (redι Z ≫ f)
    (ProjSpace.isProjOver_comp_of_isClosedImmersion _ hf) _ _ hAV (hpe Z hZ) G ?_
  intro E hE hη
  haveI := hE
  have hE' : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj E) :=
    ProperFinite.isFiniteQC_pushforward (redι Z) hAV E
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN E).2 (hsmall _ hE' ?_)
  have hsub := GlobalTheory.T.support_pushforward_subset_image (redι Z) E
  refine ⟨hsub.trans ((Set.image_subset_range _ _).trans (range_redι Z).le), fun hle => hη ?_⟩
  have hηZ : (redι Z) (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ∈ (Z : Set X) :=
    (range_redι Z).le ⟨_, rfl⟩
  obtain ⟨y, hy, hyη⟩ := hsub (hle hηZ)
  rwa [(redι Z).isClosedEmbedding.injective hyη] at hy

end GlobalTheory
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan : ∀ (p q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ), h ∈ (GlobalTheory.GrassTop.J p q).restrictScalars ℝ ⊔ Submodule.span ℝ (GlobalTheory.GrassTop.basis p q) := by
  first | exact @GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top | exact GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top | (intros; apply GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coefficientSpace_le_span_unitary_orbit_extremal : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), VV ℂ lam ≤ Submodule.span ℂ {F | ∃ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos n)) ∧ F = vact lam u (ten fun τ => extremal ℂ n (lam τ))} := by
  first | exact @GlobalTheory.JointHarm.VV_le_span_vact_extremal | exact GlobalTheory.JointHarm.VV_le_span_vact_extremal | (intros; apply GlobalTheory.JointHarm.VV_le_span_vact_extremal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowestWeight_matrixCoefficient_depends_on_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (π' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P') (x y : P) (x' y' : P'), IsHolRep ε B π → IsHolRep ε B' π' → IsBottom ε π μ x → IsBottom ε π μ y → IsBottom ε π' μ x' → IsBottom ε π' μ y' → ∀ k ∈ Formalism.REAL.Kset ε, B x (π k y) * B' x' y' = B x y * B' x' (π' k y') := by
  first | exact @GlobalTheory.JointHarm.Sph.coeff_eq | exact GlobalTheory.JointHarm.Sph.coeff_eq | (intros; apply GlobalTheory.JointHarm.Sph.coeff_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.upwardHeckeOperator_commute_diamond : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E), Function.Surjective res → (∀ x, (p x).Ok res) → ∀ g ∈ AdFun S emb, ∀ (v' : HeightOneSpectrum (𝓞 F)) (hv' : (T : 𝓞 F) ∈ v'.asIdeal) (a : ℤ) (δ : GA σ J), v' ∉ bad → (v' = v → (a : k) ≠ 0) → IsDia S v' hv' a δ → ∀ x, upAd res t v p (fun y => g (y * δ)) x = upAd res t v p g (x * δ) := by
  first | exact @GlobalTheory.LevelHecke.UpDia.upAd_dia | exact GlobalTheory.LevelHecke.UpDia.upAd_dia | (intros; apply GlobalTheory.LevelHecke.UpDia.upAd_dia <;> assumption)
end
