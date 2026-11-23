module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem pair_fst_of_snd {F : Type} [Field F] [NumberField F] (a : AF F) (h : sndA F a = 0) :
    pairA F (fstA F a) 0 = a := Prod.ext rfl h.symm

theorem half_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (θ : Ainf F ⊗[F] E →+* ℂ)
    (a : AF F) :
    θ (fstA F (algebraMap F (AF F) (1 / 2) * a) ⊗ₜ[F] (1 : E)) = θ (fstA F a ⊗ₜ[F] (1 : E)) / 2 := by
  have h2 : algebraMap F (AF F) (1 / 2) * a + algebraMap F (AF F) (1 / 2) * a = a := by
    rw [← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]
  conv_rhs => rw [← h2, map_add (f := _), TensorProduct.add_tmul, RingHom.map_add (f := _)]
  ring

theorem valTau_coe {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AF D.host.F) :
    ((valTau θ τ a : ℝ) : ℂ) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
  have h := conj_tmul_one hθ τ (fstA D.host.F a)
  exact Complex.conj_eq_iff_re.1 h

theorem real_adele_ext_and_char : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ a : AF D.host.F, sndA D.host.F a = 0 → ((∀ τ, valTau θ τ a = 0) → a = 0) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) = Complex.exp (-(Real.pi * Complex.I) * ((∑ τ, valTau θ τ a : ℝ) : ℂ)) := by
  intro D θ σ h a ha
  refine ⟨fun h0 => ?_, fun ψ hψ => ?_⟩
  · have h1 : (a ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = 0 := by
      refine h.ext _ ?_ fun τ => ?_
      · have e : finPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ha, TensorProduct.zero_tmul]
      · have e : infPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ← valTau_coe h.inf, h0, Complex.ofReal_zero]
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := AF D.host.F)
      (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [map_zero]
    exact h1
  · have hc := hψ.2.2 θ h.inf (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a))
    rw [psiInf, pair_fst_of_snd _ (by rw [map_mul, ha, mul_zero])] at hc
    rw [hc]
    congr 1
    have e : ∀ ρ, θ ρ (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) ⊗ₜ[D.host.F] (1 : D.host.E))
        = ((valTau θ ρ a : ℝ) : ℂ) / 2 := fun ρ => by
      rw [valTau_coe h.inf]
      exact half_tmul (θ ρ) a
    rw [Finset.sum_congr rfl fun ρ _ => e ρ, ← Finset.sum_div, Complex.ofReal_sum]
    push_cast
    ring

end GlobalTheory.FockCompare
end

section

noncomputable section

open scoped ContDiff

namespace GlobalTheory.FockCompare

section

variable {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
  {ι : R →+ G} {π : G →+ R} {om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ}


omit [FiniteDimensional ℝ R] in
theorem heisComm_coset (hπ : ∀ x, π (ι x) = x)
    (hf : ∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u)
    (f : G → ℂ) (h : Sm ι f) (v : R) (w : G) :
    (fun x : R => hD ι π om v f (w + ι x)) = fun x : R =>
      -(Real.pi * Complex.I) * (om (π w + x) v : ℝ) * f (w + ι x) + fderiv ℝ (fun y : R => f (w + ι y)) x v := by
  funext x
  rw [hf f h, map_add (f := _), hπ]
  congr 2
  have e : (fun y : R => f (w + ι x + ι y)) = fun y : R => (fun z : R => f (w + ι z)) (x + y) := by
    funext y; simp only [map_add (f := _), add_assoc]
  rw [e, fderiv_comp_add_left (f := fun z : R => f (w + ι z)), add_zero]

theorem heisComm_hasFDerivAt_om (a v x : R) :
    HasFDerivAt (fun x : R => ((om (a + x) v : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))) x := by
  have h := (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))).hasFDerivAt (x := a + x)
  have h2 := h.comp x ((hasFDerivAt_id x).const_add a)
  rw [ContinuousLinearMap.comp_id] at h2
  exact h2

theorem heisComm_contDiff_om (a v : R) : ContDiff ℝ ∞ (fun x : R => ((om (a + x) v : ℝ) : ℂ)) :=
  (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))).contDiff.comp
    (contDiff_const.add contDiff_id)

theorem heisComm_second (hπ : ∀ x, π (ι x) = x)
    (hf : ∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u)
    (f : G → ℂ) (h : Sm ι f) (u v : R) (w : G) :
    hD ι π om u (hD ι π om v f) w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) *
        (-(Real.pi * Complex.I) * (om (π w) v : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 v) +
      (-(Real.pi * Complex.I) * (om u v : ℝ) * f w +
        -(Real.pi * Complex.I) * (om (π w) v : ℝ) * fderiv ℝ (fun x : R => f (w + ι x)) 0 u +
        fderiv ℝ (fderiv ℝ (fun x : R => f (w + ι x))) 0 u v) := by
  have hfd : ∀ w', ContDiff ℝ ∞ (fderiv ℝ (fun x : R => f (w' + ι x))) := fun w' =>
    (h w').fderiv_right (m := ∞) (by simp)
  have hs : Sm ι (hD ι π om v f) := by
    intro w'
    rw [heisComm_coset hπ hf f h v w']
    exact ((contDiff_const.mul (heisComm_contDiff_om _ _)).mul (h w')).add
      ((hfd w').clm_apply contDiff_const)
  rw [hf _ hs, hf f h v w, heisComm_coset hπ hf f h v w]
  congr 1
  have h1 : HasFDerivAt (fun x : R => f (w + ι x)) (fderiv ℝ (fun x : R => f (w + ι x)) 0) 0 :=
    ((h w).differentiable (by simp) 0).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ (fun x : R => f (w + ι x))) (fderiv ℝ (fderiv ℝ (fun x : R => f (w + ι x))) 0) 0 :=
    ((hfd w).differentiable (by simp) 0).hasFDerivAt
  have h3 := ((((heisComm_hasFDerivAt_om (om := om) (π w) v 0).const_mul (-(Real.pi * Complex.I))).mul h1).add
    (h2.clm_apply (hasFDerivAt_const v 0))).fderiv
  have h4 := congrArg (fun L => L u) h3
  refine Eq.trans h4 ?_
  simp
  ring

end

theorem heisenberg_derivative_commutator :
    ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
      (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) →
      (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
        -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) →
      (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → ∀ u v : R,
      hD ι π om u (hD ι π om v f) - hD ι π om v (hD ι π om u f) =
        (-(2 * Real.pi * Complex.I) * (om u v : ℝ)) • f := by
  intro G R _ _ _ _ ι π om hπ hf ha f h u v
  funext w
  have hsym : IsSymmSndFDerivAt ℝ (fun x : R => f (w + ι x)) 0 :=
    (h w).contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [Pi.sub_apply, heisComm_second hπ hf f h u v, heisComm_second hπ hf f h v u, hsym u v, ha u v]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end GlobalTheory.FockCompare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem eq_zero_of_bounded_of_creation_eq {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (F : R → ℂ) (hF : Differentiable ℝ F) (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) (u u' : R) (a b q : ℝ) (hq : 0 < q)
    (h : ∀ s t : ℝ, fderiv ℝ F (s • u - t • u') u - Complex.I * fderiv ℝ F (s • u - t • u') u' =
      Real.pi * Complex.I * ((a + t * q) - Complex.I * (b + s * q)) * F (s • u - t • u')) :
    F 0 = 0 := by
  let L : ℂ →L[ℝ] R := Complex.reCLM.smulRight u - Complex.imCLM.smulRight u'
  have hL : ∀ z : ℂ, L z = z.re • u - z.im • u' := fun z => rfl
  let re' : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  let im' : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have hre : ∀ z : ℂ, re' z = (z.re : ℂ) := fun z => rfl
  have him : ∀ z : ℂ, im' z = (z.im : ℂ) := fun z => rfl
  let c1 : ℂ := -(Real.pi * Complex.I)
  let c2 : ℂ := -(Real.pi * q / 2)
  let φ : ℂ → ℂ := fun z => c1 * (a * re' z - b * im' z) + c2 * (re' z * re' z + im' z * im' z)
  let H : ℂ → ℂ := fun z => Complex.exp (φ z) * F (L z)
  have hHd : Differentiable ℂ H := by
    intro z
    have r := re'.hasFDerivAt (x := z)
    have i := im'.hasFDerivAt (x := z)
    have h1 := ((((r.const_mul (a : ℂ)).sub (i.const_mul (b : ℂ))).const_mul c1).add
      (((r.mul r).add (i.mul i)).const_mul c2)).cexp
    have h2 := (hF (L z)).hasFDerivAt.comp z (L.hasFDerivAt (x := z))
    have h3 : HasFDerivAt H _ z := h1.mul h2
    rw [differentiableAt_complex_iff_differentiableAt_real]
    refine ⟨h3.differentiableAt, ?_⟩
    rw [h3.fderiv]
    have e := h z.re z.im
    rw [← hL] at e
    have e1 : L 1 = u := by simp [hL]
    have eI : L Complex.I = -u' := by simp [hL]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, e1, eI, hre, him, smul_eq_mul, map_neg, Function.comp_apply,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.ofReal_zero, Complex.ofReal_one]
    generalize Complex.exp _ = E
    rw [sub_eq_iff_eq_add] at e
    rw [e]
    simp only [c1, c2]
    linear_combination (-(E * fderiv ℝ F (L z) u') + E * F (L z) * Real.pi * (-(z.im * q) + Complex.I * (b + z.re * q))) * Complex.I_mul_I
  have hn : ∀ z, ‖H z‖ ≤ C * Real.exp (-(Real.pi * q / 2) * ‖z‖ ^ 2) := by
    intro z
    have : (φ z).re = -(Real.pi * q / 2) * ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [φ, c1, c2, hre, him]
    simp only [H]
    rw [norm_mul, Complex.norm_exp, this, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  have ht : Filter.Tendsto H (Filter.cocompact ℂ) (nhds 0) := by
    refine squeeze_zero_norm hn ?_
    have hp : -(Real.pi * q / 2) < 0 := by have := Real.pi_pos; have : 0 < Real.pi * q / 2 := by positivity
                                           linarith
    have t1 : Filter.Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Filter.cocompact ℂ) Filter.atTop :=
      (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop
    have t2 := (Real.tendsto_exp_atBot.comp (t1.const_mul_atTop_of_neg hp)).const_mul C
    simpa using t2
  have h0 := hHd.apply_eq_of_tendsto_cocompact 0 ht
  simp only [H, map_zero, mul_eq_zero, Complex.exp_ne_zero, false_or] at h0
  exact h0

theorem eq_zero_of_creation_eq_zero : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  intro G R _ _ _ _ ι π om hπ hform hanti f hf hb u u' hq h0
  funext w
  obtain ⟨C, hC⟩ := hb w
  have hF : Differentiable ℝ fun x : R => f (w + ι x) := (hf w).differentiable (by simp)
  have huu : ∀ v, om v v = 0 := fun v => by have := hanti v v; linarith
  have key := eq_zero_of_bounded_of_creation_eq (fun x : R => f (w + ι x)) hF C hC u u'
    (om (π w) u) (om (π w) u') (om u u') hq (fun s t => by
      set x := s • u - t • u' with hx
      have e := congrFun h0 (w + ι x)
      have hfd : fderiv ℝ (fun y : R => f (w + ι x + ι y)) 0 = fderiv ℝ (fun y : R => f (w + ι y)) x := by
        have : (fun y : R => f (w + ι x + ι y)) = fun y => (fun y : R => f (w + ι y)) (x + y) := by
          funext y; simp only [map_add (f := _), add_assoc]
        rw [this, fderiv_comp_add_left (f := fun y : R => f (w + ι y)), add_zero]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hform f hf, hfd] at e
      have e1 : om (π (w + ι x)) u = om (π w) u + t * om u u' := by
        rw [map_add (f := _), hπ, map_add (f := _), LinearMap.add_apply, hx]
        simp [huu, hanti u u']
      have e2 : om (π (w + ι x)) u' = om (π w) u' + s * om u u' := by
        rw [map_add (f := _), hπ, map_add (f := _), LinearMap.add_apply, hx]
        simp [huu]
      rw [e1, e2] at e
      push_cast at e
      linear_combination e)
  simpa using key

end GlobalTheory.FockCompare
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCxAlg

variable {D : D7}

theorem actC_actC (V W : HSp D) (g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h h' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (x : WC V W) :
    actC V W g h (actC V W g' h' x) = actC V W (g * g') (h * h') x := by
  unfold actC
  split_ifs <;> simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actC_smul (V W : HSp D) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (c : ℂ) (x : WC V W) :
    actC V W g h (c • x) = c • actC V W g h x := by
  unfold actC
  split_ifs <;> simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem actC_one (V W : HSp D) (x : WC V W) : actC V W 1 1 x = x := by
  unfold actC
  split_ifs <;> simp

theorem hC_actC (V W : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ)
    (hh : hᴴ * gramAt D W τ * h = gramAt D W τ) (x y : WC V W) :
    hC V W τ (actC V W g h x) (actC V W g h y) = hC V W τ x y := by
  unfold hC actC
  split_ifs with hr
  · rw [GlobalTheory.DualPairCheck.sum_small, GlobalTheory.DualPairCheck.sum_small]
    exact GlobalTheory.DualPairCheck.inv_small (starRingEnd ℂ) Complex.conj_conj _ _ _ _ hg hh x y
  · rw [GlobalTheory.DualPairCheck.sum_large, GlobalTheory.DualPairCheck.sum_large]
    exact GlobalTheory.DualPairCheck.inv_large (starRingEnd ℂ) Complex.conj_conj _ _ _ _ hg hh x y

theorem I_smul_unitary {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : tᴴ * G * t = G) :
    (Complex.I • t)ᴴ * G * (Complex.I • t) = G := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h]
  simp

theorem cx_alg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → (∀ x, jAt V W τ s s' (jAt V W τ s s' x) = -x) ∧ (∀ x y, symplC V W τ (jAt V W τ s s' x) (jAt V W τ s s' y) = symplC V W τ x y) ∧ (∀ g h, Commute g (thAt V τ s) → Commute h (thAt W τ s') → ∀ x, jAt V W τ s s' (actC V W g h x) = actC V W g h (jAt V W τ s s' x)) ∧ ∃ g ∈ KAt V τ s, ∃ h ∈ KAt W τ s', ∀ x, jAt V W τ s s' x = actC V W g h x := by
  intro D V W τ s s' hV hW
  refine ⟨fun x => ?_, fun x y => ?_, fun g h hg hh x => ?_, ?_⟩
  · unfold jAt
    rw [actC_smul, actC_actC, hV.1, hW.1, actC_one, smul_smul, Complex.I_mul_I, neg_one_smul]
  · unfold symplC jAt
    rw [hC_smul_left, hC_smul_right, hC_actC V W τ _ _ hV.2.1 hW.2.1, ← mul_assoc (starRingEnd ℂ Complex.I),
      Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  · unfold jAt
    rw [actC_smul, actC_actC, actC_actC, hg.eq, hh.eq]
  · by_cases hr : V.rank ≤ W.rank
    · refine ⟨thAt V τ s, ⟨hV.2.1, rfl⟩, Complex.I • thAt W τ s',
        ⟨I_smul_unitary hW.2.1, by rw [Matrix.smul_mul, Matrix.mul_smul]⟩, fun x => ?_⟩
      unfold jAt actC
      rw [if_pos hr, if_pos hr, Matrix.transpose_smul, Matrix.mul_smul]
    · refine ⟨Complex.I • thAt V τ s,
        ⟨I_smul_unitary hV.2.1, by rw [Matrix.smul_mul, Matrix.mul_smul]⟩, thAt W τ s', ⟨hW.2.1, rfl⟩, fun x => ?_⟩
      unfold jAt actC
      rw [if_neg hr, if_neg hr, Matrix.smul_mul, Matrix.smul_mul]

end GlobalTheory.FockCxAlg
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Kronecker

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_kron_pos {m n : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} {Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * P i k * Q j l * x k l := by
  have h := (hP.kronecker hQ).dotProduct_mulVec_pos (x := fun p : Fin m × Fin n => x p.1 p.2)
    (fun h0 => hx (by ext i j; exact congrFun h0 (i, j)))
  convert h using 1
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Finset.mul_sum, kroneckerMap_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
  rw [Complex.star_def]; ring

theorem IsCart.adj_mul {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : IsCart G t) :
    (t.map (starRingEnd ℂ))ᵀ * G = G * t := by
  have e : (t.map (starRingEnd ℂ))ᵀ = tᴴ := by ext i j; rfl
  rw [e]
  calc tᴴ * G = tᴴ * G * (t * t) := by rw [h.1, Matrix.mul_one]
    _ = G * t := by rw [← Matrix.mul_assoc, h.2.1]

theorem hC_actC_pos {D : D7} (V W : HSp D) (τ : D.what₂.Tau) (t : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (t' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : IsCart (gramAt D V τ) t) (h' : IsCart (gramAt D W τ) t')
    (x : WC V W) (hx : x ≠ 0) : 0 < hC V W τ x (actC V W t t' x) := by
  unfold hC actC
  split_ifs with hr
  · have p := sum_kron_pos h.2.2.transpose h'.2.2 x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_small] at p ⊢
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    convert p using 2
    rw [← h.adj_mul]
    simp only [Matrix.mul_assoc]
  · have p := sum_kron_pos h.2.2 h'.2.2.transpose x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_large] at p ⊢
    convert p using 2
    rw [← h'.adj_mul]
    simp only [Matrix.mul_assoc]

theorem symplC_jAt_neg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V)
    (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') →
    ∀ x : WC V W, x ≠ 0 → 0 < -symplC V W τ (jAt V W τ s s' x) x := by
  intro D V W τ s s' h h' x hx
  have p := hC_actC_pos V W τ _ _ h h' x hx
  have q := xi_zero_im_pos D τ
  unfold symplC jAt
  rw [hC_smul_right]
  obtain ⟨p1, p2⟩ := Complex.pos_iff.1 p
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ← p2]
  nlinarith [mul_pos p1 q]

end GlobalTheory.FockCompare
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complexStructureOfInvolutions_properties : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → (∀ x, jAt V W τ s s' (jAt V W τ s s' x) = -x) ∧ (∀ x y, symplC V W τ (jAt V W τ s s' x) (jAt V W τ s s' y) = symplC V W τ x y) ∧ (∀ g h, Commute g (thAt V τ s) → Commute h (thAt W τ s') → ∀ x, jAt V W τ s s' (actC V W g h x) = actC V W g h (jAt V W τ s s' x)) ∧ ∃ g ∈ KAt V τ s, ∃ h ∈ KAt W τ s', ∀ x, jAt V W τ s s' x = actC V W g h x := by
  first | exact @GlobalTheory.FockCxAlg.cx_alg | exact GlobalTheory.FockCxAlg.cx_alg | (intros; apply GlobalTheory.FockCxAlg.cx_alg <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eq_zero_of_hD_sub_I_smul_hD_eq_zero_of_bounded : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  first | exact @GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | exact GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | (intros; apply GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergDerivative_commutator_relation : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → ∀ u v : R, hD ι π om u (hD ι π om v f) - hD ι π om v (hD ι π om u f) = (-(2 * Real.pi * Complex.I) * (om u v : ℝ)) • f := by
  first | exact @GlobalTheory.FockCompare.heisenberg_derivative_commutator | exact GlobalTheory.FockCompare.heisenberg_derivative_commutator | (intros; apply GlobalTheory.FockCompare.heisenberg_derivative_commutator <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → ∀ x : WC V W, x ≠ 0 → 0 < -symplC V W τ (jAt V W τ s s' x) x := by
  first | exact @GlobalTheory.FockCompare.symplC_jAt_neg | exact GlobalTheory.FockCompare.symplC_jAt_neg | (intros; apply GlobalTheory.FockCompare.symplC_jAt_neg <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realAdele_ext_and_standardCharacter_formula : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ a : AF D.host.F, sndA D.host.F a = 0 → ((∀ τ, valTau θ τ a = 0) → a = 0) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) = Complex.exp (-(Real.pi * Complex.I) * ((∑ τ, valTau θ τ a : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.FockCompare.real_adele_ext_and_char | exact GlobalTheory.FockCompare.real_adele_ext_and_char | (intros; apply GlobalTheory.FockCompare.real_adele_ext_and_char <;> assumption)

end
end
