module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

open scoped Matrix.Norms.Operator

private theorem ex_val (X : Lie E 2) (t : ℝ) : (ex X t).val = NormedSpace.exp (t • Matrix.of X) := rfl

private theorem ex_add (X : Lie E 2) (s t : ℝ) : ex X (s + t) = ex X s * ex X t := by
  refine Units.ext ?_
  rw [Units.val_mul, ex_val, ex_val, ex_val, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)

private theorem ex_zero (X : Lie E 2) : ex X 0 = 1 := by
  refine Units.ext ?_
  rw [ex_val, zero_smul, NormedSpace.exp_zero]
  rfl

private theorem ex_inv (X : Lie E 2) (t : ℝ) : (ex X t)⁻¹ = ex X (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← ex_add, add_neg_cancel, ex_zero])

private theorem ex_val_cont (X : Lie E 2) : Continuous fun t : ℝ => (ex X t).val :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) t).continuousAt

private theorem ex_cont (X : Lie E 2) : Continuous (ex X) := by
  refine Units.continuous_iff.2 ⟨ex_val_cont X, ?_⟩
  simp only [ex_inv]
  exact (ex_val_cont X).comp continuous_neg

private theorem ex_der (X : Lie E 2) : HasDerivAt (fun t => toL (ex X t).val) X 0 := by
  let L : Matrix (Fin 2) (Fin 2) (Cinf E) →L[ℝ] Lie E 2 :=
    { toLinearMap := (Matrix.ofLinearEquiv ℝ).symm.toLinearMap, cont := continuous_id }
  have h : HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • Matrix.of X)))
      (L (NormedSpace.exp ((0 : ℝ) • Matrix.of X) * Matrix.of X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) (0 : ℝ))
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

private theorem ex_ent (X : Lie E 2) (i j : Fin 2) :
    HasDerivAt (fun t => (ex X t).val i j) (X i j) 0 :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 (ex_der X) i) j

private theorem ex_det_der (X : Lie E 2) :
    HasDerivAt (fun t => (ex X t).val.det) ((Matrix.of X).trace) 0 := by
  have h := ((ex_ent X 0 0).mul (ex_ent X 1 1)).sub ((ex_ent X 0 1).mul (ex_ent X 1 0))
  have e0 : (ex X 0).val = 1 := by rw [ex_zero]; rfl
  simp only [e0, Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
    Matrix.one_apply_ne, mul_one, one_mul, zero_mul, mul_zero, add_zero, sub_zero] at h
  rw [Matrix.trace_fin_two]
  simp only [Matrix.det_fin_two]
  exact h

private theorem ex_det (X : Lie E 2) (hX : (Matrix.of X).trace = 0) (t : ℝ) : (ex X t).val.det = 1 := by
  have hm : ∀ s t, (ex X (s + t)).val.det = (ex X s).val.det * (ex X t).val.det := fun s t => by
    rw [ex_add, Units.val_mul, Matrix.det_mul]
  have hd : ∀ t, HasDerivAt (fun s => (ex X s).val.det) (0 : Cinf E) t := fun t => by
    have h0 := ex_det_der X
    rw [hX] at h0
    have h1 : HasDerivAt (fun s => (ex X (s - t)).val.det) (0 : Cinf E) t :=
      HasDerivAt.comp_sub_const t t (by simpa using h0)
    have h2 := h1.const_mul (ex X t).val.det
    rw [mul_zero] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show (ex X s).val.det = (ex X t).val.det * (ex X (s - t)).val.det
    rw [← hm, add_sub_cancel]
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have e0 : (ex X 0).val = 1 := by rw [ex_zero]; rfl
  simpa [e0] using hc

private theorem ex_cen (X : Lie E 2) (s : Cinf E) (t : ℝ) : ex (X + zE s) t = ex (zE s) t * ex X t := by
  refine Units.ext ?_
  rw [Units.val_mul, ex_val, ex_val, ex_val]
  have e : Matrix.of (X + zE s) = Matrix.of (zE s) + Matrix.of X := by
    rw [add_comm]; rfl
  have c : Commute (Matrix.of (zE s)) (Matrix.of X) :=
    Matrix.scalar_commute s (fun r => Commute.all _ _) (Matrix.of X)
  rw [e, smul_add]
  exact NormedSpace.exp_add_of_commute ((c.smul_left t).smul_right t)

end

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.exPar :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ExPar E := by
  intro E _ _ _ X
  exact ⟨ex_add X, ex_cont X, ex_der X, ex_det X, fun s t => ex_cen X s t⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

open UpperTheory.ConvolutionTheory.R2.Fo (pl cw)

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private def Dm (s : ℂ) (d : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![d 1, (2 : ℂ)⁻¹ * (d 2 + s⁻¹ * d 3); (2 : ℂ)⁻¹ * (d 2 - s⁻¹ * d 3), d 0]

private theorem pair (s : ℂ) (hs : s ≠ 0) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) (d : Fin 4 → ℂ) :
    ∑ a, ∑ b, Hm s w x a b * Dm s d a b = ∑ i, ((x i w : ℝ) : ℂ) * d i := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_four]
  simp [Hm, Dm]
  field_simp
  ring

private theorem Hm_neg (s : ℂ) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) :
    Hm (-s) w x = (Hm s w x)ᵀ := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Hm] <;> ring

private theorem Dm_neg (s : ℂ) (d : Fin 4 → ℂ) : Dm (-s) d = (Dm s d)ᵀ := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Dm] <;> ring

private theorem swap (Y H D : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ a, ∑ b, (Y.map (starRingEnd ℂ) * Hᵀ) a b * Dᵀ a b = ∑ a, ∑ b, (H * Yᴴ) a b * D a b := by
  simp [Fin.sum_univ_two, Matrix.mul_apply]
  ring

private theorem pair_neg (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ a, ∑ b, (-(A + B)) a b * D a b = -(∑ a, ∑ b, A a b * D a b) - ∑ a, ∑ b, B a b * D a b := by
  simp [Fin.sum_univ_two]
  ring

private theorem im_of_sq {s : ℂ} {r : ℝ} (h : s ^ 2 = (r : ℂ)) (hr : r < 0) :
    starRingEnd ℂ s = -s ∧ s ≠ 0 := by
  have hre : s.re * s.re - s.im * s.im = r := by
    have := congrArg Complex.re h
    simpa [pow_two, Complex.mul_re] using this
  have him : s.re * s.im + s.im * s.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two, Complex.mul_im] using this
  have h0 : s.re = 0 := by
    have : s.re * s.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg s.re]
  refine ⟨Complex.ext (by simp [h0]) (by simp), fun hs => ?_⟩
  rw [hs] at hre
  simp at hre
  linarith

private theorem isReal_comp (τ : E →+* ℂ) : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
  InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)

private theorem θ_sq (D : Dat F E) (τ : E →+* ℂ) : (τ D.θ) ^ 2 = (τ.comp (algebraMap F E)) D.δ := by
  rw [← map_pow, D.sq]
  rfl

private theorem θ_im (D : Dat F E) (τ : E →+* ℂ) : starRingEnd ℂ (τ D.θ) = -τ D.θ ∧ τ D.θ ≠ 0 := by
  have hr := isReal_comp (F := F) τ
  refine im_of_sq (r := hr.embedding D.δ) ?_ (D.neg hr.embedding)
  rw [θ_sq, hr.coe_embedding_apply]

private theorem emb_ext (D : Dat F E) {τ τ' : E →+* ℂ} (h : τ.comp (algebraMap F E) = τ'.comp (algebraMap F E))
    (hθ : τ D.θ = τ' D.θ) : τ = τ' := by
  have hc : ∀ c : F, τ (algebraMap F E c) = τ' (algebraMap F E c) := fun c => RingHom.congr_fun h c
  refine RingHom.ext fun x => ?_
  rw [← D.b.sum_repr x, Fin.sum_univ_two, D.b0, D.b1]
  simp only [Algebra.smul_def, map_add (f := _), map_mul, map_one, hc, hθ]

private theorem conj_comp (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap F E) = τ.comp (algebraMap F E) := by
  have hr := ComplexEmbedding.isReal_iff.1 (isReal_comp (F := F) τ)
  ext x
  have := RingHom.congr_fun hr x
  simpa [ComplexEmbedding.conjugate_coe_eq] using congrArg id this

private theorem pl_conj (τ : E →+* ℂ) : pl (F := F) (ComplexEmbedding.conjugate τ) = pl (F := F) τ := by
  unfold pl
  rw [conj_comp]

private theorem conj_θ (D : Dat F E) (τ : E →+* ℂ) : (ComplexEmbedding.conjugate τ) D.θ = -τ D.θ := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact (θ_im D τ).1

private theorem conj_ne (D : Dat F E) (τ : E →+* ℂ) : τ ≠ ComplexEmbedding.conjugate τ := fun h => by
  have h1 := conj_θ D τ
  rw [← h] at h1
  have h2 := (θ_im D τ).2
  exact h2 (self_eq_neg.1 h1)

private theorem pl_fiber (D : Dat F E) {τ τ' : E →+* ℂ} (h : pl (F := F) τ' = pl (F := F) τ) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by
  have h1 : τ'.comp (algebraMap F E) = τ.comp (algebraMap F E) := by
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact h
    · rw [← h]
      exact (ComplexEmbedding.isReal_iff.1 (isReal_comp (F := F) τ')).symm
  have h2 : (τ' D.θ) ^ 2 = (τ D.θ) ^ 2 := by rw [θ_sq, θ_sq, h1]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ h2 with h3 | h3
  · exact Or.inl (emb_ext D h1 h3)
  · exact Or.inr (emb_ext D (h1.trans (conj_comp τ).symm) (h3.trans (conj_θ D τ).symm))

private theorem pl_surj (D : Dat F E) (w : InfinitePlace F) : ∃ τ : E →+* ℂ, pl (F := F) τ = w := by
  haveI : Module.Finite F E := Module.Finite.of_basis D.b
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
  refine ⟨w'.embedding, ?_⟩
  unfold pl
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw'

private theorem sum_pl (D : Dat F E) (f : (E →+* ℂ) → ℂ) (g : InfinitePlace F → ℂ)
    (h : ∀ τ, f τ + f (ComplexEmbedding.conjugate τ) = g (pl (F := F) τ)) : ∑ τ, f τ = ∑ w, g w := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ => pl (F := F) τ) f]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨τ, rfl⟩ := pl_surj D w
  have hf : (Finset.univ.filter fun τ' : E →+* ℂ => pl (F := F) τ' = pl (F := F) τ) = {τ, ComplexEmbedding.conjugate τ} := by
    ext τ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨pl_fiber D, ?_⟩
    rintro (rfl | rfl)
    · rfl
    · exact pl_conj τ
  rw [← h τ, ← Finset.sum_pair (conj_ne D τ), ← hf]

variable (D : Dat F E) (O : Fo.Ops F) (v : V4 F)

private theorem X_apply (τ : E →+* ℂ) (a b : Fin 2) (ψ' : S4 F) :
    (O.X D τ a b ψ').1 v = Hm (τ D.θ) (pl (F := F) τ) (fun i => TR.pInf F (v i)) a b * ψ'.1 v := by
  fin_cases a <;> fin_cases b <;> simp [Fo.Ops.X, Hm, O.x_apply, Fo.cw] <;> ring

private theorem DX_apply (τ : E →+* ℂ) (a b : Fin 2) (ψ' : S4 F) :
    (O.DX D τ a b ψ').1 v = Dm (τ D.θ) (fun i => (O.d (pl (F := F) τ) i ψ').1 v) a b := by
  fin_cases a <;> fin_cases b <;> simp [Fo.Ops.DX, Dm] <;> ring

private theorem dE_apply (τ : E →+* ℂ) (i j : Fin 2) (ψ' : S4 F) :
    (O.dE D τ i j ψ').1 v = -(if i = j then ψ'.1 v else 0) -
      ∑ b, Hm (τ D.θ) (pl (F := F) τ) (fun i => TR.pInf F (v i)) j b *
        Dm (τ D.θ) (fun i => (O.d (pl (F := F) τ) i ψ').1 v) i b := by
  unfold Fo.Ops.dE
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  by_cases h : i = j
  · simp [h, Module.End.mul_apply, X_apply, DX_apply]
  · simp [h, Module.End.mul_apply, X_apply, DX_apply]

private theorem dL_apply (Y : Lie E 2) (ψ' : S4 F) :
    (O.dL D Y ψ').1 v = ∑ τ : E →+* ℂ, ∑ i, ∑ j, coord τ (Y i j) * (O.dE D τ i j ψ').1 v := by
  simp [Fo.Ops.dL, LinearMap.sum_apply, Finset.sum_apply]

private def T (Y : Lie E 2) (ψ' : S4 F) (τ : E →+* ℂ) : ℂ :=
  ∑ a, ∑ b, ((Matrix.of Y).map (coord τ) * Hm (τ D.θ) (pl (F := F) τ) (fun i => TR.pInf F (v i))) a b *
    Dm (τ D.θ) (fun i => (O.d (pl (F := F) τ) i ψ').1 v) a b

private theorem T_conj (Y : Lie E 2) (ψ' : S4 F) (τ : E →+* ℂ) :
    T D O v Y ψ' (ComplexEmbedding.conjugate τ) =
      ∑ a, ∑ b, (Hm (τ D.θ) (pl (F := F) τ) (fun i => TR.pInf F (v i)) * ((Matrix.of Y).map (coord τ))ᴴ) a b *
        Dm (τ D.θ) (fun i => (O.d (pl (F := F) τ) i ψ').1 v) a b := by
  have hy : (Matrix.of Y).map (coord (ComplexEmbedding.conjugate τ)) =
      ((Matrix.of Y).map (coord τ)).map (starRingEnd ℂ) := by
    ext a b
    simp [GlobalTheory.IsoPull.coord_conj]
  unfold T
  rw [pl_conj, conj_θ, Hm_neg, Dm_neg, hy]
  exact swap _ _ _

private theorem term (Y : Lie E 2) (hY : (Matrix.of Y).trace = 0) (ψ' : S4 F) (τ : E →+* ℂ) :
    ∑ i, ∑ j, coord τ (Y i j) * (O.dE D τ i j ψ').1 v = -T D O v Y ψ' τ := by
  have tr : coord τ (Y 0 0) + coord τ (Y 1 1) = 0 := by
    rw [Matrix.trace_fin_two] at hY
    rw [← map_add (f := _)]
    have : Y 0 0 + Y 1 1 = 0 := hY
    rw [this, map_zero]
  simp only [dE_apply, T, Fin.sum_univ_two, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_true, if_false]
  linear_combination (-(ψ'.1 v)) * tr

end UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators

end

open UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators in
theorem UpperTheory.ConvolutionTheory.R2.Ff.vfOps :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), VfOps D O := by
  intro F E _ _ _ _ _ _ _ D O Y hY v x' hx φ
  rw [Finset.sum_comm, dL_apply]
  simp_rw [term D O v Y hY φ]
  symm
  refine sum_pl D (fun τ => -T D O v Y φ τ) _ fun τ => ?_
  have h1 := pair (τ D.θ) (θ_im D τ).2 (pl (F := F) τ) x' (fun i => (O.d (pl (F := F) τ) i φ).1 v)
  rw [hx τ, pair_neg] at h1
  rw [← h1, T_conj]
  unfold T
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem fiber_eq (w : InfinitePlace E) :
    (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk τ := by rw [InfinitePlace.mk_embedding, h]
    exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

private theorem emb_ne (w : InfinitePlace E) : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
    (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))

private theorem pl_eq (τ : E →+* ℂ) : Fo.pl F τ = (InfinitePlace.mk τ).comap (algebraMap F E) := by
  rw [InfinitePlace.comap_mk]; rfl

private theorem sum_coord_pl {M : Type*} [AddCommGroup M] [Module ℂ M] (s : Cinf E) (G : InfinitePlace F → M) :
    ∑ τ : E →+* ℂ, coord τ s • G (Fo.pl F τ) = ∑ v, ((trI F s v : ℝ) : ℂ) • G v := by
  have hr : ∀ v, ((trI F s v : ℝ) : ℂ) • G v =
      ∑ w : InfinitePlace E, (if w.comap (algebraMap F E) = v then ((2 * (s w).re : ℝ) : ℂ) • G v else 0) := by
    intro v
    simp only [trI]
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hr]
  rw [Finset.sum_comm, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), fiber_eq, Finset.sum_pair (emb_ne w), pl_eq, pl_eq,
    InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding,
    UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding, ← add_smul, Complex.add_conj]

private theorem theta_ne (D : Dat F E) : D.θ ≠ 0 := by
  rw [← D.b1]; exact D.b.ne_zero 1

private theorem dE_sum (D : Dat F E) (O : Fo.Ops F) (τ : E →+* ℂ) :
    O.dE D τ 0 0 + O.dE D τ 1 1 = -O.h (Fo.pl F τ) := by
  have ht : τ D.θ ≠ 0 := fun h => theta_ne D ((map_eq_zero τ).1 h)
  have h2 : (2 : Module.End ℂ (S4 F)) = 1 + 1 := one_add_one_eq_two.symm
  simp only [Fo.Ops.dE, Fo.Ops.X, Fo.Ops.DX, Fo.Ops.h, Fin.sum_univ_two, Fin.sum_univ_four, h2]
  simp only [Fin.isValue, if_true, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val]
  generalize τ D.θ = t at ht
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  match_scalars <;> field_simp <;> ring

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), DLCen D O := by
  intro F E _ _ _ _ _ _ _ D O
  refine ⟨fun s => ?_, fun Y Y' => ?_, fun c Y => ?_, fun s => ?_⟩
  · have hz : ∀ i j, zE s i j = if i = j then s else 0 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [zE, GlobalTheory.CuspRep.toL, Matrix.scalar_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.sum_univ_two, hz]
    simp only [Fin.isValue, if_true, one_ne_zero, zero_ne_one, if_false, map_zero, zero_smul, add_zero, zero_add]
    rw [← smul_add, dE_sum, smul_neg]
  · simp only [Fo.Ops.dL, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (Y + Y') i j = Y i j + Y' i j from rfl, map_add (f := _)]
  · simp only [Fo.Ops.dL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (c • Y) i j = c • Y i j from rfl, UpperTheory.V.FieldIso.coord_smul, Complex.real_smul, mul_smul]
  · rw [sum_coord_pl s (fun v => TR.Eop v 0 0 + TR.Eop v 1 1)]
    have hz : zF (trI F s) = ∑ v, trI F s v • (TR.toL (Matrix.single 0 0 (Pi.single v 1)) + TR.toL (Matrix.single 1 1 (Pi.single v 1)) : TR.Lie F 2) := by
      ext i j w
      fin_cases i <;> fin_cases j <;> simp [zF, TR.toL, Matrix.scalar_apply, Finset.sum_apply, Pi.single_apply, Matrix.single_apply]

    rw [hz, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_add (f := _)]
    first
      | rfl
      | exact (Complex.coe_smul _ _).symm
      | (ext φ g; rfl)
end
