module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem co_mkE (D : Dat F E) (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have h : D.mkE u t = ∑ i, (![u, t] : Fin 2 → A F) i • AdeleBaseChange.adeleBasis D.b i := by
    rw [Fin.sum_univ_two]
    simp only [AdeleBaseChange.adeleBasis_apply, D.b0, D.b1, Algebra.smul_def, map_one, Dat.mkE,
      AdeleBaseChange.algebraMap_adeleRing]
    simp
  unfold Dat.co
  rw [h, Module.Basis.repr_sum_self]

private theorem bar_mkE (D : Dat F E) (u t : A F) : D.bar (D.mkE u t) = D.mkE u (-t) := by
  have h1 : ∀ a : A F, D.bar (AdeleBaseChange.adeleMap F E a) = AdeleBaseChange.adeleMap F E a :=
    fun a => AdeleBaseChange.smul_adeleMap D.σ a
  have h2 : D.bar (rt D.θ) = - rt D.θ := by
    have : D.bar (rt D.θ) = rt (D.σ D.θ) := AdeleBaseChange.smul_algebraMap D.σ D.θ
    rw [this, D.conj]; simp [UpperTheory.ConvolutionTheory.R2.rt]
  simp only [Dat.mkE, map_add (f := _), map_mul, h1, h2, map_neg]
  ring

private theorem theta_sq (D : Dat F E) :
    rt D.θ * rt D.θ = AdeleBaseChange.adeleMap F E (rt D.δ) := by
  rw [UpperTheory.ConvolutionTheory.R2.rt, UpperTheory.ConvolutionTheory.R2.rt, AdeleBaseChange.adeleMap_algebraMap, ← D.sq, ← map_mul, pow_two]

private theorem nu_gl (b : A E) : nu F (gl (nU b)) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (gl (nU b)) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.det]
  simp [nu, h]

private theorem ab_one : ab (1 : (A F)ˣ) = 1 := by simp [ab]

private theorem gl_val (b : A E) : (gl (nU b)).val = !![1, b; 0, 1] := rfl

private theorem gl_inv (b : A E) : (gl (nU b))⁻¹ = gl (nU (-b)) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, gl_val, gl_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem act_nU (D : Dat F E) (u t s z₀ z₁ : A F) :
    D.act (gl (nU (D.mkE u t)))⁻¹ ![0, s, z₀, z₁] =
      ![0, s - 2 * (u * z₀ - UpperTheory.ConvolutionTheory.R2.rt D.δ * (t * z₁)), z₀, z₁] := by
  rw [gl_inv]
  have hb : D.bar (-D.mkE u t) = - D.mkE u (-t) := by rw [map_neg, bar_mkE]
  have h0 : D.mkE 0 0 = 0 := by simp [Dat.mkE]
  have hθ := theta_sq D
  have e11 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 1 1 = 0 := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0]
  have e01 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 0 1 = D.mkE z₀ z₁ := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0]
  have e00 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 0 0 =
      D.mkE (s - 2 * (u * z₀ - UpperTheory.ConvolutionTheory.R2.rt D.δ * (t * z₁))) 0 := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0, hb]
    simp only [Dat.mkE, map_sub, map_mul, map_add (f := _), map_neg, map_zero, map_ofNat]
    linear_combination (2 * AdeleBaseChange.adeleMap F E t * AdeleBaseChange.adeleMap F E z₁) * hθ
  have z0 : D.co 0 = ![0, 0] := by rw [← h0, co_mkE]
  rw [Dat.act, Dat.unherm, e11, e01, e00, co_mkE, co_mkE, z0]
  ext i
  fin_cases i <;> simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.D.hatNE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ u t φ x z₀ z₁, hat (W.L (gl (nU (D.mkE u t))) φ).1 ![0, x, z₀, z₁] =
      ψ (-(x * (2 * (u * z₀ - rt D.δ * (t * z₁))))) * hat φ.1 ![0, x, z₀, z₁] := by
  intro F E _ _ _ _ _ _ _ D W u t φ x z₀ z₁
  set T : A F := 2 * (u * z₀ - rt D.δ * (t * z₁)) with hT
  have hup : ∀ s : A F, Function.update (![0, x, z₀, z₁] : V4 F) 1 s = ![0, s, z₀, z₁] := by
    intro s
    ext i
    fin_cases i <;> simp
  set g : A F → ℂ := fun s => φ.1 ![0, s, z₀, z₁] * ψ (-(s * x)) with hg
  have hR : hat φ.1 ![0, x, z₀, z₁] = ∫ s, g s ∂(adeleMeasure F) := by
    simp only [hat, hup, hg]
    rfl
  have hL : hat (W.L (gl (nU (D.mkE u t))) φ).1 ![0, x, z₀, z₁] =
      ∫ s, ψ (-(x * T)) * g (s - T) ∂(adeleMeasure F) := by
    simp only [hat, hup]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    have e : ψ (-(s * x)) = ψ (-(x * T)) * ψ (-((s - T) * x)) := by
      rw [← psi_add]; congr 1; ring
    simp only [W.L_apply, nu_gl, act_nU, hg, ← hT]
    simp [e, ab_one]
    ring
  rw [hL, hR, integral_const_mul, integral_sub_right_eq_self g T]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding

section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem map_mul_inv_eq_one {R : Type} [CommRing R] (h : A K →+* R) (g : GL ι (A K)) :
    g.val.map h * (g⁻¹).val.map h = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one h (map_zero h) (map_one h)]

private theorem map_inv_mul_eq_one {R : Type} [CommRing R] (h : A K →+* R) (g : GL ι (A K)) :
    (g⁻¹).val.map h * g.val.map h = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one h (map_zero h) (map_one h)]

private noncomputable def infEquiv (g : GL ι (A K)) :
    (ι → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ g.val.map adeleInfHom *ᵥ u
      invFun := fun u ↦ (g⁻¹).val.map adeleInfHom *ᵥ u
      map_add' := fun u v ↦ Matrix.mulVec_add _ u v
      map_smul' := fun c u ↦ Matrix.mulVec_smul _ c u
      left_inv := fun u ↦ by
        simp only [Matrix.mulVec_mulVec, map_inv_mul_eq_one, Matrix.one_mulVec]
      right_inv := fun u ↦ by
        simp only [Matrix.mulVec_mulVec, map_mul_inv_eq_one, Matrix.one_mulVec] }

private noncomputable def finHomeo (g : GL ι (A K)) :
    (ι → FiniteAdeleRing (𝓞 K) K) ≃ₜ (ι → FiniteAdeleRing (𝓞 K) K) where
  toFun u := g.val.map adeleFinHom *ᵥ u
  invFun u := (g⁻¹).val.map adeleFinHom *ᵥ u
  left_inv u := by
    simp only [Matrix.mulVec_mulVec, map_inv_mul_eq_one, Matrix.one_mulVec]
  right_inv u := by
    simp only [Matrix.mulVec_mulVec, map_mul_inv_eq_one, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

private theorem infPartPi_gl (g : GL ι (A K)) (x : ι → A K) :
    infPartPi (g.val *ᵥ x) = infEquiv g (infPartPi x) := by
  rw [infPartPi_eq_adeleInfHom, infPartPi_eq_adeleInfHom, map_mulVec_eq]
  rfl

private theorem finPartPi_gl (g : GL ι (A K)) (x : ι → A K) :
    finPartPi (g.val *ᵥ x) = finHomeo g (finPartPi x) := by
  rw [finPartPi_eq_adeleFinHom, finPartPi_eq_adeleFinHom, map_mulVec_eq]
  rfl

end

end UpperTheory.ConvolutionTheory.R2.D

theorem UpperTheory.ConvolutionTheory.R2.D.sClos :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (A F)) (φ : (ι → A F) → ℂ),
    φ ∈ schwartzBruhatPi (K := F) (ι := ι) → (fun v => φ (g.val *ᵥ v)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  intro F _ _ ι _ _ g φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, h, hh, rfl⟩ := hG
    have e : (fun v => schwartzBruhatTensorPi f h (g.val *ᵥ v)) =
        schwartzBruhatTensorPi (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (infEquiv g) f)
          (h ∘ finHomeo g) := by
      funext x
      simp only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, infPartPi_gl, finPartPi_gl]
    rw [e]
    refine schwartzBruhatTensorPi_mem _ ((mem_finiteSchwartzBruhatPi F).2 ⟨?_, ?_⟩)
    · exact ((mem_finiteSchwartzBruhatPi F).1 hh).1.comp_continuous (finHomeo g).continuous
    · exact ((mem_finiteSchwartzBruhatPi F).1 hh).2.comp_homeomorph (finHomeo g)
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.D

variable {F : Type} [Field F] [NumberField F]

private theorem comp_signed_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (ε : κ → F)
    (hε : ∀ k, ε k * ε k = 1) {G : (κ → A F) → ℂ} (hG : G ∈ schwartzBruhatPi (K := F) (ι := κ)) :
    (fun x : ι → A F => G fun k => rt (ε k) * x (e k)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  have hD : Matrix.diagonal ε * Matrix.diagonal ε = (1 : Matrix κ κ F) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hε k
  let M : Matrix κ ι F := (Matrix.diagonal ε).submatrix id e.symm
  let N : Matrix ι κ F := (Matrix.diagonal ε).submatrix e.symm id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) e.symm id e.symm
      Function.bijective_id
    rw [hD, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) id e.symm id
      e.symm.bijective
    rw [hD, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hG
  have hx : ∀ x : ι → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun k => rt (ε k) * x (e k) := by
    intro x
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← e.sum_comp]
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simpa only [hx] using h

private def eS : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private def sg : Fin 3 ⊕ Unit → F := Sum.elim 1 fun _ => -1

private theorem sg_mul (k) : (sg k : F) * sg k = 1 := by
  rcases k with i | i <;> simp [sg]

private def FF (φ : V4 F → ℂ) (z : Fin 3 ⊕ Unit → A F) : ℂ := φ fun i => z (eS.symm i)

private theorem FF_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    FF φ ∈ schwartzBruhatPi (K := F) (ι := Fin 3 ⊕ Unit) := by
  have h := comp_signed_mem (F := F) eS.symm (fun _ => 1) (fun _ => by simp) hφ
  have he : FF φ = fun x => φ fun k => rt ((fun _ => 1 : Fin 4 → F) k) * x (eS.symm k) := by
    funext x
    simp [FF]
  rw [he]
  exact h

private theorem hat_eq (φ : V4 F → ℂ) (x : V4 F) :
    hat φ x = GroundTheory.Heights₂.Theta.partialFourierPi (FF φ) fun k => rt (sg k) * x (eS k) := by
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  have h := hmp.integral_comp' (g := fun s => φ (Function.update x 1 s) * ψ (-(s * x 1)))
  rw [hat, ← h, GroundTheory.Heights₂.Theta.partialFourierPi, adelicFourierPi, adeleMeasurePi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h1 : Function.update x 1 (MeasurableEquiv.funUnique Unit (A F) y) =
      fun i => (Sum.elim (fun i => rt (sg (Sum.inl i)) * x (eS (Sum.inl i))) y
        : Fin 3 ⊕ Unit → A F) (eS.symm i) := by
    funext i
    fin_cases i <;> simp [eS, sg]
  have h2 : ψ (-(MeasurableEquiv.funUnique Unit (A F) y * x 1)) =
      ((adelicChar F (∑ i, y i * (rt (sg (Sum.inr i)) * x (eS (Sum.inr i)))) : Circle) : ℂ) := by
    simp [ψ, eS, sg]
  simp only [FF]
  rw [h1, h2]

private def tE {ι κ : Type} (e : κ ≃ ι) (ε : κ → F) (hε : ∀ k, ε k * ε k = 1) : (ι → F) ≃ (κ → F) where
  toFun ξ k := ε k * ξ (e k)
  invFun ξ i := ε (e.symm i) * ξ (e.symm i)
  left_inv ξ := by
    funext i
    simp [← mul_assoc, hε]
  right_inv ξ := by
    funext k
    simp [← mul_assoc, hε]

end UpperTheory.ConvolutionTheory.R2.D

end

theorem UpperTheory.ConvolutionTheory.R2.D.hatMem :
    ∀ (F : Type) [Field F] [NumberField F] (φ : S4 F), hat φ.1 ∈ schwartzBruhatPi (K := F) (ι := Fin 4) ∧ Th φ.1 = Th (hat φ.1) := by
  intro F _ _ φ
  have hF := FF_mem φ.2
  constructor
  · have h := comp_signed_mem (F := F) eS sg sg_mul (GroundTheory.Heights₂.Theta.partialFourierPi_mem hF)
    have he : hat φ.1 = fun x => GroundTheory.Heights₂.Theta.partialFourierPi (FF φ.1) fun k => rt (sg k) * x (eS k) :=
      funext (hat_eq φ.1)
    rw [he]
    exact h
  · have hP := GroundTheory.Heights₂.Theta.tsum_partialFourierPi hF
    have h1 : Th φ.1 = ∑' ξ : Fin 3 ⊕ Unit → F, FF φ.1 fun s => algebraMap F (A F) (ξ s) := by
      rw [Th, ← (tE (F := F) eS (fun _ => 1) (fun _ => by simp)).tsum_eq]
      refine tsum_congr fun ξ => ?_
      simp [FF, tE]
    have h2 : Th (hat φ.1) = ∑' ξ : Fin 3 ⊕ Unit → F,
        GroundTheory.Heights₂.Theta.partialFourierPi (FF φ.1) fun s => algebraMap F (A F) (ξ s) := by
      rw [Th, ← (tE (F := F) eS sg sg_mul).tsum_eq]
      refine tsum_congr fun ξ => ?_
      rw [hat_eq]
      congr 1
      funext k
      simp [tE]
    rw [h1, h2, hP]
end
