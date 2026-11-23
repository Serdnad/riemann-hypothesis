module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Bundle002
import GroundTheory.AutomorphicForms.Bundle012
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle007
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
open UpperTheory.ConvolutionTheory.R2.C

private lemma psi_add' {F : Type} [Field F] [NumberField F] (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private lemma psi_neg_mul {F : Type} [Field F] [NumberField F] (a : A F) : ψ (-a) * ψ a = 1 := by
  rw [← psi_add', neg_add_cancel]
  simp [ψ]

private lemma quadraticForm_shift_expand {F : Type} [Field F] [NumberField F] (δ : F) (b c : A F) (hbc : b * c = 1) (x y v : V4 F) :
    b * q4 δ (x + (y + fun i => c * v i)) = b * q4 δ (x + y) + B4 δ x v + B4 δ y v + c * q4 δ v := by
  simp only [q4, B4, Pi.add_apply]
  linear_combination (2 * ((x 2 + y 2) * v 2 - rt δ * ((x 3 + y 3) * v 3)) - (x 1 + y 1) * v 0 - (x 0 + y 0) * v 1
    + c * (v 2 ^ 2 - rt δ * v 3 ^ 2 - v 1 * v 0)) * hbc

private lemma quaternaryForm_neg_right {F : Type} [Field F] [NumberField F] (δ : F) (x v : V4 F) : B4 δ x (-v) = -B4 δ x v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.idxFt :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    ft4 δ (Pc δ (b : A F) φ.1) v = c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * ft4 δ φ.1 (-v) := by
  intro F _ _ δ b c h φ v
  have hbc : (b : A F) * ((b⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv b
  let φ' : S4 F := ⟨fun x => ψ (0 * q4 δ x + B4 δ x (-v)) * φ.1 x, chirpQ F δ 0 (-v) φ.1 φ.2⟩
  have hφ' : ∀ x, φ'.1 x = ψ (0 * q4 δ x + B4 δ x (-v)) * φ.1 x := fun _ => rfl
  have hr : ∫ x, φ'.1 x ∂(adeleMeasurePi F) = ft4 δ φ.1 (-v) := by
    unfold ft4
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', zero_mul, zero_add]
    exact mul_comm _ _
  have hl : ft4 δ (Pc δ (b : A F) φ.1) v =
      ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * Lam4 δ (b : A F) φ'.1 := by
    unfold ft4 Pc Lam4 abelian₂
    rw [← integral_add_right_eq_self
      (fun y => ∫ x, φ'.1 x * ψ ((b : A F) * q4 δ (x + y)) ∂(adeleMeasurePi F))
      (fun i => ((b⁻¹ : (A F)ˣ) : A F) * v i), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', zero_mul, zero_add, quaternaryForm_neg_right]
    rw [quadraticForm_shift_expand δ _ _ hbc x y v, psi_add', psi_add', psi_add']
    have e1 := psi_neg_mul (B4 δ x v)
    have e2 := psi_neg_mul (((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)
    linear_combination (-(φ.1 x * ψ ((b : A F) * q4 δ (x + y)) * ψ (B4 δ y v))
      * (ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * ψ (((b⁻¹ : (A F)ˣ) : A F) * q4 δ v))) * e1
      - (φ.1 x * ψ ((b : A F) * q4 δ (x + y)) * ψ (B4 δ y v)) * e2
  rw [hl, h φ', hr]
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

noncomputable section

private theorem continuous_form {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a c b d e : R) :
    Continuous fun y : Fin 4 → R => 2 * (y 2 * a - c * (y 3 * b)) - y 1 * d - y 0 * e := by
  fun_prop

namespace UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_psi : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp (continuous_adelicChar (K := F))

private theorem norm_psi (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _

private theorem continuous_quaternaryForm_left (δ : F) (v : V4 F) : Continuous fun y : V4 F => B4 δ y v := by
  exact continuous_form (v 2) (rt δ) (v 3) (v 0) (v 1)

private theorem integrable_ft (δ : F) {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (v : V4 F) :
    Integrable (fun y => φ y * ψ (B4 δ y v)) (adeleMeasurePi F) := by
  refine (integrable_of_mem_schwartzBruhatPi hφ).mul_bdd (c := 1) ?_ ?_
  · exact (continuous_psi.comp (continuous_quaternaryForm_left δ v)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => (norm_psi _).le

private theorem quaternaryFourier_add (δ : F) {φ φ' : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (hφ' : φ' ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (v : V4 F) :
    ft4 δ (φ + φ') v = ft4 δ φ v + ft4 δ φ' v := by
  unfold ft4
  rw [← integral_add (integrable_ft δ hφ v) (integrable_ft δ hφ' v)]
  congr 1
  funext y
  simp [add_mul]

private theorem quaternaryFourier_smul (δ : F) (c : ℂ) (φ : V4 F → ℂ) (v : V4 F) :
    ft4 δ (c • φ) v = c * ft4 δ φ v := by
  unfold ft4
  rw [← integral_const_mul]
  congr 1
  funext y
  simp [mul_assoc]

private def opN (δ : F) (b : A F) : Module.End ℂ (S4 F) where
  toFun φ := ⟨fun v => ψ (b * q4 δ v) * φ.1 v, by
    have h := chirpQ F δ b 0 φ.1 φ.2
    have e : (fun v => ψ (b * q4 δ v + B4 δ v 0) * φ.1 v) = fun v => ψ (b * q4 δ v) * φ.1 v := by
      funext v
      simp [B4]
    rwa [e] at h⟩
  map_add' φ φ' := by
    ext v
    simp [mul_add]
  map_smul' c φ := by
    ext v
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

private def scal (a : (A F)ˣ) : GL (Fin 4) (A F) :=
  ⟨(a : A F) • 1, ((a⁻¹ : (A F)ˣ) : A F) • 1, by simp [smul_smul], by simp [smul_smul]⟩

private def opM (η : (A F)ˣ →* ℂˣ) (a : (A F)ˣ) : Module.End ℂ (S4 F) where
  toFun φ := ⟨fun v => ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * v i, by
    have h := D.sClos F (Fin 4) (scal a) φ.1 φ.2
    have e : (fun v => φ.1 ((scal a).val *ᵥ v)) = fun v => φ.1 fun i => (a : A F) * v i := by
      funext v
      have e' : (scal a).val *ᵥ v = fun i => (a : A F) * v i := by
        funext i
        simp [scal, Matrix.smul_mulVec]
      rw [e']
    rw [e] at h
    exact Submodule.smul_mem _ (((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ)) h⟩
  map_add' φ φ' := by
    ext v
    simp [mul_add]
  map_smul' c φ := by
    ext v
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

private def opW (δ : F) (hδ : δ ≠ 0) : Module.End ℂ (S4 F) where
  toFun φ := ⟨ft4 δ φ.1, (ftBasic F δ hδ φ.1 φ.2).1⟩
  map_add' φ φ' := by
    ext v
    exact quaternaryFourier_add δ φ.2 φ'.2 v
  map_smul' c φ := by
    ext v
    exact quaternaryFourier_smul δ c φ.1 v

end UpperTheory.ConvolutionTheory.R2.C

end

theorem UpperTheory.ConvolutionTheory.R2.C.opsEx :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ), δ ≠ 0 → Nonempty (Ops δ η) := by
  intro F _ _ δ η hδ
  exact ⟨{ N := opN δ, M := opM η, W := opW δ hδ
           N_apply := fun _ _ _ => rfl
           M_apply := fun _ _ _ => rfl
           W_apply := fun _ _ => rfl }⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem lamR_quad (β r : ℝ) (hβ : β ≠ 0) (hr : 0 < r) :
    lamR (-β) * lamR β * lamR (-β) * lamR (-(r * β)) = -(lamR β * lamR (-β) * lamR β * lamR (r * β)) := by
  have h1 : |r * β| = r * |β| := by rw [abs_mul, abs_of_pos hr]
  have h2 : |r * -β| = r * |β| := by rw [abs_mul, abs_of_pos hr, abs_neg]
  have hs : ∀ x : ℝ, ((SignType.sign (r * x) : SignType) : ℂ) = ((SignType.sign x : SignType) : ℂ) := by
    intro x
    rw [sign_mul, sign_pos hr, one_mul]
  have hneg : ∀ x : ℝ, ((SignType.sign (-x) : SignType) : ℂ) = -((SignType.sign x : SignType) : ℂ) := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · simp [sign_neg h, sign_pos (neg_pos.2 h)]
    · simp [h]
    · simp [sign_pos h, sign_neg (neg_neg_of_pos h)]
  have hsq : ((SignType.sign β : SignType) : ℂ) ^ 2 = 1 := by
    rcases lt_or_gt_of_ne hβ with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]
  unfold lamR
  rw [show -(r * β) = r * -β by ring, hs (-β), hs β, hneg β, h1, h2, abs_neg]
  generalize ((SignType.sign β : SignType) : ℂ) = s at hsq ⊢
  generalize ((2 * √|β| : ℝ) : ℂ) = D
  generalize ((2 * √(r * |β|) : ℝ) : ℂ) = D'
  have h : (1 - Complex.I * -s) * (1 - Complex.I * -s) = -((1 - Complex.I * s) * (1 - Complex.I * s)) := by
    linear_combination (2 * s ^ 2) * Complex.I_sq - 2 * hsq
  linear_combination ((1 - Complex.I * -s) * (1 - Complex.I * s) * D⁻¹ ^ 3 * D'⁻¹) * h

theorem UpperTheory.ConvolutionTheory.R2.C.sgnLam :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ φ : F →+* ℝ, φ δ < 0) → ∀ a b : (A F)ˣ, IsSgn a → ∀ g : FiniteAdeleRing (𝓞 F) F → ℂ,
    Lam4 δ ((a * b : (A F)ˣ) : A F) (four (g1 g)) = -Lam4 δ (b : A F) (four (g1 g)) := by
  intro F _ _ _ δ hδ a b ha g
  obtain ⟨ha2, w₀, haw⟩ := ha
  let e : F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w₀).comp ((TR.pInf F).comp (algebraMap F (A F)))
  have he : TR.pInf F (rt δ) w₀ < 0 := hδ e
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 := hδ e
    simp at h0
  obtain ⟨C, hC⟩ := lamOne F g
  let d : (A F)ˣ := Units.map (algebraMap F (A F)).toMonoidHom (Units.mk0 δ hδ0)
  have hd : (d : A F) = rt δ := rfl
  have key : ∀ c : (A F)ˣ, Lam4 δ (c : A F) (four (g1 g)) =
      (C (c : A F).2 * C ((-c : (A F)ˣ) : A F).2 * C (c : A F).2 * C ((-(d * c) : (A F)ˣ) : A F).2) *
      ∏ w, (lamR (TR.pInf F (c : A F) w) * lamR (-TR.pInf F (c : A F) w) * lamR (TR.pInf F (c : A F) w) *
        lamR (-(TR.pInf F (rt δ) w * TR.pInf F (c : A F) w))) := by
    intro c
    have h1 := hC c
    have h2 := hC (-c)
    have h3 := hC (-(d * c))
    have e2 : ((-c : (A F)ˣ) : A F) = -(c : A F) := Units.val_neg c
    have e3 : ((-(d * c) : (A F)ˣ) : A F) = -(rt δ * (c : A F)) := by
      rw [Units.val_neg, Units.val_mul, hd]
    rw [lamFour, ← e3, ← e2, h1, h2, h3, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have p2 : ∀ w, TR.pInf F ((-c : (A F)ˣ) : A F) w = -TR.pInf F (c : A F) w := by
      intro w; rw [e2, map_neg, Pi.neg_apply]
    have p3 : ∀ w, TR.pInf F ((-(d * c) : (A F)ˣ) : A F) w = -(TR.pInf F (rt δ) w * TR.pInf F (c : A F) w) := by
      intro w; rw [e3, map_neg, map_mul, Pi.neg_apply, Pi.mul_apply]
    simp only [p2, p3]
    ring
  have pm : ∀ w, TR.pInf F ((a * b : (A F)ˣ) : A F) w = TR.pInf F (a : A F) w * TR.pInf F (b : A F) w := by
    intro w; rw [Units.val_mul, map_mul, Pi.mul_apply]
  let pf : A F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have ha2' : pf (a : A F) = 1 := ha2
  have f0 : pf ((a * b : (A F)ˣ) : A F) = pf (b : A F) := by
    rw [Units.val_mul, map_mul, ha2', one_mul]
  have f1 : ((a * b : (A F)ˣ) : A F).2 = (b : A F).2 := f0
  have f2 : ((-(a * b) : (A F)ˣ) : A F).2 = ((-b : (A F)ˣ) : A F).2 := by
    have h : pf ((-(a * b) : (A F)ˣ) : A F) = pf ((-b : (A F)ˣ) : A F) := by
      rw [Units.val_neg, Units.val_neg, map_neg, map_neg, f0]
    exact h
  have f3 : ((-(d * (a * b)) : (A F)ˣ) : A F).2 = ((-(d * b) : (A F)ˣ) : A F).2 := by
    have h : pf ((-(d * (a * b)) : (A F)ˣ) : A F) = pf ((-(d * b) : (A F)ˣ) : A F) := by
      rw [Units.val_neg, Units.val_neg, map_neg, map_neg, Units.val_mul, Units.val_mul d b, map_mul, map_mul, f0]
    exact h
  have hβ : TR.pInf F (b : A F) w₀ ≠ 0 := by
    intro h0
    have h1 : TR.pInf F (b : A F) * TR.pInf F ((b⁻¹ : (A F)ˣ) : A F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrFun h1 w₀
    rw [Pi.mul_apply, h0, zero_mul] at h2
    exact zero_ne_one h2
  have hP : ∀ w ∈ Finset.univ.erase w₀,
      lamR (TR.pInf F ((a * b : (A F)ˣ) : A F) w) * lamR (-TR.pInf F ((a * b : (A F)ˣ) : A F) w) *
        lamR (TR.pInf F ((a * b : (A F)ˣ) : A F) w) *
        lamR (-(TR.pInf F (rt δ) w * TR.pInf F ((a * b : (A F)ˣ) : A F) w)) =
      lamR (TR.pInf F (b : A F) w) * lamR (-TR.pInf F (b : A F) w) * lamR (TR.pInf F (b : A F) w) *
        lamR (-(TR.pInf F (rt δ) w * TR.pInf F (b : A F) w)) := by
    intro w hw
    simp only [pm, haw, if_neg (Finset.ne_of_mem_erase hw), one_mul]
  have hq := lamR_quad (TR.pInf F (b : A F) w₀) (-TR.pInf F (rt δ) w₀) hβ (neg_pos.2 he)
  have h0 : lamR (TR.pInf F ((a * b : (A F)ˣ) : A F) w₀) * lamR (-TR.pInf F ((a * b : (A F)ˣ) : A F) w₀) *
        lamR (TR.pInf F ((a * b : (A F)ˣ) : A F) w₀) *
        lamR (-(TR.pInf F (rt δ) w₀ * TR.pInf F ((a * b : (A F)ˣ) : A F) w₀)) =
      -(lamR (TR.pInf F (b : A F) w₀) * lamR (-TR.pInf F (b : A F) w₀) * lamR (TR.pInf F (b : A F) w₀) *
        lamR (-(TR.pInf F (rt δ) w₀ * TR.pInf F (b : A F) w₀))) := by
    have t1 : TR.pInf F ((a * b : (A F)ˣ) : A F) w₀ = -TR.pInf F (b : A F) w₀ := by
      rw [pm, haw, if_pos rfl, neg_one_mul]
    rw [t1, neg_neg, show -(TR.pInf F (rt δ) w₀ * -TR.pInf F (b : A F) w₀) =
      -(-TR.pInf F (rt δ) w₀ * TR.pInf F (b : A F) w₀) by ring, hq, neg_mul]
  rw [key (a * b), key b, f1, f2, f3,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀ : w₀ ∈ Finset.univ),
    Finset.prod_congr rfl hP, h0]
  ring
end
