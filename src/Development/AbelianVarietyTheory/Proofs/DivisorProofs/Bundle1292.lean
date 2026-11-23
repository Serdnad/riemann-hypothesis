module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RealConjFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inv_mem_UAt {n : ℕ} {X : Spc F E n} {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) :
    g⁻¹ ∈ UAt σ X (evI F) := by
  intro u hu
  have h1 : u • (mat g - 1) = 0 := hg u hu
  have hm : mat g⁻¹ * mat g = 1 := by simp [mat]
  have : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, hm, Matrix.mul_one, neg_sub]
  rw [this, smul_neg, ← Matrix.mul_smul, h1, Matrix.mul_zero, neg_zero]

theorem acts_comp {κ : Type} [Fintype κ] {A B : Module.End ℂ ((κ → AF F) → ℂ)}
    (hA : ∀ Φ ∈ schA F κ, A Φ ∈ schA F κ) {f f₁ f₂ : SInf F κ}
    (h₁ : Acts (evI F) A (⇑f) (⇑f₁)) (h₂ : Acts (evI F) B (⇑f₁) (⇑f₂)) :
    Acts (evI F) (B * A) (⇑f) (⇑f₂) := by
  intro r hr
  have e₁ := h₁ r hr
  have hr₁ : Rest (evI F) (⇑f₁) r := ⟨hr.1, by rw [← e₁]; exact hA _ hr.2⟩
  rw [Module.End.mul_apply, e₁]
  exact h₂ r hr₁

end GlobalTheory.RealConjFac
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem heisenbergDeriv_tensor_conj (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ))
    (hg₁ : ∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y)
    (hg₂ : ∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y)
    (hh : ∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x)
    (hf₀ : ∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) := by
  let L₁ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inl i))
  let L₂ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inr i))
  have hL₁ : ∀ y, L₁ y = y ∘ Sum.inl := fun y => rfl
  have hL₂ : ∀ y, L₂ y = y ∘ Sum.inr := fun y => rfl
  have hfun : (f₀ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ) = fun y => f (L₁ y) * Complex.conjCLE (f (L₂ y)) := by
    funext y; rw [hf₀]; rfl
  have hd₁ : HasFDerivAt (fun y => f (L₁ y)) ((fderiv ℝ f (L₁ x)).comp L₁) x :=
    (f.differentiableAt.hasFDerivAt).comp x L₁.hasFDerivAt
  have hd₂ : HasFDerivAt (fun y => Complex.conjCLE (f (L₂ y)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f (L₂ x)).comp L₂)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x ((f.differentiableAt.hasFDerivAt).comp x L₂.hasFDerivAt)
  have hD : fderiv ℝ f₀ x = f (L₁ x) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f (L₂ x)).comp L₂)) + Complex.conjCLE (f (L₂ x)) • ((fderiv ℝ f (L₁ x)).comp L₁) := by
    rw [hfun]
    exact (hd₁.mul hd₂).fderiv
  have hevneg : ∀ b : AF F, evI F (-b) = - evI F b := by
    intro b
    unfold evI
    rw [show (-b).1 = -b.1 from rfl, map_neg]
  have htr : (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ)
      = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, (x ∘ Sum.inl) i * evI F (b₁ i))
        - Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, (x ∘ Sum.inr) i * evI F (b₂ i)) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, hevneg, mul_neg, Finset.sum_neg_distrib,
      map_add, map_neg, Function.comp_apply]
    ring
  rw [hh x, hg₁, hg₂, hD, htr, hf₀]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, hL₁, hL₂, smul_eq_mul]
  have e1 : ((fun i => evI F (Sum.elim a₁ a₂ i)) ∘ Sum.inl) = fun i => evI F (a₁ i) := rfl
  have e2 : ((fun i => evI F (Sum.elim a₁ a₂ i)) ∘ Sum.inr) = fun i => evI F (a₂ i) := rfl
  rw [e1, e2]
  simp only [star_sub, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

end GlobalTheory
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.RestCofactor

variable {F : Type} [Field F] [NumberField F]

def shiftFin (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) : κ → Af F :=
  fun i => y i + (singleFin v (x₀ i) - singleFin v (evalV F v (y i)))

theorem evalV_shiftFin (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) (i : κ) :
    evalV F v (shiftFin v x₀ y i) = x₀ i := by
  simp only [shiftFin, map_add (f := _), map_sub, evalV_singleFin_self]
  abel

theorem shiftFin_back (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) :
    shiftFin v (fun i => evalV F v (y i)) (shiftFin v x₀ y) = y := by
  funext i
  rw [shiftFin, evalV_shiftFin]
  simp only [shiftFin]
  abel

theorem continuous_shiftFin (v : Pl (F := F)) {κ : Type} :
    Continuous fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2 := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  refine continuous_pi fun i => ?_
  have h2 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.2 i := (continuous_apply i).comp continuous_snd
  have h1 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.1 i := (continuous_apply i).comp continuous_fst
  exact h2.add (((continuous_singleFin v).comp h1).sub ((continuous_singleFin v).comp (hev.comp h2)))

theorem mem_SB_shift (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) {φ' : (κ → Fv F v) → ℂ}
    (hφ' : φ' ∈ SB (κ → Fv F v)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    (fun y : κ → Af F => φ' (fun i => evalV F v (y i)) * g (shiftFin v x₀ y)) ∈ SB (κ → Af F) := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have hE : Continuous fun y : κ → Af F => fun i => evalV F v (y i) :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have hS : Continuous (shiftFin v x₀) :=
    (continuous_shiftFin v).comp (continuous_const.prodMk continuous_id)
  refine ⟨(hφ'.1.comp_continuous hE).mul (hg.1.comp_continuous hS), ?_⟩
  have hK : IsCompact ((fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2) ''
      (tsupport φ' ×ˢ tsupport g)) := (IsCompact.prod hφ'.2 hg.2).image (continuous_shiftFin v)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  have ha : φ' (fun i => evalV F v (y i)) ≠ 0 := left_ne_zero_of_mul hne
  have hb : g (shiftFin v x₀ y) ≠ 0 := right_ne_zero_of_mul hne
  exact hy ⟨(fun i => evalV F v (y i), shiftFin v x₀ y),
    ⟨subset_tsupport _ ha, subset_tsupport _ hb⟩, shiftFin_back v x₀ y⟩

theorem rest_of_rest : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (φ φ' : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ≠ 0 → φ' ∈ SB (κ → Fv F v) →
    Rest (evFin F v) φ r → Rest (evFin F v) φ' r := by
  intro F _ _ κ _ v φ φ' r hφ hφ' hr
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hφ
  refine ⟨hr.1, ?_⟩
  let z : (κ → AF F) → κ → AF F := fun x i =>
    pairA F 0 (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2))
  have hz : ∀ x, At (evFin F v) (z x) := by
    intro x u hu
    funext i
    refine Prod.ext ?_ ?_
    · change u.1 * 0 = 0
      exact mul_zero _
    · change u.2 * (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2)) = 0
      refine af_ext fun w => ?_
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw
        have : evalV F w u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [map_sub, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_zero, mul_zero]
  have h1 : ∀ x i, ((x + z x) i).1 = (x i).1 := fun x i => by
    change (x i).1 + 0 = (x i).1
    exact add_zero _
  have h2 : ∀ x i, ((x + z x) i).2 = shiftFin v x₀ (fun i => (x i).2) i := fun x i => rfl
  have hev : ∀ x i, evFin F v ((x + z x) i) = x₀ i := fun x i => by
    change evalV F v ((x + z x) i).2 = x₀ i
    rw [h2, evalV_shiftFin]
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => φ' (fun i => evFin F v (x i)) * Φ (x + z x)
      map_add' := fun Φ Ψ => funext fun x => by simp only [Pi.add_apply]; ring
      map_smul' := fun c Φ => funext fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hL : schA F κ ≤ (schA F κ).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨f, _, mem_SB_shift v x₀ hφ' hg, funext fun x => ?_⟩
    change φ' (fun i => evFin F v (x i)) * pureA F f g (x + z x) = _
    simp only [pureA, h1, h2]
    change _ = _ * (φ' (fun i => evFin F v (x i)) * _)
    ring
  have key : tens (evFin F v) φ' r = (φ x₀)⁻¹ • L (tens (evFin F v) φ r) := by
    funext x
    change φ' (fun i => evFin F v (x i)) * r x =
      (φ x₀)⁻¹ * (φ' (fun i => evFin F v (x i)) * (φ (fun i => evFin F v ((x + z x) i)) * r (x + z x)))
    have hx : φ x₀ ≠ 0 := hx₀
    simp only [hev, hr.1 x (z x) (hz x)]
    rw [mul_left_comm (φ x₀)⁻¹, ← mul_assoc (φ x₀)⁻¹, inv_mul_cancel₀ hx, one_mul]
  rw [key]
  exact Submodule.smul_mem _ _ (hL hr.2)

end GlobalTheory.RestCofactor
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.CartanTensor

open Matrix
open scoped Kronecker ComplexOrder

variable {n d : ℕ}

theorem map_star_mul {a b c : Type} [Fintype b] (A : Matrix a b ℂ) (B : Matrix b c ℂ) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

theorem cartan_comm {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M * θ.map star = θᵀ * M := by
  obtain ⟨h1, h2, -⟩ := h
  have h1' : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h1]
    exact Matrix.map_one star (star_zero _) (star_one _)
  calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [h2]
    _ = θᵀ * M := by rw [Matrix.mul_assoc (θᵀ * M), h1', Matrix.mul_one]

theorem cartan_posDef {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) :
    (θᵀ * M).PosDef := by
  have hH : (θᵀ * M).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, ← cartan_comm h]
    congr 1 <;> ext i j <;> simp [hM]
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun c hc => Complex.pos_iff.2 ⟨?_, (hH.im_star_dotProduct_mulVec_self c).symm⟩⟩
  have hx : star c ≠ 0 := by simpa using hc
  have := h.2.2 (star c) hx
  rw [star_star] at this
  convert this using 2
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem quadruple_sum_eq_trace_transpose_mul (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * A i k * B j l * star (y k l)) = trace (xᵀ * (A * y.map star * Bᵀ)) := by
  rw [← trace_transpose_mul, transpose_transpose]
  simp only [trace, diag_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quadruple_sum_eq_kronecker_quadraticForm (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ) (x : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * P i k * Q j l * star (x k l)) =
      star (fun p : Fin n × Fin d => star (x p.1 p.2)) ⬝ᵥ ((P ⊗ₖ Q) *ᵥ fun p : Fin n × Fin d => star (x p.1 p.2)) := by
  simp only [dotProduct, mulVec, kronecker_apply, Fintype.sum_prod_type, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem map_star_smulI {a b : Type} (M : Matrix a b ℂ) : (Complex.I • M).map star = (-Complex.I) • M.map star := by
  ext i j; simp

theorem cancelI {A B : Matrix (Fin d) (Fin d) ℂ} (h : Complex.I • A = Complex.I • B) : A = B :=
  smul_right_injective _ Complex.I_ne_zero h

theorem tensor_cartan_invariant_pos : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  intro n d JX θX JW θW hJX hX hJW hW x y
  have hWc : θWᵀ * JW * θW.map star = JW := by
    have h := hW.2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cW : JW * θW.map star = θWᵀ * JW := by
    have h := cartan_comm hW
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cX := cartan_comm hX
  have hIW : ∀ i j, star ((Complex.I • JW) j i) = (Complex.I • JW) i j := by
    intro i j; simp [hJW]
  constructor
  · rw [quadruple_sum_eq_trace_transpose_mul, quadruple_sum_eq_trace_transpose_mul]
    have e1 : (Complex.I • (θX * x * θWᵀ))ᵀ * (JX * (Complex.I • (θX * y * θWᵀ)).map star * JWᵀ) =
        θW * (xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ) := by
      rw [map_star_smulI, transpose_smul, map_star_mul, map_star_mul, transpose_mul, transpose_mul, transpose_transpose,
        transpose_map]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_mul]
    have e2 : xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ * θW =
        xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θWᵀ * JW * θW.map star)ᵀ := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [e1, trace_mul_comm, e2, hX.2.1, hWc]
    simp only [Matrix.mul_assoc]
  · intro hx
    have e3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
        -(xᵀ * ((θXᵀ * JX) * x.map star * (θWᵀ * (Complex.I • JW))ᵀ)) := by
      have h3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
          (-Complex.I) • (xᵀ * (JX * θX.map star) * x.map star * (JW * θW.map star)ᵀ) := by
        rw [map_star_smulI, map_star_mul, map_star_mul, transpose_map, transpose_mul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      rw [h3, cX, cW]
      simp only [Matrix.smul_mul, Matrix.mul_smul, transpose_smul, neg_smul, Matrix.mul_assoc]
    rw [quadruple_sum_eq_trace_transpose_mul, e3, trace_neg, Complex.neg_re, neg_neg,
      ← quadruple_sum_eq_trace_transpose_mul (θXᵀ * JX) (θWᵀ * (Complex.I • JW)) x x, quadruple_sum_eq_kronecker_quadraticForm]
    have hK := (cartan_posDef hJX hX).kronecker (cartan_posDef hIW hW)
    have hc : (fun p : Fin n × Fin d => star (x p.1 p.2)) ≠ 0 := by
      intro h; apply hx; ext i j; have := congrFun h (i, j); simpa using this
    exact (Complex.pos_iff.1 ((posDef_iff_dotProduct_mulVec.1 hK).2 hc)).1

end GlobalTheory.CartanTensor
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormLocSplit

theorem norm_at_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (z - 1) →
    At (evFin F v) (Algebra.norm (AF F) z - 1) ∧ evFin F v (Algebra.norm (AF F) z) = piW τ z * piW (τ.comp σ) z := by
  intro F E _ _ _ _ _ σ h v τ z hz
  have hN : algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (Algebra.norm (AF F) z) = z * cA σ z :=
    GlobalTheory.Doubling.algebraMap_norm_eq h z
  have hinj : Function.Injective (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    Algebra.TensorProduct.includeLeft_injective (S := AF F) (algebraMap F E).injective
  refine ⟨fun u hu => hinj ?_, ?_⟩
  · have h1 : u • (z - 1) = 0 := hz u hu
    have h2 : u • (cA σ z - 1) = 0 := by
      have := congrArg (cA σ) h1
      rwa [map_smul, map_sub, map_one, map_zero] at this
    rw [smul_eq_mul, map_mul, map_sub, map_one, hN, map_zero, ← Algebra.smul_def,
      show z * cA σ z - 1 = (z - 1) * cA σ z + (cA σ z - 1) by ring, smul_add, ← smul_mul_assoc, h1, h2,
      zero_mul, add_zero]
  · have h3 := congrArg (piW τ) hN
    have hc : piW τ (cA σ z) = piW (τ.comp σ) z := by
      change splitProj τ (compFin F E v (sigR (AF F) σ z)) = splitProj (τ.comp σ) (compFin F E v z)
      have hs : ∀ y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), compFin F E v (sigR (AF F) σ y) = sigR (Fv F v) σ (compFin F E v y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a x => rfl
        | add x y hx hy => simp only [map_add (f := _), hx, hy]
      rw [hs, splitProj_comp]
    have ha : piW τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (Algebra.norm (AF F) z)) = evFin F v (Algebra.norm (AF F) z) := by
      change splitProj τ (compFin F E v (Algebra.norm (AF F) z ⊗ₜ[F] 1)) = _
      simp [compFin]
    rw [map_mul, hc, ha] at h3
    exact h3

end GlobalTheory.NormLocSplit
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.ArchHeisPure

open scoped Classical Matrix

theorem exists_phase_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (a : V)
    (f : SchwartzMap V ℂ) : ∃ g : SchwartzMap V ℂ, ∀ x,
      g x = Complex.exp (-(2 * Real.pi * Complex.I) * ((L x + c : ℝ) : ℂ)) * f (x + a) := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (GlobalTheory.LinPhaseSeminorm.phaseLine c 1 ∘ ⇑L) (SchwartzMap.compSubConstCLM ℂ (-a) f),
    fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c 1),
    ← GlobalTheory.LinPhaseSeminorm.phase_eq]
  simp

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F) in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

def trForm (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add (f := _)]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem evHom_apply (a : AF F) : evHom F a = evI F a := rfl

theorem trForm_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trForm c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

theorem schr_pureA [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)}
    (hw : At (evI F) w) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, schr ψ w (pureA F f h) = pureA F f₁ h := by
  obtain ⟨p, q⟩ := w
  obtain ⟨g, hg⟩ := exists_phase_translate (trForm fun i => evI F (q i))
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q)))) (fun i => evI F (p i)) f
  refine ⟨g, fun h => funext fun x => ?_⟩
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => evI F (x i)) + fun i => evI F (p i) := by
    funext i
    exact map_add (evHom F) (x i) (p i)
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      trForm (fun i => evI F (q i)) (fun i => evI F (x i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q))) := by
    rw [← evHom_apply, map_add (f := _), map_add (f := _), RingHom.map_dotProduct, trForm_apply]
    rfl
  simp only [schr, pureA]
  rw [hψ.2.2 _ hAt, htr, hfin, harch, ← mul_assoc, ← hg]
  rfl

theorem rho_pureA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f
  refine schr_pureA hψ (fun r hr => ?_) f
  rw [← map_smul, hu r hr, map_zero]

end GlobalTheory.ArchHeisPure

end
end
