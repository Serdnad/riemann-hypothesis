module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace GlobalTheory.RealWeilF

theorem map_conjTranspose_of_herm {n : ℕ} (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [conjTranspose_apply, map_apply]
  rw [← hcm, hJ]

theorem im_ne_zero_of_skew (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    {ξ₀ : E} (h0 : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀) (τ : E →+* ℂ) : (τ ξ₀).im ≠ 0 := by
  intro him
  have h1 : star (τ ξ₀) = -τ ξ₀ := by rw [← hcm, hσ, map_neg]
  have hre : (τ ξ₀).re = 0 := by
    have := congrArg Complex.re h1
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  have : τ ξ₀ = 0 := Complex.ext hre him
  exact h0 ((map_eq_zero τ).1 this)

theorem hermitianFormRealCoordinateBlock_hermitian_det {nS nT : ℕ} (σ : E →ₐ[F] E) (hcm : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x))
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (h0 : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀)
    (tau : InfinitePlace F → (E →+* ℂ)) :
    (HMF JS JT ξ₀ tau)ᴴ = HMF JS JT ξ₀ tau ∧ (HMF JS JT ξ₀ tau).det ≠ 0 := by
  classical
  have hdS : ∀ w, IsUnit (JS.map (tau w)).det := fun w => by
    have e := RingHom.map_det (tau w) JS
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hS.2))
  have hdT : ∀ w, IsUnit (JT.map (tau w)).det := fun w => by
    have e := RingHom.map_det (tau w) JT
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero (tau w)).2 hT.2))
  have hc : ∀ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) ≠ 0 := fun w => by
    have := im_ne_zero_of_skew σ hcm h0 hσ (tau w)
    exact_mod_cast mul_ne_zero two_ne_zero this
  constructor
  · unfold HMF
    rw [GlobalTheory.RealWeil.blk_conjTranspose]
    congr 1 <;> funext w
    · rw [conjTranspose_smul, map_conjTranspose_of_herm σ hcm hT.1]
      simp
    · rw [conjTranspose_nonsing_inv, map_conjTranspose_of_herm σ hcm hS.1]
  · have : HMF JS JT ξ₀ tau * GlobalTheory.RealWeil.blk (fun w => ((2 * (tau w ξ₀).im : ℝ) : ℂ)⁻¹ • (JT.map (tau w))⁻¹)
        (fun w => JS.map (tau w)) = 1 := by
      unfold HMF
      rw [GlobalTheory.RealWeil.blk_mul, ← GlobalTheory.RealWeil.blk_one]
      congr 1 <;> funext w
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hc w), one_smul,
          mul_nonsing_inv _ (hdT w)]
      · rw [mul_nonsing_inv _ (hdS w)]
    exact (isUnit_det_of_right_inverse this).ne_zero

end GlobalTheory.RealWeilF

theorem GlobalTheory.RealWeilF.HMF_herm_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ
  exact GlobalTheory.RealWeilF.hermitianFormRealCoordinateBlock_hermitian_det σ hB.cm.2.2.2 JS JT hS hT ξ₀ h0 hσ _
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem actOF_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (g : GAF σ JS) (h : GAF σ JT) (v : IxF F nS nT → ℂ),
        actOF σ JS JT g h (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ θ _ ι hι g h v
  have hfin : ∀ u : IxF F nS nT → ℂ, (iotaVF ι u).map (finPartF F E) = 0 := fun u => real_iotaVF hι u
  have hL : (actOF σ JS JT g h (iotaVF ι v)).map (finPartF F E) = 0 := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hfin, Matrix.mul_zero, Matrix.zero_mul]
  have hcpt : ∀ (u : IxF F nS nT → ℂ) w, compAtF θ w (iotaVF ι u) = GlobalTheory.RealWeil.cpt u w := by
    intro u w
    ext i j
    exact hι.comp _ w
  have hC : ∀ w, compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
      compAtF θ w (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v)) := by
    intro w
    have e : compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
        compAtF θ w (mtF σ JT h) * compAtF θ w (iotaVF ι v) * compAtF θ w (mtF σ JS g⁻¹) := by
      unfold actOF compAtF
      rw [Matrix.map_mul, Matrix.map_mul]
    rw [e, hcpt, hcpt, mMF_apply, GlobalTheory.RealWeil.cpt_blk]
  ext i j
  rw [← sub_eq_zero]
  refine hι.ext _ ?_ fun w => ?_
  · have h1 : finPartF F E (actOF σ JS JT g h (iotaVF ι v) i j) = 0 := congrFun (congrFun hL i) j
    have h2 : finPartF F E (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) i j) = 0 := congrFun (congrFun (hfin _) i) j
    rw [RingHom.map_sub, h1, h2, sub_zero]
  · have h3 := congrFun (congrFun (hC w) i) j
    simp only [compAtF, Matrix.map_apply, RingHom.comp_apply] at h3
    rw [RingHom.map_sub, RingHom.map_sub, h3, sub_self]

end GlobalTheory.RealWeilF
end

section

noncomputable section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF.CMChart

open Formalism.L2.Fam.ThC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rc [IsTotallyReal F] (v : InfinitePlace F) : v.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)

theorem compF_eq [IsTotallyReal F] (τ : E →+* ℂ) (w : InfinitePlace F) (h : plF (F := F) τ = w) (a : Ainf F) :
    compF (F := F) τ a = (rc w (a w) : ℝ) := by
  subst h
  exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal _) _).symm

def rho [IsTotallyReal F] : (InfinitePlace F → ℝ) →+ Ainf F where
  toFun x v := (rc v).symm (x v)
  map_zero' := funext fun v => map_zero (rc v).symm
  map_add' _ _ := funext fun v => map_add (rc v).symm _ _

theorem continuous_rho [IsTotallyReal F] : Continuous (rho (F := F)) :=
  continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous.comp
      (continuous_apply v)

theorem rc_rho [IsTotallyReal F] (x : InfinitePlace F → ℝ) (w : InfinitePlace F) : rc w (rho x w) = x w :=
  (rc w).apply_symm_apply _

def embA (e : E) : Ainf F →+ AEF F E where
  toFun a := pairA F a 0 ⊗ₜ[F] e
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' a b := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext rfl (add_zero _).symm

theorem continuous_embA (e : E) : Continuous (embA (F := F) e) := by
  haveI := isModuleTopology_AE F E
  have h1 : Continuous fun a : Ainf F => pairA F a 0 :=
    Continuous.prodMk continuous_id continuous_const
  have h2 : Continuous fun a : AF F => a • ((1 : AF F) ⊗ₜ[F] e : AEF F E) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  refine (h2.comp h1).congr fun a => ?_
  show pairA F a 0 • ((1 : AF F) ⊗ₜ[F] e : AEF F E) = pairA F a 0 ⊗ₜ[F] e
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem finPart_embA (e : E) (a : Ainf F) : finPartF F E (embA e a) = 0 :=
  TensorProduct.zero_tmul _ e

theorem infPart_embA (e : E) (a : Ainf F) : infPartF F E (embA e a) = a ⊗ₜ[F] e := rfl

theorem tensor_span {M : Type} [AddCommGroup M] [Module F M] (δ : E)
    (h : ∀ x : E, ∃ u v : F, u • (1 : E) + v • δ = x) (a : M ⊗[F] E) :
    ∃ a₀ a₁ : M, a = a₀ ⊗ₜ[F] (1 : E) + a₁ ⊗ₜ[F] δ := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul m x =>
    obtain ⟨u, v, rfl⟩ := h x
    exact ⟨u • m, v • m, by simp only [TensorProduct.tmul_add, TensorProduct.smul_tmul]⟩
  | add a b ha hb =>
    obtain ⟨a₀, a₁, rfl⟩ := ha
    obtain ⟨b₀, b₁, rfl⟩ := hb
    exact ⟨a₀ + b₀, a₁ + b₁, by simp only [TensorProduct.add_tmul]; abel⟩

theorem exists_gen {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ δ : E, (∀ τ : E →+* ℂ, (τ δ).im ≠ 0) ∧ ∀ x : E, ∃ u v : F, u • (1 : E) + v • δ = x := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hn : ¬ ComplexEmbedding.IsReal τ₀ := IsTotallyComplex.complexEmbedding_not_isReal τ₀
  have : ∃ δ : E, σ δ ≠ δ := by
    by_contra hcon
    push Not at hcon
    apply hn
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hσ τ₀ x
    rw [hcon] at this
    exact this.symm
  obtain ⟨δ, hδ⟩ := this
  refine ⟨δ, fun τ hτ => hδ (τ.injective ?_), ?_⟩
  · rw [hσ]
    exact Complex.conj_eq_iff_im.2 hτ
  · have hli : LinearIndependent F ![(1 : E), δ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h3 := congrArg σ hst
      rw [map_add (f := _), Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, σ.commutes, σ.commutes, map_one, map_zero,
        ← Algebra.smul_def, ← Algebra.smul_def] at h3
      have h4 : t • (σ δ - δ) = 0 := by
        rw [smul_sub, eq_neg_of_add_eq_zero_right h3, eq_neg_of_add_eq_zero_right hst, sub_self]
      have ht : t = 0 := (smul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hδ)
      rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, ht⟩
    have hsp := hli.span_eq_top_of_card_eq_finrank (by rw [h2]; rfl)
    intro x
    have hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ]) := hsp ▸ Submodule.mem_top
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union,
      Submodule.mem_span_pair] at hx
    exact hx

def fstC {I : Type} (c : I → ℂ) : (I → ℂ) →+ (I → ℝ) where
  toFun z i := (z i).re - (z i).im / (c i).im * (c i).re
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp only [Pi.add_apply, Complex.add_re, Complex.add_im]; ring

def sndC {I : Type} (c : I → ℂ) : (I → ℂ) →+ (I → ℝ) where
  toFun z i := (z i).im / (c i).im
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp only [Pi.add_apply, Complex.add_im]; ring

theorem exists_chart_of_cm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (tau : InfinitePlace F → (E →+* ℂ))
    (htau : ∀ w, plF (F := F) (tau w) = w) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (hθ : IsInfFamF tau θ) :
    ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  haveI : IsTotallyReal F := h.1
  obtain ⟨δ, hδ, hsp⟩ := exists_gen h
  have hθ' : ∀ w (a : Ainf F) (x : E), θ w (a ⊗ₜ[F] x) = (rc w (a w) : ℝ) * tau w x := by
    intro w a x
    rw [isInfEmb_unique (tau w) (hθ w) (projAt_isInfEmb (tau w)), projAt_tmul, compF_eq _ w (htau w)]
  let c : InfinitePlace F → ℂ := fun w => tau w δ
  let ι : (InfinitePlace F → ℂ) →+ AEF F E :=
    (embA 1).comp (rho.comp (fstC c)) + (embA δ).comp (rho.comp (sndC c))
  have hι : ∀ z, ι z = embA 1 (rho (fstC c z)) + embA δ (rho (sndC c z)) := fun _ => rfl
  refine ⟨ι, ?_, fun z => ?_, fun z w => ?_, fun a hf hi => ?_⟩
  · have c2 : ∀ w, Continuous fun z : InfinitePlace F → ℂ => (z w).im / (c w).im := fun w =>
      (Complex.continuous_im.comp (continuous_apply w)).div_const _
    have c1 : Continuous (fstC c) :=
      continuous_pi fun w => (Complex.continuous_re.comp (continuous_apply w)).sub ((c2 w).mul continuous_const)
    have c3 : Continuous (sndC c) := continuous_pi c2
    exact ((continuous_embA _).comp (continuous_rho.comp c1)).add ((continuous_embA _).comp (continuous_rho.comp c3))
  · rw [hι, RingHom.map_add (f := _), finPart_embA, finPart_embA, add_zero]
  · rw [hι, RingHom.map_add (f := _), infPart_embA, infPart_embA, RingHom.map_add (f := _), hθ', hθ', rc_rho, rc_rho, map_one, mul_one]
    have h0 : (c w).im ≠ 0 := hδ _
    show (((z w).re - (z w).im / (c w).im * (c w).re : ℝ) : ℂ) + (((z w).im / (c w).im : ℝ) : ℂ) * c w = z w
    apply Complex.ext
    · rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, div_mul_cancel₀ _ h0]
  · obtain ⟨b₀, b₁, hb⟩ := tensor_span δ hsp (infPartF F E a)
    have key : ∀ w, rc w (b₀ w) = 0 ∧ rc w (b₁ w) = 0 := by
      intro w
      have e := hi w
      rw [hb, RingHom.map_add (f := _), hθ', hθ', map_one, mul_one] at e
      have e1 := congrArg Complex.re e
      have e2 := congrArg Complex.im e
      rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, Complex.zero_im] at e2
      have e3 := (mul_eq_zero.1 e2).resolve_right (hδ _)
      rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, e3, zero_mul, add_zero, Complex.zero_re] at e1
      exact ⟨e1, e3⟩
    have z0 : b₀ = 0 := funext fun w => (rc w).map_eq_zero_iff.1 (key w).1
    have z1 : b₁ = 0 := funext fun w => (rc w).map_eq_zero_iff.1 (key w).2
    rw [z0, z1, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero] at hb
    have hp : pairE (infPartF F E a) (finPartF F E a) = a := pairE_eta a
    rw [← hp, hb, hf]
    simp [pairE]

theorem exists_chartF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  intro F E _ _ _ _ _ σ B hB θ hθ
  refine exists_chart_of_cm hB.cm (fun w => (B.emb w).1) (fun w => ?_) θ hθ
  show InfinitePlace.mk ((B.emb w).1.comp (algebraMap F E)) = w
  rw [(B.emb w).2, InfinitePlace.mk_embedding]

end GlobalTheory.RealWeilF.CMChart

end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem eq_of_sq_mul_eq_cube {α : Type*} [LinearOrderedCommGroupWithZero α] {a b c : α} (hc : c ≠ 0)
    (ha : a ≤ c) (hb : b ≤ c) (h : a ^ 2 * b = c ^ 3) : a = c := by
  by_contra hne
  have hlt : a < c := lt_of_le_of_ne ha hne
  have hc0 : 0 < c := zero_lt_iff.mpr hc
  have h1 : a ^ 2 * b ≤ a ^ 2 * c := by gcongr
  have h2 : a ^ 2 < c ^ 2 := pow_lt_pow_left₀ hlt zero_le' two_ne_zero
  have h3 : a ^ 2 * c < c ^ 2 * c := mul_lt_mul_of_pos_right h2 hc0
  have h4 : c ^ 2 * c = c ^ 3 := by rw [pow_succ c 2]
  rw [h4] at h3
  rw [h] at h1
  exact lt_irrefl _ (lt_of_le_of_lt h1 h3)

theorem natCast_mul_intCast_mul_mem (L : PeriodPair) {N : ℕ} {z : ℂ} (hN : (N : ℂ) * z ∈ L.lattice) (k : ℤ) :
    (N : ℂ) * ((k : ℂ) * z) ∈ L.lattice := by
  have e : (N : ℂ) * ((k : ℂ) * z) = k • ((N : ℂ) * z) := by rw [zsmul_eq_mul]; ring
  rw [e]
  exact L.lattice.smul_mem k hN

theorem mem_lattice_of_coprime (L : PeriodPair) {N k : ℕ} (hNk : Nat.Coprime N k) {z : ℂ}
    (hN : (N : ℂ) * z ∈ L.lattice) (hk : (k : ℂ) * z ∈ L.lattice) : z ∈ L.lattice := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hNk
  have hab' : (a : ℂ) * (N : ℂ) + (b : ℂ) * (k : ℂ) = 1 := by exact_mod_cast hab
  have e : z = a • ((N : ℂ) * z) + b • ((k : ℂ) * z) := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    linear_combination (-z) * hab'
  rw [e]
  exact L.lattice.add_mem (L.lattice.smul_mem a hN) (L.lattice.smul_mem b hk)

theorem weierstrassP_sub_two_mul_unit : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ¬ 3 ∣ N → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → 2 * z ∉ L.lattice ∧ V.valuation (L.weierstrassP z - L.weierstrassP (2 * z)) = V.valuation u ^ 2 := by
  intro L β u V N hβ hβim hu hN hodd h3 z hz hNz
  have cop2 : Nat.Coprime N 2 := (Nat.coprime_two_left.mpr hodd).symm
  have cop3 : Nat.Coprime N 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have h2z : 2 * z ∉ L.lattice := fun h =>
    hz (mem_lattice_of_coprime L cop2 hNz (by push_cast; exact h))
  have h3z : 3 * z ∉ L.lattice := fun h =>
    hz (mem_lattice_of_coprime L cop3 hNz (by push_cast; exact h))
  have hN2z : (N : ℂ) * (2 * z) ∈ L.lattice := by
    simpa using natCast_mul_intCast_mul_mem L hNz 2
  have hN3z : (N : ℂ) * (3 * z) ∈ L.lattice := by
    simpa using natCast_mul_intCast_mul_mem L hNz 3
  refine ⟨h2z, ?_⟩
  have e1 : 2 * z - z = z := by ring
  have e2 : 2 * z + z = 3 * z := by ring
  have hd := GlobalTheory.T.weierstrassP_sub_sq_mul_add_sub_eq_neg_deriv_mul L (2 * z) z h2z hz (by rw [e1]; exact hz) (by rw [e2]; exact h3z)
  rw [e1, e2] at hd
  have d1 := GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu hN hodd z hz hNz
  have d2 := GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion L β u V N hβ hβim hu hN hodd (2 * z) h2z hN2z
  have m1 := (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN z (2 * z) hz h2z hNz hN2z).2
  have m2 := (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN (3 * z) z h3z hz hN3z hNz).2
  have hv : V.valuation u ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hu
    exact latticeCurve_Δ_ne_zero L ((Valuation.zero_iff _).mp hu.symm)
  have hv2 : 0 < V.valuation u ^ 2 := zero_lt_iff.mpr (pow_ne_zero 2 hv)
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀, map_pow, div_le_one₀ hv2] at m1 m2
  have hval := congrArg V.valuation hd
  rw [map_mul, map_pow, Valuation.map_neg, map_mul, d1, d2,
    Valuation.map_sub_swap V.valuation (L.weierstrassP (2 * z))] at hval
  refine eq_of_sq_mul_eq_cube (pow_ne_zero 2 hv) m1 m2 ?_
  rw [hval, ← pow_add, ← pow_mul]

end GlobalTheory.CMModel
end

section


theorem _root_.GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange : ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V'] (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension iV → GlobalTheory.FieldBaseChange.IsExtension iW → ∀ (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W'), (∀ i v, a' i (iV v) = iV (a i v)) → (∀ i w, b' i (iW w) = iW (b i w)) → ∀ E' : V' →ₗ[F] W', Function.Bijective E' → (∀ i v, E' (a' i v) = b' i (E' v)) → ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | exact GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.PrincLev

def congGroup {D : D7} (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | GlobalTheory.Member.FinCong V N k}
  one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V N
  mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
  inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha

theorem isOpen_congGroup {D : D7} (V : HSp D) {N : ℕ} (hN : 0 < N) : IsOpen (congGroup V N : Set (GA D V)) :=
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  Subgroup.isOpen_of_mem_nhds _ (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN)

theorem mem_of_isLevelK {D : D7} {V W : HSp D} (hV : V = W) {N : ℕ} {Kf : Subgroup (GA D V)} (hK : IsLevelK V N Kf)
    (k : GA D W) (h1 : k ∈ congGroup W N) (h2 : k ∈ GfC W) : cast (congrArg (GA D) hV.symm) k ∈ Kf := by
  subst hV
  exact (hK k).2 ⟨h2, h1⟩

theorem mem_levG_triv_iff {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    k ∈ levG (Wc D i) (L.βW i) (L.datWp i L.triv) ↔ IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) 1 k :=
  ⟨fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩, fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.2 h.2.2⟩⟩

theorem levChi_triv_eq_one {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  have h : ∀ x, ext1 L.triv.H L.triv.chi x = 1 := fun x => by
    unfold ext1; split_ifs <;> rfl
  unfold levChi levFn
  simp [LevCh.datWp, datY]
  exact h _



theorem principal_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, (∀ g : GA D (Wc D i), g ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ↔ cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ)) ∧ (∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1) ∧ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ≤ GfC (Wc D i) ∧ ∃ U : Subgroup (GA D (Wc D i)), IsOpen (U : Set (GA D (Wc D i))) ∧ ∀ k ∈ U, k ∈ GfC (Wc D i) → k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL _ ht hpb i σ hσ hV
  have key : ∀ g : GA D (Wc D i), g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ↔
      cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ) := fun g =>
    (mem_levG_triv_iff R.toLevCh i g).trans (GlobalTheory.T.level_character_embedding_compat T R κ v₀ hL ht hpb i (res T σ) hσ hV g)
  have hg : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  refine ⟨key, fun k _ => levChi_triv_eq_one R.toLevCh i k, fun k hk => hk.1,
    congGroup (Wc D i) (D.host.g 0 * D.host.g 1), isOpen_congGroup _ hg, fun k h1 h2 => (key k).2 ?_⟩
  exact mem_of_isLevelK hV (ht.laws.levelK _ (inR i) _ hσ) k h1 h2

end GlobalTheory.HolDict.PrincLev
end
end
