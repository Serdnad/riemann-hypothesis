module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle045
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

section TmSurj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem embOf_coe (s : 𝓞 E →+* ℂ) (x : 𝓞 E) : embOf s (x : E) = s x :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) x


omit [IsCMField E] in
theorem embOf_restrict (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) x


omit [IsCMField E] in
theorem embOf_conj (s : 𝓞 E →+* ℂ) : embOf ((starRingEnd ℂ).comp s) = ComplexEmbedding.conjugate (embOf s) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  have h1 := embOf_coe ((starRingEnd ℂ).comp s) x
  have h2 := embOf_coe s x
  simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq]
  change embOf ((starRingEnd ℂ).comp s) (x : E) = starRingEnd ℂ (embOf s (x : E))
  rw [h1, h2]; rfl


omit [IsCMField E] in
theorem embOf_inj {s s' : 𝓞 E →+* ℂ} (h : embOf s = embOf s') : s = s' := by
  ext x
  rw [← embOf_coe s, ← embOf_coe s', h]

variable {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact F.cm.1 (embOf_inj h)
    · exfalso
      rw [← embOf_conj] at h
      have h' := embOf_inj h
      exact (F.cm.2 (F.σ τ)).1 ⟨τ, rfl⟩ ⟨τ', h'.symm⟩
  · intro w
    by_cases hs : ∃ τ, F.σ τ = w.embedding.comp (algebraMap (𝓞 E) E)
    · obtain ⟨τ, hτ⟩ := hs
      refine ⟨τ, ?_⟩
      simp only [plc, hτ, embOf_restrict, InfinitePlace.mk_embedding]
    · have := not_imp_not.2 (F.cm.2 (w.embedding.comp (algebraMap (𝓞 E) E))).2 hs
      obtain ⟨τ, hτ⟩ := not_not.1 this
      refine ⟨τ, ?_⟩
      have : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding := by
        rw [hτ, ← RingHom.comp_assoc, embOf_restrict]; rfl
      simp only [plc, this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

end TmSurj

theorem tm_surj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (b : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (b τ)ᴴ * C.gr τ * b τ = C.gr τ) → ∃ a : C.Arch, ∀ τ, C.tm a τ = b τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C b hb
  classical
  have hbij := plc_bijective F
  let e : Ψ ≃ InfinitePlace E := Equiv.ofBijective (plc F) hbij
  have he : ∀ τ, e.symm (plc F τ) = τ := fun τ => e.symm_apply_apply τ
  have hw : ∀ w, plc F (e.symm w) = w := fun w => e.apply_symm_apply w
  let v := Pi.basisFun E (Fin (j + j'))
  let M : InfinitePlace E → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun w =>
    if w.embedding = embOf (F.σ (e.symm w)) then b (e.symm w) else (b (e.symm w)).map (starRingEnd ℂ)
  have hct : ∀ X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i k; simp [Matrix.conjTranspose_apply]
  have hM : ∀ w, ((M w).map (starRingEnd ℂ))ᵀ * gramAt C.h v w * M w = gramAt C.h v w := by
    intro w
    have hτ := hb (e.symm w)
    rw [hct]
    by_cases hc : w.embedding = embOf (F.σ (e.symm w))
    · have hg : gramAt C.h v w = C.gr (e.symm w) := by
        simp only [gramAt, LatEmb.gr, hc]; rfl
      simp only [M, if_pos hc, hg]
      exact hτ
    · have hconj : w.embedding = ComplexEmbedding.conjugate (embOf (F.σ (e.symm w))) := by
        have h1 : InfinitePlace.mk (embOf (F.σ (e.symm w))) = InfinitePlace.mk w.embedding := by
          rw [InfinitePlace.mk_embedding]; exact hw w
        rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
        · exact absurd h.symm hc
        · exact h.symm
      have hg : gramAt C.h v w = (C.gr (e.symm w)).map (starRingEnd ℂ) := by
        ext i k
        simp only [gramAt, LatEmb.gr, Matrix.map_apply, hconj]
        rfl
      have h2 := congrArg (fun X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ => X.map (starRingEnd ℂ)) hτ
      simp only [Matrix.map_mul] at h2
      have h3 : ((b (e.symm w)).map (starRingEnd ℂ))ᴴ = ((b (e.symm w))ᴴ).map (starRingEnd ℂ) := by
        ext i k; simp [Matrix.conjTranspose_apply]
      simp only [M, if_neg hc, hg]
      rw [h3]
      exact h2
  have hH : ∀ w, IsUnit (gramAt C.h v w).det := by
    intro w
    have := (isUnit_det_gram C.h v).map w.embedding
    rw [RingHom.map_det] at this
    exact this
  let a : InfinitePlace E → GL (Fin (j + j')) ℂ := fun w =>
    Matrix.nonsingInvUnit (M w) (isUnit_det_of_unitary (starRingEnd ℂ) (hH w) (hM w))
  have ha : a ∈ C.Arch := mem_archUnitary.2 fun w => hM w
  refine ⟨⟨a, ha⟩, fun τ => ?_⟩
  have haM : ∀ w, (a w : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) = M w := fun w => rfl
  simp only [LatEmb.tm, tauMat, haM, M, he]
  by_cases hc : (plc F τ).embedding = embOf (F.σ τ)
  · simp only [if_pos hc]
  · simp only [if_neg hc]
    ext i k
    simp

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem tm_archEmbed_mulVec_vec (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ)
    (C : LatEmb F) (γ : C.h.unitaryGroup) (x : Λ) (τ : Ψ) :
    C.tm (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ) τ *ᵥ C.vec x τ =
      fun i => embOf (F.σ τ)
        (((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) i) := by
  set b := Pi.basisFun E (Fin (j + j')) with hb
  set G : GL (Fin (j + j')) E := (unitaryGroupEquivMatrix C.h b γ).1 with hG
  have hGM : (G : Matrix (Fin (j + j')) (Fin (j + j')) E) =
      LinearMap.toMatrix b b (((γ : C.h.unitaryGroup) :
        (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E)) :=
    unitaryGroupEquivMatrix_apply C.h b γ
  have hact : ∀ v : Fin (j + j') → E, (G : Matrix (Fin (j + j')) (Fin (j + j')) E) *ᵥ v =
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) v := by
    intro v
    rw [hGM, hb, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec]
    rfl
  have htm : C.tm (archEmbed C.h b γ) τ =
      (G : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) := by
    have hw : ∀ w : InfinitePlace E,
        (((archEmbed C.h b γ : archUnitary C.h b) : InfinitePlace E → GL (Fin (j + j')) ℂ) w :
          Matrix (Fin (j + j')) (Fin (j + j')) ℂ) =
        (G : Matrix (Fin (j + j')) (Fin (j + j')) E).map w.embedding := fun w => rfl
    unfold LatEmb.tm tauMat
    split_ifs with h
    · rw [hw, h]
    · rw [hw]
      rcases InfinitePlace.embedding_mk_eq (embOf (F.σ τ)) with h' | h'
      · exact absurd h' h
      · have h'' : (plc F τ).embedding = ComplexEmbedding.conjugate (embOf (F.σ τ)) := h'
        rw [h'']
        ext a c
        simp [ComplexEmbedding.conjugate_coe_eq]
  rw [htm]
  funext i
  have := RingHom.map_mulVec (embOf (F.σ τ)) (G : Matrix (Fin (j + j')) (Fin (j + j')) E) (C.e x) i
  rw [hact] at this
  rw [this]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem perExt_differentiableOn {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ}
    {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)
    (y : Ψ → Fin (j + j') → ℂ) :
    DifferentiableOn ℂ (fun t => C.perExt (F.R t) y) (ballDom F.q) := by
  have h : (fun t => C.perExt (F.R t) y) =
      fun t => ∑ k, C.bas.equivFun y k • (F.R t).P (C.lam k) := by
    funext t
    exact Module.Basis.constr_apply_fintype ℝ C.bas _ y
  rw [h]
  refine DifferentiableOn.fun_sum fun k _ => ?_
  exact (F.hol.2 (C.lam k)).const_smul (C.bas.equivFun y k)

theorem pPart_differentiableOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (y : Fin (j + j') → ℂ), DifferentiableOn ℂ (fun t => C.pPart (F.R t) τ y) (ballDom F.q) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C τ y
  classical
  unfold LatEmb.pPart
  exact ((perExt_differentiableOn C _).sub
    ((perExt_differentiableOn C _).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Boost

section Blocks

open scoped MatrixOrder

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem exists_congr_one {A : Matrix a a ℂ} (hA : A.PosDef) : ∃ X : Matrix a a ℂ, Xᴴ * A * X = 1 ∧ IsUnit X.det := by
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hs : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  obtain ⟨C, hCA⟩ : ∃ C : Matrix a a ℂ, A = Cᴴ * C :=
    ⟨CFC.sqrt A, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self A h0]⟩
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit
  have hC : IsUnit C.det := by
    rw [hCA, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  have h1 : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hC
  refine ⟨C⁻¹, ?_, ?_⟩
  · calc (C⁻¹)ᴴ * A * C⁻¹ = (C * C⁻¹)ᴴ * (C * C⁻¹) := by
          rw [hCA, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  · exact (Matrix.isUnit_nonsing_inv_det_iff).2 hC

theorem posDef_one_sub_swap {W : Matrix b a ℂ} (h : (1 - W * Wᴴ).PosDef) : (1 - Wᴴ * W).PosDef := by
  set B := 1 - W * Wᴴ with hB
  have hBu : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hP : (1 + Wᴴ * B⁻¹ * W).PosDef :=
    Matrix.PosDef.one.add_posSemidef (h.inv.posSemidef.conjTranspose_mul_mul_same W)
  have hinv : (1 + Wᴴ * B⁻¹ * W) * (1 - Wᴴ * W) = 1 := by
    have e2 : W * Wᴴ = 1 - B := by rw [hB]; abel
    have e : Wᴴ * B⁻¹ * W * (Wᴴ * W) = Wᴴ * B⁻¹ * (W * Wᴴ) * W := by simp only [Matrix.mul_assoc]
    have e3 : Wᴴ * B⁻¹ * (1 - B) * W = Wᴴ * B⁻¹ * W - Wᴴ * W := by
      have hBi' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc (Wᴴ) (B⁻¹) B, hBi', Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, e, e2, e3]
    abel
  have : (1 - Wᴴ * W) = (1 + Wᴴ * B⁻¹ * W)⁻¹ := (Matrix.inv_eq_right_inv hinv).symm
  rw [this]
  exact hP.inv

theorem exists_boost {W : Matrix b a ℂ} (h : (1 - W * Wᴴ).PosDef) :
    ∃ u : Matrix (a ⊕ b) (a ⊕ b) ℂ,
      uᴴ * fromBlocks 1 0 0 (-1) * u = fromBlocks 1 0 0 (-1) ∧ u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = W := by
  obtain ⟨X, hX, hXu⟩ := exists_congr_one (posDef_one_sub_swap h)
  obtain ⟨Y, hY, -⟩ := exists_congr_one h
  refine ⟨fromBlocks X (Wᴴ * Y) (W * X) Y, ?_, ?_⟩
  · have e11 : Xᴴ * X - Xᴴ * Wᴴ * (W * X) = 1 := by
      rw [← hX, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    have e22 : Yᴴ * W * (Wᴴ * Y) - Yᴴ * Y = -1 := by
      rw [← hY, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.neg_mul]
    congr 1
    · simp only [Matrix.mul_assoc, add_neg_cancel]
    · simp only [Matrix.mul_assoc, add_neg_cancel]
  · have : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXu
    simp only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁]
    rw [Matrix.mul_assoc, this, Matrix.mul_one]

end Blocks

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Boost

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem moebBall_transitive : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q → ∃ u : Ψ → Matrix (Sg j j') (Sg j j') ℂ, (∀ τ, IsSgU (u τ)) ∧ moebBall q u 0 = t := by
  intro Ψ _ j j' n q t ht
  have hW : ∀ τ, (1 - (ballMat q t τ)ᵀ * ((ballMat q t τ)ᵀ)ᴴ).PosDef := by
    intro τ
    have h := (ht τ).transpose
    have e : (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ = 1 - (ballMat q t τ)ᵀ * ((ballMat q t τ)ᵀ)ᴴ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
      congr 2
    rwa [e] at h
  choose u hu hm using fun τ => Boost.exists_boost (hW τ)
  refine ⟨u, hu, ?_⟩
  have h0 : ∀ τ, moebW (u τ) (ballMat q 0 τ)ᵀ = (ballMat q t τ)ᵀ := by
    intro τ
    have hz : ballMat q 0 τ = 0 := by
      ext a b
      simp [ballMat]
    rw [hz, moebW, Matrix.transpose_zero, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    exact hm τ
  funext k
  simp only [moebBall, ballPt, h0]
  simp [ballMat]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi

theorem conj_inv_mul_rt (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (s : 𝓞 E →+* ℂ) (m : ℕ)
    (hm : m ≠ 0) : ∃ ε : ℝ, ε ^ 2 = 1 ∧ embOf s (((m : E) * (H.rt : E))⁻¹) =
      Complex.I * (((1 / ((m : ℝ) * Real.sqrt H.d)) * ε : ℝ) : ℂ) := by
  have hcoe : embOf s (H.rt : E) = s H.rt := IsFractionRing.lift_algebraMap (intEmb_injective s) H.rt
  have hw : (s H.rt) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg s H.rt_sq
    simpa [map_pow, map_neg, map_natCast] using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hr0 : 0 < Real.sqrt H.d := Real.sqrt_pos.2 hd
  have hrC : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hr2 : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = (H.d : ℂ) := by
    have h := Real.sq_sqrt hd.le
    exact_mod_cast h
  have hfac : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) *
      (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) = 0 := by
    have : (s H.rt - Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) *
        (s H.rt + Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) =
        (s H.rt) ^ 2 - Complex.I ^ 2 * ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 := by ring
    rw [this, hw, hr2, Complex.I_sq]; ring
  have hval : embOf s (((m : E) * (H.rt : E))⁻¹) = ((m : ℂ) * s H.rt)⁻¹ := by
    rw [map_inv₀, map_mul, map_natCast, hcoe]
  rcases mul_eq_zero.1 hfac with h | h
  · refine ⟨-1, by norm_num, ?_⟩
    have hw' : s H.rt = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) := sub_eq_zero.1 h
    rw [hval, hw']
    push_cast
    field_simp
    rw [Complex.I_sq]
    norm_num
  · refine ⟨1, by norm_num, ?_⟩
    have hw' : s H.rt = -(Complex.I * ((Real.sqrt H.d : ℝ) : ℂ)) := eq_neg_of_add_eq_zero_left h
    rw [hval, hw']
    push_cast
    field_simp
    rw [Complex.I_sq]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi
end
end

section

open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M

theorem _root_.GlobalTheory.T.tail_log_bound_local_integrable : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (Φ : Fin e → LocPot X) (CE : ℝ), (∀ i, IsPotential A (Φ i)) → (∀ x ∈ Yo, 1 ≤ r x) → (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A Φ j y) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A Yo r Φ CE → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)), S ⊆ (A.chart j).target → IsCompact S → ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ → IntegrableOn (fun y => (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y) S ∧ ∫ y in S, (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y ≤ CE * Real.log R₀ ^ (e + 1) / R₀ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart | exact GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart | (intros; apply GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.uniform_energy_bound_of_section : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (C₁ : ℝ), (∀ i, IsPotential A (Θ i)) → (∀ i, IsPosPot A (Θ i)) → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → 0 ≤ C₁ → ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (u : Fin e → X → ℝ) (T : Fin e → LocPot X), (∀ i, A.Smooth (u i)) → (∀ i, IsPsh A (Θ i + LocPot.ofFun (u i))) → (∀ i, ∀ y ∉ bdry s, -C₁ * Real.log (rW L s y) ≤ u i y ∧ u i y ≤ 0) → (∀ i x y, (T i).φ x y = (Θ i).φ x y + u i y) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A (bdry s)ᶜ (rW L s) T CE := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tailLogBound_of_tailBound | exact GlobalTheory.CompanionTheory.Ar.Giv.tailLogBound_of_tailBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tailLogBound_of_tailBound <;> assumption)
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.normalized_degree_full_rank_sublattice : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds | exact GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds | (intros; apply GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)


theorem _root_.GlobalTheory.T.integrable_domCell_logNorm_chart : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff

theorem _root_.GlobalTheory.T.bounded_psh_correction_locally_smooth : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.smoothOn_of_chart_levi_nonneg : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (th : LocPot X) (x₀ : X) (j : Fin B.n) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → ℝ), A.Compatible B → IsPotential A th → (B.chart j).source ⊆ th.U x₀ → IsOpen V → V ⊆ (B.chart j).target → ContDiffOn ℝ ∞ g V → (∀ z ∈ V, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z' => th.φ x₀ ((B.chart j).symm z') + g z') z w) → A.SmoothOn ((B.chart j).source ∩ B.chart j ⁻¹' V) (g ∘ B.chart j) ∧ IsPshOn A ((B.chart j).source ∩ B.chart j ⁻¹' V) (th + LocPot.ofFun (g ∘ B.chart j)) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack | exact GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack | (intros; apply GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack <;> assumption)
end
