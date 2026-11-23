module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.AdmLift

theorem exists_admissible_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
  ∀ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z, π₁ (cA σ z) = π₂ z) → (∀ z, π₂ (cA σ z) = π₁ z) → (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  S.map (fun x => (x : Fv F v)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∀ X₁ X₂ : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), X₁ᵀ * S + S * X₂ = 0 →
  ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
    Y.map π₁ = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) * X₁.map (fun x => (x : Fv F v)) * ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Y.map π₂ = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) * X₂.map (fun x => (x : Fv F v)) * ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 := by
  intro F E _ _ _ _ _ σ d W v hskew π₁ π₂ b₁ b₂ h12 h21 inj surj S hS X₁ X₂ hX

  let c : v.adicCompletionIntegers F →+* Fv F v := (v.adicCompletionIntegers F).toSubring.subtype
  have hc : ∀ A : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), A.map (fun x => (x : Fv F v)) = A.map c := fun _ => rfl
  set B₁ : Matrix (Fin d) (Fin d) (Fv F v) := (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) with hB₁
  set B₂ : Matrix (Fin d) (Fin d) (Fv F v) := (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) with hB₂
  set C₁ : Matrix (Fin d) (Fin d) (Fv F v) := ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hC₁
  set C₂ : Matrix (Fin d) (Fin d) (Fv F v) := ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hC₂
  have hBC₂ : B₂ * C₂ = 1 := b₂.mul_inv
  have hCB₁ : C₁ᵀ * B₁ᵀ = 1 := by rw [← Matrix.transpose_mul, show B₁ * C₁ = 1 from b₁.mul_inv, Matrix.transpose_one]
  set J₁ : Matrix (Fin d) (Fin d) (Fv F v) := (incM F W.J).map π₁ with hJ₁
  set M₁ : Matrix (Fin d) (Fin d) (Fv F v) := B₁ * X₁.map (fun x => (x : Fv F v)) * C₁ with hM₁
  set M₂ : Matrix (Fin d) (Fin d) (Fv F v) := B₂ * X₂.map (fun x => (x : Fv F v)) * C₂ with hM₂

  have hX' : (X₁.map c)ᵀ * S.map c + S.map c * X₂.map c = 0 := by
    have := congrArg (fun A => A.map c) hX
    simpa [Matrix.map_add (f := _), Matrix.map_mul, Matrix.transpose_map] using this
  rw [hc] at hS
  have key₁ : M₁ᵀ * J₁ + J₁ * M₂ = 0 := by
    have e : M₁ᵀ * J₁ + J₁ * M₂ = C₁ᵀ * ((X₁.map c)ᵀ * S.map c + S.map c * X₂.map c) * C₂ := by
      rw [hS, hM₁, hM₂, hc, hc]
      simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      congr 1
      · rw [hBC₂, Matrix.mul_one]
      · rw [← Matrix.mul_assoc C₁ᵀ, hCB₁, Matrix.one_mul]
    rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

  have hJ₂ : (incM F W.J).map π₂ = -J₁ᵀ := by
    ext i j
    have h1 : cA σ (inclR (F := F) (AF F) (W.J i j)) = inclR (F := F) (AF F) (σ (W.J i j)) := by simp [cA, inclR]
    simp only [incM, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, hJ₁]
    rw [← h12, h1, hskew j i, map_neg, map_neg]
  have key₂ : M₂ᵀ * (-J₁ᵀ) + (-J₁ᵀ) * M₁ = 0 := by
    have gen : ∀ A B K : Matrix (Fin d) (Fin d) (Fv F v), Bᵀ * (-Kᵀ) + (-Kᵀ) * A = -(Aᵀ * K + K * B)ᵀ := by
      intro A B K
      rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, neg_add,
        Matrix.mul_neg, Matrix.neg_mul, add_comm]
    rw [gen, key₁, Matrix.transpose_zero, neg_zero]

  choose z hzA hz1 hz2 using surj
  let Y : Matrix (Fin d) (Fin d) (AE F E) := Matrix.of fun i j => z (M₁ i j) (M₂ i j)
  have hY1 : Y.map π₁ = M₁ := by ext i j; simp [Y, hz1]
  have hY2 : Y.map π₂ = M₂ := by ext i j; simp [Y, hz2]
  have hAtE : ∀ i j, At (evFin F v) (Y i j) := fun i j => hzA _ _
  have atMulR : ∀ a b : AE F E, At (evFin F v) a → At (evFin F v) (a * b) := fun a b ha u hu => by
    rw [← smul_mul_assoc, ha u hu, zero_mul]
  have atMulL : ∀ a b : AE F E, At (evFin F v) b → At (evFin F v) (a * b) := fun a b hb u hu => by
    rw [← mul_smul_comm, hb u hu, mul_zero]
  have atCA : ∀ a : AE F E, At (evFin F v) a → At (evFin F v) (cA σ a) := fun a ha u hu => by
    rw [← map_smul, ha u hu, map_zero]
  have atSum : ∀ f : Fin d → AE F E, (∀ k, At (evFin F v) (f k)) → At (evFin F v) (∑ k, f k) := fun f hf u hu => by
    rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun k _ => hf k u hu
  have atAdd : ∀ a b : AE F E, At (evFin F v) a → At (evFin F v) b → At (evFin F v) (a + b) := fun a b ha hb u hu => by
    rw [smul_add, ha u hu, hb u hu, add_zero]
  refine ⟨Y, ?_, hY1, hY2, ?_⟩
  · intro u hu
    ext i j
    rw [Matrix.smul_apply, Matrix.zero_apply]
    exact hAtE i j u hu
  · set Q := Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) with hQ
    have hcomp₁ : (Y.map (cA σ)).map π₁ = M₂ := by
      rw [← hY2]; ext i j; simp [h12]
    have hcomp₂ : (Y.map (cA σ)).map π₂ = M₁ := by
      rw [← hY1]; ext i j; simp [h21]
    have hQ1 : Q.map π₁ = 0 := by
      rw [hQ, Matrix.map_add (f := _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hY1, hcomp₁, ← hJ₁, key₁]
      exact fun a b => map_add π₁ a b
    have hQ2 : Q.map π₂ = 0 := by
      rw [hQ, Matrix.map_add (f := _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hY2, hcomp₂, hJ₂, key₂]
      exact fun a b => map_add π₂ a b
    ext i j
    apply inj
    · simp only [hQ, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      exact atAdd _ _ (atSum _ fun k => atMulR _ _ (hAtE k i)) (atSum _ fun k => atMulL _ _ (atCA _ (hAtE k j)))
    · have := congrFun (congrFun hQ1 i) j
      simpa using this
    · have := congrFun (congrFun hQ2 i) j
      simpa using this

end GlobalTheory.AdmLift

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CMSkewUnit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cm_sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cm_exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)
  by_contra hne
  push_neg at hne
  apply hc
  ext x
  have hx := h.2.2.2 w.embedding x
  rw [hne x] at hx
  simpa [ComplexEmbedding.conjugate_coe_eq] using hx.symm

theorem cm_exists_skew (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨x, hx⟩ := cm_exists_moved σ h
  refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  rw [map_sub, cm_sigma_sigma σ h]; ring

end GlobalTheory.CMSkewUnit

namespace GlobalTheory.CMSkewUnit

theorem exists_unit_of_val_eq_one {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {x : Fv F v} (hx : Valued.v x = 1) :
    ∃ u : (v.adicCompletionIntegers F)ˣ, ((u : v.adicCompletionIntegers F) : Fv F v) = x := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hx; exact zero_ne_one hx
  have hmem : x ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_eq hx)
  have hmem' : x⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hx, inv_one])
  refine ⟨⟨⟨x, hmem⟩, ⟨x⁻¹, hmem'⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

end GlobalTheory.CMSkewUnit

namespace GlobalTheory.CMSkewUnit

theorem exists_skew_unit_at : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (π : AE F E →+* Fv F v),
    (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
    ∃ δ : E, σ δ = -δ ∧ ∃ u : (v.adicCompletionIntegers F)ˣ,
      ((u : v.adicCompletionIntegers F) : Fv F v) = π (inclR (F := F) (AF F) δ) := by
  intro F E _ _ _ _ _ σ h v π hπ
  obtain ⟨δ₀, h0, hs⟩ := cm_exists_skew σ h
  have ht : π (inclR (F := F) (AF F) δ₀) ≠ 0 :=
    (map_ne_zero_iff (π.comp (inclR (F := F) (AF F))) (RingHom.injective _)).2 h0
  have hF : ∀ f : F, π (inclR (F := F) (AF F) (algebraMap F E f)) = algebraMap F (Fv F v) f := by
    intro f
    have e1 : inclR (F := F) (AF F) (algebraMap F E f) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) f) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes f
    rw [e1, hπ, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  set t := π (inclR (F := F) (AF F) δ₀) with ht_def
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  refine ⟨algebraMap F E (ϖ ^ WithZero.log (Valued.v t)) * δ₀, ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes, hs]; ring
  · apply exists_unit_of_val_eq_one
    rw [map_mul, map_mul, hF, ← ht_def, map_mul]
    have e2 : Valued.v (algebraMap F (Fv F v) (ϖ ^ WithZero.log (Valued.v t))) =
        v.valuation F (ϖ ^ WithZero.log (Valued.v t)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [e2, map_zpow₀, hϖ]
    conv_lhs => rw [← WithZero.exp_log hvt]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp

end GlobalTheory.CMSkewUnit
end
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

namespace GlobalTheory.HeisDerivZero

theorem evI_surj {F : Type} [Field F] [NumberField F] (y : mixedEmbedding.mixedSpace F) : ∃ a : AF F, evI F a = y :=
  ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0), (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y⟩

theorem actsD_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hA : ActsD (evI F) (M.heisLine ψ u) g h) (hc : g = 0 ∨ IsEmpty (Fin n × Fin d)) : h = 0 := by
  have hR : Rest (evI F) g (fun _ => 1) := by
    refine ⟨fun _ _ _ => rfl, ?_⟩
    rcases hc with rfl | hE
    · have : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) (fun _ => 1) = 0 := by
        funext x; simp [tens]
      rw [this]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨g, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, rfl⟩
      exact HasCompactSupport.of_compactSpace _
  have hconst : ∀ t x, M.heisLine ψ u t (tens (evI F) g fun _ => 1) x = tens (evI F) g (fun _ => 1) x := by
    intro t x
    rcases hc with rfl | hE
    · simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, tens]
    · simp only [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, dotProduct, Finset.univ_eq_empty,
        Finset.sum_empty, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      congr 1
      exact Subsingleton.elim _ _
  ext y
  choose x hx using fun i => evI_surj (F := F) (y i)
  have h1 := hA _ hR x
  simp only [hconst] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  simpa [tens, hx] using h2

end GlobalTheory.HeisDerivZero
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem integralBlocks_leftInverse_isUnit_det : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b : GL (Fin d) (Fv F v))
  (g h : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), h * g = 1 →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  ∃ G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F), G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) ∧ IsUnit G.det := by
  intro F E _ _ _ _ _ d v π b g h hhg g11 g12 g21 g22 h11 h12 h21 h22
  classical
  set Bi : Matrix (Fin d) (Fin d) (Fv F v) := ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hBi
  set Bm : Matrix (Fin d) (Fin d) (Fv F v) := (b : Matrix (Fin d) (Fin d) (Fv F v)) with hBm
  have hbb : Bm * Bi = 1 := by
    simp only [hBi, hBm]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hbb' : Bi * Bm = 1 := by
    simp only [hBi, hBm]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ x : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Matrix.fromBlocks (Bi * x.toBlocks₁₁.map π * Bm) (Bi * x.toBlocks₁₂.map π * Bm)
        (Bi * x.toBlocks₂₁.map π * Bm) (Bi * x.toBlocks₂₂.map π * Bm)
      = Matrix.fromBlocks Bi 0 0 Bi * x.map π * Matrix.fromBlocks Bm 0 0 Bm := by
    intro x
    have hx : x.map π = Matrix.fromBlocks (x.toBlocks₁₁.map π) (x.toBlocks₁₂.map π)
        (x.toBlocks₂₁.map π) (x.toBlocks₂₂.map π) := by
      rw [← Matrix.fromBlocks_map, Matrix.fromBlocks_toBlocks]
    rw [hx, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hprod : (Matrix.fromBlocks Bi 0 0 Bi * h.map π * Matrix.fromBlocks Bm 0 0 Bm) *
      (Matrix.fromBlocks Bi 0 0 Bi * g.map π * Matrix.fromBlocks Bm 0 0 Bm) = 1 := by
    have hBB : Matrix.fromBlocks Bm 0 0 Bm * Matrix.fromBlocks Bi 0 0 Bi = (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) := by
      rw [Matrix.fromBlocks_multiply]; simp [hbb]
    have hBB' : Matrix.fromBlocks Bi 0 0 Bi * Matrix.fromBlocks Bm 0 0 Bm = (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) := by
      rw [Matrix.fromBlocks_multiply]; simp [hbb']
    have hhg' : h.map π * g.map π = 1 := by
      rw [← Matrix.map_mul, hhg, Matrix.map_one _ (map_zero π) (map_one π)]
    calc (Matrix.fromBlocks Bi 0 0 Bi * h.map π * Matrix.fromBlocks Bm 0 0 Bm) *
          (Matrix.fromBlocks Bi 0 0 Bi * g.map π * Matrix.fromBlocks Bm 0 0 Bm)
        = Matrix.fromBlocks Bi 0 0 Bi * h.map π * (Matrix.fromBlocks Bm 0 0 Bm *
          Matrix.fromBlocks Bi 0 0 Bi) * g.map π * Matrix.fromBlocks Bm 0 0 Bm := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hBB, Matrix.mul_one, Matrix.mul_assoc (Matrix.fromBlocks Bi 0 0 Bi), hhg', Matrix.mul_one, hBB']

  let G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F) := fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => ⟨_, g11 i j⟩
    | Sum.inl i, Sum.inr j => ⟨_, g12 i j⟩
    | Sum.inr i, Sum.inl j => ⟨_, g21 i j⟩
    | Sum.inr i, Sum.inr j => ⟨_, g22 i j⟩
  let H : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F) := fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => ⟨_, h11 i j⟩
    | Sum.inl i, Sum.inr j => ⟨_, h12 i j⟩
    | Sum.inr i, Sum.inl j => ⟨_, h21 i j⟩
    | Sum.inr i, Sum.inr j => ⟨_, h22 i j⟩
  have hG : G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (Bi * g.toBlocks₁₁.map π * Bm) (Bi * g.toBlocks₁₂.map π * Bm)
        (Bi * g.toBlocks₂₁.map π * Bm) (Bi * g.toBlocks₂₂.map π * Bm) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
  have hH : H.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (Bi * h.toBlocks₁₁.map π * Bm) (Bi * h.toBlocks₁₂.map π * Bm)
        (Bi * h.toBlocks₂₁.map π * Bm) (Bi * h.toBlocks₂₂.map π * Bm) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
  refine ⟨G, hG, ?_⟩
  apply Matrix.isUnit_det_of_left_inverse (B := H)
  have hmap : (H * G).map (v.adicCompletionIntegers F).subtype = 1 := by
    rw [Matrix.map_mul]
    change H.map (fun x => (x : Fv F v)) * G.map (fun x => (x : Fv F v)) = 1
    rw [hG, hH, key, key, hprod]
  refine Matrix.ext fun i j => Subtype.coe_injective ?_
  have := congrFun (congrFun hmap i) j
  rw [Matrix.map_apply] at this
  change (v.adicCompletionIntegers F).subtype ((H * G) i j) = (v.adicCompletionIntegers F).subtype ((1 : Matrix _ _ _) i j)
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchSlice

theorem exists_schwartz_slice : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g 0 • f, fun t => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, pureA, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  | zero => exact ⟨0, fun t => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁⟩ := hx
    obtain ⟨g₂, h₂⟩ := hy
    exact ⟨g₁ + g₂, fun t => by rw [SchwartzMap.add_apply, h₁, h₂]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨g₁, h₁⟩ := hx
    exact ⟨c • g₁, fun t => by rw [SchwartzMap.smul_apply, h₁]; rfl⟩

end GlobalTheory.ArchSlice
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.Twist

theorem halfBlockSum_inv_conj_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π : AE F E →+* Fv F v) (b : GL (Fin d) (Fv F v)),
  (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
  ∀ (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F)),
  G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) →
  ∀ X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  IsUnit (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ +
    X * (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)).det →
  ∀ Y : Matrix (Fin d) (Fin d) (AE F E), Y.map π = (b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) * ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∃ N : Matrix (Fin d) (Fin d) (Fv F v), N * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))).map π = 1 ∧ (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * N * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ d v π b hπ g G hG X hdet Y hY
  set B : Matrix (Fin d) (Fin d) (Fv F v) := (b : Matrix (Fin d) (Fin d) (Fv F v)) with hB
  set Bi : Matrix (Fin d) (Fin d) (Fv F v) := ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hBi
  have hBBi : B * Bi = 1 := Units.mul_inv b
  have hBiB : Bi * B = 1 := Units.inv_mul b
  let φ : v.adicCompletionIntegers F →+* Fv F v := (v.adicCompletionIntegers F).subtype
  have conj : ∀ M : Matrix (Fin d) (Fin d) (Fv F v), B * (Bi * M * B) * Bi = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBBi, Matrix.one_mul, Matrix.mul_assoc, hBBi,
      Matrix.mul_one]
  have hGφ : G.map (fun x => (x : Fv F v)) = G.map φ := rfl
  rw [hGφ] at hG
  have h11 : g.toBlocks₁₁.map π = B * G.toBlocks₁₁.map φ * Bi := by
    have := congrArg Matrix.toBlocks₁₁ hG
    rw [Matrix.toBlocks_fromBlocks₁₁] at this
    have e : (G.map φ).toBlocks₁₁ = G.toBlocks₁₁.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h12 : g.toBlocks₁₂.map π = B * G.toBlocks₁₂.map φ * Bi := by
    have := congrArg Matrix.toBlocks₁₂ hG
    rw [Matrix.toBlocks_fromBlocks₁₂] at this
    have e : (G.map φ).toBlocks₁₂ = G.toBlocks₁₂.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h21 : g.toBlocks₂₁.map π = B * G.toBlocks₂₁.map φ * Bi := by
    have := congrArg Matrix.toBlocks₂₁ hG
    rw [Matrix.toBlocks_fromBlocks₂₁] at this
    have e : (G.map φ).toBlocks₂₁ = G.toBlocks₂₁.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h22 : g.toBlocks₂₂.map π = B * G.toBlocks₂₂.map φ * Bi := by
    have := congrArg Matrix.toBlocks₂₂ hG
    rw [Matrix.toBlocks_fromBlocks₂₂] at this
    have e : (G.map φ).toBlocks₂₂ = G.toBlocks₂₂.map φ := rfl
    rw [e] at this; rw [this, conj]
  have hYφ : Y.map π = B * X.map φ * Bi := hY
  set c : Fv F v := π (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) with hc
  have hc2 : (2 : Fv F v) * c = 1 := by
    rw [hc, hπ, ← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  have hsm : ∀ M : Matrix (Fin d) (Fin d) (AE F E), (⅟(2 : AF F) • M).map π = c • M.map π := by
    intro M; ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, map_mul, Matrix.smul_apply, Matrix.map_apply, hc, smul_eq_mul]
  have aπ : ∀ M N : Matrix (Fin d) (Fin d) (AE F E), (M + N).map π = M.map π + N.map π :=
    fun M N => Matrix.map_add π (map_add π) M N
  have sπ : ∀ M N : Matrix (Fin d) (Fin d) (AE F E), (M - N).map π = M.map π - N.map π :=
    fun M N => Matrix.map_sub π (map_sub π) M N
  have aφ : ∀ M N : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), (M + N).map φ = M.map φ + N.map φ :=
    fun M N => Matrix.map_add φ (map_add φ) M N
  have sφ : ∀ M N : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), (M - N).map φ = M.map φ - N.map φ :=
    fun M N => Matrix.map_sub φ (map_sub φ) M N
  set s := G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ with hs
  set t := G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂ with ht
  set P := s + X * t with hP
  have hSπ : (g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂).map π = B * s.map φ * Bi := by
    simp only [aπ, aφ, h11, h12, h21, h22, hs, Matrix.mul_add, Matrix.add_mul]
  have hTπ : (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂).map π = B * t.map φ * Bi := by
    simp only [aπ, sπ, aφ, sφ, h11, h12, h21, h22, ht, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul]
  have hK : (⅟(2 : AF F) • (g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂) +
      Y * (⅟(2 : AF F) • (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂))).map π
      = c • (B * P.map φ * Bi) := by
    rw [aπ, Matrix.map_mul, hsm, hsm, hSπ, hTπ, hYφ, hP, aφ s (X * t), Matrix.map_mul (f := φ) (M := t) (L := X)]
    rw [Matrix.mul_smul, ← smul_add]
    congr 1
    have : B * X.map φ * Bi * (B * t.map φ * Bi) = B * (X.map φ * t.map φ) * Bi := by
      calc B * X.map φ * Bi * (B * t.map φ * Bi) = B * X.map φ * (Bi * B) * t.map φ * Bi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBiB, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, ← Matrix.add_mul, ← Matrix.mul_add]
  refine ⟨(2 : Fv F v) • (B * (P⁻¹).map φ * Bi), ?_, ?_⟩
  · rw [hK, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc2, one_smul]
    have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    calc B * (P⁻¹).map φ * Bi * (B * P.map φ * Bi) = B * ((P⁻¹).map φ * (Bi * B) * P.map φ) * Bi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hBiB, Matrix.mul_one, ← Matrix.map_mul, hPinv, Matrix.map_one _ (map_zero φ) (map_one φ),
            Matrix.mul_one, hBBi]
  · intro i j
    have : Bi * ((2 : Fv F v) • (B * (P⁻¹).map φ * Bi)) * B = (2 : Fv F v) • (P⁻¹).map φ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc Bi * (B * (P⁻¹).map φ * Bi) * B = (Bi * B) * (P⁻¹).map φ * (Bi * B) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBiB, Matrix.one_mul, Matrix.mul_one]
    rw [this, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    have e : (2 : Fv F v) * φ (P⁻¹ i j) = φ (2 * P⁻¹ i j) := by rw [map_mul, map_ofNat]
    rw [e]
    exact (2 * P⁻¹ i j).2

end GlobalTheory.Twist
end
