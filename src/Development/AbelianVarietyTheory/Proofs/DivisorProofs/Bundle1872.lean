module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalToGlobal.Columns.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffOneRealOfIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BlockHeight

open scoped NNReal
open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation Formalism.UG

section Generic

variable {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem htOf_blk_le {R : Type} [CommRing R] {N₁ : Matrix (Fin p) (Fin p) R → ℝ≥0} {N₂ : Matrix (Fin q) (Fin q) R → ℝ≥0}
    {N : Matrix (Fin d) (Fin d) R → ℝ≥0} (hN : ∀ a b, N (blk e a b) ≤ max (N₁ a) (N₂ b))
    (X : GL (Fin d) R) (x : GL (Fin p) R) (y : GL (Fin q) R)
    (h1 : (X : Matrix (Fin d) (Fin d) R) = blk e (x : Matrix (Fin p) (Fin p) R) (y : Matrix (Fin q) (Fin q) R))
    (h2 : ((X⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R) =
      blk e ((x⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) ((y⁻¹ : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) :
    htOf N X ≤ htOf N₁ x * htOf N₂ y := by
  have hx := one_le_htOf N₁ x
  have hy := one_le_htOf N₂ y
  refine max_le (one_le_mul_of_one_le_of_one_le hx hy) (max_le ?_ ?_)
  · rw [h1]
    refine (hN _ _).trans (max_le ?_ ?_)
    · exact (le_htOf N₁ x).trans (le_mul_of_one_le_right' hy)
    · exact (le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)
  · rw [h2]
    refine (hN _ _).trans (max_le ?_ ?_)
    · exact (inv_le_htOf N₁ x).trans (le_mul_of_one_le_right' hy)
    · exact (inv_le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)

theorem bc_val_blk {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : GL (Fin d) R} {x : GL (Fin p) R}
    {y : GL (Fin q) R}
    (h1 : (X : Matrix (Fin d) (Fin d) R) = blk e (x : Matrix (Fin p) (Fin p) R) (y : Matrix (Fin q) (Fin q) R)) :
    ((bc φ X : GL (Fin d) R') : Matrix (Fin d) (Fin d) R') =
      blk e ((bc φ x : GL (Fin p) R') : Matrix (Fin p) (Fin p) R') ((bc φ y : GL (Fin q) R') : Matrix (Fin q) (Fin q) R') := by
  show (X : Matrix (Fin d) (Fin d) R).map φ = _
  rw [h1, blk_map _ _ _ (map_zero φ)]
  rfl

theorem bc_inv_blk {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : GL (Fin d) R} {x : GL (Fin p) R}
    {y : GL (Fin q) R}
    (h2 : ((X⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R) =
      blk e ((x⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) ((y⁻¹ : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) :
    (((bc φ X)⁻¹ : GL (Fin d) R') : Matrix (Fin d) (Fin d) R') =
      blk e (((bc φ x)⁻¹ : GL (Fin p) R') : Matrix (Fin p) (Fin p) R')
        (((bc φ y)⁻¹ : GL (Fin q) R') : Matrix (Fin q) (Fin q) R') := by
  simp only [← map_inv]
  exact bc_val_blk e φ h2

theorem opNorm_blk_le (a : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin q) (Fin q) ℂ) :
    opNorm (blk e a b) ≤ max (opNorm a) (opNorm b) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  obtain ⟨v, rfl⟩ : ∃ v : Fin d → ℂ, x = WithLp.toLp 2 v := ⟨x.ofLp, rfl⟩
  set c : ℝ := ((max (opNorm a) (opNorm b) : ℝ≥0) : ℝ) with hcdef
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have ha : ‖(WithLp.toLp 2 (a *ᵥ fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ≤
      c * ‖(WithLp.toLp 2 (fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ((opNorm a : ℝ≥0) : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast le_max_left _ _
    exact this
  have hb : ‖(WithLp.toLp 2 (b *ᵥ fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ≤
      c * ‖(WithLp.toLp 2 (fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ((opNorm b : ℝ≥0) : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast le_max_right _ _
    exact this
  have key : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (blk e a b) (WithLp.toLp 2 v)‖ ^ 2 =
      ‖(WithLp.toLp 2 (a *ᵥ fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ^ 2 +
      ‖(WithLp.toLp 2 (b *ᵥ fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ^ 2 := by
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← e.sum_comp, Fintype.sum_sum_type]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, mulVec, dotProduct, ← e.sum_comp, Fintype.sum_sum_type]
  have knorm : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ ^ 2 =
      ‖(WithLp.toLp 2 (fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ^ 2 +
      ‖(WithLp.toLp 2 (fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ← e.sum_comp,
      Fintype.sum_sum_type]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).1 ?_
  rw [key, mul_pow, knorm, mul_add, ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2) (pow_le_pow_left₀ (norm_nonneg _) hb 2)

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem normFin_blk_le (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (a : Matrix (Fin p) (Fin p) (Fv F v ⊗[F] E)) (b : Matrix (Fin q) (Fin q) (Fv F v ⊗[F] E)) :
    normFin F v (blk e a b) ≤ max (normFin F v a) (normFin F v b) := by
  refine (normFin_le_iff F v).2 fun i j => ?_
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_apply]
  rcases e.symm i with i | i <;> rcases e.symm j with j | j
  · rw [fromBlocks_apply₁₁]; exact (absFin_le_normFin F v a i j).trans (le_max_left _ _)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₂]; exact (absFin_le_normFin F v b i j).trans (le_max_right _ _)

theorem normInf_blk_le (w : InfinitePlace F) (a : Matrix (Fin p) (Fin p) (w.Completion ⊗[F] E))
    (b : Matrix (Fin q) (Fin q) (w.Completion ⊗[F] E)) :
    normInf F w (blk e a b) ≤ max (normInf F w a) (normInf F w b) :=
  (normInf_le_iff F w).2 fun τ => by
    rw [blk_map _ _ _ (map_zero (infEmb τ))]
    exact (opNorm_blk_le e _ _).trans
      (max_le_max ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem heightGL_blk_le (X : GL (Fin d) (AF F ⊗[F] E)) (x : GL (Fin p) (AF F ⊗[F] E)) (y : GL (Fin q) (AF F ⊗[F] E))
    (h1 : (X : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) =
      blk e (x : Matrix (Fin p) (Fin p) (AF F ⊗[F] E)) (y : Matrix (Fin q) (Fin q) (AF F ⊗[F] E)))
    (h2 : ((X⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) =
      blk e ((x⁻¹ : GL (Fin p) (AF F ⊗[F] E)) : Matrix (Fin p) (Fin p) (AF F ⊗[F] E))
        ((y⁻¹ : GL (Fin q) (AF F ⊗[F] E)) : Matrix (Fin q) (Fin q) (AF F ⊗[F] E))) :
    heightGL F X ≤ heightGL F x * heightGL F y := by
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (finite_mulSupport_htFin F x) (finite_mulSupport_htFin F y)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) ?_ fun v => ?_)
  · exact htOf_blk_le e (normInf_blk_le F e w) _ _ _ (bc_val_blk e _ h1) (bc_inv_blk e _ h2)
  · exact ((finite_mulSupport_htFin F x).union (finite_mulSupport_htFin F y)).subset (Function.mulSupport_mul _ _)
  · exact htOf_blk_le e (normFin_blk_le F e v) _ _ _ (bc_val_blk e _ h1) (bc_inv_blk e _ h2)

theorem ht_blkU_le : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A) (g₁ : GA D B),
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)) : ℝ) ≤ GlobalTheory.Grow.height A g * GlobalTheory.Grow.height B g₁ := by
  intro D A B d e J hJ g g₁
  have h := heightGL_blk_le D.host.F e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)).1 (Formalism.L2.Theta.matHom A g)
    (Formalism.L2.Theta.matHom B g₁) rfl (by
      show blk e (Formalism.L2.Theta.mt A g⁻¹) (Formalism.L2.Theta.mt B g₁⁻¹) = _
      simp only [Formalism.L2.Theta.mt, map_inv])
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ ((heightGL D.host.F _ : ℝ≥0) : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.BlockHeight

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.TripleSpace

theorem hasSig_neg_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (-M) q p := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨?_, ?_⟩
  · have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  · let Q : Matrix (Fin n) (Fin q ⊕ Fin p) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e Sum.swap
    refine ⟨Q.map star, ?_⟩
    have hQ : (Q.map star)ᵀ = Qᴴ := rfl
    have hQ2 : (Q.map star).map star = Q := by ext a b; simp
    rw [hQ, hQ2, Matrix.mul_neg, Matrix.neg_mul]
    have key : Qᴴ * M * Q = ((Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) *
        Matrix.reindex e e M * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).submatrix Sum.swap Sum.swap := by
      have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
          (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by ext a b; rfl
      have hM : M = (Matrix.reindex e e M).submatrix e e := by ext a b; simp
      have hQh : Qᴴ = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ.submatrix Sum.swap e := by
        simp only [Q, Matrix.conjTranspose_submatrix]
      rw [hc, hQh, hM, ← Matrix.submatrix_mul _ _ _ e _ e.bijective, Matrix.reindex_apply,
        Matrix.submatrix_submatrix]
      simp only [Q]
      rw [← Matrix.submatrix_mul _ _ _ e _ e.bijective]
      simp [Matrix.reindex_apply]
    rw [key, hP]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply]


open Formalism.IndefR.Datum in
theorem isCartan_neg_conj {n : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (-(G.map star)) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsG : sᴴ * G = G * s := by
    calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
    _ = (sᴴ * G * s) * s := by simp only [Matrix.mul_assoc]
    _ = G * s := by rw [h2]
  have e2 : sᵀ * G.map star * s.map star = G.map star := by
    have := congrArg (fun X => X.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    have a1 : sᴴ.map (starRingEnd ℂ) = sᵀ := by ext a b; simp [Matrix.conjTranspose_apply]
    have a2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = M.map star := fun M => rfl
    rw [a1, a2, a2] at this
    exact this
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · have e1 : (-s).map star = -(s.map star) := by ext a b; simp
    rw [e1, Matrix.transpose_neg]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, e2]
  · intro x hx
    have hz := h3.dotProduct_mulVec_pos hx
    have hGs : (G.map star) *ᵥ star x = star (G *ᵥ x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum]
    have key : ((-s) *ᵥ x) ⬝ᵥ ((-(G.map star)) *ᵥ star x) = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
      rw [Matrix.neg_mulVec, Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg, hGs,
        ← star_star (s *ᵥ x), star_dotProduct_star]
      congr 1
      rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hsG]
    rw [key, Complex.star_def, Complex.conj_re]
    exact (Complex.pos_iff.1 hz).1

theorem star_gram {D : D7} (V : HSp D) (a b : Fin V.rank) : star (V.gram a b) = V.gram b a :=
  V.herm.eq (V.frame a) (V.frame b)

theorem form_neg_eq {D : D7} (V : HSp D) (y x : Fin V.rank → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) y x =
      -star (∑ i, ∑ j, star ((star x) i) * V.gram i j * (star y) j) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Matrix.smul_apply, star_sum, Pi.star_apply,
    star_star, star_mul', star_gram, Finset.mul_sum, smul_eq_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show y b * (-1 * V.gram b a * star (x a)) = -(star (x a) * V.gram b a * y b)
  ring

theorem mem_starLat_iff_form {D : D7} (V : HSp D) {Λ₀ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hsd : IsSelfDualC V Λ₀) (y : Fin V.rank → D.host.E) :
    y ∈ Formalism.L2.Col.starLat D.host.E Λ₀ ↔ ∀ x ∈ Formalism.L2.Col.starLat D.host.E Λ₀,
      IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) y x) := by
  rw [Formalism.L2.Col.mem_starLat, hsd.2]
  constructor
  · intro H x hx
    obtain ⟨b, hb⟩ := H (star x) hx
    rw [form_neg_eq, ← hb]
    exact ((RingOfIntegers.isIntegral_coe b).map (starRingEnd D.host.E).toIntAlgHom).neg
  · intro H x hx
    have h := H (star x) (by rw [Formalism.L2.Col.mem_starLat, star_star]; exact hx)
    rw [form_neg_eq, star_star] at h
    have h2 := h.neg.map (starRingEnd D.host.E).toIntAlgHom
    rw [neg_neg] at h2
    exact ⟨⟨_, h2⟩, star_star (R := D.host.E) _⟩

theorem negConj_isHerm : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin (spW₁ G i j).rank → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)),
      Spc.IsHerm D.sp.cm.sig B
        (Spc.mk ((-1 : D.host.E) • (spW₁ G i j).gram) Λ (fun w => -W.cart (.grid (i : ℕ) (j : ℕ)) (τf w)) bas)
        ((D.R.m - j) / 2) ((spW₁ G i j).rank - (D.R.m - j) / 2) := by
  intro D T L sc G μ₀ hL W i j B τf hB
  have hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ)) := ⟨i.2.le, j.2.le⟩
  have hV := node_isV G hL hR
  have hsd : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) := hV.sd
  have hlat : Submodule.IsFullLattice D.host.E (Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ)))) := by
    let N := G.Λ (.grid (i : ℕ) (j : ℕ))
    have hN : Submodule.IsFullLattice D.host.E N :=
      Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsd
    letI : Submodule.IsLattice D.host.E (Formalism.L2.Col.starLat D.host.E N) :=
      Formalism.L2.Col.brp_starLat_lattice D.host.E N hsd.1
    refine ⟨?_⟩
    have heq : star '' (N : Set (Fin (spW₁ G i j).rank → D.host.E)) =
        (Formalism.L2.Col.starLat D.host.E N : Set (Fin (spW₁ G i j).rank → D.host.E)) := by
      ext x
      change (∃ y, y ∈ N ∧ star y = x) ↔ star x ∈ N
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨star x, hx, star_star x⟩
    rw [← heq]
    exact Formalism.L2.Col.brp_star_span_top D.host.E _ (Submodule.IsFullLattice.span_eq_top (self := hN))
  have hb : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) (Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ)))) β :=
    fun v => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) _ (GlobalTheory.AdelicU.isCMExt_host D)
  refine ⟨Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ))),
    fun v => if h : v ∈ B.P then (hb ⟨v, h⟩).choose else 1, ⟨?_, ?_, hlat, ?_, ?_, ?_⟩⟩
  · intro a b
    show star (((-1 : D.host.E) • (spW₁ G i j).gram) b a) = ((-1 : D.host.E) • (spW₁ G i j).gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, star_gram]
  · intro w
    have hs := hV.sigOK (B.emb w).1
    rw [hV.sig, ← hV.rank] at hs
    have eJ : ((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1 = -((spW₁ G i j).gram.map (B.emb w).1) := by
      ext a b; simp
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1) _ _
    rw [eJ]
    exact hasSig_neg_of_hasSignature hs
  · intro y
    exact mem_starLat_iff_form (spW₁ G i j) hsd y
  · intro w
    have eJ : ((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1 =
        -((gramAt D (spW₁ G i j) (τf w)).map star) := by
      ext a b; simp [gramAt, hB]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1) _
    rw [eJ]
    exact isCartan_neg_conj (W.cart_is _ hR (τf w))
  · intro v
    show GlobalTheory.AdelicU.IsSplitBasis _ _ (if h : v.1 ∈ B.P then (hb ⟨v.1, h⟩).choose else 1)
    rw [dite_eq_left v.2]
    exact (hb v).choose_spec

end GlobalTheory.TripleSpace
end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem kudlaSplittingSplitUnitary : GlobalTheory.Published.KudlaSplittingSplitUnitary := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α ν _ _ _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres
  letI : MeasurableSpace (Matrix α ν E) := borel _
  haveI : BorelSpace (Matrix α ν E) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨-, hG⟩ := hmat α ν
  haveI := hG.grp
  haveI := hG.t2
  haveI := hG.lc
  haveI := hG.sc
  obtain ⟨κ, ω, hKW⟩ := GlobalTheory.T.exists_weil_representation_split_unitary_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (Measure.addHaar)
  refine ⟨ω, GlobalTheory.T.splitUnitaryWeilRepresentation_isSmooth F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_,
    GlobalTheory.T.weilRepresentation_intertwines_heisenberg F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_⟩
  · intro μ' hμ' g φ
    exact GlobalTheory.T.weil_representation_preserves_L2_space F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW μ' g φ
  · intro a φ x
    have hp : levi c hE.invol a ∈ sieg c ν := by
      rw [mem_sieg, mat, levi_val, toBlocks_fromBlocks₂₁]
    rw [hKW.par _ hp φ]
    have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by
      simp [pr, form, GlobalTheory.WeilM.hTens]
    obtain ⟨-, -, hsc, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
    have hd := hsc (Matrix.GeneralLinearGroup.det a)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hd
    simp only [parFun, mat, levi_val, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.mul_zero, h0,
      mul_zero, AddChar.map_zero_eq_one, one_mul, hd]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem bad_part_le_locShare : ∀ (D : D7) (Γ V : Type) [Group Γ] [Finite Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G0g D.nd) (ι : G0g D.nd →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D P lam ψ → ∀ (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup (G0g D.nd)), (∀ k, IsHalf D k (H k)) → ∀ (n : Fin 2 → ℕ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → ∀ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) → ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) : ℝ) ≤ c * (locShare D (fun k _ => eUk D k (ψ₀ k)) 0 (S 0) + locShare D (fun k _ => eUk D k (ψ₀ k)) 1 (S 1)) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  intro D Γ V _ _ _ _ _ π ι hs ρ P lam ψ hW lamb hlamb H hH n c hemb hn ψ₀ hψ₀
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  haveI : Finite (G0g D.nd) := Finite.of_injective ι (fun a b h => by
    have := congrArg π h; rwa [hs.1, hs.1] at this)
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨S, hbad, hsplit⟩ := GlobalTheory.T.one_sub_goodIdempotent_eq_badTupleSums D
  have hloc : ∀ k, locShare D (fun k' v => eUk D k' (ψ ⟨k', v⟩)) k (S k) =
      locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) := by
    intro k
    unfold locShare
    refine Finset.sum_congr rfl fun t _ => Finset.prod_congr rfl fun v _ => ?_
    exact GlobalTheory.T.weight_upperUnitriangularIdempotent_indep_character D k _ _ (hW.1 ⟨k, v⟩) (hψ₀ k) (t v)
  refine ⟨S, hbad, ?_⟩
  have key := GlobalTheory.T.finrank_eigen_inf_ker_le_of_semidirect_split (G0g D.nd) Γ V π ι hs ρ P lam lamb hlamb H n D.ntypes.e0
    (fun k => badElt D k (S k)) (fun k => locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k)) c hemb hn
    (fun k => (GlobalTheory.BadCount.IdemCen.badElt_idem_central D k (S k)).1)
    (fun k a => (GlobalTheory.BadCount.IdemCen.badElt_idem_central D k (S k)).2 a)
    (by simpa using hsplit)
    (fun k g hg => (GlobalTheory.BadCount.badElt_mul_lvlIdem D P lam ψ hW k (S k) (H k) (hH k)).1 g hg)
    (fun k => by rw [← hloc k]; exact (GlobalTheory.BadCount.badElt_mul_lvlIdem D P lam ψ hW k (S k) (H k) (hH k)).2)
  simpa using key

end GlobalTheory.BadCount
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonneColength_eq_log_degree : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e → Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  first | exact @GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | exact GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | (intros; apply GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.lineBundleFamily_openChart_affine_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), LocallyOfFiniteType U.hom → Fam A M → Inj A M → (∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Mono f], (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → IsOpenImmersion f) → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left) (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U), Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ → ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u) → ChartAt A M N := by
  first | exact @GlobalTheory.DualCon.chartAt_of_lifting | exact GlobalTheory.DualCon.chartAt_of_lifting | (intros; apply GlobalTheory.DualCon.chartAt_of_lifting <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.lineBundleFamilyParamInjective_of_geomFiberInjective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), LocallyOfFiniteType U.hom → Fam A M → FibInj A M → Inj A M := by
  first | exact @GlobalTheory.DualInj.inj_of_fibInj | exact GlobalTheory.DualInj.inj_of_fibInj | (intros; apply GlobalTheory.DualInj.inj_of_fibInj <;> assumption)
end
