module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Theta.Capelli.CompleteHomogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairConeAlg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∃ (l : Fin N → Fin M) (m' : Fin M'), LinearIndependent Ω (φ ∘ l) ∧
      pairProjCoord y e φ φ' t ⟨none, m'⟩ ≠ 0 ∧
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic
          (Algebra.adjoin O
            (Set.range (fun q : Σ k, ι k =>
                (C (algebraMap Ω Φ (y q)) * X (some (some q.1)) : MvPolynomial (Option (Option K)) Φ)) ∪
              Set.range (Sum.elim
                (fun i : Fin N => C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none))
                (fun _ : Unit => C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none))))
          (C (pairProjCoord y e φ φ' t p) * X p.1)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem SpanBundleTrdegGe.algebraicIndependent_linComb {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    {i : ℕ} (s : Fin i → Φ) (hs : AlgebraicIndependent Ω s) (A : Matrix (Fin i) (Fin i) Ω)
    (hA : IsUnit A) : AlgebraicIndependent Ω (fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) := by
  classical
  let L : Matrix (Fin i) (Fin i) Ω → MvPolynomial (Fin i) Ω →ₐ[Ω] MvPolynomial (Fin i) Ω :=
    fun B => aeval fun r => ∑ j, C (B r j) * X j
  have hcomp : ∀ B B', (L B').comp (L B) = L (B * B') := by
    intro B B'
    apply MvPolynomial.algHom_ext
    intro r

    simp only [L, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hid : L 1 = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, Matrix.one_apply]
  have heq : (aeval fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) = (aeval s).comp (L A) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, mul_comm]
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have hinj : Function.Injective (L A) := Function.LeftInverse.injective (g := L A⁻¹) fun p => by
    rw [← AlgHom.comp_apply, hcomp, hAinv, hid, AlgHom.id_apply]
  rw [algebraicIndependent_iff_injective_aeval, heq]
  exact (algebraicIndependent_iff_injective_aeval.1 hs).comp hinj

theorem SpanBundleTrdegGe.injective_aeval_mul_X {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ] {i : ℕ}
    (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    Function.Injective (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) := by
  let H : MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial (MvPolynomial (Fin i) Ω) :=
    aeval fun r => Polynomial.C (X r) * Polynomial.X
  have hH : Function.Injective H := by
    have h1 : ((Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω).comp H =
        AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro r
      simp [H]
    exact Function.LeftInverse.injective (g := (Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω)
      fun p => by rw [← AlgHom.comp_apply, h1, AlgHom.id_apply]
  have heq : (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) = (Polynomial.mapAlgHom (aeval σ)).comp H := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [H]
  rw [heq]
  exact (Polynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.1 hσ)).comp hH

theorem SpanBundleTrdegGe.exists_injective_cone {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    (K : Type*) {i : ℕ} (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    ∃ Ψ : MvPolynomial (Fin i) (MvPolynomial K Ω) →+* MvPolynomial (Option K) Φ, Function.Injective Ψ ∧
      (∀ p, Ψ (C p) = rename some (map (algebraMap Ω Φ) p)) ∧ ∀ r, Ψ (X r) = C (σ r) * X none := by
  let θ : MvPolynomial (Fin i) Ω →+* Polynomial Φ :=
    (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ).toRingHom
  have hθ : Function.Injective θ := SpanBundleTrdegGe.injective_aeval_mul_X σ hσ
  let e := (optionEquivRight Φ K).symm
  have heC : ∀ a : Φ, e (C (Polynomial.C a)) = C a := fun a =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_C Φ K a).symm
  have heX : ∀ k, e (X k) = X (some k) := fun k =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_some Φ K k).symm
  have heN : e (C Polynomial.X) = X none :=
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_none Φ K).symm
  refine ⟨e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom),
    e.injective.comp ((map_injective θ hθ).comp (commAlgEquiv Ω (Fin i) K).injective), ?_, ?_⟩
  · intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h1 : θ (C a) = Polynomial.C (algebraMap Ω Φ a) := by simp [θ]
      simp [h1, heC]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p k hp =>
      rw [C_mul, map_mul, hp, map_mul, map_mul]
      have h2 : (e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom))
          (C (X k)) = X (some k) := by
        simp [heX]
      rw [h2, map_X, rename_X]
  · intro r
    have h3 : θ (X r) = Polynomial.C (σ r) * Polynomial.X := by simp [θ]
    have h4 : e (C (Polynomial.C (σ r) * Polynomial.X)) = C (σ r) * X none := by
      rw [C_mul, map_mul, heC, heN]
    simp [h3, heC, heN]

theorem SpanBundleTrdegGe.proof : SpanBundleTrdegGe.Statement := by
  intro F _ Ω _ _ K ι y M i G hG Φ _ _ s hs
  classical
  let : Algebra F Φ := ((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra
  have : IsScalarTower F Ω Φ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set z := projCoord y (Pi.basisFun Ω (Fin i))
    (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s with hz
  change Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
    Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ pointIdeal F z)
  have hzn : ∀ m, z ⟨none, m⟩ = ∑ j, s j * algebraMap Ω Φ (G m j) := by
    intro m
    simp [hz, projCoord, Matrix.col]
    rfl
  have hzs : ∀ k (q : ι k), z ⟨some k, q⟩ = algebraMap Ω Φ (y ⟨k, q⟩) := fun _ _ => rfl

  obtain ⟨l, hl⟩ : ∃ l : Fin i → Fin M, IsUnit (Matrix.of fun r j => G (l r) j) := by
    have hrk : (Matrix.of G).rank = i := by
      rw [← Matrix.rank_transpose]
      simpa using LinearIndependent.rank_matrix (M := Matrix.transpose (Matrix.of G)) hG
    obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' Ω (Matrix.of G).row
    have : Finite κ := hli.finite
    let : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = i := by
      rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrk]
    let e : Fin i ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨a ∘ e, Matrix.linearIndependent_rows_iff_isUnit.1 ?_⟩
    exact hli.comp e e.injective
  set σ : Fin i → Φ := fun r => ∑ j, s j * algebraMap Ω Φ (G (l r) j) with hσdef
  have hσ : AlgebraicIndependent Ω σ :=
    SpanBundleTrdegGe.algebraicIndependent_linComb s hs _ hl

  have : (pointIdeal F y).IsPrime := RingHom.ker_isPrime _
  have : (pointIdeal F z).IsPrime := RingHom.ker_isPrime _
  set Ay := MRing ι F ⧸ pointIdeal F y
  set Az := MRing (bundleIdx ι M) F ⧸ pointIdeal F z
  let qy : Ay →ₐ[F] MvPolynomial K Ω := Ideal.kerLiftAlg (pointConeMap F y)
  have hqy : Function.Injective qy := Ideal.kerLiftAlg_injective _
  let qz : Az →ₐ[F] MvPolynomial (Option K) Φ := Ideal.kerLiftAlg (pointConeMap F z)
  let emb : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (R := Φ) some).toRingHom.comp (map (algebraMap Ω Φ))
  let σ' : (Σ k, ι k) → (Σ o, bundleIdx ι M o) := fun p => ⟨some p.1, p.2⟩
  have hE1 : ∀ g : MRing ι F, pointConeMap F z (rename σ' g) = emb (pointConeMap F y g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [pointConeMap, emb, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      simp only [map_mul, hp, rename_X]
      simp [pointConeMap, emb, σ', hzs]
  have hle : pointIdeal F y ≤ (pointIdeal F z).comap (rename σ' : MRing ι F →ₐ[F] _) := by
    intro g hg
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker] at hg ⊢
    rw [hE1, hg, map_zero]
  let fy : Ay →ₐ[F] Az := Ideal.quotientMapₐ (pointIdeal F z) (rename σ') hle
  let Θ : MvPolynomial (Fin i) Ay →ₐ[F] Az :=
    aevalTower fy fun r => Ideal.Quotient.mk _ (X ⟨none, l r⟩)

  obtain ⟨Ψ, hΨ, hΨC, hΨX⟩ := SpanBundleTrdegGe.exists_injective_cone K σ hσ
  have key : ∀ a, qz (Θ a) = Ψ (map qy.toRingHom a) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [Θ, aevalTower_C, map_C]
      rw [hΨC]
      change qz (Ideal.Quotient.mk _ (rename σ' g)) = emb (qy (Ideal.Quotient.mk _ g))
      simp only [qz, qy]
      exact hE1 g
    | add p q hp hq =>
      rw [map_add Θ, map_add qz, (map qy.toRingHom : MvPolynomial (Fin i) Ay →+* _).map_add, map_add Ψ, hp, hq]
    | mul_X p r hp =>
      simp only [map_mul, hp, map_X, hΨX]
      congr 1
      simp only [Θ, aevalTower_X]
      refine (Ideal.kerLiftAlg_mk (pointConeMap F z) _).trans ?_
      simp only [pointConeMap, aeval_X]
      exact congrArg (fun a => C a * X none) (hzn (l r))
  have hΘ : Function.Injective Θ := by
    intro a b hab
    apply map_injective qy.toRingHom hqy
    apply hΨ
    rw [← key, ← key, hab]

  have : FaithfulSMul F Ay :=
    (faithfulSMul_iff_algebraMap_injective F Ay).2 (algebraMap F Ay).injective
  have : FaithfulSMul Ay (MvPolynomial (Fin i) Ay) :=
    (faithfulSMul_iff_algebraMap_injective Ay _).2 (C_injective _ _)
  have e1 := trdeg_add_eq F Ay (A := MvPolynomial (Fin i) Ay)
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at e1
  rw [e1]
  exact trdeg_le_of_injective Θ hΘ

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial Finset

namespace SymmetricSpanHsymm

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem sum_esymm_mul_hsymm_int {k : ℕ} (hk : k ≠ 0) :
    ∑ s ∈ range (k + 1), (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s) = 0 := by
  apply map_injective (Int.castRingHom ℂ) Int.cast_injective
  apply MvPolynomial.funext
  intro x

  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_esymm, map_hsymm, map_zero]
  simp [GroundTheory.Heights₂.Theta.SymmFun.sum_esymm_mul_hsymm x k, hk]

theorem esymm_mem_adjoin (k : ℕ) :
    esymm σ ℤ k ∈ Algebra.adjoin ℤ (Set.range (hsymm σ ℤ)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set A := Algebra.adjoin ℤ (Set.range (hsymm σ ℤ))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [esymm_zero]; exact one_mem A
  have h := sum_esymm_mul_hsymm_int (σ := σ) hk.ne'
  rw [sum_range_succ, Nat.sub_self, hsymm_zero, mul_one] at h
  have h2 : ((-1 : MvPolynomial σ ℤ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have he : esymm σ ℤ k =
      -((-1) ^ k * ∑ s ∈ range k, (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s)) := by
    linear_combination (-1 : MvPolynomial σ ℤ) ^ k * h - esymm σ ℤ k * h2
  have hm1 : ∀ j : ℕ, (-1 : MvPolynomial σ ℤ) ^ j ∈ A := fun j => pow_mem (neg_mem (one_mem A)) j
  rw [he]
  refine neg_mem (mul_mem (hm1 k) (sum_mem fun s hs => mul_mem (mul_mem (hm1 s)
    (ih s (mem_range.mp hs))) (Algebra.subset_adjoin ⟨k - s, rfl⟩)))


omit [Fintype σ] [DecidableEq σ] in
theorem isHomogeneous_prod_map_X (t : Multiset σ) :
    ((t.map (X : σ → MvPolynomial σ ℤ)).prod).IsHomogeneous (Multiset.card t) := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
    exact (isHomogeneous_X ℤ a).mul ih

theorem isHomogeneous_hsymm_int (a : ℕ) : (hsymm σ ℤ a).IsHomogeneous a := by
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  have := isHomogeneous_prod_map_X (σ := σ) s.1
  rwa [s.2] at this

theorem isHomogeneous_prod_map_hsymm (t : Multiset ℕ) :
    ((t.map (hsymm σ ℤ)).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (isHomogeneous_hsymm_int a).mul ih

theorem isHomogeneous_hsymmPart {n : ℕ} (μ : n.Partition) : (hsymmPart σ ℤ μ).IsHomogeneous n := by
  have := isHomogeneous_prod_map_hsymm (σ := σ) μ.parts
  rwa [μ.parts_sum] at this

theorem exists_hsymmPart_of_mem_closure {x : MvPolynomial σ ℤ}
    (hx : x ∈ Submonoid.closure (Set.range (hsymm σ ℤ))) :
    ∃ (n : ℕ) (μ : n.Partition), x = hsymmPart σ ℤ μ := by
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, .indiscrete a, (hsymmPart_indiscrete σ ℤ a).symm⟩
  | one => exact ⟨0, .indiscrete 0, (hsymmPart_zero σ ℤ).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨n, μ, rfl⟩ := hy
    obtain ⟨n', ν, rfl⟩ := hz
    refine ⟨n + n', ⟨μ.parts + ν.parts, fun {i} hi => ?_, ?_⟩, ?_⟩
    · rcases Multiset.mem_add.mp hi with h | h
      exacts [μ.parts_pos h, ν.parts_pos h]
    · rw [Multiset.sum_add, μ.parts_sum, ν.parts_sum]
    · simp only [hsymmPart, Multiset.map_add (f := _), Multiset.prod_add]

theorem proof : SymmetricSpanHsymm.Statement := by
  intro N m G hG hsym
  set S := Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)
  have hA : G ∈ Algebra.adjoin ℤ (Set.range (hsymm (Fin N) ℤ)) := by
    obtain ⟨p, hp⟩ := esymmAlgHom_fin_surjective ℤ (le_refl N) ⟨G, hsym⟩
    have hG' : G = aeval (fun i : Fin N => esymm (Fin N) ℤ (i + 1)) p := by
      rw [← esymmAlgHom_apply, hp]
    rw [hG']
    clear hp hG'
    induction p using MvPolynomial.induction_on with
    | C r => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ r
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (esymm_mem_adjoin _)
  have hspan : G ∈ Submodule.span ℤ
      (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) := by
    rw [← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]
    exact hA
  have hle : Submodule.span ℤ
      (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) ≤
      S.comap (homogeneousComponent m) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨n, μ, rfl⟩ := exists_hsymmPart_of_mem_closure hx
    show homogeneousComponent m (hsymmPart (Fin N) ℤ μ) ∈ S
    rw [homogeneousComponent_of_mem (isHomogeneous_hsymmPart μ)]
    split_ifs with h
    · subst h; exact Submodule.subset_span ⟨μ, rfl⟩
    · exact zero_mem S
  have := hle hspan
  rwa [Submodule.mem_comap, homogeneousComponent_eq_self hG] at this

end SymmetricSpanHsymm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairBundleTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) =
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((N + 1 : ℕ) : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

instance projIdeal.isPrime {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M : ℕ} {E : Type*}
    [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ] (F : Type*) [Field F]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) : (projIdeal F y w φ t).IsPrime := by
  unfold projIdeal
  exact RingHom.ker_isPrime _

def FlagLineDegree.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    0 < N →
      FieldNumbers.relDeg (Function.Embedding.some : K ↪ Option K)
        (projIdeal F y w φ (truncCoord t 1)) = 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem lengthFormulaDimTwo : LengthFormulaDimTwo.Statement.{u} :=
  ReciprocityTheory.ChartRestriction.G.AI.length_two_generator_quotient

end GroundTheory.Heights₂.Heights.NumbersDVR
end
