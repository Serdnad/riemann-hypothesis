module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle023
import Formalism.RealPlaceAnalysis.Bundle005
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.SmoothKZ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem semiconj_gen {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ}
    {A : Type} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι)
    (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (T : A) (P Q : Matrix (Fin n) (Fin n) R)
    (h : ∀ X, T * l X = l (P * X * Q) * T) (τ : ι) (i j : Fin n) :
    T * gen D l τ i j = (∑ k, ∑ m, (D.ch τ (P k i) * D.ch τ (Q j m)) • gen D l τ k m) * T := by
  have ent : ∀ (k m : Fin n) (r : R), (P * Matrix.single i j r * Q) k m = P k i * Q j m * r := by
    intro k m r
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
    ring
  have key : ∀ x : ℂ ⊗[ℝ] R, T * unitMap l i j x =
      (∑ k, ∑ m, unitMap l k m ((1 ⊗ₜ[ℝ] (P k i * Q j m)) * x)) * T := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      rw [unitMap_tmul, mul_smul_comm, h, Matrix.matrix_eq_sum_single (P * Matrix.single i j r * Q)]

      simp only [map_sum, Finset.sum_mul, Finset.smul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      unitMap_tmul, ent, smul_mul_assoc]
    | add x y hx hy =>
      simp only [map_add (f := _), mul_add, hx, hy, Finset.sum_add_distrib, add_mul]
  show T * unitMap l i j (D.e τ) = _
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  rw [D.mul_e, map_smul, map_mul]
  rfl

private theorem rtInf_lam {K : Type} [Field K] [NumberField K] {n : ℕ} (a : archGroup K n)
    (y : GL (Fin n) (mixedSpace K)) (hy : y = a.1) (X : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    rtInf a * lam K n X = lam K n (y.val * X * (y⁻¹).val) * rtInf a := by
  subst hy
  apply LinearMap.ext
  intro φ
  simp only [Module.End.mul_apply, lam_apply]
  rw [uAction_rtInf, IsExpLieAlgebra.AdU_ι]
  congr 4
  apply Subtype.ext
  simp [IsExpLieAlgebra.AdLie, IsExpLieAlgebra.Ad, toLie, IsExpLieAlgebra.toLie, IsExpLieAlgebra.ofLie,
    mul_assoc]
  show (show ArchMatrix K n from X) = ((↑(↑a : (ArchMatrix K n)ˣ)⁻¹ : ArchMatrix K n)) *
    ((((↑a : (ArchMatrix K n)ˣ) : ArchMatrix K n) * ((show ArchMatrix K n from X) *
      ((↑(↑a : (ArchMatrix K n)ˣ)⁻¹ : ArchMatrix K n)))) * ((↑a : (ArchMatrix K n)ˣ) : ArchMatrix K n))
  simp only [mul_assoc, Units.inv_mul_cancel_left]
  exact (Units.inv_mul_cancel_right (show ArchMatrix K n from X) (a : (ArchMatrix K n)ˣ)).symm

theorem UpperTheory.capOp_commute_rightTranslation :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ) (a : archGroup K n), Commute (capOp D n τ u) (rtInf a) := by
  intro K _ _ n ι _ D τ u a
  let y : GL (Fin n) (mixedSpace K) := a.1
  let P : Matrix (Fin n) (Fin n) ℂ := (D.ch τ).mapMatrix y.val
  let Q : Matrix (Fin n) (Fin n) ℂ := (D.ch τ).mapMatrix (y⁻¹).val
  have hQP : Q * P = 1 := by
    simp only [Q, P]
    rw [← map_mul, Units.inv_mul, map_one]
  have hsemi := semiconj_gen D (lam K n) (rtInf a) y.val (y⁻¹).val
    (fun X => rtInf_lam a y rfl X) τ
  have hq := GlobalTheory.CapAdInv.qdet_semiconj (gen D (lam K n) τ) _ (rtInf a) hsemi u
  have hGl := (UpperTheory.gen_glRelations_and_commute_of_isLie (mixedSpace K) ι n _ D (lam K n) (isLie_lam K n)).1 τ
  have had := GlobalTheory.CapAdInv.qdet_ad (gen D (lam K n) τ) hGl P Q hQP u
  show Formalism.REAL.qdet (gen D (lam K n) τ) u * rtInf a = rtInf a * Formalism.REAL.qdet (gen D (lam K n) τ) u
  rw [hq]
  congr 1
  exact had.symm
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem qdet_mem' {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (S : Subalgebra ℂ A) (X : Fin n → Fin n → A)
    (h : ∀ a b, X a b ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

private theorem aux {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ} {A : Type} [Ring A]
    [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] {B : Type} [Ring B] [Algebra ℝ B] (D : Idem R ι)
    (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] B) (hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X))
    (htop : Algebra.adjoin ℝ (Set.range l) = ⊤) (ρ : B →ₐ[ℝ] A) (τ : ι) (u : ℂ) :
    Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u ∈
      Submodule.span ℂ (ρ '' (Subalgebra.center ℝ B : Set B)) := by
  let j : B →ₐ[ℝ] ℂ ⊗[ℝ] B := Algebra.TensorProduct.includeRight
  let ψ : ℂ ⊗[ℝ] B →ₐ[ℂ] A := Algebra.TensorProduct.lift (Algebra.ofId ℂ A) ρ fun c x => Algebra.commutes c (ρ x)
  have hψ : ∀ c x, ψ (c ⊗ₜ x) = c • ρ x := fun c x =>
    (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (ρ x)).symm
  let l' : Matrix (Fin n) (Fin n) R →ₗ[ℝ] ℂ ⊗[ℝ] B := j.toLinearMap ∘ₗ l
  have hl' : IsLie l' := fun X Y => by
    change j (l X) * j (l Y) - j (l Y) * j (l X) = j (l (X * Y - Y * X))
    rw [← hl, map_sub, map_mul, map_mul]
  obtain ⟨hrel, hc⟩ := UpperTheory.gen_glRelations_and_commute_of_isLie R ι n _ D l' hl'
  set w := Formalism.REAL.qdet (gen D l' τ) u with hw
  have h0 : ∀ σ a b, gen D l' σ a b ∈ Subalgebra.centralizer ℂ {w} := fun σ a b => by
    rintro _ rfl
    by_cases e : σ = τ
    · subst e
      exact (Formalism.REAL.qDetCentral _ n _ (hrel σ) u a b)
    · refine (qdet_mem' (Subalgebra.centralizer ℂ {gen D l' σ a b}) _ (fun c d => ?_) u _ rfl).symm
      rintro _ rfl
      exact hc σ τ e a b c d
  have h1 : ∀ x : B, j x * w = w * j x := fun x => by
    have : Algebra.adjoin ℝ (Set.range l) ≤ (Subalgebra.centralizer ℝ {w}).comap j := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨X, rfl⟩
      have h2 : l' X ∈ Subalgebra.centralizer ℂ {w} := by
        rw [UpperTheory.lieMap_eq_sum_idempotent_gen R ι n _ D l' X]
        exact sum_mem fun σ _ => sum_mem fun a _ => sum_mem fun b _ => Subalgebra.smul_mem _ (h0 σ a b) _
      exact h2
    exact (this (htop ▸ Algebra.mem_top) w rfl).symm
  obtain ⟨p, hp, q, hq, e⟩ := UpperTheory.V.Fb.exists_re_im w h1
  have h2 : ψ w = Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u := by
    rw [hw, UpperTheory.V.Fb.map_qdet]
    congr 1
    funext a b
    exact gen_inter D l' (ρ.toLinearMap ∘ₗ l) τ a b a b ψ.toLinearMap LinearMap.id fun x =>
      (hψ 1 _).trans (one_smul _ _)
  rw [← h2, e, map_add (f := _), hψ, hψ]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩))

theorem UpperTheory.qdet_generates_universalEnveloping_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ), capOp D n τ u ∈ Zc K n := by
  intro K _ _ n ι _ D τ u
  let l : Matrix (Fin n) (Fin n) (mixedSpace K) →ₗ[ℝ] UEnv K n :=
    (UniversalEnvelopingAlgebra.ι ℝ (L := (isExpLieAlgebra K n).lieSubalgebra)).toLinearMap ∘ₗ (toLie K n).toLinearMap
  have hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X) := fun X Y => by
    change UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) -
      UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) =
      UniversalEnvelopingAlgebra.ι ℝ (toLie K n (X * Y - Y * X))
    rw [← Ring.lie_def, ← LieHom.map_lie]
    rfl
  have htop : Algebra.adjoin ℝ (Set.range l) = ⊤ := by
    refine eq_top_iff.2 fun z hz => ?_
    clear hz
    induction z using UEnv.induction with
    | halg r => exact Subalgebra.algebraMap_mem _ r
    | hι X => exact Algebra.subset_adjoin ⟨(toLie K n).symm X, by simp [l]⟩
    | hmul a b ha hb => exact mul_mem ha hb
    | hadd a b ha hb => exact add_mem ha hb
  have h := aux D l hl htop (uAction (K := K) (n := n)) τ u
  exact Algebra.span_le_adjoin ℂ _ h
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.centerU_action_mem_adjoin_capOp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), ∀ z ∈ (isExpLieAlgebra K n).centerU, uAction z ∈ Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} := by
  intro K _ _ n ι _ D z hz
  obtain ⟨hrel, hcomm⟩ := UpperTheory.gen_glRelations_and_commute_of_isLie (mixedSpace K) ι n _ D (lam K n) (isLie_lam K n)
  have h1 : ∀ u : UEnv K n,
      uAction u ∈ Algebra.adjoin ℂ {x | ∃ τ i j, x = gen D (lam K n) τ i j} := by
    intro u
    induction u using UEnv.induction with
    | halg r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℝ ℂ]
      exact Subalgebra.algebraMap_mem _ _
    | hι Y =>
      obtain ⟨X, rfl⟩ := (toLie K n).surjective Y
      rw [← lam_apply, UpperTheory.lieMap_eq_sum_idempotent_gen (mixedSpace K) ι n _ D (lam K n) X]
      exact sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨τ, i, j, rfl⟩)) _
    | hmul x y hx hy => rw [map_mul]; exact mul_mem hx hy
    | hadd x y hx hy => rw [map_add]; exact add_mem hx hy
  refine UpperTheory.V.Fb.multiCentre (gen D (lam K n)) hrel hcomm (h1 z) fun τ i j => ?_
  have h2 := gen_mem D (lam K n) τ i j
    (Subalgebra.toSubmodule (Subalgebra.centralizer ℂ {uAction z})) fun x => by
      rintro _ rfl
      rw [lam_apply, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  exact (h2 _ rfl).symm
end
