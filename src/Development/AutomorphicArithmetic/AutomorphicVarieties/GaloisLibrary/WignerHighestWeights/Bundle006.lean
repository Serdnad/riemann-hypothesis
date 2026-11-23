module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem atEmb_add' {E : Type} [Field E] (τ : E →+* ℂ) (z w : ℂ) :
    atEmb τ (z + w) = atEmb τ z + atEmb τ w := by
  rw [atEmb_eq τ (z + w), atEmb_eq τ z, atEmb_eq τ w, Complex.add_re, Complex.add_im, add_smul, add_smul]
  abel

private noncomputable def atEmbHom {E : Type} [Field E] (τ : E →+* ℂ) : ℂ →+ Cinf E :=
  AddMonoidHom.mk' (atEmb τ) (atEmb_add' τ)

private theorem mul_atEmb_map {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    p * x.map (atEmb τ) = (p.map (coord τ) * x).map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.mul_apply, Matrix.map_apply]

  rw [show atEmb τ (∑ k, coord τ (p i k) * x k j) = ∑ k, atEmb τ (coord τ (p i k) * x k j) from
  map_sum (atEmbHom τ) _ _]
  exact Finset.sum_congr rfl fun k _ => GlobalTheory.CapAdInv.mul_atEmb _ _ _

private theorem atEmb_map_mul {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    x.map (atEmb τ) * p = (x * p.map (coord τ)).map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.mul_apply, Matrix.map_apply]

  rw [show atEmb τ (∑ k, x i k * coord τ (p k j)) = ∑ k, atEmb τ (x i k * coord τ (p k j)) from
  map_sum (atEmbHom τ) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, mul_comm (x i k)]
  exact GlobalTheory.CapAdInv.mul_atEmb _ _ _

private theorem atEmb_map_sub {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (x y : Matrix (Fin a) (Fin a) ℂ) :
    (x - y).map (atEmb τ) = x.map (atEmb τ) - y.map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.sub_apply, Matrix.map_apply]
  exact map_sub (atEmbHom τ) _ _

theorem UpperTheory.V.AlgRepEndIrreducible.holMul :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N),
      (∀ p q : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (p * X * q))) →
        ∀ x, hol τ L' x = hol τ L (p.map (coord τ) * x * q.map (coord τ))) ∧
      ∀ Y : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (Y * X - X * Y))) →
        ∀ x, hol τ L' x = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  intro E _ _ _ a N _ _ _ _ τ L L'
  refine ⟨fun p q h x => ?_, fun Y h x => ?_⟩
  · rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← atEmb_map_sub, ← atEmb_map_sub, ← smul_sub]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.wtEq :
    ∀ (n : ℕ) (ν ν' : Fin n → ℂ), Dom ν → Dom ν' →
      (∀ u : ℂ, ∏ k : Fin n, (u - (k : ℂ) + ν k) = ∏ k : Fin n, (u - (k : ℂ) + ν' k)) → ν = ν' := by
  intro n ν ν' hν hν' hp
  classical
  have key : ∀ μ : Fin n → ℂ, Dom μ → ∀ i : Fin n,
      (Multiset.filter (fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1)
        (Multiset.map (fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val)).card = (i : ℕ) := by
    intro μ hμ i
    have hP : ∀ j : Fin n, (∃ k : ℕ, μ j - (j : ℂ) - (μ i - (i : ℂ)) = (k : ℂ) + 1) ↔ j < i := by
      intro j
      constructor
      · rintro ⟨k, hk⟩
        by_contra hji
        rcases (not_lt.1 hji).lt_or_eq with hij | hij
        · obtain ⟨m, hm⟩ := hμ i j hij
          have h1 : (((i : ℕ) : ℕ) : ℂ) = ((k + 1 + m + (j : ℕ) : ℕ) : ℂ) := by
            push_cast
            linear_combination hk + hm
          have h2 : (i : ℕ) = k + 1 + m + (j : ℕ) := Nat.cast_injective h1
          have h3 : (i : ℕ) < (j : ℕ) := hij
          omega
        · subst hij
          have h1 : ((k + 1 : ℕ) : ℂ) = ((0 : ℕ) : ℂ) := by
            push_cast
            linear_combination -hk
          have h2 : k + 1 = 0 := Nat.cast_injective h1
          omega
      · intro hji
        obtain ⟨m, hm⟩ := hμ j i hji
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
        have hi : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) + (d : ℂ) + 1 := by
          exact_mod_cast hd
        refine ⟨m + d, ?_⟩
        push_cast
        linear_combination hm + hi
    rw [Multiset.filter_map, Multiset.card_map]
    have hf : Multiset.filter ((fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1) ∘
        fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val
          = Multiset.filter (fun j : Fin n => j < i) Finset.univ.val :=
      Multiset.filter_congr (fun j _ => hP j)
    rw [hf]
    calc (Multiset.filter (fun j : Fin n => j < i) Finset.univ.val).card
        = (Finset.univ.filter (fun j : Fin n => j < i)).card := rfl
      _ = (Finset.Iio i).card := by
        congr 1
        ext j
        simp
      _ = (i : ℕ) := Fin.card_Iio i
  have hm : Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val
      = Multiset.map (fun j : Fin n => ν' j - (j : ℂ)) Finset.univ.val := by
    apply msetSep
    intro u
    rw [Multiset.map_map, Multiset.map_map]
    have e : ∀ μ : Fin n → ℂ, (Multiset.map ((fun x => u + x) ∘ fun j : Fin n => μ j - (j : ℂ))
        Finset.univ.val).prod = ∏ k : Fin n, (u - (k : ℂ) + μ k) := by
      intro μ
      rw [Finset.prod_eq_multiset_prod]
      congr 2
      funext k
      dsimp
      ring
    rw [e, e]
    exact hp u
  funext i
  have hmem : ν' i - (i : ℂ) ∈ Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val := by
    rw [hm]
    exact Multiset.mem_map.2 ⟨i, by simp, rfl⟩
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hmem
  have h1 := key ν hν j
  have h2 := key ν' hν' i
  rw [← hm, ← hj, h1] at h2
  have hji : j = i := Fin.ext h2
  subst hji
  linear_combination hj
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem multi_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : (Fin q → V) →ₘₗ[ℝ] ℂ) : Continuous μ := by
  let b := Module.finBasis ℝ V
  have e : (μ : (Fin q → V) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, b.coord (r i) (x i)) • μ fun i => b (r i) := by
    funext x
    have h : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm

    conv_lhs => rw [h, μ.map_sum]
    simp only [μ.map_smul_univ, RingHom.id_apply]
  rw [e]
  refine continuous_finsetSum _ fun r _ => Continuous.fun_smul ?_ continuous_const
  exact continuous_finsetProd _ fun i _ =>
    (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

private theorem multi_deriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : (Fin q → V) →ₘₗ[ℝ] ℂ) (c : ℝ → Fin q → V) (c' : Fin q → V)
    (hc : ∀ i, HasDerivAt (fun t => c t i) (c' i) 0) :
    HasDerivAt (fun t => μ (c t)) (∑ i, μ (Function.update (c 0) i (c' i))) 0 := by
  let ν : ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℂ := ⟨μ, multi_cont μ⟩
  have h := (ν.hasFDerivAt (c 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi.2 hc)
  rw [ContinuousMultilinearMap.linearDeriv_apply] at h
  exact h

private theorem hp_herm {E : Type} [Field E] {a : ℕ} (Y : Herm E a) : hp (toL Y.1) = Y := by
  apply Subtype.ext
  have h : star Y.1 = Y.1 := Y.2
  rw [hp_val, h, ← two_smul ℝ, smul_smul]
  norm_num

private theorem conj_deriv {E : Type} [Field E] [NumberField E] {a : ℕ} (k : ℝ → Kinf E a)
    (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (h0 : k 0 = 1)
    (hk : HasDerivAt (fun t => toL (k t).1) (toL Z) 0) (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t => toL ((k t).1 * Y * star (k t).1)) (toL (Z * Y - Y * Z)) 0 := by
  open scoped Matrix.Norms.Operator in
  have h1 : HasDerivAt (fun t => (k t).1) Z 0 := hk
  open scoped Matrix.Norms.Operator in
  have h2 : HasDerivAt (fun t => star (k t).1) (star Z) 0 :=
    (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => (hasDerivAt_pi.1 (hasDerivAt_pi.1 hk j) i).star :
      HasDerivAt (fun t => toL (star (k t).1)) (toL (star Z)) 0)
  open scoped Matrix.Norms.Operator in
  have h := (h1.mul_const Y).mul h2
  simp only [h0, hZ, OneMemClass.coe_one, star_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg] at h
  exact h

theorem UpperTheory.V.AlgRepEndIrreducible.infAbs :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M),
      SepDer κ L → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq L ω := by
  intro E _ _ _ a M _ _ _ _ κ L hS q ω hω Z hZ Y
  obtain ⟨k, h0, hk⟩ := kCurve E a Z hZ
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨l, hl, hd⟩ := hS k Z h0 hk _ hne
  apply hl
  let μ : (Fin q → Lie E a) →ₘₗ[ℝ] ℂ :=
    (l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hp)
  have hμ : ∀ X : Fin q → Herm E a, μ (fun i => toL (X i).1) = l (ω X) := fun X => by
    change l (ω fun i => hp (toL (X i).1)) = _
    simp only [hp_herm]
  have h1 := multi_deriv μ (fun t i => toL (adHerm (k t) (Y i)).1) (fun i => toL (brH Z hZ (Y i)).1)
    (fun i => conj_deriv k Z hZ h0 hk (Y i).1)
  have h2 : ∀ t, μ (fun i => toL (adHerm (k t) (Y i)).1) = l (κ (k t) (ω Y)) := fun t => by
    rw [hμ, hω]
  simp only [h2] at h1

  rw [map_sub, (hd (ω Y)).unique h1, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hμ]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp only [Function.update_self]
  · simp only [Function.update_of_ne h, h0, adHerm, OneMemClass.coe_one, star_one, mul_one, one_mul]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private def UpperTheory.V.AlgRepEndIrreducible.altFlip {A V M : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add (f := _), AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

theorem UpperTheory.V.AlgRepEndIrreducible.homot :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M),
      IsRetr κ L α → (∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq L ω) → ¬ HasCohomology κ L := by
  intro E _ _ _ a M _ _ _ _ κ L α hα hinf
  rintro (⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩)
  · refine h2 (AlternatingMap.ext fun Y => ?_)
    have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := by
      intro X
      let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
      have hZ : star Z = -Z := by
        simp only [Z]
        rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
      have hX : toL X = toL (hp (toL X)).1 + toL Z := by
        have h : X = (hp (toL X)).1 + Z := by
          rw [hp_val]; simp only [Z]; module
        exact congrArg toL h
      have h3 := DFunLike.congr_fun h1 fun _ => hp (toL X)
      rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y] at h3
      have h4 : L (toL (hp (toL X)).1) (ω Y) = 0 := by simpa using h3
      rw [congrArg L hX, map_add (f := _), LinearMap.add_apply, h4, hinf 0 ω h0 Z hZ Y]
      simp
    rw [← hα.retr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero, AlternatingMap.zero_apply]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := altFlip (ω.curryLeft ∘ₗ hp)
    have hF : ∀ Y X, F Y X = ω (Matrix.vecCons (hp X) Y) := fun _ _ => rfl
    let ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a := fun Y =>
      { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y)
        map_add' := fun X X' => by
          have h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y =
              (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y) := by noncomm_ring
          exact congrArg toL h
        map_smul' := fun c X => by
          have h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y) := by
            rw [smul_sub, mul_smul_comm, smul_mul_assoc]
          exact congrArg toL h }
    refine h2 (α.compAlternatingMap F) (fun k Y => ?_) (AlternatingMap.ext fun Y => ?_)
    · refine (hα.cpt k (F Y) (F fun i => adHerm k (Y i)) fun X => ?_).symm
      have e : hp (toL (k.1 * X * star k.1)) = adHerm k (hp (toL X)) := by
        apply Subtype.ext
        change _ = k.1 * (hp (toL X)).1 * star k.1
        rw [hp_val, hp_val, star_mul, star_mul, star_star, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
          mul_assoc k.1 (star X)]
      rw [hF, hF, ← h0, e]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    · let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
        (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
      have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
        hα.lie _ _ _ fun X => (sub_add_cancel _ _).symm

      rw [dCo_apply, ← hα.retr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, ← h3]
        rfl
      · rw [LinearMap.sum_apply]
        exact homId E a M L q ω h1 (hinf _ ω h0) (Matrix.of X) Y
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.hwIso :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (F' : ι → Fin n → Fin n → Module.End ℂ V'),
      IsMultiGl F → IsMultiGl F' → (∀ W, Stab F W → W = ⊥ ∨ W = ⊤) → (∀ W, Stab F' W → W = ⊥ ∨ W = ⊤) →
      ∀ (ν : ι → Fin n → ℂ) (v : V) (v' : V'), v ≠ 0 → v' ≠ 0 → (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
        (∀ t, Formalism.REAL.IsHW (F' t) (ν t) v') → ∃ T : V ≃ₗ[ℂ] V', ∀ t i j x, T (F t i j x) = F' t i j (T x) := by
  intro ι V _ _ _ n F V' _ _ F' hF hF' hS hS' ν v v' hv0 hv0' hv hv'
  let P : ι → Fin n → Fin n → Module.End ℂ (V × V') := fun t i j => (F t i j).prodMap (F' t i j)
  have hPa : ∀ t i j (x : V) (y : V'), P t i j (x, y) = (F t i j x, F' t i j y) := fun _ _ _ _ _ => rfl
  have hP : IsMultiGl P := by
    refine ⟨fun t i j k l => ?_, fun s t hst i j k l => ?_⟩
    · refine LinearMap.ext fun z => ?_
      have e := LinearMap.congr_fun (hF.1 t i j k l) z.1
      have e' := LinearMap.congr_fun (hF'.1 t i j k l) z.2
      refine Prod.ext (e.trans ?_) (e'.trans ?_)
      · split_ifs <;> rfl
      · split_ifs <;> rfl
    · refine LinearMap.ext fun z => ?_
      exact Prod.ext (LinearMap.congr_fun (hF.2 s t hst i j k l) z.1)
        (LinearMap.congr_fun (hF'.2 s t hst i j k l) z.2)
  have hvv : ∀ t, Formalism.REAL.IsHW (P t) (ν t) (v, v') := fun t =>
    ⟨fun i => Prod.ext ((hv t).1 i) ((hv' t).1 i),
      fun i j h => Prod.ext ((hv t).2 i j h) ((hv' t).2 i j h)⟩
  obtain ⟨hm, hst⟩ := lowStab ι (V × V') n P hP ν (v, v') hvv
  have hl := lowLine ι (V × V') n P hP ν (v, v') hvv
  generalize low P (v, v') = W at hm hst hl
  have hA : ∀ y : V', ((0 : V), y) ∈ W → y = 0 := by
    rcases hS' (W.comap (LinearMap.inr ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw
      rwa [LinearMap.inr_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : ((0 : V), v') ∈ W := (Submodule.eq_top_iff'.1 h v' :)
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by
        rw [hPa, map_zero, (hv' t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.fst hc).symm).resolve_right hv0
      rw [h2, zero_smul] at hc
      exact absurd (congrArg Prod.snd hc) hv0'
  have hB : ∀ x : V, (x, (0 : V')) ∈ W → x = 0 := by
    rcases hS (W.comap (LinearMap.inl ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw
      rwa [LinearMap.inl_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : (v, (0 : V')) ∈ W := (Submodule.eq_top_iff'.1 h v :)
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by
        rw [hPa, map_zero, (hv t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.snd hc).symm).resolve_right hv0'
      rw [h2, zero_smul] at hc
      exact absurd (congrArg Prod.fst hc) hv0
  have hC : W.map (LinearMap.fst ℂ V V') = ⊤ := by
    refine (hS _ ?_).resolve_left fun h => hv0 ((Submodule.eq_bot_iff _).1 h v ⟨_, hm, rfl⟩)
    rintro t i j _ ⟨z, hz, rfl⟩
    exact ⟨_, hst t i j z hz, rfl⟩
  have hD : W.map (LinearMap.snd ℂ V V') = ⊤ := by
    refine (hS' _ ?_).resolve_left fun h => hv0' ((Submodule.eq_bot_iff _).1 h v' ⟨_, hm, rfl⟩)
    rintro t i j _ ⟨z, hz, rfl⟩
    exact ⟨_, hst t i j z hz, rfl⟩
  have b1 : Function.Bijective ((LinearMap.fst ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : x = 0)
      exact Subtype.ext (Prod.ext rfl (hA y hz))
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hC x
      exact ⟨⟨z, hz⟩, rfl⟩
  have b2 : Function.Bijective ((LinearMap.snd ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : y = 0)
      exact Subtype.ext (Prod.ext (hB x hz) rfl)
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hD x
      exact ⟨⟨z, hz⟩, rfl⟩
  have key : ∀ z : W, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) z.1.1 = z.1.2 := by
    intro z
    have : (LinearEquiv.ofBijective _ b1).symm z.1.1 = z := (LinearEquiv.ofBijective _ b1).symm_apply_apply z
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨(LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2), fun t i j x => ?_⟩
  obtain ⟨z, rfl⟩ := b1.2 x
  exact (key ⟨_, hst t i j z.1 z.2⟩).trans (congrArg (F' t i j) (key z).symm)
end
