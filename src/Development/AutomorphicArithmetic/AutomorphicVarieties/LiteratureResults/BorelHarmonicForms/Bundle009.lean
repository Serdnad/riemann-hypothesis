module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem isOpen_units (T : Type) [Fintype T] (a : ℕ) :
    IsOpen {x : Fin a → Fin a → T → ℂ | IsUnit (Matrix.of x)} := by
  have e : {x : Fin a → Fin a → T → ℂ | IsUnit (Matrix.of x)} = ⋂ t, {x : Fin a → Fin a → T → ℂ | (Matrix.of x).det t ≠ 0} := by
    ext x
    simp [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
  rw [e]
  refine isOpen_iInter_of_finite fun t => isOpen_ne_fun ?_ continuous_const
  have h : Continuous fun x : Fin a → Fin a → T → ℂ => (Matrix.of x).det := Continuous.matrix_det continuous_id
  exact (continuous_apply t).comp h

theorem UpperTheory.V.Lit.Bor.cxExt :
    UpperTheory.V.Lit.Bor.CxExt := by
  intro E _ _ _ a Ξ
  classical
  obtain ⟨R, Φ, hΦ, hR, hm⟩ := UpperTheory.V.Lit.Bor.cxGrp E a Ξ
  have ho := isOpen_units (E →+* ℂ) a
  let o : Fin a → Fin a → (E →+* ℂ) → ℂ := fun i j => (1 : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ)) i j
  have hd : ∀ k l (g : GL (Fin a) ((E →+* ℂ) → ℂ)), DifferentiableAt ℂ (Φ k l) (fun i j => g.val i j) := fun k l g =>
    (hΦ k l).differentiableAt (ho.mem_nhds g.isUnit)
  have hd1 : ∀ k l, HasFDerivAt (Φ k l) ((fderiv ℂ (Φ k l) o).restrictScalars ℝ) o := fun k l =>
    (hd k l 1).hasFDerivAt.restrictScalars ℝ
  let D : Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ) →ₗ[ℂ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
    { toFun := fun Z => Matrix.of fun k l => fderiv ℂ (Φ k l) o (fun i j => Z i j)
      map_add' := fun X Y => by
        ext k l
        exact map_add (fderiv ℂ (Φ k l) o) (fun i j => X i j) (fun i j => Y i j)
      map_smul' := fun c X => by
        ext k l
        exact map_smul (fderiv ℂ (Φ k l) o) c (fun i j => X i j) }
  refine ⟨R, D, ⟨fun k l => ?_, fun c Z h0 hc k l => ?_⟩, fun X => ?_⟩
  · simp only [hR]
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hv : Continuous fun g : GL (Fin a) ((E →+* ℂ) → ℂ) => (fun i j => g.val i j : Fin a → Fin a → (E →+* ℂ) → ℂ) :=
      Units.continuous_val (M := Matrix (Fin a) (Fin a) ((E →+* ℂ) → ℂ))
    exact ContinuousAt.comp (f := fun g : GL (Fin a) ((E →+* ℂ) → ℂ) => (fun i j => g.val i j : Fin a → Fin a → (E →+* ℂ) → ℂ))
      (hd k l g).continuousAt hv.continuousAt
  · simp only [hR]
    have h1 : HasDerivAt (fun s => (fun i j => (c s).val i j : Fin a → Fin a → (E →+* ℂ) → ℂ)) (fun i j => Z i j) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun t => hc i j t
    exact (hd1 k l).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [h0]; rfl)
  · ext k l
    let L : Lie E a →L[ℝ] (Fin a → Fin a → (E →+* ℂ) → ℂ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun τ =>
        (coordL τ).comp ((ContinuousLinearMap.proj j).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) i))
    have hL : L (oneL E a) = o := by
      funext i j
      exact congrFun (congrFun (Matrix.map_one (emb E) (map_zero _) (map_one _)) i) j
    have h := extGL_eventuallyEq (f := fun y => Ξ.mat y k l) (F := fun x => Φ k l (L x))
      (fun y => by rw [← hm, hR]; rfl) (x := oneL E a) isUnit_one
    have h1 : HasFDerivAt (Φ k l) ((fderiv ℂ (Φ k l) o).restrictScalars ℝ) (L (oneL E a)) := by
      rw [hL]; exact hd1 k l
    have h2 := HasFDerivAt.comp (oneL E a) h1 L.hasFDerivAt
    change _ = fderiv ℝ _ _ (toL X)
    rw [h.fderiv_eq]
    exact (congrArg (fun M : Lie E a →L[ℝ] ℂ => M (toL X)) h2.fderiv).symm
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cas_inter {E : Type} [Field E] [NumberField E] {a n : ℕ} (e : Fin n → Herm E a)
    {M N : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
    (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (L' : Lie E a →ₗ[ℝ] Module.End ℂ N) (f : M →ₗ[ℂ] N) (r : ℝ)
    (h : ∀ X m, f (L X m) = L' X (f m)) (m : M) :
    f (cas (shift L r) e m) = cas (shift L' r) e (f m) := by
  have h' : ∀ X m, f (shift L r X m) = shift L' r X (f m) := fun X m => by
    simp only [shift_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), h,
      LinearMap.map_smul_of_tower]

  simp only [cas, LinearMap.sum_apply, LinearMap.sub_apply, Module.End.mul_apply, map_sum, map_sub, h']

private theorem cas_alg {E : Type} [Field E] [NumberField E] {a n : ℕ} (e : Fin n → Herm E a)
    {A B : Type} [Ring A] [Algebra ℂ A] [Module ℝ A]
    [Ring B] [Algebra ℂ B] [Module ℝ B]
    (L : Lie E a →ₗ[ℝ] A) (L' : Lie E a →ₗ[ℝ] B) (f : A →ₐ[ℂ] B) (h : ∀ X, f (L X) = L' X) :
    f (cas L e) = cas L' e := by

  simp only [cas, map_sum, map_sub, map_mul, h]

theorem UpperTheory.V.Lit.Bor.casTens :
    UpperTheory.V.Lit.Bor.CasTens := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ a n e he π Ξ r
    obtain ⟨c₁, h₁⟩ := casPi E a n e he π r
    obtain ⟨c₂, h₂⟩ := casXi E a n e he Ξ (-r)
    have hB := cas_alg (B := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) e (shift Ξ.dmat (-r)) (shift (lieB π Ξ) (-r))
      ((Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) π.V).comp
        (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom)
      fun X => by
        rw [shift_apply, shift_apply, map_add (f := _), ← algebraMap_smul ℂ _ (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), map_smul, map_one]
        rfl
    rw [h₂, map_smul, map_one] at hB
    have hπ : ∀ φ : π.V, cas (A := Module.End ℂ π.V) (shift (lieOp π) r) e φ = c₁ • φ := fun φ =>
      Subtype.ext ((cas_inter e (lieOp π) (lie E a) π.V.subtype r (fun _ _ => rfl) φ).trans (h₁ φ.1 φ.2))
    have hA : ∀ m, cas (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (shift (lieA π Ξ) r) e m = c₁ • m := fun m => by
      induction m using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
      | tmul φ v =>
        have h := cas_inter e (lieOp π) (lieA π Ξ) ((TensorProduct.mk ℂ π.V (Fin Ξ.d → ℂ)).flip v) r
          (fun _ _ => rfl) φ
        rw [hπ, map_smul] at h
        exact h.symm
    refine ⟨c₂ - c₁, fun m => ?_⟩
    rw [LinearMap.sub_apply, hA, ← hB]
    exact (sub_smul c₂ c₁ m).symm
end
