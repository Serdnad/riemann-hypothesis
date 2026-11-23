module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle004
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

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem op_comm {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (k : GL (Fin a) (Af E)) (o : Op E a) (ho : ∀ k', o ≠ .fin k') : Commute (π.op o) (π.finPart k) := by
  have h : act o * act (.fin k) = act (.fin k) * act o := by
    cases o with
    | fin k' => exact (ho k' rfl).elim
    | cpt u =>
      change rt E a _ * rt E a _ = rt E a _ * rt E a _
      rw [← map_mul, ← map_mul]
      exact congrArg _ (infGL_comm _ _)
    | lie X => exact lie_rt_fin X k
  exact LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h x.1)

theorem UpperTheory.V.Lit.Bor.levelOp :
    UpperTheory.V.Lit.Bor.LevelOp := by
  intro E _ _ _ a U hU π hF φ hφ
  obtain ⟨p, hp1, hp2, hp3⟩ := UpperTheory.V.Lit.Bor.avgProj _ _ π.finPart U hU π.isSmooth_finPart
  have hc : ∀ (o : Op E a), (∀ k', o ≠ .fin k') → ∀ g, Commute (p * π.finPart g) (π.op o) := fun o ho g =>
    ((hp3 _ fun u _ => op_comm π u o ho).mul_right (op_comm π g o ho)).symm
  by_contra hne
  have hφ0 : ∀ g, (p * π.finPart g) φ = 0 := fun g => by
    by_contra h
    exact hne ⟨p * π.finPart g, h, fun k => hc _ (fun _ h => by cases h) g, fun ψ u hu => hp1 _ u hu⟩
  set N : Submodule ℂ π.V := ⨅ g, LinearMap.ker (p * π.finPart g) with hN
  have hm : ∀ x, x ∈ N ↔ ∀ g, (p * π.finPart g) x = 0 := fun x => by simp only [hN, Submodule.mem_iInf, LinearMap.mem_ker]
  have hs : ∀ o, ∀ x ∈ N, π.op o x ∈ N := fun o x hx => by
    rw [hm] at hx ⊢
    intro g
    by_cases ho : ∀ k', o ≠ .fin k'
    · have := LinearMap.congr_fun (hc o ho g).eq x
      rw [Module.End.mul_apply, Module.End.mul_apply (π.op o), hx g, map_zero] at this
      exact this
    · push Not at ho
      obtain ⟨k, rfl⟩ := ho
      have := hx (g * k)
      rw [map_mul] at this
      exact this
  rcases π.irred (N.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hs o x hx, rfl⟩) with e | e
  · have : φ.1 ∈ N.map π.V.subtype := ⟨φ, (hm φ).2 hφ0, rfl⟩
    rw [e, Submodule.mem_bot] at this
    exact hφ (Subtype.ext this)
  · obtain ⟨v, hv0, hv⟩ := hF
    have : v.1 ∈ N.map π.V.subtype := by rw [e]; exact v.2
    obtain ⟨w, hw, hwv⟩ := this
    obtain rfl : w = v := Subtype.ext hwv
    have h1 := (hm w).1 hw 1
    rw [map_one, mul_one, hp2 w hv] at h1
    exact hv0 h1
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.smForm :
    UpperTheory.V.Lit.Bor.SmForm := by
  intro E _ _ _ a Ξ r H G hH hG X x hx y hy
  set c : ℂ := ((2 * r * ell E a (toL X.1) : ℝ) : ℂ) with hc
  have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
  obtain ⟨h1, h2⟩ := UpperTheory.V.Lit.Bor.tformAdj (Sm E a) Ξ.d H (sqSub E a r) G (Ξ.dmat (toL X.1)) (Ξ.dmat (toL X.1))
    (lie E a (toL X.1)) (-lie E a (toL X.1) - c • 1)
  have hX : star X.1 = X.1 := X.2
  have e1 := h1 (by have := hG.adj X.1; rwa [hX] at this) x y
  have e2 := h2 (fun φ hφ ψ hψ => by
    have := hH.skew (toL X.1) φ hφ ψ hψ
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg,
      LinearMap.map_smulₛₗ, hcc, smul_eq_mul]
    rw [← hc] at this
    linear_combination this) x hx y hy
  have e3 : smLie Ξ (toL X.1) y = smA Ξ (toL X.1) y + smB Ξ (toL X.1) y := by
    simp [smB]
  have e4 : smAdj Ξ r (toL X.1) x = smB Ξ (toL X.1) x +
      (-lie E a (toL X.1) - c • (1 : Module.End ℂ (Sm E a))).rTensor _ x := by
    rw [smAdj, adj_apply, smA_apply, LinearMap.rTensor_sub, LinearMap.rTensor_neg, LinearMap.rTensor_smul,
      Module.End.one_eq_id, LinearMap.rTensor_id, ← algebraMap_smul ℂ (2 * r * ell E a (toL X.1)) x]
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [show algebraMap ℝ ℂ (2 * r * ell E a (toL X.1)) = c from rfl]
    abel
  rw [e3, e4, map_add (f := _), map_add (f := _), LinearMap.add_apply, smA_apply, smB_apply, e1, e2, add_comm]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem diff_translate {T : Type} [Fintype T] {a : ℕ} (Φ : (Fin a → Fin a → T → ℂ) → ℂ)
    (hΦ : DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)}) (A B : GL (Fin a) (T → ℂ)) :
    DifferentiableOn ℂ (fun x : Fin a → Fin a → T → ℂ => Φ (fun i j => (A.val * Matrix.of x * B.val) i j))
      {x | IsUnit (Matrix.of x)} := by
  have hd : Differentiable ℂ
      (fun x : Fin a → Fin a → T → ℂ => (fun i j => (A.val * Matrix.of x * B.val) i j : Fin a → Fin a → T → ℂ)) := by
    refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => differentiable_pi.2 fun t => ?_
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply]
    fun_prop
  refine hΦ.comp hd.differentiableOn fun x hx => ?_
  exact (A.isUnit.mul hx).mul B.isUnit

theorem UpperTheory.V.Lit.Bor.holId :
    UpperTheory.V.Lit.Bor.HolId := by
  intro E _ _ _ a
  have hv : ∀ y : GL (Fin a) (Cinf E),
      (GeneralLinearGroup.map (emb E) y).val = Matrix.of (fun i j => emb E (y.val i j)) := fun y => rfl
  let S : Submonoid (GL (Fin a) ((E →+* ℂ) → ℂ)) :=
    { carrier := {g | ∀ Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ,
        DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} →
        (∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = 0) → Φ (fun i j => g.val i j) = 0}
      one_mem' := fun Φ _ h0 => by
        have h := h0 1
        have e : (fun i j => emb E ((1 : GL (Fin a) (Cinf E)).val i j)) =
            fun i j => (1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val i j := by
          have := hv 1
          rw [map_one] at this
          exact this.symm
        rwa [e] at h
      mul_mem' := fun {g h} hg hh Φ hΦ h0 => by
        have h1 : ∀ y : GL (Fin a) (Cinf E),
            Φ (fun i j => ((GeneralLinearGroup.map (emb E) y).val * h.val) i j) = 0 := fun y => by
          have := hh _ (diff_translate Φ hΦ (GeneralLinearGroup.map (emb E) y) 1) fun z => by
            have h2 := h0 (y * z)
            have h3 := hv (y * z)
            rw [map_mul, Units.val_mul, hv z] at h3
            simp only [Units.val_one, mul_one, h3]
            exact h2
          simp only [Units.val_one, mul_one] at this
          exact this
        have := hg _ (diff_translate Φ hΦ 1 h) fun z => by
          simp only [Units.val_one, one_mul]
          exact h1 z
        simp only [Units.val_one, one_mul] at this
        exact this }
  intro Φ hΦ h0 g
  refine expGenPi _ a S (fun X y hy Ψ hΨ h1 => ?_) g Φ hΦ h0
  rw [hy]
  exact holIdExp E a Ψ hΨ h1 X
end
