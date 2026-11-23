module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle003
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem midOf_zero (r : ℕ) : midOf (0 : Fin (r + 1 + 1)) = none := by
  unfold midOf
  rw [dite_eq_right]
  simp

theorem subY_X_zero (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) : subY A r (X (a, 0)) = X (a, 0) := by
  simp only [subY, aeval_X, midOf_zero]

theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

def dOneY (A : Type) [CommRing A] (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A)) :=
  fun s t => Fin.cases (Fin.cases 1 (fun _ => 0) t) (fun s' => Fin.cases 0 (fun t' => C (X (s', t'))) t) s

theorem det_dOneY (A : Type) [CommRing A] (r : ℕ) : (dOneY A r).det = C (detY A r) := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin r, dOneY A r i.succ 0 = 0 := fun i => rfl
  have h1 : dOneY A r 0 0 = 1 := rfl
  simp only [h0, h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  unfold detY
  have h := RingHom.map_det (C : MvPolynomial (Fin r × Fin r) A →+*
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A))
    (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
  refine Eq.trans ?_ h.symm
  congr 1

theorem subY_covY (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1 + 1)) :
    subY K r (covY K (r + 1) i) = C (detY K r) * map C (covY K (r + 1) i) := by
  unfold covY
  rw [map_mul, map_mul, map_pow, map_pow, map_neg, map_neg, map_one, map_one]
  have hA := AlgHom.map_det (subY K r)
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hB := RingHom.map_det (map (C : K →+* MvPolynomial (Fin r × Fin r) K))
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hM : (subY K r).mapMatrix
      (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      (map (C : K →+* MvPolynomial (Fin r × Fin r) K)).mapMatrix
        (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) *
        dOneY K r := by
    apply Matrix.ext
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    induction b using Fin.cases with
    | zero =>
      have h0 : ∀ s : Fin r, dOneY K r s.succ 0 = 0 := fun s => rfl
      have h1 : dOneY K r 0 0 = 1 := rfl
      simp only [h0, h1, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
      show subY K r (X (i.succAbove a, (0 : Fin (r + 1)).castSucc)) = map C (X (i.succAbove a, (0 : Fin (r + 1)).castSucc))
      rw [Fin.castSucc_zero, subY_X_zero, map_X]
    | succ j =>
      have h0 : dOneY K r 0 j.succ = 0 := rfl
      have h1 : ∀ s : Fin r, dOneY K r s.succ j.succ = C (X (s, j)) := fun s => rfl
      simp only [h0, h1, mul_zero, zero_add]
      show subY K r (X (i.succAbove a, j.succ.castSucc)) =
        ∑ s : Fin r, map C (X (i.succAbove a, s.succ.castSucc)) * C (X (s, j))
      have e : ∀ s : Fin r, s.succ.castSucc = midI r s := fun s => (Fin.succ_castSucc s).symm
      simp only [e, map_X]
      rw [subY_X_mid]
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hdet : subY K r (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      C (detY K r) * map C (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) := by
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, det_dOneY, mul_comm]
    congr 1
    exact hB.symm
  rw [hdet]
  ring

theorem subY_dPsi_monomial (K : Type) [Field K] (r : ℕ) (v : XY (r + 1 + 1) →₀ ℕ) (c : K) :
    subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) =
      C (detY K r ^ yDeg v) * map C (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) := by
  have hx : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inr i))) = covY K (r + 1) i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (r + 1 + 1) × Fin (r + 1 + 1) → Fin (r + 1 + 1) × Fin (r + 1 + 1)) = id := rfl
    rw [this, rename_id_apply]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, subY_X_zero, subY_covY, mul_pow, Finset.prod_mul_distrib, map_X]
  have hC : subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) = map C (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) := by
    simp only [← algebraMap_eq, AlgHom.commutes]
    simp [algebraMap_eq]
  rw [hC]
  have hp : ∏ i : Fin (r + 1 + 1), (C (detY K r) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (MvPolynomial (Fin r × Fin r) K)) ^ v (Sum.inr i) = C (detY K r) ^ yDeg v := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hp]
  ring

theorem subMuP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : SubMuP := by
  intro p n' R r hr P Q F hF
  rw [← tie3 h2 h5 hCO R (r + 1) (by omega) P Q] at hF
  obtain ⟨f, hf, rfl⟩ := hF
  rw [dPsi_apply, f.as_sum]

  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [subY_dPsi_monomial, (hf v hv).2]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem detY_ne_zero (K : Type) [Field K] (r : ℕ) : detY K r ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin r) K

theorem qPh_of (hTau : TauP) (hSm : SmithP) (hBil : BilinP) (hDet : DetFactsP) (hNum : NumP) (hDD : DetDivP) : QPh := by
  intro p n' R r hr a c N α hαA hαN hc hca
  letI := R.charZeroO
  haveI := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, he_def⟩ : ∃ e, α (Fin.last m) = e := ⟨_, rfl⟩
  have he : ∀ i, e ≤ α i := fun i => he_def ▸ hαA (Fin.le_last i)
  have hex : ∃ i, α i = e := ⟨_, he_def⟩
  have heN : e ≤ N := he_def ▸ hαN _
  have hγA : Antitone (fun i => α i - e) := by
    intro i j hij
    have := hαA hij
    show α j - e ≤ α i - e
    omega
  have wtK : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf},
      ν = ν' → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have wtO : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.O},
      ν = ν' → f ∈ dualWeyl R.O (m + 1) (m + 1) ν → f ∈ dualWeyl R.O (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have hwα : (fun j => (fun i => α i - e) j + e) = α := by
    funext j
    have := he j
    simp only
    omega
  obtain ⟨τ, hτK, hτO, hτsurj, hτeq⟩ := hTau R.O R.Kf hinj (m + 1) N e α (by omega) hαA hαN he hex
  obtain ⟨B, hBeq, hBint, nb, x, x', ka, hnb, hka, hx, hx', hdual⟩ :=
    hSm p n' R m (fun i => α i - e) hγA (by simp [he_def])
  set D : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := detY R.Kf (m + 1) ^ e with hD_def
  have hD0 : D ≠ 0 := pow_ne_zero _ (detY_ne_zero R.Kf _)
  let μ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := LinearMap.mulLeft R.Kf D
  have hμ : Function.Injective μ := fun u v h => mul_left_cancel₀ hD0 h
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (LinearMap.range μ)
  let σ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf :=
    (LinearEquiv.ofInjective μ hμ).symm.toLinearMap ∘ₗ (LinearMap.range μ).projectionOnto Cc hCc
  have hσ : ∀ g, σ (D * g) = g := by
    intro g
    have hmem : D * g ∈ LinearMap.range μ := ⟨g, rfl⟩
    show (LinearEquiv.ofInjective μ hμ).symm ((LinearMap.range μ).projectionOnto Cc hCc (D * g)) = g
    rw [show D * g = ((⟨D * g, hmem⟩ : LinearMap.range μ) : MvPolynomial _ _) from rfl,
      Submodule.linearProjOfIsCompl_apply_left hCc, LinearEquiv.symm_apply_eq]
    ext1
    rw [LinearEquiv.ofInjective_apply]
    rfl
  obtain ⟨L, hL⟩ := hBil R.Kf (m + 1) ((B.compl₂ τ) ∘ₗ σ)
  have hL' : ∀ f f', L ((blockEmb R.Kf true) f * (blockEmb R.Kf false) f') = B (σ f) (τ f') := by
    intro f f'
    rw [hL]
    rfl
  have hmapD : map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e) = D := by
    rw [map_pow, detY_map]
  have hdivK : ∀ f ∈ dualWeyl R.Kf (m + 1) (m + 1) α,
      ∃ g ∈ dualWeyl R.Kf (m + 1) (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    exact hDD R.Kf (m + 1) e (fun i => α i - e) (by omega) hγA f (wtK hwα.symm hf)
  have hdivO : ∀ f ∈ intO R.O (m + 1) α,
      ∃ g ∈ intO R.O (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    obtain ⟨fO, hfO, rfl⟩ := Submodule.mem_map.1 hf
    obtain ⟨gO, hgO, hfg⟩ := hDD R.O (m + 1) e (fun i => α i - e) (by omega) hγA fO (wtO hwα.symm hfO)
    refine ⟨map (algebraMap R.O R.Kf) gO, Submodule.mem_map.2 ⟨gO, hgO, rfl⟩, ?_⟩
    show map (algebraMap R.O R.Kf) fO = _
    rw [hfg, map_mul, hmapD]
  choose U hU hτU using fun a' => hτsurj (x' a') (hx' a')
  refine ⟨L, ?_, ?_, nb, fun b => D * x b, U, ka, ?_, ?_, ?_, hU, ?_⟩
  · intro l hl f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivK f hf
    rw [hL', hL', hσ]
    have hrD : rowAct R.Kf l (D * g) = D * (l.det ^ e • rowAct R.Kf l g) := by
      rw [map_mul, hD_def, map_pow, (hDet R.Kf (m + 1) e).2 l, MvPolynomial.smul_eq_C_mul, map_pow]
      ring
    rw [hrD, hσ, map_smul, LinearMap.smul_apply, hBeq, hτeq l hl f' hf', map_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' heN]
  · intro f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivO f hf
    rw [hL', hσ]
    exact hBint g hg (τ f') (hτO f' hf')
  · rw [hnb]
    unfold weylDim
    refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
    simp only [Nat.cast_sub (he i), Nat.cast_sub (he j), sub_sub_sub_cancel_right]
  · intro b
    refine (hka b).trans ?_
    have h1 := hc 0 (Fin.last m)
    exact hNum p a c (m + 1) (α 0 - e) R.std.1.prime.two_le (by omega) (by omega) hca
  · intro b
    obtain ⟨xO, hxO, hxe⟩ := Submodule.mem_map.1 (hx b)
    refine Submodule.mem_map.2 ⟨detY R.O (m + 1) ^ e * xO,
      wtO (by funext j; have := he j; simp only [Pi.add_apply]; omega)
        (dualWeyl_mul R.O (m + 1) (m + 1) _ _ (hDet R.O (m + 1) e).1 hxO), ?_⟩
    show map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e * xO) = D * x b
    rw [map_mul, hmapD, ← hxe]
    rfl
  · intro a' b
    rw [hL', hσ, hτU]
    exact hdual a' b

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems
open scoped TensorProduct

theorem bilinP : BilinP := by
  classical
  intro K _ r B
  let g : Bool → MvPolynomial (Fin r × Fin r) K →ₗ[K]
      (MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K) := fun b =>
    match b with
    | true => (Algebra.TensorProduct.includeLeft :
        MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K).toLinearMap
    | false => (Algebra.TensorProduct.includeRight :
        MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K).toLinearMap
  obtain ⟨F, hF⟩ := KP.tensorMap (K := K) (S := Bool) (α := Fin r × Fin r) g
  refine ⟨(TensorProduct.lift B) ∘ₗ F, ?_⟩
  intro f f'
  have h := hF (fun b => match b with | true => f | false => f')
  rw [Fintype.prod_bool, Fintype.prod_bool] at h
  have h' : F (blockEmb K true f * blockEmb K false f') = f ⊗ₜ[K] f' := by
    refine h.trans ?_
    show (f ⊗ₜ[K] (1 : MvPolynomial (Fin r × Fin r) K)) * ((1 : MvPolynomial (Fin r × Fin r) K) ⊗ₜ[K] f') = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [LinearMap.comp_apply, h', TensorProduct.lift.tmul]

theorem detFactsP : DetFactsP := by
  intro A _ r e
  constructor
  · have h1 : detY A r ∈ dualWeyl A r r (qcOm r r) := by
      rw [← qc_full_minor A r r le_rfl id strictMono_id rfl]
      exact qc_initMinor_mem A id le_rfl
    have h2 := qc_pow_mem A r r _ _ h1 e
    have e1 : e • qcOm r r = fun _ => e := by
      funext t
      simp [qcOm, t.isLt]
    rwa [e1] at h2
  · intro l
    unfold detY
    have hA := AlgHom.map_det (rowAct A (n := r) l) (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
    have hM : (rowAct A (n := r) l).mapMatrix (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A)) =
        (C : A →+* MvPolynomial (Fin r × Fin r) A).mapMatrix l *
          (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A)) := by
      apply Matrix.ext
      intro i j
      rw [Matrix.mul_apply]
      show rowAct A l (X (i, j)) = ∑ b, C (l i b) * X (b, j)
      simp [rowAct]
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, ← RingHom.map_det]
    rfl

theorem numP : NumP := by
  intro p a c r ell hp hr hl hc
  unfold N0 deF kappaOneExponent lgA
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hN : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by
    have h0 : r * (r - 1) / 2 ≤ (r + 1) ^ 2 := by
      calc r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
        _ ≤ (r + 1) * (r + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (r + 1) ^ 2 := by ring
    exact_mod_cast h0
  have h1 : Nat.log p (ell + r - 1) ≤ Nat.log p (8 * a + (r + 1)) := Nat.log_mono_right (by omega)
  have h2 : (Nat.log p (8 * a + (r + 1)) : ℝ) ≤ Real.logb p ((8 * a + (r + 1) : ℕ) : ℝ) := by
    first
    | exact Real.natLog_le_logb _ _
    | (have hpow := Nat.pow_log_le_self p (x := 8 * a + (r + 1)) (by omega)
       rw [Real.le_logb_iff_rpow_le hp1 (by positivity)]
       exact_mod_cast hpow)
  have h3 : (Nat.log p (ell + r - 1) : ℝ) ≤ Nat.log p (8 * a + (r + 1)) := by exact_mod_cast h1
  have hL : (Nat.log p (ell + r - 1) : ℝ) ≤ Real.logb p ((8 * a + (r + 1) : ℕ) : ℝ) + 1 := by linarith
  push_cast at hL hN
  have key : ((r * (r - 1) / 2 * Nat.log p (ell + r - 1) : ℕ) : ℝ) ≤
      ((r : ℝ) + 1) ^ 2 * (Real.logb p (8 * (a : ℝ) + ((r : ℝ) + 1)) + 1) := by
    push_cast
    exact mul_le_mul hN hL (Nat.cast_nonneg _) (by positivity)
  have key2 := key.trans (Nat.le_ceil _)
  push_cast at key2 ⊢
  exact_mod_cast key2

end Formalism.MainNotions.flipOneThree.Pf

end
end
