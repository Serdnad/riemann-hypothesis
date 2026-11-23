module

public import Formalism.JumpKernelCokernel.Bundle001
public import Formalism.JumpKernelCokernel.JumpShiftProofs.Bundle001
public import Formalism.JumpKernelCokernel.JumpShiftProofs.Bundle003
public import Formalism.JumpKernelCokernel.JumpShiftProofs.Bundle002
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

namespace Formalism.KernelCokernelLengths.QuotientLengthJointLemmas

theorem quot_le (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R]
    (π : Module.End O R) (R' R'' : Submodule O R) (B : Type) [AddCommGroup B] [Module O B]
    (πB : Module.End O B) (j : ↥R'' →ₗ[O] B)
    (hstab : R''.map π ≤ R'') (hker : LinearMap.ker j = R'.comap R''.subtype)
    (hj : ∀ (x : ↥R'') (hx : π x ∈ R''), j ⟨π x, hx⟩ = πB (j x)) :
    Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) ≤
      Module.length O (↥(LinearMap.range j) ⧸
        ((LinearMap.range j).map πB).comap (LinearMap.range j).subtype) := by
  set K := (R' ⊔ R''.map π).comap R''.subtype with hK
  set L := ((LinearMap.range j).map πB).comap (LinearMap.range j).subtype with hL
  have hkerK : LinearMap.ker j ≤ K := by
    rw [hker]; exact Submodule.comap_mono le_sup_left
  let ψ : ↥(LinearMap.range j) →ₗ[O] ↥R'' ⧸ K :=
    (Submodule.factor hkerK).comp (j.quotKerEquivRange.symm : ↥(LinearMap.range j) →ₗ[O] ↥R'' ⧸ LinearMap.ker j)
  have hψ : ∀ y : ↥R'', ψ (j.rangeRestrict y) = K.mkQ y := by
    intro y
    have e : j.quotKerEquivRange.symm (j.rangeRestrict y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk j y).symm
    show Submodule.factor hkerK (j.quotKerEquivRange.symm (j.rangeRestrict y)) = K.mkQ y
    rw [e]
    exact Submodule.factor_mk hkerK y
  have hLψ : L ≤ LinearMap.ker ψ := by
    intro m hm
    obtain ⟨b, ⟨x, rfl⟩, hbm⟩ := hm
    have hpx : π x ∈ R'' := hstab ⟨x, x.2, rfl⟩
    have hy : j.rangeRestrict ⟨π x, hpx⟩ = m := Subtype.ext ((hj x hpx).trans hbm)
    rw [LinearMap.mem_ker, ← hy, hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right ⟨x, x.2, rfl⟩
  have hsurj : Function.Surjective (L.liftQ ψ hLψ) := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective K z
    exact ⟨L.mkQ (j.rangeRestrict y), by rw [Submodule.mkQ_apply, Submodule.liftQ_apply, hψ]⟩
  exact Module.length_le_of_surjective _ hsurj

end Formalism.KernelCokernelLengths.QuotientLengthJointLemmas

theorem Formalism.KernelCokernelLengths.lemma_D_joint_form : Formalism.KernelCokernelLengths.LemmaDJoint := by
  intro O _ R _ _ π R' R'' B _ _ πB j hle hstab hB hker hj
  have hN : (LinearMap.range j).map πB ≤ LinearMap.range j := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨⟨π x, hstab ⟨x, x.2, rfl⟩⟩, hj x _⟩
  calc _ ≤ _ := Formalism.KernelCokernelLengths.LengthSplittingLemmas.main O R π R' R'' hle
    _ ≤ _ := add_le_add le_rfl ((Formalism.KernelCokernelLengths.QuotientLengthJointLemmas.quot_le O R π R' R'' B πB j hstab hker hj).trans
          (Formalism.KernelCokernelLengths.KernelCokernelLemmas.main O B hB πB _ hN))
end

section

namespace Formalism.KernelCokernelLengths.RowDegreeJointLemmas

lemma aR_nonneg (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (H : ℕ) : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H := by
  unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
  have hl : (1:ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have t1 : 0 ≤ (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (sq_nonneg _)
  have t2 : 0 ≤ Real.logb (ℓ : ℝ) (2 * (H : ℝ)) := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · simp [h0]
    · have : (1:ℝ) ≤ H := by exact_mod_cast h0
      exact Real.logb_nonneg hl (by linarith)
  linarith

end Formalism.KernelCokernelLengths.RowDegreeJointLemmas

theorem Formalism.KernelCokernelLengths.row_degree_joint_form : Formalism.KernelCokernelLengths.RowDJoint := by
  refine ⟨1 / 100, by norm_num, 1000, ?_⟩
  intro ℓ hℓ b η S t bi h s₁ E e₂ hb hη hS ht h1 h2 h3
  intro η' a hs₁ hE he₂
  have hℓR : (11:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hbR : (1000:ℝ) ≤ b := by exact_mod_cast hb
  have h1R : (b:ℝ) ≤ bi + t + 1 := by exact_mod_cast h1
  have h2R : (bi:ℝ) + S ≤ h := by exact_mod_cast h2
  have h3R : (h:ℝ) ≤ b + η + t + S + 1 := by exact_mod_cast h3
  have hη' : (η' : ℝ) = η + t + 1 := by
    show ((η + t + 1 : ℕ) : ℝ) = _
    push_cast
    ring
  have hη0 : (0:ℝ) ≤ η := Nat.cast_nonneg _
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hS0 : (0:ℝ) ≤ S := Nat.cast_nonneg _
  have hA : 2 * η' ≤ h := by
    have : (2 * (η' : ℝ)) ≤ h := by rw [hη']; linarith
    exact_mod_cast this
  have hB : h ≤ 2 * bi := by
    have : (h : ℝ) ≤ 2 * bi := by linarith
    exact_mod_cast this
  have haR := Formalism.KernelCokernelLengths.RowDegreeJointLemmas.aR_nonneg ℓ hℓ (h + η')
  have ha : (a : ℝ) ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + η') + 1 := (Nat.ceil_lt_add_one haR).le
  have hC : 2 * a + η' + 1 ≤ bi := by
    have hHR : ((h + η' : ℕ) : ℝ) ≤ 1.05 * b + 2 := by push_cast; rw [hη']; linarith
    have hH1 : (1:ℝ) ≤ ((h + η' : ℕ) : ℝ) := by push_cast; rw [hη']; linarith
    have hfrac : (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ 21 / 100 := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have he5 : (100:ℝ) ≤ Real.exp 5 := by
      have e1 := Real.exp_one_gt_d9
      have e2 : (2.7:ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
      rw [← Real.exp_nat_mul] at e2
      norm_num at e2
      linarith
    have hlog : ∀ y : ℝ, 0 < y → Real.log y ≤ y / 100 + 4 := by
      intro y hy
      have h5 := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 5))
      rw [Real.log_div hy.ne' (Real.exp_pos 5).ne', Real.log_exp] at h5
      have : y / Real.exp 5 ≤ y / 100 := div_le_div_of_nonneg_left hy.le (by norm_num) he5
      linarith
    have hl11 : (2:ℝ) < Real.log ℓ := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have e1 := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [Real.exp_pos 1]
    have hlam : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam ℓ (h + η') ≤ ((h + η' : ℕ) : ℝ) / 100 + 3 := by
      unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
      have hy : (0:ℝ) < 2 * ((h + η' : ℕ) : ℝ) := by linarith
      have hlg := hlog _ hy
      have hlg0 : 0 ≤ Real.log (2 * ((h + η' : ℕ) : ℝ)) := Real.log_nonneg (by linarith)
      rw [Real.logb]
      have hdd : Real.log (2 * ((h + η' : ℕ) : ℝ)) / Real.log ℓ ≤ Real.log (2 * ((h + η' : ℕ) : ℝ)) / 2 :=
        div_le_div_of_nonneg_left hlg0 (by norm_num) hl11.le
      linarith
    have haR2 : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + η') ≤ 0.22 * ((h + η' : ℕ) : ℝ) + 6 := by
      unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR
      have : ((h + η' : ℕ) : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤
          ((h + η' : ℕ) : ℝ) * (21 / 100) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
      linarith
    have : (2 * (a : ℝ) + η' + 1) ≤ bi := by rw [hη'] at *; linarith
    exact_mod_cast this
  refine ⟨⟨hA, hB, hC⟩, ?_⟩
  exact Formalism.KernelCokernelLengths.row_degree_exponent ℓ hℓ h η' S bi a s₁ E e₂ hA (by omega) ha hs₁ hE he₂
end

section

open Polynomial Module

namespace Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem charpoly_of_range_le {R : Type} [CommRing R] [IsDomain R] {M : Type} [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    (S : Submodule R M) [Module.Free R S] [Module.Finite R S] [Module.Free R (M ⧸ S)]
    [Module.Finite R (M ⧸ S)] (d : Module.End R M) (hd : ∀ m, d m ∈ S) :
    d.charpoly = (d.restrict (p := S) (q := S) (fun x _ => hd x)).charpoly *
      X ^ finrank R (M ⧸ S) := by
  classical
  obtain ⟨g, hg⟩ := Module.projective_lifting_property S.mkQ LinearMap.id
    (Submodule.mkQ_surjective S)
  have hg' : ∀ x, S.mkQ (g x) = x := fun x => LinearMap.congr_fun hg x
  let pr : M →ₗ[R] M := LinearMap.id - g ∘ₗ S.mkQ
  have hmem : ∀ m, pr m ∈ S := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero]
    simp only [pr, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [Submodule.Quotient.mk_sub]
    have := hg' (S.mkQ m)
    simp only [Submodule.mkQ_apply] at this ⊢
    rw [this, sub_self]
  let F : M →ₗ[R] S × (M ⧸ S) :=
    LinearMap.prod (pr.codRestrict S hmem) S.mkQ
  let G : S × (M ⧸ S) →ₗ[R] M := S.subtype.coprod g
  have h1 : F ∘ₗ G = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨s, c⟩
    have hs : S.mkQ (s : M) = 0 := by simp
    have hs' : (Submodule.Quotient.mk (s : M) : M ⧸ S) = 0 := hs
    have hg'' : (Submodule.Quotient.mk (g c) : M ⧸ S) = c := hg' c
    apply Prod.ext
    · apply Subtype.ext
      simp [F, G, pr, hg', hs]
    · simp [F, G, pr, hs', hg'']
  have h2 : G ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    intro m
    simp [F, G, pr]
  let e : M ≃ₗ[R] S × (M ⧸ S) := LinearEquiv.ofLinearMap (f := F) (g := G) h1 h2
  let dS := d.restrict (p := S) (q := S) (fun x _ => hd x)
  let bS := Module.Free.chooseBasis R S
  let bQ := Module.Free.chooseBasis R (M ⧸ S)
  let b := bS.prod bQ
  have hconj : ∀ x, e.conj d x = (⟨d (G x), hd _⟩, 0) := by
    intro x
    rw [LinearEquiv.conj_apply]
    have hq : S.mkQ (d (G x)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hd _
    apply Prod.ext
    · apply Subtype.ext
      simp [e, F, pr, hq]
    · simp [e, F, pr, hq]
  have hM : LinearMap.toMatrix b b (e.conj d) =
      Matrix.fromBlocks (LinearMap.toMatrix bS bS dS) (LinearMap.toMatrix b b (e.conj d)).toBlocks₁₂
        0 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix b b (e.conj d))]
    congr 1
    · ext i j
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply, b,
        Module.Basis.prod_apply, Sum.elim_inl, hconj, Module.Basis.prod_repr_inl]
      congr 2
      apply Subtype.ext
      simp [G, dS]
    · ext i j
      simp [Matrix.toBlocks₂₁, LinearMap.toMatrix_apply, b, hconj]
    · ext i j
      simp [Matrix.toBlocks₂₂, LinearMap.toMatrix_apply, b, hconj]
  rw [← e.charpoly_conj d, ← LinearMap.charpoly_toMatrix (e.conj d) b, hM,
    Matrix.charpoly_fromBlocks_zero₂₁, LinearMap.charpoly_toMatrix, Matrix.charpoly_zero,
    Module.finrank_eq_card_chooseBasisIndex]

end Formalism.KernelCokernelLengths.CokernelTorsionLemmas

namespace Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem eq_of_mul_X_pow {R : Type} [CommRing R] [IsDomain R] (P Q : R[X]) (k r : ℕ)
    (hP : P.coeff 0 ≠ 0) (hQ : Q.coeff 0 ≠ 0) (h : P * X ^ r = X ^ k * Q) : P = Q := by
  have hP0 : P ≠ 0 := fun h0 => hP (by simp [h0])
  have hQ0 : Q ≠ 0 := fun h0 => hQ (by simp [h0])
  have tP : P.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP)
  have tQ : Q.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ)
  have hrk : r = k := by
    have h1 := congrArg Polynomial.natTrailingDegree h
    rw [mul_comm (X ^ k) Q, Polynomial.natTrailingDegree_mul_X_pow hP0,
      Polynomial.natTrailingDegree_mul_X_pow hQ0, tP, tQ] at h1
    omega
  subst hrk
  rw [mul_comm (X ^ r) Q] at h
  exact mul_right_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) h

end Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem Formalism.KernelCokernelLengths.cokernel_torsion_holds : Formalism.KernelCokernelLengths.CokerTors := by
  intro O _ _ _ M _ _ _ _ d k Q hQ0 hchar hann
  classical
  have hQc : Q.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]

  have hdQ : ∀ m, d (aeval d Q m) = 0 := by
    intro m
    have := LinearMap.congr_fun hann m
    simpa [map_mul, aeval_X] using this
  have hQd : ∀ m, aeval d Q (d m) = 0 := by
    intro m
    have h0 : aeval d (Q * X) = 0 := by rw [mul_comm]; exact hann
    have := LinearMap.congr_fun h0 m
    simpa [map_mul, aeval_X] using this

  have hsplit : ∀ m, aeval d Q m = Q.coeff 0 • m + d (aeval d Q.divX m) := by
    intro m
    conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
    rw [map_add (f := _), map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, add_comm]
  have hcommR : ∀ m, d (aeval d Q.divX m) = aeval d Q.divX (d m) := by
    intro m
    have h0 : aeval d (X * Q.divX) = aeval d (Q.divX * X) := by rw [mul_comm]
    have := LinearMap.congr_fun h0 m
    simpa [map_mul, aeval_X] using this
  let S : Submodule O M := LinearMap.ker (aeval d Q)
  have hdS : ∀ m, d m ∈ S := fun m => hQd m

  have htf : Module.IsTorsionFree O (M ⧸ S) := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun a x hx => ?_)
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        rw [Submodule.Quotient.mk_eq_zero]
        have : a • aeval d Q m = 0 := by
          rw [← map_smul]; exact hx
        exact (smul_eq_zero.mp this).resolve_left ha
  have : Module.Free O (M ⧸ S) := Module.free_of_finite_type_torsion_free'
  let dS := d.restrict (p := S) (q := S) (fun x _ => hdS x)
  have hc := Formalism.KernelCokernelLengths.CokernelTorsionLemmas.charpoly_of_range_le S d hdS

  have hker : LinearMap.ker dS = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    have hs1 : d (s : M) = 0 := by
      have := congrArg Subtype.val hs
      simpa [dS] using this
    have hs2 : aeval d Q (s : M) = 0 := s.2
    rw [hsplit, hcommR, hs1, map_zero (aeval d Q.divX), add_zero] at hs2
    exact Subtype.ext ((smul_eq_zero.mp hs2).resolve_left hQc)
  have hdet : LinearMap.det dS ≠ 0 := fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hker
  have hPc : dS.charpoly.coeff 0 ≠ 0 := by
    intro h; apply hdet; rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero]
  have hPQ : dS.charpoly = Q :=
    Formalism.KernelCokernelLengths.CokernelTorsionLemmas.eq_of_mul_X_pow _ _ k _ hPc hQc (hc.symm.trans hchar)
  have hspan : Ideal.span {LinearMap.det dS} = Ideal.span {Q.eval 0} := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, hPQ, Polynomial.coeff_zero_eq_eval_zero]
    exact Ideal.span_singleton_mul_left_unit ((isUnit_neg_one).pow _) _
  have hlen := Formalism.KernelCokernelLengths.determinant_length_formula O S dS hdet
  rw [hspan] at hlen
  rw [← hlen]

  have hmemT : ∀ s : S, (LinearMap.range d).mkQ (s : M) ∈
      Submodule.torsion O (M ⧸ LinearMap.range d) := by
    intro s
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨Q.coeff 0, mem_nonZeroDivisors_of_ne_zero hQc⟩, ?_⟩
    show Q.coeff 0 • (Submodule.Quotient.mk (s : M) : M ⧸ LinearMap.range d) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hs2 : aeval d Q (s : M) = 0 := s.2
    rw [hsplit] at hs2
    rw [eq_neg_of_add_eq_zero_left hs2]
    exact Submodule.neg_mem _ (LinearMap.mem_range_self d _)
  let φ : S →ₗ[O] Submodule.torsion O (M ⧸ LinearMap.range d) :=
    ((LinearMap.range d).mkQ ∘ₗ S.subtype).codRestrict _ hmemT
  have hφ : LinearMap.range dS ≤ LinearMap.ker φ := by
    rintro _ ⟨s, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show (LinearMap.range d).mkQ (d (s : M)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self d _
  refine Module.length_le_of_surjective ((LinearMap.range dS).liftQ φ hφ) ?_
  rintro ⟨x, hx⟩
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    rw [Submodule.mem_torsion_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨m', hm'⟩ := ha
    have h1 : (a : O) • aeval d Q m = 0 := by
      rw [← map_smul]
      show aeval d Q ((a : O) • m) = 0
      rw [show (a : O) • m = d m' from hm'.symm]; exact hQd m'
    have hmS : m ∈ S := (smul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero a)
    refine ⟨Submodule.Quotient.mk ⟨m, hmS⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    rfl
end
