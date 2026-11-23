module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SelfAdj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.GalN.V

private theorem ratio_ne {A B q x y : ℝ} (hA : 0 < A) (hB : 0 < B) (hq : 1 < q) (h1 : A < q * B) (h2 : B < q * A)
    (h3 : A ^ 2 ≠ q * B ^ 2) (h4 : B ^ 2 ≠ q * A ^ 2)
    (hx : x = A / B ∨ x = 1 ∨ x = B / A) (hy : y = A / B ∨ y = 1 ∨ y = B / A) : x ≠ q * y := by
  have hAn : A ≠ 0 := hA.ne'
  have hBn : B ≠ 0 := hB.ne'
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> intro h <;> field_simp at h
  all_goals first
    | nlinarith
    | exact h3 (by nlinarith)
    | exact h4 (by nlinarith)

private theorem split_two {K : Type} [Field K] [IsAlgClosed K] (g : GL (Fin 2) K) :
    ∃ a b : Kˣ, (g : Matrix (Fin 2) (Fin 2) K).charpoly = (X - C (a : K)) * (X - C (b : K)) := by
  set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hM
  have hmon : M.charpoly.Monic := Matrix.charpoly_monic M
  have hsplit : M.charpoly.Splits := IsAlgClosed.splits _
  have hprod := hsplit.eq_prod_roots_of_monic hmon
  have hcard : M.charpoly.roots.card = 2 := by
    rw [← hsplit.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have hdet : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).mp (Units.isUnit g)
    exact this.ne_zero
  have hnz : ∀ c ∈ M.charpoly.roots, c ≠ 0 := by
    intro c hc h0
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly, h0] at hc
    apply hdet
    simpa [Matrix.det_neg] using hc
  have ha : a ≠ 0 := hnz a (by rw [hab]; simp)
  have hb : b ≠ 0 := hnz b (by rw [hab]; simp)
  refine ⟨Units.mk0 a ha, Units.mk0 b hb, ?_⟩
  rw [hprod, hab]
  simp

theorem UpperTheory.V.Z.Sym.Unl.adUnl :
    UpperTheory.V.Z.Sym.Unl.AdUnl := by
  intro F Ω _ _ _ _ _ l _ ι r hR hN w hw A hA _
  obtain ⟨s, hs⟩ := exists_isFrob hA
  refine ⟨s, 1, le_rfl, by simpa using hs, ?_⟩
  intro α β hα hβ k hk heq
  obtain ⟨a, b, hab⟩ := split_two (r s)
  have hc := (ad0Facts l (G F Ω) r).2.2.2.2.1 s a b hab
  have ra : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (a : Qbar l) := by
    rw [hab]; simp
  have rb : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (b : Qbar l) := by
    rw [hab]; simp
  have hA0 : 0 < ‖ι (a : Qbar l)‖ := norm_pos_iff.2 (by simp)
  have hB0 : 0 < ‖ι (b : Qbar l)‖ := norm_pos_iff.2 (by simp)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := hR w hw A hA s hs _ _ ra ra
    by_contra h
    nlinarith [not_lt.mp h]
  have root : ∀ x : Qbar l, (ad0 r s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly.IsRoot x →
      ‖ι x‖ = ‖ι (a : Qbar l)‖ / ‖ι (b : Qbar l)‖ ∨ ‖ι x‖ = 1 ∨ ‖ι x‖ = ‖ι (b : Qbar l)‖ / ‖ι (a : Qbar l)‖ := by
    intro x hx
    rw [hc] at hx
    simp only [IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hx
    rcases hx with (rfl | rfl) | rfl
    · left; simp
    · right; left; simp
    · right; right; simp
  have hn : ‖ι α‖ ^ k = (((normV w : ℕ) : ℝ) * ‖ι β‖) ^ k := by
    have := congrArg (fun z => ‖ι z‖) heq
    simpa [map_pow, map_mul, norm_pow, norm_mul, Complex.norm_natCast] using this
  have hn' : ‖ι α‖ = ((normV w : ℕ) : ℝ) * ‖ι β‖ :=
    (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by omega)).1 hn
  exact ratio_ne hA0 hB0 hq (hR w hw A hA s hs _ _ ra rb) (hR w hw A hA s hs _ _ rb ra)
    (hN w hw A hA s hs _ _ ra rb) (hN w hw A hA s hs _ _ rb ra) (root α hα) (root β hβ) hn'
end

section

open Finset UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have h1 : ZMod.dft (χ : ZMod N → ℂ) = fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar :=
    funext fun k => hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h2 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [h1, ZMod.dft_mul_const (fun k => χ⁻¹ (-k)), ZMod.dft_comp_neg (fun k => χ⁻¹ k)] at h2
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at h2
  have h3 := hi.fourierTransform_eq_inv_mul_gaussSum 1
  rw [inv_inv] at h3
  have h4 : ZMod.dft (fun k => χ⁻¹ k) 1 = χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar := h3
  rw [h4] at h2
  rw [← h2]; ring

private theorem gauss_inv_ne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
  intro h
  have := gauss_mul_gauss_inv χ hχ
  rw [h, mul_zero, zero_mul] at this
  exact (NeZero.ne N) (by exact_mod_cast this.symm)

private theorem map_Lk (σ : ℂ ≃+* ℂ) (k : ℕ) (x : ℂ) : σ (Lk k x) = Lk k (σ x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (σ.toRingHom.toIntAlgHom) x (numL k)).symm

private theorem cj_inv_apply {N : ℕ} (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    σ (χ⁻¹ a) = (cj σ χ)⁻¹ a := by
  rw [MulChar.inv_apply, MulChar.inv_apply]
  rfl

private theorem sum_conj {N : ℕ} [NeZero N] (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) (s : (ZMod N)ˣ)
    (hs : ∀ b : ZMod N, σ (ZMod.stdAddChar b : ℂ) = (ZMod.stdAddChar ((s : ZMod N) * b) : ℂ))
    (F : ℂ → ℂ) (hF : ∀ x, σ (F x) = F (σ x)) :
    σ (∑ a : ZMod N, χ⁻¹ a * F (ZMod.stdAddChar a : ℂ)) =
      (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * ∑ a : ZMod N, (cj σ χ)⁻¹ a * F (ZMod.stdAddChar a : ℂ) := by

  rw [map_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulLeft s) _ _ fun a => ?_
  have hu : (Units.mulLeft s a : ZMod N) = (s : ZMod N) * a := rfl
  rw [map_mul, hF, hs, cj_inv_apply, hu, ← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul]

theorem constCj : ConstCj := by
  intro N k _ hN χ hχ σ c c' h1 h2
  obtain ⟨s, hs, -⟩ := eisCj N hN σ
  have hG := sum_conj σ χ s hs id (fun _ => rfl)
  have hS := sum_conj σ χ s hs (Lk k) (map_Lk σ k)
  simp only [id] at hG
  have hG' : σ (gaussSum χ⁻¹ ZMod.stdAddChar) =
      (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar := hG
  have hne : (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar ≠ 0 := by
    rw [← hG']
    exact (map_ne_zero σ).2 (gauss_inv_ne χ hχ)
  have h3 := congrArg σ h1
  rw [hS, ← h2, map_mul, map_mul, hG', map_ofNat] at h3
  have h4 : ((cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar) * (2 * σ c) =
      ((cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar) * (2 * c') := by
    linear_combination h3
  have h5 := mul_left_cancel₀ hne h4
  have h6 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact (mul_left_cancel₀ h6 h5).symm

end UpperTheory.V.Z.Sym.Unl
end

section

noncomputable section

namespace UpperTheory.V.Z.Sym.Unl

theorem goodHalf : GoodHalf := by
  intro k N _ hk χ hχ g hg p hp hpN α β hs hm
  obtain ⟨σ, hσ⟩ := sqrtFlip p hp
  obtain ⟨g', hg'⟩ := conjEig k N χ g hg σ
  have hu : IsUnit ((p : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  have h1 : ‖χ (p : ZMod N)‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one χ hu.unit
    simpa using this
  have e : cj σ χ (p : ZMod N) = σ (χ (p : ZMod N)) := rfl
  have h2 : ‖σ (χ (p : ZMod N))‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one (cj σ χ) hu.unit
    rw [IsUnit.unit_spec, e] at this
    exact this
  have a1 := selfAdj k N hk χ hχ g p hp hpN
  have a2 := selfAdj k N hk (cj σ χ) (primCj N χ σ hχ) g' p hp hpN
  rw [hg' p hp.one_lt.le, e] at a2
  exact halfAlg p (k - 1) (g.a p) (χ (p : ZMod N)) α β σ hp.two_le h1 h2 hσ a1 a2 hs hm

end UpperTheory.V.Z.Sym.Unl
end
end
