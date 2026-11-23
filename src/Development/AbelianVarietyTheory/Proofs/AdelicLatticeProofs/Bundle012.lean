module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Circle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UTrans.IsoBasis

variable {E : Type} [Field E] {n : ℕ}

def hfL (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf σ G x y
  map_add' u v := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [hf, Finset.mul_sum, mul_assoc]

theorem hfL_apply (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    hfL σ G y x = hf σ G x y := rfl

theorem hf_symm {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) (x y : Fin n → E) :
    σ (hf σ G x y) = hf σ G y x := by

  simp only [hf, map_sum, map_mul, hG.invol, hG.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hfL_ne {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) {y : Fin n → E}
    (hy : y ≠ 0) : ∃ x, hfL σ G y x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hy
  have h0 : G.mulVec (fun b => σ (y b)) = 0 := by
    funext a
    have := h (Pi.single a 1)
    simpa [hfL_apply, hf, Pi.single_apply, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_irrel] using this
  have h1 := Matrix.eq_zero_of_mulVec_eq_zero hG.det_ne h0
  funext b
  have := congrFun h1 b
  simpa using this

theorem hf_comb {σ : E →+* E} (G : Matrix (Fin n) (Fin n) E) (a b : E) (u w : Fin n → E) :
    hf σ G (a • u + b • w) (a • u + b • w) =
      a * σ a * hf σ G u u + a * σ b * hf σ G u w + b * σ a * hf σ G w u + b * σ b * hf σ G w w := by
  simp only [hf, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem exists_isotropic_avoid [CharZero E] {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
    (hG : IsHerm σ G) (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0)
    {ι : Type} [Finite ι] (f : ι → (Fin n → E) →ₗ[E] E) (hf0 : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ z, hf σ G z z = 0 ∧ ∀ i, f i z ≠ 0 := by
  obtain ⟨w, hw0, hw⟩ := hz
  obtain ⟨c, hc⟩ := hG.ne_id
  set δ := c - σ c with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hc.symm
  have hδσ : σ δ = -δ := by simp [hδ, hG.invol]
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun o : Option ι => o.elim (hfL σ G w) f) (by
      rintro (_ | i)
      · exact hfL_ne hG hw0
      · exact hf0 i)
  have huw : hf σ G u w ≠ 0 := hu none
  have hui : ∀ i, f i u ≠ 0 := fun i => hu (some i)
  set a := hf σ G w u with ha
  have hσa : σ a = hf σ G u w := hf_symm hG _ _
  have ha0 : a ≠ 0 := by
    intro h; apply huw; rw [← hσa, h, map_zero]
  have huu : σ (hf σ G u u) = hf σ G u u := hf_symm hG _ _
  let bad : ι → E := fun i => (hf σ G u u / 2 - a * f i u / f i w) / δ
  have hfin : (Set.range bad).Finite := Set.finite_range bad
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : E) ∉ Set.range bad := by
    by_contra h
    push_neg at h
    exact (Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (t : E)) Nat.cast_injective h) hfin
  refine ⟨a • u + (-(hf σ G u u) / 2 + δ * t) • w, ?_, fun i => ?_⟩
  · rw [hf_comb, hw, ← ha, ← hσa]
    simp only [map_add (f := _), map_mul, map_div₀, map_neg, huu, hδσ, map_natCast, map_ofNat]
    ring
  · rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    by_cases h : f i w = 0
    · simp [h, ha0, hui i]
    · intro h'
      apply ht
      refine ⟨i, ?_⟩
      simp only [bad]
      field_simp
      linear_combination (-2 : E) * h'

theorem exists_isotropic_basis (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) (x y : Fin n → E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧
      ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  let S : Set (Fin n → E) := {z | hf σ G z z = 0 ∧ hf σ G x z ≠ 0 ∧ hf σ G y z ≠ 0}
  have hspan : Submodule.span E S = ⊤ := by
    by_contra h
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
    obtain ⟨z, hz0, hz1⟩ := exists_isotropic_avoid hG hz ![g, hfL σ G x, hfL σ G y] (by
      intro i
      fin_cases i
      · by_contra h
        push_neg at h
        exact hg0 (LinearMap.ext h)
      · exact hfL_ne hG hx
      · exact hfL_ne hG hy)
    have hzS : z ∈ S := by
      refine ⟨hz0, fun h => hz1 1 ?_, fun h => hz1 2 ?_⟩
      · show hf σ G z x = 0
        rw [← hf_symm hG, h, map_zero]
      · show hf σ G z y = 0
        rw [← hf_symm hG, h, map_zero]
    exact hz1 0 (hg (Submodule.subset_span hzS))
  obtain ⟨v, hvS, -, hv⟩ := Submodule.exists_fun_fin_finrank_span_eq E S
  have hn : n = Module.finrank E (Submodule.span E S) := by
    rw [hspan]; simp
  exact ⟨v ∘ Fin.cast hn, hv.comp _ (Fin.cast_injective hn), fun i => hvS _⟩

end GlobalTheory.UTrans.IsoBasis
end
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_monomial_eq_prod_X {σ : Type} (n : ℕ) : ∀ d : σ →₀ ℕ, d.degree = n →
    ∃ a : Fin n → σ, (MvPolynomial.monomial d (1 : ℂ)) = ∏ k, MvPolynomial.X (a k) := by
  classical
  induction n with
  | zero =>
    intro d hd
    rw [Finsupp.degree_eq_zero_iff] at hd
    subst hd
    exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro d hd
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    have hle : Finsupp.single i 1 ≤ d := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr hi
    obtain ⟨d', rfl⟩ := exists_add_of_le hle
    have hd' : d'.degree = n := by
      rw [map_add (f := _), Finsupp.degree_single] at hd
      omega
    obtain ⟨a, ha⟩ := ih d' hd'
    refine ⟨Fin.cons i a, ?_⟩
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← ha, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC, map_add (f := _)] at *
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul] at *
    rw [hp]
    simp [ltr, Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem evC_ext {f f' : MvPolynomial (ι × ι) ℂ} (h : ∀ y, evC f y = evC f' y) : f = f' := by
  apply MvPolynomial.funext
  intro x
  exact h (Matrix.of fun i j => x (i, j))

theorem tpow_mul_complex (n : ℕ) (y z : Matrix ι ι ℂ) : tpow n (y * z) = tpow n y * tpow n z := by
  ext a b
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

noncomputable def tensorForm (n : ℕ) (b : Fin n → ι) : ((Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ :=
  ∑ a : Fin n → ι, (LinearMap.proj a).smulRight (∏ k, MvPolynomial.X (a k, b k))

theorem tensorForm_apply (n : ℕ) (b : Fin n → ι) (l : (Fin n → ι) → ℂ) :
    tensorForm n b l = ∑ a : Fin n → ι, l a • ∏ k, MvPolynomial.X (a k, b k) := by
  simp [tensorForm, LinearMap.sum_apply]

theorem evC_tensorForm (n : ℕ) (b : Fin n → ι) (l : (Fin n → ι) → ℂ) (y : Matrix ι ι ℂ) :
    evC (tensorForm n b l) y = (l ᵥ* tpow n y) b := by
  rw [tensorForm_apply]

  simp [evC, tpow, Matrix.vecMul, dotProduct, map_sum, map_prod]

theorem ltr_tensorForms : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ), evC (ltr g f) y = evC f (g * y)) ∧ (∀ (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ), IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f) ∧ (∀ (g : Matrix ι ι ℂ) (n : ℕ) (f : MvPolynomial (ι × ι) ℂ), f.IsHomogeneous n → (ltr g f).IsHomogeneous n) ∧ ∀ n : ℕ, ∃ p : (Fin n → ι) → ((Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ, (∀ b l (y : Matrix ι ι ℂ), evC (p b l) y = (l ᵥ* tpow n y) b) ∧ (∀ b l (g : Matrix ι ι ℂ), ltr g (p b l) = p b (l ᵥ* tpow n g)) ∧ ∀ f : MvPolynomial (ι × ι) ℂ, f.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, f = ∑ b, p b (l b) := by
  intro ι _ _
  refine ⟨evC_ltr, ?_, ?_, ?_⟩
  · intro Γ f
    constructor
    · intro h g hg
      exact evC_ext fun y => by rw [evC_ltr, h g hg]
    · intro h g hg y
      rw [← evC_ltr, h g hg]
  · intro g n f hf
    have := hf.aeval (S := ℂ) (n := 1)
      (fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * MvPolynomial.X (k, ij.2)) (fun ij =>
        MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
    rw [one_mul] at this
    exact this
  · intro n
    refine ⟨tensorForm n, evC_tensorForm n, ?_, ?_⟩
    · intro b l g
      apply evC_ext
      intro y
      rw [evC_ltr, evC_tensorForm, evC_tensorForm, tpow_mul_complex, Matrix.vecMul_vecMul]
    · intro f hf
      let Φ : ((Fin n → ι) → (Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ :=
        ∑ b, (tensorForm n b).comp (LinearMap.proj b)
      have hΦ : ∀ l, Φ l = ∑ b, tensorForm n b (l b) := by
        intro l
        simp [Φ, LinearMap.sum_apply]
      suffices h : f ∈ LinearMap.range Φ by
        obtain ⟨l, hl⟩ := h
        exact ⟨l, by rw [← hΦ, hl]⟩
      rw [f.as_sum]
      refine Submodule.sum_mem _ fun d hd => ?_
      have hdeg : d.degree = n := by
        by_contra h
        exact (MvPolynomial.mem_support_iff.mp hd) (hf.coeff_eq_zero h)
      obtain ⟨a, ha⟩ := exists_monomial_eq_prod_X n d hdeg
      have h1 : MvPolynomial.monomial d (f.coeff d) = f.coeff d • MvPolynomial.monomial d (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [h1, ha]
      refine Submodule.smul_mem _ _ ⟨Pi.single (fun k => (a k).2) (Pi.single (fun k => (a k).1) 1), ?_⟩
      rw [hΦ, Finset.sum_eq_single (fun k => (a k).2)]
      · rw [Pi.single_eq_same, tensorForm_apply, Finset.sum_eq_single (fun k => (a k).1)]
        · simp
        · intro c _ hc
          simp [hc]
        · simp
      · intro c _ hc
        simp [hc]
      · simp

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open MvPolynomial

variable {ι : Type}

theorem evC_aeval_invariants {κ : Type} (Φ : κ → MvPolynomial (ι × ι) ℂ) (P : MvPolynomial κ ℂ)
    (y : Matrix ι ι ℂ) : evC (aeval Φ P) y = eval (fun k => evC (Φ k) y) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [evC, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p n hp => simp only [evC, map_mul, aeval_X, eval_X] at *; rw [hp]

theorem evC_det_generic [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) :
    evC (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det y = y.det := by
  unfold evC
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem exists_evC_eq_of_relations [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ]
    (Φ : κ → MvPolynomial (ι × ι) ℂ) (hR : IsReynolds Γ Rey) (hΦ : ∀ k, IsInv Γ (Φ k))
    (hgen : ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) (z : κ → ℂ)
    (hz : ∀ P : MvPolynomial κ ℂ, aeval Φ P = 0 → eval z P = 0) :
    ∃ y : Matrix ι ι ℂ, z = fun k => evC (Φ k) y := by
  set I : Ideal (MvPolynomial (ι × ι) ℂ) := Ideal.span (Set.range fun k => Φ k - C (z k)) with hI
  have hne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ I := h ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have hinv : ∀ k, IsInv Γ (Φ k - C (z k)) := by
      intro k g hg y
      have := hΦ k g hg y
      simp only [evC, map_sub, eval_C] at *
      rw [this]
    have hone : Rey 1 = 1 := hR.fix 1 (fun g hg y => by simp [evC])
    have h2 : ∑ k, (Φ k - C (z k)) * Rey (a k) = 1 := by

      rw [← hone, ← ha, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm (a k), hR.mul _ _ (hinv k)]
    have h3 : ∀ k, ∃ P : MvPolynomial κ ℂ, aeval Φ P = Rey (a k) := by
      intro k
      have := hgen _ (hR.inv (a k))
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    choose P hP using h3
    have h4 := hz (∑ k, (X k - C (z k)) * P k - 1) (by

      simp only [map_sub, map_sum, map_mul, aeval_X, aeval_C, map_one, hP, algebraMap_eq]
      rw [h2, sub_self])
    simp at h4
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨Matrix.of fun i j => x (i, j), funext fun k => ?_⟩
  have hk : Φ k - C (z k) ∈ M := hIM (Ideal.subset_span ⟨k, rfl⟩)
  rw [hx, mem_vanishingIdeal_singleton_iff] at hk
  simp only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, coe_aeval_eq_eval] at hk
  have : evC (Φ k) (Matrix.of fun i j => x (i, j)) = aeval x (Φ k) := rfl
  rw [this]
  exact (sub_eq_zero.1 hk).symm

theorem isClosed_image_invariants :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  intro ι _ _ Γ Rey κ _ Φ hR hdet hΦ hgen
  have hD : IsInv Γ (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det := by
    intro g hg y
    rw [evC_det_generic, evC_det_generic, det_mul, hdet g hg, one_mul]
  have hD' := hgen _ hD
  rw [Algebra.adjoin_range_eq_range_aeval] at hD'
  obtain ⟨Q, hQ⟩ := hD'
  have hQ' : ∀ y : Matrix ι ι ℂ, eval (fun k => evC (Φ k) y) Q = y.det := by
    intro y
    rw [← evC_aeval_invariants, ← evC_det_generic y, ← hQ]
    rfl
  have hset : {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} =
      {z | eval z Q = 1} ∩ ⋂ P : MvPolynomial κ ℂ, ⋂ _ : aeval Φ P = 0, {z | eval z P = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by rw [hQ', hy], fun P hP => ?_⟩
      rw [← evC_aeval_invariants, hP]
      simp [evC]
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := exists_evC_eq_of_relations Γ Rey κ Φ hR hΦ hgen z h2
      exact ⟨y, by rw [← hQ', h1], rfl⟩
  rw [hset]
  exact (isClosed_eq (MvPolynomial.continuous_eval Q) continuous_const).inter
    (isClosed_iInter fun P => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval P) continuous_const)

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isClosed_isLog : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by
  intro ι _ _
  let K : Set (Matrix ι ι ℂ) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1))
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D : K × (Matrix ι ι ℂ × Matrix ι ι ℂ) → ι → ℝ :=
    fun q i => (((q.1 : Matrix ι ι ℂ)ᴴ * q.2.1 * (q.1 : Matrix ι ι ℂ)) i i).re
  have hU : Continuous (fun q : K × (Matrix ι ι ℂ × Matrix ι ι ℂ) => (q.1 : Matrix ι ι ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hD : ∀ i, Continuous (fun q => D q i) := by
    intro i
    refine Complex.continuous_re.comp ?_
    exact ((hU.matrix_conjTranspose.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      hU).matrix_elem i i
  let S : Set (K × (Matrix ι ι ℂ × Matrix ι ι ℂ)) :=
    {q | (q.1 : Matrix ι ι ℂ) * (q.1 : Matrix ι ι ℂ)ᴴ = 1 ∧
      q.2.1 = (q.1 : Matrix ι ι ℂ) * diagonal (fun i => (D q i : ℂ)) * (q.1 : Matrix ι ι ℂ)ᴴ ∧
      q.2.2 = (q.1 : Matrix ι ι ℂ) * diagonal (fun i => (Real.exp (D q i) : ℂ)) *
        (q.1 : Matrix ι ι ℂ)ᴴ}
  have hS : IsClosed S := by
    refine IsClosed.inter (isClosed_eq (hU.matrix_mul hU.matrix_conjTranspose) continuous_const)
      (IsClosed.inter (isClosed_eq (continuous_fst.comp continuous_snd) ?_)
        (isClosed_eq (continuous_snd.comp continuous_snd) ?_))
    · refine (hU.matrix_mul (Continuous.matrix_diagonal ?_)).matrix_mul hU.matrix_conjTranspose
      exact continuous_pi fun i => Complex.continuous_ofReal.comp (hD i)
    · refine (hU.matrix_mul (Continuous.matrix_diagonal ?_)).matrix_mul hU.matrix_conjTranspose
      exact continuous_pi fun i =>
        Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hD i))
  have key : {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} = Prod.snd '' S := by
    ext p
    constructor
    · rintro ⟨U, d, h1, h2, h3⟩
      have hUK : U ∈ K := by
        intro i _ j _
        have hu : U ∈ Matrix.unitaryGroup ι ℂ := Matrix.mem_unitaryGroup_iff.mpr h1
        simpa using entry_norm_bound_of_unitary hu i j
      have h1' : Uᴴ * U = 1 := mul_eq_one_comm.mp h1
      have hd : D (⟨U, hUK⟩, p) = d := by
        funext i
        show ((Uᴴ * p.1 * U) i i).re = d i
        have : Uᴴ * p.1 * U = diagonal (fun i => (d i : ℂ)) := by
          rw [h2]
          calc Uᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ) * U
              = (Uᴴ * U) * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [h1']; simp
        rw [this]; simp
      refine ⟨(⟨U, hUK⟩, p), ⟨h1, ?_, ?_⟩, rfl⟩
      · rw [hd]; exact h2
      · rw [hd]; exact h3
    · rintro ⟨q, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨q.1, D q, h1, h2, h3⟩
  rw [key]
  exact isClosedMap_snd_of_compactSpace S hS

end GlobalTheory.ClassFin
end

section

open scoped Topology

theorem _root_.GlobalTheory.T.exists_continuous_circle_char_extension' : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (ψ : H →* Circle), IsOpen (H : Set G) → Continuous ψ → (∀ x : H, (x : G) ∈ N → ψ x = 1) → ∃ χ : G →* Circle, Continuous χ ∧ (∀ x ∈ N, χ x = 1) ∧ ∀ x : H, χ x = ψ x := by
  first | exact @GlobalTheory.exists_continuous_circle_char_extension | exact GlobalTheory.exists_continuous_circle_char_extension | (intros; apply GlobalTheory.exists_continuous_circle_char_extension <;> assumption)
end
