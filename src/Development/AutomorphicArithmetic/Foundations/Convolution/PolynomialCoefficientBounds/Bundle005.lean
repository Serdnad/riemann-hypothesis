module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem weightAbsEntrySum_nonneg {ι : Type} (p : MvPolynomial ι ℂ) : 0 ≤ l1 p := Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem intMvPolynomialCoeffAbsSum_add_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p + q) ≤ l1 p + l1 q := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).1

private theorem intMvPolynomialCoeffAbsSum_mul_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p * q) ≤ l1 p * l1 q := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).2.1

private theorem intMvPolynomialCoeffAbsSum_sum_le {ι κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) : l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (intMvPolynomialCoeffAbsSum_add_le _ _).trans (by linarith)

private theorem intMvPolynomialCoeffAbsSum_pow_le {ι : Type} (p : MvPolynomial ι ℂ) (b : ℕ) : l1 (p ^ b) ≤ l1 p ^ b := by
  induction b with
  | zero =>
    have := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι 0 0).2.2.2.1 (0 : ι →₀ ℕ) 1
    simp only [monomial_zero', C_1, norm_one] at this
    simpa [l1] using this.le
  | succ b ih => rw [pow_succ, pow_succ]; exact (intMvPolynomialCoeffAbsSum_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (weightAbsEntrySum_nonneg _))

theorem UpperTheory.ConvolutionTheory.FX.piece_size :
    ∀ (ι : Type) [Fintype ι] (f : EP ι), ∃ K : ℝ, ∀ k, l1 (piece k f) ≤ K ^ (k + 1) / k.factorial := by
  intro ι _ f
  suffices h : ∃ K : ℝ, 0 ≤ K ∧ ∀ k, l1 (piece k f) ≤ K ^ (k + 1) / k.factorial from h.imp fun _ h => h.2
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, le_rfl, fun k => by simp [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, l1]⟩
  | add f g hf hg =>
    obtain ⟨K, hK, h⟩ := hf
    obtain ⟨K', hK', h'⟩ := hg
    refine ⟨K + K', by positivity, fun k => ?_⟩
    rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).1]
    refine (intMvPolynomialCoeffAbsSum_add_le _ _).trans ((add_le_add (h k) (h' k)).trans ?_)
    rw [← add_div]
    gcongr
    exact pow_add_pow_le hK hK' (Nat.succ_ne_zero k)
  | single v p =>
    set D : ℝ := ((p.totalDegree.factorial : ℕ) : ℝ) with hDd
    set y := l1 (lin v)
    have hy : 0 ≤ y := weightAbsEntrySum_nonneg _
    have hp := weightAbsEntrySum_nonneg p
    have hD : 0 ≤ D := Nat.cast_nonneg _
    refine ⟨l1 p * D + (y + 1), by positivity, fun k => ?_⟩
    rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2]
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    have t : ∀ b ∈ Finset.range (k + 1), l1 (homogeneousComponent (k - b) p * (C ((b.factorial : ℂ)⁻¹) * lin v ^ b)) ≤
        l1 p * D / k.factorial * (y ^ b * 1 ^ (k - b) * k.choose b) := by
      intro b hb
      have hbk : b ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      by_cases hd : p.totalDegree < k - b
      · rw [homogeneousComponent_eq_zero _ p hd, zero_mul]
        simp only [l1, support_zero, Finset.sum_empty]
        exact mul_nonneg (div_nonneg (mul_nonneg hp hD) hk.le) (by positivity)
      · have h1 : l1 (homogeneousComponent (k - b) p) ≤ l1 p := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p p).2.2.2.2.1 _
        have h2 : l1 (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) ≤ (b.factorial : ℝ)⁻¹ * y ^ b := by
          have e : l1 (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) = ‖(b.factorial : ℂ)⁻¹‖ * l1 (lin v ^ b) :=
            (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι (lin v ^ b) p).2.2.1 _
          rw [e, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (intMvPolynomialCoeffAbsSum_pow_le _ _) (by positivity)
        have h3 : ((k - b).factorial : ℝ) ≤ D := Nat.cast_le.2 (Nat.factorial_le (not_lt.1 hd))
        have h4 : (k.factorial : ℝ) = k.choose b * b.factorial * (k - b).factorial := by
          exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hbk).symm
        have hb0 : (0 : ℝ) < b.factorial := by exact_mod_cast b.factorial_pos
        have hc0 : (0 : ℝ) < k.choose b := by exact_mod_cast Nat.choose_pos hbk
        have he0 : (0 : ℝ) < (k - b).factorial := by exact_mod_cast (k - b).factorial_pos
        refine (intMvPolynomialCoeffAbsSum_mul_le _ _).trans ((mul_le_mul h1 h2 (weightAbsEntrySum_nonneg _) hp).trans ?_)
        calc l1 p * ((b.factorial : ℝ)⁻¹ * y ^ b)
            = l1 p * (k - b).factorial / k.factorial * (y ^ b * 1 ^ (k - b) * k.choose b) := by
              rw [h4]; field_simp; simp
          _ ≤ _ := by gcongr
    refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ((Finset.sum_le_sum t).trans ?_)
    rw [← Finset.mul_sum, ← add_pow, div_mul_eq_mul_div, pow_succ']
    have : 0 ≤ l1 p * D := mul_nonneg hp hD
    refine div_le_div_of_nonneg_right (mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) k) (by positivity) (by linarith)) hk.le
end

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem UpperTheory.ConvolutionTheory.FX.aeval_single_zero {ι ι' : Type} (q : ι → MvPolynomial ι' ℂ)
    (p : MvPolynomial ι ℂ) :
    aeval (fun i => (AddMonoidAlgebra.single 0 (q i) : EP ι')) p
      = (AddMonoidAlgebra.single 0 (aeval q p) : EP ι') := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, aeval_C]
    rfl
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr, AddMonoidAlgebra.single_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]

private theorem UpperTheory.ConvolutionTheory.FX.lin_delta {ι ι' : Type} [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (i : ι) :
    lin (fun j => if δ i = j then (1 : ℝ) else 0) = (X (δ i) : MvPolynomial ι' ℂ) := by
  unfold lin
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem UpperTheory.ConvolutionTheory.FX.lin_push {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) :
    lin (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0)) = rename δ (lin v) := by
  unfold lin

  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, map_mul, rename_C, rename_X,
  Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem UpperTheory.ConvolutionTheory.FX.ren_single {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) (p : MvPolynomial ι ℂ) :
    ren δ (AddMonoidAlgebra.single v p : EP ι) =
      (AddMonoidAlgebra.single (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0))
        (rename δ p) : EP ι') := by
  have h1 : (fun i => (C ((0 : ι → ℂ) i) + lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i) :
      MvPolynomial ι' ℂ)) = X ∘ δ := by
    funext i
    have := UpperTheory.ConvolutionTheory.FX.lin_delta δ i
    simp only [Pi.zero_apply, map_zero, zero_add, Function.comp]
    exact this
  unfold ren aff lift
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change aeval (fun i => (AddMonoidAlgebra.single 0 (C ((0 : ι → ℂ) i) +
      lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i)) : EP ι')) p *
    (AddMonoidAlgebra.single (Matrix.vecMul v _) (C (expChar 0 (Multiplicative.ofAdd v))) : EP ι') = _
  rw [UpperTheory.ConvolutionTheory.FX.aeval_single_zero, h1, AddMonoidAlgebra.single_mul_single, zero_add]
  have h2 : expChar (0 : ι → ℂ) (Multiplicative.ofAdd v) = 1 := by simp [expChar]
  rw [h2, map_one, mul_one, rename_eq_aeval]

theorem UpperTheory.ConvolutionTheory.FX.piece_ren :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (k : ℕ), piece k (ren δ f) = rename δ (piece k f) := by
  intro ι _ f ι' _ _ δ k
  obtain ⟨ha, h0, hs⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι k
  obtain ⟨ha', h0', hs'⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι' k
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, h0, h0', map_zero]
  | add f g hf hg => rw [map_add (f := _), ha, ha', map_add (f := _), hf, hg]
  | single v p =>

    rw [UpperTheory.ConvolutionTheory.FX.ren_single, hs, hs', map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, map_pow, rename_C, UpperTheory.ConvolutionTheory.FX.lin_push, rename_homogeneousComponent]
end

section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ)
    (p : MvPolynomial ι ℂ) : lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem hom_ext {ι A : Type} [CommRing A] (f g : EP ι →+* A)
    (h1 : ∀ c : ℂ, f (AddMonoidAlgebra.single 0 (C c)) = g (AddMonoidAlgebra.single 0 (C c)))
    (h2 : ∀ i, f (AddMonoidAlgebra.single 0 (X i)) = g (AddMonoidAlgebra.single 0 (X i)))
    (h3 : ∀ v, f (AddMonoidAlgebra.single v 1) = g (AddMonoidAlgebra.single v 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun p => ?_) h3
  have : f.comp (AddMonoidAlgebra.singleZeroRingHom) = g.comp AddMonoidAlgebra.singleZeroRingHom :=
    MvPolynomial.ringHom_ext (fun c => h1 c) (fun i => h2 i)
  exact RingHom.congr_fun this p

theorem UpperTheory.ConvolutionTheory.FX.subst :
    PositivityTheory.Rg.Fx.Subst := by
  intro ι ι' _ _ Λ₀ M f
  refine ⟨fun lam => ?_, fun ι'' _ Λ₁ N => ?_⟩
  · refine RingHom.congr_fun (hom_ext ((ev lam).comp (aff Λ₀ M)) _ ?_ ?_ ?_) f
    · intro c
      simp [aff, ev, lift_single, AddMonoidAlgebra.coe_algebraMap]
    · intro i
      simp [aff, ev, lift_single, lin]
    · intro v
      simp only [aff, ev, lift_single, RingHom.comp_apply, map_one, one_mul, affChar, expChar, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, ← Complex.exp_add]
      congr 1
      simp only [Matrix.vecMul, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib, mul_assoc]
      rw [Finset.sum_comm]
  · refine RingHom.congr_fun (hom_ext ((aff Λ₁ N).comp (aff Λ₀ M)) _ ?_ ?_ ?_) f
    · intro c
      simp [aff, lift_single, AddMonoidAlgebra.coe_algebraMap]
    · intro i
      have e : ∀ p : MvPolynomial ι' ℂ, aeval (fun j => (AddMonoidAlgebra.single 0 (C (Λ₁ j) + lin (N j)) : EP ι'')) p =
          AddMonoidAlgebra.single 0 (aeval (fun j => (C (Λ₁ j) + lin (N j) : MvPolynomial ι'' ℂ)) p) := fun p => by
        induction p using MvPolynomial.induction_on with
        | C a => simp [AddMonoidAlgebra.coe_algebraMap]
        | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, AddMonoidAlgebra.single_add]
        | mul_X p j hp => rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]
      simp only [aff, lift_single, RingHom.comp_apply, aeval_X, ofAdd_zero, map_one, mul_one, e]
      congr 1

      simp only [lin, map_add (f := _), map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, Complex.ofReal_sum,
      Complex.ofReal_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc, add_assoc]
      rw [Finset.sum_comm (s := (Finset.univ : Finset ι''))]
    · intro v
      simp only [aff, lift_single, RingHom.comp_apply, map_one, one_mul, affChar, expChar, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, aeval_C, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add,
        algebraMap_eq, ← C_mul, ← Complex.exp_add, Matrix.vecMul_vecMul]
      congr 3
      simp only [Matrix.vecMul, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib, mul_assoc]
      rw [Finset.sum_comm]
end
