module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle043
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle001
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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

open Matrix Polynomial NumberField IsDedekindDomain UpperTheory.ConvolutionTheory.D
open scoped TensorProduct

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ} (σ : R ≃ₐ[k] R)

private theorem sg_succ (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg (σ ^ m) (sg σ x) := by
  rw [pow_succ]
  rfl

private theorem sg_succ' (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg σ (sg (σ ^ m) x) := by
  rw [pow_succ']
  rfl

private theorem sg_one (x : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) x = x := rfl

private theorem nm_succ (m : ℕ) (δ : GL (Fin n) R) : nm σ (m + 1) δ = nm σ m δ * sg (σ ^ m) δ := by
  simp [nm, List.range_succ]

private theorem nm_conj (m : ℕ) (x δ : GL (Fin n) R) : nm σ m (sgConj σ x δ) = x⁻¹ * nm σ m δ * sg (σ ^ m) x := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, nm_succ, ih, sgConj, map_mul, map_mul, map_inv, sg_succ]
    group

private theorem sg_nm (m : ℕ) (δ : GL (Fin n) R) : sg σ (nm σ m δ) = δ⁻¹ * nm σ m δ * sg (σ ^ m) δ := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, map_mul, ih, ← sg_succ']
    group

end

theorem UpperTheory.ConvolutionTheory.D.nmPoly :
    UpperTheory.ConvolutionTheory.D.NmPoly := by
  intro k R _ _ _ σ q h n δ
  refine ⟨?_, fun x => by rw [nm_conj, h.pow, sg_one]⟩
  have e : (cp (nm σ q δ)).map (σ : R →+* R) = cp (nm σ q δ) := by
    have h1 := sg_nm σ q δ
    rw [h.pow, sg_one] at h1
    have h2 : cp (sg σ (nm σ q δ)) = (cp (nm σ q δ)).map (σ : R →+* R) := Matrix.charpoly_map _ _
    rw [← h2, h1, cp, cp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hl : cp (nm σ q δ) ∈ Polynomial.lifts (algebraMap k R) := (Polynomial.lifts_iff_coeff_lifts _).2 fun i =>
    h.fix _ (by simpa [Polynomial.coeff_map] using congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) e)
  obtain ⟨p, hp⟩ := hl
  exact ⟨p, Polynomial.monic_of_injective h.inj (by rw [show p.map (algebraMap k R) = _ from hp]; exact Matrix.charpoly_monic _), hp.symm⟩
end

section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section SlopeTestRemainingChoices

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]

private lemma tr_mem {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) (y : R) :
    ∃ t : k, algebraMap k R t = ∑ j ∈ Finset.range q, (σ ^ j) y := by
  apply h.fix

  rw [map_sum]
  have h1 := Finset.sum_range_succ (fun j => (σ ^ j) y) q
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) y) q
  rw [h2, h.pow, pow_zero] at h1
  have h3 := add_right_cancel h1
  rw [← h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

private lemma expand {σ : R ≃ₐ[k] R} {q s : ℕ} (hq : 0 < q) {x y : Fin s → R}
    (hs : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0) (r : R) :
    ∑ i, (∑ j ∈ Finset.range q, (σ ^ j) (y i * r)) * x i = r := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ j ∈ Finset.range q, ∑ i, (σ ^ j) (y i * r) * x i = if j = 0 then r else 0 := by
    intro j hj
    have := hs j (Finset.mem_range.1 hj)
    have h2 : ∑ i, (σ ^ j) (y i * r) * x i = (∑ i, x i * (σ ^ j) (y i)) * (σ ^ j) r := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    rw [h2, this]
    split_ifs with h0
    · simp [h0]
    · simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' ]
  simp [hq]

private def phi (σ : R ≃ₐ[k] R) (q : ℕ) : R ⊗[k] R →ₐ[R] (Fin q → R) :=
  Algebra.TensorProduct.lift (Algebra.ofId R (Fin q → R))
    (Pi.algHom k _ fun j : Fin q => ((σ ^ (j : ℕ) : R ≃ₐ[k] R) : R →ₐ[k] R)) fun _ _ => Commute.all _ _

private lemma phi_tmul (σ : R ≃ₐ[k] R) (q : ℕ) (a b : R) (j : Fin q) :
    phi σ q (a ⊗ₜ b) j = a * (σ ^ (j : ℕ)) b := by
  simp [phi, Algebra.ofId_apply]

private lemma phi_inj {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Function.Injective (phi σ q) := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  have key : ∀ z : R ⊗[k] R, ∑ i, (∑ j : Fin q, (σ ^ (j : ℕ)) (y i) * phi σ q z j) ⊗ₜ[k] x i = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      simp only [map_add (f := _), Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul, hu, hv]
    | tmul a b =>
      choose t ht using fun i => tr_mem h (y i * b)
      have hb := expand h.pos hs b
      conv_rhs => rw [← hb, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ht, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ht,
        Finset.sum_range, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [phi_tmul, map_mul]; ring
  intro u v huv
  rw [← key u, ← key v, huv]

private lemma phi_surj {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Function.Surjective (phi σ q) := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  have key : ∀ m j : Fin q, phi σ q (∑ i, x i ⊗ₜ[k] (σ ^ (q - m)) (y i)) j = if j = m then 1 else 0 := by
    intro m j

    rw [map_sum, Finset.sum_apply]
    simp_rw [phi_tmul, ← AlgEquiv.mul_apply, ← pow_add]
    rw [pow_eq_pow_mod _ h.pow, hs _ (Nat.mod_lt _ h.pos)]
    have hm := m.2
    have hj := j.2
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff]
    rcases lt_or_ge (j : ℕ) m with hl | hl
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  intro f
  refine ⟨∑ m : Fin q, f m • ∑ i, x i ⊗ₜ[k] (σ ^ (q - m)) (y i), ?_⟩
  funext j

  rw [map_sum, Finset.sum_apply]
  simp_rw [map_smul, Pi.smul_apply, key]
  simp

private lemma fin {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Module.Finite k R := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  refine Module.Finite.of_surjective (Fintype.linearCombination k x) fun b => ?_
  choose t ht using fun i => tr_mem h (y i * b)
  refine ⟨t, ?_⟩
  rw [Fintype.linearCombination_apply]
  simp_rw [Algebra.smul_def, ht]
  exact expand h.pos hs b

private lemma norm_pi {q : ℕ} (f : Fin q → R) : Algebra.norm R f = ∏ j, f j := by
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun R (Fin q)), ← Matrix.det_diagonal]
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.normProd :
    UpperTheory.ConvolutionTheory.D.NormProd := by
  intro k R _ _ _ _ σ q h r
  haveI := UpperTheory.ConvolutionTheory.D.fin h
  have h1 : algebraMap k R (Algebra.norm k r) = Algebra.norm R ((1 : R) ⊗ₜ[k] r) := by
    rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
    congr 1
    ext b
    simp
  let e := AlgEquiv.ofBijective (UpperTheory.ConvolutionTheory.D.phi σ q) ⟨UpperTheory.ConvolutionTheory.D.phi_inj h, UpperTheory.ConvolutionTheory.D.phi_surj h⟩
  rw [h1, ← Algebra.norm_eq_of_algEquiv e, UpperTheory.ConvolutionTheory.D.norm_pi, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (UpperTheory.ConvolutionTheory.D.phi_tmul σ q 1 r j).trans (one_mul _)
end

section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section
variable {R : Type} [CommRing R] {n : ℕ}

private def kry (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (g ^ (j : ℕ) *ᵥ v) i

private noncomputable def pol (c : Fin n → R) : R[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)

private theorem kry_mulVec (g : Matrix (Fin n) (Fin n) R) (v c : Fin n → R) :
    kry g v *ᵥ c = aeval g (pol c) *ᵥ v := by

  rw [pol, map_sum, Matrix.sum_mulVec]
  funext i
  rw [Finset.sum_apply]
  simp only [aeval_monomial, ← Algebra.smul_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, kry, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem pol_coeff (p : R[X]) (h : p.degree < n) : pol (fun i : Fin n => p.coeff i) = p := by
  simp only [pol]
  exact sum_fin (fun i a => monomial i a) (by simp) h |>.trans (sum_monomial_eq p)

private theorem aeval_mulVec [Nontrivial R] (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (p : R[X]) :
    aeval g p *ᵥ v = kry g v *ᵥ fun i : Fin n => (p %ₘ g.charpoly).coeff i := by
  rw [kry_mulVec, pol_coeff, ← Matrix.aeval_eq_aeval_mod_charpoly]
  have := degree_modByMonic_lt p g.charpoly_monic
  rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this

private theorem mul_kry [Nontrivial R] (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    g * kry g v = kry g v * Matrix.of fun i j : Fin n => ((X ^ ((j : ℕ) + 1) : R[X]) %ₘ g.charpoly).coeff i := by
  ext i j
  have := congrFun (aeval_mulVec g v (X ^ ((j : ℕ) + 1))) i
  rw [map_pow, aeval_X, pow_succ', ← Matrix.mulVec_mulVec] at this
  exact this

end

section
variable {K : Type} [Field K] {n : ℕ}

end

private theorem exists_kry {R : Type} [CommRing R] [Finite (MaximalSpectrum R)] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (h : g.charpoly.Separable) : ∃ v, IsUnit (kry g v).det :=
  _root_.UpperTheory.Reformulated.B.G8.exists_kry g h

end UpperTheory.ConvolutionTheory.D

open UpperTheory.ConvolutionTheory.D in
theorem UpperTheory.ConvolutionTheory.D.conjSep :
    UpperTheory.ConvolutionTheory.D.ConjSep := by
  intro k R _ _ _ _ _ n g h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨fun g' _ => ⟨1, Subsingleton.elim _ _⟩, fun y _ => ⟨0, Subsingleton.elim _ _⟩,
      fun p => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩⟩
  have := PositivityTheory.UnitarySelfGeneration.free_semilocal k R
  obtain ⟨v, hv⟩ := exists_kry g h
  obtain ⟨P, hP⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv
  refine ⟨fun g' hg => ?_, fun y hy => ?_, fun p => ⟨fun hp => ?_, ?_⟩⟩
  · obtain ⟨v', hv'⟩ := exists_kry g' (hg ▸ h)
    obtain ⟨Q, hQ⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv'
    have h1 := mul_kry g v
    have h2 := mul_kry g' v'
    rw [hg, ← hQ] at h2
    rw [← hP] at h1
    refine ⟨P * Q⁻¹, ?_⟩
    rw [Units.val_mul, ← mul_assoc, h1, mul_assoc, mul_assoc]
    congr 1
    rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, h2, Units.inv_mul_cancel_left]
  · let c := (P⁻¹).val *ᵥ (y *ᵥ v)
    have h1 : aeval g (pol c) *ᵥ v = y *ᵥ v := by
      rw [← kry_mulVec, ← hP, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    refine ⟨pol c, (Units.mul_left_inj P).1 ?_⟩
    rw [hP]
    ext i j
    have c1 : y * g ^ (j : ℕ) = g ^ (j : ℕ) * y := (Commute.pow_right hy j).eq
    have c2 : aeval g (pol c) * g ^ (j : ℕ) = g ^ (j : ℕ) * aeval g (pol c) := by
      rw [← aeval_X_pow (R := R), ← map_mul, ← map_mul, mul_comm]
    change (y *ᵥ (g ^ (j : ℕ) *ᵥ v)) i = (aeval g (pol c) *ᵥ (g ^ (j : ℕ) *ᵥ v)) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, c1, c2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]
  · have h1 := aeval_mulVec g v p
    rw [hp, Matrix.zero_mulVec, ← hP] at h1
    have h2 := congrArg (fun z => (P⁻¹).val *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [← modByMonic_eq_zero_iff_dvd g.charpoly_monic]
    have h3 := degree_modByMonic_lt p g.charpoly_monic
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at h3
    rw [← pol_coeff _ h3, ← h2]
    simp [pol]
  · rintro ⟨q, rfl⟩
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]
end
