module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DerivationAlgebraicIndependence

open MvPolynomial

theorem derivation_aeval_eq {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    (d : Derivation K R R) (z : ι → R) (P : MvPolynomial ι K) :
    d (aeval z P) = ∑ i, aeval z (pderiv i P) * d (z i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, smul_eq_mul, pderiv_X, Pi.single_apply,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [map_add (f := _), map_mul, aeval_X, apply_ite (aeval z), map_zero, map_one, add_mul, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring

theorem totalDegree_pderiv_lt {K ι : Type*} [CommRing K] (P : MvPolynomial ι K) (i : ι)
    (hP : 0 < P.totalDegree) : (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hsum : pderiv i P = ∑ m ∈ P.support, pderiv i (monomial m (AddMonoidAlgebra.coeff P m)) := by
    conv_lhs => rw [P.as_sum]

    rw [map_sum]
  rw [hsum]
  refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_lt_iff hP]
  intro m hm
  rw [pderiv_monomial]
  by_cases hmi : m i = 0
  · simp [hmi, hP]
  · have hm1 : m = (m - Finsupp.single i 1) + Finsupp.single i 1 := by
      ext k
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hk]
    have key : ((m - Finsupp.single i 1).sum fun _ e => e) + 1 = m.sum fun _ e => e := by
      conv_rhs => rw [hm1]
      rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl]
    have hle : (m.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hm
    refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
    show ((m - Finsupp.single i 1).sum fun _ e => e) < _
    omega

theorem eq_C_of_pderiv_eq_zero {K ι : Type*} [Field K] [CharZero K] (P : MvPolynomial ι K)
    (h : ∀ i, pderiv i P = 0) : P.totalDegree = 0 := by
  classical
  by_contra hne
  obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support
    (Finset.nonempty_of_ne_empty (by rintro hs; apply hne; simp [totalDegree, hs]))
    (fun s => s.sum fun _ e => e)
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    simpa [totalDegree] using hmd
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm0 (Finsupp.ext hc)
  have hc := congrArg (AddMonoidAlgebra.coeff · (m - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have hm' : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    ext k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hk]
  rw [hm'] at hc
  rcases mul_eq_zero.mp hc with h1 | h1
  · exact (mem_support_iff.mp hm) h1
  · exact Nat.cast_add_one_ne_zero _ h1

theorem algebraicIndependent_of_derivations {K R ι J : Type*} [Field K] [CharZero K] [CommRing R]
    [Nontrivial R] [Algebra K R] [Fintype ι] (z : ι → R) (δ : J → Derivation K R R)
    (h : ∀ c : ι → R, (∀ j, ∑ i, c i * δ j (z i) = 0) → ∀ i, c i = 0) :
    AlgebraicIndependent K z := by
  classical
  rw [algebraicIndependent_iff]
  suffices H : ∀ n (P : MvPolynomial ι K), P.totalDegree = n → aeval z P = 0 → P = 0 from
    fun P => H _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP
  have hd : ∀ i, pderiv i P = 0 := by
    have hv : ∀ i, aeval z (pderiv i P) = 0 :=
      h (fun i => aeval z (pderiv i P)) (fun j => by rw [← derivation_aeval_eq, hP, map_zero])
    intro i
    by_cases h0 : P.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C] at h0
      rw [h0]
      simp
    · exact ih _ (hn ▸ totalDegree_pderiv_lt P i (Nat.pos_of_ne_zero h0)) _ rfl (hv i)
  have h0 := eq_C_of_pderiv_eq_zero P hd
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  rw [h0, aeval_C] at hP
  have hc : AddMonoidAlgebra.coeff P 0 = 0 := (algebraMap K R).injective (hP.trans (map_zero _).symm)
  rw [h0, hc, map_zero]

end DerivationAlgebraicIndependence

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

noncomputable def degreeLeEquivAntidiag (D e : ℕ) :
    {α : Fin D →₀ ℕ // α.degree ≤ e} ≃
      ((Finset.univ : Finset (Fin (D + 1))).finsuppAntidiag e) where
  toFun α := ⟨Finsupp.equivFunOnFinite.symm (Fin.cons (e - α.1.degree) (⇑α.1)), by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [Fin.sum_univ_succ]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_succ]
    rw [← Finsupp.degree_eq_sum]
    have := α.2
    omega⟩
  invFun β := ⟨Finsupp.equivFunOnFinite.symm (Fin.tail ⇑β.1), by
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    rw [Finsupp.degree_eq_sum]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    ext i
    simp
  right_inv β := by
    apply Subtype.ext
    ext i
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero]
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
      omega
    · simp [Fin.tail]

theorem card_degree_le (D e : ℕ) :
    Nat.card {α : Fin D →₀ ℕ // α.degree ≤ e} = (e + D).choose D := by
  rw [Nat.card_congr (degreeLeEquivAntidiag D e), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
    show D + 1 + e - 1 = D + e by omega, ← Nat.choose_symm_add, add_comm]

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial Matrix

theorem unip_trace_aeval_zero {K : Type*} [Field K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval N P).trace = P.coeff 0 * r := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [Matrix.trace_one]
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Matrix.trace_smul, hN (i + 1) (by omega) (by omega), smul_zero]

theorem unip_idem_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (E : Matrix (Fin r) (Fin r) K)
    (hE : E * E = E) (ht : E.trace = 0) : E = 0 := by
  set f := Matrix.toLin' E with hfdef
  have hf : LinearMap.IsProj (LinearMap.range f) f := by
    constructor
    · intro x
      exact LinearMap.mem_range_self f x
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      simp only [hfdef, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hE]
  have htr : LinearMap.trace K _ f = E.trace := by
    rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin r)),
      LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']
  have h0 : ((Module.finrank K (LinearMap.range f) : ℕ) : K) = 0 := by
    rw [← hf.trace, htr, ht]
  have h1 : Module.finrank K (LinearMap.range f) = 0 := by exact_mod_cast h0
  have h2 : LinearMap.range f = ⊥ := Submodule.finrank_eq_zero.mp h1
  have h3 : f = 0 := LinearMap.range_eq_bot.mp h2
  exact Matrix.toLin'.injective (h3.trans (map_zero _).symm)

theorem unip_pow_card_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) : N ^ r = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact Subsingleton.elim _ _
  have hint : IsIntegral K N := IsIntegral.of_finite K N
  set m := minpoly K N with hm
  have hmon : m.Monic := minpoly.monic hint
  have hm0 : aeval N m = 0 := minpoly.aeval K N
  have hmdeg : m.natDegree ≤ r := by
    have h2 := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N)
      (Matrix.charpoly_monic N).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hrK : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hmc : m.coeff 0 = 0 := by
    have h := unip_trace_aeval_zero N hN m hmdeg
    rw [hm0, Matrix.trace_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hrK
  have hXm : X ∣ m := Polynomial.X_dvd_iff.mpr hmc
  obtain ⟨q, hq, hXq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd m hmon.ne_zero 0
  simp only [map_zero, sub_zero] at hq hXq
  set k := m.rootMultiplicity 0 with hkdef
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hq
    exact hXq (hq ▸ hXm)
  have hcop : IsCoprime (X ^ k) q :=
    ((Polynomial.irreducible_X.coprime_iff_not_dvd).mpr hXq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨P, hP⟩ : ∃ P : K[X], P = u * X ^ k := ⟨_, rfl⟩
  have hPP : aeval N P * aeval N P = aeval N P := by
    have hsub : P - 1 = -(v * q) := by rw [hP, ← huv]; ring
    have hfac : P * P - P = -(u * v) * m := by
      calc P * P - P = P * (P - 1) := by ring
        _ = -(u * v) * (X ^ k * q) := by rw [hsub, hP]; ring
        _ = -(u * v) * m := by rw [← hq]
    have h := congrArg (aeval N) hfac
    rw [map_sub, map_mul, map_mul, hm0, mul_zero] at h
    exact sub_eq_zero.mp h
  obtain ⟨P', hP'⟩ : ∃ P' : K[X], P' = P %ₘ m := ⟨_, rfl⟩
  have hdiv : P' + m * (P /ₘ m) = P := by
    rw [hP']
    first
      | exact Polynomial.modByMonic_add_div P hmon
      | exact Polynomial.modByMonic_add_div P m
  have hPeq : aeval N P' = aeval N P := by
    have h := congrArg (aeval N) hdiv
    rw [map_add (f := _), map_mul, hm0, zero_mul, add_zero] at h
    exact h
  have hP'deg : P'.natDegree ≤ r := by
    rw [hP']
    refine le_trans ?_ hmdeg
    first
      | exact Polynomial.natDegree_modByMonic_le P hmon
      | exact Polynomial.natDegree_modByMonic_le P m
  have hP'0 : P'.coeff 0 = 0 := by
    have h := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) hdiv
    simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, hmc, zero_mul, add_zero] at h
    rw [h, hP, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have htr : (aeval N P).trace = 0 := by
    rw [← hPeq, unip_trace_aeval_zero N hN P' hP'deg, hP'0, zero_mul]
  have hE : aeval N P = 0 := unip_idem_eq_zero _ hPP htr
  have hmP : m ∣ P := minpoly.dvd K N hE
  have hqu : q ∣ u := by
    rw [hq, hP, mul_comm u] at hmP
    exact (mul_dvd_mul_iff_left (pow_ne_zero k Polynomial.X_ne_zero)).mp hmP
  have hq1 : IsUnit q := by
    apply isUnit_of_dvd_one
    rw [← huv]
    exact (dvd_mul_of_dvd_left hqu _).add (dvd_mul_left q v)
  have hNk : N ^ k = 0 := by
    have h := hm0
    rw [hq, map_mul, map_pow, Polynomial.aeval_X] at h
    exact ((hq1.map (aeval N)).mul_left_eq_zero).mp h
  have hkm : k ≤ m.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd ⟨q, hq⟩ hmon.ne_zero
    rwa [Polynomial.natDegree_X_pow] at h
  exact pow_eq_zero_of_le (le_trans hkm hmdeg) hNk

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric NumberField

abbrev UnitSphereC (n : ℕ) : Type := sphere (0 : EuclideanSpace ℂ (Fin n)) 1

def sphereProb (n : ℕ) : Measure (UnitSphereC n) :=
  ProbabilityTheory.cond (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ

instance (n : ℕ) : IsZeroOrProbabilityMeasure (sphereProb n) := by
  unfold sphereProb; infer_instance

def spherePoint {n : ℕ} (z : UnitSphereC n) : Fin n → ℂ :=
  WithLp.ofLp (z : EuclideanSpace ℂ (Fin n))

abbrev BlockSphere (B n : ℕ) : Type := Fin B → UnitSphereC n

def blockSphereProb (B n : ℕ) : Measure (BlockSphere B n) :=
  Measure.pi fun _ => sphereProb n

def blockPoint {B n : ℕ} (z : BlockSphere B n) : Fin B × Fin n → ℂ :=
  fun p => spherePoint (z p.1) p.2

def blockSphereMean (B n : ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ) : ℝ :=
  ∫ z, Real.log ‖MvPolynomial.eval (blockPoint z) f‖ ∂(blockSphereProb B n)

def IsMultiHomogeneous {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) : Prop :=
  ∀ s ∈ f.support, ∀ b : Fin B, ∑ j : Fin n, s (b, j) = a b

def gaussAbs {K : Type*} [Field K] [NumberField K] {ι : Type*} (w : FinitePlace K)
    (f : MvPolynomial ι K) : ℝ :=
  ((f.support.sup fun s => (w (f.coeff s)).toNNReal : NNReal) : ℝ)

def h0 {K : Type*} [Field K] [NumberField K] {B n : ℕ} (f : MvPolynomial (Fin B × Fin n) K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f)) +
      ∑ σ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)

def SphereLinLogStatement : Prop :=
  ∀ (n : ℕ) (c : EuclideanSpace ℂ (Fin n)), c ≠ 0 →
    Integrable (fun z : UnitSphereC n => Real.log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖)
        (sphereProb n) ∧
      ∫ z, Real.log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(sphereProb n) =
        Real.log ‖c‖ - (harmonic (n - 1) : ℝ) / 2

def SJStatement : Prop :=
  ∀ (n a : ℕ) (f : MvPolynomial (Fin n) ℂ) (u : EuclideanSpace ℂ (Fin n)),
    f.IsHomogeneous a → ‖u‖ = 1 → MvPolynomial.eval (WithLp.ofLp u) f ≠ 0 →
    Integrable (fun z : UnitSphereC n => Real.log ‖MvPolynomial.eval (spherePoint z) f‖)
        (sphereProb n) ∧
      Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ - (a : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
        ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) f‖ ∂(sphereProb n)

def SphereLogIntegrableStatement : Prop :=
  ∀ (B n : ℕ) (a : Fin B → ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ),
    f ≠ 0 → IsMultiHomogeneous a f →
    Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖) (blockSphereProb B n)

def HeightAdditiveStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B n : ℕ) (a a' : Fin B → ℕ)
    (f g : MvPolynomial (Fin B × Fin n) K),
    0 < n → f ≠ 0 → g ≠ 0 → IsMultiHomogeneous a f → IsMultiHomogeneous a' g →
    h0 (f * g) = h0 f + h0 g ∧ ∀ c : K, c ≠ 0 → h0 (MvPolynomial.C c * f) = h0 f

def HeightLowerBoundStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B n : ℕ) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K),
    0 < n → f ≠ 0 → IsMultiHomogeneous a f →
    -(∑ b, (a b : ℝ) * (Real.log n + 1 / 2)) ≤ h0 f

def torusProb (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Ioc (0 : ℝ) 1)

def torusPoint {ι : Type*} (θ : ι → ℝ) : ι → ℂ :=
  fun i => Complex.exp (2 * Real.pi * Complex.I * (θ i : ℂ))

def torusMean {ι : Type*} [Fintype ι] (f : MvPolynomial ι ℂ) : ℝ :=
  ∫ θ, Real.log ‖MvPolynomial.eval (torusPoint θ) f‖ ∂(torusProb ι)

def coeffIn {R : Type*} [CommSemiring R] {ι : Type*} (i : ι) (k : ℕ) (f : MvPolynomial ι R) :
    MvPolynomial ι R :=
  ∑ s ∈ f.support.filter (fun s => s i = k), MvPolynomial.monomial (s.erase i) (f.coeff s)

def polyL2 {ι : Type*} (f : MvPolynomial ι ℂ) : ℝ :=
  Real.sqrt (∑ s ∈ f.support, ‖f.coeff s‖ ^ 2)

def polyInner {ι : Type*} (P Q : MvPolynomial ι ℂ) : ℂ :=
  ∑ s ∈ P.support, P.coeff s * star (Q.coeff s)

def TorusMeanBasicStatement : Prop :=
  ∀ (ι : Type) [Fintype ι],
    (∀ f : MvPolynomial ι ℂ, f ≠ 0 →
      Integrable (fun θ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) (torusProb ι)) ∧
    (∀ f g : MvPolynomial ι ℂ, f ≠ 0 → g ≠ 0 → torusMean (f * g) = torusMean f + torusMean g) ∧
    (∀ (s : ι →₀ ℕ) (c : ℂ), torusMean (MvPolynomial.monomial s c) = Real.log ‖c‖)

def TorusCoeffStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : MvPolynomial ι ℂ) (i : ι) (k : ℕ), coeffIn i k f ≠ 0 →
    ((∀ k', k < k' → coeffIn i k' f = 0) ∨ (∀ k', k' < k → coeffIn i k' f = 0)) →
    torusMean (coeffIn i k f) ≤ torusMean f

def TorusLexStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [LinearOrder ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ), s ∈ f.support →
    (∀ t ∈ f.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i) →
    Real.log ‖f.coeff s‖ ≤ torusMean f

def TorusL2Cauchy : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : MvPolynomial ι ℂ),
    (f ≠ 0 → torusMean f ≤ Real.log (polyL2 f)) ∧
    ∀ s : ι →₀ ℕ, ∃ θ : ι → ℝ, ‖f.coeff s‖ ≤ ‖MvPolynomial.eval (torusPoint θ) f‖

def GramStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : MvPolynomial ι ℂ) (S : Finset (ι →₀ ℕ)), F ≠ 0 →
    Real.exp (2 * S.card * torusMean F) ≤
      (Matrix.det (Matrix.of fun m m' : S =>
        polyInner (F * MvPolynomial.monomial (m : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (m' : ι →₀ ℕ) 1))).re

def SphereLeTorusStatement : Prop :=
  ∀ (B n : ℕ) (a : Fin B → ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ),
    0 < n → f ≠ 0 → IsMultiHomogeneous a f → blockSphereMean B n f ≤ torusMean f

end ReciprocityTheory.MultiplicativeHeights
end
end
