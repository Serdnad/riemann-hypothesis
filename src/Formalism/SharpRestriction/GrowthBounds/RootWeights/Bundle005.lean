module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Factorial.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def genericMatrixRootWeights (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  (genMat R n).map fun x => algebraMap _ (GLCoord R n) x

def genericMatrixInverse (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  ((genMat R n).adjugate).map fun x =>
    IsLocalization.Away.invSelf (genMat R n).det * algebraMap _ (GLCoord R n) x

def coefficientMap (R : Type*) [CommRing R] (n : ℕ) : R →+* GLCoord R n :=
  (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).comp MvPolynomial.C

def genericTranslate {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) (GLCoord R n) :=
  matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n) G


open Classical in
def weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ F.support.filter (fun m => wtS LL S m = nu), monomial m (F.coeff m)

def TorusActsThroughWeight : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (φ : R →+* B) (D : Fin n → Bˣ) (m : ι × Fin n →₀ ℕ) (c : R),
      matrixSubst LL S φ (Matrix.diagonal fun a => ((D a : Bˣ) : B)) (Matrix.diagonal fun a => (((D a)⁻¹ : Bˣ) : B))
        (monomial m c) = monomial m (φ c * ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B))

def BinomialStableContainsComponents : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (W : Submodule R (MvPolynomial (ι × Fin n) R)), (∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) →
    ∀ x ∈ W, ∀ nu, weightComponent LL S nu x ∈ W

def TwistExponentsAreWeightEntries : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R),
      sDegs LL S j G = (genericTranslate LL S G).support.image (fun m => wtS LL S m j)

def GenericMonomialsSpecialise : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1), g0 * g0inv = 1 →
    ∀ G : MvPolynomial (ι × Fin n) R, (matrixSubst LL S φ g0inv g0 G).support ⊆ (genericTranslate LL S G).support

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def laurentUnit (B : Type*) [CommRing B] : (LaurentPolynomial B)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

theorem laurentUnit_zpow (B : Type*) [CommRing B] (w : ℤ) :
    (((laurentUnit B) ^ w : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T w := by
  have hinv : (((laurentUnit B)⁻¹ : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T (-1) := rfl
  have hval : (((laurentUnit B) : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  induction w using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, hval, ← LaurentPolynomial.T_add]
  | pred i ih => rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add]; rfl

theorem binomialOperator_monomial {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : R) :
    binomPol R LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : R)) := by
  have hm : (monomial m c : MvPolynomial (ι × Fin n) R) = c • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, LinearMap.map_smul]
  simp only [binomPol]
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

def weightEntryPropertySubmodule : Submodule R (MvPolynomial (ι × Fin n) R) where
  carrier := {y | ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1),
    g0 * g0inv = 1 → ∀ m ∈ (matrixSubst LL S φ g0inv g0 y).support, Pr (wtS LL S m j)}
  zero_mem' := by
    intro k1 _ φ g0 g0inv _ m hm
    simp at hm
  add_mem' := by
    classical
    intro x y hx hy k1 _ φ g0 g0inv h m hm
    rw [map_add (f := _)] at hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
    · exact hx k1 φ g0 g0inv h m h1
    · exact hy k1 φ g0 g0inv h m h1
  smul_mem' := by
    intro c y hy k1 _ φ g0 g0inv h m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
    exact hy k1 φ g0 g0inv h m (MvPolynomial.support_smul hm)

theorem laurent_coefficients_mem_property (y : MvPolynomial (ι × Fin n) R) (K : Finset ℤ) (yk : ℤ → MvPolynomial (ι × Fin n) R)
    (hh : ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1), ∃ h h' : Matrix (Fin n) (Fin n) (LaurentPolynomial k1),
      h' * h = 1 ∧ matrixSubst LL S (LaurentPolynomial.C.comp φ) h h' y =
        ∑ k ∈ K, C (LaurentPolynomial.T k) * MvPolynomial.map (LaurentPolynomial.C.comp φ) (yk k))
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : ∀ k ∈ K, yk k ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  intro k hk k1 _ φ g0 g0inv hg m hm
  obtain ⟨h, h', hh1, hE⟩ := hh k1 φ
  set ψ : k1 →+* LaurentPolynomial k1 := LaurentPolynomial.C with hψ
  have h2 : g0.map ψ * g0inv.map ψ = 1 := by
    rw [← Matrix.map_mul, hg, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
  have hinv : (h' * g0.map ψ) * (g0inv.map ψ * h) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g0.map ψ), h2, Matrix.one_mul, hh1]
  apply hy (LaurentPolynomial k1) (ψ.comp φ) (h' * g0.map ψ) (g0inv.map ψ * h) hinv m

  rw [← matrixSubst_comp, hE, map_sum]
  have hA : ∀ k', matrixSubst LL S (RingHom.id _) (g0inv.map ψ) (g0.map ψ)
      (C (LaurentPolynomial.T k') * MvPolynomial.map (ψ.comp φ) (yk k')) =
      C (LaurentPolynomial.T k') * MvPolynomial.map ψ (matrixSubst LL S φ g0inv g0 (yk k')) := by
    intro k'
    rw [map_mul, matrixSubst_C, RingHom.id_apply, matrixSubst_map, map_matrixSubst]
  simp_rw [hA]
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro hz
  apply hm
  rw [MvPolynomial.coeff_sum] at hz
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hz
  have hz2 := congrArg (fun p : LaurentPolynomial k1 => p.coeff k) hz
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hz2
  have hT : ∀ k' (c : k1), (LaurentPolynomial.T k' * ψ c).coeff k = if k' = k then c else 0 := by
    intro k' c
    rw [hψ, mul_comm, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp_rw [hT, Finset.sum_ite_eq' K k] at hz2
  simpa [hk] using hz2

end fwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem weighted_sum_shift_recombine {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (c c' r : ℕ → K) (B : ℕ → M) (k : ℕ)
    (h0 : c' 0 = c 0) (hs : ∀ j, j < k + 1 → c' (j + 1) = c (j + 1) + c j * r j) (hz : c (k + 1) = 0) :
    ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) = ∑ j ∈ range (k + 2), c' j • B j := by
  rw [Finset.sum_range_succ' (fun j => c' j • B j), h0]
  have e1 : ∑ j ∈ range (k + 1), c' (j + 1) • B (j + 1) =
      ∑ j ∈ range (k + 1), (c (j + 1) • B (j + 1) + (c j * r j) • B (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j (Finset.mem_range.mp hj), add_smul]
  rw [e1, Finset.sum_add_distrib]
  have e2 : ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) =
      ∑ j ∈ range (k + 1), c j • B j + ∑ j ∈ range (k + 1), (c j * r j) • B (j + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_add, smul_smul]
  rw [e2]
  have e3 : ∑ j ∈ range (k + 1), c j • B j =
      c 0 • B 0 + ∑ j ∈ range (k + 1), c (j + 1) • B (j + 1) := by
    rw [Finset.sum_range_succ (fun j => c (j + 1) • B (j + 1)), hz, zero_smul, add_zero,
      Finset.sum_range_succ' (fun j => c j • B j)]
    abel
  rw [e3]
  abel

section Heisenberg₂

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

theorem heisenberg_mul_pow_commutator {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (m : ℕ) :
    X * Y ^ m = Y ^ m * X + (m : K) • (Y ^ (m - 1) * Z) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : X * Y ^ (m + 1) = (X * Y ^ m) * Y := by rw [pow_succ, mul_assoc]
    have e2 : Y ^ (m - 1) * Z * Y = Y ^ (m - 1) * Y * Z := by rw [mul_assoc, hZY, ← mul_assoc]
    rw [e1, ih, add_mul, mul_assoc (Y ^ m) X Y, hZ, smul_mul_assoc, e2, mul_add, ← mul_assoc, ← pow_succ]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← pow_succ, Nat.sub_add_cancel hm]
      simp only [Nat.add_sub_cancel, Nat.cast_succ, add_smul, one_smul]
      abel

theorem heisenberg_pow_mul_pow_expansion {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (hZX : X * Z = Z * X) (k l : ℕ) :
    X ^ k * Y ^ l = ∑ j ∈ range (k + 1),
      (((k.choose j * l.descFactorial j : ℕ) : K)) • (Y ^ (l - j) * Z ^ j * X ^ (k - j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : ∀ j : ℕ, Commute X (Z ^ j) := fun j => Commute.pow_right (show Commute X Z from hZX) j
    have step : ∀ j ∈ range (k + 1),
        X * ((((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k - j))) =
        (((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j) +
          (((l - j : ℕ)) : K) • (Y ^ (l - (j + 1)) * Z ^ (j + 1) * X ^ (k + 1 - (j + 1)))) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_smul_comm]
      congr 1
      rw [← mul_assoc, ← mul_assoc, heisenberg_mul_pow_commutator (K := K) hZ hZY (l - j), add_mul, add_mul,
        smul_mul_assoc, smul_mul_assoc]
      congr 1
      · simp only [mul_assoc]
        rw [← mul_assoc X (Z ^ j), (hc j).eq, mul_assoc (Z ^ j), ← pow_succ',
          show k - j + 1 = k + 1 - j by omega]
      · congr 1
        rw [show l - (j + 1) = l - j - 1 by omega, show k + 1 - (j + 1) = k - j by omega,
          mul_assoc (Y ^ (l - j - 1)) Z, ← pow_succ']
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum, Finset.sum_congr rfl step]
    exact weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : K))
      (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : K)) (fun j => ((l - j : ℕ) : K))
      (fun j => Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j)) k (by simp)
      (fun j _ => by
        have e : (k + 1).choose (j + 1) * l.descFactorial (j + 1) =
            k.choose (j + 1) * l.descFactorial (j + 1) + k.choose j * l.descFactorial j * (l - j) := by
          rw [Nat.choose_succ_succ, Nat.descFactorial_succ]; ring
        rw [e]
        push_cast
        ring)
      (by simp [Nat.choose_succ_self])

def dividedPower (K : Type*) [Field K] {A : Type*} [Ring A] [Algebra K A] (X : A) (k : ℕ) : A := ((k.factorial : K)⁻¹) • X ^ k

theorem heisenberg_dividedPower_expansion {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (hZX : X * Z = Z * X) (k l : ℕ) :
    dividedPower K X k * dividedPower K Y l = ∑ j ∈ range (k + 1),
      if j ≤ l then dividedPower K Y (l - j) * dividedPower K Z j * dividedPower K X (k - j) else 0 := by
  unfold dividedPower
  rw [smul_mul_smul_comm, heisenberg_pow_mul_pow_expansion (K := K) hZ hZY hZX, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs with hjl
  · rw [smul_smul, smul_mul_smul_comm, smul_mul_smul_comm]
    congr 1
    have h1 : ((k.factorial : ℕ) : K) = (k.choose j : K) * j.factorial * (k - j).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
    have h2 : ((l.factorial : ℕ) : K) = ((l - j).factorial : K) * l.descFactorial j := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjl).symm
    have h3 : (k.choose j : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
    have h4 : (l.descFactorial j : K) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
    have h5 : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((k - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h7 : ((l - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [h1, h2]
    push_cast
    field_simp
  · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

end Heisenberg₂

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section good

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

def DividedPowersPreserve (Q : V → Prop) (D : Module.End K V) : Prop :=
  ∀ (k : ℕ) (x : V), Q x → Q (((k.factorial : K)⁻¹) • (D ^ k) x)

theorem predicate_finset_sum_mem (Q : V → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y)) {α : Type*}
    (s : Finset α) (f : α → V) (h : ∀ i ∈ s, Q (f i)) : Q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem divided_powers_preserve_add (Q : V → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y))
    (D D' : Module.End K V) (hc : Commute D D') (hD : DividedPowersPreserve Q D) (hD' : DividedPowersPreserve Q D') :
    DividedPowersPreserve Q (D + D') := by
  intro k x hx
  rw [hc.add_pow, LinearMap.sum_apply, Finset.smul_sum]
  refine predicate_finset_sum_mem Q h0 hadd _ _ fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have h1 := hD m _ (hD' (k - m) x hx)
  have h2 : ((k.factorial : K)⁻¹) • (D ^ m * D' ^ (k - m) * ((k.choose m : ℕ) : Module.End K V)) x =
      ((m.factorial : K)⁻¹) • (D ^ m) ((((k - m).factorial : K)⁻¹) • (D' ^ (k - m)) x) := by
    have h3 : ((k.choose m : ℕ) : Module.End K V) x = ((k.choose m : ℕ) : K) • x := by
      rw [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    simp only [Module.End.mul_apply, h3, map_smul, smul_smul]
    congr 1
    have h4 : ((k.choose m : ℕ) : K) = (k.factorial : K) / ((m.factorial : K) * ((k - m).factorial : K)) :=
      Nat.cast_choose K hmk
    have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hm' : (m.factorial : K) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hkm : ((k - m).factorial : K) ≠ 0 := by exact_mod_cast (k - m).factorial_ne_zero
    rw [h4]
    field_simp
  rw [h2]
  exact h1

end good

end Formalism.MainNotions.G.GLWeightTheory
end
end
