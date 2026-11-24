module
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous


public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace GroundTheory.Heights₂.Heights.MultiHomogeneous

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {R : Type*} [CommRing R]

private def blockWeight [DecidableEq K] (k : K) (p : Σ j, ι j) : ℕ :=
  if p.1 = k then 1 else 0

private theorem weight_blockWeight [DecidableEq K] (k : K) (m : (Σ j, ι j) →₀ ℕ) :
    Finsupp.weight (blockWeight k) m = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [blockWeight]
  · intro j _ hj
    simp [blockWeight, hj]
  · simp

private theorem weighted_iff [DecidableEq K] {f : MRingOver R ι} {a : K → ℕ} :
    IsMultiHomog f a ↔ ∀ k, IsWeightedHomogeneous (blockWeight k) f (a k) := by
  constructor
  · intro h k m hm
    rw [weight_blockWeight]
    exact h m (mem_support_iff.mpr hm) k
  · intro h m hm k
    rw [← weight_blockWeight]
    exact h k (mem_support_iff.mp hm)

theorem one : IsMultiHomog (1 : MRingOver R ι) 0 := by
  classical
  exact weighted_iff.mpr fun _ => isWeightedHomogeneous_one R _

theorem constant (r : R) : IsMultiHomog (C r : MRingOver R ι) 0 := by
  classical
  exact weighted_iff.mpr fun _ => isWeightedHomogeneous_C _ _

theorem add {f g : MRingOver R ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  exact weighted_iff.mpr fun k => (weighted_iff.mp hf k).add (weighted_iff.mp hg k)

theorem sub {f g : MRingOver R ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) : IsMultiHomog (f - g) a := by
  classical
  exact weighted_iff.mpr fun k => (weighted_iff.mp hf k).sub (weighted_iff.mp hg k)

theorem mul {f g : MRingOver R ι} {a b : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  exact weighted_iff.mpr fun k => (weighted_iff.mp hf k).mul (weighted_iff.mp hg k)

theorem pow {f : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  classical
  exact weighted_iff.mpr fun k => (weighted_iff.mp hf k).pow n

theorem sum {J : Type*} (s : Finset J) {f : J → MRingOver R ι} {a : K → ℕ}
    (hf : ∀ j ∈ s, IsMultiHomog (f j) a) : IsMultiHomog (∑ j ∈ s, f j) a := by
  classical
  exact weighted_iff.mpr fun k => IsWeightedHomogeneous.sum s f (a k)
    (fun j hj => weighted_iff.mp (hf j hj) k)

theorem prod {J : Type*} (s : Finset J) {f : J → MRingOver R ι} {a : J → K → ℕ}
    (hf : ∀ j ∈ s, IsMultiHomog (f j) (a j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, a j) := by
  classical
  apply weighted_iff.mpr
  intro k
  simpa only [Finset.sum_apply] using
    IsWeightedHomogeneous.prod s f (fun j => a j k) (fun j hj => weighted_iff.mp (hf j hj) k)

theorem variableForm [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRingOver R ι) (Pi.single p.1 1) := by
  apply weighted_iff.mpr
  intro k
  simpa only [blockWeight, Pi.single_apply, eq_comm] using
    (isWeightedHomogeneous_X R (blockWeight k) p)

theorem variablePower [DecidableEq K] (p : Σ k, ι k) (n : ℕ) :
    IsMultiHomog (X p ^ n : MRingOver R ι) (Pi.single p.1 n) := by
  convert pow (variableForm (R := R) p) n using 1
  ext k
  by_cases hk : k = p.1 <;> simp [hk]

theorem coordinateProduct (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) d := by
  classical
  convert prod Finset.univ (fun k _ => variablePower (R := R) ⟨k, c k⟩ (d k)) using 1
  ext k
  simp [Pi.single_apply, Finset.sum_apply]


theorem eval₂CoordinateScale {S : Type*} [CommRing S] (φ : R →+* S) {f : MRingOver R ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → S) (v : (Σ k, ι k) → S) :
    eval₂ φ (fun p => c p.1 * v p) f = (∏ k, c k ^ a k) * eval₂ φ v f := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hprod : ∏ p, (c p.1 * v p) ^ d p = (∏ k, c k ^ a k) * ∏ p, v p ^ d p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  rw [hprod]
  ac_rfl

theorem aevalCoordinateScale {S : Type*} [CommRing S] [Algebra R S] {f : MRingOver R ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → S) (v : (Σ k, ι k) → S) :
    aeval (fun p => c p.1 * v p) f = (∏ k, c k ^ a k) * aeval v f :=
  eval₂CoordinateScale (algebraMap R S) hf c v


end GroundTheory.Heights₂.Heights.MultiHomogeneous
