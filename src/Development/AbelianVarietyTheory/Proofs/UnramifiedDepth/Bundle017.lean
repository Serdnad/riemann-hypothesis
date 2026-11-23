module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.DualLattices.Bundle010
public import ReciprocityTheory.DualLattices.FormalChartAtZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.IsPairingValueAddRight
public import ReciprocityTheory.DualLattices.Bundle006
public import ReciprocityTheory.DualLattices.Bundle016
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}

private lemma gram_zero (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h
  have e : z * z = z := B.pairing_unique N 0 y _ _ h hz
  have e1 : z = 1 := by simpa using e
  rwa [e1] at hz

private lemma gram_nsmul (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (m : ℕ) : B.IsPairing N (m • x) y (z ^ m) := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    exact gram_zero B N y h.2.1
  | succ m ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ y _ _ ih h

private lemma gram_sum {κ : Type} (s : Finset κ) (N : ℕ) (x : κ → B.G R) (y : B.G R)
    (z : κ → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact gram_zero B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ y _ _ (h a) ih

end SlopeTestRemainingChoices

private lemma gram_limit {p : ℕ} [Fact p.Prime] (k : ℕ → ℕ)
    (hk : ∀ n, k n ≡ k (n + 1) [MOD p ^ (n + 1)]) :
    ∃ a : ℤ_[p], ∀ n, PadicInt.toZModPow (n + 1) a = (k n : ZMod (p ^ (n + 1))) := by
  have hi : ∀ i : ℕ, (p : ℤ) ^ i ∣ (fun i : ℕ => (k (i - 1) : ℤ)) (i + 1) -
      (fun i : ℕ => (k (i - 1) : ℤ)) i := by
    intro i
    cases i with
    | zero => simp
    | succ n =>
      have h := (Nat.modEq_iff_dvd.1 (hk n))
      simpa using h
  have key := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i : ℕ => (k (i - 1) : ℤ)) p hi
  refine ⟨_, fun n => (key (n + 1)).trans ?_⟩
  simp only [Nat.add_sub_cancel, Int.cast_natCast]

private lemma gram_ext {p : ℕ} [Fact p.Prime] (a b : ℤ_[p])
    (h : ∀ n, PadicInt.toZModPow (n + 1) a = PadicInt.toZModPow (n + 1) b) : a = b := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, h,
    PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) b]

private lemma gram_toZMod {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) (k : ℕ)
    (h : PadicInt.toZModPow (0 + 1) a = (k : ZMod (p ^ (0 + 1)))) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : a - (k : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) (0 + 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, h, sub_self]
  rw [PadicInt.ker_toZModPow, zero_add, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h1
  exact h1

theorem tateBasis_gram :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) [IsDomain (Tw.O : Type)] [Algebra ℤ_[p] (Tw.O : Type)],
    (∀ n, RingHom.ker (Tw.q n).1 = Ideal.span {((p : ℕ) : (Tw.O : Type)) ^ (n + 1)}) →
    (∀ n, IsPrimitiveRoot (Tw.ζ n) (p ^ (n + 1))) → (∀ n, Tw.ζ (n + 1) ^ p = Tw.ζ n) →
    ∀ τ : Ix g → ℕ → B.G Tw.O, (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : B.G Tw.O, p • x = 0 → ∃! t : Ix g → ZMod p, x = ptOf B τ t) →
    (∀ x : B.G Tw.O, p • x = 0 → (∀ y : B.G Tw.O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∃ E : Matrix (Ix g) (Ix g) ℤ_[p], (Eᵀ = -E ∧ ∀ i, E i i = 0) ∧ IsUnit E.det ∧
      ∀ i j n, B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ (PadicInt.toZModPow (n + 1) (E i j)).val)) := by
  intro R₀ _ p hp g B Tw _ _ _ hζ hζp τ htors hcomp hbasis hnd
  have hex : ∀ i j n, ∃ k : ℕ, k < p ^ (n + 1) ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k) := by
    intro i j n
    obtain ⟨z, hz⟩ := B.pairing_exists _ _ _ (htors i n) (htors j n)
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    obtain ⟨k, hk, e⟩ := (hζ n).eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity _ z).2 (B.pairing_pow _ _ _ _ hz))
    exact ⟨k, hk, e ▸ hz⟩
  choose k hklt hk using hex
  have hcompat : ∀ i j n, k i j n ≡ k i j (n + 1) [MOD p ^ (n + 1)] := by
    intro i j n
    have h1 := gram_nsmul B _ _ _ _ (hk i j (n + 1)) p
    rw [← hcomp, pow_succ p (n + 1)] at h1
    have h2 := B.pairing_mul _ p _ _ _ (htors i n)
      (by rw [← pow_succ]; exact htors j (n + 1)) h1
    rw [← hcomp, ← pow_mul, mul_comm, pow_mul, hζp] at h2
    have h3 := B.pairing_unique _ _ _ _ _ (hk i j n) h2
    rwa [pow_eq_pow_iff_modEq, ← (hζ n).eq_orderOf] at h3
  choose E hE using fun i j => gram_limit (k i j) (hcompat i j)
  have hanti : ∀ i j, E j i = -E i j := by
    intro i j
    refine gram_ext _ _ fun n => ?_
    have h1 := B.pairing_unique _ _ _ _ _ (hk j i n) (B.pairing_sw _ _ _ _ (hk i j n))
    rw [eq_inv_iff_mul_eq_one, ← pow_add, (hζ n).pow_eq_one_iff_dvd,
      ← ZMod.natCast_eq_zero_iff, Nat.cast_add] at h1
    rw [map_neg, hE, hE]
    exact eq_neg_of_add_eq_zero_left h1
  refine ⟨Matrix.of E, ⟨?_, fun i => ?_⟩, ?_, fun i j n => ?_⟩
  · apply Matrix.ext
    intro i j
    exact hanti i j
  · exact self_eq_neg.1 (hanti i i)
  · by_contra hu
    have hd : (Matrix.of E).det ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod]
      exact hu
    rw [RingHom.mem_ker, RingHom.map_det] at hd
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have ht0 : ∀ i, p • τ i 0 = 0 := fun i => by simpa using htors i 0
    have hpt : ∀ t : Ix g → ZMod p, p • ptOf B τ t = 0 := fun t => by
      simp only [ptOf, Finset.smul_sum, smul_comm p]
      exact Finset.sum_eq_zero fun j _ => by rw [ht0, smul_zero]
    have hrow : ∀ j, B.IsPairing p (ptOf B τ s) (τ j 0) 1 := by
      intro j
      have h1 := gram_sum B Finset.univ (p ^ (0 + 1)) (fun i => (s i).val • τ i 0) (τ j 0)
        (fun i => (Tw.ζ 0 ^ k i j 0) ^ (s i).val) (htors j 0)
        (fun i => gram_nsmul B _ _ _ _ (hk i j 0) _)
      have h2 : ∏ i, (Tw.ζ 0 ^ k i j 0) ^ (s i).val = 1 := by
        simp only [← pow_mul]
        rw [Finset.prod_pow_eq_pow_sum, (hζ 0).pow_eq_one_iff_dvd, zero_add, pow_one,
          ← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (congrFun hs j)
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm, ← gram_toZMod _ _ (hE i j 0)]
        rfl
      rw [h2, zero_add, pow_one] at h1
      exact h1
    have hx : ptOf B τ s = 0 := by
      refine hnd _ (hpt s) fun y hy => ?_
      obtain ⟨t, rfl, -⟩ := hbasis y hy
      have h1 := gram_sum B Finset.univ p (fun j => (t j).val • τ j 0) (ptOf B τ s)
        (fun j => (1⁻¹) ^ (t j).val) (hpt s)
        (fun j => gram_nsmul B _ _ _ _ (B.pairing_sw _ _ _ _ (hrow j)) _)
      have h2 := B.pairing_sw _ _ _ _ h1
      simp only [inv_one, one_pow, Finset.prod_const_one] at h2
      exact h2
    have h0 : (0 : B.G Tw.O) = ptOf B τ (0 : Ix g → ZMod p) := by simp [ptOf]
    exact hs0 ((hbasis 0 (smul_zero p)).unique hx.symm h0)
  · rw [Matrix.of_apply, hE, ZMod.val_cast_of_lt (hklt i j n)]
    exact hk i j n

end GlobalTheory
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WittQuot

private lemma wS_mul (p : ℕ) [hp : Fact p.Prime] (n : ℕ) : (p : MvPolynomial (Fin n) ℤ) * wS p n =
    (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p := by
  set q : MvPolynomial (Fin n) ℤ := (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p with hq
  have hd : MvPolynomial.C (p : ℤ) ∣ q := by
    rw [MvPolynomial.C_dvd_iff_zmod, hq]

    simp only [map_sub, map_sum, map_pow, MvPolynomial.map_X]
    rw [sum_pow_char, sub_self]
  rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hd
  conv_rhs => rw [q.as_sum]
  change _ * ∑ m ∈ q.support, MvPolynomial.monomial m (q.coeff m / (p : ℤ)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← map_natCast (MvPolynomial.C : ℤ →+* _), MvPolynomial.C_mul_monomial,
    Int.mul_ediv_cancel' (hd m)]

private lemma teich_decomp (p : ℕ) [Fact p.Prime] {K : Type} [CommRing K] [CharP K p]
    [PerfectRing K p] (x : WittVector p K) :
    ∃ y : WittVector p K, x = WittVector.teichmuller p (x.coeff 0) + p * y := by
  have hmem : x - WittVector.teichmuller p (x.coeff 0) ∈
      Ideal.span {(p : WittVector p K) ^ 1} := by
    rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero,
      ← WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [WittVector.teichmuller_coeff_zero]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨w, ?_⟩
  rw [pow_one] at hw
  rw [mul_comm, hw]; abel

theorem teichmuller_quot :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (ϖ : PreTilt O p), ϖ.untilt = (p : O) →
    ∀ (W : Type) [CommRing W] (pr : Ainf.A p O →+* W), Function.Surjective pr →
    RingHom.ker pr = Ideal.span {(p : Ainf.A p O) ^ 2, WittVector.teichmuller p ϖ} →
    (∀ w : W, ∃ c : PreTilt O p, ∃ c' : W, w = pr (WittVector.teichmuller p c) + p * c') ∧
    (∀ (n : ℕ) (a : Fin n → PreTilt O p), ∑ j, pr (WittVector.teichmuller p (a j)) = pr (WittVector.teichmuller p (∑ j, a j)) +
      p * pr (WittVector.teichmuller p (MvPolynomial.eval₂ (Int.castRingHom (PreTilt O p)) (fun j => (frobeniusEquiv (PreTilt O p) p).symm (a j)) (wS p n)))) ∧
    (∀ c : PreTilt O p, WittVector.fontaineTheta O p (WittVector.teichmuller p c) ∈ Ideal.span {(p : O)} → pr (WittVector.teichmuller p c) = 0)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε ϖ hϖ W _ pr hpr hker
  have hp2 : pr ((p : Ainf.A p O) ^ 2) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span (by simp)
  have hϖ0 : pr (WittVector.teichmuller p ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span (by simp)
  refine ⟨fun w => ?_, fun n a => ?_, fun c hc => ?_⟩
  · obtain ⟨x, rfl⟩ := hpr w
    obtain ⟨y, hy⟩ := teich_decomp p x
    refine ⟨x.coeff 0, pr y, ?_⟩
    conv_lhs => rw [hy]
    rw [map_add (f := _), map_mul, map_natCast]
  · obtain ⟨w, hw⟩ := ((teichSum p (Fin n) Finset.univ).2 (PreTilt O p) a (wS p n) (wS_mul p n)).1
    have h := congrArg pr hw

    rw [map_sum, map_add (f := _), map_add (f := _), map_mul, map_mul, hp2, zero_mul, add_zero, map_natCast] at h
    rw [h, MvPolynomial.aeval_def]
    rfl
  · have hK := ((a0 p C v O hv).2.2.1 ϖ hϖ).2.2
    have hm : WittVector.teichmuller p c ∈
        Ideal.span {(p : WittVector p (PreTilt O p)), WittVector.teichmuller p ϖ} := by
      rw [← hK, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hc
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hm
    have h := congrArg (WittVector.constantCoeff (p := p) (R := PreTilt O p)) hxy
    rw [map_add (f := _), map_mul, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero, zero_add] at h
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
    rw [← h, map_mul, map_mul, hϖ0, mul_zero]

end GlobalTheory.WittQuot
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private noncomputable abbrev serNatI (R₀ κ : Type) [CommRing R₀] (N : ℕ) : Ideal (MvPolynomial κ R₀) :=
  Ideal.span (Set.range fun j : κ => (MvPolynomial.X j : MvPolynomial κ R₀) ^ N)

private lemma serNat_coeff {R₀ κ : Type} [CommRing R₀] [DecidableEq κ] {N : ℕ}
    {q : MvPolynomial κ R₀} (hq : q ∈ serNatI R₀ κ N) :
    ∀ m : κ →₀ ℕ, (∀ j, m j < N) → AddMonoidAlgebra.coeff q m = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨j, rfl⟩ m hm
    simp only [MvPolynomial.coeff_X_pow]
    rw [if_neg]
    rintro rfl
    simpa using hm j
  · intro m _; simp
  · intro x y _ _ hx hy m hm
    rw [MvPolynomial.coeff_add, hx m hm, hy m hm, add_zero]
  · intro r x _ hx m hm
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2, mul_zero]
    intro j
    have : p.1 + p.2 = m := by simpa using hp
    have h2 := hm j
    rw [← this, Finsupp.add_apply] at h2
    omega

private lemma serNat_nil {R₀ κ : Type} [CommRing R₀] (N : ℕ) (j : κ) :
    (Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)) ^ N = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩

private lemma serNat_aeval {R₀ κ : Type} [CommRing R₀] [Fintype κ] [DecidableEq κ]
    {S : Type} [CommRing S] [Algebra R₀ S] {N : ℕ} {a : κ → S} (ha : ∀ i, a i ^ N = 0)
    (q : MvPolynomial κ R₀) :
    MvPolynomial.aeval a q = ∑ e : κ → Fin N, algebraMap R₀ S (AddMonoidAlgebra.coeff
      q (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ))) * ∏ i, a i ^ (e i : ℕ) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add (f := _), MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | monomial m r =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    by_cases hm : ∀ j, m j < N
    · rw [Finset.sum_eq_single (fun j => (⟨m j, hm j⟩ : Fin N))]
      · rw [MvPolynomial.coeff_monomial, if_pos]
        ext j; simp
      · intro e _ he
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply he
        funext j
        apply Fin.ext
        simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · push Not at hm
        obtain ⟨j, hj⟩ := hm
        rw [Finset.prod_eq_zero (f := fun i => a i ^ m i) (Finset.mem_univ j)
          (pow_eq_zero_of_le hj (ha j)), mul_zero]
      · intro e _
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply hm
        intro j
        simp [h]

theorem exists_series_of_natural_on_nilpotent :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) := by
  intro hE R₀ _ κ _ _ c hc
  choose p hp using fun N : ℕ => Ideal.Quotient.mk_surjective (I := serNatI R₀ κ N)
    (c (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N)
      (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)))
  have key : ∀ (N : ℕ) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, a i ^ N = 0) →
      c S a = MvPolynomial.aeval a (p N) := by
    intro N S _ _ a ha
    let φ : (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ (serNatI R₀ κ N) (MvPolynomial.aeval a) (by
        intro x hx
        have : serNatI R₀ κ N ≤ RingHom.ker (MvPolynomial.aeval (R := R₀) a) := by
          refine Ideal.span_le.2 ?_
          rintro _ ⟨j, rfl⟩
          simp [RingHom.mem_ker, ha j]
        exact this hx)
    have hφ : ∀ x, φ (Ideal.Quotient.mk (serNatI R₀ κ N) x) = MvPolynomial.aeval a x :=
      fun x => rfl
    have h := hc _ S φ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => ⟨N, serNat_nil N j⟩)
    rw [← hp N, hφ] at h
    simp only [hφ, MvPolynomial.aeval_X] at h
    exact h.symm
  have compat : ∀ N M : ℕ, N ≤ M → ∀ m : κ →₀ ℕ, (∀ j, m j < N) →
      AddMonoidAlgebra.coeff (p M) m = AddMonoidAlgebra.coeff (p N) m := by
    intro N M h m hm
    have h1 := key M _ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => pow_eq_zero_of_le h (serNat_nil N j))
    have h2 : MvPolynomial.aeval (R := R₀)
        (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
        = Ideal.Quotient.mkₐ R₀ (serNatI R₀ κ N) := by
      ext j; simp
    rw [← hp N, h2, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h1
    have h3 := serNat_coeff h1 m hm
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
    exact h3.symm
  refine ⟨fun m => AddMonoidAlgebra.coeff (p (Finset.univ.sup m + 1)) m, ?_⟩
  intro S _ _ a ha
  choose n hn using ha
  have hN : ∀ i, a i ^ (Finset.univ.sup n) = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  generalize Finset.univ.sup n = N at hN
  refine Eq.trans ?_ ((hE _ S a).1 N hN).symm
  rw [key N S a hN, serNat_aeval hN]
  unfold tEval
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 2
  set m : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ) with hm
  change _ = AddMonoidAlgebra.coeff (p (Finset.univ.sup m + 1)) m
  rw [← compat N (max N (Finset.univ.sup m + 1)) (le_max_left _ _) m (fun j => by simp [hm]),
    compat _ _ (le_max_right _ _) m
      (fun j => Nat.lt_succ_of_le (Finset.le_sup (f := m) (Finset.mem_univ j)))]

end GlobalTheory
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory

theorem sumMvList_eq_ptSumL {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) {τ : Type} (l : List (Fin d → MvPowerSeries τ C)) :
    sumMvList G l = ptSumL G l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [sumMvList, ptSumL, ih]; rfl

theorem basisMap_eq_ptBasisMap {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C) : basisMap G γ = ptBasisMap G γ :=
  sumMvList_eq_ptSumL G _

theorem typicalBasis_coordinates : TypicalCurveEigenspace → TypicalCurveBasisExists := by
  intro h2 C _ _ _ v p hp hvp d h hh ty G μ
  refine ⟨?_, fun γ hγ => ?_⟩
  · have key : ∀ a : Fin d, ∃ γ : Fin d → PowerSeries C,
        IsCurve v γ ∧ G.IsOfType p ty (ty a) γ ∧ tangent γ = Pi.single a 1 := by
      intro a
      refine h2 C v p hp hvp d h hh ty G μ (ty a) (Pi.single a 1) (fun b => ?_) (fun b hb => ?_)
      · unfold IsIntV
        by_cases e : b = a
        · subst e; simp
        · simp [Pi.single_eq_of_ne e]
      · exact Pi.single_eq_of_ne (fun e => hb (by rw [e])) _
    choose γ h1 h2' h3 using key
    refine ⟨γ, h1, h2', ?_⟩
    have : (Matrix.of fun a b => tangent (γ a) b) = (1 : Matrix (Fin d) (Fin d) C) := by
      ext a b
      simp [h3, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, v.map_one]
  · rw [basisMap_eq_ptBasisMap]
    exact ⟨ptBasisMap_inv G hγ.1 hγ.2.2, ptBasisMap_lg G hγ.1⟩

end GlobalTheory
end
