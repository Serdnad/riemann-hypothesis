module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RingHom.Etale
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

section

noncomputable section

namespace GlobalTheory
namespace LeadSubst

open MvPowerSeries

variable {σ τ R : Type*} [CommRing R]

def Near (n : ℕ) (P Q : MvPowerSeries τ R) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((n + 1 : ℕ) : ℕ∞) ≤ (P - Q).order

theorem Near.one : Near 0 (1 : MvPowerSeries τ R) 1 := by
  simp [Near]

theorem Near.mul {n m : ℕ} {P Q P' Q' : MvPowerSeries τ R} (h : Near n P Q)
    (h' : Near m P' Q') : Near (n + m) (P * P') (Q * Q') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast; exact (add_le_add h1 h1').trans le_order_mul
  · push_cast; exact (add_le_add h2 h2').trans le_order_mul
  · have e : P * P' - Q * Q' = P * (P' - Q') + (P - Q) * Q' := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h1 h3')
      push_cast; ring
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h3 h2')
      push_cast; ring

theorem Near.prod {a b : σ → MvPowerSeries τ R}
    (h : ∀ s, Near 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Near d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa using (Near.one : Near 0 (1 : MvPowerSeries τ R) 1)
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add (f := _)]
    exact hf.mul hg
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.degree_single]
    induction n with
    | zero => simpa using (Near.one : Near 0 (1 : MvPowerSeries τ R) 1)
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul (h s)

theorem near_one {u v : MvPowerSeries τ R} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h1 : ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ u = coeff γ v) : Near 1 u v := by
  refine ⟨by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu,
    by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hv, ?_⟩
  refine nat_le_order fun d hd => ?_
  rw [map_sub, sub_eq_zero]
  rcases (show d.degree = 0 ∨ d.degree = 1 by omega) with h | h
  · rw [(Finsupp.degree_eq_zero_iff d).mp h, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hu, hv]
  · exact h1 d h

end LeadSubst


open MvPowerSeries in
theorem coeff_subst_leading :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries τ R) (N : ℕ)
      (f : MvPowerSeries σ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (∀ i (γ : τ →₀ ℕ), γ.degree = 1 → coeff γ (u i) = coeff γ (v i)) →
      (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) →
      ∀ γ : τ →₀ ℕ, (γ.degree < N → coeff γ (subst u f) = 0) ∧
        (γ.degree ≤ N → coeff γ (subst u f) = coeff γ (subst v f)) := by
  intro R _ σ τ _ u v N f hu hv h1 hf γ
  have hn : ∀ s, LeadSubst.Near 1 (u s) (v s) := fun s => LeadSubst.near_one (hu s) (hv s) (h1 s)
  refine ⟨fun hγ => ?_, fun hγ => ?_⟩
  · rw [coeff_subst (hasSubst_of_constantCoeff_zero hu)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : d.degree < N
    · rw [hf d hd, zero_smul]
    · rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega : γ.degree < d.degree))
        (LeadSubst.Near.prod hn d).1), smul_zero]
  · rw [coeff_subst (hasSubst_of_constantCoeff_zero hu),
      coeff_subst (hasSubst_of_constantCoeff_zero hv)]
    refine finsum_congr fun d => ?_
    by_cases hd : d.degree < N
    · rw [hf d hd, zero_smul, zero_smul]
    · congr 1
      have h := coeff_of_lt_order (d := γ) (lt_of_lt_of_le
        (by exact_mod_cast (by omega : γ.degree < d.degree + 1)) (LeadSubst.Near.prod hn d).2.2)
      rwa [map_sub, sub_eq_zero] at h

end GlobalTheory
end
end

section

namespace GlobalTheory

theorem strip_prime_factors (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ}
    (π : Fin n → R) (J : Finset (Fin n)) (x : R) (hx : x ≠ 0) :
    ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧
      ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  induction J using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, x, by simp, by simp⟩
  | @insert j J hj ih =>
    obtain ⟨m, y, hxy, hy⟩ := ih
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hxy)
    by_cases hp : Prime (π j)
    · obtain ⟨y', hy', hnd⟩ :=
        (FiniteMultiplicity.of_not_isUnit hp.not_unit hy0).exists_eq_pow_mul_and_not_dvd
      refine ⟨Function.update m j (multiplicity (π j) y), y', ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self]
        have hJ : ∏ i ∈ J, π i ^ Function.update m j (multiplicity (π j) y) i
            = ∏ i ∈ J, π i ^ m i := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
        rw [hJ, hxy]
        conv_lhs => rw [hy']
        ring
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hnd hdvd
        · exact hy i hi hpi (hdvd.trans (Dvd.intro_left _ hy'.symm))
    · refine ⟨Function.update m j 0, y, ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self, pow_zero, one_mul]
        rw [hxy]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hp hpi
        · exact hy i hi hpi hdvd

theorem strip_prime_factors_target : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y :=
  fun R _ _ _ _ π J x hx => strip_prime_factors R π J x hx

end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

theorem sub_apply_bijective_of_iterate_eq_zero {M : Type} [AddCommGroup M] (L : M →+ M) (K : ℕ)
    (hK : ∀ z, (⇑L)^[K] z = 0) : Function.Bijective (fun z => z - L z) := by
  constructor
  · intro a b hab
    have hab' : a - L a = b - L b := hab
    have hfix : L (a - b) = a - b := by
      rw [map_sub]
      rw [sub_eq_sub_iff_sub_eq_sub] at hab'
      exact hab'.symm
    have h1 : ∀ m, (⇑L)^[m] (a - b) = a - b := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih, hfix]
    exact sub_eq_zero.mp ((h1 K).symm.trans (hK _))
  · intro c
    refine ⟨∑ k ∈ Finset.range K, (⇑L)^[k] c, ?_⟩
    show (∑ k ∈ Finset.range K, (⇑L)^[k] c) - L (∑ k ∈ Finset.range K, (⇑L)^[k] c) = c

    rw [map_sum]
    have hs : ∀ k, L ((⇑L)^[k] c) = (⇑L)^[k + 1] c := fun k =>
      (Function.iterate_succ_apply' (⇑L) k c).symm
    simp only [hs]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub', hK, sub_zero]
    rfl

noncomputable def perfLevelOp (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) : (ι → S) →+ (ι → S) where
  toFun w := (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k)
  map_zero' := by ext i; simp [Matrix.mulVec, dotProduct]
  map_add' a b := by ext i; simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]

theorem perfLevelOp_apply (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (w : ι → S) :
    perfLevelOp p S Q n w = (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k) :=
  rfl

theorem perfLevelOp_coeff (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (x : ι → Perfection S p) :
    (fun i => Perfection.coeff S p n ((x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k))) i))
      = (fun i => Perfection.coeff S p n (x i))
        - perfLevelOp p S Q n (fun i => Perfection.coeff S p n (x i)) := by
  ext i
  simp only [Pi.sub_apply, map_sub, perfLevelOp_apply]
  congr 1
  rw [RingHom.map_mulVec]
  have hc : (Perfection.coeff S p n) ∘ (fun k => frobenius (Perfection S p) p (x k))
      = fun k => frobenius S p (Perfection.coeff S p n (x k)) := by
    funext k
    simp [frobenius_def, map_pow]
  rw [hc]

theorem perfLevelOp_frobenius (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (w : ι → S) :
    (fun i => frobenius S p ((w - perfLevelOp p S Q (n + 1) w) i))
      = (fun i => frobenius S p (w i)) - perfLevelOp p S Q n (fun i => frobenius S p (w i)) := by
  ext i
  simp only [perfLevelOp_apply, Pi.sub_apply, map_sub]
  congr 1

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  congr 1
  ext j
  congr 1
  rw [frobenius_def, Perfection.coeff_pow_p']

theorem perfection_frobenius_solve : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := by
  intro p _ S _ _ ι _ Q hnil c
  have bij : ∀ n, Function.Bijective (fun z => z - perfLevelOp p S Q n z) := by
    intro n
    obtain ⟨K, hK⟩ := hnil n
    exact sub_apply_bijective_of_iterate_eq_zero _ K hK
  let z : ℕ → ι → S := fun n => Function.surjInv (bij n).2 (fun i => Perfection.coeff S p n (c i))
  have hz : ∀ n, z n - perfLevelOp p S Q n (z n) = fun i => Perfection.coeff S p n (c i) :=
    fun n => Function.surjInv_eq (bij n).2 _
  have compat : ∀ n k, z (n + 1) k ^ p = z n k := by
    intro n
    have h : (fun k => frobenius S p (z (n + 1) k)) = z n := by
      apply (bij n).1
      show (fun k => frobenius S p (z (n + 1) k))
          - perfLevelOp p S Q n (fun k => frobenius S p (z (n + 1) k)) = z n - perfLevelOp p S Q n (z n)
      rw [← perfLevelOp_frobenius, hz (n + 1), hz n]
      ext i
      simp [frobenius_def, Perfection.coeff_pow_p']
    intro k
    have := congrFun h k
    simpa [frobenius_def] using this
  let x : ι → Perfection S p := fun k => ⟨fun n => z n k, fun n => compat n k⟩
  refine ⟨x, ?_, ?_⟩
  · funext i
    apply Perfection.ext
    intro n
    have h1 := congrFun (perfLevelOp_coeff p S Q n x) i
    have hx : (fun i => Perfection.coeff S p n (x i)) = z n := rfl
    rw [hx, hz n] at h1
    exact h1
  · intro y hy
    funext k
    apply Perfection.ext
    intro n
    have h2 : (fun i => Perfection.coeff S p n (y i)) = z n := by
      apply (bij n).1
      show (fun i => Perfection.coeff S p n (y i))
          - perfLevelOp p S Q n (fun i => Perfection.coeff S p n (y i)) = z n - perfLevelOp p S Q n (z n)
      rw [← perfLevelOp_coeff, hy, hz n]
    exact congrFun h2 k

end GlobalTheory
end

section

namespace GlobalTheory

open IsLocalRing

open IsLocalRing in
theorem _root_.GlobalTheory.preTilt_isLocalRing : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Fact ¬IsUnit (p : O)], IsLocalRing (PreTilt O p) := by
  intro p _ O _ _ _
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Perfection.coeff (ModP O p) p 0) := by
    refine ⟨fun x hx => ?_⟩
    have hunit : ∀ n, IsUnit (Perfection.coeff (ModP O p) p n x) := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih =>
        rw [← Perfection.coeff_pow_p' x n] at ih
        exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ih
    let y : Perfection (ModP O p) p := ⟨fun n => ↑(hunit n).unit⁻¹, fun n => by
      have key : (hunit (n + 1)).unit ^ p = (hunit n).unit :=
        Units.ext (by simpa using Perfection.coeff_pow_p' x n)
      rw [← Units.val_pow_eq_pow_val, inv_pow, key]⟩
    have hxy : x * y = 1 := Perfection.ext fun n => by
      rw [map_mul, map_one]
      show Perfection.coeff (ModP O p) p n x * ↑(hunit n).unit⁻¹ = 1
      exact (hunit n).mul_val_inv
    exact ⟨⟨x, y, hxy, mul_comm y x ▸ hxy⟩, rfl⟩
  exact (Perfection.coeff (ModP O p) p 0).domain_isLocalRing

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

namespace PicPi

variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [DecidableEq ι]

theorem exists_one_tmul (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i)
    (z : R i ⊗[(j : ι) → R j] M) : ∃ y : M, (1 : R i) ⊗ₜ y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r y =>
    refine ⟨(Pi.single i r : (j : ι) → R j) • y, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, hA]
    simp
  | add a b ha hb =>
    obtain ⟨ya, rfl⟩ := ha
    obtain ⟨yb, rfl⟩ := hb
    exact ⟨ya + yb, by rw [TensorProduct.tmul_add]⟩

theorem single_smul_eq_zero (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i) (y : M)
    (h : (1 : R i) ⊗ₜ[(j : ι) → R j] y = 0) : (Pi.single i 1 : (j : ι) → R j) • y = 0 := by
  let φ : R i →ₗ[(j : ι) → R j] M →ₗ[(j : ι) → R j] M :=
    LinearMap.mk₂ _ (fun r y => (Pi.single i r : (j : ι) → R j) • y)
      (fun r₁ r₂ y => by simp only [Pi.single_add, add_smul])
      (fun s r y => by
        have hs : (Pi.single i (s • r) : (j : ι) → R j) = s * Pi.single i r := by
          ext j
          by_cases hj : j = i
          · subst hj; simp [Algebra.smul_def, hA]
          · simp [hj]
        simp only [hs, mul_smul])
      (fun r y₁ y₂ => smul_add _ _ _)
      (fun s r y => smul_comm _ _ _)
  have := congrArg (TensorProduct.lift φ) h
  simpa [φ] using this

variable [Fintype ι]

theorem eq_one_of_forall (M : CommRing.Pic ((j : ι) → R j))
    (h : ∀ i, CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M = 1) : M = 1 := by
  letI inst : ∀ i, Algebra ((j : ι) → R j) (R i) := fun i => (Pi.evalRingHom R i).toAlgebra
  have hA : ∀ i, algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i := fun i => rfl
  have e : ∀ i, (R i ⊗[(j : ι) → R j] M) ≃ₗ[R i] R i := by
    intro i
    have hi := h i
    rw [← hA i, CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapAlgebra_apply,
      CommRing.Pic.mk_eq_one_iff] at hi
    exact hi.some
  choose m hm using fun i => exists_one_tmul i M (hA i) ((e i).symm 1)
  let m₀ : M := ∑ i, (Pi.single i 1 : (j : ι) → R j) • m i
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ((j : ι) → R j) M m₀) := by
    intro x
    refine ⟨fun i => e i ((1 : R i) ⊗ₜ x), ?_⟩
    have key : ∀ i, (Pi.single i 1 : (j : ι) → R j) • x =
        (Pi.single i (e i ((1 : R i) ⊗ₜ x)) : (j : ι) → R j) • m i := by
      intro i
      set r := e i ((1 : R i) ⊗ₜ x) with hr
      have h1 : (1 : R i) ⊗ₜ[(j : ι) → R j] x =
          (1 : R i) ⊗ₜ ((Pi.single i r : (j : ι) → R j) • m i) := by
        apply (e i).injective
        rw [← TensorProduct.smul_tmul]
        have h0 : (Pi.single i r : (j : ι) → R j) • (1 : R i) = r := by
          rw [Algebra.smul_def, hA i]; simp
        rw [h0]
        have h5 : (r ⊗ₜ[(j : ι) → R j] m i : R i ⊗[(j : ι) → R j] M) = r • ((1 : R i) ⊗ₜ m i) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h5, map_smul, hm i, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      have h2 : (1 : R i) ⊗ₜ[(j : ι) → R j] (x - (Pi.single i r : (j : ι) → R j) • m i) = 0 := by
        rw [TensorProduct.tmul_sub, h1, sub_self]
      have h3 := single_smul_eq_zero i M (hA i) _ h2
      rw [smul_sub, sub_eq_zero, smul_smul] at h3
      rw [h3, ← Pi.single_mul, one_mul]
    rw [LinearMap.toSpanSingleton_apply, Finset.smul_sum]
    have hs : ∀ i, (fun i => e i ((1 : R i) ⊗ₜ x) : (j : ι) → R j) •
        (Pi.single i 1 : (j : ι) → R j) • m i = (Pi.single i 1 : (j : ι) → R j) • x := by
      intro i
      rw [key i, smul_smul]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [Finset.sum_congr rfl (fun i _ => hs i), ← Finset.sum_smul]
    have h1 : ∑ i, (Pi.single i 1 : (j : ι) → R j) = 1 := by
      simpa using Finset.univ_sum_single (1 : (j : ι) → R j)
    rw [h1, one_smul]
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact CommRing.Pic.mk_eq_self.symm.trans
    (CommRing.Pic.mk_eq_one_iff.mpr ⟨(LinearEquiv.ofBijective _ hbij).symm⟩)

end PicPi

theorem pic_pi_isOfFinOrder : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)],
    (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) →
      ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by
  intro ι _ R _ hR M
  classical
  haveI := Fintype.ofFinite ι
  have hk : 0 < ∏ i, orderOf (CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M) :=
    Finset.prod_pos fun i _ => (hR i _).orderOf_pos
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hk, ?_⟩
  apply PicPi.eq_one_of_forall
  intro i
  rw [map_pow]
  exact orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

end GlobalTheory
end

section

namespace GlobalTheory


open MvPolynomial in
theorem _root_.GlobalTheory.etale_mvPolynomial_map_of_etale {B A N : Type} [CommRing B] [CommRing A] (g : B →+* A)
    (hg : g.Etale) : (MvPolynomial.map (σ := N) g).Etale := by
  letI := g.toAlgebra
  letI : Algebra (MvPolynomial N B) (MvPolynomial N A) := MvPolynomial.algebraMvPolynomial
  exact RingHom.Etale.isStableUnderBaseChange B A (MvPolynomial N B) (MvPolynomial N A) hg

end GlobalTheory
end
