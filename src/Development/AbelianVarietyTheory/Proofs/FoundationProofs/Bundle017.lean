module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Norm.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

@[expose] public section

section

open Polynomial

namespace GlobalTheory.NormFormBound

theorem prod_pow_bound {k σ : Type} [Field k] (s : Finset σ) (m : σ → ℕ) (p : σ → k[X]) (d : ℕ)
    (hp : ∀ i, (p i).natDegree ≤ d) :
    (∏ i ∈ s, p i ^ m i).natDegree ≤ (∑ i ∈ s, m i) * d ∧
      (∏ i ∈ s, p i ^ m i).coeff ((∑ i ∈ s, m i) * d) = ∏ i ∈ s, (p i).coeff d ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, add_mul]
    have hpa : (p a ^ m a).natDegree ≤ m a * d :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hp a))
    refine ⟨natDegree_mul_le.trans (add_le_add hpa ih1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hpa ih1, coeff_pow_of_natDegree_le (hp a), ih2, Finset.prod_insert ha]

theorem form_bound {k σ : Type} [Field k] [Infinite k] [Fintype σ] (n : ℕ)
    (F : MvPolynomial σ k[X]) (hF : F.IsHomogeneous n) (h0 : F ≠ 0) :
    ∃ (c : ℕ) (lam : σ → k),
      (∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (MvPolynomial.eval p F).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) → (∀ i, (p i).coeff d = lam i) →
        (MvPolynomial.eval p F).coeff (n * d + c) ≠ 0 := by
  classical
  set c := F.support.sup (fun m => (F.coeff m).natDegree) with hc
  set G : MvPolynomial σ k := ∑ m ∈ F.support, MvPolynomial.monomial m ((F.coeff m).coeff c) with hG
  have hsumdeg : ∀ m ∈ F.support, ∑ i ∈ m.support, m i = n := by
    intro m hm
    have h := hF (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  have hcle : ∀ m ∈ F.support, (F.coeff m).natDegree ≤ c := fun m hm =>
    Finset.le_sup (f := fun m => (F.coeff m).natDegree) hm
  have hG0 : G ≠ 0 := by
    have hne : F.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
    obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image F.support (fun m => (F.coeff m).natDegree) hne
    have hcm : c = (F.coeff m0).natDegree :=
      le_antisymm (Finset.sup_le fun m hm => hmax m hm) (hcle m0 hm0)
    intro hG'
    have h1 := congrArg (AddMonoidAlgebra.coeff · m0) hG'
    rw [hG, MvPolynomial.coeff_sum, Finset.sum_eq_single m0] at h1
    · rw [MvPolynomial.coeff_monomial, if_pos rfl, hcm, MvPolynomial.coeff_zero] at h1
      exact (MvPolynomial.mem_support_iff.mp hm0) (Polynomial.leadingCoeff_eq_zero.mp h1)
    · intro m _ hm
      rw [MvPolynomial.coeff_monomial, if_neg hm]
    · intro h
      exact absurd hm0 h
  obtain ⟨lam, hlam⟩ : ∃ lam : σ → k, MvPolynomial.eval lam G ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hG0 (MvPolynomial.funext fun x => by simpa using hall x)
  refine ⟨c, lam, ?_, ?_⟩
  · intro d p hp
    rw [MvPolynomial.eval_eq]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    have hdeg := (prod_pow_bound m.support m p d hp).1
    rw [hsumdeg m hm] at hdeg
    refine natDegree_mul_le.trans ?_
    have := hcle m hm
    omega
  · intro d p hp hpl
    rw [MvPolynomial.eval_eq, Polynomial.finsetSum_coeff]
    have hterm : ∀ m ∈ F.support, (F.coeff m * ∏ i ∈ m.support, p i ^ m i).coeff (n * d + c) =
        (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      intro m hm
      have hb := prod_pow_bound m.support m p d hp
      rw [hsumdeg m hm] at hb
      rw [add_comm (n * d) c, coeff_mul_add_eq_of_natDegree_le (hcle m hm) hb.1, hb.2]
      simp [hpl]
    rw [Finset.sum_congr rfl hterm]
    have hev : MvPolynomial.eval lam G =
        ∑ m ∈ F.support, (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by

      rw [hG, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.eval_monomial, Finsupp.prod]
    rw [← hev]
    exact hlam

theorem exists_norm_form {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (b : Module.Basis (Fin n) R A) :
    ∃ F : MvPolynomial (Fin n) R, F.IsHomogeneous n ∧
      ∀ p : Fin n → R, MvPolynomial.eval p F = Algebra.norm R (∑ i, p i • b i) := by
  classical
  refine ⟨(Matrix.of fun a c => ∑ i, MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) *
      MvPolynomial.X i).det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    have hC : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) R) =
        MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
    rw [hC]
    have hent : ∀ a ∈ (Finset.univ : Finset (Fin n)), ((Matrix.of fun a c => ∑ i,
        MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) * MvPolynomial.X i) (σ a) a).IsHomogeneous 1 := by
      intro a _
      rw [Matrix.of_apply]
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) (Algebra.leftMulMatrix b (b i) (σ a) a)).mul
        (MvPolynomial.isHomogeneous_X R i)
    have hmul := (MvPolynomial.isHomogeneous_C (Fin n) ((Equiv.Perm.sign σ : ℤ) : R)).mul
      (MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) hent)
    simpa using hmul
  · intro p
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext a c

    simp [map_sum, Matrix.sum_apply, mul_comm]

theorem norm_degree (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) :
    ∃ (c : ℕ) (lam : Fin n → k),
      (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < (d : WithBot ℕ)) →
        ∑ i, (C (lam i) * X ^ d + p i) • b i ≠ 0 ∧
          (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c := by
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  obtain ⟨F, hFh, hFev⟩ := exists_norm_form n b
  have hF0 : F ≠ 0 := by
    intro hF
    have h1 := hFev (fun i => b.repr 1 i)
    rw [hF, map_zero, b.sum_repr 1, map_one] at h1
    exact one_ne_zero h1.symm
  obtain ⟨c, lam, hb1, hb2⟩ := form_bound n F hFh hF0
  refine ⟨c, lam, fun d p hp => ?_, fun d p hp => ?_⟩
  · rw [← hFev]
    exact hb1 d p hp
  · have hq1 : ∀ i, (C (lam i) * X ^ d + p i).natDegree ≤ d := fun i =>
      (natDegree_add_le _ _).trans
        (max_le (natDegree_C_mul_X_pow_le _ _) (natDegree_le_of_degree_le (hp i).le))
    have hq2 : ∀ i, (C (lam i) * X ^ d + p i).coeff d = lam i := fun i => by
      rw [coeff_add, coeff_C_mul_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt (hp i), add_zero]
    have hN : (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).coeff (n * d + c) ≠ 0 := by
      rw [← hFev]
      exact hb2 d (fun i => C (lam i) * X ^ d + p i) hq1 hq2
    refine ⟨fun h0 => hN (by rw [h0, Algebra.norm_zero, coeff_zero]), ?_⟩
    apply le_antisymm
    · rw [← hFev]
      exact hb1 d (fun i => C (lam i) * X ^ d + p i) hq1
    · exact le_natDegree_of_ne_zero hN

end GlobalTheory.NormFormBound
end

section

namespace GlobalTheory

theorem mvPowerSeries_three_eq_zero_of_subst_lines :
    ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K),
      (∀ t : Fin 3 → K, (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) →
      Φ = 0 := by
  intro K _ _ Φ h
  ext d
  set n := ∑ i, d i with hn
  let S : Finset (Fin 3 →₀ ℕ) :=
    (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => n)).filter (fun e => ∑ i, e i = n)
  have hS : ∀ e, e ∈ S ↔ ∑ i, e i = n := by
    intro e
    simp only [S, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
    intro he i
    change e i ≤ n
    rw [← he]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  let P : MvPolynomial (Fin 3) K := ∑ e ∈ S, MvPolynomial.monomial e (MvPowerSeries.coeff e Φ)
  have hcoef : ∀ t : Fin 3 → K, PowerSeries.coeff n (MvPowerSeries.subst
      (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) = MvPolynomial.eval t P := by
    intro t
    have ha : MvPowerSeries.HasSubst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
        rw [map_mul]; exact mul_eq_zero_of_right _ (MvPowerSeries.constantCoeff_X ()))
    have hprod : ∀ e : Fin 3 →₀ ℕ,
        (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) =
          PowerSeries.C (∏ s, t s ^ e s) * PowerSeries.X ^ (∑ s, e s) := by
      intro e
      rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
    have h1 : PowerSeries.coeff n (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) =
        ∑ᶠ e : Fin 3 →₀ ℕ, MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) :=
      MvPowerSeries.coeff_subst ha Φ (Finsupp.single () n)
    have hsupp : Function.support (fun e : Fin 3 →₀ ℕ =>
        MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k)) ⊆ S := by
      intro e he
      rw [Function.mem_support] at he
      rw [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul] at he
      rw [Finset.mem_coe, hS]
      by_contra hne
      exact he (by simp [Ne.symm hne])
    rw [h1]
    rw [finsum_eq_sum_of_support_subset _ (s := S) hsupp]
    simp only [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul]

    · simp only [P, map_sum, MvPolynomial.eval_monomial]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [if_pos ((hS e).1 he).symm, Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
  have hP : P = 0 := MvPolynomial.funext (fun t => by rw [← hcoef, h t, map_zero, map_zero])
  have hd := congrArg (AddMonoidAlgebra.coeff · d) hP
  simp only [P, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hS d).2 rfl)] at hd
  simpa using hd

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem algebraMap_norm_dvd_polyX {k A : Type} [Field k] [CommRing A] [Algebra k[X] A] {n : ℕ}
    (b : Module.Basis (Fin n) k[X] A) (g : A) : g ∣ algebraMap k[X] A (Algebra.norm k[X] g) := by
  classical
  set M := Algebra.leftMulMatrix b g with hM
  have hCH : Polynomial.aeval g M.charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, map_zero, ← hM, Matrix.aeval_self_charpoly]
  have hsplit := Polynomial.X_mul_divX_add M.charpoly
  have h0 : g * Polynomial.aeval g M.charpoly.divX + algebraMap k[X] A (M.charpoly.coeff 0) = 0 := by
    have := congrArg (Polynomial.aeval g) hsplit
    rw [hCH, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at this
    exact this
  have hdet : Algebra.norm k[X] g = (-1) ^ n * M.charpoly.coeff 0 := by
    rw [Algebra.norm_eq_matrix_det b, ← hM, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
  rw [hdet, map_mul, eq_neg_of_add_eq_zero_right h0]
  exact ⟨-(algebraMap k[X] A ((-1) ^ n) * Polynomial.aeval g M.charpoly.divX), by ring⟩

theorem exists_lowDegree_coords_mod : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (g : A) (q : k[X]) (d : ℕ), g ≠ 0 → q ≠ 0 → (Algebra.norm k[X] g).natDegree + q.natDegree ≤ d + 1 →
 ∀ w : A, ∃ p : Fin n → k[X], (∀ i, (p i).natDegree ≤ d) ∧ w - ∑ i, p i • b i ∈ Ideal.span {g * algebraMap k[X] A q} := by
  intro k A _ _ _ _ n b g q d hg hq hdeg w
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  have hN : Algebra.norm k[X] g ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  set p₀ := Algebra.norm k[X] g * q with hp₀
  have hp₀0 : p₀ ≠ 0 := mul_ne_zero hN hq
  have hp₀deg : p₀.natDegree ≤ d + 1 := by rw [hp₀, natDegree_mul hN hq]; exact hdeg
  refine ⟨fun i => b.repr w i % p₀, ?_, ?_⟩
  · intro i
    by_cases h0 : b.repr w i % p₀ = 0
    · simp [h0]
    · have hlt : (b.repr w i % p₀).degree < p₀.degree := EuclideanDomain.mod_lt _ hp₀0
      have := Polynomial.natDegree_lt_natDegree h0 hlt
      show (b.repr w i % p₀).natDegree ≤ d
      omega
  · have key : w - ∑ i, (b.repr w i % p₀) • b i
        = algebraMap k[X] A p₀ * ∑ i, (b.repr w i / p₀) • b i := by
      set a := b.repr w with ha
      have hw : w = ∑ i, a i • b i := (b.sum_repr w).symm
      rw [hw, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ← eq_sub_of_add_eq (EuclideanDomain.div_add_mod (a i) p₀), mul_smul,
        Algebra.smul_def]
    rw [key, Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := algebraMap_norm_dvd_polyX b g
    refine ⟨c * ∑ i, (b.repr w i / p₀) • b i, ?_⟩
    rw [hp₀, map_mul, hc]
    ring

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem newton_powerSeries_of_surjective_linearisation (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ]
    (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k))
    (hL : Function.Surjective L)
    (h0 : ∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0)
    (hG : ∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e -
        PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) :
    ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  classical
  let r := Function.surjInv hL
  have hLr : ∀ v, L (r v) = v := Function.surjInv_eq hL
  let step : ℕ → (ι → PowerSeries k) → (ι → PowerSeries k) := fun m x i =>
    x i + PowerSeries.X ^ m * PowerSeries.C (r (fun e => -PowerSeries.coeff m (G x e)) i)
  let sq : ℕ → (ι → PowerSeries k) := fun n =>
    Nat.rec (motive := fun _ => ι → PowerSeries k) (fun i => PowerSeries.C (x₀ i)) (fun n x => step (n + 1) x) n
  have sq_zero : sq 0 = fun i => PowerSeries.C (x₀ i) := rfl
  have sq_succ : ∀ n, sq (n + 1) = step (n + 1) (sq n) := fun n => rfl
  have coeffXC : ∀ (m j : ℕ) (c : k),
      PowerSeries.coeff j ((PowerSeries.X : PowerSeries k) ^ m * PowerSeries.C c) = if j = m then c else 0 := by
    intro m j c
    rw [mul_comm, PowerSeries.coeff_C_mul_X_pow]
  have inv : ∀ n, (∀ i, PowerSeries.constantCoeff (sq n i) = x₀ i) ∧
      ∀ e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G (sq n) e := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => by simp [sq_zero], fun e => ?_⟩
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, sq_zero]
      exact h0 e
    | succ n ih =>
      have hc : ∀ i, PowerSeries.constantCoeff (sq (n + 1) i) = x₀ i := by
        intro i
        simp [sq_succ, step, ih.1 i]
      refine ⟨hc, fun e => ?_⟩
      set x := sq n with hx
      set v : κ → k := fun e => -PowerSeries.coeff (n + 1) (G x e) with hv
      have key := hG x (fun i => PowerSeries.C (r v i)) (n + 1) (by omega) ih.1 e
      have hcv : (fun i => PowerSeries.constantCoeff (PowerSeries.C (r v i))) = r v := by
        funext i; simp
      rw [hcv, hLr] at key
      have hs : sq (n + 1) = fun i => x i + PowerSeries.X ^ (n + 1) * PowerSeries.C (r v i) := by
        rw [sq_succ]
      have h2 : (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) ∣
          G x e + PowerSeries.X ^ (n + 1) * PowerSeries.C (v e) := by
        rw [PowerSeries.X_pow_dvd_iff]
        intro j hj
        rw [map_add (f := _), coeffXC]
        rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
        · have := (PowerSeries.X_pow_dvd_iff.mp (ih.2 e)) j hj'
          rw [this, if_neg (by omega), add_zero]
        · have hjn : j = n + 1 := by omega
          subst hjn
          simp [hv]
      have := dvd_add key h2
      rw [hs]
      convert this using 1
      ring
  have stab : ∀ i j n, j ≤ n → PowerSeries.coeff j (sq n i) = PowerSeries.coeff j (sq j i) := by
    intro i j n hjn
    induction n, hjn using Nat.le_induction with
    | base => rfl
    | succ n hjn ihn =>
      rw [← ihn, sq_succ]
      simp only [step, map_add (f := _)]
      rw [coeffXC, if_neg (by omega), add_zero]
  let xl : ι → PowerSeries k := fun i => PowerSeries.mk (fun j => PowerSeries.coeff j (sq j i))
  have hdiff : ∀ n i, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ xl i - sq n i := by
    intro n i
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    simp only [xl, map_sub, PowerSeries.coeff_mk]
    rw [stab i j n (by omega), sub_self]
  have hlim : ∀ n e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e := by
    intro n e
    choose d hd using hdiff n
    have hx : xl = fun i => sq n i + PowerSeries.X ^ (n + 1) * d i := by
      funext i; rw [← hd i]; ring
    have key := hG (sq n) d (n + 1) (by omega) (inv n).1 e
    rw [← hx] at key
    have k1 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e - G (sq n) e := by
      have h3 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) :=
        pow_dvd_pow _ (by omega)
      have := dvd_add (h3.trans key) (dvd_mul_right ((PowerSeries.X : PowerSeries k) ^ (n + 1))
        (PowerSeries.C (L (fun i => PowerSeries.constantCoeff (d i)) e)))
      simpa using this
    have := dvd_add k1 ((inv n).2 e)
    simpa using this
  refine ⟨xl, fun i => ?_, fun e => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [xl, PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (inv 0).1 i
  · ext j
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.mp (hlim j e) j (by omega)

theorem newton_powerSeries_target : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 :=
  fun k ι κ _ _ _ G x₀ L hL h0 hG => newton_powerSeries_of_surjective_linearisation k ι κ G x₀ L hL h0 hG

end GlobalTheory
end

section

namespace GlobalTheory

open Polynomial

theorem valuationSubring_pow_sub_one_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x : Ω}
    (hx : A.valuation x ≤ 1) (k : ℕ) :
    A.valuation (x ^ k - 1) ≤ A.valuation (x - 1) := by
  have h : x ^ k - 1 = (∑ i ∈ Finset.range k, x ^ i) * (x - 1) := (geom_sum_mul x k).symm
  rw [h, map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, x ^ i) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_pow]; exact pow_le_one' hx i
  exact mul_le_of_le_one_left' hs

theorem valuation_zeta_sub_one_pow_totient (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω) (hn : 1 ≤ n)
    (hζ : IsPrimitiveRoot ζ (l ^ n)) :
    A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hv1 : ∀ {μ : Ω}, IsPrimitiveRoot μ (l ^ n) → A.valuation μ ≤ 1 := by
    intro μ hμ
    have h1 : A.valuation μ ^ (l ^ n) = 1 := by rw [← map_pow, hμ.pow_eq_one, map_one]
    exact (pow_eq_one_iff.1 h1 |>.resolve_right hN.ne').le
  have key : ∀ μ ∈ primitiveRoots (l ^ n) Ω, A.valuation (1 - μ) = A.valuation (ζ - 1) := by
    intro μ hμ
    rw [mem_primitiveRoots hN] at hμ
    rw [Valuation.map_sub_swap]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply le_antisymm
    · rw [← hi]; exact valuationSubring_pow_sub_one_le A (hv1 hζ) i
    · rw [← hj]; exact valuationSubring_pow_sub_one_le A (hv1 hμ) j
  have hcyc := cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : (l : Ω) = ∏ μ ∈ primitiveRoots (l ^ (k + 1)) Ω, (1 - μ) := by
    have := congrArg (eval 1) hcyc
    rw [eval_one_cyclotomic_prime_pow, eval_prod] at this
    simpa using this
  rw [h1, map_prod, Finset.prod_congr rfl key, Finset.prod_const, hζ.card_primitiveRoots]

end GlobalTheory
end
