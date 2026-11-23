module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

theorem exists_semilinear_descent_to_baseChange :
  ∀ {LL : Type} [Field LL] [Algebra ℚ LL] (L0 : IntermediateField ℚ LL) {Ks : Type} [Field Ks] [Algebra Ks LL]
    (kKs : Ks →+* L0), (∀ x, ((kKs x : L0) : LL) = algebraMap Ks LL x) →
    ∀ {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL) {n : ℕ} (bs : Fin n → WL), (∀ i, bs i ∈ WK) →
    Submodule.span Ks (Set.range bs) = WK → LinearIndependent LL bs → Submodule.span LL (Set.range bs) = ⊤ →
    ∀ {KT : Type} [Field KT] [Algebra Ks KT] (rd : L0 →+* KT), (∀ s, algebraMap Ks KT s = rd (kKs s)) →
    ∃ Φ : WL →+ KT ⊗[Ks] WK, (∀ (c : L0) (x : WL), Φ ((c : LL) • x) = rd c • Φ x) ∧
      (∀ (f : WL →ₗ[LL] WL) (fr : WK →ₗ[Ks] WK), (∀ w : WK, (fr w : WL) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange KT fr (Φ x)) ∧
      ∀ w : WK, Φ (w : WL) = (1 : KT) ⊗ₜ[Ks] w := by
  intro LL _ _ L0 Ks _ _ kKs hk WL _ _ _ _ WK n bs hb hKs hLi hLs KT _ _ rd hrd
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L0 LL)
    (LinearMap.ker_eq_bot.mpr (algebraMap L0 LL).injective)
  have hπ1 : π 1 = 1 := by
    have := LinearMap.congr_fun hπ 1
    simpa using this
  have hπx : ∀ (c : L0) (y : LL), π ((c : LL) * y) = c * π y := by
    intro c y
    have : ((c : LL) * y) = c • y := (Algebra.smul_def c y).symm
    rw [this, map_smul, smul_eq_mul]
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin n) LL WL, ∀ k, B k = bs k :=
    ⟨Module.Basis.mk hLi (by rw [hLs]), fun k => Module.Basis.mk_apply _ _ k⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : WL →+ KT ⊗[Ks] WK,
      ∀ x, Φ x = ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK)) :=
    ⟨{ toFun := fun x => ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK))
       map_zero' := by simp
       map_add' := by intro x y; simp [map_add (f := _), add_smul, Finset.sum_add_distrib] },
     fun _ => rfl⟩
  have key : ∀ (l : LL) (w : WK), Φ (l • (w : WL)) = rd (π l) • ((1 : KT) ⊗ₜ[Ks] w) := by
    intro l w
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).mp
      (show (w : WL) ∈ Submodule.span Ks (Set.range bs) by rw [hKs]; exact w.2)
    have hw : w = ∑ k, s k • (⟨bs k, hb k⟩ : WK) := by
      apply Subtype.ext; simp [hs]
    have hrep : ∀ k, B.repr (l • (w : WL)) k = l * algebraMap Ks LL (s k) := by
      have : l • (w : WL) = ∑ k, (l * algebraMap Ks LL (s k)) • B k := by
        rw [← hs, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hB, mul_smul, algebraMap_smul]
      intro k
      rw [this, B.repr_sum_self]
    rw [hΦ]
    conv_rhs => rw [hw, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrep, ← hk, mul_comm, hπx, map_mul, ← hrd, TensorProduct.tmul_smul, ← algebraMap_smul KT (s k),
      smul_smul, mul_comm]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro c x
    rw [hΦ, hΦ x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hπx, map_mul, mul_smul]
  · intro f fr hf x
    conv_lhs => rw [← B.sum_repr x]

    rw [map_sum, map_sum, hΦ x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hB, ← hf ⟨bs k, hb k⟩, key, map_smul, LinearMap.baseChange_tmul]
  · intro w
    have := key 1 w
    rw [one_smul, hπ1, map_one, one_smul] at this
    exact this

end GlobalTheory
end

section

open Polynomial IsLocalRing

namespace GlobalTheory

theorem genval_descent {K : Type} [Field K] {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ιV : K →+* V) (sV v : V) (a : K) (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0) :
    ∀ n : ℕ, ∀ p : Polynomial (Polynomial K), p.leadingCoeff.natDegree = n → p ≠ 0 →
      p.eval₂ (eval₂RingHom ιV sV) v = 0 →
      ∃ q : Polynomial K, q ≠ 0 ∧ q.eval₂ ((residue V).comp ιV) (residue V v) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp hpv
  by_cases hq : p.map (evalRingHom a) = 0
  · have hdvd : C (X - C a) ∣ p := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      rw [dvd_iff_isRoot]
      have := congrArg (fun q => q.coeff i) hq
      simpa [coeff_map] using this
    obtain ⟨p', rfl⟩ := hdvd
    have hp' : p' ≠ 0 := by rintro rfl; simp at hp
    have hXa : (X - C a : Polynomial K) ≠ 0 := X_sub_C_ne_zero a
    refine ih p'.leadingCoeff.natDegree ?_ p' rfl hp' ?_
    · rw [← hn, leadingCoeff_mul, leadingCoeff_C,
        natDegree_mul hXa (leadingCoeff_ne_zero.mpr hp'), natDegree_X_sub_C]
      omega
    · rw [eval₂_mul, eval₂_C] at hpv
      have h2 : (eval₂RingHom ιV sV) (X - C a) = sV - ιV a := by simp
      rw [h2] at hpv
      exact (mul_eq_zero.mp hpv).resolve_left hne
  · refine ⟨_, hq, ?_⟩
    have h1 : (residue V).comp (eval₂RingHom ιV sV) =
        ((residue V).comp ιV).comp (evalRingHom a) := by
      apply Polynomial.ringHom_ext
      · intro c; simp
      · have : residue V sV = residue V (ιV a) := by
          rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
        simpa using this
    rw [eval₂_map, ← h1, ← hom_eval₂, hpv, map_zero]

theorem genval_residue_bij {K : Type} [Field K] [IsAlgClosed K] {L : Type} [Field L]
    (V : ValuationSubring L) (ιV : K →+* V) (sV : V) (a : K)
    (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0)
    (halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
      p.eval₂ (eval₂RingHom ιV sV) v = 0) :
    Function.Bijective ((residue V).comp ιV) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro x
  obtain ⟨v, rfl⟩ := residue_surjective x
  obtain ⟨p, hp, hpv⟩ := halg v
  obtain ⟨q, hq, hqv⟩ := genval_descent ιV sV v a hsa hne _ p rfl hp hpv
  refine ⟨q * C (q.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq, ?_⟩
  rw [eval₂_mul, hqv, zero_mul]

theorem genval (K : Type) [Field K] [IsAlgClosed K] : ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by
  let L := AlgebraicClosure (RatFunc K)
  let φ0 : Polynomial K →+* L := algebraMap (Polynomial K) L
  have hφ0 : Function.Injective φ0 := by
    have : φ0 = (algebraMap (RatFunc K) L).comp (algebraMap (Polynomial K) (RatFunc K)) :=
      IsScalarTower.algebraMap_eq _ _ _
    rw [this]
    exact (algebraMap (RatFunc K) L).injective.comp (IsFractionRing.injective _ _)
  let ι : K →+* L := φ0.comp C
  let s : L := φ0 X
  have hev : ∀ P : Polynomial K, P.eval₂ ι s = φ0 P := by
    intro P
    have : eval₂RingHom ι s = φ0 := Polynomial.ringHom_ext (fun c => by simp [ι]) (by simp [s])
    exact congrArg (fun f => f P) this
  refine ⟨L, inferInstance, inferInstance, ι, s, ?_, ?_⟩
  · intro P hP
    rw [hev] at hP
    exact hφ0 (by rw [hP, map_zero])
  · intro a
    let e : Polynomial K ≃+* φ0.range := RingEquiv.ofBijective φ0.rangeRestrict
      ⟨fun x y h => hφ0 (congrArg Subtype.val h), φ0.rangeRestrict_surjective⟩
    let ψ : φ0.range →+* K := (evalRingHom a).comp e.symm.toRingHom
    obtain ⟨V, hAV, hI⟩ :=
      Ideal.image_subset_nonunits_valuationSubring (RingHom.ker ψ) (RingHom.ker_ne_top ψ)
    have hmemA : ∀ P, φ0 P ∈ V := fun P => hAV ⟨P, rfl⟩
    let ιV : K →+* V := ι.codRestrict V (fun c => hmemA (C c))
    let sV : V := ⟨s, hmemA X⟩
    have hsaL : s - ι a ∈ V.nonunits := by
      apply hI
      refine ⟨φ0.rangeRestrict (X - C a), ?_, ?_⟩
      · rw [SetLike.mem_coe, RingHom.mem_ker]
        have : e.symm (φ0.rangeRestrict (X - C a)) = X - C a :=
          e.symm_apply_apply (X - C a)
        show evalRingHom a (e.symm (φ0.rangeRestrict (X - C a))) = 0
        rw [this]
        simp
      · simp [ι, s]
    have hsa : sV - ιV a ∈ maximalIdeal V := by
      have hsaL' : s - ι a ∈ ((↑) : V → L) '' (maximalIdeal V : Set V) := by
        rw [ValuationSubring.image_maximalIdeal]; exact hsaL
      obtain ⟨w, hw, hw'⟩ := hsaL'
      have heq : sV - ιV a = w := by
        apply Subtype.ext
        exact hw'.symm
      rw [heq]
      exact hw
    have hne : sV - ιV a ≠ 0 := by
      intro h
      have h1 := congrArg Subtype.val h
      have h2 : φ0 (X - C a) = 0 := by simpa [ι, s, sV, ιV] using h1
      exact X_sub_C_ne_zero a (hφ0 (by rw [h2, map_zero]))
    have hcomp : (algebraMap V L).comp (eval₂RingHom ιV sV) = φ0 :=
      Polynomial.ringHom_ext (fun c => by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]; rfl)
        (by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]; rfl)
    have halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
        p.eval₂ (eval₂RingHom ιV sV) v = 0 := by
      intro v
      have h1 : IsAlgebraic (Polynomial K) (v : L) :=
        (IsFractionRing.isAlgebraic_iff (Polynomial K) (RatFunc K) L).mpr
          (Algebra.IsAlgebraic.isAlgebraic _)
      obtain ⟨p, hp, hpv⟩ := h1
      refine ⟨p, hp, ?_⟩
      apply IsFractionRing.injective V L
      rw [hom_eval₂, hcomp, map_zero]
      exact hpv
    have hbij := genval_residue_bij V ιV sV a hsa hne halg
    let E := RingEquiv.ofBijective _ hbij
    have hres : residue V sV = E a := by
      show residue V sV = residue V (ιV a)
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
    refine ⟨V, ιV, E.symm.toRingHom.comp (residue V), sV, ?_, ?_, ?_, rfl, ?_⟩
    · exact RingHom.ext fun c => rfl
    · ext c
      exact E.symm_apply_apply c
    · ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        map_eq_zero_iff _ E.symm.injective, residue_eq_zero_iff]
    · show E.symm (residue V sV) = a
      rw [hres, E.symm_apply_apply]

end GlobalTheory
end

section

namespace GlobalTheory.NormEvalSubBound

open Polynomial

section
variable {C : Type} [NormedField C] [IsUltrametricDist C]

lemma norm_pow_sub_pow_le {y a : C} (hy : ‖y‖ ≤ 1) (ha : ‖a‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - a ^ i‖ ≤ ‖y - a‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - a ^ (i + 1) = y * (y ^ i - a ^ i) + (y - a) * a ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - a‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - a‖ * ‖a‖ ^ i ≤ ‖y - a‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ha) (norm_nonneg _)
        _ = ‖y - a‖ := mul_one _

lemma norm_eval_sub_le (Q : C[X]) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {y a : C} (hy : ‖y‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) : ‖Q.eval y - Q.eval a‖ ≤ ‖y - a‖ := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖Q.coeff i‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
        mul_le_mul (hc i) (norm_pow_sub_pow_le hy ha i) (norm_nonneg _) zero_le_one
    _ = ‖y - a‖ := one_mul _

lemma norm_le_one_of_root (Q : C[X]) (hm : Q.Monic) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {a : C}
    (h : Q.eval a = 0) : ‖a‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  set n := Q.natDegree
  have hpos : 0 < ‖a‖ := lt_trans zero_lt_one hlt
  have hs : ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ ≤ ‖a‖ ^ n / ‖a‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' : i + 1 ≤ n := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    calc ‖Q.coeff i‖ * ‖a‖ ^ i * ‖a‖ ≤ 1 * ‖a‖ ^ i * ‖a‖ := by
          gcongr
          exact hc i
      _ = ‖a‖ ^ (i + 1) := by ring
      _ ≤ ‖a‖ ^ n := pow_le_pow_right₀ hlt.le hi'
  have hlt2 : ‖a‖ ^ n / ‖a‖ < ‖a‖ ^ n := div_lt_self (by positivity) hlt
  have he : Q.eval a = a ^ n + ∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by
    conv_lhs => rw [hm.as_sum]
    simp [eval_finsetSum, n]
  rw [h] at he
  have : a ^ n = -∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by linear_combination -he
  have h3 : ‖a‖ ^ n = ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ := by
    rw [← norm_pow, this, norm_neg]
  linarith
end

theorem main_theorem : (let d1 : {C : Type} → [inst : NormedField C] → [IsUltrametricDist C] → Subfield C → Subring C := @(fun {C : Type} [NormedField C] [IsUltrametricDist C] (F : Subfield C) ↦ Subfield.toSubring F ⊓ Valuation.integer NormedField.valuation); ∀ {C : Type} [inst : NormedField C] [inst_1 : IsUltrametricDist C] {F : Subfield C} [IsAlgClosed C] [inst_3 : IsLocalRing ↥(d1 F)], (∀ (x : C), ‖x‖ ≤ (1 : ℝ) → ∃ y ∈ F, ‖x - y‖ < (1 : ℝ)) → IsAlgClosed (IsLocalRing.ResidueField ↥(d1 F))) := by
  intro d1 C _ _ F _ _ hdense
  have mem : ∀ x : C, x ∈ d1 F ↔ x ∈ F ∧ ‖x‖ ≤ 1 := by
    intro x
    simp only [d1, Subring.mem_inf, Subfield.mem_toSubring, Valuation.mem_integer_iff,
      NormedField.valuation_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
  apply IsAlgClosed.of_exists_root
  intro p hmon hirr
  have hlift : p ∈ lifts (IsLocalRing.residue (d1 F)) :=
    (mem_lifts p).mpr (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_degree_eq_and_monic hlift hmon
  set Q : C[X] := q.map (d1 F).subtype with hQ
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    rw [hQ, coeff_map]; exact ((mem _).mp (q.coeff i).2).2
  have hQm : Q.Monic := hqmon.map _
  have hQdeg : Q.degree ≠ 0 := by
    rw [hQ, degree_map_eq_of_injective (Subring.subtype_injective _), hqdeg]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root Q hQdeg
  have ha1 : ‖a‖ ≤ 1 := norm_le_one_of_root Q hQm hQc ha
  obtain ⟨y, hyF, hya⟩ := hdense a ha1
  have hy1 : ‖y‖ ≤ 1 := by
    have : y = a - (a - y) := by ring
    rw [this]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 ?_)
    rw [norm_neg]; exact hya.le
  let y' : d1 F := ⟨y, (mem y).mpr ⟨hyF, hy1⟩⟩
  refine ⟨IsLocalRing.residue _ y', ?_⟩
  rw [← hqmap, eval_map, eval₂_hom, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hval : ((q.eval y' : d1 F) : C) = Q.eval y := by
    rw [hQ, eval_map]
    exact (eval₂_hom (d1 F).subtype y').symm
  have hn : ‖((q.eval y' : d1 F) : C)‖ < 1 := by
    rw [hval]
    have : Q.eval y = Q.eval y - Q.eval a := by rw [IsRoot.def.mp ha, sub_zero]
    rw [this]
    refine lt_of_le_of_lt (norm_eval_sub_le Q hQc hy1 ha1) ?_
    rwa [norm_sub_rev]
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  have h1 : ((q.eval y' : d1 F) : C) * (v : C) = 1 := by
    have := congrArg Subtype.val huv
    simpa using this
  have hv : ‖(v : C)‖ ≤ 1 := ((mem _).mp v.2).2
  have : ‖((q.eval y' : d1 F) : C) * (v : C)‖ < 1 := by
    rw [norm_mul]
    calc _ ≤ ‖((q.eval y' : d1 F) : C)‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hn
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

end GlobalTheory.NormEvalSubBound
end

section

noncomputable section

namespace GlobalTheory.PolFan.OrbMark

variable {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def pullAdd (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) : LinearMap.BilinForm ℤ X :=
  u.compl₁₂ f.toIntLinearMap f.toIntLinearMap

@[simp] theorem pullAdd_apply (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) (x y : X) : pullAdd f u x y = u (f x) (f y) := rfl

theorem pullAdd_injective {f : X →+ Y} (hf : Function.Surjective f) : Function.Injective (pullAdd f) :=
  fun u u' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    exact LinearMap.congr_fun₂ h a b

def pullAddLin (f : X →+ Y) : LinearMap.BilinForm ℤ Y →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pullAdd f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.PolFan.OrbMark
end
end

section

namespace GlobalTheory.AdaptedFamilyIwasawaDecomposition

theorem exists_adapted_family (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)) (hIL : I ≤ L)
    (hg : Module.finrank ℚ ↥L = g) :
    ∃ rk ≤ g, ∃ (ε : Fin g → Fin r → ℚ), LinearIndependent ℚ ε ∧ (∀ (i : Fin g), ε i ∈ L) ∧
      (∀ (i : Fin g), (↑i : ℕ) < rk → ε i ∈ I) ∧
      ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i : Fin g | (↑i : ℕ) < rk}) := by
  obtain ⟨C₀, hC₀⟩ := I.exists_isCompl
  have hdis : Disjoint I (C₀ ⊓ L) := hC₀.disjoint.mono_right inf_le_left
  have hsup : I ⊔ (C₀ ⊓ L) = L := by
    rw [← sup_inf_assoc_of_le C₀ hIL, hC₀.sup_eq_top, top_inf_eq]
  have hCL : C₀ ⊓ L ≤ L := inf_le_right
  generalize C₀ ⊓ L = C at hdis hsup hCL
  have hdim : Module.finrank ℚ I + Module.finrank ℚ C = g := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq I C
    rw [hsup, hdis.eq_bot, finrank_bot, hg] at h
    omega
  obtain ⟨k, ⟨bI⟩⟩ : ∃ k, Nonempty (Module.Basis (Fin k) ℚ I) := ⟨_, ⟨Module.finBasis ℚ I⟩⟩
  obtain ⟨m, ⟨bC⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℚ C) := ⟨_, ⟨Module.finBasis ℚ C⟩⟩
  rw [Module.finrank_eq_card_basis bI, Module.finrank_eq_card_basis bC, Fintype.card_fin,
    Fintype.card_fin] at hdim
  clear hg
  subst hdim
  let u : Fin k → Fin r → ℚ := I.subtype ∘ bI
  let v : Fin m → Fin r → ℚ := C.subtype ∘ bC
  have hu : LinearIndependent ℚ u := bI.linearIndependent.map' _ (Submodule.ker_subtype I)
  have hv : LinearIndependent ℚ v := bC.linearIndependent.map' _ (Submodule.ker_subtype C)
  have huI : ∀ i, u i ∈ I := fun i => (bI i).2
  have hvC : ∀ i, v i ∈ C := fun i => (bC i).2
  have hus : Submodule.span ℚ (Set.range u) = I := by
    rw [Set.range_comp, ← Submodule.map_span, bI.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hvs : Submodule.span ℚ (Set.range v) ≤ C := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hvC i
  have hli : LinearIndependent ℚ (Sum.elim u v) :=
    hu.sum_type hv (by rw [hus]; exact hdis.mono_right hvs)
  refine ⟨k, Nat.le_add_right k m, Sum.elim u v ∘ finSumFinEquiv.symm,
    hli.comp _ finSumFinEquiv.symm.injective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using hIL (huI j)
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr] using hCL (hvC j)
  · intro i hi
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using huI j
    · simp at hi
  · intro x hx
    rw [← hus] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨j, rfl⟩
    refine ⟨finSumFinEquiv (Sum.inl j), ?_, ?_⟩
    · simp
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

end GlobalTheory.AdaptedFamilyIwasawaDecomposition
end
