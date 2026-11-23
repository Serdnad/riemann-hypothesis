module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.Lattice
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

section

open Polynomial

namespace GlobalTheory

theorem isUnit_aeval_of_forall_isUnit_sub {A : Type*} [Ring A] [Algebra ℂ A] (T : A)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ A c)) (q : ℂ[X]) (hq : q ≠ 0) :
    IsUnit (aeval T q) := by
  have hs : spectrum ℂ T = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false, spectrum.notMem_iff]
    simpa using (h c).neg
  by_cases hd : 0 < q.degree
  · have h1 := spectrum.map_polynomial_aeval_of_degree_pos T q hd
    rw [hs, Set.image_empty] at h1
    have h0 : (0 : ℂ) ∉ spectrum ℂ (aeval T q) := by rw [h1]; simp
    exact (spectrum.zero_notMem_iff ℂ).1 h0
  · have h2 : q = C (q.coeff 0) := eq_C_of_degree_le_zero (not_lt.1 hd)
    have h3 : q.coeff 0 ≠ 0 := fun h => hq (by rw [h2, h, C_0])
    rw [h2, aeval_C]
    exact (IsUnit.mk0 _ h3).map _

theorem linearIndependent_of_sub_apply_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c))
    (v : V) (hv : v ≠ 0) (w : ℂ → V)
    (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  set q : ℂ[X] := ∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j) with hqdef
  have hq0 : aeval T q v = 0 := by
    have h1 : ∀ k ∈ s, aeval T (C (g k) * ∏ j ∈ s.erase k, (X - C j)) v
        = aeval T (∏ j ∈ s, (X - C j : ℂ[X])) (g k • w k) := by
      intro k hk
      rw [← Finset.prod_erase_mul s _ hk, ← hw k, map_mul, map_mul, aeval_C, map_sub, aeval_X,
        aeval_C, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        map_smul, map_smul]

    rw [hqdef, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl h1, ← map_sum, hg, map_zero]
  have hq : q = 0 := by
    by_contra hne
    have hu := isUnit_aeval_of_forall_isUnit_sub T h q hne
    have hinj := ((Module.End.isUnit_iff _).1 hu).1
    exact hv (hinj (by rw [hq0, map_zero]))
  have h2 : eval i q = g i * ∏ j ∈ s.erase i, (i - j) := by
    rw [hqdef, Polynomial.eval_finsetSum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro k _ hki
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hki.symm, hi⟩)
        (by simp), mul_zero]
    · intro h; exact absurd hi h
  rw [hq, eval_zero] at h2
  refine (mul_eq_zero.1 h2.symm).resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.mem_erase.1 hj).1.symm

theorem dixmier_schur_of_rank_le_aleph0 :
    ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V),
      Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
      (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  intro V ι _ _ ρ T hV hrank hirr hcomm
  by_contra hne
  push_neg at hne
  have hunit : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c) := by
    intro c
    set S := T - algebraMap ℂ (Module.End ℂ V) c with hS
    have hS0 : S ≠ 0 := by
      intro h0
      apply hne c
      rw [← Algebra.algebraMap_eq_smul_one]
      exact sub_eq_zero.1 h0
    have hSc : ∀ i x, S (ρ i x) = ρ i (S x) := by
      intro i x
      have := LinearMap.congr_fun (hcomm i) x
      simp only [Module.End.mul_apply] at this
      simp [hS, this, Module.algebraMap_end_apply]
    rw [Module.End.isUnit_iff]
    constructor
    · rw [← LinearMap.ker_eq_bot]
      refine (hirr _ ?_).resolve_right ?_
      · intro i x hx
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hSc, hx, map_zero]
      · rw [LinearMap.ker_eq_top]; exact hS0
    · rw [← LinearMap.range_eq_top]
      refine (hirr _ ?_).resolve_left ?_
      · rintro i _ ⟨x, rfl⟩
        exact ⟨ρ i x, hSc i x⟩
      · rw [LinearMap.range_eq_bot]; exact hS0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  choose w hw using fun c => ((Module.End.isUnit_iff _).1 (hunit c)).2 v
  have hli := linearIndependent_of_sub_apply_eq T hunit v hv w hw
  have h1 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)

end GlobalTheory
end

section

open NumberField

noncomputable section

open Polynomial

namespace GlobalTheory.CycSpanFin

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem commute_aeval_left {x y : Module.End ℂ V} (h : Commute x y) (p : ℂ[X]) : Commute (aeval x p) y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n a => rw [aeval_monomial]; exact (Algebra.commute_algebraMap_left a y).mul_left (h.pow_left n)

theorem coeff_mem_span_fin {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} {a : ℕ → M} {p : ℂ → M}
    (hp : ∀ u, p u = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) {i : ℕ} (hi : i < n + 1) :
    a i ∈ Submodule.span ℂ (Set.range fun j : Fin (n + 1) => p ((j : ℕ) : ℂ)) := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  set Q : ℂ[X] := ∑ j ∈ Finset.range (n + 1), monomial j (φ (a j)) with hQdef
  have hev : ∀ u, Q.eval u = φ (p u) := by
    intro u

    rw [hp, map_sum]
    simp only [Q, Polynomial.eval_finsetSum, eval_monomial]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hdeg : Q.natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have h0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f := fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Nat.cast_injective.comp Fin.val_injective) ?_ ?_
    · intro j
      rw [hev]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simpa using Nat.lt_succ_of_le hdeg
  have hcoeff : Q.coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
  rw [hQdef, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi), Polynomial.coeff_monomial_same] at hcoeff
  · exact hcoeff
  · intro j _ hji
    exact Polynomial.coeff_monomial_of_ne _ hji.symm

def stabAlg (N : Submodule ℂ V) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {T | ∀ v ∈ N, T v ∈ N}
  mul_mem' ha hb v hv := ha _ (hb v hv)
  add_mem' ha hb v hv := N.add_mem (ha v hv) (hb v hv)
  algebraMap_mem' r v hv := by
    rw [Module.algebraMap_end_apply]
    exact N.smul_mem r hv

def ext (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ k : Fin (d + 1), N.map (T ^ (k : ℕ))

theorem le_ext (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : N ≤ ext T d N := fun v hv =>
  Submodule.mem_iSup_of_mem (0 : Fin (d + 1)) ⟨v, hv, by simp⟩

theorem pow_mem_ext (T : Module.End ℂ V) {d k : ℕ} (hk : k ≤ d) {N : Submodule ℂ V} {v : V} (hv : v ∈ N) :
    (T ^ k) v ∈ ext T d N :=
  Submodule.mem_iSup_of_mem (⟨k, by omega⟩ : Fin (d + 1)) (Submodule.mem_map_of_mem hv)

theorem aeval_mem_ext (T : Module.End ℂ V) {Q : ℂ[X]} (hQ : Q ≠ 0) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, aeval T Q v = 0) (p : ℂ[X]) {v : V} (hv : v ∈ N) : aeval T p v ∈ ext T Q.natDegree N := by
  set Q' := Q * C Q.leadingCoeff⁻¹ with hQ'
  have hm : Q'.Monic := monic_mul_leadingCoeff_inv hQ
  have hdeg : Q'.natDegree = Q.natDegree := by
    rw [hQ', natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hQ))]
  have hQ'v : aeval T Q' v = 0 := by
    rw [hQ', mul_comm, map_mul, mul_apply_eq_comp, hN v hv, map_zero]
  have hsplit : p = p %ₘ Q' + (p /ₘ Q') * Q' := by
    rw [mul_comm]; exact (modByMonic_add_div p Q').symm
  rw [hsplit, map_add (f := _), LinearMap.add_apply, map_mul, mul_apply_eq_comp, hQ'v, map_zero, add_zero]
  have hlt : (p %ₘ Q').natDegree < Q.natDegree + 1 := by
    have := natDegree_modByMonic_le p hm
    omega
  rw [aeval_eq_sum_range' hlt, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (pow_mem_ext T (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hv)

theorem ext_stable (T : Module.End ℂ V) {Q : ℂ[X]} (hQ : Q ≠ 0) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, aeval T Q v = 0) : ∀ v ∈ ext T Q.natDegree N, T v ∈ ext T Q.natDegree N := by
  have : ext T Q.natDegree N ≤ (ext T Q.natDegree N).comap T := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    change T ((T ^ (k : ℕ)) x) ∈ ext T Q.natDegree N
    have := aeval_mem_ext T hQ hN (X ^ ((k : ℕ) + 1)) hx
    rwa [map_pow, aeval_X, pow_succ', mul_apply_eq_comp] at this
  exact fun v hv => this hv

theorem ext_stable_comm (T S : Module.End ℂ V) (d : ℕ) (hST : Commute S T) {N : Submodule ℂ V}
    (hS : ∀ v ∈ N, S v ∈ N) : ∀ v ∈ ext T d N, S v ∈ ext T d N := by
  have : ext T d N ≤ (ext T d N).comap S := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    change S ((T ^ (k : ℕ)) x) ∈ ext T d N
    have h := congrArg (fun F : Module.End ℂ V => F x) (hST.pow_right (k : ℕ)).eq
    simp only [mul_apply_eq_comp] at h
    rw [h]
    exact pow_mem_ext T (Nat.lt_succ_iff.1 k.2) (hS x hx)
  exact fun v hv => this hv

theorem ext_kill (T R : Module.End ℂ V) (d : ℕ) (hRT : Commute R T) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, R v = 0) : ∀ v ∈ ext T d N, R v = 0 := by
  have : ext T d N ≤ LinearMap.ker R := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [LinearMap.mem_ker]
    have h := congrArg (fun F : Module.End ℂ V => F x) (hRT.pow_right (k : ℕ)).eq
    simp only [mul_apply_eq_comp] at h
    rw [h, hN x hx, map_zero]
  exact fun v hv => this hv

theorem exists_stable (a : ℕ → Module.End ℂ V) (Q : ℕ → ℂ[X]) (hc : ∀ i j, Commute (a i) (a j))
    (hQ : ∀ j, Q j ≠ 0) (w : V) (hw : ∀ j, aeval (a j) (Q j) w = 0) : ∀ m : ℕ, ∃ N : Submodule ℂ V,
      FiniteDimensional ℂ N ∧ w ∈ N ∧ (∀ j < m, ∀ v ∈ N, a j v ∈ N) ∧ (∀ j, ∀ v ∈ N, aeval (a j) (Q j) v = 0) := by
  intro m
  induction m with
  | zero =>
    exact ⟨Submodule.span ℂ {w}, inferInstance, Submodule.mem_span_singleton_self w, by simp, fun j v hv => by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hw, smul_zero]⟩
  | succ m ih =>
    obtain ⟨N, hf, hwN, hst, hk⟩ := ih
    refine ⟨ext (a m) (Q m).natDegree N, ?_, le_ext _ _ _ hwN, ?_, ?_⟩
    · unfold ext
      infer_instance
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact ext_stable_comm (a m) (a j) _ (hc j m) (hst j h)
      · subst j
        exact ext_stable (a m) (hQ m) (hk m)
    · intro j
      exact ext_kill (a m) _ _ (commute_aeval_left (hc j m) _) (hk j)

theorem finiteDimensional_span_adjoin : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V)
    (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) →
    ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) →
    FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by
  intro V _ _ n c g hg hc w P hP hw
  obtain ⟨N, hf, hwN, hst, -⟩ := exists_stable (fun j : ℕ => g (j : ℂ)) (fun j => P (j : ℂ))
    (fun i j => hc _ _) (fun j => hP _) w (fun j => hw _) (n + 1)
  have hgS : ∀ u, g u ∈ stabAlg N := by
    intro u
    have hspan : Submodule.span ℂ (Set.range fun j : Fin (n + 1) => g ((j : ℕ) : ℂ)) ≤
        Subalgebra.toSubmodule (stabAlg N) :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact fun v hv => hst j j.2 v hv)
    apply hspan
    rw [hg u]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (coeff_mem_span_fin hg (Finset.mem_range.1 hi))
  have hA : Algebra.adjoin ℂ (Set.range g) ≤ stabAlg N :=
    Algebra.adjoin_le (by rintro _ ⟨u, rfl⟩; exact hgS u)
  have hle : Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w} ≤ N :=
    Submodule.span_le.2 (by rintro _ ⟨b, hb, rfl⟩; exact hA hb w hwN)
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CycSpanFin
end
end

section

open Polynomial IsLocalRing

namespace GlobalTheory

theorem kummer_residue_aeval (T V : Type) [CommRing T] [IsLocalRing T] [CommRing V] [IsLocalRing V]
    [Algebra T V] [IsLocalHom (algebraMap T V)] (γ : V) (p : T[X]) :
    residue V (aeval γ p) = aeval (residue V γ) (p.map (residue T)) := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a hp => simp [hp, pow_succ, ← mul_assoc]

theorem kummer_step_one (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra T V]
    [IsLocalHom (algebraMap T V)]
    (γ : V) (ϖ u : T) (k : ℕ) (hϖ : Irreducible ϖ) (hu : IsUnit u) (hk : IsUnit (k : T))
    (hk0 : 0 < k) (hγ : γ ^ k = algebraMap T V u) (h : T[X])
    (hm : aeval γ h ∈ maximalIdeal V) :
    ∃ ν r : T[X], IsUnit (aeval γ ν) ∧
      aeval γ h * aeval γ ν = algebraMap T V ϖ * aeval γ r := by
  set γ' := residue V γ with hγ'
  set f : (ResidueField T)[X] := X ^ k - C (residue T u) with hf
  have hkκ : ((k : ℕ) : ResidueField T) ≠ 0 := by
    have := (hk.map (residue T)).ne_zero
    simpa using this
  have hu' : residue T u ≠ 0 := (hu.map (residue T)).ne_zero
  have hsep : f.Separable := separable_X_pow_sub_C _ hkκ hu'
  have hfγ : aeval γ' f = 0 := by
    have := congrArg (residue V) hγ
    simp only [map_pow] at this
    simp [hf, hγ', this]
  have hhm : aeval γ' (h.map (residue T)) = 0 := by
    rw [hγ', ← kummer_residue_aeval]
    exact (residue_eq_zero_iff _).mpr hm
  obtain ⟨νb, hνb⟩ := minpoly.dvd (ResidueField T) γ' hfγ
  obtain ⟨qb, hqb⟩ := minpoly.dvd (ResidueField T) γ' hhm
  have hνne : aeval γ' νb ≠ 0 := by
    intro h0
    have hcop : IsCoprime (minpoly (ResidueField T) γ') νb := Separable.isCoprime (hνb ▸ hsep)
    obtain ⟨a, b, hab⟩ := hcop
    have := congrArg (aeval γ') hab
    simp [minpoly.aeval, h0] at this
  obtain ⟨ν, rfl⟩ := map_surjective (residue T) residue_surjective νb
  obtain ⟨q, rfl⟩ := map_surjective (residue T) residue_surjective qb
  set D : T[X] := h * ν - q * (X ^ k - C u) with hD
  have hDm : D.map (residue T) = 0 := by
    have e1 : (X ^ k - C u).map (residue T) = f := by simp [hf]
    rw [hD, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, e1, hνb, hqb]
    ring
  have hDI : D ∈ Ideal.span {C ϖ} := by
    have : D ∈ Ideal.map (C : T →+* T[X]) (maximalIdeal T) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [← residue_eq_zero_iff, ← coeff_map, hDm, coeff_zero]
    rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton] at this
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hDI
  refine ⟨ν, r, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, kummer_residue_aeval]
    exact hνne
  · have := congrArg (aeval γ) hr
    simp only [hD, map_mul, map_sub, map_pow, aeval_X, aeval_C, hγ, sub_self, mul_zero,
      sub_zero] at this
    rw [← this, mul_comm]

theorem kummer_valuation : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (γ : V) (ϖ u : T) (k : ℕ), Irreducible ϖ → IsUnit u → IsUnit (k : T) → 0 < k →
    γ ^ k = algebraMap T V u →
    ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h' := by
  intro T V _ _ _ _ _ _ _ _ hinj γ ϖ u k hϖ hu hk hk0 hγ h
  by_cases h0 : aeval γ h = 0
  · exact Or.inl h0
  right
  have hϖV : ¬ IsUnit (algebraMap T V ϖ) := fun h' => hϖ.not_isUnit (isUnit_of_map_unit _ _ h')
  suffices H : ∀ x : V, ∀ h : T[X], aeval γ h = x → x ≠ 0 →
      ∃ (a : ℕ) (h' c : T[X]), IsUnit (aeval γ c) ∧ IsUnit (aeval γ h') ∧
        aeval γ c * aeval γ h = algebraMap T V ϖ ^ a * aeval γ h' from H _ h rfl h0
  intro x
  refine (wellFounded_dvdNotUnit (α := V)).induction
    (C := fun x => ∀ h : T[X], aeval γ h = x → x ≠ 0 →
      ∃ (a : ℕ) (h' c : T[X]), IsUnit (aeval γ c) ∧ IsUnit (aeval γ h') ∧
        aeval γ c * aeval γ h = algebraMap T V ϖ ^ a * aeval γ h') x ?_
  intro x ih h hx hx0
  subst hx
  by_cases hunit : IsUnit (aeval γ h)
  · exact ⟨0, h, 1, by simp, hunit, by simp⟩
  have hm : aeval γ h ∈ maximalIdeal V := (mem_maximalIdeal _).mpr hunit
  obtain ⟨ν, r, hν, hr⟩ := kummer_step_one T V γ ϖ u k hϖ hu hk hk0 hγ h hm
  have hr0 : aeval γ r ≠ 0 := by
    intro h'
    rw [h', mul_zero] at hr
    exact mul_ne_zero hx0 hν.ne_zero hr
  have hdvd : DvdNotUnit (aeval γ r) (aeval γ h) := by
    refine ⟨hr0, algebraMap T V ϖ * ↑hν.unit⁻¹, ?_, ?_⟩
    · intro hu'
      exact hϖV (isUnit_of_mul_isUnit_left hu')
    · calc aeval γ h = aeval γ h * aeval γ ν * ↑hν.unit⁻¹ := by
            rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
        _ = _ := by rw [hr]; ring
  obtain ⟨a, h', c, hc, hh', he⟩ := ih _ hdvd r rfl hr0
  refine ⟨a + 1, h', c * ν, ?_, hh', ?_⟩
  · rw [map_mul]
    exact hc.mul hν
  · calc aeval γ (c * ν) * aeval γ h = aeval γ c * (aeval γ h * aeval γ ν) := by
          rw [map_mul]; ring
      _ = algebraMap T V ϖ * (aeval γ c * aeval γ r) := by rw [hr]; ring
      _ = _ := by rw [he]; ring

end GlobalTheory
end

section

namespace GlobalTheory.RootNormLowerBound

theorem pow_card_le_norm_prod {ε : ℝ} (hε : 0 < ε) (s : Multiset ℂ)
    (h : ∀ t ∈ s, ε ≤ ‖t‖) : ε ^ Multiset.card s ≤ ‖(s.map (fun a => -a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun t ht => h t (Multiset.mem_cons_of_mem ht)
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_neg, pow_succ,
      mul_comm (ε ^ Multiset.card s)]
    exact mul_le_mul ha ih' (by positivity) (norm_nonneg _)

theorem exists_root_norm_lt {F : Polynomial ℂ} (hF : Polynomial.Monic F) {ε : ℝ}
    (hε : (0 : ℝ) < ε) (h0 : ‖F.coeff (0 : ℕ)‖ < ε ^ Polynomial.natDegree F) :
    ∃ (t : ℂ), Polynomial.IsRoot F t ∧ ‖t‖ < ε := by
  by_contra hcon
  have hall : ∀ t ∈ F.roots, ε ≤ ‖t‖ := fun t ht =>
    le_of_not_gt fun hlt => hcon ⟨t, (Polynomial.mem_roots hF.ne_zero).1 ht, hlt⟩
  have h1 := pow_card_le_norm_prod hε F.roots hall
  have hc : F.coeff 0 = (F.roots.map fun a => -a).prod := by
    rw [(IsAlgClosed.splits F).coeff_zero_eq_prod_roots_of_monic hF, Multiset.prod_map_neg,
      IsAlgClosed.card_roots_eq_natDegree]
  rw [IsAlgClosed.card_roots_eq_natDegree, ← hc] at h1
  linarith

end GlobalTheory.RootNormLowerBound
end
