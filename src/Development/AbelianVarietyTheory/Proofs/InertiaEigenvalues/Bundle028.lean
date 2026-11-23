module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.Monoid

@[expose] public section

section

namespace GlobalTheory.PerfectCompletion

section General

variable {V : Type} [CommRing V] (x : V)

theorem eval_eq_zero_iff (n : ℕ) (y : AdicCompletion (Ideal.span {x}) V) :
    AdicCompletion.eval (Ideal.span {x}) V n y = 0 ↔
      (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ n ∣ y := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton x),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem complete :
    IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x})
      (AdicCompletion (Ideal.span {x}) V) := by
  have h := AdicCompletion.isAdicComplete (M := V) (Submodule.fg_span_singleton x)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {x}) V),
    Ideal.map_span, Set.image_singleton] at h
  exact h

theorem dense (y : AdicCompletion (Ideal.span {x}) V) (r : ℕ) :
    ∃ (s : V) (z : AdicCompletion (Ideal.span {x}) V),
      y = algebraMap V _ s + (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {x}) V r y)
  have : AdicCompletion.eval (Ideal.span {x}) V r (y - algebraMap V _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff x r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩

theorem dvd_iff (s : V) (r : ℕ) :
    (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r ∣ algebraMap V _ s ↔ x ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {x}) V r (algebraMap V _ s) =
      Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem sModEq_iff {C : Type} [CommRing C] (c : C) (n : ℕ) (u v : C) :
    u ≡ v [SMOD (Ideal.span {c} ^ n • ⊤ : Submodule C C)] ↔ c ^ n ∣ u - v := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

end General

section Perfect

variable (l : ℕ) [Fact l.Prime] {V : Type} [CommRing V] [CharP V l] [PerfectRing V l]

theorem pow_root (c : V) : ((frobeniusEquiv V l).symm c) ^ l = c := by
  have := (frobeniusEquiv V l).apply_symm_apply c
  rwa [frobeniusEquiv_apply, frobenius_def] at this

theorem dvd_of_pow_dvd_pow (x s : V) (n : ℕ) (h : x ^ (l * n) ∣ s ^ l) : x ^ n ∣ s := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(frobeniusEquiv V l).symm c, (frobeniusEquiv V l).injective ?_⟩
  rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, hc, mul_pow,
    pow_root, ← pow_mul, mul_comm n l]

end Perfect

theorem perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l]
    [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧
      Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  intro l hl V _ _ _ x
  set C := AdicCompletion (Ideal.span {x}) V
  set X := algebraMap V C x with hX
  have h0 : ((l : ℕ) : C) = 0 := by
    rw [← map_natCast (algebraMap V C), CharP.cast_eq_zero, map_zero]
  refine ⟨h0, ?_⟩
  rcases subsingleton_or_nontrivial C with hC | hC
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  haveI : CharP C l := (CharP.charP_iff_prime_eq_zero hl.out).mpr h0
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hle : ∀ n : ℕ, n ≤ l * n := fun n => Nat.le_mul_of_pos_left n hl.out.pos
  refine ⟨fun y z hyz => ?_, fun y => ?_⟩
  ·
    have hw : (y - z) ^ l = 0 := by
      simp only at hyz
      rw [sub_pow_char, hyz, sub_self]
    rw [← sub_eq_zero]
    set w := y - z
    refine AdicCompletion.ext fun n => ?_
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, map_zero, eval_eq_zero_iff]
    obtain ⟨s, t, hst⟩ := dense x w (l * n)
    have h1 : X ^ (l * n) ∣ algebraMap V C (s ^ l) := by
      have e : algebraMap V C (s ^ l) = -((X ^ (l * n)) ^ l * t ^ l) := by
        rw [map_pow, eq_neg_iff_add_eq_zero, ← mul_pow, ← add_pow_char, ← hst, hw]
      rw [e, dvd_neg]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _
    rw [dvd_iff] at h1
    have h2 := dvd_of_pow_dvd_pow l x s n h1
    rw [hst]
    refine dvd_add ?_ (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)
    rw [dvd_iff]
    exact h2
  ·
    choose s t hst using fun n => dense x y (l * n)
    set b : ℕ → V := fun n => (frobeniusEquiv V l).symm (s n) with hb
    have hbs : ∀ n, b n ^ l = s n := fun n => pow_root l (s n)
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        algebraMap V C (b m) ≡ algebraMap V C (b n) [SMOD (Ideal.span {X} ^ m • ⊤ : Submodule C C)] := by
      intro m n hmn
      rw [sModEq_iff, ← map_sub, dvd_iff]
      refine dvd_of_pow_dvd_pow l x _ m ?_
      rw [sub_pow_char, hbs, hbs, ← dvd_iff, map_sub]
      have e : algebraMap V C (s m) - algebraMap V C (s n) = X ^ (l * n) * t n - X ^ (l * m) * t m := by
        have := hst m; have := hst n; linear_combination hst n - hst m
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow X (Nat.mul_le_mul_left l hmn)) _)
        (dvd_mul_right _ _)
    obtain ⟨L, hL⟩ := (complete x).toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    simp only
    rw [← sub_eq_zero]
    refine (complete x).toIsHausdorff.haus _ fun n => ?_
    rw [sModEq_iff, sub_zero]
    obtain ⟨u, hu⟩ := (sModEq_iff _ _ _ _).1 (hL n)
    have e : L ^ l - y = -((X ^ n) ^ l * u ^ l) - X ^ (l * n) * t n := by
      have hL' : L = algebraMap V C (b n) - X ^ n * u := by rw [← hu]; ring
      rw [hL', sub_pow_char, ← map_pow, hbs, mul_pow]
      linear_combination -(hst n)
    rw [e]
    exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _))
      (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)

end GlobalTheory.PerfectCompletion
end

section

open Polynomial

namespace GlobalTheory.TraceDetSplit

theorem det_aeval_prod {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (s : Multiset K) :
    (aeval N (s.map fun r => X - C r).prod).det
      = (-1) ^ (n * s.card) * (s.map N.charpoly.eval).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have h1 : (aeval N (X - C r)).det = (-1) ^ n * N.charpoly.eval r := by
      have e : Matrix.scalar (Fin n) r - N = -(N - algebraMap K (Matrix (Fin n) (Fin n) K) r) := by
        rw [neg_sub, Matrix.algebraMap_eq_diagonal]
        rfl
      rw [Matrix.eval_charpoly, e, Matrix.det_neg, Fintype.card_fin, map_sub, aeval_X, aeval_C,
        ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, map_mul, Matrix.det_mul, ih, h1]
    ring

theorem det_aeval {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E) (p : E[X])
    (hp : p.Monic) :
    (aeval N p).det = (-1) ^ (n * p.natDegree) * resultant p N.charpoly := by
  classical
  let φ := algebraMap E (AlgebraicClosure E)
  apply φ.injective
  have hp' : (p.map φ).Monic := hp.map φ
  have hs : (p.map φ).Splits := IsAlgClosed.splits _
  have hd : (p.map φ).natDegree = p.natDegree := natDegree_map φ
  have key : φ.mapMatrix (aeval N p) = aeval (N.map φ) (p.map φ) := by
    rw [aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId E (AlgebraicClosure E))) N p).symm
  rw [RingHom.map_det, key, map_mul, map_pow, map_neg, map_one, ← resultant_map_map,
    ← Matrix.charpoly_map]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hp']
  rw [det_aeval_prod, ← hs.natDegree_eq_card_roots, hd, ← hd,
    resultant_eq_prod_eval _ _ _ (by rw [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim]) hs,
    hp'.leadingCoeff, one_pow, one_mul]

theorem det_trace_monic {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (g : A)
    (e : Fin n → A) (q : Fin n → E[X]) (hd : ∀ k, (q k).natDegree = k) (hm : ∀ k, (q k).Monic) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l)).det
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)).det := by
  classical
  have hM : (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)) =
      (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)) *
        Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply]

    rw [aeval_eq_sum_range' (n := n) (by rw [hd k]; exact k.isLt), Finset.sum_mul, map_sum,
    ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul]
  have hC : (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun k _ => ?_
      simp only [Matrix.of_apply]
      have := (hm k).coeff_natDegree
      rwa [hd k] at this
    · intro i j hij
      simp only [Matrix.of_apply]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hd i]
      exact hij
  rw [hM, Matrix.det_mul, hC, one_mul]

theorem charpoly_leftMul_basis {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] {n : ℕ} (g : A) (w : Module.Basis (Fin n) E A) :
    (Algebra.leftMulMatrix w g).charpoly = (LinearMap.mulLeft E g).charpoly := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rfl

theorem trace_mul_eq {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (x : Fin n → A)
    (h : A) (w : Module.Basis (Fin n) E A) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * h * w l))
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * w l)) * Algebra.leftMulMatrix w h := by
  ext k l
  simp only [Matrix.of_apply, Matrix.mul_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [mul_assoc, ← w.sum_repr (h * w l)]

  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.TraceDetSplit


open GlobalTheory.TraceDetSplit in
theorem GlobalTheory.det_trace_pow_prod : ∀ (E A₁ A₂ : Type) [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (a b : ℕ) (u : Module.Basis (Fin a) E A₁) (w : Module.Basis (Fin b) E A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → ∃ ε : E, ε * ε = 1 ∧ (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂) ((g₁, g₂) ^ (k : ℕ) * Fin.addCases (fun i => (u i, 0)) (fun j => (0, w j)) l)).det = ε * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly * (Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)).det * (Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)).det := by
  intro E A₁ A₂ _ _ _ _ _ _ _ g₁ g₂ a b u w _
  classical
  have hdeg₁ : (LinearMap.mulLeft E g₁).charpoly.natDegree = a := by
    rw [LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis u, Fintype.card_fin]
  have hCH : aeval g₁ (LinearMap.mulLeft E g₁).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g₁)
    have h2 : aeval (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₁).charpoly =
        Algebra.lmul E A₁ (aeval g₁ (LinearMap.mulLeft E g₁).charpoly) :=
      Polynomial.aeval_algHom_apply (Algebra.lmul E A₁) g₁ _
    rw [h2] at h
    simpa using LinearMap.congr_fun h 1
  let q : Fin (a + b) → E[X] := fun k =>
    if (k : ℕ) < a then X ^ (k : ℕ) else X ^ ((k : ℕ) - a) * (LinearMap.mulLeft E g₁).charpoly
  have hd : ∀ k, (q k).natDegree = k := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp [q, hk]
    · simp only [q, hk, if_false]
      rw [(monic_X_pow _).natDegree_mul (LinearMap.charpoly_monic _), natDegree_X_pow, hdeg₁]
      omega
  have hm : ∀ k, (q k).Monic := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp only [q, hk, if_true]
      exact monic_X_pow _
    · simp only [q, hk, if_false]
      exact (monic_X_pow _).mul (LinearMap.charpoly_monic _)
  refine ⟨(-1) ^ (a * b), by rw [← mul_pow, neg_one_mul, neg_neg, one_pow], ?_⟩
  rw [det_trace_monic (g₁, g₂) _ q hd hm]
  let M := Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
    (aeval (g₁, g₂) (q k) * Fin.addCases (fun i => ((u i, 0) : A₁ × A₂)) (fun j => (0, w j)) l)
  let T₁ := Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)
  let T₂ := Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)
  let S := Matrix.of fun k l : Fin b =>
    Algebra.trace E A₂ (g₂ ^ (k : ℕ) * aeval g₂ (LinearMap.mulLeft E g₁).charpoly * w l)
  have hblock : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks T₁ (Matrix.of fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 S := by
    ext (i | i) (l | l)
    · simp [M, T₁, q, Algebra.trace_prod_apply, aeval_prod_apply]
    · simp [M]
    · simp [M, q, Algebra.trace_prod_apply, aeval_prod_apply, hCH]
    · simp [M, S, q, Algebra.trace_prod_apply, aeval_prod_apply, mul_assoc]
  have hS : S = T₂ * Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly) :=
    trace_mul_eq (fun k : Fin b => g₂ ^ (k : ℕ)) _ w
  have hres : (Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly)).det =
      (-1) ^ (b * a) * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly := by
    rw [← Polynomial.aeval_algHom_apply, det_aeval _ _ (LinearMap.charpoly_monic _),
      charpoly_leftMul_basis, hdeg₁]
  calc M.det = (M.submatrix finSumFinEquiv finSumFinEquiv).det :=
        (Matrix.det_submatrix_equiv_self _ _).symm
    _ = T₁.det * S.det := by rw [hblock, Matrix.det_fromBlocks_zero₂₁]
    _ = _ := by
      rw [hS, Matrix.det_mul, hres]
      ring
end

section

namespace GlobalTheory

open scoped BigOperators

theorem transfer_continuous_of_continuousOn : ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X] (ρ : Representation R G X) (H : Subgroup G) [Fintype (G ⧸ H)], IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → let tr : (G → X) → G → X := fun f g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)); ∀ f : G → X, ContinuousOn f H → Continuous (tr f) := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ hH hρ tr f hf
  show Continuous (fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)))
  refine continuous_finsetSum _ (fun q _ => ?_)
  refine continuous_iff_continuousAt.2 (fun g₀ => ?_)
  have hsmul : ∀ g : G, g • q = ((g * q.out : G) : G ⧸ H) := by
    intro g
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  let ψ : G → G := fun g => (g * q.out)⁻¹ * (g₀ • q).out
  have hψc : Continuous ψ := by fun_prop
  let V : Set G := ψ ⁻¹' (H : Set G)
  have hVo : IsOpen V := hH.preimage hψc
  have key : ∀ g ∈ V, g • q = g₀ • q := by
    intro g hg
    have h1 : ((g * q.out : G) : G ⧸ H) = ((g₀ • q).out : G ⧸ H) := QuotientGroup.eq.2 hg
    rw [hsmul g, h1, QuotientGroup.out_eq']
  have hg₀ : g₀ ∈ V := by
    show (g₀ * q.out)⁻¹ * (g₀ • q).out ∈ H
    apply QuotientGroup.eq.1
    rw [QuotientGroup.out_eq', hsmul]
  have hmem : ∀ g ∈ V, (g₀ • q).out⁻¹ * g * q.out ∈ H := by
    intro g hg
    have h1 := QuotientGroup.eq.1 (show (((g₀ • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H) by
      rw [QuotientGroup.out_eq', ← hsmul g, key g hg])
    simpa [mul_assoc] using h1
  have hV : V ∈ nhds g₀ := hVo.mem_nhds hg₀
  have hc : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀ := by
    have hφ : Continuous (fun g : G => (g₀ • q).out⁻¹ * g * q.out) := by fun_prop
    have hw : ContinuousWithinAt (fun g => f ((g₀ • q).out⁻¹ * g * q.out)) V g₀ :=
      ContinuousWithinAt.comp (g := f) (f := fun g : G => (g₀ • q).out⁻¹ * g * q.out) (t := (H : Set G))
        (hf _ (hmem g₀ hg₀)) hφ.continuousWithinAt (fun g hg => hmem g hg)
    exact (hρ _).continuousAt.comp (hw.continuousAt hV)
  refine hc.congr ?_
  filter_upwards [hV] with g hg
  rw [key g hg]

end GlobalTheory
end

section

namespace GlobalTheory

theorem index_transfer_along_projection {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (L : AddSubgroup M) (T p : M →+ M) (Φ : M →+ N) (h : N →+ N)
    (hpL : ∀ y ∈ L, p y ∈ L) (hTp : ∀ y, T (p y) = p (T y))
    (hT1 : ∀ y, T (y - p y) = y - p y) (hΦ : ∀ y, Φ y = 0 → p y = 0)
    (hΦT : ∀ y, Φ (T y) = h (Φ y)) :
    (L.map T).relIndex L = ((L.map Φ).map h).relIndex (L.map Φ) := by
  have key : ∀ y ∈ L, (y ∈ L.map T ↔ Φ y ∈ (L.map Φ).map h) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Φ x, ⟨x, hx, rfl⟩, (hΦT x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      have h0 : Φ (T x - y) = 0 := by rw [map_sub, hΦT, hxy, sub_self]
      have hp : p (T x) = p y := by
        have := hΦ _ h0
        rwa [map_sub, sub_eq_zero] at this
      refine ⟨p x + (y - p y), L.add_mem (hpL x hx) (L.sub_mem hy (hpL y hy)), ?_⟩
      show T (p x + (y - p y)) = y
      rw [map_add (f := _), hT1, hTp, hp]
      abel
  let ψ : L →+ L.map Φ :=
    (Φ.comp L.subtype).codRestrict (L.map Φ) (fun x => ⟨x.1, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc : (L.map T).addSubgroupOf L =
      (((L.map Φ).map h).addSubgroupOf (L.map Φ)).comap ψ := by
    ext ⟨y, hy⟩
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact key y hy
  unfold AddSubgroup.relIndex
  rw [hc, AddSubgroup.index_comap_of_surjective _ hψ]

end GlobalTheory
end

section

namespace GlobalTheory

theorem index_smul_cocycle_eq_coboundary (R G X : Type) [CommRing R] [Group G] [AddCommGroup X]
    [Module R X] (ρ : Representation R G X) (H : Subgroup G) [H.FiniteIndex] (f : G → X)
    (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (hH : ∃ x, ∀ h ∈ H, f h = ρ h x - x) :
    ∃ x, ∀ g, H.index • f g = ρ g x - x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hH
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → X := fun g => f g - (ρ g x₀ - x₀) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + ρ g (f' h) := by
    intro g h
    simp only [hf', hf, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hz : ∀ h ∈ H, f' h = 0 := by
    intro h hh
    simp only [hf', hx₀ h hh, sub_self]
  have hq : ∀ (g : G) (q : G ⧸ H), f' (g • q).out = f' g + ρ g (f' q.out) := by
    intro g q
    have h1 : ((g * q.out : G) : G ⧸ H) = ((g • q).out : G ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    have h2 := QuotientGroup.eq.mp h1
    have h3 : (g • q).out = (g * q.out) * ((g * q.out)⁻¹ * (g • q).out) := by group
    rw [h3, hc, hz _ h2, map_zero, add_zero, hc]
  refine ⟨H.index • x₀ - ∑ q : G ⧸ H, f' q.out, fun g => ?_⟩
  have hs : ∑ q : G ⧸ H, f' (g • q).out = ∑ q : G ⧸ H, f' q.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f' q.out)
  simp only [hq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs

  rw [← map_sum, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hs
  have hfg : f g = f' g + (ρ g x₀ - x₀) := by simp [hf']
  have hs' : H.index • f' g = ∑ q : G ⧸ H, f' q.out - ρ g (∑ q : G ⧸ H, f' q.out) :=
    eq_sub_of_add_eq hs
  rw [hfg, smul_add, hs', map_sub, map_nsmul, smul_sub]
  abel

end GlobalTheory
end
