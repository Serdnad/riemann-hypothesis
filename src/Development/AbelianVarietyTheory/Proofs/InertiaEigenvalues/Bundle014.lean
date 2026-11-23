module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open scoped BigOperators
open Polynomial

namespace GlobalTheory.SplittingAlgebra

theorem exists_monomials_span (t : ℕ) : ∃ e : Fin t.factorial → Fin t → ℕ,
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (y : Fin t → A),
      (∏ c, (X - C (y c))) ∈ Polynomial.lifts (algebraMap R A) →
      ∀ a ∈ Algebra.adjoin R (Set.range y),
        ∃ cf : Fin t.factorial → R, a = ∑ k, cf k • ∏ c, y c ^ e k c := by
  induction t with
  | zero =>
    refine ⟨fun _ _ => 0, fun R A _ _ _ y _ a ha => ?_⟩
    rw [Set.range_eq_empty, Algebra.adjoin_empty, Algebra.mem_bot] at ha
    obtain ⟨r, rfl⟩ := ha
    refine ⟨fun _ => r, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [Algebra.algebraMap_eq_smul_one]
  | succ t ih =>
    obtain ⟨e, he⟩ := ih
    let E : Fin (t + 1).factorial ≃ Fin (t + 1) × Fin t.factorial :=
      (finCongr (Nat.factorial_succ t)).trans finProdFinEquiv.symm
    refine ⟨fun k => Fin.cons ((E k).1 : ℕ) (e (E k).2), fun R A _ _ _ y hP a ha => ?_⟩
    have hPm : (∏ c, (X - C (y c))).Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hP hPm
    have hdeg : q.natDegree ≤ t + 1 := by
      rw [hqd]
      refine (natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => 1) fun c _ => natDegree_X_sub_C_le _).trans ?_
      simp
    have hq0 : aeval (y 0) q = 0 := by
      rw [← eval_map_algebraMap, hq, Fin.prod_univ_succ]
      simp
    set R1 := Algebra.adjoin R {y 0} with hR1
    have hR1s : ∀ s ∈ R1, ∃ d : Fin (t + 1) → R, s = ∑ i, d i • y 0 ^ (i : ℕ) := by
      intro s hs
      classical
      have h1 : s ∈ Subalgebra.toSubmodule R1 := hs
      rw [hR1, ← Submodule.span_range_natDegree_eq_adjoin hqm hq0] at h1
      have h2 : s ∈ Submodule.span R (Set.range fun i : Fin (t + 1) => y 0 ^ (i : ℕ)) := by
        refine Submodule.span_mono ?_ h1
        intro z hz
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        exact ⟨⟨i, by omega⟩, rfl⟩
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      exact ⟨d, hd.symm⟩
    have hQ : (∏ c : Fin t, (X - C (y c.succ))) ∈ Polynomial.lifts (algebraMap R1 A) := by
      let y0 : R1 := ⟨y 0, Algebra.self_mem_adjoin_singleton R _⟩
      refine ⟨(q.map (algebraMap R R1)) /ₘ (X - C y0), ?_⟩
      rw [coe_mapRingHom, map_divByMonic _ (monic_X_sub_C _), Polynomial.map_map,
        ← IsScalarTower.algebraMap_eq, hq, Fin.prod_univ_succ]
      have : Polynomial.map (algebraMap R1 A) (X - C y0) = X - C (y 0) := by
        simp [y0]
      rw [this, mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
    have ha' : a ∈ Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ) := by
      have : Algebra.adjoin R (Set.range y) ≤
          (Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ)).restrictScalars R := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨c, rfl⟩
        refine Fin.cases ?_ (fun c => ?_) c
        · exact Subalgebra.algebraMap_mem (Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ))
            (⟨y 0, Algebra.self_mem_adjoin_singleton R _⟩ : R1)
        · exact Algebra.subset_adjoin (R := R1) (s := Set.range fun c : Fin t => y c.succ) ⟨c, rfl⟩
      exact this ha
    obtain ⟨cf, hcf⟩ := he R1 A (fun c => y c.succ) hQ a ha'
    choose d hd using fun k => hR1s (cf k) (cf k).2
    refine ⟨fun k => d (E k).2 (E k).1, ?_⟩
    rw [hcf, ← E.symm.sum_comp, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, hd k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Fin.prod_univ_succ]

theorem adjoin_perm_eq_top {K : Type} [Field K] {t : ℕ} (α : Fin t → K)
    (hα : Function.Injective α) (f : Equiv.Perm (Fin t) → K) :
    f ∈ Algebra.adjoin K (Set.range fun (c : Fin t) (σ : Equiv.Perm (Fin t)) => α (σ c)) := by
  classical
  set S := Algebra.adjoin K (Set.range fun (c : Fin t) (σ : Equiv.Perm (Fin t)) => α (σ c))
  have h1 : ∀ σ : Equiv.Perm (Fin t), (Pi.single σ (1 : K) : Equiv.Perm (Fin t) → K) ∈ S := by
    intro σ
    have : (Pi.single σ (1 : K) : Equiv.Perm (Fin t) → K) =
        ∏ c, aeval (fun τ : Equiv.Perm (Fin t) => α (τ c)) (Lagrange.basis Finset.univ α (σ c)) := by
      funext τ
      rw [Finset.prod_apply]
      simp only [aeval_pi_apply₂, coe_aeval_eq_eval]
      by_cases h : τ = σ
      · subst h
        rw [Pi.single_eq_same]
        exact (Finset.prod_eq_one fun c _ =>
          Lagrange.eval_basis_self hα.injOn (Finset.mem_univ _)).symm
      · rw [Pi.single_eq_of_ne h]
        obtain ⟨c, hc⟩ : ∃ c, σ c ≠ τ c := by
          by_contra hh
          push_neg at hh
          exact h (Equiv.ext fun c => (hh c).symm)
        exact (Finset.prod_eq_zero (Finset.mem_univ c)
          (Lagrange.eval_basis_of_ne hc (Finset.mem_univ _))).symm
    rw [this]
    refine Subalgebra.prod_mem _ fun c _ => ?_
    refine Algebra.adjoin_mono ?_ (aeval_mem_adjoin_singleton K _)
    rintro _ rfl
    exact ⟨c, rfl⟩
  rw [pi_eq_sum_univ' f]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _ (h1 σ) _

theorem coeff_prod_apply {O I : Type} [CommRing O] {t : ℕ} (y : Fin t → I → O) (i : I) (j : ℕ) :
    (∏ c, (X - C (y c))).coeff j i = (∏ c, (X - C (y c i))).coeff j := by
  have := coeff_map (p := ∏ c, (X - C (y c))) (Pi.evalRingHom (fun _ : I => O) i) j
  rw [Polynomial.map_prod] at this
  simpa using this.symm

theorem main : ∀ {O X : Type} [CommRing O] [IsDomain O] [Finite X]
    (T : Subalgebra O (X → O)) (t : ℕ) (α : X → Fin t → O),
    (∀ x, Function.Injective (α x)) →
    (∀ x y, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    (∀ j, (fun x => (∏ c, (Polynomial.X - Polynomial.C (α x c))).coeff j) ∈ T) →
    (let T' : Subalgebra O (X × Equiv.Perm (Fin t) → O) :=
        Algebra.adjoin O ((fun f : X → O => fun x' => f x'.1) '' (T : Set (X → O)) ∪
          Set.range (fun c : Fin t => fun x' => α x'.1 (x'.2 c)))
      ∃ b : Fin t.factorial → X × Equiv.Perm (Fin t) → O,
        (∀ k, b k ∈ T') ∧ ∀ f ∈ T', ∃! cf : Fin t.factorial → T,
          f = ∑ k, (fun x' => (cf k : X → O) x'.1) * b k) := by
  intro O Y _ _ _ T t α hα _ hT T'
  obtain ⟨e, he⟩ := exists_monomials_span t
  let y : Fin t → Y × Equiv.Perm (Fin t) → O := fun c x' => α x'.1 (x'.2 c)
  refine ⟨fun k => ∏ c, y c ^ e k c, fun k => ?_, fun f hf => ?_⟩
  · have hy : ∀ c, y c ∈ T' := fun c =>
      Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_range_self c))
    exact Subalgebra.prod_mem _ fun c _ => Subalgebra.pow_mem _ (hy c) _
  have hind : ∀ (x : Y) (d : Fin t.factorial → O),
      (∀ σ : Equiv.Perm (Fin t), ∑ k, d k * ∏ c, α x (σ c) ^ e k c = 0) → ∀ k, d k = 0 := by
    intro x d hd k
    let K := FractionRing O
    have hi : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
    let β : Fin t → K := fun c => algebraMap O K (α x c)
    let z : Fin t → Equiv.Perm (Fin t) → K := fun c σ => β (σ c)
    have hl : (∏ c, (X - C (z c))) ∈ Polynomial.lifts (algebraMap K (Equiv.Perm (Fin t) → K)) := by
      rw [lifts_iff_coeff_lifts]
      intro j
      refine ⟨(∏ c, (X - C (β c))).coeff j, funext fun σ => ?_⟩
      rw [coeff_prod_apply, Equiv.prod_comp σ (fun c => X - C (β c))]
      rfl
    have hli : LinearIndependent K (fun k => ∏ c, z c ^ e k c) := by
      refine linearIndependent_of_top_le_span_of_card_eq_finrank (fun g _ => ?_) ?_
      · obtain ⟨cf, hcf⟩ := he K _ z hl g (adjoin_perm_eq_top β (hi.comp (hα x)) g)
        exact (Submodule.mem_span_range_iff_exists_fun K).2 ⟨cf, hcf.symm⟩
      · simp [Fintype.card_perm]
    have := Fintype.linearIndependent_iff.1 hli (fun k => algebraMap O K (d k)) (by
      funext σ
      have := congrArg (algebraMap O K) (hd σ)
      simpa [z, β, Finset.sum_apply, Finset.prod_apply, Algebra.smul_def] using this) k
    exact hi (by simpa using this)
  let φ : T →+* (Y × Equiv.Perm (Fin t) → O) :=
    Pi.ringHom fun x' => (Pi.evalRingHom (fun _ : Y => O) x'.1).comp T.val.toRingHom
  letI : Algebra T (Y × Equiv.Perm (Fin t) → O) := φ.toAlgebra
  have hl : (∏ c, (X - C (y c))) ∈
      Polynomial.lifts (algebraMap T (Y × Equiv.Perm (Fin t) → O)) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    refine ⟨⟨_, hT j⟩, funext fun x' => ?_⟩
    rw [coeff_prod_apply, Equiv.prod_comp x'.2 (fun c => X - C (α x'.1 c))]
    rfl
  have hf' : f ∈ Algebra.adjoin T (Set.range y) := by
    induction hf using Algebra.adjoin_induction with
    | mem g hg =>
      rcases hg with ⟨g, hg, rfl⟩ | hg
      · exact Subalgebra.algebraMap_mem _ (⟨g, hg⟩ : T)
      · exact Algebra.subset_adjoin hg
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (algebraMap O T r)
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  obtain ⟨cf, hcf⟩ := he T _ y hl f hf'
  refine ⟨cf, hcf, fun cg hcg => ?_⟩
  funext k
  ext x
  refine sub_eq_zero.1 (hind x (fun k => (cg k : Y → O) x - (cf k : Y → O) x) (fun σ => ?_) k)
  have h1 : f = ∑ k, (fun x' => (cf k : Y → O) x'.1) * ∏ c, y c ^ e k c := hcf
  have h2 := congrFun (hcg.symm.trans h1) (x, σ)
  simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply, y] at h2
  simp only [sub_mul, Finset.sum_sub_distrib, h2, sub_self]

end GlobalTheory.SplittingAlgebra
end

section

namespace GlobalTheory

def powDenomSubring {S EE : Type} [CommRing S] [CommRing EE] (a : S →+* EE) (Q : S) :
    Subring EE where
  carrier := {e | ∃ (n : ℕ) (t : S), a Q ^ n * e = a t}
  mul_mem' := by
    rintro e f ⟨n, t, ht⟩ ⟨m, r, hr⟩
    refine ⟨n + m, t * r, ?_⟩
    rw [map_mul, ← ht, ← hr]; ring
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro e f ⟨n, t, ht⟩ ⟨m, r, hr⟩
    refine ⟨n + m, Q ^ m * t + Q ^ n * r, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← ht, ← hr]; ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro e ⟨n, t, ht⟩
    refine ⟨n, -t, ?_⟩
    rw [map_neg, ← ht]; ring

theorem eq_zero_of_sum_smul_eq_zero_of_powDenom {S EE W RW Y : Type} [CommRing S] [CommRing EE]
    [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW)
    (c : W →+* RW) (ψ : S →+* W) (Q : S) (hι : Function.Injective ι)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y)
    (hx : ∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) (E : Fin q → EE)
    (hE : ∀ m, E m ∈ powDenomSubring a Q) (h0 : ∑ m, ι (E m) • x m = 0) (m : Fin q) :
    E m = 0 := by
  choose n t ht using hE
  set N := ∑ m, n m with hN
  have hle : ∀ m, n m ≤ N := fun m =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  have h1 : ∀ m, a Q ^ N * E m = a (Q ^ (N - n m) * t m) := by
    intro m
    rw [map_mul, map_pow, ← ht, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle m)]
  have h2 := hx (fun m => ψ (Q ^ (N - n m) * t m)) (by
    have : ∀ m, c (ψ (Q ^ (N - n m) * t m)) • x m = ι (a Q ^ N) • (ι (E m) • x m) := by
      intro m
      rw [← hc, ← h1, map_mul, mul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h0, smul_zero])
  have h3 : ψ (Q ^ (N - n m) * t m) = 0 := congrFun h2 m
  have h4 : a Q ^ N * E m = 0 := by
    apply hι
    rw [h1, hc, h3, map_zero, map_zero]
  exact ((hQ.pow N).mul_right_eq_zero).1 h4

theorem exists_coeff_powDenom {S EE W RW Y : Type} [CommRing S] [CommRing EE]
    [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW)
    (c : W →+* RW) (ψ : S →+* W) (Q : S)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y) (y : Y)
    (hy : ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • y = ∑ i, c (ψ (s i)) • x i) :
    ∃ E : Fin q → EE, (∀ i, E i ∈ powDenomSubring a Q) ∧ y = ∑ i, ι (E i) • x i := by
  obtain ⟨k, s, hs⟩ := hy
  obtain ⟨v, hv⟩ := (hQ.pow k).exists_left_inv
  refine ⟨fun i => v * a (s i), fun i => ⟨k, s i, ?_⟩, ?_⟩
  · rw [← mul_assoc, mul_comm _ v, hv, one_mul]
  · have : ∀ i, ι (v * a (s i)) • x i = ι v • (c (ψ (s i)) • x i) := by
      intro i
      rw [map_mul, mul_smul, hc]
    simp only [this]
    rw [← Finset.smul_sum, ← hs, ← hc, ← map_pow, ← mul_smul, ← map_mul, hv, map_one, one_smul]

theorem exists_isUnit_matrix_of_pow_smul_span : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by
  intro S EE W RW Y _ _ _ _ _ _ a ι c ψ Q hι hc hQ q x z hx hz hx'
  choose A hAm hA using fun j => exists_coeff_powDenom a ι c ψ Q hc hQ x (z j) (hz j)
  choose B hBm hB using fun i => exists_coeff_powDenom a ι c ψ Q hc hQ z (x i) (hx' i)
  refine ⟨Matrix.of fun i j => A j i, ?_, fun j => by simpa using hA j⟩
  have hAB : (Matrix.of fun i j => A j i) * (Matrix.of fun j i => B i j)
      = (1 : Matrix (Fin q) (Fin q) EE) := by
    ext m i
    rw [← sub_eq_zero]
    refine eq_zero_of_sum_smul_eq_zero_of_powDenom a ι c ψ Q hι hc hQ x hx
      (fun m => ((Matrix.of fun i j => A j i) * (Matrix.of fun j i => B i j)) m i
        - (1 : Matrix (Fin q) (Fin q) EE) m i) ?_ ?_ m
    · intro m
      refine sub_mem ?_ ?_
      · rw [Matrix.mul_apply]
        exact sum_mem fun j _ => mul_mem (hAm j m) (hBm i j)
      · rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have h1 : ∑ m, ι ((1 : Matrix (Fin q) (Fin q) EE) m i) • x m = x i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro m _ hm
          simp [Matrix.one_apply_ne hm]
        · simp
      rw [h1]
      conv_rhs => rw [hB i]

      simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hA j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, mul_comm, mul_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hAB)

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem one_sub_unit_mul_exp_ne_zero (L : ℝ) (hL : 0 < L) (χ : ℂ) (hχ : ‖χ‖ = 1) (t : ℝ)
    (ht : t ≠ 0) : 1 - χ * Complex.exp (-((L : ℂ) * (t : ℂ))) ≠ 0 := by
  intro h
  have h1 : χ * Complex.exp (-((L : ℂ) * (t : ℂ))) = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, hχ, one_mul, Complex.norm_exp, norm_one] at h2
  have h3 : (-((L : ℂ) * (t : ℂ))).re = 0 := by
    have := Real.exp_eq_one_iff _ |>.mp h2
    exact this
  simp at h3
  rcases h3 with h3 | h3
  · exact hL.ne' h3
  · exact ht h3

theorem exists_analytic_sub_one_div_one_sub_unit_mul_exp :
    ∀ (L : ℝ), 0 < L → ∀ χ : ℂ, ‖χ‖ = 1 → ∃ h : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧ (χ ≠ 1 → h 1 = 0) := by
  intro L hL χ hχ
  by_cases h1 : χ = 1
  · subst h1
    set f : ℂ → ℂ := fun w => 1 - Complex.exp (-((L : ℂ) * w)) with hf
    have hfd : Differentiable ℂ f := by
      rw [hf]; fun_prop
    have hkd : Differentiable ℂ (dslope f 0) := by
      rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
      exact hfd.differentiableOn
    have hk : ∀ w : ℂ, w ≠ 0 → dslope f 0 w = f w / w := by
      intro w hw
      rw [dslope_of_ne _ hw, slope_def_field]
      simp [hf]
    have hk0 : dslope f 0 0 = L := by
      rw [dslope_same]
      have : HasDerivAt f (0 - Complex.exp (-((L : ℂ) * 0)) * (-((L : ℂ) * 1))) 0 :=
        (hasDerivAt_const _ _).sub (((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).neg.cexp)
      rw [this.deriv]; simp
    refine ⟨fun s => (dslope f 0 (s - 1))⁻¹, ?_, ?_, fun h => absurd rfl h⟩
    · intro x _
      have hd : Differentiable ℂ (fun s : ℂ => dslope f 0 (s - 1)) :=
        hkd.comp (differentiable_id.sub_const 1)
      refine (hd.analyticAt _).inv ?_
      by_cases hx : x = 1
      · subst hx
        show dslope f 0 (((1 : ℝ) : ℂ) - 1) ≠ 0
        rw [Complex.ofReal_one, sub_self, hk0]
        exact_mod_cast hL.ne'
      · have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
        have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
        show dslope f 0 ((x : ℂ) - 1) ≠ 0
        rw [hk _ hx'']
        refine div_ne_zero ?_ hx''
        have := one_sub_unit_mul_exp_ne_zero L hL 1 hχ (x - 1) hx'
        simpa [hf] using this
    · intro x hx
      have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx.ne'
      have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
      show (dslope f 0 ((x : ℂ) - 1))⁻¹ = _
      rw [hk _ hx'', inv_div, one_mul]
  · refine ⟨fun s => (s - 1) / (1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))), ?_, fun _ _ => rfl,
      fun _ => by simp⟩
    intro x _
    have hd : Differentiable ℂ (fun s : ℂ => 1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))) := by
      fun_prop
    have hn : Differentiable ℂ (fun s : ℂ => s - 1) := by fun_prop
    refine (hn.analyticAt _).div (hd.analyticAt _) ?_
    by_cases hx : x = 1
    · subst hx
      simpa [sub_eq_zero] using fun h => h1 (Eq.symm h)
    · have := one_sub_unit_mul_exp_ne_zero L hL χ hχ (x - 1) (sub_ne_zero.mpr hx)
      simpa using this

end GlobalTheory
end

section

namespace GlobalTheory

theorem matrix_inv_near_one : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n]
    [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 →
    (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  intro E _ _ n _ _ X Z t ht0 ht1 hZX hX i j
  have key : Z - 1 = -((X - 1) + (Z - 1) * (X - 1)) := by
    have h : (Z - 1) * (X - 1) = Z * X - Z - X + 1 := by noncomm_ring
    rw [h, hZX]; abel
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨i0, j0⟩, hmax⟩ := Finite.exists_max (fun p : n × n => ‖(Z - 1) p.1 p.2‖)
  set s := ‖(Z - 1) i0 j0‖ with hs
  have hbound : ∀ a b, ‖(Z - 1) a b‖ ≤ max t (s * t) := by
    intro a b
    have hprod : ‖((Z - 1) * (X - 1)) a b‖ ≤ s * t := by
      rw [Matrix.mul_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg (norm_nonneg _) ht0) fun k _ => ?_
      rw [norm_mul]
      exact mul_le_mul (hmax (a, k)) (hX k b) (norm_nonneg _) (norm_nonneg _)
    rw [key, Matrix.neg_apply, norm_neg, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hX a b) hprod)
  have hs0 : 0 ≤ s := norm_nonneg _
  have hst : s ≤ t := by
    by_contra hlt
    push_neg at hlt
    have h1 := hbound i0 j0
    rw [← hs] at h1
    rcases le_max_iff.mp h1 with h | h
    · linarith
    · nlinarith
  exact (hmax (i, j)).trans hst

end GlobalTheory
end
