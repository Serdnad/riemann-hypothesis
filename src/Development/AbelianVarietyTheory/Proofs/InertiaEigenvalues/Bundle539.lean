module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle067
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

private theorem TopBasis.c_mem_of_mem_map_pow {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (tb : TopBasis s I ι) (m : ℕ) (j : ι) {y : A} (hy : y ∈ (I ^ m).map s) : tb.c j y ∈ I ^ m := by
  suffices h : ∀ r : A, tb.c j (r * y) ∈ I ^ m by simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r : A, tb.c j (r * y) ∈ I ^ m) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, ha, rfl⟩ r
    rw [mul_comm, tb.c_mul]
    exact Ideal.mul_mem_right _ _ ha
  · intro r; simp
  · intro x y _ _ hx hy r
    rw [mul_add, map_add (f := _)]
    exact Ideal.add_mem _ (hx r) (hy r)
  · intro a x _ hx r
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (r * a)

theorem TopBasis.basis_mod_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type)
    (tb : TopBasis s I ι) (m : ℕ), letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra;
    ∃ b : Module.Basis ι (S ⧸ I ^ m) (A ⧸ (I ^ m).map s), ∀ i, b i = Ideal.Quotient.mk _ (tb.b i) := by
  intro S A _ _ s I ι tb m
  letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra
  have hsmul : ∀ (a : S) (x : A), (Ideal.Quotient.mk (I ^ m) a) • (Ideal.Quotient.mk ((I ^ m).map s) x)
      = Ideal.Quotient.mk ((I ^ m).map s) (s a * x) := by
    intro a x
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk, map_mul]
  have hli : LinearIndependent (S ⧸ I ^ m) (fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)) := by
    rw [linearIndependent_iff']
    intro F g hg j hj
    choose h hh using fun i => Ideal.Quotient.mk_surjective (I := I ^ m) (g i)
    have hsum : (∑ i ∈ F, s (h i) * tb.b i) ∈ (I ^ m).map s := by

      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hh i, hsmul]
    have hc := tb.c_mem_of_mem_map_pow m j hsum

    rw [map_sum, Finset.sum_eq_single j] at hc
    · rw [tb.c_mul, tb.c_self, mul_one] at hc
      rw [← hh j]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    · intro i _ hij
      rw [tb.c_mul, tb.c_ne j i (Ne.symm hij), mul_zero]
    · intro h'; exact (h' hj).elim
  have hsp : ⊤ ≤ Submodule.span (S ⧸ I ^ m) (Set.range fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)) := by
    rintro x -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hF : ∀ i, i ∉ (tb.fin y m).toFinset → tb.c i y ∈ I ^ m := by
      intro i hi
      simpa using hi
    have hx := tb.approx y m (tb.fin y m).toFinset hF
    have : Ideal.Quotient.mk ((I ^ m).map s) y = ∑ i ∈ (tb.fin y m).toFinset,
        (Ideal.Quotient.mk (I ^ m) (tb.c i y)) • Ideal.Quotient.mk ((I ^ m).map s) (tb.b i) := by

      simp_rw [hsmul, ← map_sum]
      exact Ideal.Quotient.eq.mpr hx
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => by simp⟩

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMap_of_pow_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F := by
  intro l _ A A' _ _ f u u' ρ ρ' k hρ' hdvd hk
  obtain ⟨z, hz⟩ := hdvd
  have h : ‖toDisc l u' ρ' (f u)‖ ≤ ρ := by
    rw [hz, map_mul]
    calc ‖toDisc l u' ρ' (u' ^ k) * toDisc l u' ρ' z‖
        ≤ ‖toDisc l u' ρ' (u' ^ k)‖ * ‖toDisc l u' ρ' z‖ := norm_mul_le _ _
      _ ≤ (ρ' : ℝ) ^ k * 1 :=
          mul_le_mul (norm_toDisc_pow_le k hρ') (norm_toDisc_le z) (norm_nonneg _) (by positivity)
      _ = ((ρ' ^ k : ℝ≥0) : ℝ) := by simp
      _ ≤ ρ := NNReal.coe_le_coe.2 hk
  exact ⟨Disc.map f h, isDiscMap_map f h⟩

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.coeff_mem_of_mem_map {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (i : ι) (J : Ideal S) {y : A} (hy : y ∈ J.map s) : TB.c i y ∈ J := by
  have key : ∀ a, TB.c i (a * y) ∈ J := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      intro a
      rw [mul_comm, TB.c_mul]
      exact J.mul_mem_right _ hw
    | zero => intro a; rw [mul_zero, map_zero]; exact J.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact J.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

def TopBasis.comp {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (TB : TopBasis s I ι) {A' : Type} [CommRing A'] {t : A →+* A'} {κ : Type}
    (TB' : TopBasis t (I.map s) κ) : TopBasis (t.comp s) I (ι × κ) where
  b p := t (TB.b p.1) * TB'.b p.2
  c p := (TB.c p.1).comp (TB'.c p.2)
  c_mul p a x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.coe_comp]
    rw [TB'.c_mul, TB.c_mul]
  c_self p := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [TB'.c_mul, TB'.c_self, mul_one, TB.c_self]
  c_ne p q h := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [TB'.c_mul]
    by_cases hj : p.2 = q.2
    · rw [hj, TB'.c_self, mul_one, TB.c_ne]
      intro hi; exact h (Prod.ext hi hj)
    · rw [TB'.c_ne _ _ hj, mul_zero, map_zero]
  fin x n := by
    have hS := TB'.fin x n
    refine ((Set.Finite.biUnion hS fun j _ => TB.fin (TB'.c j x) n).prod hS).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, AddMonoidHom.coe_comp, Function.comp_apply] at hp
    have h2 : TB'.c p.2 x ∉ (I.map s) ^ n := fun h =>
      hp (TB.coeff_mem_of_mem_map p.1 _ (by rwa [← Ideal.map_pow] at h))
    exact ⟨Set.mem_biUnion (x := p.2) h2 hp, h2⟩
  approx x n F hF := by
    classical
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.coe_comp] at hF ⊢
    have hS := TB'.fin x n
    set G : Finset κ := F.image Prod.snd ∪ hS.toFinset with hG
    set Fi : Finset ι := F.image Prod.fst with hFi
    have h1 : x - ∑ j ∈ G, t (TB'.c j x) * TB'.b j ∈ (I ^ n).map (t.comp s) := by
      have := TB'.approx x n G (fun j hj => by
        by_contra h
        exact hj (Finset.mem_union_right _ (hS.mem_toFinset.2 h)))
      rwa [← Ideal.map_pow, Ideal.map_map] at this
    have h2 : ∀ j, t (TB'.c j x) * TB'.b j - ∑ i ∈ Fi.filter (fun i => (i, j) ∈ F),
        t (s (TB.c i (TB'.c j x))) * (t (TB.b i) * TB'.b j) ∈ (I ^ n).map (t.comp s) := by
      intro j
      have := TB.approx (TB'.c j x) n (Fi.filter (fun i => (i, j) ∈ F)) (fun i hi => by
        apply hF (i, j)
        intro hij
        exact hi (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hij, hij⟩))
      have h' := Ideal.mem_map_of_mem t this
      rw [Ideal.map_map] at h'
      have h'' := Ideal.mul_mem_right (TB'.b j) _ h'
      convert h'' using 1

      rw [map_sub, map_sum, sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    have hsub : F ⊆ Fi ×ˢ G := fun p hp =>
      Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)⟩
    have h3 : ∑ p ∈ F, t (s (TB.c p.1 (TB'.c p.2 x))) * (t (TB.b p.1) * TB'.b p.2) =
        ∑ j ∈ G, ∑ i ∈ Fi.filter (fun i => (i, j) ∈ F), t (s (TB.c i (TB'.c j x))) * (t (TB.b i) * TB'.b j) := by
      simp_rw [Finset.sum_filter]
      rw [← Finset.sum_product_right (s := Fi) (t := G)
        (f := fun p => if p ∈ F then t (s (TB.c p.1 (TB'.c p.2 x))) * (t (TB.b p.1) * TB'.b p.2) else 0)]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    rw [h3]
    have := Ideal.add_mem _ h1 (Ideal.sum_mem (t := G) _ fun j _ => h2 j)
    convert this using 1
    rw [Finset.sum_sub_distrib]; ring
  complete := by rw [← Ideal.map_map]; exact TB'.complete
  i₀ := (TB.i₀, TB'.i₀)
  b_i₀ := by simp [TB.b_i₀, TB'.b_i₀]

theorem topBasis_comp_exists : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type)
    (TB : TopBasis s I ι) (A' : Type) [CommRing A'] (t : A →+* A') (I' : Ideal A) (κ : Type)
    (TB' : TopBasis t I' κ), I' = I.map s → ∃ TC : TopBasis (t.comp s) I (ι × κ),
      (∀ i j, TC.b (i, j) = t (TB.b i) * TB'.b j) ∧ ∀ i j x, TC.c (i, j) x = TB.c i (TB'.c j x) := by
  intro S A _ _ s I ι TB A' _ t I' κ TB' hI
  subst hI
  exact ⟨TB.comp TB', fun _ _ => rfl, fun _ _ _ => rfl⟩

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}

theorem pow_smul_top_eq {R : Type} [CommRing R] (J : Ideal R) (n : ℕ) :
    (J ^ n • ⊤ : Submodule R R) = J ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem c_mem_of_mem (tb : TopBasis s I ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) (i : ι) :
    tb.c i x ∈ I ^ n := by
  have key : ∀ a : A, tb.c i (a * x) ∈ I ^ n := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      intro a
      rw [mul_comm, tb.c_mul]
      exact Ideal.mul_mem_right _ _ hz
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem mem_map_pow_iff (tb : TopBasis s I ι) (n : ℕ) (x : A) :
    x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n :=
  ⟨fun h i => c_mem_of_mem tb n h i, fun h => by simpa using tb.approx x n ∅ (fun i _ => h i)⟩

theorem eq_zero_of_c_eq_zero (tb : TopBasis s I ι) (x : A) (h : ∀ i, tb.c i x = 0) : x = 0 := by
  refine tb.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq, ← Ideal.map_pow]
  exact (mem_map_pow_iff tb n x).2 fun i => by rw [h i]; exact zero_mem _

theorem exists_coeffs_eq_of_null (tb : TopBasis s I ι) (hS : IsHausdorff I S) (a : ι → S)
    (ha : ∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) : ∃ x, ∀ i, tb.c i x = a i := by
  classical
  let F : ℕ → Finset ι := fun n => (ha n).toFinset
  have hF : ∀ n i, i ∉ F n → a i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  have hFm : Monotone F := by
    intro m n hmn i hi
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  let y : ℕ → A := fun n => ∑ i ∈ F n, s (a i) * tb.b i
  have hy : ∀ m n, m ≤ n → y n - y m ∈ (I ^ m).map s := by
    intro m n hmn
    have e : y n - y m = ∑ i ∈ F n \ F m, s (a i) * tb.b i := by
      simp only [y]; rw [← Finset.sum_sdiff (hFm hmn)]; ring
    rw [e]
    exact Ideal.sum_mem _ fun i hi =>
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m i (Finset.mem_sdiff.1 hi).2))
  obtain ⟨x, hx⟩ := tb.complete.toIsPrecomplete.prec (f := y) (fun {m n} hmn => by
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub]
    exact neg_mem (hy m n hmn))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
  have h1 : tb.c i (x - y n) ∈ I ^ n := by
    have h := hx n
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub] at h
    exact c_mem_of_mem tb n (by simpa using neg_mem h) i
  have h2 : tb.c i (y n) - a i ∈ I ^ n := by
    have e : tb.c i (y n) = ∑ j ∈ F n, a j * tb.c i (tb.b j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, map_sum, tb.c_mul]
    rw [e]
    by_cases hi : i ∈ F n
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [tb.c_ne i j (Ne.symm hj), mul_zero])
        (fun h => (h hi).elim), tb.c_self, mul_one, sub_self]
      exact zero_mem _
    · rw [Finset.sum_eq_zero (fun j hj => by rw [tb.c_ne i j (fun h => hi (h ▸ hj)), mul_zero]), zero_sub]
      exact neg_mem (hF n i hi)
  have e : tb.c i x - a i = tb.c i (x - y n) + (tb.c i (y n) - a i) := by rw [map_sub]; ring
  rw [e]
  exact add_mem h1 h2

end GlobalTheory.BSP.TopBasis

theorem GlobalTheory.BSP.TopBasis.coeff_facts : ∀ (S A ι : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S)
    (tb : TopBasis s I ι), (∀ x, (∀ i, tb.c i x = 0) → x = 0) ∧ (∀ (n : ℕ) x, x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n) ∧
    (IsHausdorff I S → ∀ a : ι → S, (∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) → ∃ x, ∀ i, tb.c i x = a i) :=
  fun _ _ _ _ _ _ _ tb => ⟨GlobalTheory.BSP.TopBasis.eq_zero_of_c_eq_zero tb, GlobalTheory.BSP.TopBasis.mem_map_pow_iff tb,
    fun hS a ha => GlobalTheory.BSP.TopBasis.exists_coeffs_eq_of_null tb hS a ha⟩
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}

theorem smul_top_ideal (J : Ideal A) : (J • ⊤ : Submodule A A) = J := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem sub_mem_iff (J : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD ((J ^ n • ⊤ : Submodule A A))] ↔ x - y ∈ J ^ n := by
  rw [SModEq.sub_mem, smul_top_ideal]

theorem eq_zero_of_c (TB : TopBasis s I ι) (x : A) (h : ∀ i, TB.c i x = 0) : x = 0 := by
  have hH : IsHausdorff (I.map s) A := TB.complete.toIsHausdorff
  refine hH.haus x fun n => ?_
  rw [sub_mem_iff, ← Ideal.map_pow]
  have := TB.approx x n ∅ (fun i _ => by rw [h i]; exact zero_mem _)
  simpa using this

theorem c_s (TB : TopBasis s I ι) (i : ι) (a : S) (x : A) : TB.c i (x * s a) = a * TB.c i x := by
  rw [mul_comm]; exact TB.c_mul i a x

theorem coeff_unitIndex_baseMap (TB : TopBasis s I ι) (a : S) : TB.c TB.i₀ (s a) = a := by
  have := TB.c_mul TB.i₀ a (TB.b TB.i₀)
  rw [TB.b_i₀, mul_one, ← TB.b_i₀, TB.c_self, mul_one] at this
  exact this

theorem injective (TB : TopBasis s I ι) : Function.Injective s := fun a b h => by
  rw [← coeff_unitIndex_baseMap TB a, h, coeff_unitIndex_baseMap]

theorem c_mem_of_mem_map (TB : TopBasis s I ι) (L : Ideal S) (x : A) (hx : x ∈ L.map s) (i : ι) :
    TB.c i x ∈ L := by
  let J : Ideal A :=
    { carrier := {y | ∀ a : A, ∀ i, TB.c i (a * y) ∈ L}
      add_mem' := fun {y z} hy hz a i => by rw [mul_add, map_add (f := _)]; exact L.add_mem (hy a i) (hz a i)
      zero_mem' := fun a i => by rw [mul_zero, map_zero]; exact L.zero_mem
      smul_mem' := fun b y hy a i => by rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b) i }
  have hle : L.map s ≤ J := Ideal.map_le_iff_le_comap.2 fun y hy a i => by
    show TB.c i (a * s y) ∈ L
    rw [c_s]; exact L.mul_mem_right _ hy
  have := hle hx 1 i
  rwa [one_mul] at this

theorem mem_map_iff (TB : TopBasis s I ι) (L : Ideal S) (n : ℕ) (hL : I ^ n ≤ L) (x : A) :
    x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L := by
  refine ⟨fun hx i => c_mem_of_mem_map TB L x hx i, fun h => ?_⟩
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n := fun i hi => by
    simpa using hi
  have h1 := Ideal.map_mono (f := s) hL (TB.approx x n _ hF)
  have h2 : ∑ i ∈ (TB.fin x n).toFinset, s (TB.c i x) * TB.b i ∈ L.map s :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (h i))
  simpa using Ideal.add_mem _ h1 h2

open Classical in
theorem c_sum (TB : TopBasis s I ι) (z : ι → S) (F : Finset ι) (i : ι) :
    TB.c i (∑ j ∈ F, s (z j) * TB.b j) = if i ∈ F then z i else 0 := by

  rw [map_sum]
  simp_rw [TB.c_mul]
  split_ifs with hi
  · rw [Finset.sum_eq_single i (fun j _ hj => by rw [TB.c_ne i j (Ne.symm hj), mul_zero])
      (fun h => (h hi).elim), TB.c_self, mul_one]
  · exact Finset.sum_eq_zero fun j hj => by
      rw [TB.c_ne i j (fun e => hi (e ▸ hj)), mul_zero]

theorem exists_c_eq (TB : TopBasis s I ι) (hS : IsHausdorff I S) (z : ι → S)
    (hz : ∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) : ∃ x, ∀ i, TB.c i x = z i := by
  classical
  let F : ℕ → Finset ι := fun n => (hz n).toFinset
  have hFm : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  have hFc : ∀ n i, i ∉ F n → z i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  let f : ℕ → A := fun n => ∑ i ∈ F n, s (z i) * TB.b i
  have hP : IsPrecomplete (I.map s) A := TB.complete.toIsPrecomplete
  obtain ⟨x, hx⟩ := hP.prec' f (fun {m n} hmn => by
    rw [sub_mem_iff, ← Ideal.map_pow, ← neg_mem_iff, neg_sub]
    show (∑ i ∈ F n, s (z i) * TB.b i) - ∑ i ∈ F m, s (z i) * TB.b i ∈ _
    rw [← Finset.sum_sdiff (hFm hmn), add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem s (hFc m i (Finset.mem_sdiff.1 hi).2)))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_top_ideal]
  have h1 : TB.c i (f n - x) ∈ I ^ n := by
    have := (sub_mem_iff _ n _ _).1 (hx n)
    rw [← Ideal.map_pow] at this
    exact c_mem_of_mem_map TB _ _ this i
  have h2 : TB.c i (f n) - z i ∈ I ^ n := by
    show TB.c i (∑ j ∈ F n, s (z j) * TB.b j) - z i ∈ I ^ n
    rw [c_sum]
    split_ifs with hi
    · rw [sub_self]; exact zero_mem _
    · rw [zero_sub, neg_mem_iff]; exact hFc n i hi
  have := Ideal.sub_mem _ h2 h1
  rw [map_sub] at this
  simpa using this

theorem map_nonZeroDivisors (TB : TopBasis s I ι) (a : S) (ha : a ∈ nonZeroDivisors S) :
    s a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => eq_zero_of_c TB x fun i => ?_, fun x hx => eq_zero_of_c TB x fun i => ?_⟩
  · have := congrArg (TB.c i) hx
    rw [TB.c_mul, map_zero] at this
    first
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)
  · have := congrArg (TB.c i) hx
    rw [c_s, map_zero] at this
    first
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)

end GlobalTheory.BSP.TopBasis

theorem GlobalTheory.BSP.TopBasis.basic_facts : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι), IsHausdorff I S → (∀ x, (∀ i, TB.c i x = 0) → x = 0) ∧ Function.Injective s ∧ (∀ (L : Ideal S) (n : ℕ), I ^ n ≤ L → ∀ x, x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L) ∧ (∀ z : ι → S, (∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) → ∃ x, ∀ i, TB.c i x = z i) ∧ ∀ a ∈ nonZeroDivisors S, s a ∈ nonZeroDivisors A := by
  intro S A _ _ s I ι TB hS
  exact ⟨TB.eq_zero_of_c, TB.injective, TB.mem_map_iff, TB.exists_c_eq hS, TB.map_nonZeroDivisors⟩
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isDomain_closedDiscGaugeCompletion_of_equiv_norm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), ∀ (N : A → ℝ) (c : ℝ), 0 < c → (∀ x y, N (x * y) = N x * N y) → (∀ x y, N (x + y) ≤ max (N x) (N y)) → N (l : A) = (l : ℝ)⁻¹ → (∀ x, N x ≤ ‖toDisc l u ρ x‖) → (∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) → IsDomain (Disc l u ρ) ∧ ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
  first | exact @GlobalTheory.BSP.DiscDomain.isDomain_disc | exact GlobalTheory.BSP.DiscDomain.isDomain_disc | (intros; apply GlobalTheory.BSP.DiscDomain.isDomain_disc <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.regular_and_bounded_torsion_of_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (i : A →+* Q) (d : A) (N : ℕ) (ι : Type), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → TopBasis i (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ι → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  first | exact @GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded | exact GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded | (intros; apply GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.exists_localUnitary_embedding_definiteUnitary_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → (∀ x, Valued.v (s x) = Valued.v x) → ¬ IsSplitAt w → ∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧ (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧ ∀ x g, cLoc w x = 1 → x * ι g = ι g * x := by
  first | exact @GlobalTheory.UnitaryBC.exists_locUnitary_embedding | exact GlobalTheory.UnitaryBC.exists_locUnitary_embedding | (intros; apply GlobalTheory.UnitaryBC.exists_locUnitary_embedding <;> assumption)
end
