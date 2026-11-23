module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace LatTens

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem div_mem_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s)
    (ht : Λ.IsGenAt p t) : s / t ∈ regAt ξ p := by
  obtain ⟨_, hsΛ⟩ := hs
  obtain ⟨ht0, htΛ⟩ := ht
  have hmem : s ∈ Submodule.span (regAt ξ p) ({t} : Set Ω) := by
    rw [← htΛ, hsΛ]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hr' : (r : Ω) * t = s := by
    first
    | exact hr
    | simpa [Subring.smul_def] using hr
  rw [← hr', mul_div_assoc, div_self ht0, _root_.mul_one]
  exact r.2

theorem zpow_mem_of_inv_mem {R : Subring Ω} {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (a : ℤ) : u ^ a ∈ R := by
  cases a with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using pow_mem h n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow_mem h' (n + 1)

theorem tens_eq_span {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) :
    Lat.tens Λ a p = Submodule.span (regAt ξ p) {∏ i, s i ^ a i} := by
  rw [show Lat.tens Λ a p = Submodule.span (regAt ξ p)
      {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} from rfl]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨s', hs', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨∏ i, (s' i / s i) ^ a i, ?_⟩, ?_⟩
    · refine prod_mem fun i _ => zpow_mem_of_inv_mem (div_mem_of_isGenAt (hs' i) (hs i)) ?_ (a i)
      rw [inv_div]
      exact div_mem_of_isGenAt (hs i) (hs' i)
    · show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨s, hs, rfl⟩

theorem isGenAt_tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, tens_eq_span Λ a p s hs⟩
  exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1

theorem mem_finset_inf {I : Type} (S : Finset I) (U : I → X.Opens) (x : X) :
    x ∈ S.inf U ↔ ∀ i ∈ S, x ∈ U i := by
  classical
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.inf_empty]
    exact ⟨fun _ i hi => by simp at hi, fun _ => TopologicalSpace.Opens.mem_top x⟩
  · intro j S' _ ih
    rw [Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih]
    rw [Finset.forall_mem_insert]

theorem isGenAt_of_isFrameAt {Λ : Lat ξ Ω} {b : Fin 1 → Ω} {p : Cpt ξ} (h : Λ.IsFrameAt b p) :
    Λ.IsGenAt p (b 0) := by
  refine ⟨LinearIndependent.ne_zero 0 h.1, ?_⟩
  rw [h.2, Set.range_unique, Subsingleton.elim (default : Fin 1) 0]

theorem isFrameAt_of_isGenAt {Λ : Lat ξ Ω} {c : Ω} {p : Cpt ξ} (h : Λ.IsGenAt p c) :
    Λ.IsFrameAt (fun _ : Fin 1 => c) p := by
  refine ⟨linearIndependent_unique_iff.mpr h.1, ?_⟩
  rw [h.2, Set.range_const]

theorem tens_isVBOn (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type)
    [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (h : ∀ i, (Λ i).IsVBOn T 1 ⊤) (a : I → ℤ) :
    (Lat.tens Λ a).IsVBOn T 1 ⊤ ∧ ∀ p ∈ T, ∀ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) →
      (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, fun p _ s hs => isGenAt_tens Λ a p s hs⟩
  intro p hp
  choose U hpU b _ hfr using fun i => h i p hp
  refine ⟨Finset.univ.inf U, (mem_finset_inf _ _ _).mpr fun i _ => hpU i,
    fun _ => ∏ i, b i 0 ^ a i, ?_, ?_⟩
  · have hc : (∏ i, b i 0 ^ a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
      zpow_ne_zero _ (LinearIndependent.ne_zero 0 (hfr i p hp (hpU i)).1)
    rw [Set.range_const, eq_top_iff]
    intro y _
    rw [Submodule.mem_span_singleton]
    exact ⟨y / ∏ i, b i 0 ^ a i, by rw [smul_eq_mul, div_mul_cancel₀ _ hc]⟩
  · intro q hq hqU
    rw [mem_finset_inf] at hqU
    exact isFrameAt_of_isGenAt (isGenAt_tens Λ a q (fun i => b i 0) fun i =>
      isGenAt_of_isFrameAt (hfr i q hq (hqU i (Finset.mem_univ i))))

end LatTens

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagGrGen

theorem exists_coord {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b : Fin r → E}
    (hb : LinearIndependent Ω b) (i : Fin r) :
    ∃ φ : E →ₗ[Ω] Ω, φ (b i) = 1 ∧ ∀ k, k ≠ i → φ (b k) = 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hb).coord i)
  have key : ∀ k, g (b k) = Finsupp.single k (1 : Ω) i := by
    intro k
    have hk : (Module.Basis.span hb k : E) = b k := by rw [Module.Basis.span_apply]
    have := LinearMap.congr_fun hg (Module.Basis.span hb k)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply, Module.Basis.repr_self] at this
    rw [hk] at this
    exact this
  refine ⟨g, ?_, ?_⟩
  · rw [key]
    simp
  · intro k hk
    rw [key]
    simp [Ne.symm hk]

theorem gr_isGenAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b₀ b : Fin r → E) (p : Cpt ξ) (i : Fin r) (t : Ω), LinearIndependent Ω b₀ → (∀ s, flagStep Ω b s = flagStep Ω b₀ s) → L.IsFrameAt b p → b i - t • b₀ i ∈ flagStep Ω b₀ i → (L.gr b₀ i).IsGenAt p t := by
  intro X Ω _ ξ E _ _ L r b₀ b p i t hb₀ hflag hframe hti
  obtain ⟨hb, hLp⟩ := hframe
  obtain ⟨f0, hf0⟩ := exists_coord hb₀ i
  obtain ⟨g, hg⟩ := exists_coord hb i
  have hflag_i : flagStep Ω b₀ (i : ℕ) = flagStep Ω b (i : ℕ) := (hflag (i : ℕ)).symm
  have hf0ker : ∀ v ∈ flagStep Ω b₀ (i : ℕ), f0 v = 0 := by
    intro v hv
    have hle : flagStep Ω b₀ (i : ℕ) ≤ LinearMap.ker f0 := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hki : k ≠ i := by
        rintro rfl
        simp at hk
      exact LinearMap.mem_ker.mpr (hf0.2 k hki)
    exact LinearMap.mem_ker.mp (hle hv)
  have hgker : ∀ v ∈ flagStep Ω b (i : ℕ), g v = 0 := by
    intro v hv
    have hle : flagStep Ω b (i : ℕ) ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hki : k ≠ i := by
        rintro rfl
        simp at hk
      exact LinearMap.mem_ker.mpr (hg.2 k hki)
    exact LinearMap.mem_ker.mp (hle hv)
  have hf0bi : f0 (b i) = t := by
    have := hf0ker _ hti
    rw [map_sub, map_smul, hf0.1, smul_eq_mul, _root_.mul_one, sub_eq_zero] at this
    exact this
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hbi : b i ∈ flagStep Ω b (i : ℕ) := by
      rw [← hflag_i]
      simpa using hti
    have := hgker _ hbi
    rw [hg.1] at this
    exact one_ne_zero this
  have hmono : flagStep Ω b (i : ℕ) ≤ flagStep Ω b ((i : ℕ) + 1) :=
    Submodule.span_mono (Set.image_mono (fun k hk => by
      simp only [Set.mem_setOf_eq] at hk ⊢
      omega))
  have hb0i : b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := by
    rw [hflag]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have hagree : ∀ v ∈ flagStep Ω b ((i : ℕ) + 1), f0 v = t * g v := by
    intro v hv
    have hle : flagStep Ω b ((i : ℕ) + 1) ≤ LinearMap.eqLocus f0 (t • g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
      rw [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearMap.smul_apply, smul_eq_mul]
      rcases lt_or_eq_of_le (by omega : (k : ℕ) ≤ (i : ℕ)) with hlt | heq
      · have hki : k ≠ i := by
          rintro rfl
          exact lt_irrefl _ hlt
        rw [hg.2 k hki, mul_zero]
        apply hf0ker
        rw [hflag_i]
        exact Submodule.subset_span ⟨k, hlt, rfl⟩
      · have hki : k = i := Fin.ext heq
        rw [hki, hg.1, _root_.mul_one, hf0bi]
    have := hle hv
    rw [LinearMap.mem_eqLocus, LinearMap.smul_apply, smul_eq_mul] at this
    exact this
  have hgO : ∀ v ∈ Submodule.span (regAt ξ p) (Set.range b), g v ∈ regAt ξ p := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      by_cases hki : k = i
      · rw [hki, hg.1]
        exact one_mem _
      · rw [hg.2 k hki]
        exact zero_mem _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      show g ((a : Ω) • x) ∈ regAt ξ p
      rw [map_smul, smul_eq_mul]
      exact mul_mem a.2 hx
  have hbiL : b i ∈ L p := by
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩
  show t ≠ 0 ∧ Submodule.span (regAt ξ p) {s | ∃ e ∈ L p, e - s • b₀ i ∈ flagStep Ω b₀ i} = Submodule.span (regAt ξ p) {t}
  refine ⟨ht0, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro s ⟨e, he, hes⟩
    rw [hLp] at he
    have he_flag : e ∈ flagStep Ω b ((i : ℕ) + 1) := by
      have h1 : e - s • b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := hmono (by rw [← hflag_i]; exact hes)
      have h2 : s • b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := Submodule.smul_mem _ s hb0i
      simpa using add_mem h1 h2
    have hs : s = f0 e := by
      have := hf0ker _ hes
      rw [map_sub, map_smul, hf0.1, smul_eq_mul, _root_.mul_one, sub_eq_zero] at this
      exact this.symm
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨g e, hgO e he⟩, ?_⟩
    show g e * t = s
    rw [hs, hagree e he_flag, _root_.mul_comm]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨b i, hbiL, hti⟩

end GlobalTheory.CompanionTheory.Ar.FlagGrGen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TensDeg

lemma zpow_mem_of_unit {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat n => simpa using pow_mem h n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

lemma exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {s t : Ω} (ht : t ≠ 0)
    (h : Submodule.span R {s} = Submodule.span R {t}) : ∃ u, u ∈ R ∧ u⁻¹ ∈ R ∧ s = u * t := by
  have h1 : s ∈ Submodule.span R {t} := h ▸ Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span R {s} := h ▸ Submodule.mem_span_singleton_self t
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  have ha' : (a : Ω) * t = s := ha
  have hb' : (b : Ω) * s = t := hb
  have hba : (b : Ω) * a = 1 := by
    apply mul_right_cancel₀ ht
    rw [_root_.mul_assoc, ha', hb', _root_.one_mul]
  refine ⟨a, a.2, ?_, ha'.symm⟩
  rw [inv_eq_of_mul_eq_one_left hba]
  exact b.2

lemma zpow_finset_sum {Ω I : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) (s : Finset I) (f : I → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hx, ih]

end GlobalTheory.CompanionTheory.Ar.TensDeg


open GlobalTheory.CompanionTheory.Ar.TensDeg in
theorem GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (d : I → K → ℤ) (e : I → Ω), (∀ i, (Λ i).IsDegOn T y (d i) (e i)) → ∀ a : I → ℤ, (Lat.tens Λ a).IsDegOn T y (∑ i, a i • d i) (∏ i, e i ^ a i) := by
  intro X Ω _ ξ K _ J y I _ Λ T d e h a
  have he : ∀ i, e i ≠ 0 := fun i => (h i).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (he i), ?_⟩
  intro p hp c hc
  have hc0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k)
  let g : I → Ω := fun i => (∏ k, y ⟨k, c k⟩ ^ d i k) • e i
  have hg0 : ∀ i, g i ≠ 0 := fun i =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (he i)
  have hgen : ∀ i, (Λ i).IsGenAt p (g i) := fun i => ⟨hg0 i, (h i).2 p hp c hc⟩
  have hG : (∏ k, y ⟨k, c k⟩ ^ (∑ i, a i • d i) k) • (∏ i, e i ^ a i) = ∏ i, g i ^ a i := by
    simp only [g, smul_eq_mul, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    simp_rw [← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.sum_apply, zpow_finset_sum (hy k)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  rw [hG]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s, hs, rfl⟩
    choose u hu hu' hsu using fun i =>
      exists_unit_of_span_eq (regAt ξ p) (hg0 i) ((hs i).2.symm.trans (hgen i).2)
    have hm : ∏ i, u i ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_mem_of_unit _ (hu i) (hu' i) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ i, u i ^ a i) * ∏ i, g i ^ a i = ∏ i, s i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hsu i, mul_zpow]
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨g, hgen, rfl⟩))
end

section

open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem leadCoef_ratio_mem (Ω : Type) [Field Ω] (Li : Type) [AddCommGroup Li] [Module Ω Li] (W : Subring Ω) (r : ℕ)
    (b₀ b b' : Fin r → Li) (N : Ω) (k : Fin r) (t t' : Ω) (hb : LinearIndependent Ω b)
    (hbf : ∀ j, flagStep Ω b j = flagStep Ω b₀ j) (_hbf' : ∀ j, flagStep Ω b' j = flagStep Ω b₀ j)
    (hN : ∀ j, N • b' j ∈ Submodule.span W (Set.range b))
    (ht : b k - t • b₀ k ∈ flagStep Ω b₀ k) (ht' : b' k - t' • b₀ k ∈ flagStep Ω b₀ k) :
    N * (t' / t) ∈ W := by
  by_cases ht0 : t = 0
  · rw [ht0, div_zero, mul_zero]
    exact W.zero_mem
  obtain ⟨u, hu_def⟩ : ∃ u : Ω, u = t' / t := ⟨_, rfl⟩
  rw [← hu_def]
  have hu : u * t = t' := by rw [hu_def, div_mul_cancel₀ t' ht0]
  have hF : N • b' k - (N * u) • b k ∈ flagStep Ω b k := by
    rw [hbf]
    have h1 := Submodule.sub_mem _ (Submodule.smul_mem _ N ht') (Submodule.smul_mem _ (N * u) ht)
    rw [← hu] at h1
    convert h1 using 1
    module
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun W).mp (hN k)
  rw [← hw] at hF
  have hF' : (∑ i, w i • b i) - (N * u) • b k ∈ Submodule.span Ω (b '' {j : Fin r | (j : ℕ) < k}) := hF
  obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp hF'
  have hsum : Finsupp.linearCombination Ω b
      (Finsupp.equivFunOnFinite.symm fun i => (w i : Ω) - if i = k then N * u else 0) =
      (∑ i, w i • b i) - (N * u) • b k := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ (fun i a => a • b i) (fun i => zero_smul Ω _)]
    simp only [Finsupp.coe_equivFunOnFinite_symm, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Subring.smul_def]
  have h0 : Finsupp.linearCombination Ω b
      ((Finsupp.equivFunOnFinite.symm fun i => (w i : Ω) - if i = k then N * u else 0) - l) = 0 := by
    rw [map_sub, hsum, hlc, sub_self]
  have hl0 := sub_eq_zero.mp (linearIndependent_iff.mp hb _ h0)
  have hk := DFunLike.congr_fun hl0 k
  simp only [Finsupp.coe_equivFunOnFinite_symm, ↓reduceIte] at hk
  have hlk : l k = 0 := (Finsupp.mem_supported' Ω l).mp hl k (by simp)
  rw [hlk, sub_eq_zero] at hk
  rw [← hk]
  exact (w k).2

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.Transport

theorem flagStep_equiv {Ω F F' : Type} [Field Ω] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (Φ : F ≃ₗ[Ω] F') {r : ℕ} (b : Fin r → F) (i : ℕ) :
    flagStep Ω (fun k => Φ (b k)) i = (flagStep Ω b i).map Φ.toLinearMap := by
  rw [flagStep, flagStep, Submodule.map_span, Set.image_image]
  rfl

theorem isGenericFlag_transport : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E₀ E F F' : Type)
    [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F]
    [AddCommGroup F'] [Module Ω F'] (a : E₀ ≃ₗ[Ω₀] E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (S : Type) (r : S → ℕ)
    (V : S → Submodule Ω₀ E) (V₀ : S → Submodule Ω₀ E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ),
    (∀ s e, e ∈ V₀ s ↔ a e ∈ V s) → IsGenericFlag (Ω' := Ω) j V b d →
    IsGenericFlag (Ω' := Ω) ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) V₀
      (fun s k => Φ (b s k)) d := by
  intro Ω₀ Ω _ _ _ E₀ E F F' _ _ _ _ _ _ _ _ a j Φ S r V V₀ b d hV hG
  obtain ⟨c, u, hc, hjlin, hjc, hb, hu1, hu0, hflag, halg, hd, hrank⟩ := hG
  refine ⟨fun σ k => a.symm (c σ k), u, fun σ => ⟨?_, ?_⟩, ?_, fun σ => ?_, fun σ => ?_, hu1, hu0,
    fun σ i => ?_, halg, hd, hrank⟩
  · exact (hc σ).1.map' a.symm.toLinearMap a.symm.ker
  · have h1 : Submodule.span Ω₀ (Set.range fun k => a.symm (c σ k)) =
        (Submodule.span Ω₀ (Set.range (c σ))).map a.symm.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1, (hc σ).2]
    ext e
    rw [hV σ e, Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  · intro x e
    show Φ (j (a (x • e))) = algebraMap Ω₀ Ω x • Φ (j (a e))
    rw [map_smul, hjlin, map_smul]
  · have hfe : (fun k => ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom)
        (a.symm (c σ k))) = ⇑Φ.toLinearMap ∘ fun k => j (c σ k) := by
      funext k
      show Φ (j (a (a.symm (c σ k)))) = Φ (j (c σ k))
      rw [LinearEquiv.apply_symm_apply]
    have h3 : LinearIndependent Ω (fun k => ((Φ.toLinearMap.toAddMonoidHom.comp j).comp
        a.toLinearMap.toAddMonoidHom) (a.symm (c σ k))) := by
      rw [hfe]
      exact (hjc σ).map' Φ.toLinearMap Φ.ker
    exact h3
  · exact (hb σ).map' Φ.toLinearMap Φ.ker
  · have hfun : (fun k => ∑ l, u σ l k •
        ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) (a.symm (c σ l))) =
        fun k => Φ (∑ l, u σ l k • j (c σ l)) := by
      funext k

      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      show u σ l k • Φ (j (a (a.symm (c σ l)))) = u σ l k • Φ (j (c σ l))
      rw [LinearEquiv.apply_symm_apply]
    calc flagStep Ω (fun k => Φ (b σ k)) i = (flagStep Ω (b σ) i).map Φ.toLinearMap := flagStep_equiv Φ (b σ) i
      _ = (flagStep Ω (fun k => ∑ l, u σ l k • j (c σ l)) i).map Φ.toLinearMap := by rw [hflag σ i]
      _ = flagStep Ω (fun k => Φ (∑ l, u σ l k • j (c σ l))) i := (flagStep_equiv Φ _ i).symm
      _ = flagStep Ω (fun k => ∑ l, u σ l k •
          ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) (a.symm (c σ l))) i := by
        rw [hfun]

end GlobalTheory.CompanionTheory.Ar.FlagStep.Transport
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

theorem _root_.GlobalTheory.T.hom_add_mul_of_unit_section : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G] (P V : Type) [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (u : ob x P ⟶ G), zsec x ≫ u = 1 → ∀ f g : P →ₗ[R] V, hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed | exact GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed | (intros; apply GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed <;> assumption)
end
