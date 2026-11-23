module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle014
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open MvPolynomial

theorem finrank_map_add_finrank_inf_ker_of_finite {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (P : Submodule K M) [Module.Finite K P] :
    Module.finrank K ↥(P.map f) + Module.finrank K ↥(P ⊓ LinearMap.ker f) = Module.finrank K P := by
  have h := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq P, Submodule.map_comap_subtype] at h
  exact h

theorem mem_homogeneousSubmodule_mul_of_add {K σ : Type*} [Field K] {m n : ℕ}
    {F : MvPolynomial σ K} (hF : F.IsHomogeneous (m + n)) :
    F ∈ homogeneousSubmodule σ K m * homogeneousSubmodule σ K n := by
  rw [← homogeneousSubmodule_one_pow K m, ← homogeneousSubmodule_one_pow K n, ← pow_add,
    homogeneousSubmodule_one_pow]
  exact hF

theorem sub_rename_mem_span_degree {K σ : Type*} [Field K] (t : σ → σ)
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ F, F - rename t F ∈ I) {d : ℕ} (hd : 1 ≤ d)
    {e : ℕ} (he : d ≤ e) : ∀ F : MvPolynomial σ K, F.IsHomogeneous e →
      F - rename t F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  have hk : ∀ (l : MvPolynomial σ K), l.IsHomogeneous 1 → l ∈ I → ∀ n, d ≤ n →
      ∀ H : MvPolynomial σ K, H.IsHomogeneous n →
      l * H ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    intro l hl hlI n hn H hH
    have hn' : n = (d - 1) + (n - (d - 1)) := by omega
    rw [hn'] at hH
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hH) ?_ ?_
    · intro A hA B _
      rw [← _root_.mul_assoc]
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Ideal.mul_mem_right _ _ hlI, ?_⟩)
      have h := hl.mul hA
      rwa [show 1 + (d - 1) = d by omega] at h
    · intro x y hx hy
      rw [mul_add]
      exact add_mem hx hy
  induction e, he using Nat.le_induction with
  | base =>
    intro F hF
    exact Ideal.subset_span ⟨hI F, hF.sub hF.rename_isHomogeneous⟩
  | succ n hn ih =>
    intro F hF
    rw [add_comm] at hF
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hF) ?_ ?_
    · intro l hl G hG
      have hl' : l.IsHomogeneous 1 := hl
      have hG' : G.IsHomogeneous n := hG
      have : l * G - rename t (l * G) =
          l * (G - rename t G) + (l - rename t l) * rename t G := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ (ih G hG'))
        (hk _ (hl'.sub hl'.rename_isHomogeneous) (hI l) n hn _ hG'.rename_isHomogeneous)
    · intro x y hx hy
      have : x + y - rename t (x + y) = (x - rename t x) + (y - rename t y) := by
        rw [map_add (f := _)]; ring
      rw [this]
      exact add_mem hx hy

theorem regularity_comap_rename_of_surjective :
    ∀ (σ σ₀ : Type) [Finite σ] [Finite σ₀] [Nonempty σ₀] (r : σ → σ₀) (Q₀ : Polynomial ℚ), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (I₀ : Ideal (MvPolynomial σ₀ K)) (I : Ideal (MvPolynomial σ K)) (d : ℕ), I = I₀.comap (MvPolynomial.rename r) → 1 ≤ d → ∀ e ≥ d, (((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ₀ K e ⊓ (I₀).restrictScalars K) : ℕ) : ℚ) = Q₀.eval (e : ℚ) → ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ (I).restrictScalars K) : ℕ) : ℚ) = Q.eval (e : ℚ)) ∧ ((∀ F ∈ I₀, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I₀ ∧ G.IsHomogeneous d}) → ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}) := by
  intro σ σ₀ _ _ _ r Q₀ hr
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  haveI : Nonempty σ := ⟨s (Classical.arbitrary _)⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule σ
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule σ₀
  refine ⟨Q₀ + P - P₀, ?_⟩
  intro K _ I₀ I d hI hd e he
  have hrs : ∀ G : MvPolynomial σ₀ K, rename r (rename s G) = G := by
    intro G
    rw [rename_rename, hs.comp_eq_id, rename_id_apply]
  have hmem : ∀ F, F ∈ I ↔ rename r F ∈ I₀ := by
    intro F
    rw [hI]; exact Ideal.mem_comap
  constructor
  · intro h
    haveI : Module.Finite K (homogeneousSubmodule σ K e) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
    haveI : Module.Finite K ↥(homogeneousSubmodule σ K e ⊓ I.restrictScalars K) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have h1 := finrank_map_add_finrank_inf_ker_of_finite
      (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap (homogeneousSubmodule σ K e)
    have h2 := finrank_map_add_finrank_inf_ker_of_finite
      (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap
      (homogeneousSubmodule σ K e ⊓ I.restrictScalars K)
    have e1 : (homogeneousSubmodule σ K e).map
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ₀ K e := by
      apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        exact IsHomogeneous.rename_isHomogeneous hF
      · intro G hG
        exact ⟨rename s G, IsHomogeneous.rename_isHomogeneous hG, hrs G⟩
    have e2 : (homogeneousSubmodule σ K e ⊓ I.restrictScalars K).map
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ₀ K e ⊓ I₀.restrictScalars K := by
      apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        exact ⟨IsHomogeneous.rename_isHomogeneous hF.1, (hmem F).1 hF.2⟩
      · intro G hG
        refine ⟨rename s G, ⟨IsHomogeneous.rename_isHomogeneous hG.1, (hmem _).2 ?_⟩, hrs G⟩
        rw [hrs]; exact hG.2
    have e3 : homogeneousSubmodule σ K e ⊓ I.restrictScalars K ⊓ LinearMap.ker
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ K e ⊓ LinearMap.ker
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap := by
      apply le_antisymm
      · exact inf_le_inf_right _ inf_le_left
      · intro F hF
        refine ⟨⟨hF.1, (hmem F).2 ?_⟩, hF.2⟩
        have : rename r F = 0 := hF.2
        rw [this]; exact zero_mem _
    rw [e1] at h1
    rw [e2, e3] at h2
    rw [Polynomial.eval_sub, Polynomial.eval_add, ← h, ← hP K e, ← hP₀ K e, ← h1, ← h2]
    push_cast
    ring
  · intro h F hF hFe
    have hA := sub_rename_mem_span_degree (s ∘ r) I (fun G => by
      rw [hmem, map_sub, ← rename_rename, hrs, sub_self]; exact zero_mem _) hd he F hFe
    have hB : Ideal.span {G | G ∈ I₀ ∧ G.IsHomogeneous d} ≤
        (Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}).comap (rename s) := by
      rw [Ideal.span_le]
      intro G hG
      refine Ideal.mem_comap.mpr (Ideal.subset_span ⟨(hmem _).2 ?_, hG.2.rename_isHomogeneous⟩)
      rw [hrs]; exact hG.1
    have hC := Ideal.mem_comap.mp (hB (h _ ((hmem F).1 hF) hFe.rename_isHomogeneous))
    rw [rename_rename] at hC
    simpa using add_mem hA hC

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.span_range_algebraMap_eq_top_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → Module.Finite R C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Submodule.span B (Set.range (algebraMap R C)) = ⊤ := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcompat _ htame hin
  classical
  let M : Subalgebra B C := Algebra.adjoin B (Set.range (algebraMap R C))
  have hRM : ∀ r : R, algebraMap R C r ∈ M := fun r => Algebra.subset_adjoin ⟨r, rfl⟩
  letI : Algebra R M := ((algebraMap R C).codRestrict M hRM).toAlgebra
  haveI : IsScalarTower R M C := IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite M C := Module.Finite.of_restrictScalars_finite R M C
  have hsmulM : ∀ (m : M) (c : C), m • c = (m : C) * c := fun m c => rfl
  have hsmulB : ∀ (b : B) (c : C), b • c = (algebraMap B M b : C) * c := fun b c => by
    rw [Algebra.smul_def]
    rfl
  let P' : Submodule M C := Submodule.span M {1}
  have hmemP' : ∀ c ∈ M, c ∈ P' := by
    intro c hc
    rw [Submodule.mem_span_singleton]
    exact ⟨⟨c, hc⟩, by rw [hsmulM, _root_.mul_one]⟩
  have hcomp : ∀ (g : Γ) (b : B) (x : C), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hcompat]
  have hin' : ∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ x : C,
      g • x - x ∈ q • (⊤ : Submodule B C) := by
    intro q hq g hg x
    rw [Ideal.smul_top_eq_map]
    exact hin q hq g hg x
  have hloc : ∀ P : Ideal M, P.IsMaximal → (⊤ : Submodule M (C ⧸ P')) ≤ P • ⊤ := by
    intro P hP x _
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective P' x
    haveI : P.IsPrime := hP.isPrime
    have hq : (P.comap (algebraMap B M)).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨s, hs, hsc⟩ := _root_.GlobalTheory.exists_smul_mem_span_invariants_sup Γ B C hcomp _ hq
      (htame _ hq) (hin' _ hq) c
    have hsmall : ∀ y ∈ Submodule.span B {y : C | ∀ g : Γ, g • y = y} ⊔
        (P.comap (algebraMap B M)) • (⊤ : Submodule B C),
        (Submodule.Quotient.mk y : C ⧸ P') ∈ P • (⊤ : Submodule M (C ⧸ P')) := by
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [Submodule.Quotient.mk_add]
      refine add_mem ?_ ?_
      · have h1 : y₁ ∈ Subalgebra.toSubmodule M := by
          refine (Submodule.span_le (p := Subalgebra.toSubmodule M)).mpr ?_ hy₁
          intro z hz
          obtain ⟨r, rfl⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := Γ) z hz
          exact hRM r
        rw [(Submodule.Quotient.mk_eq_zero P').mpr (hmemP' _ h1)]
        exact zero_mem _
      · refine Submodule.smul_induction_on
          (p := fun y => (Submodule.Quotient.mk y : C ⧸ P') ∈ P • (⊤ : Submodule M (C ⧸ P'))) hy₂ ?_ ?_
        · intro b hb z _
          rw [show b • z = (algebraMap B M b) • z by rw [hsmulM, hsmulB],
            Submodule.Quotient.mk_smul]
          exact Submodule.smul_mem_smul hb trivial
        · intro z w hz hw
          simp only [Submodule.Quotient.mk_add]
          exact add_mem hz hw
    have hσ : algebraMap B M s ∉ P := hs
    obtain ⟨u, i, hi, hui⟩ := hP.exists_inv hσ
    have hx : (Submodule.Quotient.mk c : C ⧸ P') =
        u • (Submodule.Quotient.mk (s • c) : C ⧸ P') + i • Submodule.Quotient.mk c := by
      rw [show s • c = (algebraMap B M s) • c by rw [hsmulM, hsmulB], Submodule.Quotient.mk_smul,
        smul_smul, ← add_smul, hui, one_smul]
    rw [hx]
    exact add_mem (Submodule.smul_mem _ _ (hsmall _ hsc)) (Submodule.smul_mem_smul hi trivial)
  have hann : Module.annihilator M (C ⧸ P') = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P
      (⊤ : Submodule M (C ⧸ P')) Module.Finite.fg_top (hloc P hP)
    have hrP : r ∈ P := hle (Module.mem_annihilator.mpr fun n => hr n trivial)
    have h1 : (1 : M) ∈ P := by simpa using P.sub_mem hrP hr1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  refine eq_top_iff.mpr fun c _ => ?_
  have h1 : (1 : M) ∈ Module.annihilator M (C ⧸ P') := by
    rw [hann]
    exact Submodule.mem_top
  have hc0 : (Submodule.Quotient.mk c : C ⧸ P') = 0 := by
    have h := Module.mem_annihilator.mp h1 (Submodule.Quotient.mk c)
    rwa [one_smul] at h
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero P').mp hc0)
  rw [hsmulM, _root_.mul_one] at hm
  have hcM : c ∈ Subalgebra.toSubmodule M := hm ▸ m.2
  rw [Algebra.adjoin_eq_span] at hcM
  refine Submodule.span_mono ?_ hcM
  intro z hz
  have hcl : Submonoid.closure (Set.range (algebraMap R C)) ≤
      (algebraMap R C).rangeS.toSubmonoid :=
    Submonoid.closure_le.mpr fun w ⟨r, hr⟩ => ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hcl hz
  exact ⟨r, hr⟩

end GlobalTheory
end
