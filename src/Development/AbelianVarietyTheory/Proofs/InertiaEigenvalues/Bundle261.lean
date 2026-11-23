module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle046
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
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
import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.Int.LeastGreatest

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem length_torsionBy_quotient_divisible_le (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z Q : Type) [AddCommGroup Z] [Module O Z] [AddCommGroup Q]
    [Module O Q] (π : Z →ₗ[O] Q) (hs : Function.Surjective π)
    (hdiv : ∀ b : O, b ≠ 0 → ∀ x, π x = 0 → ∃ y, π y = 0 ∧ b • y = x)
    (htor : ∃ x, x ≠ 0 ∧ π x = 0 ∧ ∃ b : O, b ≠ 0 ∧ b • x = 0) (a : O) (ha : a ≠ 0) (k : ℕ)
    (hle : Module.length O ↥(Submodule.torsionBy O Z a) ≤
      ((k + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) :
    Module.length O ↥(Submodule.torsionBy O Q a) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical

  have hLfin : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    exact isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero ha)

  let φ : Submodule.torsionBy O Z a →ₗ[O] Submodule.torsionBy O Q a :=
    LinearMap.codRestrict (Submodule.torsionBy O Q a) (π ∘ₗ (Submodule.torsionBy O Z a).subtype)
      (fun z => by
        rw [Submodule.mem_torsionBy_iff, LinearMap.comp_apply, Submodule.subtype_apply,
          ← map_smul, (Submodule.mem_torsionBy_iff _ _).mp z.2, map_zero])

  have hφ : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, rfl⟩ := hs q
    have h1 : π (a • z) = 0 := by
      rw [map_smul]; exact (Submodule.mem_torsionBy_iff _ _).mp hq
    obtain ⟨y, hy0, hy⟩ := hdiv a ha (a • z) h1
    refine ⟨⟨z - y, ?_⟩, ?_⟩
    · rw [Submodule.mem_torsionBy_iff, smul_sub, hy, sub_self]
    · apply Subtype.ext
      simp [φ, hy0]
  have hexact := Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ
    (Submodule.subtype_injective _) hφ (LinearMap.exact_subtype_ker_map φ)

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨x, hx0, hxK, b, hb0, hbx⟩ := htor
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hxm : ϖ ^ m • x = 0 := by
    rw [mul_smul, ← Units.smul_def, smul_eq_zero_iff_eq] at hbx
    exact hbx
  have hex : ∃ j, ϖ ^ j • x = 0 := ⟨m, hxm⟩
  have hj : ϖ ^ Nat.find hex • x = 0 := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, one_smul] at hj
    exact hx0 hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have he0 : ϖ ^ i • x ≠ 0 := Nat.find_min hex (by omega)
  have hϖe : ϖ • (ϖ ^ i • x) = 0 := by
    rw [hi] at hj
    rw [smul_smul, ← pow_succ']; exact hj
  have heK : π (ϖ ^ i • x) = 0 := by rw [map_smul, hxK, smul_zero]
  have hunit_e : ∀ w : O, IsUnit w → w • (ϖ ^ i • x) ≠ 0 := by
    intro w hw h
    exact he0 ((hw.smul_eq_zero).mp h)
  obtain ⟨n, v, hav⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hadvd : ∀ c : O, a ∣ c ↔ ϖ ^ n ∣ c := by
    intro c; rw [hav, Units.mul_left_dvd]
  obtain ⟨y₀, hy₀K, hy₀⟩ : ∃ y₀ : Z, π y₀ = 0 ∧ ∀ c : O, c • y₀ = 0 ↔ a ∣ c := by
    cases n with
    | zero =>
      refine ⟨0, map_zero π, fun c => ?_⟩
      rw [hadvd, pow_zero]
      simp
    | succ n' =>
      obtain ⟨y, hyK, hy⟩ := hdiv (ϖ ^ n') (pow_ne_zero _ hϖ.ne_zero) _ heK
      refine ⟨y, hyK, fun c => ?_⟩
      rw [hadvd]
      constructor
      · intro hc
        by_cases hc0 : c = 0
        · rw [hc0]; exact dvd_zero _
        obtain ⟨r, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
        by_cases hr : n' + 1 ≤ r
        · exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hr) _
        · exfalso
          obtain ⟨d, hd⟩ : ∃ d, n' = r + d := ⟨n' - r, by omega⟩
          apply hunit_e (w : O) w.isUnit
          have hmul : (w : O) * ϖ ^ n' = ϖ ^ d * ((w : O) * ϖ ^ r) := by rw [hd, pow_add]; ring
          rw [← hy, smul_smul, hmul, mul_smul, hc, smul_zero]
      · rintro ⟨d, rfl⟩
        have hmul : ϖ ^ (n' + 1) * d = d * ϖ * ϖ ^ n' := by ring
        rw [hmul, mul_smul, hy, mul_smul, hϖe, smul_zero]
  have hy₀T : y₀ ∈ Submodule.torsionBy O Z a :=
    (Submodule.mem_torsionBy_iff _ _).mpr ((hy₀ a).mpr dvd_rfl)
  have hy₀ker : (⟨y₀, hy₀T⟩ : Submodule.torsionBy O Z a) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp [φ, hy₀K]
  let f : O →ₗ[O] LinearMap.ker φ := LinearMap.toSpanSingleton O _ ⟨⟨y₀, hy₀T⟩, hy₀ker⟩
  have hker : Ideal.span {a} = LinearMap.ker f := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton, ← hy₀ c]
    simp [Subtype.ext_iff]
  have hK : Module.length O (O ⧸ Ideal.span {a}) ≤ Module.length O (LinearMap.ker φ) := by
    calc Module.length O (O ⧸ Ideal.span {a})
        = Module.length O (O ⧸ LinearMap.ker f) :=
          (Submodule.quotEquivOfEq _ _ hker).length_eq
      _ = Module.length O (LinearMap.range f) := f.quotKerEquivRange.length_eq
      _ ≤ Module.length O (LinearMap.ker φ) :=
          Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _)
  have h2 : Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (O ⧸ Ideal.span {a}) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) + Module.length O (O ⧸ Ideal.span {a}) := by
    calc _ ≤ Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (LinearMap.ker φ) := by
            gcongr
      _ = Module.length O ↥(Submodule.torsionBy O Z a) := by rw [hexact, add_comm]
      _ ≤ _ := hle
      _ = _ := by push_cast; ring
  exact (ENat.add_le_add_iff_right hLfin).mp h2

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

open scoped Topology

theorem fixingSubgroupEquiv_bicontinuous (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] :
    Continuous (IntermediateField.fixingSubgroupEquiv K) ∧
      Continuous (IntermediateField.fixingSubgroupEquiv K).symm := by
  refine ⟨continuous_of_continuousAt_one _ ?_, continuous_of_continuousAt_one _ ?_⟩
  · rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro s hs
    obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
    have : IsScalarTower k K E := ⟨fun a b x => Subtype.ext (smul_assoc a b (x : Ω))⟩
    have hE' : Module.Finite k E := Module.Finite.trans K E
    have hfin : FiniteDimensional k (E.restrictScalars k) := hE'
    rw [mem_nhds_subtype]
    refine ⟨(E.restrictScalars k).fixingSubgroup,
      (krullTopology_mem_nhds_one_iff k Ω _).2 ⟨E.restrictScalars k, hfin, subset_rfl⟩, ?_⟩
    intro σ hσ
    apply hEs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx
  · rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro s hs
    obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).1 hs
    obtain ⟨E, hE, hEu⟩ := (krullTopology_mem_nhds_one_iff k Ω u).1 hu
    let F : IntermediateField K Ω := IntermediateField.extendScalars (le_sup_right : K ≤ E ⊔ K)
    have hk : FiniteDimensional k (E ⊔ K : IntermediateField k Ω) := inferInstance
    have : Module.Finite k F := hk
    have hF : FiniteDimensional K F := Module.Finite.of_restrictScalars_finite k K F
    refine (krullTopology_mem_nhds_one_iff K Ω _).2 ⟨F, hF, ?_⟩
    intro τ hτ
    apply hus
    apply hEu
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := E) hx))

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_family_adapted_filtration :
    ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W) (d : ℕ), Module.Finite E ↥D → Module.finrank E ↥D = d → (∀ a, F (a + 1) ≤ F a) → (∀ x, ∃ a, x ∈ F a) → (∀ x, (∀ a, x ∈ F a) → x = 0) → ∃ (x : Fin d → W) (u : Fin d → ℤ), (∀ k, x k ∈ D ∧ x k ∈ F (u k)) ∧ ∀ (a : ℤ) (c : Fin d → E), (∀ k, u k ≠ a → c k = 0) → ∑ k, c k • x k ∈ F (a + 1) → ∀ k, c k = 0 := by
  intro E W _ _ _ D F d hfin hd hF hex hsep
  have anti : Antitone F := antitone_int_of_succ_le hF
  induction d generalizing D with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  | succ d ih =>
    have hne : D ≠ ⊥ := by
      rintro rfl
      simp at hd
    have hinh : ∃ z, D ≤ F z := by
      obtain ⟨s, hs⟩ : D.FG := Module.Finite.iff_fg.mp hfin
      choose g hg using hex
      obtain ⟨m, hm⟩ := (s.image g).bddBelow
      refine ⟨m, ?_⟩
      rw [← hs, Submodule.span_le]
      intro y hy
      exact anti (hm (by simpa using ⟨y, hy, rfl⟩)) (hg y)
    have hbdd : ∃ b : ℤ, ∀ z, D ≤ F z → z ≤ b := by
      obtain ⟨y, hyD, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have : ∃ b, y ∉ F b := by
        by_contra h
        push Not at h
        exact hy0 (hsep y h)
      obtain ⟨b, hb⟩ := this
      refine ⟨b, fun z hz => ?_⟩
      by_contra h
      exact hb (anti (not_le.mp h).le (hz hyD))
    obtain ⟨lo, hlo, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
    have hnot : ¬ D ≤ F (lo + 1) := fun h => by have := hmax _ h; omega
    obtain ⟨x0, hx0D, hx0F⟩ := SetLike.not_le_iff_exists.mp hnot
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hx0F
    have hx0 : x0 ∉ D ⊓ LinearMap.ker f := fun h => hf0 h.2
    have hfin' : Module.Finite E ↥(D ⊓ LinearMap.ker f) :=
      Submodule.finiteDimensional_of_le (inf_le_left : D ⊓ LinearMap.ker f ≤ D)
    have hsup : (D ⊓ LinearMap.ker f) ⊔ Submodule.span E {x0} = D := by
      apply le_antisymm
      · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hx0D)
      · intro y hy
        have h1 : y - (f y / f x0) • x0 ∈ D ⊓ LinearMap.ker f := by
          refine ⟨D.sub_mem hy (D.smul_mem _ hx0D), ?_⟩
          simp [LinearMap.mem_ker, div_mul_cancel₀ _ hf0]
        have h2 : (f y / f x0) • x0 ∈ Submodule.span E {x0} :=
          Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        simpa using Submodule.add_mem_sup h1 h2
    have hd' : Module.finrank E ↥(D ⊓ LinearMap.ker f) = d := by
      have hne0 : x0 ≠ 0 := fun h => hf0 (by simp [h])
      have := Submodule.finrank_sup_add_finrank_inf_eq (D ⊓ LinearMap.ker f) (Submodule.span E {x0})
      rw [hsup, hd, ((Submodule.disjoint_span_singleton' hne0).mpr hx0).eq_bot, finrank_bot,
        finrank_span_singleton hne0] at this
      omega
    obtain ⟨x, u, h1, h2⟩ := ih _ hfin' hd'
    refine ⟨Fin.cons x0 x, Fin.cons lo u, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ⟨hx0D, hlo hx0D⟩
      · exact ⟨(h1 j).1.1, (h1 j).2⟩
    · intro a c hc hs
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      have hc0 : c 0 = 0 := by
        by_cases ha : lo = a
        · subst ha
          have h3 := hf hs

          rw [LinearMap.mem_ker, map_add (f := _), map_sum, map_smul] at h3
          have h4 : ∑ j : Fin d, f (c j.succ • x j) = 0 :=
            Finset.sum_eq_zero fun j _ => by
              rw [map_smul, (LinearMap.mem_ker.mp (h1 j).1.2), smul_zero]
          rw [h4, add_zero, smul_eq_mul] at h3
          exact (mul_eq_zero.mp h3).resolve_right hf0
        · exact hc 0 ha
      rw [hc0, zero_smul, zero_add] at hs
      have h5 := h2 a (fun j => c j.succ) (fun j hj => hc j.succ hj) hs
      intro k
      exact Fin.cases hc0 h5 k

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.finite_setOf_inf_filtration_ne_succ : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W), Module.Finite E ↥D → (∀ a, F (a + 1) ≤ F a) → {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  first | exact @GlobalTheory.finite_jumps_inf_filtration | exact GlobalTheory.finite_jumps_inf_filtration | (intros; apply GlobalTheory.finite_jumps_inf_filtration <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Topology Filter

namespace GlobalTheory

private lemma mem_span_pow_smul_iff_exists_pow_smul {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] (n : ℕ) (x : M) :
    x ∈ (Ideal.span {a}) ^ n • (⊤ : Submodule R M) ↔ ∃ y : M, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp [eq_comm]

theorem continuous_adicModule_iff {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] {G : Type} [TopologicalSpace G] (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g : G) (n : ℕ), ∀ᶠ h in 𝓝 g, ∃ y : M, f h - f g = a ^ n • y := by
  let _ : TopologicalSpace R := (Ideal.span {a}).ringFilterBasis.topology
  let _ : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hB : ∀ y : M, (𝓝 y).HasBasis
      (fun V : Set M => ∃ n : ℕ, V = ↑((Ideal.span {a}) ^ n • (⊤ : Submodule R M)))
      (fun V => (fun z => y + z) '' V) := fun y =>
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M)).toAddGroupFilterBasis.nhds_hasBasis y
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g => ?_
  refine ((hB (f g)).tendsto_right_iff).trans ⟨fun H n => ?_, fun H V hV => ?_⟩
  · filter_upwards [H _ ⟨n, rfl⟩] with h hh
    obtain ⟨z, hz, hzh⟩ := hh
    obtain ⟨y, rfl⟩ := (mem_span_pow_smul_iff_exists_pow_smul a n z).1 hz
    beta_reduce at hzh
    exact ⟨y, by rw [← hzh, add_sub_cancel_left]⟩
  · obtain ⟨n, rfl⟩ := hV
    filter_upwards [H n] with h hh
    obtain ⟨y, hy⟩ := hh
    exact ⟨a ^ n • y, (mem_span_pow_smul_iff_exists_pow_smul a n _).2 ⟨y, rfl⟩, by
      show f g + a ^ n • y = f h
      rw [← hy]; abel⟩

end GlobalTheory
end
