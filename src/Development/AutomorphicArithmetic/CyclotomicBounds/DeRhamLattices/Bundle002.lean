module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule :
    ∀ {G O LL V : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (ρ : Representation LL G V)
      (Λ : Lattice (O := O) ρ) (A : Submodule O V), A.FG → (∀ g, ∀ a ∈ A, ρ g a ∈ A) → ∀ μ : O, μ ≠ 0 →
      ∃ L : Lattice (O := O) ρ, ∀ v, v ∈ L.T ↔ ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u := by
  intro G O LL V _ _ _ _ _ _ _ _ _ _ _ ρ Λ A hA hst μ hμ
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hmem : ∀ v, v ∈ A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)) ↔
      ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u := by
    intro v
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, z, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨a, ha, u, hu, by simp⟩
    · rintro ⟨a, ha, u, hu, rfl⟩
      exact ⟨a, ha, μ • u, ⟨u, hu, by simp⟩, rfl⟩
  have hfg : (A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))).FG := hA.sup (Λ.fg.map _)
  have htf : Module.IsTorsionFree O V := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r m h
    rw [← algebraMap_smul LL r m, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  refine ⟨⟨A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)), ?_, hfg, ?_, ?_⟩, hmem⟩
  · intro g x hx
    obtain ⟨a, ha, u, hu, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨ρ g a, hst g a ha, ρ g u, Λ.stable g u hu, ?_⟩
    rw [map_add (f := _), ← algebraMap_smul LL μ u, map_smul, algebraMap_smul]
  · haveI : Module.Finite O ↥(A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))) :=
      Module.Finite.iff_fg.2 hfg
    infer_instance
  · rw [eq_top_iff, ← Λ.span, Submodule.span_le]
    intro u hu
    have hne : algebraMap O LL μ ≠ 0 := fun h => hμ (hinj (by rw [h, map_zero]))
    have : u = (algebraMap O LL μ)⁻¹ • (μ • u) := by
      rw [← algebraMap_smul LL μ u, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hmem _).2 ⟨0, A.zero_mem, u, hu, by simp⟩))
end

section

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.isLocallyConstant_torsion_push_of_continuous :
    ∀ {G O LL Q : Type} [TopologicalSpace G] [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field LL] [TopologicalSpace LL]
      [IsTopologicalRing LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup Q] [Module O Q] {a n : ℕ}
      (Y : Submodule O (Fin a → Fin n → LL)) (φ : ↥Y →ₗ[O] Q) (u : G → Fin a → Fin n → LL) (hu : ∀ g, u g ∈ Y) (c : O),
      IsOpen (Set.range (algebraMap O LL)) → Continuous u → c ≠ 0 → (∀ y, c • φ y = 0) →
      IsLocallyConstant fun g => φ ⟨u g, hu g⟩ := by
  classical
  intro G O LL Q _ _ _ _ _ _ _ _ _ _ _ a n Y φ u hu c hopen hcont hc hkill
  let Lmap : (Fin a → Fin n → O) →ₗ[O] (Fin a → Fin n → LL) :=
    ((Algebra.linearMap O LL).compLeft (Fin n)).compLeft (Fin a)
  let Λ := LinearMap.range Lmap
  have hΛ : Λ.FG := by
    show (LinearMap.range Lmap).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  obtain ⟨μ, hμ0, hμ⟩ := admissible_lattices_commensurable (LL := LL) Λ Y hΛ c hc
  have hμL : algebraMap O LL μ ≠ 0 := fun h =>
    hμ0 ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
  let W : Set LL := (fun x => (algebraMap O LL μ)⁻¹ * x) ⁻¹' Set.range (algebraMap O LL)
  have hW : IsOpen W := hopen.preimage (continuous_const.mul continuous_id)
  let U : Set (Fin a → Fin n → LL) := {v | ∀ j m, v j m ∈ W}
  have hU : IsOpen U := by
    have hUe : U = ⋂ j, ⋂ m, (fun v : Fin a → Fin n → LL => v j m) ⁻¹' W := by
      ext v; simp [U]
    rw [hUe]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun m =>
      hW.preimage ((continuous_apply m).comp (continuous_apply j))
  have key : ∀ v ∈ Y, v ∈ U → ∃ y ∈ Y, v = c • y := by
    intro v hvY hvU
    simp only [U, W, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range] at hvU
    choose x hx using hvU
    have hxΛ : Lmap x ∈ Λ := LinearMap.mem_range_self _ _
    have hmul : μ • Lmap x = v := by
      funext j m
      show μ • algebraMap O LL (x j m) = v j m
      rw [Algebra.smul_def, hx j m, ← mul_assoc, mul_inv_cancel₀ hμL, one_mul]
    obtain ⟨y, hy, hyeq⟩ := hμ _ hxΛ (hmul ▸ hvY)
    exact ⟨y, hy, hmul ▸ hyeq⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have hnhds : {g | u g - u g0 ∈ U} ∈ nhds g0 := by
    refine (hU.preimage (hcont.sub continuous_const)).mem_nhds ?_
    intro j m
    refine ⟨0, ?_⟩
    simp
  filter_upwards [hnhds] with g hg
  obtain ⟨y, hy, hyeq⟩ := key _ (Y.sub_mem (hu g) (hu g0)) hg
  have hsplit : (⟨u g, hu g⟩ : Y) = ⟨u g0, hu g0⟩ + c • ⟨y, hy⟩ := by
    ext1
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [← hyeq]
    abel
  rw [hsplit, map_add (f := _), map_smul, hkill, add_zero]
end
