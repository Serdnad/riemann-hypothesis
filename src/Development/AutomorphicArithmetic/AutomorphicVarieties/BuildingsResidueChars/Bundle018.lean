module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NnDefs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle005
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem adjoin_alg {V : Type} [AddCommGroup V] [Module ℂ V] {R : Type} [CommRing R] [Algebra ℂ R]
    (φ : R →ₐ[ℂ] Module.End ℂ V) (S : Submodule ℂ V) (t : Set R) (ht : ∀ r ∈ t, AlgMod S ⊥ (φ r)) :
    ∀ r ∈ Algebra.adjoin ℂ t, AlgMod S ⊥ (φ r) := by
  let I : Ideal R :=
    { carrier := {r | ∀ x ∈ S, φ r x = 0}
      add_mem' := fun {a b} ha hb x hx => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), LinearMap.add_apply, ha x hx, hb x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c r hr x hx => by
        simp only [Set.mem_setOf_eq] at hr ⊢
        rw [smul_eq_mul, map_mul, Module.End.mul_apply, hr x hx, map_zero] }
  have hint : ∀ r ∈ t, IsIntegral ℂ (Ideal.Quotient.mkₐ ℂ I r) := by
    intro r hr
    obtain ⟨p, hp, hx⟩ := ht r hr
    refine ⟨p, hp, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    intro x hxS
    have hx' := hx x hxS
    rw [Polynomial.aeval_algHom_apply, Submodule.mem_bot] at hx'
    exact hx'
  intro r hr
  have h1 : Ideal.Quotient.mkₐ ℂ I r ∈ Algebra.adjoin ℂ (Ideal.Quotient.mkₐ ℂ I '' t) := by
    rw [Algebra.adjoin_image]
    exact ⟨r, hr, rfl⟩
  have h2 : Ideal.Quotient.mkₐ ℂ I r ∈ integralClosure ℂ (R ⧸ I) := by
    refine Algebra.adjoin_le ?_ h1
    rintro _ ⟨r', hr', rfl⟩
    exact hint r' hr'
  obtain ⟨p, hp, hev⟩ := h2
  refine ⟨p, hp, fun x hx => ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hev
  rw [Polynomial.aeval_algHom_apply, Submodule.mem_bot]
  exact hev x hx

theorem UpperTheory.algMod_bot_of_mem_adjoin_commuting :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (s : Set (Module.End ℂ M)), (∀ x ∈ s, ∀ y ∈ s, x * y = y * x) → (∀ T ∈ s, AlgMod S ⊥ T) → ∀ T ∈ Algebra.adjoin ℂ s, AlgMod S ⊥ T := by
  intro M _ _ S s hcomm hs T hT
  letI : IsMulCommutative (Algebra.adjoin ℂ s) :=
    Algebra.isMulCommutative_adjoin ℂ (fun x hx y hy _ => hcomm x hx y hy)
  open scoped IsMulCommutative in
    have hmem : (⟨T, hT⟩ : Algebra.adjoin ℂ s) ∈
        Algebra.adjoin ℂ (((↑) : Algebra.adjoin ℂ s → Module.End ℂ M) ⁻¹' s) := by
      rw [Algebra.adjoin_adjoin_coe_preimage]
      trivial
    exact adjoin_alg (Algebra.adjoin ℂ s).val S
      (((↑) : Algebra.adjoin ℂ s → Module.End ℂ M) ⁻¹' s)
      (fun r hr => hs r hr) ⟨T, hT⟩ hmem
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Ws

theorem UpperTheory.exists_mem_pins_insert_ker_of_padic_character :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (I : Subgroup G), IsClosed (I : Set G) → ∀ ε : G →* ℤ_[l]ˣ, Continuous ε → ∃ s ∈ I, Pins l I (insert s {g | g ∈ I ∧ ε g = 1}) := by
  intro l _ hl G _ _ _ _ I hI ε hε
  have hclo : ∀ K : Subgroup G, IsClosed (K : Set G) →
      IsClosed ((K.map ε : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    intro K hK
    rw [Subgroup.coe_map]
    exact (hK.isCompact.image hε).isClosed
  obtain ⟨γ, hγ, hV⟩ := UpperTheory.V.Kum.existsGen l (I.map ε) (hclo I hI) (Or.inl hl)
  obtain ⟨s, hsI, rfl⟩ := Subgroup.mem_map.mp hγ
  refine ⟨s, hsI, ?_⟩
  intro R _ _ _ _ _ ψ hψ _ hS g hg
  have hK : IsClosed ((ψ.ker ⊓ I : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_ker_of_adicCont ψ hψ).inter hI
  have hsK : s ∈ ψ.ker ⊓ I :=
    Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr (hS s (Set.mem_insert _ _)), hsI⟩
  have hle : I.map ε ≤ (ψ.ker ⊓ I).map ε := by
    refine hV.trans (Subgroup.topologicalClosure_minimal _ ?_ (hclo _ hK))
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map_of_mem _ hsK
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map_of_mem ε hg))
  have hk' := Subgroup.mem_inf.mp hk
  have h1 : ψ (g * k⁻¹) = 1 :=
    hS _ (Set.mem_insert_of_mem _ ⟨I.mul_mem hg (I.inv_mem hk'.2), by simp [hkg]⟩)
  have hk1 : ψ k = 1 := MonoidHom.mem_ker.mp hk'.1
  simpa [hk1] using h1
end
