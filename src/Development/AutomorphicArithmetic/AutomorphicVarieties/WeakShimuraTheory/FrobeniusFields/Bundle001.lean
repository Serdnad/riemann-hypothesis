module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.fixAb :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ H → ∃ (F : IntermediateField ℚ Ω) (_ : NumberField F) (_ : IsAbelianGalois ℚ F), F.fixingSubgroup = H ∧ Module.finrank ℚ F = H.index := by
  intro Ω _ _ hc V hV hcomm
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hcl : IsClosed (V : Set (Ω ≃ₐ[ℚ] Ω)) := Subgroup.isClosed_of_isOpen V hV
  set L : IntermediateField ℚ Ω := IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[ℚ] Ω)) with hL
  have hfix : L.fixingSubgroup = V := InfiniteGalois.fixingSubgroup_fixedField ⟨V, hcl⟩
  have hnorm : V.Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ * n⁻¹ ∈ V :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have := mul_mem h hn
    rwa [inv_mul_cancel_right] at this⟩
  haveI hfin : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hfix]; exact hV)
  haveI hgal : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hfix]; exact hnorm)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker = V :=
    (@IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ L hgal.to_normal).trans hfix
  have hab : IsAbelianGalois ℚ L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := hsurj a
        obtain ⟨b, rfl⟩ := hsurj b
        have h : a * b * a⁻¹ * b⁻¹ ∈ V :=
          hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
          mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        exact h⟩ }
  have hnf : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  refine ⟨L, hnf, hab, hfix, ?_⟩
  exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω L).trans (congrArg Subgroup.index hfix)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ext_cc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω)
    (φ : F →+* ℂ) :
    ∃ (σ : G ℚ Ω) (j : Ω →+* ℂ), (∀ x, j (σ x) = starRingEnd ℂ (j x)) ∧ ∀ x : F, j x = φ x := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : F, j x = φ x := by
    letI : Algebra F ℂ := φ.toAlgebra
    let j : Ω →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    exact ⟨j.toRingHom, fun x => j.commutes x⟩
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.toRatAlgHom.commutes x).symm
  let cj : Ω →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp j).toRatAlgHom
  exact ⟨cj.restrictNormal' Ω, j, fun x => AlgHom.restrictNormal_commutes cj Ω x, hj⟩

theorem UpperTheory.V.Ws.fixInf :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F], ((∀ σ : G ℚ Ω, IsCC σ → σ ∈ F.fixingSubgroup) → IsTotallyReal F) ∧ ((∀ σ : G ℚ Ω, IsCC σ → σ ∉ F.fixingSubgroup) → Module.finrank ℚ F = 2 → IsCMField F) := by
  intro Ω _ _ _ F _
  refine ⟨fun h => ⟨fun w => ?_⟩, fun h h2 => ?_⟩
  · obtain ⟨σ, j, hσ, hj⟩ := ext_cc F w.embedding
    have hm := (F.mem_fixingSubgroup_iff σ).1 (h σ ⟨j, hσ⟩)
    refine InfinitePlace.isReal_iff.2 (RingHom.ext fun x => ?_)
    show starRingEnd ℂ (w.embedding x) = w.embedding x
    rw [← hj, ← hσ, hm x.1 x.2]
  · haveI : IsTotallyComplex F := ⟨fun w => by
      rw [← InfinitePlace.not_isReal_iff_isComplex]
      intro hw
      obtain ⟨σ, j, hσ, hj⟩ := ext_cc F w.embedding
      refine h σ ⟨j, hσ⟩ ((F.mem_fixingSubgroup_iff σ).2 fun x hx => j.injective ?_)
      have e : starRingEnd ℂ (w.embedding ⟨x, hx⟩) = w.embedding ⟨x, hx⟩ :=
        RingHom.congr_fun (InfinitePlace.isReal_iff.1 hw) ⟨x, hx⟩
      rw [← hj] at e
      rw [hσ]; exact e⟩
    haveI : Algebra.IsQuadraticExtension ℚ F := ⟨h2⟩
    exact IsCMField.ofCMExtension ℚ F
end
