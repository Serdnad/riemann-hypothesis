module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle014
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle013

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isIntegral_of_densePart {T U : Scheme.{0}} (j : U ⟶ T) [IsIntegral T]
    [GlobalTheory.IsNormalScheme T] [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsIntegral U := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j
  have : GlobalTheory.IsNormalScheme U := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j
  have hη : genericPoint T ∈ genericPoints T := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  have hgen : IsGenericPoint u (Set.univ : Set U) := by
    rw [isGenericPoint_iff_specializes]
    refine fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hu]
    exact (genericPoint_spec T).specializes trivial
  have : IrreducibleSpace U := by
    rw [irreducibleSpace_def]
    exact hgen.isIrreducible
  exact GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace U

theorem existsUnique_lift_of_densePart : ∀ (T U X Y : Scheme.{0}) [IsLocallyNoetherian T] (j : U ⟶ T), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (q : Y ⟶ X) (f : T ⟶ X) (g : U ⟶ Y), IsIntegralHom q → g ≫ q = j ≫ f → ∃! h : T ⟶ Y, j ≫ h = g ∧ h ≫ q = f := by
  intro T U Y Z _ j hT _ _ _ _ p b a _ h
  have := GlobalTheory.IsNormalScheme.of_pred hT
  have H (W : irreducibleComponents T) := by
    have : IsDominant (j ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j› _
    have : IsIntegral (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).toScheme :=
      isIntegral_of_densePart (j ∣_ GlobalTheory.IsNormalScheme.component W)
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ∣_ GlobalTheory.IsNormalScheme.component W)
    exact existsUnique_lift_of_birational (j ∣_ GlobalTheory.IsNormalScheme.component W) p
      ((j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ a) ((GlobalTheory.IsNormalScheme.component W).ι ≫ b)
      (by rw [Category.assoc, h, morphismRestrict_ι_assoc])
  choose c hc _ using H
  obtain ⟨hT⟩ := GlobalTheory.IsNormalScheme.nonempty_isColimit_component (X := T)
  let c₀ : T ⟶ Z := Cofan.IsColimit.desc hT c
  have hc₀ (W) : (GlobalTheory.IsNormalScheme.component W).ι ≫ c₀ = c W := Cofan.IsColimit.fac hT c W
  have h₂ : c₀ ≫ p = b := Cofan.IsColimit.hom_ext hT _ _ fun W ↦ by
    change (GlobalTheory.IsNormalScheme.component W).ι ≫ _ = (GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [reassoc_of% hc₀ W, (hc W).2]
  have h₁ : j ≫ c₀ = a := by
    refine Scheme.Cover.hom_ext (U.openCoverOfIsOpenCover _
      (.comap (GlobalTheory.IsNormalScheme.iSup_component T) j.base.1)) _ _ fun W ↦ ?_
    change (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _ =
      (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [← morphismRestrict_ι_assoc, hc₀ W, (hc W).1]
  exact ⟨c₀, ⟨h₁, h₂⟩, fun c' hc' ↦
    lift_unique_of_isDominant j p (hc'.1.trans h₁.symm) (hc'.2.trans h₂.symm)⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_existsUnique_comp_eq :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (T : Scheme.{0}) (f : X ⟶ T), (∀ g, (ρ g).asIso.hom ≫ f = f) → ∃! f' : X' ⟶ T, π ≫ f' = f := by
  intro Γ _ _ X X' ρ π ⟨hπ, hinv, hV⟩ T f hf

  have hq : IsAffineQuotient ρ π :=
    { comp_eq := hinv
      isAffineHom := hπ
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (fun g _ => by obtain ⟨_, e⟩ := hs g; exact e) }
  exact hq.existsUnique_comp_eq f hf

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_isReduced_isNormal_flat :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X → IsReduced X') ∧ (IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') ∧ ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (s' : X' ⟶ Sp R), Flat (π ≫ s') → Flat s' := by
  rintro Γ _ _ X X' ρ π ⟨_, hπ, hV⟩
  have h : IsAffineQuotient ρ π :=
    ⟨hπ, ‹_›, fun W ↦ (hV W).1, fun W s hs ↦ (hV W).2 s fun g _ ↦ (hs g).2⟩
  refine ⟨fun _ ↦ h.isReduced, fun _ hN ↦ ?_, fun R _ _ s' _ ↦ ?_⟩
  · have := IsNormalScheme.of_pred hN
    have := h.isNormalScheme
    exact IsNormalScheme.pred X'
  · have := h.isSchemeTheoreticallyDominant
    exact flat_of_isSchemeTheoreticallyDominant
      (fun _ _ _ h ↦ IsDedekindDomain.flat_iff_torsion_eq_bot.mpr h) π s'

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_action_of_isPullback {Γ : Type} [Group Γ] {X X' Y Y' : Scheme.{0}}
    (ρ : Γ →* Aut X) {π : X ⟶ X'} {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'}
    (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π) (H : IsPullback p φ π p') :
    ∃ τ : Γ →* Aut Y, ∀ g,
      (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom := by
  have hc : ∀ g : Γ, (p ≫ (ρ g).asIso.hom) ≫ π = φ ≫ p' := fun g => by
    rw [Category.assoc, hπ g, H.w]
  let e : Γ → (Y ⟶ Y) := fun g => H.lift (p ≫ (ρ g).asIso.hom) φ (hc g)
  have e_p : ∀ g, e g ≫ p = p ≫ (ρ g).asIso.hom := fun g => H.lift_fst _ _ _
  have e_φ : ∀ g, e g ≫ φ = φ := fun g => H.lift_snd _ _ _
  have e_one : e 1 = 𝟙 Y := H.hom_ext
    (by rw [e_p, map_one]; exact (Category.comp_id p).trans (Category.id_comp p).symm)
    (by rw [e_φ, Category.id_comp])
  have e_mul : ∀ g h, e (g * h) = e h ≫ e g := fun g h => H.hom_ext
    (by
      rw [e_p, Category.assoc, e_p, ← Category.assoc, e_p, Category.assoc, map_mul]
      rfl)
    (by rw [e_φ, Category.assoc, e_φ, e_φ])
  let τf : Γ → Aut Y := fun g => Aut.of
    { hom := e g
      inv := e g⁻¹
      hom_inv_id := by rw [← e_mul, inv_mul_cancel, e_one]
      inv_hom_id := by rw [← e_mul, mul_inv_cancel, e_one] }
  refine ⟨{ toFun := τf, map_one' := ?_, map_mul' := ?_ }, fun g => ⟨e_φ g, e_p g⟩⟩
  · exact Aut.ext (Iso.ext e_one)
  · intro g h
    exact Aut.ext (Iso.ext (e_mul g h))

theorem quotient_flat_baseChange :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) (ρ : Γ →* Aut X)
      (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'),
      (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧
        ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
          (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)),
            ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) →
      IsPullback φ p p' π → Flat p' →
      (∃ τ : Γ →* Aut Y, ∀ g,
        (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) ∧
      ∀ τ : Γ →* Aut Y,
        (∀ g, (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) →
        (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧
          ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
            (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)),
              ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) := by
  intro Γ _ _ X X' Y Y' ρ π φ p p' hq H hflat
  obtain ⟨hπa, hπ, hV⟩ := hq
  refine ⟨exists_action_of_isPullback ρ hπ H.flip, fun τ hτ => ?_⟩
  have hQ : IsAffineQuotient ρ π :=
    { comp_eq := hπ
      isAffineHom := hπa
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (by
        unfold IsInvariantSection at hs
        intro g h
        obtain ⟨_, e⟩ := hs g
        exact e) }
  have := hflat
  have hB := hQ.of_isPullback H.flip (fun g => (hτ g).2) (fun g => (hτ g).1)
  exact ⟨hB.isAffineHom, hB.comp_eq, fun V => ⟨hB.app_injective V, fun f hf => hB.mem_range_app V f (by
    unfold IsInvariantSection
    intro g
    have hle : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ φ ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, (hτ g).1]
    exact ⟨hle, hf g hle⟩)⟩⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_isFinite_locallyOfFiniteType_descend :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s' : X' ⟶ S), LocallyOfFiniteType (π ≫ s') → IsFinite π ∧ LocallyOfFiniteType s' ∧ (QuasiCompact (π ≫ s') → QuasiCompact s') ∧ (IsSeparated (π ≫ s') → IsSeparated s') ∧ (IsProper (π ≫ s') → IsProper s') := by
  intro G _ _ X X' ρ π hπ S _ s' hft
  obtain ⟨hA, hc, hV⟩ := hπ
  have hq : IsAffineQuotient ρ π :=
    { comp_eq := hc
      isAffineHom := hA
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (by
        intro g hg
        unfold IsInvariantSection at hs
        obtain ⟨_, e⟩ := hs g
        exact e) }
  exact ⟨hq.isFinite s', hq.locallyOfFiniteType s',
    fun _ => hq.quasiCompact s', fun _ => hq.isSeparated s', fun _ => hq.isProper s'⟩

end GlobalTheory
end

section

open Filter Metric Set
open scoped Topology

namespace GlobalTheory.ThetaFamily

theorem exists_quotient_closure {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] {W : Set (V × V')}
    {f θ : V × V' → ℂ} (hW : IsOpen W) (hf : DifferentiableOn ℂ f W) (hθ : DifferentiableOn ℂ θ W) {S : Set V}
    (hS : ∀ b ∈ S, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W} ∧ ∀ z, (b, z) ∈ W → F z * θ (b, z) = f (b, z))
    {w : V × V'} (hw : w ∈ W) (hfr : ∃ᶠ z in 𝓝 w.2, θ (w.1, z) ≠ 0) :
    ∃ (U : Set (V × V')) (G : V × V' → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ W ∧ DifferentiableOn ℂ G U ∧
      ∀ y ∈ U, y.1 ∈ closure S → G y * θ y = f y := by
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) hfr
  let p : V × V' → ℂ → V × V' := fun y t => (y.1, y.2 + t • v)
  have hp : Continuous fun q : (V × V') × ℂ => p q.1 q.2 := by fun_prop
  have h1 : ∀ᶠ y in 𝓝 w, ∀ t ∈ closedBall (0 : ℂ) r, p y t ∈ W :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht =>
      hp.continuousAt.eventually (hW.mem_nhds (hin t ht))
  have h2 : ∀ᶠ y in 𝓝 w, ∀ t ∈ sphere (0 : ℂ) r, θ (p y t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => by
      have hc : ContinuousAt θ (p w t) :=
        (hθ.differentiableAt (hW.mem_nhds (hin t (sphere_subset_closedBall ht)))).continuousAt
      exact (ContinuousAt.comp (g := θ) (f := fun q : (V × V') × ℂ => p q.1 q.2) (x := (w, t))
        hc hp.continuousAt).eventually_ne (hne t ht)
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.1 (h1.and h2)
  have hp0 : ∀ y, p y 0 = y := fun y => by simp [p]
  have hUW : U ⊆ W := fun y hy => hp0 y ▸ (hU y hy).1 0 (mem_closedBall_self hr.le)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · obtain ⟨G, hGd, hEq⟩ : ∃ G : V × V' → ℂ, DifferentiableOn ℂ G U ∧ ∀ y ∈ U, y.1 ∈ S → G y * θ y = f y := by
      refine ⟨fun y => ((2 * Real.pi)⁻¹ : ℝ) • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)), hG.const_smul ((2 * Real.pi)⁻¹ : ℝ), fun y hy hyS => ?_⟩
      obtain ⟨F, hFd, hF⟩ := hS _ hyS
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (y.2 + t • v)) (closedBall 0 r) :=
        hFd.comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (y.2 + t • v)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def, zero_smul, add_zero] at hav
      rw [← hF y.2 (hUW hy), ← hav]
      beta_reduce
      congr 2
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      show _ / _ = _
      rw [div_eq_iff ((hU y hy).2 _ hs)]
      exact (hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))).symm
    refine ⟨U, G, hUo, hwU, hUW, hGd, fun y hy hyS => ?_⟩
    have hc : Continuous fun b : V => (b, y.2) := by fun_prop
    have c1 : ContinuousAt (fun b : V => G (b, y.2) * θ (b, y.2)) y.1 :=
      ContinuousAt.comp (g := fun q => G q * θ q) (f := fun b : V => (b, y.2)) (x := y.1)
        ((hGd.mul (hθ.mono hUW)).differentiableAt (hUo.mem_nhds hy)).continuousAt hc.continuousAt
    have c2 : ContinuousAt (fun b : V => f (b, y.2)) y.1 :=
      ContinuousAt.comp (g := f) (f := fun b : V => (b, y.2)) (x := y.1)
        (hf.differentiableAt (hW.mem_nhds (hUW hy))).continuousAt hc.continuousAt
    have hev : ∀ᶠ b in 𝓝 y.1, (b, y.2) ∈ U := hc.continuousAt.eventually (hUo.mem_nhds hy)
    exact tendsto_nhds_unique_of_frequently_eq c1 c2
      (((mem_closure_iff_frequently.1 hyS).and_eventually hev).mono fun b hb => hEq _ hb.2 hb.1)
  · have hq : Continuous fun q : ℝ × (V × V') => p q.2 (circleMap 0 r q.1) :=
      hp.comp (f := fun q : ℝ × (V × V') => (q.2, circleMap 0 r q.1)) (by fun_prop)
    have hm : ∀ q : ℝ × (V × V'), q ∈ uIcc 0 (2 * Real.pi) ×ˢ U →
        p q.2 (circleMap 0 r q.1) ∈ W := fun q hq =>
      (hU _ hq.2).1 _ (sphere_subset_closedBall (hcm _))
    exact (hf.continuousOn.comp hq.continuousOn hm).div
      (hθ.continuousOn.comp hq.continuousOn hm) fun q hq => (hU _ hq.2).2 _ (hcm _)
  · intro s _
    have hq : Differentiable ℂ fun y : V × V' => p y (circleMap 0 r s) := by fun_prop
    have hm : ∀ y ∈ U, p y (circleMap 0 r s) ∈ W := fun y hy =>
      (hU _ hy).1 _ (sphere_subset_closedBall (hcm _))
    simp only [div_eq_mul_inv]
    exact (hf.comp hq.differentiableOn hm).mul
      ((hθ.comp hq.differentiableOn hm).inv fun y hy => (hU _ hy).2 _ (hcm _))

theorem exists_entire_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {θ θ' : E → ℂ}
    (hfr : ∀ z, ∃ᶠ w in 𝓝 z, θ' w ≠ 0)
    (h : ∀ z, ∃ ρ : E → ℂ, ρ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ' w = θ w) :
    ∃ ρ : E → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ z, ρ z * θ' z = θ z := by
  choose ρ h0 h using h
  refine ⟨fun z => ρ z z, fun z => ?_, h0, fun z => (h z).self_of_nhds.2⟩
  refine (h z).self_of_nhds.1.congr_of_eventuallyEq ?_
  filter_upwards [(h z).eventually_nhds] with w hw
  refine tendsto_nhds_unique_of_frequently_eq (h w).self_of_nhds.1.continuousAt hw.self_of_nhds.1.continuousAt ?_
  exact (((hfr w).and_eventually (h w)).and_eventually hw).mono fun u hu =>
    mul_right_cancel₀ hu.1.1 (hu.1.2.2.trans hu.2.2.symm)

theorem eq_of_finite_of_closed_fibres {X Y : Type*} [TopologicalSpace X] {B : Set X} (hB : IsPreconnected B)
    {C : Set Y} (hC : C.Finite) (c : X → Y) (hc : ∀ b ∈ B, c b ∈ C)
    (h : ∀ k ∈ C, ∀ b ∈ B, b ∈ closure {b' ∈ B | c b' = k} → c b = k) : ∀ b ∈ B, ∀ b' ∈ B, c b = c b' := by
  have : PreconnectedSpace B := Subtype.preconnectedSpace hB
  have hl : IsLocallyConstant fun b : B => c b := fun s => by
    have e : ((fun b : B => c b) ⁻¹' s)ᶜ = ⋃ k ∈ C \ s, (Subtype.val ⁻¹' closure {b' ∈ B | c b' = k} : Set B) := by
      ext b
      simp only [mem_compl_iff, mem_preimage, mem_iUnion, mem_diff, exists_prop]
      exact ⟨fun hb => ⟨c b, ⟨hc b b.2, hb⟩, subset_closure ⟨b.2, rfl⟩⟩,
        fun ⟨k, hk, hb⟩ => (h k hk.1 b b.2 hb).symm ▸ hk.2⟩
    rw [← isClosed_compl_iff, e]
    exact (hC.subset diff_subset).isClosed_biUnion fun k _ => isClosed_closure.preimage continuous_subtype_val
  exact fun b hb b' hb' => hl.apply_eq_of_preconnectedSpace ⟨b, hb⟩ ⟨b', hb'⟩

theorem frequently_ne_zero_of_entire {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {θ : E → ℂ} (hd : Differentiable ℂ θ) (h0 : θ ≠ 0) (z : E) : ∃ᶠ w in 𝓝 z, θ w ≠ 0 := by
  intro h
  refine h0 (funext fun w => ?_)
  exact (SCV.analyticOnNhd_of_differentiable hd univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ z) (h.mono fun _ hu => not_not.1 hu) (mem_univ w)

theorem differentiableOn_left_inverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : Type} [Fintype n]
    [DecidableEq n] {B : Set V} {M h : V → Matrix n n ℂ} (hM : ∀ i j, DifferentiableOn ℂ (fun b => M b i j) B)
    (hh : ∀ b ∈ B, h b * M b = 1) (i j : n) : DifferentiableOn ℂ (fun b => h b i j) B := by
  have hdet : ∀ {N : V → Matrix n n ℂ}, (∀ i j, DifferentiableOn ℂ (fun b => N b i j) B) →
      DifferentiableOn ℂ (fun b => (N b).det) B := fun {N} hN => by
    exact ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of (F := fun i j b => N b i j) hN
  have hne : ∀ b ∈ B, (M b).det ≠ 0 := fun b hb => (Matrix.isUnit_det_of_left_inverse (hh b hb)).ne_zero
  refine (((hdet hM).inv hne).mul (hdet (N := fun b => (M b).updateRow j (Pi.single i 1)) fun k l => ?_)).congr
    fun b hb => ?_
  · by_cases hk : k = j
    · simp only [hk, Matrix.updateRow_self]; exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hk]; exact hM k l
  · rw [← Matrix.inv_eq_left_inv (hh b hb), Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply,
      Ring.inverse_eq_inv', smul_eq_mul]
    rfl

end GlobalTheory.ThetaFamily
end

section

open scoped TensorProduct
theorem _root_.GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace : ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by
  first | exact @GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace | exact GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace | (intros; apply GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace <;> assumption)
end

section

open scoped TensorProduct
theorem _root_.GlobalTheory.T.exists_integral_of_local_presentation_pow : ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  first | exact @GlobalTheory.exists_integral_of_local_presentation | exact GlobalTheory.exists_integral_of_local_presentation | (intros; apply GlobalTheory.exists_integral_of_local_presentation <;> assumption)
end
