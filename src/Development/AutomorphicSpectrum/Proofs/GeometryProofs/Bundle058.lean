module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle046
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle012
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_eigen_field_extension : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp | exact GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_span_projection_bound : ∀ (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li), IsExtOver i ι → Submodule.span Ω (Set.range ι) = ⊤ → ∀ (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ) (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω) (m : Ω₀), Submodule.span W L = Submodule.span W (ι '' L₀) → (∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) → (∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j)) → (∀ j, m • b₀ j ∈ L₀) → (∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0) → (∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) → (∀ j, κ • b j ∈ L) → (∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) → (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧ ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Frames.two_frames | exact GlobalTheory.CompanionTheory.Ar.Frames.two_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Frames.two_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.normal_iso_of_integrally_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ), NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) → IsoAt ξ' f (RingHom.id Ω) p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed | exact GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed | (intros; apply GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.integral_closure_chart_span : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), (∀ c, x c ≠ 0 → Module.Finite (chRing o x c) (integralClosure (chRing o x c) Ω)) → ∃ (d n : ℕ) (z : κ ⊕ Fin n → Ω), (∀ c, z (Sum.inl c) = x c ^ d) ∧ ∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntClGens.exists_twisted_gens | exact GlobalTheory.CompanionTheory.Ar.IntClGens.exists_twisted_gens | (intros; apply GlobalTheory.CompanionTheory.Ar.IntClGens.exists_twisted_gens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.projective_model_nonempty : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), (∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v) → Nonempty (PModel o x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart | exact GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem join_points_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' :=
  @PositivityTheory.HtPt.Mb.join_charts

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem coh_vb_images_sums_multiples : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) :=
  @PositivityTheory.HtPt.Mc.coh_ops

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem frame_spread_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsCohOn T → p ∈ T → L.IsFrameAt b p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q :=
  PositivityTheory.HtPt.Mc.frame_spread

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.dominating_model_chart_compat : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ'), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') → (∀ c, x c ≠ 0 → y (e c) ≠ 0) → (∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p) → (∀ c, x c ≠ 0 → ∃ s : Finset Ω', ∀ a : Ω', a ∈ chRing o y (e c) ↔ a ∈ Submodule.span (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (s : Set Ω')) → IsFinite f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts | exact GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus

theorem exists_dense_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), M.ξ ≫ f = y₀ ≫ Y.j → ∃ U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens, Dense (U : Set ((pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}))) ∧ pullback.fst (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' (f ⁻¹' abLocus Y.t.G) = U := by
  intro E _ _ _ H D l Xo c Y Ω _ κ _ x M f y₀ hξ
  set π := spMap (algebraMap (𝓞 c.F) c.F) with hπ
  haveI : IsOpenImmersion Y.jQ := Y.jQ_open
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI hpre : IsPreimmersion π :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  haveI hfst : IsPreimmersion (pullback.fst (f ≫ Y.s) π) := inferInstance
  have hcond : (pullback.fst (f ≫ Y.s) π ≫ f) ≫ Y.s = pullback.snd (f ≫ Y.s) π ≫ π := by
    rw [Category.assoc, pullback.condition]
  set g := pullback.lift (pullback.fst (f ≫ Y.s) π ≫ f) (pullback.snd (f ≫ Y.s) π) hcond with hg
  have hgf : g ≫ pullback.fst Y.s π = pullback.fst (f ≫ Y.s) π ≫ f := pullback.lift_fst _ _ _
  have hpt : ∀ p, f (pullback.fst (f ≫ Y.s) π p) = pullback.fst Y.s π (g p) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgf]
  have hopen : IsOpen (g ⁻¹' Set.range Y.jQ) :=
    (IsOpenImmersion.isOpen_range Y.jQ).preimage g.continuous
  refine ⟨⟨g ⁻¹' Set.range Y.jQ, hopen⟩, ?_, ?_⟩
  · have hc2 : M.ξ ≫ f ≫ Y.s = (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) ≫ π := by
      rw [← Category.assoc, hξ]
      simp only [Model.j, Category.assoc, pullback.condition]
      rfl
    set ξ' := pullback.lift M.ξ (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) hc2 with hξ'
    have hξg : ξ' ≫ g = y₀ ≫ Y.jQ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hgf, ← Category.assoc, pullback.lift_fst, hξ]
        simp only [Model.j, Category.assoc]
        rfl
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc]
    set p0 := ξ' (IsLocalRing.closedPoint Ω) with hp0
    have hp0U : p0 ∈ g ⁻¹' Set.range Y.jQ := by
      refine ⟨y₀ (IsLocalRing.closedPoint Ω), ?_⟩
      have h := congrArg (fun (k : Spec (CommRingCat.of Ω) ⟶ pullback Y.s π) => k (IsLocalRing.closedPoint Ω)) hξg
      change g (ξ' (IsLocalRing.closedPoint Ω)) = Y.jQ (y₀ (IsLocalRing.closedPoint Ω)) at h
      exact h.symm
    have hp0M : pullback.fst (f ≫ Y.s) π p0 = genPt M.ξ := by
      have h := congrArg (fun (k : Spec (CommRingCat.of Ω) ⟶ M.X) => k (IsLocalRing.closedPoint Ω))
        (pullback.lift_fst M.ξ (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) hc2)
      change pullback.fst (f ≫ Y.s) π (ξ' (IsLocalRing.closedPoint Ω)) = M.ξ (IsLocalRing.closedPoint Ω) at h
      exact h
    have hemb := Scheme.Hom.isEmbedding (pullback.fst (f ≫ Y.s) π)
    intro p
    have hsp : p0 ⤳ p := by
      rw [← hemb.isInducing.specializes_iff, hp0M]
      exact M.all _
    exact closure_mono (Set.singleton_subset_iff.2 hp0U) (specializes_iff_mem_closure.1 hsp)
  · ext p
    simp only [Set.mem_preimage, TopologicalSpace.Opens.coe_mk]
    rw [hpt, ← Set.mem_preimage (f := pullback.fst Y.s π), Y.ab_gen]

end GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.bijective_logPeriods_T : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a), Function.Bijective (L.T i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij.T_bijective | exact GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij.T_bijective | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij.T_bijective <;> assumption)
end

section

open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.adapted_family_basis_change : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (lab : Ψ → Ψ ⊕ Ψ) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : Ψ → Fin k → A.Λ) (bL : Ψ → Fin m → V) (T : Ψ → Matrix (Fin m) (Fin m) L), IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ (e : L →+* ℂ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) → Function.Injective j → ∀ (ρ' : 𝓞 E →+* Module.End ℂ V'), (∀ a x, ρ' a (j x) = j (A.ρ a x)) → (∀ τ a, eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a)) = j (eigComp A.ρ (A.σ (lab τ)) (v a))) → ∀ hb : V' → V' → ℂ, (∀ τ c c', hb (j (q τ c)) (j (q τ c')) = (A.Bq.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c)) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] A.f (q τ c'))) → PhiNormSq ρ' hb (A.I.map j) (4 * Real.pi)⁻¹ (fun τ => e.comp (A.σ (lab τ))) (fun τ i => j (bL τ i)) ((((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange.phiNormSq_baseChange | exact GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange.phiNormSq_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange.phiNormSq_baseChange <;> assumption)
end
