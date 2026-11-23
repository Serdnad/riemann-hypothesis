module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.characterLatticeAtFibre_const_preconnected : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y : RatModel o Ω) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Z : Scheme.{0}) (q : Y.Z ⟶ Z) (z : Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → (∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt G w r₀) → ∀ (I T : Type) (f : I → (G ⟶ G)), (∀ e, IsMonHom (f e)) → ∀ (gγ : T → (Over.mk Y.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ t, gγ t ^ L = 1) → (∀ t w, q.base w = z → ExtNear (gγ t) w) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w w' : Y.Z), q.base w = z → q.base w' = z → LatAt f gγ ζ L m c w → LatAt f gγ ζ L m c w' := by
  first | exact @GlobalTheory.UPoinc.GFib.latAt_const_on_fibre | exact GlobalTheory.UPoinc.GFib.latAt_const_on_fibre | (intros; apply GlobalTheory.UPoinc.GFib.latAt_const_on_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GenericRatio

theorem exists_complete_point (T : Scheme.{0}) [IsLocallyNoetherian T] (t : T) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B), IsAdicComplete (maximalIdeal B) B ∧
      ∃ q : Sp B ⟶ T, Flat q ∧ q (closedPoint B) = t := by
  let O : Type := T.presheaf.stalk t
  have : IsNoetherianRing O := inferInstanceAs (IsNoetherianRing (T.presheaf.stalk t))
  refine ⟨AdicCompletion (maximalIdeal O) O, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O))) ≫ T.fromSpecStalk t, ?_, ?_⟩
  · have h1 : Flat (T.fromSpecStalk t) := GenericExt.flat_fromSpecStalk T t
    have h2 : Flat (Spec.map (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    exact Flat.comp _ _
  · have : IsLocalHom (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O))).hom :=
      inferInstanceAs (IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)))
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (T.fromSpecStalk t) Spec_closedPoint).trans
      Scheme.fromSpecStalk_closedPoint)

theorem secRatioEq_of_levels {B : Type} [CommRing B] [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {k k' : ℕ} {u v : Sp B ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'}
    (h : ∀ e, SecRatioEq L (thick B (maximalIdeal B) e ≫ u) (thick B (maximalIdeal B) e ≫ v) s₁ s₂ t₁ t₂) :
    SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  have top : ∀ w : Sp B ⟶ X, ∃ i : Fin 1 → L.ι, ⊤ ≤ w ⁻¹ᵁ secChart L i := fun w => by
    obtain ⟨i, hi⟩ := exists_chart hL (w (closedPoint B))
    have : closedPoint B ∈ w ⁻¹ᵁ secChart L (fun _ => i) := Set.mem_iInter.2 fun _ => hi
    exact ⟨fun _ => i, ((IsLocalRing.closedPoint_mem_iff _).1 this).ge⟩
  obtain ⟨i, hi⟩ := top u
  obtain ⟨i', hi'⟩ := top v
  have key : ∀ (s : H0 L k) (t : H0 L k') (Z : Scheme.{0}) (r : Z ⟶ Sp B) (z : Z),
      gs r z ⊤ ((u.appLE _ ⊤ hi).hom (s.f i) * (v.appLE _ ⊤ hi').hom (t.f i')) =
        secGerm (r ≫ u) z s i * secGerm (r ≫ v) z t i' := fun s t Z r z =>
    (gs_mul r z ⊤ trivial _ _).trans (congrArg₂ (· * ·) (gs_appLE u _ ⊤ hi r z trivial _)
      (gs_appLE v _ ⊤ hi' r z trivial _))
  have E := GlobalTheory.FormalGeneric.fn_ext_germs (maximalIdeal B) (a := (u.appLE _ ⊤ hi).hom (s₁.f i) *
      (v.appLE _ ⊤ hi').hom (t₂.f i')) (b := (u.appLE _ ⊤ hi).hom (s₂.f i) * (v.appLE _ ⊤ hi').hom (t₁.f i'))
    fun e z => (key _ _ _ _ z).trans ((secRatioEq_iff_germ.1 (h e) z i i' (hi trivial) (hi' trivial)).trans
      (key _ _ _ _ z).symm)
  refine secRatioEq_of_exists_germ fun y => ⟨i, i', hi trivial, hi' trivial, ?_⟩
  exact (key s₁ t₂ _ (𝟙 _) y).symm.trans ((congrArg _ E).trans (key s₂ t₁ _ (𝟙 _) y))

theorem exists_generic_mem {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) [Flat f]
    (W : Y.Opens) {y : Y} (hy : y ∈ W) : ∃ a : (pullback f (jK R) :), pullback.fst f (jK R) a ∈ W := by
  let ξ : Sp R := jK R (closedPoint (FractionRing R))
  have hξ : ξ ⤳ f y := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
    have h1 : algebraMap R (FractionRing R) r ∈ maximalIdeal (FractionRing R) := hr
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot,
      map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    rw [h1]
    exact Ideal.zero_mem _
  obtain ⟨y', h1, h2⟩ := Flat.generalizingMap f hξ
  have : y' ∈ Set.range (pullback.fst f (jK R)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨_, h2.symm⟩
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha ▸ h1.mem_open W.isOpen hy⟩

theorem isDominant_of_flat {X Y : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [Flat f] (y : Y) : IsDominant f := by
  obtain ⟨y', -, h2⟩ := Flat.generalizingMap f (genericPoint_specializes (f y))
  refine ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨y', h2⟩) ?_⟩
  exact dense_iff_closure_eq.2 (genericPoint_spec X)

theorem exists_formal_pair {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G] [LocallyOfFiniteType G.hom]
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (hb : ∀ e, IsMonHom (b e))
    (hc : ∀ e, thickMap R (maximalIdeal R) e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R (maximalIdeal R) e G)
    {L : LB G.left} (hL : L.IsLB) :
    ∃ (Y : Over (Sp R)) (x₁ x₂ : Y ⟶ G) (Φ : (Y ⟶ G) → (Y ⟶ G)), Nonempty Y.left ∧ Flat (lift x₁ x₂).left ∧
      (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Y ⟶ G) (k k' : ℕ) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'),
        (∀ e, SecRatioEq L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left
          s₁ s₂ t₁ t₂) → SecRatioEq L (Φ x).left x.left s₁ s₂ t₁ t₂ := by
  have : LocallyOfFiniteType (G ⊗ G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom))
  have : IsLocallyNoetherian (G ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (G ⊗ G).hom
  let o : 𝟙_ (Over (Sp R)) ⟶ G ⊗ G := lift 1 1
  obtain ⟨B, _, _, hB, q, hq, hqt⟩ := exists_complete_point (G ⊗ G).left (o.left (closedPoint R))
  have hs : (q ≫ (G ⊗ G).hom) (closedPoint B) ∈ Set.range (thick R (maximalIdeal R) 0) := by
    have h1 : (q ≫ (G ⊗ G).hom) (closedPoint B) = closedPoint R :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (G ⊗ G).hom hqt).trans
        ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun g => g (closedPoint R)) (Over.w o))))
    exact ⟨_, (GlobalTheory.adicLevelι_closedPoint (maximalIdeal.isMaximal R).ne_top 0).trans h1.symm⟩
  obtain ⟨Φ, hΦ, hr⟩ := GlobalTheory.T.exists_additive_action_thickeningEndos_completePoints R (maximalIdeal R) G b hb hc B (q ≫ (G ⊗ G).hom) hs
  let q' : Over.mk (q ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk q rfl
  refine ⟨Over.mk (q ≫ (G ⊗ G).hom), q' ≫ fst G G, q' ≫ snd G G, Φ, ⟨closedPoint B⟩, ?_, hΦ,
    fun x k k' s₁ s₂ t₁ t₂ h => secRatioEq_of_levels hL fun e => ?_⟩
  · rw [lift_comp_fst_snd]
    exact hq
  · obtain ⟨r, h1, h2⟩ := hr x e
    have h3 := (h e).comp r
    exact h1 ▸ h2 ▸ h3

theorem exists_generic_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), 1 ≤ N → (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∃ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ ∧ (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' _ b hb N S _ hS hnd
  have := hR.1.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  let F := Over.pullback (jK R)
  letI : F.Monoidal := (Over.instBraidedPullback (f := jK R)).toMonoidal
  let π : (F.obj G).left ⟶ G.left := pullback.fst G.hom (jK R)
  have hA : GlobalTheory.SS.SmConn (F.obj G) := ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd G.hom (jK R))),
    inferInstanceAs (IsSeparated (pullback.snd G.hom (jK R))),
    inferInstanceAs (QuasiCompact (pullback.snd G.hom (jK R))),
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (jK R)))⟩
  have := hA.2.1
  have := hA.2.2.2.2
  have hint : IsIntegral (F.obj G).left := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (F.obj G).hom
  obtain ⟨m, σ, hσ⟩ := GlobalTheory.T.exists_veryAmple_fourth_power_uniformised_group R (maximalIdeal R) D A G U
  obtain ⟨s₀, y₀, i₀, i₀', -, hy₀⟩ := hnd 4 (by norm_num)
  have ht₀ : ∃ p : (F.obj G).left, π p ∈ nonzeroLocus (S 4 s₀) := by
    refine exists_generic_mem G.hom _ (y := (fstG (maximalIdeal R) 0 G).left y₀) ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i₀', (Scheme.preimage_basicOpen _ _).ge hy₀⟩
  obtain ⟨Y, x₁, x₂, Φ, ⟨y⟩, hfl, hΦ, hrat⟩ := exists_formal_pair G b hb.1 hb.2.1 U.LG.isLB
  have hπ : ∀ x : Y ⟶ G, (F.map x).left ≫ π = pullback.fst Y.hom (jK R) ≫ x.left := fun x =>
    pullback.lift_fst _ _ _
  have hratK : ∀ (x : Y ⟶ G) (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((F.map (Φ x)).left ≫ π)
      ((F.map x).left ≫ π) s₁ s₂ (S k s₁) (S k s₂) := fun x k s₁ s₂ => by
    rw [hπ, hπ]
    exact (hrat x k _ s₁ s₂ _ _ fun e => hS k e s₁ s₂).comp _
  have hflK : Flat (lift (F.map x₁) (F.map x₂)).left := by
    rw [← Functor.OplaxMonoidal.lift_δ, Over.comp_left]
    have h1 : Flat (F.map (lift x₁ x₂)).left := MorphismProperty.overPullbackMap (P := @Flat) (jK R) _ hfl
    have h2 : IsIso (Functor.OplaxMonoidal.δ F G G).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (Functor.OplaxMonoidal.δ F G G)))
    infer_instance
  have hYfl : Flat Y.hom := by
    have : Flat (G ⊗ G).hom := inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
    rw [← Over.w (lift x₁ x₂)]
    infer_instance
  obtain ⟨yK, -⟩ := exists_generic_mem Y.hom ⊤ (y := y) trivial
  have : Smooth (fst (F.obj G) (F.obj G)).left :=
    inferInstanceAs (Smooth (pullback.fst (F.obj G).hom (F.obj G).hom))
  have : GeometricallyConnected (fst (F.obj G) (F.obj G)).left :=
    inferInstanceAs (GeometricallyConnected (pullback.fst (F.obj G).hom (F.obj G).hom))
  have : IsIntegral (F.obj G ⊗ F.obj G).left := by
    have := GlobalTheory.isNormalScheme_of_smooth (S := Sp (FractionRing R)) (F.obj G).hom
    have : IsLocallyNoetherian (F.obj G).left := LocallyOfFiniteType.isLocallyNoetherian (F.obj G).hom
    exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (fst (F.obj G) (F.obj G)).left
  have hdom : IsDominant (lift (F.map x₁) (F.map x₂)).left := isDominant_of_flat _ yK
  have hfl₁ : Flat (F.map x₁).left := by
    rw [← lift_fst (F.map x₁) (F.map x₂), Over.comp_left]
    infer_instance
  have hdom₁ : IsDominant (F.map x₁).left := isDominant_of_flat _ yK
  obtain ⟨V, j, f, hj, hV, hf⟩ := GlobalTheory.T.exists_morphism_of_sectionRatios_veryAmple (FractionRing R) (F.obj G) G.left U.LG.L U.LG.isLB π 4 _ m σ hσ s₀
    (S 4 s₀) (fun i => S 4 (σ i)) ht₀ (F.obj Y) (F.map x₁) (F.map (Φ x₁)) hdom₁ fun i => hratK x₁ 4 _ _
  have hpt : ∀ (x : Y ⟶ G) (Z : Over (Sp (FractionRing R))) (w : Z ⟶ F.obj Y) (u : Z ⟶ V),
      u ≫ j = w ≫ F.map x → u ≫ f = w ≫ F.map (Φ x) := fun x Z w u e => hf Z u _ fun i => by
    rw [e, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    exact (hratK x 4 _ _).comp _
  have hadd := GlobalTheory.T.mul_of_mul_at_dominant_pair_commGroup (FractionRing R) (F.obj G) hA V j f hj (F.obj Y) _ _ _ _ hdom (hpt x₁) (hpt x₂)
    (by rw [← Functor.map_mul, ← Functor.map_mul, ← hΦ]; exact hpt (x₁ * x₂))
  obtain ⟨φ, hφ, hjφ⟩ := GlobalTheory.T.exists_monHom_extension_openPart_field (FractionRing R) (F.obj G) (F.obj G) V hA hA j f hj hV hadd
  refine ⟨φ, hφ, fun k s₁ s₂ => ?_⟩
  let Z : Over (Sp (FractionRing R)) := Over.mk (pullback.fst (F.map x₁).left j.left ≫ (F.obj Y).hom)
  let w : Z ⟶ F.obj Y := Over.homMk (pullback.fst (F.map x₁).left j.left) rfl
  let u : Z ⟶ V := Over.homMk (pullback.snd (F.map x₁).left j.left) (by
    have e := congrArg (· ≫ (F.obj G).hom) (pullback.condition (f := (F.map x₁).left) (g := j.left))
    simp only [Category.assoc, Over.w] at e
    exact e.symm)
  have huw : u ≫ j = w ≫ F.map x₁ := Over.OverMorphism.ext pullback.condition.symm
  have e : (w ≫ F.map x₁) ≫ φ = w ≫ F.map (Φ x₁) := by rw [← huw, Category.assoc, hjφ, hpt x₁ Z w u huw]
  obtain ⟨z⟩ : Nonempty Z.left := by
    obtain ⟨v⟩ := hV
    obtain ⟨p, v', hp⟩ := (F.map x₁).left.denseRange.exists_mem_open (IsOpenImmersion.isOpen_range j.left)
      ⟨_, v, rfl⟩
    obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback p v' hp.symm
    exact ⟨z⟩
  have : Flat (w ≫ F.map x₁).left :=
    inferInstanceAs (Flat (pullback.fst (F.map x₁).left j.left ≫ (F.map x₁).left))
  have := isDominant_of_flat (w ≫ F.map x₁).left z
  refine SecRatioEq.of_isDominant (Y := (F.obj G).left) (w ≫ F.map x₁).left ?_
  have e' : (w ≫ F.map x₁).left ≫ φ.left ≫ π = w.left ≫ (F.map (Φ x₁)).left ≫ π := by
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
  have h3 := (hratK x₁ k s₁ s₂).comp w.left
  rw [← e', ← Category.assoc w.left] at h3
  exact h3

end GlobalTheory.Mum.GenericRatio
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Build

lemma exp_nsmul {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (hadd : ∀ z w, e (z + w) = e z * e w) (z : Fin g → ℂ) : ∀ n : ℕ, e (n • z) = e z ^ n := by
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this |>.symm ▸ rfl
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

lemma exists_nsmul_eq_of_dvd {La : Type} [AddCommGroup La] (EF E₁ : LinearMap.BilinForm ℤ La) (hE₁ : EF = (2:ℤ) • E₁)
    (e₀ : ℕ) (a : La) (k : ℕ) (hdv : ∀ y, (k : ℤ) ∣ E₁ a y) (nondeg : ∀ x, (∀ y, EF x y = 0) → x = 0)
    (hperf : ∀ f : La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e₀ • f) : ∃ x', e₀ • a = k • x' := by
  let φ : La →ₗ[ℤ] ℤ :=
    { toFun := fun y => E₁ a y / k
      map_add' := fun u v => by
        rw [map_add (f := _)]; exact Int.add_ediv_of_dvd_left (hdv u)
      map_smul' := fun c u => by
        rw [map_zsmul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdv u) }
  obtain ⟨x', hx''⟩ := hperf φ
  refine ⟨x', ?_⟩
  rw [← sub_eq_zero]
  apply nondeg
  intro y
  have hφ : E₁ x' y = e₀ * (E₁ a y / k) := by
    have := congrArg (fun F : La →ₗ[ℤ] ℤ => F y) hx''
    simpa [φ] using this
  have hm : (k : ℤ) * (E₁ a y / k) = E₁ a y := Int.mul_ediv_cancel' (hdv y)
  rw [hE₁]
  simp only [LinearMap.smul_apply, map_sub, map_nsmul, LinearMap.sub_apply, smul_eq_mul, nsmul_eq_mul, hφ]
  linear_combination (-2 * (e₀:ℤ)) * hm

lemma half_unique {La : Type} [AddCommGroup La] (E E' : LinearMap.BilinForm ℤ La) (h : (2:ℤ) • E = (2:ℤ) • E') :
    E = E' := by
  ext u v
  have h2 := congrArg (fun B : LinearMap.BilinForm ℤ La => B u v) h
  simp only [LinearMap.smul_apply, smul_eq_mul] at h2
  omega

end GlobalTheory.UPel.HT.Build


open GlobalTheory.UPel.HT.Build in
theorem GlobalTheory.UPel.HT.exists_obj_unifAt_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) t Q, 0 < N → N.Coprime p → b.IsType σ ρ → D.Cls N D' t → IsPeriod D' ρ Q → ∃ (o : Obj b N (spMap σ)) (h : _) (hL : _) (e : _), UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ D' t Q hN hNp htype hcls hper
  obtain ⟨hgen, E₁, hE₁, e₀, he₀p, hperf⟩ := hcls
  obtain ⟨A, _, _, act, P, e, hab, hdim, hP, r₁, r₂, hsy, ham, hexp, hker, hact, hweil⟩ :=
    GlobalTheory.T.exists_abelianVariety_of_halved_periodMap D.O D.inv D.g ρ D' Q E₁ hper hE₁
  have hadd := hexp.1
  have hsurj := hexp.2.1
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.T.lieCondition_of_complexExp_intertwines_action p D R b N σ ρ A act e hab hdim hexp hact htype
  have hgen' := hgen
  obtain ⟨f, ν, rfl, -, hf⟩ := hgen
  have hfN := hf N hN hNp
  let eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun a => e ((N : ℂ)⁻¹ • Q (f N a))
  have heta : ∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (f N a)) := fun a => Category.id_comp _
  have hsc : ∀ (c : D.O) (k : ℂ) (x : D'.La), e (k • Q (c • x)) = e (k • Q x) ≫ act.act c := by
    intro c k x
    rw [hper.1, ← Matrix.mulVec_smul, hact]
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQ1 : ∀ x, e (Q x) = 1 := fun x => (hker _).2 ⟨x, rfl⟩
  have hgeom := GlobalTheory.T.exists_primeToP_tateSimilitude_complexTorus p D N ρ A act _ D' (f N) Q e eta hN hNp hab (pull_isLB hP _) hgen' hper hadd hsurj hker
    hact hweil heta
  let o : Obj b N (spMap σ) :=
    { A := A
      ab := hab
      act := act
      P := P
      isLB := hP
      rig₁ := r₁
      rig₂ := r₂
      symm := hsy
      ample := ham
      kerP := ⟨e₀, he₀p, GlobalTheory.T.birigidified_bundle_kernel_killed_of_complex_points A D.g hab hdim P hP r₁ r₂ hsy ham e₀ (fun x hx => by
        obtain ⟨k, hk, hxk⟩ := GlobalTheory.T.exists_pow_eq_one_of_poincareKernel_complex A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1
          hper.2.2.2.1 hker hweil x hx
        obtain ⟨z, rfl⟩ := hsurj x
        have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        have h1 : e (k • z) = 1 := by rw [exp_nsmul e hadd]; exact hxk
        obtain ⟨a, ha⟩ := (hker _).1 h1
        have hz : z = (k : ℂ)⁻¹ • Q a := by
          rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul]
        obtain ⟨E₁', hE₁', hdiv⟩ := GlobalTheory.T.diag_form_two_smul_and_ker_alt A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp
          hper.2.1 hker hweil
        have hx' : ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a))
            (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen := by
          rw [← hz]; exact hx
        have hdv : ∀ y, (k : ℤ) ∣ E₁' a y := (hdiv k a hk).2 hx'
        have hEE : E₁' = E₁ := half_unique _ _ (hE₁'.symm.trans hE₁)
        rw [hEE] at hdv
        obtain ⟨x', key⟩ := exists_nsmul_eq_of_dvd D'.EF E₁ hE₁ e₀ a k hdv D'.nondeg hperf
        have hQ : Q x' = e₀ • ((k : ℂ)⁻¹ • Q a) := by
          rw [smul_comm, ← map_nsmul, key, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk',
            one_smul]
        show e z ^ e₀ = 1
        rw [← exp_nsmul e hadd, hz, ← hQ]
        exact hQ1 x')⟩
      rosati := fun c => by
        refine (GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1 hker hweil
          (act.act c) (act.act (D.star c).unop) (AddMonoidHom.mk' (fun x => c • x) (smul_add c))
          (AddMonoidHom.mk' (fun x => (D.star c).unop • x) (smul_add _)) (act.hom c) (act.hom _)
          (fun k x _ => hsc c _ x) (fun k x _ => hsc _ _ x)).2 ?_
        intro x y
        exact D'.adj c x y
      lie := hlie
      lieRank := fun k _ _ x β hx i => hlieR k x β hx i
      eta := eta
      eta_add := fun x y => by
        show e _ = e _ * e _
        erw [map_add (f N) x y, map_add, smul_add, hadd]
        rfl
      eta_lin := fun c x => by
        obtain ⟨e', he'⟩ := hfN.2.1 c x
        show e _ = e _ ≫ _
        erw [he', map_add, smul_add, hadd, hsc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1, _root_.mul_one]
      eta_ker := fun x => by
        show e _ = 1
        erw [map_nsmul (f N) N x, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1]
      geom := fun k _ _ x β _ => hgeom k x }
  refine ⟨o, hdim, pull_isLB hP _, e, ?_⟩
  refine ⟨Category.id_comp _, hper, hexp, hker, hact, hweil, heta⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Near.closed_fibre_constant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left), (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'), t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left → N.Pt s (t ≫ h) (x * y).left) → ∀ z z' : O.toScheme, pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z) = pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z') → (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z)) = closedPoint R → h z = h z' := by
  intro R _ _ _ M G' _ E N fU l hl hf hπ O h hyp z z' hzz hcl
  have hzz' : (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) z = (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) z' := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hzz
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback z z' hzz'
  let P := pullback (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π)
  let t : Sp (P.residueField w) ⟶ O.toScheme := P.fromSpecResidueField w ≫ pullback.fst _ _
  let t' : Sp (P.residueField w) ⟶ O.toScheme := P.fromSpecResidueField w ≫ pullback.snd _ _
  have ht : ∀ u, t u = z := fun u => by
    show (P.fromSpecResidueField w ≫ pullback.fst _ _) u = z
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hw
  have ht' : ∀ u, t' u = z' := fun u => by
    show (P.fromSpecResidueField w ≫ pullback.snd _ _) u = z'
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hw'
  have hc₀ : t' ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π = t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π := by
    show (P.fromSpecResidueField w ≫ pullback.snd _ _) ≫ (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) =
      (P.fromSpecResidueField w ≫ pullback.fst _ _) ≫ (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π)
    rw [Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_spMap_residueField_of_forall_eq_closedPoint R (P.residueField w)
    ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (N.U ⊗ N.U).hom) (fun u => by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ht]; exact hcl)
  have key : ∀ (t₁ : Sp (P.residueField w) ⟶ O.toScheme),
      t₁ ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π = t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π →
      ∃ (s : Sp (P.residueField w) ⟶ M.S) (x y : Over.mk s ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) ∧
        N.Pt s ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (fst N.U N.U).left) x.left ∧
        N.Pt s ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (snd N.U N.U).left) y.left ∧
        N.Pt s (t₁ ≫ h) (x * y).left := by
    intro t₁ e
    have hs : (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π =
        (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (N.U ⊗ N.U).hom := by
      rw [← e, Category.assoc, Category.assoc, Category.assoc, Category.assoc, pullback.condition]
    have ea : ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (fst N.U N.U).left) ≫ N.U.hom =
        (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π := by
      rw [hs, Category.assoc, Over.w]
    have eb : ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (snd N.U N.U).left) ≫ N.U.hom =
        (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π := by
      rw [hs, Category.assoc, Over.w]
    let x : Over.mk (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ⟶ G' :=
      Over.homMk (pullback.lift _ _ ea ≫ N.u) (by
        rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
    let y : Over.mk (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ⟶ G' :=
      Over.homMk (pullback.lift _ _ eb ≫ N.u) (by
        rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
    refine ⟨_, x, y, hs.trans hκ, ⟨pullback.lift _ _ ea, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩,
      ⟨pullback.lift _ _ eb, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, hyp _ t₁ _ x y rfl ?_ ?_⟩
    · refine ⟨pullback.lift _ _ ea, ?_, pullback.lift_snd _ _ _, rfl⟩
      rw [pullback.lift_fst, ← e]; simp only [Category.assoc]
    · refine ⟨pullback.lift _ _ eb, ?_, pullback.lift_snd _ _ _, rfl⟩
      rw [pullback.lift_fst, ← e]; simp only [Category.assoc]
  obtain ⟨s, x, y, hs, hx, hy, hxy⟩ := key t rfl
  obtain ⟨s', x', y', hs', hx', hy', hxy'⟩ := key t' hc₀
  have e := GlobalTheory.T.closedFibre_product_coordinate_independent R M G' E N fU l hl hf hπ (P.residueField w) κ s s' _ _ (t ≫ h) (t' ≫ h) x y x' y'
    hs hs' hx hy hxy hx' hy' hxy'
  have := congrArg (fun g : Sp (P.residueField w) ⟶ N.U.left => g (IsLocalRing.closedPoint _)) e
  rw [← ht (IsLocalRing.closedPoint _), ← ht' (IsLocalRing.closedPoint _)]
  first
    | exact this
    | simpa only [Scheme.Hom.comp_apply] using this
    | simpa only [Scheme.comp_base_apply] using this

end GlobalTheory.Mum
end
