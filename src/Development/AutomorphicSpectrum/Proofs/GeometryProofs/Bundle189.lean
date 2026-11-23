module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticePointUniversal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtension
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceFamilyOverlap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle184
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle182
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyDegreePpData
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle183
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.coords_after_finite_extension : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] [CharZero Ω] (i : Ω₁ →+* Ω) (y : (Σ k, J k) → Ω₁) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (M : PModel ℤ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩)) (h : M.X ⟶ X), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ h i ∧ Flat.NormalCpt M.ξ ∧ SmoothGenericFibreM y' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model | exact GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProjModel

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem sec_ext (hg : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {W : X.Opens} {s t : Γ(X, W)}
    (h : ∀ hW : genPt ξ ∈ W, CoordBase.val (ξ := ξ) W hW s = CoordBase.val (ξ := ξ) W hW t) : s = t := by
  refine TopCat.Presheaf.section_ext X.sheaf W s t fun p hp => ?_
  have hW : genPt ξ ∈ W := (hall p).mem_open W.isOpen hp
  refine hg.inj ⟨p, hall p⟩ ?_
  exact (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp s).trans
    ((h hW).trans (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp t).symm)

theorem val_resG {U V : X.Opens} (h : V ≤ U) (hV : genPt ξ ∈ V) (s : Γ(X, U)) :
    CoordBase.val (ξ := ξ) V hV (resG X h s) = CoordBase.val (ξ := ξ) U (h hV) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply (homOfLE h).op.unop _ hV s)

theorem exists_charts {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x) (hall : ∀ q : X, genPt ξ ⤳ q) :
    ∃ U : κ → X.Opens, (∀ c, IsAffineOpen (U c)) ∧ ∀ c q, q ∈ U c ↔ InChart ξ x c ⟨q, hall q⟩ := by
  have : ∀ c, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ q, q ∈ U ↔ InChart ξ x c ⟨q, hall q⟩ := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨⊥, isAffineOpen_bot X, fun q => ⟨fun h => h.elim, fun h => (h.1 hc).elim⟩⟩
    · obtain ⟨U, hU, hm⟩ := hT.affine c hc
      exact ⟨U, hU, fun q => (hm q).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hall q, h⟩⟩⟩
  choose U hU using this
  exact ⟨U, fun c => (hU c).1, fun c => (hU c).2⟩

theorem eval₂Hom_surjective {A J : Type} [CommRing A] (b : ℤ →+* A) (ρ : J → A) (v : A →+* Ω)
    (hv : Function.Injective v) (y : J → Ω) (hρ : ∀ j, v (ρ j) = y j)
    (hA : ∀ a, v a ∈ Algebra.adjoin ℤ (Set.range y)) :
    Function.Surjective (MvPolynomial.eval₂Hom b ρ) := by
  intro g
  have hg := hA g
  rw [Algebra.adjoin_range_eq_range_aeval] at hg
  obtain ⟨P, hP⟩ := hg
  refine ⟨P, hv ?_⟩
  have key : v.comp (MvPolynomial.eval₂Hom b ρ) =
      (MvPolynomial.aeval y : MvPolynomial J ℤ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp
    · simp [hρ]
  exact (congrArg (fun φ : MvPolynomial J ℤ →+* Ω => φ P) key).trans hP

theorem isProjOver_of_coordTie {N : ℕ} {x : Fin (N + 1) → Ω} (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) (s : X ⟶ Sp ℤ) : IsProjOver s := by
  classical
  obtain ⟨U, hU, hm⟩ := exists_charts hT hall
  have hmem : ∀ c q, q ∈ U c ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩ := fun c q =>
    (hm c q).trans ⟨fun h => ⟨hall q, h⟩, fun ⟨_, h⟩ => h⟩
  have hgen : ∀ c, genPt ξ ∈ U c → x c ≠ 0 := fun c h => ((hm c _).1 h).1
  have hr : ∀ c j, ∃ b : Γ(X, U c), ∀ hW : genPt ξ ∈ U c,
      CoordBase.val (ξ := ξ) (U c) hW b = x j / x c := by
    intro c j
    by_cases hW : genPt ξ ∈ U c
    · obtain ⟨b, hb⟩ := (CoordBase.mem_adjoin_iff hT (hgen c hW) (hU c) (hmem c) hW (x j / x c)).1
        (Algebra.subset_adjoin ⟨j, rfl⟩)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => (hW h).elim⟩
  choose r hr using hr
  have H : IsCoordFamily U r :=
    { cover := by
        rw [eq_top_iff]
        intro q _
        obtain ⟨c, hc⟩ := hT.cover ⟨q, hall q⟩
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, (hm c q).2 hc⟩
      self := fun i => sec_ext hT.gen hall fun hW => by
        rw [hr, map_one, div_self (hgen i hW)]
      mul := fun i j k => sec_ext hT.gen hall fun hW => by
        have hi := hgen i hW.1
        have hj := hgen j hW.2
        rw [map_mul, val_resG, val_resG, val_resG, hr, hr, hr]
        field_simp
      basicOpen_le := fun i j p hp => by
        have hpi : p ∈ U i := X.basicOpen_le _ hp
        obtain ⟨u, hu⟩ : IsUnit (X.presheaf.germ (U i) p hpi (r i j)) :=
          (X.mem_basicOpen _ p hpi).1 hp
        have hW : genPt ξ ∈ U i := (hall p).mem_open (U i).isOpen hpi
        have hxi := hgen i hW
        have hv : genMap ξ ⟨p, hall p⟩ (u : X.presheaf.stalk p) = x j / x i := by
          rw [hu]
          exact (CoordBase.genMap_germ_val (U i) hW ⟨p, hall p⟩ hpi _).trans (hr _ _ _)
        have hinv : (x j / x i) * genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = 1 := by
          rw [← hv, ← map_mul, Units.mul_inv, map_one]
        have hxj : x j ≠ 0 := by
          intro h
          rw [h, zero_div, zero_mul] at hinv
          exact zero_ne_one hinv
        have hi := (hm i p).1 hpi
        refine (hm j p).2 ⟨hxj, fun c' => ?_⟩
        have e : x c' / x j = (x c' / x i) *
            genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) := by
          have e' : genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = x i / x j := by
            field_simp at hinv ⊢
            linear_combination hinv
          rw [e']
          field_simp
        rw [e]
        exact (regAt ξ _).mul_mem (hi.2 c') ⟨_, rfl⟩ }
  refine ⟨N, H.toHom s, ?_, H.toHom_str s⟩
  refine (isClosedImmersion_iff_pullRatio (H.toHom s) (H.toHom_preimage s)).2 fun i => ⟨hU i, ?_⟩
  have hρ : pullRatio (H.toHom s) (U i) i (H.toHom_preimage s i).ge = r i :=
    funext (H.pullRatio_toHom s i)
  rw [hρ]
  by_cases hW : genPt ξ ∈ U i
  · refine eval₂Hom_surjective _ _ (CoordBase.val (ξ := ξ) (U i) hW) ?_ (fun j => x j / x i) (hr i · hW) ?_
    · intro a a' e
      exact sec_ext hT.gen hall fun _ => e
    · intro a
      exact (CoordBase.mem_adjoin_iff hT (hgen i hW) (hU i) (hmem i) hW _).2 ⟨a, rfl⟩
  · exact fun g => ⟨0, sec_ext hT.gen hall fun h => (hW h).elim⟩

theorem isProjOver_pModel {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel ℤ x) : IsProjOver M.s := by
  obtain ⟨N, x', h⟩ := coordTie_int_of_finite M.X Ω M.ξ ℤ κ x M.tie
  exact isProjOver_of_coordTie h M.all M.s

theorem isProjOver_of_map {O : Type} [CommRing O] {Z : Scheme.{0}} {s : Z ⟶ Sp ℤ} (h : IsProjOver s)
    (g : Z ⟶ Sp O) : IsProjOver g := by
  have hp := isProjOver_pullback_snd (Int.castRingHom O) h
  let σ : Z ⟶ pullback s (spMap (Int.castRingHom O)) :=
    pullback.lift (𝟙 Z) g (specZIsTerminal.hom_ext _ _)
  have hσ : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ pullback.fst s (spMap (Int.castRingHom O))) := by
      rw [pullback.lift_fst]
      infer_instance
    exact .of_comp σ (pullback.fst s (spMap (Int.castRingHom O)))
  have := isProjOver_comp_of_isClosedImmersion σ hp
  rwa [pullback.lift_snd] at this

theorem isProjOver_comp_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X), IsProjOver (f ≫ Y.s) :=
  fun _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ M f => isProjOver_of_map (isProjOver_pModel M) (f ≫ Y.s)

end GlobalTheory.CompanionTheory.Ar.ProjModel
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace TripleHodge

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem one_left_comp (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
  congrArg (fun p => p.left) (map_one (pushHom h T))

theorem isTanAt_iff (h : IsGrpPullback G' G f φ) (z : Spec (CommRingCat.of ℂ) ⟶ S') (v' : epsAt z ⟶ G')
    (v : epsAt (z ≫ f) ⟶ G) (e : v.left = v'.left ≫ φ) : IsTanAt G' z v' ↔ IsTanAt G (z ≫ f) v := by
  have one := one_left_comp h (Over.mk z)
  have wv := Over.w v'
  constructor
  · intro hv
    unfold IsTanAt at hv ⊢
    rw [e, ← Category.assoc, hv]
    exact one
  · intro hv
    unfold IsTanAt at hv ⊢
    apply h.1.hom_ext
    · rw [Category.assoc, ← e, hv]
      exact one.symm
    · have w1 := Over.w (1 : Over.mk z ⟶ G')
      rw [Category.assoc, w1, wv]
      show Spec.map _ ≫ Spec.map _ ≫ z = z
      rw [← Category.assoc, ← Spec.map_comp]
      have e₁ : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext x
        simp
      rw [e₁, Spec.map_id, Category.id_comp]

variable {X X' : Scheme.{0}}

theorem exists_iso_comp {Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (p : Y ⟶ X') :
    ∃ w₂ : LB.Iso (L'.pull p) (L.pull (p ≫ F)), w₂.IsGen := by
  have hP : (L'.pull p).IsLB := pull_isLB hL' p
  have hr := (isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)
  have hw' := (isGen_iff _).1 hw
  obtain ⟨w₂, T⟩ := exists_comp hL' w _ hw' hr hL hP
  exact ⟨w₂, (isGen_iff _).2 (T.pgen_comp hL' hw' hr)⟩

theorem exists_iso_cancel {Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (p : Y ⟶ X') :
    ∃ w₂ : LB.Iso (L.pull (p ≫ F)) (L'.pull p), w₂.IsGen := by
  have hP : (L.pull (p ≫ F)).IsLB := pull_isLB hL (p ≫ F)
  have hr := (isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)
  have hw' := (isGen_iff _).1 hw
  obtain ⟨w₂, T⟩ := exists_cancel hL w _ hw' hr hL' hP
  exact ⟨w₂, (isGen_iff _).2 (T.pgen_cancel hL hw' hr)⟩

end TripleHodge

theorem hodgeInnerProduct_tripleMap_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ),
    v.left = v'.left ≫ m.φ → w.left = w'.left ≫ m.φ →
      (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  intro E _ _ _ H X t X' t' f m z v' w' v w c hv hw
  obtain ⟨i, hi, -, -⟩ := m.lin
  have tv := TripleHodge.isTanAt_iff m.cart z v' v hv
  have tw := TripleHodge.isTanAt_iff m.cart z w' w hw
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  constructor
  · rintro ⟨-, h₁, h₂, A, _, φ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩
    obtain ⟨i₂, hi₂⟩ := TripleHodge.exists_iso_comp hL hL' hi φ
    have hP := pull_isLB hL' φ
    have hQ := pull_isLB hL (φ ≫ m.φ)
    refine ⟨hL, tv.1 h₁, tw.1 h₂, A, inferInstance, φ ≫ m.φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ,
      a', b', a, b, p₁.comp m.cart, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂, ?_, ?_, p₅, p₆, rfl⟩
    · rw [hv, ← p₃, Category.assoc]
    · rw [hw, ← p₄, Category.assoc]
  · rintro ⟨-, h₁, h₂, A, _, ψ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩
    obtain ⟨φ, rfl, hφ⟩ : ∃ φ : A.left ⟶ t'.G.left, φ ≫ m.φ = ψ ∧ φ ≫ t'.G.hom = A.hom ≫ z :=
      ⟨m.cart.1.lift ψ (A.hom ≫ z) (by rw [p₁.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
    obtain ⟨i₂, hi₂⟩ := TripleHodge.exists_iso_cancel hL hL' hi φ
    have hP := pull_isLB hL (φ ≫ m.φ)
    have hQ := pull_isLB hL' φ
    have lift : ∀ (x : epsR ℂ ⟶ A) (y : epsAt z ⟶ t'.G) (y₀ : epsAt (z ≫ f) ⟶ t.G), y₀.left = y.left ≫ m.φ →
        x.left ≫ φ ≫ m.φ = y₀.left → x.left ≫ φ = y.left := by
      intro x y y₀ e e'
      apply m.cart.1.hom_ext
      · rw [Category.assoc, e', e]
      · rw [Category.assoc, hφ, ← Category.assoc, Over.w x, Over.w y]
        rfl
    exact ⟨hL', tv.2 h₁, tw.2 h₂, A, inferInstance, φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ,
      a', b', a, b, IsGrpPullback.cancel m.cart p₁ hφ, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂,
      lift a' v' v hv p₃, lift b' w' w hw p₄, p₅, p₆, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem hodgeForm_of_isHodgeGram (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n : ℕ)
    (v : Fin n → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (hL : L.IsLB) (hv : ∀ i, IsTanAt G x (v i))
    (h : Fl.IsHodgeGram G L x v Γ) (i j : Fin n) : HodgeForm G L x (v i) (v j) (Γ i j) := by
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := h
  have hM := pull_isLB hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨hL, hv i, hv j, Q.A, inferInstance, ψ, Q.g, GlobalTheory.TorsionTauCompare.transport Q.isLB hM hw u, Hm, χ, v' i, v' j,
    W i, W j, hp, GlobalTheory.TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH, (hvW i).1, (hvW j).1, (hvW i).2, (hvW j).2,
    hΓ i j⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.interior_point_polarised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → HodgeMetric.PolarisedAt 𝔐.t z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

theorem _root_.GlobalTheory.T.dual_lattice_point_universal : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ u : ob x (Module.Dual R L) ⟶ G, zsec x ≫ u = 1 ∧ (∀ e : L, hom x (Module.Dual.eval R L e) ≫ u = M.pt e) ∧ ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (v : ob x V ⟶ G), zsec x ≫ v = 1 → ∃! φ : Module.Dual R L →ₗ[R] V, hom x φ ≫ u = v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tan.Univ.tangent_universal | exact GlobalTheory.CompanionTheory.Ar.BT.Tan.Univ.tangent_universal | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tan.Univ.tangent_universal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chartPack_lift_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c₁ c₂ : ∀ k, J k), mseg y c₁ ≠ 0 → mseg y c₂ ≠ 0 → ∀ (P₁ : ChartPack G O c₁) (P₂ : ChartPack G O c₂) (x : Fin (D.p + D.q) → 𝓞 E), ∃ n : ℕ, ∃ u ∈ P₂.Dh.om, (mseg y c₁ / mseg y c₂) ^ n • (P₁.Dh.h x - P₂.Dh.h x) = (p ^ 𝔐.R p) • u :=
  PositivityTheory.Xgn.sequence_family_overlap

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.germ_jet_quotient_formula : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d m : ℕ) (w : Fin d → k) (g : Germ.PS k 2 d), AxOne g → jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) = 1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer g fun i => w i ^ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow | exact GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.germ_frobenius_torsion_jet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ j, jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j))) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.actp_vanish | exact GlobalTheory.CompanionTheory.Ar.Coc.actp_vanish | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.actp_vanish <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.FlagModelStatement_holds : FlagModelStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel | exact GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.T.key_degree_pp_data : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (x : KeyIn L) (th : D.t.PP.L.Sec) (s : Out.H0 D.t.PP.L 1) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)) (e : Fin D.g → D.B.carrier), KeyDeg.SameSec s th → KeyOver (algebraMap (𝓞 L) L) D.t th x v → IsLieBasis v → (∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left) → ∀ (σ : L →+* ℂ) (a : D.Frame σ) (θ : (Fin D.g → ℂ) → ℂ) (W : Matrix (Fin D.g) (Fin D.g) ℂ) (Fd : Set (Fin D.g → ℂ)), a.IsFn s θ → (∀ i, D.IsVec a (e i) (W i)) → IsAddFundamentalDomain a.u.Λ Fd volume → ‖σ (κ L x : L)‖ * ((∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal) ^ 4 * ((volume Fd).toReal / (Real.pi ^ D.g * ‖W.det‖ ^ 2)) ^ 2 = (2 * Real.pi) ^ (2 * D.g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDegArch.norm_key_of_frame | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDegArch.norm_key_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDegArch.norm_key_of_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.analytic_provision_holds : Prov.An := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.prov_an | exact GlobalTheory.CompanionTheory.Ar.Link.prov_an | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.prov_an <;> assumption)
end
