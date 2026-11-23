module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle036
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Mathlib.RingTheory.LaurentSeries
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag.LQF

theorem finite_preimage_of_finite_points {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (H : {z : Spec (CommRingCat.of (AlgebraicClosure (Y.residueField y))) ⟶ X | z ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y}.Finite) : (f ⁻¹' {y}).Finite := by
  let k := Y.residueField y
  let K := AlgebraicClosure k
  let pt : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have hcl : closedPoints (f.fiber y) ⊆ f.fiberι y ⁻¹' ((fun z : Spec (CommRingCat.of K) ⟶ X => z pt) '' {z |
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ Y.fromSpecResidueField y}) := by
    intro w hw
    have hw' : IsClosed ({w} : Set (f.fiber y)) := hw
    have h1 : LocallyOfFiniteType ((f.fiber y).fromSpecResidueField w) :=
      isClosed_singleton_iff_locallyOfFiniteType.1 hw'
    have h0 : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹LocallyOfFiniteType f›
    have h2 : LocallyOfFiniteType ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y) := inferInstance
    have h3 : IsFinite ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 h2
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y)
    have h4 : φ.hom.Finite := by
      rw [← IsFinite.SpecMap_iff, hφ]; exact h3
    letI : Algebra k ((f.fiber y).residueField w) := φ.hom.toAlgebra
    haveI : Module.Finite k ((f.fiber y).residueField w) := h4
    haveI : Algebra.IsAlgebraic k ((f.fiber y).residueField w) := Algebra.IsIntegral.isAlgebraic
    let ι : (f.fiber y).residueField w →ₐ[k] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ (f.fiber y).fromSpecResidueField w ≫ f.fiberι y, ?_, ?_⟩
    · show _ = _
      rw [Category.assoc, Category.assoc, Scheme.Hom.fiber_fac, ← Category.assoc ((f.fiber y).fromSpecResidueField w),
        ← hφ, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      exact ι.commutes a
    · show (Spec.map _ ≫ _ ≫ _) pt = _
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hfin : (closedPoints (f.fiber y)).Finite :=
    ((H.image _).preimage (f.fiberι y).isEmbedding.injective.injOn).subset hcl
  have huniv : (Set.univ : Set (f.fiber y)) = closedPoints (f.fiber y) := by
    have hc : IsClosed (closedPoints (f.fiber y)) := by
      rw [← Set.biUnion_of_singleton (closedPoints (f.fiber y))]
      exact hfin.isClosed_biUnion fun x hx => hx
    rw [← JacobsonSpace.closure_inter_closedPoints isClosed_univ, Set.univ_inter, hc.closure_eq]
  haveI : Finite (f.fiber y) := Set.finite_univ_iff.1 (huniv ▸ hfin)
  rw [← Scheme.Hom.range_fiberι]
  exact Set.finite_range _

end GlobalTheory.VarFlag.LQF

namespace GlobalTheory.VarFlag.LQF

open GlobalTheory.FlagMod (FlagCover FlagModel Frames initSpan initSpan_le_of_tri)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_sum_of_isCombAtG {Y : Model Xo c (RingHom.id c.F)} {K : Type} [Field K] {x x' : Sp K ⟶ Y.X} (e : x' = x)
    {m : ℕ} (u : Fin m → TanM x Y.t.G) (cf : Fin m → K) (w : TanM x Y.t.G)
    (h : IsCombAtG Y.t x' (fun j => (tv (u j)).left) cf (tv w).left) : w = ∑ j, cf j • u j := by
  subst e
  exact (GlobalTheory.LieMet.isComb_iff u cf w).1 h

theorem vecAt_left {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {K : Type}
    [Field K] (k : F.J) (z : Sp K ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp K ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ)
    (i : Fin (Dw.mult σ)) : (tv (F.vecAt k z hz hx σ i)).left = (tv (F.vecAt k z hz rfl σ i)).left := by
  subst hx; rfl

theorem initSpan_le_of_frameTri {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {K : Type} [Field K] {φ φ' : c.F →+* K} (z z' : Sp K ⟶ Z) {x : Sp K ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π = x)
    (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k') (g : EigFrame Y φ (z ≫ π))
    (g' : EigFrame Y φ' (z' ≫ π)) (hg : IsFrameAt F z k hz g) (hg' : IsFrameAt F z' k' hz' g')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (ht : g.Tri (RingHom.id K) g' t) (σ : E →+* ℂ) (i : ℕ) :
    initSpan K (F.vecAt k' z' hz' hx' σ) i ≤ initSpan K (F.vecAt k z hz hx σ) i := by
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have ex : ∀ j : Fin (Dw.mult σ), ∃ cf : Fin (Dw.mult σ) → K, (∀ k, j < k → cf k = 0) ∧
      F.vecAt k' z' hz' hx' σ j = ∑ a, cf a • F.vecAt k z hz hx σ a := fun j => by
    obtain ⟨cf, -, hcf, hc⟩ := ht.2.2 σ j
    refine ⟨cf, hcf, eq_sum_of_isCombAtG hx' _ cf _ ?_⟩
    have e1 : (fun a => spMap (dualMap (RingHom.id K)) ≫ g.v σ a) =
        fun a => (tv (F.vecAt k z hz hx σ a)).left := funext fun a => by
      rw [h1, Category.id_comp, hg σ a, vecAt_left F k z hz hx σ a]
    rw [e1, hg' σ j, ← vecAt_left F k' z' hz' hx' σ j] at hc
    exact hc
  choose cf hcf e using ex
  exact initSpan_le_of_tri (B := Matrix.of fun a j => cf j a) (fun j a h => hcf a j h) e i

end GlobalTheory.VarFlag.LQF

namespace GlobalTheory.VarFlag.LQF

open GlobalTheory.FlagMod (FlagCover FlagModel Frames initSpan)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.CompHS (Y₀ inc₀)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_base {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Y φ x} (h : C.Carries p g) :
    x = p ≫ C.π ≫ GlobalTheory.Toroidal.genι Y := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, -, htri⟩ := h
  rw [htri.1, hp, Category.assoc]

theorem tri_of_carries {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) (hC : CarriesTri C)
    {K : Type} [Field K] {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} (e : x = x') {p : Sp K ⟶ C.Y.X}
    (g : EigFrame Y φ x) (g' : EigFrame Y φ' x') (h : C.Carries p g) (h' : C.Carries p g') :
    ∃ t, g.Tri (RingHom.id K) g' t := by
  subst e
  exact hC K φ φ' x p g g' h h'

theorem finite_points {Y : Model Xo c (RingHom.id c.F)} (X : FlagModel Y) (C : FlagCpt Y (RingEquiv.refl c.F))
    (hC : CarriesTri C) (Z : Formalism.L2.Pj.Comp Xo c) (h : Y₀ X.toFlagCover Z ⟶ C.Y.X)
    (hR : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ X.toFlagCover Z), Rel X.F C (z ≫ inc₀ X.toFlagCover Z) (z ≫ h))
    (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ C.Y.X) : {z : Sp K ⟶ Y₀ X.toFlagCover Z | z ≫ h = p}.Finite := by
  rcases Set.eq_empty_or_nonempty {z : Sp K ⟶ Y₀ X.toFlagCover Z | z ≫ h = p} with h0 | ⟨z₁, hz₁⟩
  · rw [h0]; exact Set.finite_empty
  have hfin := X.fin K (z₁ ≫ inc₀ X.toFlagCover Z)
  refine (hfin.preimage (f := fun z => z ≫ inc₀ X.toFlagCover Z)
    (fun a _ b _ e => (cancel_mono (inc₀ X.toFlagCover Z)).1 e)).subset ?_
  intro z hz
  have key : ∀ w : Sp K ⟶ Y₀ X.toFlagCover Z, w ≫ h = p → ∃ (φ : c.F →+* K) (k : X.F.J)
      (hk : ⊤ ≤ (w ≫ inc₀ X.toFlagCover Z) ⁻¹ᵁ X.F.U k)
      (g : EigFrame Y φ ((w ≫ inc₀ X.toFlagCover Z) ≫ X.π)), IsFrameAt X.F _ k hk g ∧ C.Carries p g := by
    intro w hw
    obtain ⟨φ, k, hk, g, -, hg, hc⟩ := hR K w
    exact ⟨φ, k, hk, g, hg, hw ▸ hc⟩
  obtain ⟨φ, k, hk, g, hg, hc⟩ := key z hz
  obtain ⟨φ₁, k₁, hk₁, g₁, hg₁, hc₁⟩ := key z₁ hz₁
  have hx : (z ≫ inc₀ X.toFlagCover Z) ≫ X.π = (z₁ ≫ inc₀ X.toFlagCover Z) ≫ X.π :=
    (carries_base C hc).trans (carries_base C hc₁).symm
  refine ⟨hx, fun σ i => ?_⟩
  obtain ⟨t, ht⟩ := tri_of_carries C hC hx g g₁ hc hc₁
  obtain ⟨t', ht'⟩ := tri_of_carries C hC hx.symm g₁ g hc₁ hc
  rw [X.F.step_eq k _ hk hx, X.F.step_eq k₁ _ hk₁ rfl]
  exact le_antisymm (initSpan_le_of_frameTri X.F _ _ rfl hx k₁ k hk₁ hk g₁ g hg₁ hg t' ht' σ i)
    (initSpan_le_of_frameTri X.F _ _ hx rfl k k₁ hk hk₁ g g₁ hg hg₁ t ht σ i)

end GlobalTheory.VarFlag.LQF

theorem GlobalTheory.VarFlag.locallyQuasiFinite_flag : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagModel Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (h : GlobalTheory.CompHS.Y₀ X.toFlagCover Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X.toFlagCover Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X.toFlagCover Z) (z ≫ h)) → LocallyQuasiFinite h := by
  intro E _ _ _ H Dw l Xo c Y X C hC Z h _ hR
  refine LocallyQuasiFinite.of_finite_preimage_singleton h fun p => ?_
  exact GlobalTheory.VarFlag.LQF.finite_preimage_of_finite_points h p
    (GlobalTheory.VarFlag.LQF.finite_points X C hC Z h hR _ _)
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
namespace GlobalTheory.BoxLine

theorem exists_isPullback_pow {S S' : Scheme.{0}} (g : S' ⟶ S) (G : Over S) (A B : Over S')
    (φ₀ : A.left ⟶ G.left) (h : IsPullback φ₀ A.hom G.hom g) (N : ℕ) (q : Fin N → (B ⟶ A))
    (hl : IsLimit (Fan.mk B q)) :
    ∃ φ : B.left ⟶ (pow G N).left, IsPullback φ B.hom (pow G N).hom g ∧
      ∀ k, φ ≫ pr G N k = (q k).left ≫ φ₀ := by
  let ψ : Over.mk (B.hom ≫ g) ⟶ pow G N := Pi.lift fun k =>
    Over.homMk ((q k).left ≫ φ₀) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.w, ← Category.assoc, Over.w])
  have hψ : ∀ k, ψ.left ≫ pr G N k = (q k).left ≫ φ₀ := fun k => by
    have : ψ ≫ Pi.π (fun _ => G) k = _ := Pi.lift_comp_π _ k
    exact congrArg (fun t => Over.Hom.left t) this
  have hw : ψ.left ≫ (pow G N).hom = B.hom ≫ g := Over.w ψ
  have hpr : ∀ k, pr G N k ≫ G.hom = (pow G N).hom := fun k => Over.w (Pi.π (fun _ => G) k)
  refine ⟨ψ.left, ⟨⟨hw⟩, ⟨?_⟩⟩, hψ⟩
  let c : ∀ s : PullbackCone (pow G N).hom g, Fin N → (Over.mk s.snd ⟶ A) := fun s k =>
    Over.homMk (h.lift (s.fst ≫ pr G N k) s.snd (by rw [Category.assoc, hpr, s.condition]))
      (h.lift_snd _ _ _)
  have hc : ∀ s k, (c s k).left ≫ φ₀ = s.fst ≫ pr G N k := fun s k => h.lift_fst _ _ _
  let m : ∀ s : PullbackCone (pow G N).hom g, Over.mk s.snd ⟶ B := fun s =>
    hl.lift (Fan.mk _ (c s))
  have hm : ∀ s k, (m s).left ≫ (q k).left = (c s k).left := fun s k =>
    congrArg (fun t => Over.Hom.left t) (hl.fac (Fan.mk _ (c s)) ⟨k⟩)
  refine PullbackCone.IsLimit.mk _ (fun s => (m s).left) ?_ ?_ ?_
  · intro s
    have hs : (m s).left ≫ B.hom = s.snd := Over.w (m s)
    let u : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk ((m s).left ≫ ψ.left) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hw, ← Category.assoc, hs])
    let v : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk s.fst s.condition
    have huv : u = v := by
      refine Pi.hom_ext _ _ fun k => ?_
      ext1
      change ((m s).left ≫ ψ.left) ≫ pr G N k = s.fst ≫ pr G N k
      rw [Category.assoc, hψ, ← Category.assoc, hm, hc]
    exact congrArg (fun t => Over.Hom.left t) huv
  · intro s
    exact Over.w (m s)
  · intro s t h1 h2
    let u : Over.mk s.snd ⟶ B := Over.homMk t h2
    have : u = m s := by
      refine hl.uniq (Fan.mk _ (c s)) u ?_
      rintro ⟨k⟩
      ext1
      change t ≫ (q k).left = (c s k).left
      refine h.hom_ext ?_ ?_
      · rw [hc, Category.assoc, ← hψ, ← Category.assoc, h1]
      · rw [Category.assoc, Over.w, h2]
        exact (Over.w (c s k)).symm
    exact congrArg (fun t => Over.Hom.left t) this


open GlobalTheory.CechPic in
theorem cls_pull_box {S : Scheme.{0}} (G : Over S) (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {X : Scheme.{0}} (φ : X ⟶ (pow G N).left) (h : ((boxLB G L N).pull φ).IsLB) :
    cls ((boxLB G L N).pull φ) h = ∑ k, pull (φ ≫ pr G N k) (cls L hL) := by

  rw [cls_pull (LB.isLB_linComb hL _ _), cls_linComb hL, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_smul, pull_comp]

theorem isLB_triv (X : Scheme.{0}) : (LB.triv X).IsLB :=
  ⟨by simp, fun _ => map_one _, fun _ _ _ => by simp⟩


open GlobalTheory.CechPic in
theorem sections_line : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  intro V K _ _ f G _ _ L rig θ n w x hL hx N
  obtain ⟨φ₀, he, e, hg, F, hpb, hegen, -⟩ := hx
  have hbox : ∀ {X : Scheme.{0}} (φ : X ⟶ (pow G N).left), ((boxLB G L N).pull φ).IsLB :=
    fun φ => LB.isLB_linComb (LB.isLB_linComb hL _ _) _ _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨φ, hφ, -⟩ := exists_isPullback_pow (spMap f) G x.P.A (Over.mk (𝟙 (Sp K))) φ₀ hpb.1 0
      (fun k => k.elim0)
      (Fan.IsLimit.mk _ (fun s => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
        (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _))
    refine ⟨Sp K, 𝟙 _, φ, LB.triv _, ⟨fun _ => 1, fun _ _ => by simp⟩, hφ, isLB_triv _, ?_, ?_⟩
    · rw [iso_triv_iff, ← cls_eq_zero_iff (hbox φ), cls_pull_box G L hL]
      simp
    · intro s
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (s.f PUnit.unit), fun i => ?_⟩
      obtain rfl : i = PUnit.unit := rfl
      have h0 : ∀ (h : (⊤ : (Sp K).Opens) ≤ ⊤) (t : Γ(Sp K, ⊤)),
          ((Sp K).presheaf.map (homOfLE h).op).hom t = t := fun h t => by
        rw [show homOfLE h = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
        rfl
      simp [constFn, Scheme.Hom.appLE]
      exact (h0 _ _).symm
  · obtain ⟨y, p, -⟩ := GlobalTheory.KeyPow.exists_isKeyPow K x N hN
    obtain ⟨φ, hφ, hc⟩ := exists_isPullback_pow (spMap f) G x.P.A y.P.A φ₀ hpb.1 N p.pr p.lim
    obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section GlobalTheory.firstFiveLaws.2.1.secTwist y.P
    refine ⟨y.P.A.left, y.P.A.hom, φ, y.P.L, b, hφ, y.P.isLB, ?_, fun s => (hb s).exists⟩
    have h1 : cls x.P.L x.P.isLB = pull φ₀ (cls L hL) := by
      rw [← cls_pull hL φ₀ (LB.isLB_linComb hL _ _), cls_eq_iff]
      exact ⟨e, hegen⟩
    have h2 : cls y.P.L y.P.isLB
        = cls (Out.boxLB x.P.L p.pr) (LB.isLB_linComb x.P.isLB _ _) := by
      rw [cls_eq_iff]
      exact ⟨p.w, p.w_gen⟩
    rw [← cls_eq_iff y.P.isLB (hbox φ), cls_pull_box G L hL, h2, cls_linComb x.P.isLB]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_smul, hc, pull_comp, h1]

end GlobalTheory.BoxLine
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.FlagPushProof

theorem flagPushForward : GlobalTheory.Published.FlagPushForward := by
  intro F _ _ X Y ι _ m E E' φ f gr hf hg Q R hR
  have hswap := GlobalTheory.T.flagSpace_intersectionNumber_adjacent_swap_neg F X Y ι m E E' φ f hf gr hg
  refine GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq ι m (Y.interPoly gr) hswap Q (chernRoots m R * fibrePoint m) ?_
  classical
  have rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
      (R : MvPolynomial (ι × ℕ) ℝ) :
      rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
    have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
      have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
        funext i; rfl
      rw [e, ← rename_rename, rename_esymm]
    exact AlgHom.congr_fun h R

  have antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
      (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_chernRoots, mul_smul_comm]

  have prod_Ioi_rev {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
        ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
      intro f
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      congr 1
      ext j; simp
    rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
      ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
    refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
    simp [Fin.rev_lt_rev]

  have sum_sign_prod_neg_pow {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
        ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
    let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
    have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
      rw [Matrix.det_apply']
      rfl
    have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
      ext j i
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
      congr 1
      omega
    rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
      GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde]
    simp only [neg_sub_neg]
    rw [prod_Ioi_rev]

  have antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
    have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
        ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
          ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(MvPolynomial.X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
      intro w
      unfold fibrePoint
      rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [map_pow, map_neg, rename_X]
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.sum_congr rfl fun w _ => hw w]
    rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(MvPolynomial.X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
    unfold rootDiscr
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (MvPolynomial.X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))
  rw [hR, antisymm_chernRoots_mul ι m R, antisymm_fibrePoint ι m]

end GlobalTheory.FlagPushProof
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open GlobalTheory.Points GlobalTheory.HermFrame
open scoped Classical

namespace GlobalTheory.ChernTop

variable {n : ℕ}

def rowForm (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n := Fintype.linearCombination ℂ fun b => sym (a, b)

def matForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Ev n where
  toFun H := kappa • ∑ a, rowForm a (H a)
  map_add' H H' := by
    rw [← smul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_add _ _ _)
  map_smul' c H := by
    rw [RingHom.id_apply, smul_comm, Finset.smul_sum (r := c)]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul (rowForm a) c (H a))

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {σ : k →+* ℂ}

variable {c : AlgChart p σ D} {y : CxPts p σ}

end GlobalTheory.ChernTop
end
end
