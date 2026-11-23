module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle471
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle065
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle467
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
import Formalism.LocalToGlobal.IndefiniteReal.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.GenFibreComp

theorem exists_fn_hom {F L : Type} [Field F] [Field L] {V : Scheme.{0}} [IsIntegral V] (p : V ⟶ Sp F)
    (g : Sp L ⟶ V) (hg : g (IsLocalRing.closedPoint L) = genericPoint V) (ψ : F →+* L) (hψ : g ≫ p = spMap ψ) :
    ∃ φ : V.functionField →+* L, φ.comp (GlobalTheory.Cartier.constFn p) = ψ := by
  have hs : g (IsLocalRing.closedPoint L) ⤳ genericPoint V := hg ▸ specializes_rfl
  refine ⟨(V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g).hom, ?_⟩
  have h1 : V.presheaf.germ ⊤ (genericPoint V) (TopologicalSpace.Opens.mem_top _) ≫ V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g
      = g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
    exact congrArg (g.app ⊤ ≫ ·) ((congrArg (· ≫ _) ((Spec (CommRingCat.of L)).presheaf.map_id _)).trans
      (Category.id_comp _))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      = CommRingCat.ofHom ψ := by
    rw [← Scheme.Hom.comp_appTop_assoc, hψ, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h1] at h2
  ext a
  have h3 := congrArg (fun t => t.hom a) h2
  refine Eq.trans ?_ h3
  have h4 : p.appLE ⊤ ⊤ le_top = p.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg (p.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)
  rw [← h4]
  rfl

theorem isProjOver_comp_equiv {F K : Type} [Field F] [Field K] (e : F ≃+* K) {X : Scheme.{0}} (p : X ⟶ Sp K)
    (h : IsProjOver p) : IsProjOver (p ≫ spMap e.toRingHom) := by
  have hi : spMap e.symm.toRingHom ≫ spMap e.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have hi' : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have : IsIso (spMap e.symm.toRingHom) := ⟨_, hi, hi'⟩
  have h1 := (GlobalTheory.ProjSpace.points_and_stability K 0).2.2.1 F e.symm.toRingHom X p h
  have h2 := (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ (inv (pullback.fst p (spMap e.symm.toRingHom))) _
    inferInstance h1
  convert h2 using 1
  rw [IsIso.eq_inv_comp, pullback.condition_assoc, hi, Category.comp_id]

theorem exists_vars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed (Xo := Xo) (c := c) → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hF hsm
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have := Z.jQ_open
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  have hgen : ∀ i : Comp Xo c, IsGenericPoint (genPt i) i.1 := fun i => CompSplitPfD.cspD_gen i.2
  have hpre : ∀ i : Comp Xo c, Z.jQ ⁻¹' connectedComponent (Z.jQ (genPt i)) = i.1 := fun i => by
    by_contra hn
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _
      ⟨_, PtComp.preimage_connectedComponent_mem Z hS (Z.jQ (genPt i))⟩ i fun h => hn (congrArg Subtype.val h))
      mem_connectedComponent (hgen i).mem
  let V : Comp Xo c → (gen Z).Opens := fun i => ⟨connectedComponent (Z.jQ (genPt i)), (hcc _).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have key : ∀ i, ∃ (Y : GlobalTheory.ProjVar.Var F) (ε : (V i).toScheme ≅ Y.X), Y.dim = Dw.dim ∧
      ε.hom ≫ Y.str = (V i).ι ≫ genStr Z ≫ spMap e.toRingHom := fun i => by
    have : IrreducibleSpace (V i).toScheme := Subtype.irreducibleSpace (hcc _).1.1
    have : IsIntegral (V i).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have hcl : IsClosedImmersion (V i).ι := IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
    have hp : IsProjOver ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) :=
      (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
    have hsd : SmoothOfRelativeDimension Dw.dim ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
      simpa using h
    have hr : Set.range (genSp i ≫ Z.jQ) ⊆ Set.range (V i).ι := by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, genSp, Scheme.fromSpecResidueField_apply]
      exact mem_connectedComponent
    let g : Sp (kap i) ⟶ (V i).toScheme := IsOpenImmersion.lift (V i).ι (genSp i ≫ Z.jQ) hr
    have hg : g ≫ (V i).ι = genSp i ≫ Z.jQ := IsOpenImmersion.lift_fac _ _ _
    have hgp : (V i).ι (g (IsLocalRing.closedPoint (kap i))) = Z.jQ (genPt i) := by
      exact (Scheme.Hom.comp_apply g (V i).ι _).symm.trans ((congrArg (fun t : Sp (kap i) ⟶ gen Z => t (IsLocalRing.closedPoint (kap i))) hg).trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg Z.jQ (Scheme.fromSpecResidueField_apply _ _))))
    have hgg : g (IsLocalRing.closedPoint (kap i)) = genericPoint (V i).toScheme := by
      have h1 : (V i).ι (genericPoint (V i).toScheme) ⤳ Z.jQ (genPt i) :=
        hgp ▸ (genericPoint_specializes _).map (V i).ι.continuous
      obtain ⟨a, ha⟩ := h1.mem_open Z.jQ.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
      have h2 : a = genPt i := CompSplitPfD.cspD_max i.2 (hgen i) a
        (Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 (ha ▸ h1))
      apply (V i).ι.isOpenEmbedding.injective
      rw [hgp, ← ha, h2]
    obtain ⟨φ, hφ⟩ := exists_fn_hom ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) g hgg
      ((algebraMap c.F (kap i)).comp e.toRingHom) (by
        rw [reassoc_of% hg, reassoc_of% Z.jQ_over, ← Category.assoc]
        exact (congrArg (· ≫ _) (Spec.map_preimage (genSp i ≫ strK)).symm).trans (Spec.map_comp _ _).symm)
    have : GeometricallyConnected ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
      rintro a ⟨P, hP, hPa⟩
      let χ : (V i).toScheme.functionField →+* Om i := (algebraMap (kap i) (Om i)).comp φ
      have hχ : χ.comp (GlobalTheory.Cartier.constFn ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)) =
          (algebraMap c.F (Om i)).comp e.toRingHom := by
        rw [RingHom.comp_assoc, hφ, IsScalarTower.algebraMap_eq c.F (kap i) (Om i), RingHom.comp_assoc]
      obtain ⟨b, hb⟩ := hF i (χ a) ⟨P.map e.toRingHom, (Polynomial.map_ne_zero_iff e.injective).2 hP, by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hχ, ← Polynomial.hom_eval₂, hPa, map_zero]⟩
      refine ⟨e.symm b, χ.injective ?_⟩
      rw [← hb]
      exact (RingHom.congr_fun hχ _).trans (by simp)
    exact GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  choose B ε hd hs using key
  have hrange : ∀ i, Set.range ((ε i).inv ≫ (V i).ι) = connectedComponent (Z.jQ (genPt i)) := fun i => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (ε i).inv.surjective.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
    rfl
  refine ⟨B, fun i => (ε i).inv ≫ (V i).ι, fun i => ⟨inferInstance, hd i, ?_, fun p hp => ?_⟩, fun z => ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [hrange]
    rw [← hpre] at hp
    exact hp
  · refine ⟨⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩, ?_, fun i hi => ?_⟩
    · beta_reduce
      rw [hrange]
      have h := (hgen ⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩).mem
      rw [← connectedComponent_eq (show Z.jQ _ ∈ connectedComponent z from h)]
      exact mem_connectedComponent
    · beta_reduce at hi
      rw [hrange] at hi
      apply Subtype.ext
      rw [← hpre, connectedComponent_eq hi]

end GlobalTheory.GenFibreComp
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtEx

theorem nonempty_basis_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n : ℕ} {v : Fin n → (epsR R ⟶ G')} (hb : IsLieBasis v) :
    Nonempty (Module.Basis (Fin n) R (TanM x G)) := by
  let u : Fin n → TanM x G := fun j => mkT (pushHom h (epsR R) (v j)) ((PullbackSections.isTangent_iff h _).1 (hb.1 j))
  have hcomb : ∀ (a : Fin n → R) (w : epsR R ⟶ G'), IsLieComb a v w ↔
      pushHom h (epsR R) w = tv (∑ i, a i • u i) := fun a w => by
    rw [PullbackSections.isLieComb_iff h, GlobalTheory.FlagMod.tv_sum']
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination R u) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact tv_mem W)
    refine (existsUnique_congr fun a => ?_).1 (hb.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (tanM_ext e).symm, fun e => by rw [e]⟩
  exact ⟨(Pi.basisFun R (Fin n)).map (LinearEquiv.ofBijective _ hbij)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_keyAt_of_sabMap (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hg : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, th, ⟨hw, hr⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev z M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev z M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ z he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp R ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  refine ⟨⟨GlobalTheory.GenericPol.toPolAV t M.n hg hp hA hK, hn, t.PP.rig, t.PP.rigGen, th, fun s => ?_, v, hb⟩, rfl,
    m.φ, he, w, rfl, m.cart, hw, hrig ▸ hr, fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, h₁, h₂⟩ := hne s
    exact ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  · refine (hth (j PUnit.unit) i _ h le_rfl).trans ?_
    exact congrArg (· * _) (GlobalTheory.LB.resG_self _ _)
  · exact hm' ▸ hv i

theorem smoothOfRelativeDimension_fibre {K : Type} [Field K] {z : Sp K ⟶ Y.X} {t : SAB H (Sp K)} (m : SABMap t Y.t z)
    (h : Set.range z ⊆ Set.range Y.j) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom := by
  obtain ⟨K', _, i, y, e⟩ := GlobalTheory.GenericPol.exists_lift z Y.j h
  obtain ⟨t', ⟨m₁⟩⟩ := GlobalTheory.ModFam.exists_sabPull (Out.specOf i) t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t' Y.j y Y.m (e ▸ n)
  have h₁ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m'.cart.1
      (GlobalTheory.ObjDim.smoothOfRelativeDimension Y.oF)
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace ↥t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have h₂ : SmoothOfRelativeDimension d t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m₁.cart.1 hd
  rw [← H1.dim_unique _ h₂ h₁ (eSec t'.G (default : PrimeSpectrum K'))]
  exact hd

theorem exists_keyAt_model (M : GChart Y) {K : Type} [Field K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (h : Set.range z ⊆ Set.range Y.j) (hpos : 1 ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) :
    ∃ x : KeyIn K, x.P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ KeyAt M z hz x := by
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull z Y.t
  obtain ⟨hp, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv m h
  have hg := smoothOfRelativeDimension_fibre m h
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis t.G hg
  obtain ⟨b⟩ := nonempty_basis_of_isLieBasis m.cart hv
  have hn : Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = M.n := by
    simpa using Fintype.card_congr (b.indexEquiv (GlobalTheory.FlagMod.lieBasis M.toMChart z hz))
  rw [hn] at hg hpos ⊢
  exact exists_keyAt_of_sabMap M z hz m hp hA hK hg hpos

end GlobalTheory.KeyAtEx
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtBC

theorem appLE_eq_iff_stalk {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {V : X.Opens} (hV : ∀ y, F y ∈ V) (s : ∀ j, Γ(X, V ⊓ L.U j)) (s' : L'.Sec) :
    (∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ (V ⊓ L.U (j PUnit.unit))),
      (F.appLE _ _ hle).hom (s (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i)) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ (V ⊓ L.U j) := fun y hy => ⟨hV y, mem_pull.1 hy.1⟩
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

theorem mem_of_comm {X X' T T' : Scheme.{0}} {F : X' ⟶ X} {π : X ⟶ T} {π' : X' ⟶ T'} {z : T' ⟶ T}
    (e : F ≫ π = π' ≫ z) {U : T.Opens} (hz : ⊤ ≤ z ⁻¹ᵁ U) (y : X') : F y ∈ π ⁻¹ᵁ U := by
  show π (F y) ∈ U
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hz (Set.mem_univ _)

theorem spMap_comp₀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : GChart Y} {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {z : Sp R ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U}
  {x : KeyIn R} {x' : KeyIn R'}

theorem keyAt_of_keyPB (h : KeyAt M z hz x) (h' : KeyPB x' x f) :
    KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x' := by
  obtain ⟨φ, he, w, hg, hp, hw, hr, hs, hv⟩ := h
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := h'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x.P.isLB w w' g g' Y.t.PP.isLB x'.P.isLB
  have he'' : eSec x'.P.A ≫ φ' ≫ φ = (spMap f ≫ z) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [Chart.dualMapR])
  have hq := hp'.comp hp
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, hq, (isGen_iff w'').2 (T.pgen_comp x.P.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _
      (rigPull_le φ z he Y.t.PP.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ' (spMap f) he' x.P.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
      (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp x.P.isLB (fun _ => he') r₀ r₁)
  · refine (appLE_eq_iff_stalk w'' (mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ x'.th).2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x.P.isLB (φ' (q y))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.1.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).1 hs' Z q y i k hi hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [← Category.assoc, hv', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
      hF, Category.assoc]
    rfl

theorem keyPB_of_keyAt (h : KeyAt M z hz x) (h' : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x') :
    KeyPB x' x f := by
  obtain ⟨φ, he, w, hg, hc, hw, hr, hs, hv⟩ := h
  obtain ⟨φ'', he'', w'', hg'', hc'', hw'', hr'', hs'', hv''⟩ := h'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x'.P.A.left ⟶ x.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x.P.A.hom = x'.P.A.hom ≫ spMap f :=
    ⟨hp.lift φ'' (x'.P.A.hom ≫ spMap f) (by rw [hc''.1.w, Category.assoc]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x'.P.A ≫ φ' = spMap f ≫ eSec x.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', Category.assoc, Category.assoc, he]
    · have a₁ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      have a₂ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel Y.t.PP.isLB w w'' g g'' x.P.isLB x'.P.isLB
  have r := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _ (rigPull_le φ z he Y.t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
    (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).1 hr''
  refine ⟨φ', he', w', hg''.trans hg.symm, Chart.dualMapR f, hc.cancel hc'' hw0,
    (isGen_iff w').2 (T.pgen_cancel Y.t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ' (spMap f) he' x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel Y.t.PP.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).2 fun Z q y i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (φ (φ' (q y)))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (appLE_eq_iff_stalk w'' (mem_of_comm hc''.1.w (le_preimage_comp _ hz)) M.θ x'.th).1 hs'' Z q y j k hj hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
        Category.assoc]
      rfl
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyAtBC
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3

theorem finiteTypes_of_full_heckeAlgebra_eigensystems : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Lam3 Z := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hIR
  have lab := GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  let cOf : D.what₂.FT → A3.fam3.base3.Ix := fun σ => (lab σ).choose
  have hc : ∀ σ, HasLab Y σ (cOf σ) := fun σ => (lab σ).choose_spec
  have rat := GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have ind := GlobalTheory.T.iSupIndep_finiteTypeComponents_thetaLiftForms h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have dim := GlobalTheory.T.liftLabelPart_finrank_eq_rowsPart_finrank h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have cnt := GlobalTheory.T.card_baseRows_label_eq_rowsPart_finrank h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost cOf hc
  have lam := GlobalTheory.T.liftScalar_eq_labelScalar h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  refine ⟨cOf, fun i c => ?_, fun i t σ ht hne => lam σ (cOf σ) i t (hc σ) ht hne, fun c => cnt c⟩
  have hind : iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) :=
    (ind i).comp Subtype.val_injective
  refine ⟨hind, ?_⟩
  rw [rat i c]
  have hle : (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) ≤ (R.Wp3 i c).comap (Y.mj.eW i) := by
    refine iSup_le fun σ => ?_
    have := (hc σ.1).1 i
    rw [σ.2] at this
    exact Submodule.map_le_iff_le_comap.1 this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [dim i c, ← cnt c, Formalism.IndefR.Cx.finrank_iSup_eq_sum _ hind]
  rw [Finset.sum_subtype (Finset.univ.filter (fun σ => cOf σ = c)) (p := fun σ => cOf σ = c) (by simp)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact hIR ((i : ℕ) + 1) (by omega) (by omega) σ.1

end GlobalTheory.Mem.R3
end
