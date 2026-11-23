module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3327
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle443
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additiveFamily_trivial_of_quotient_pullback_trivial : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left) (P' : LB (A' ⊗ B).left) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → IsMonHom q → P'.IsLB → IsAdditive P' → LBIso (ev P' (fst A B ≫ q) (snd A B)) P → ∀ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB → IsAdditive M → Triv (ev M (fst A T ≫ q) (snd A T)) → Triv M := by
  first | exact @GlobalTheory.DualInjPull.triv_of_triv_pull | exact GlobalTheory.DualInjPull.triv_of_triv_pull | (intros; apply GlobalTheory.DualInjPull.triv_of_triv_pull <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibProperClosed

theorem isClosed_image_closure : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y P : Scheme.{0}) (q : Y ⟶ P)
    (s : P ⟶ Spec (CommRingCat.of O)) (C : Set Y), IsProper s → IsImmersion q →
    IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) →
    IsIrreducible C → (∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O) →
    IsClosed (q '' closure C) := by
  intro O _ _ _ hI Y P q s C hs hq hk hC hy
  set U : Set P := coborder (Set.range q) with hUdef
  have hUo : IsOpen U := q.isLocallyClosed_range.isOpen_coborder
  have hqU : Set.range q = U ∩ closure (Set.range q) := (coborder_inter_closure).symm
  have hZsub : closure (q '' C) ⊆ closure (Set.range q) := closure_mono (Set.image_subset_range _ _)
  have himg : q '' closure C = closure (q '' C) ∩ U := by
    rw [q.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range, hqU]
    ext x
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hZsub h1⟩
  have hZc : IsClosed (closure (q '' C)) := isClosed_closure
  have hZirr : IsIrreducible (closure (q '' C)) := (hC.image q q.continuous.continuousOn).closure

  have hZk : _root_.IsPreconnected (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) := by
    let I := Scheme.IdealSheafData.vanishingIdeal (⟨closure (q '' C), hZc⟩ : TopologicalSpace.Closeds P)
    have hrange : Set.range I.subschemeι = closure (q '' C) := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
    haveI : IsProper (I.subschemeι ≫ s) := inferInstance
    have hne : Nonempty I.subscheme := by
      obtain ⟨c, hc⟩ := hC.nonempty
      have : q c ∈ Set.range I.subschemeι := by rw [hrange]; exact subset_closure ⟨c, hc, rfl⟩
      obtain ⟨w, -⟩ := this
      exact ⟨w⟩
    have hpc : _root_.IsPreconnected (Set.univ : Set I.subscheme) := by
      rw [← I.subschemeι.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hrange]
      exact hZirr.2.isPreconnected
    haveI : ConnectedSpace I.subscheme := { toPreconnectedSpace := ⟨hpc⟩, toNonempty := hne }
    haveI hsp := GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms GlobalTheory.T.formalAlgebraisation_morphisms' O _
      (I.subschemeι ≫ s) inferInstance inferInstance
    have hT : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s)) =
        (I.subschemeι ≫ s) ⁻¹' {IsLocalRing.closedPoint O} := by
      have h := Scheme.Pullback.range_fst (I.subschemeι ≫ s)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
      rw [GlobalTheory.SpecialConn.range_residue] at h
      exact h
    have hR : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s) ≫ I.subschemeι) =
        closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hT, ← hrange, Set.inter_comm,
        ← Set.image_preimage_eq_inter_range]
      rfl
    rw [← hR]
    exact isPreconnected_range (Scheme.Hom.continuous _)

  have hkU : IsClosed ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U) := by
    let res := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
    haveI : IsClosedImmersion res :=
      IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
    haveI : IsProper (pullback.snd (q ≫ s) res ≫ res) := inferInstance
    haveI : IsProper ((pullback.fst (q ≫ s) res ≫ q) ≫ s) := by
      rw [Category.assoc, pullback.condition]; infer_instance
    haveI : IsProper (pullback.fst (q ≫ s) res ≫ q) := IsProper.of_comp _ s
    have hF : Set.range (pullback.fst (q ≫ s) res) = (q ≫ s) ⁻¹' {IsLocalRing.closedPoint O} := by
      have h := Scheme.Pullback.range_fst (q ≫ s) res
      rw [GlobalTheory.SpecialConn.range_residue] at h
      exact h
    have hcl := (pullback.fst (q ≫ s) res ≫ q).isClosedMap _
      ((isClosed_closure (s := C)).preimage (pullback.fst (q ≫ s) res).continuous)
    have e : (pullback.fst (q ≫ s) res ≫ q) '' (pullback.fst (q ≫ s) res ⁻¹' closure C) =
        (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range, hF]
      change q '' (closure C ∩ q ⁻¹' (s ⁻¹' {IsLocalRing.closedPoint O})) = _
      rw [Set.image_inter_preimage, himg]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rw [← e]; exact hcl
  have hne : ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U).Nonempty := by
    obtain ⟨y, hyC, hy⟩ := hy
    have h1 : q y ∈ closure (q '' C) ∩ U := himg ▸ ⟨y, hyC, rfl⟩
    exact ⟨q y, ⟨h1.1, hy⟩, h1.2⟩
  have hZkU : closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} ⊆ U := by
    intro z hz
    by_contra hzU
    obtain ⟨w, hw, hw1, hw2⟩ := hZk U _ hUo hkU.isOpen_compl
        (fun x _ => by
          by_cases h : x ∈ U
          · exact Or.inl h
          · exact Or.inr fun h' => h h'.2)
        (by obtain ⟨x, hx1, hx2⟩ := hne; exact ⟨x, hx1, hx2⟩) ⟨z, hz, fun h => hzU h.2⟩
    exact hw2 ⟨hw, hw1⟩
  have hZU : closure (q '' C) ⊆ U := by
    intro z hz
    by_contra hzU
    have hcl : IsClosed (s '' (closure (q '' C) \ U)) := s.isClosedMap _ (hZc.sdiff hUo)
    have hsp : s z ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (s z).2.ne_top)
    obtain ⟨z', ⟨hz'Z, hz'U⟩, hz'⟩ := hsp.mem_closed hcl ⟨z, ⟨hz, hzU⟩, rfl⟩
    exact hz'U (hZkU ⟨hz'Z, hz'⟩)
  rw [himg, Set.inter_eq_left.2 hZU]
  exact hZc

end GlobalTheory.FibProperClosed
end
end

section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.zariskiConnectedness_isPreconnected_fibre_affine : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) [IsProper f] [IsAffine X] [IsLocallyNoetherian X], Function.Bijective f.appTop → ∀ x : X, _root_.IsPreconnected (f.base ⁻¹' {x}) := by
  first | exact @GlobalTheory.ZariskiConn.isPreconnected_fibre | exact GlobalTheory.ZariskiConn.isPreconnected_fibre | (intros; apply GlobalTheory.ZariskiConn.isPreconnected_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ (N : ℕ) (X : Scheme.{0}) (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (H : Scheme.{0}) (i : H ⟶ X)
    (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left)
    (Φ : AH ⟶ BH), IsClosedImmersion c ∧ IsOpenImmersion i ∧
    IsGrpPullback AH A (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φA ∧ IsGrpPullback BH B (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) φB ∧ IsMonHom Φ ∧
    LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))) = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  first | (exact @GlobalTheory.HomFixMat.exists_locClosed_homFix) | (exact GlobalTheory.HomFixMat.exists_locClosed_homFix) | (intros; apply GlobalTheory.HomFixMat.exists_locClosed_homFix  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull_chart {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (t' : SAB H S') (m : SABMap t' t f), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  refine ⟨⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act,
    (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_⟩, ⟨cubeMapOf h, h, rfl, hact, hc'⟩,
    ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ _ rfl⟩⟩
  · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)

theorem proper_ample_kTriv {S S' : Scheme.{0}} [IsAffine S'] {f : S' ⟶ S} {t : SAB H S} {u u' : SAB H S'}
    (m : SABMap u t f) (m' : SABMap u' t f) (hP : IsProper u.G.hom) (hA : Out.RelAmple u.G u.PP.L)
    (hK : Out.KTriv u.G u.PP.L) : IsProper u'.G.hom ∧ Out.RelAmple u'.G u'.PP.L ∧ Out.KTriv u'.G u'.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ m')
  obtain ⟨w, hw, -⟩ := n.lin
  exact ⟨MorphismProperty.of_isPullback n.cart.1 hP,
    relAmple_pull n.cart.1 u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S') (fun _ => trivial) hA,
    kTriv_pull n.cart u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem bijective_appLE {X X' : Scheme.{0}} (j : X' ⟶ X) [IsOpenImmersion j] {U : X.Opens} {U' : X'.Opens}
    (h : j ''ᵁ U' = U) (e : U' ≤ j ⁻¹ᵁ U) : Function.Bijective (j.appLE U U' e).hom := by
  subst h
  rw [← Scheme.Hom.appIso_hom']
  exact ConcreteCategory.bijective_of_isIso (j.appIso U').hom

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  rw [← Scheme.Hom.appLE_map m h (homOfLE e).op]
  rfl

theorem app_appLE {X X' G G' : Scheme.{0}} {φ : G' ⟶ G} {p' : G' ⟶ X'} {p : G ⟶ X} {j : X' ⟶ X}
    (sq : φ ≫ p = p' ≫ j) {U : X.Opens} {U' : X'.Opens} (e : U' ≤ j ⁻¹ᵁ U) {O : G.Opens} (h : O ≤ p ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ O ≤ p' ⁻¹ᵁ U') (r : Γ(X, U)) :
    (φ.app O).hom ((p.appLE U O h).hom r) = (p'.appLE U' (φ ⁻¹ᵁ O) h').hom ((j.appLE U U' e).hom r) := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 3

theorem valR_comp_appLE {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) {O : Z.Opens}
    {O' : Y.Opens} (e : O' ≤ m ⁻¹ᵁ O) (hz : ⊤ ≤ z ⁻¹ᵁ O') (f : Γ(Z, O)) :
    valR (z ≫ m) O f = valR z O' ((m.appLE O O' e).hom f) := by
  rw [GlobalTheory.CechKS.valR_comp_app, ← GlobalTheory.CechKS.valR_resG z e hz]
  rfl

theorem isKS_of_openImmersion {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {j : X' ⟶ X} [IsOpenImmersion j]
    (m : SABMap t' t j) (cp : ChartPull t'.PP.L t.PP.L m.φ) (V : X.Opens) (U : X.affineOpens) (hUV : U.1 ≤ V)
    (U' : X'.affineOpens) (hU : j ''ᵁ U'.1 = U.1) (ψ : Γ(X, U.1) ≃+* Γ(X', U'.1)) (e : U'.1 ≤ j ⁻¹ᵁ U.1)
    (hψ : ∀ r, ψ r = (j.appLE U.1 U'.1 e).hom r) (hch : chart U' ≫ j = spMap ψ.toRingHom ≫ chart U) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left))
    (hv : ∀ i, IsTanAtG t (chart U) (v i)) (hv' : ∀ i, IsTanAtG t' (chart U') (v' i))
    (hvv : ∀ i, v' i ≫ m.φ = spMap (dualMap ψ.toRingHom) ≫ v i)
    (D : Γ(X, U.1) → Γ(X, U.1)) (D' : Γ(X', U'.1) → Γ(X', U'.1)) (hD : ∀ r, D' (ψ r) = ψ (D r))
    (Θ : Matrix (Fin n) (Fin n) Γ(X', U'.1)) (h : IsKS t' ⊤ U' v' D' Θ) : IsKS t V U v D (Θ.map ψ.symm) := by
  obtain ⟨J, W, c, d, hcov, hWc, hd, hl, hr⟩ := h
  obtain ⟨hoi, hrange⟩ := GlobalTheory.sabMap_isOpenImmersion_opensRange E H X X' t t' j m
  have sq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  rw [inf_top_eq] at hcov
  have hWU : ∀ i, W i ≤ t'.G.hom ⁻¹ᵁ U'.1 := fun i => hcov ▸ le_iSup W i
  have hpre : t'.G.hom ⁻¹ᵁ U'.1 = m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, sq, Scheme.Hom.comp_preimage, ← hU, Scheme.Hom.preimage_image_eq]
  have hle : ∀ i {O : t.G.left.Opens}, O ≤ m.φ ''ᵁ W i → m.φ ⁻¹ᵁ O ≤ W i := fun i O hO =>
    (m.φ.preimage_mono hO).trans (m.φ.preimage_image_eq (W i)).le
  choose d₂ hd₂ hd₂' using fun i => GlobalTheory.LogKS.isField_image _ _ m.φ (W i) (d i) (hd i)
  refine ⟨J, fun i => m.φ ''ᵁ W i, fun i => cp.idx (c i), d₂, ?_, fun i => ?_, hd₂, fun i hW r => ?_, ?_⟩
  · rw [← Scheme.Hom.image_iSup, hcov, hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, hrange, inf_eq_left.2 hUV,
      inf_eq_right]
    apply t.G.hom.preimage_mono
    rw [← hU]
    exact j.image_le_opensRange _
  · rintro _ ⟨y, hy, rfl⟩
    exact cp.le _ (hWc i hy)
  · have hinj : Function.Injective (m.φ.app (m.φ ''ᵁ W i)).hom :=
      (ConcreteCategory.bijective_of_isIso (m.φ.app (m.φ ''ᵁ W i))).1
    apply hinj
    have h1 := hle i le_rfl
    rw [hd₂' i _ le_rfl, app_appLE sq e hW (h1.trans (hWU i)), app_appLE sq e hW (h1.trans (hWU i)), ← hψ, ← hψ,
      ← hD, ← resG_appLE _ _ (hWU i) h1, (hd i).2.2 _ _ h1 le_rfl, hl i (hWU i), resG_appLE]
  · intro i i' O hO f S _ φ g₀ w hg hO₀ hT
    have hOi : O ≤ m.φ ''ᵁ W i := hO.trans inf_le_left
    have hOi' : O ≤ m.φ ''ᵁ W i' := hO.trans inf_le_right
    obtain ⟨g₁, rfl⟩ : ∃ g₁ : Sp S ⟶ t'.G.left, g₁ ≫ m.φ = g₀ :=
      ⟨IsOpenImmersion.lift m.φ g₀ (by
        rintro _ ⟨y, rfl⟩
        obtain ⟨z, -, hz⟩ := hOi (hO₀ (Set.mem_univ y))
        exact ⟨z, hz⟩), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨φ₁, rfl⟩ : ∃ φ₁ : Γ(X', U'.1) →+* S, φ₁.comp ψ.toRingHom = φ :=
      ⟨φ.comp ψ.symm.toRingHom, RingHom.ext fun r => by simp⟩
    have hg₁ : g₁ ≫ t'.G.hom = spMap φ₁ ≫ chart U' := by
      rw [← cancel_mono j, Category.assoc, ← sq, ← Category.assoc, hg, Category.assoc, hch, ← Category.assoc]
      congr 1
      exact Spec.map_comp (CommRingCat.ofHom ψ.toRingHom) (CommRingCat.ofHom φ₁)
    choose w₁ hw₁ hT₁ using fun a => GlobalTheory.TransLift.lift_isTranslate E H X X' t t' j m _ _ ψ.toRingHom (chart U) (chart U') hch
      (v a) (v' a) (hv a) (hv' a) (hvv a) S φ₁ g₁ hg₁ (w a) (hT a)
    obtain rfl : w = fun a => w₁ a ≫ m.φ := funext fun a => (hw₁ a).symm
    have hO₁ : ⊤ ≤ g₁ ⁻¹ᵁ (m.φ ⁻¹ᵁ O) := hO₀
    have key := hr i i' (m.φ ⁻¹ᵁ O) (le_inf (hle i hOi) (hle i' hOi')) ((m.φ.app O).hom f) S φ₁ g₁ w₁ hg₁ hO₁ hT₁
    have hgc : ⊤ ≤ g₁ ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) :=
      hO₁.trans (g₁.preimage_mono (le_inf ((hle i hOi).trans (hWc i)) ((hle i' hOi').trans (hWc i'))))
    have hwc : ∀ b, ⊤ ≤ w₁ b ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) := fun b =>
      GlobalTheory.CechKS.le_preimage_of_red (GlobalTheory.LogKS.IsTranslate.fst_comp E H X' t' _ S φ₁ (chart U') g₁ (v' b) (w₁ b) hg₁ (hv' b) (hT₁ b)) hgc
    have hgp := GlobalTheory.chartPull_g_appLE _ _ _ _ m.φ cp (c i) (c i')
    have hgi : ((t'.PP.L.g (c i) (c i'))⁻¹).val = (m.φ.appLE _ _
        (le_inf (inf_le_left.trans (cp.le (c i))) (inf_le_right.trans (cp.le (c i'))))).hom
        ((t.PP.L.g (cp.idx (c i)) (cp.idx (c i')))⁻¹).val :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hgp, ← map_mul, Units.mul_inv, map_one])
    rw [GlobalTheory.CechKS.valR_comp_app, map_sub, hd₂' i O hOi, hd₂' i' O hOi', key]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hgp, hgi]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (by simp) (congrArg₂ (· * ·) (congrArg TrivSqZeroExt.snd ?_) ?_))
      (congrArg TrivSqZeroExt.snd ?_)
    · exact (valR_comp_appLE (w₁ b) m.φ _ (hwc b) _).symm
    · exact (valR_comp_appLE g₁ m.φ _ hgc _).symm
    · exact (GlobalTheory.CechKS.valR_comp_app (w₁ a) m.φ O f).symm

def derivMap {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) : Derivation ℤ B B :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap
    ((ψ.toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom).comp ψ.symm.toAddMonoidHom)) fun a b => by
      simp

theorem derivMap_apply {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) (r : A) :
    derivMap ψ D (ψ r) = ψ (D r) := by
  simp [derivMap]

theorem exists_isKS_of_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens), U.1 ≤ V → ∀ (t' : SAB H (Sp Γ(X, U.1))), Nonempty (SABMap t' t (chart U)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U hUV t' ⟨m'⟩ hP hA hK n v hv hb D
  obtain ⟨u, m, ⟨cp⟩⟩ := exists_pull_chart (chart U) t
  obtain ⟨hP', hA', hK'⟩ := proper_ample_kTriv m' m hP hA hK
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let U' : (Sp Γ(X, U.1)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hU : chart U ''ᵁ U'.1 = U.1 := by
    show chart U ''ᵁ ⊤ = U.1
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact U.2.opensRange_fromSpec
  have e : U'.1 ≤ chart U ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  let ψ : Γ(X, U.1) ≃+* Γ(Sp Γ(X, U.1), U'.1) := RingEquiv.ofBijective _ (bijective_appLE (chart U) hU e)
  have hch : chart U' ≫ chart U = spMap ψ.toRingHom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec (chart U) U.2 U'.2 e).symm
  obtain ⟨v', hvv, hv', hb'⟩ := GlobalTheory.SabTan.tanBasis_sabMap E H X _ t u (chart U) m _ _ ψ.toRingHom (chart U) (chart U') hch n v hv hb
  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_cech_kodairaSpencer_class_abelianTriple E H _ u hP' hA' hK' U' n v' hv' hb' (derivMap ψ D)
  exact ⟨_, isKS_of_openImmersion m cp V U hUV U' hU ψ e (fun _ => rfl) hch v v' hv hv' hvv D _
    (derivMap_apply ψ D) Θ hΘ⟩

end GlobalTheory.KSOpen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.formalFunctions_exists_globalFunction_of_thickenings : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ (X : Over (Sp A)), IsProper X.hom → ∀ f : ∀ e : ℕ, Γ((thickObj A I e X).left, ⊤), (∀ e, (thickMap A I e X).appTop.hom (f (e + 1)) = f e) → ∃ s : Γ(X.left, ⊤), ∀ e, (pullback.fst X.hom (thick A I e)).appTop.hom s = f e := by
  first | exact @GlobalTheory.FormalFunctions.exists_of_thick | exact GlobalTheory.FormalFunctions.exists_of_thick | (intros; apply GlobalTheory.FormalFunctions.exists_of_thick <;> assumption)
end
