module

public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Development.EtaleCohomology.EtaleSheaves.Bundle004
public import Development.EtaleCohomology.EtaleSheaves.Bundle045
import Development.EtaleCohomology.EtaleSheaves.Bundle043
public import Development.EtaleCohomology.EtaleSheaves.Bundle046
public import Development.EtaleCohomology.EtaleSheaves.Bundle056
public import Development.EtaleCohomology.EtaleSheaves.Bundle006
public import Development.EtaleCohomology.EtaleSheaves.Bundle044
public import Development.EtaleCohomology.EtaleSheaves.Bundle007
public import Development.EtaleCohomology.EtaleSheaves.Bundle014
public import Development.EtaleCohomology.EtaleSheaves.Bundle026
public import Development.EtaleCohomology.EtaleSheaves.Bundle074
public import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
public import Development.EtaleCohomology.EtaleSheaves.Bundle054
public import Development.EtaleCohomology.TateTwists.Bundle035
public import Development.EtaleCohomology.TateTwists.Bundle033
public import Development.EtaleCohomology.EtaleSheaves.Bundle068
public import Development.EtaleCohomology.EtaleSheaves.Bundle069
public import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.HkpullComp
public import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Development.EtaleCohomology.EtaleSheaves.Bundle075
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.EtaleCohomology.EtaleSheaves.Bundle008

@[expose] public section

section

namespace LateralTheory.E.LeafA6nat_xy7V2Cut

theorem kumTExists : LateralTheory.E.CupProductRingLaws.LeafKumTExists := fun q _ =>
  ⟨_, LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange q⟩

theorem oneSpec : LateralTheory.E.CupProductRingLaws.LeafOneSpec :=
  LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of
    (LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit LateralTheory.E.UnitSections.LeafUnitSec_of)
    LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of

theorem etaleFirstChernClass_represented_by_chern_cocycle : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle :=
  have hr := LateralTheory.E.LeafRootLocPf.LeafRootLoc_of
  LateralTheory.E.ChernClassRootLocalization.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique
    (LateralTheory.E.ChernClassEvaluation.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness LateralTheory.E.LeafEvMkPf.LeafEvMk_of
      (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor hr kumTExists) (LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor.etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor hr kumTExists)
      (LateralTheory.E.ChernCocycleEdgeCoboundary.etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots hr) (LateralTheory.E.ChernCocycleFaceFormulas.etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r hr) (LateralTheory.E.ChernCocycleFaceDegeneracyIdentities.etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization hr))
    hr

theorem natKum : LateralTheory.E.CupProductRingLaws.LeafNatKum := fun q _ =>
  ((LateralTheory.Fix.EtaleKummerClassExplicitCocycle.holds_of LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange) q).2.1

theorem goal_of : LateralTheory.E.D2.LeafA6nat := fun q _ =>
  ⟨LateralTheory.E.LeafNatCupPf.LeafNatCup_of LateralTheory.Fix.CupProductTensor.cupSpec q,
   LateralTheory.E.LeafNatOnePf.LeafNatOne_of oneSpec q,
   LateralTheory.E.FirstChernNaturality.etale_first_chern_class_natural_of_spec etaleFirstChernClass_represented_by_chern_cocycle q,
   natKum q⟩

end LateralTheory.E.LeafA6nat_xy7V2Cut
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StalkVanishing
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem goal_of (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) : LateralTheory.E.LeafVan0Pf.LeafVanStalk := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m hsub y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i toK ι p hp U m y ?_
  intro A _ t hA
  have := hsub A t hA
  exact Subsingleton.elim _ _

end LateralTheory.E.StalkVanishing
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafPtVPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling
  LateralTheory.E.SecondDegreeKilling.Comp LateralTheory.E.SecondDegreeKilling.Nbhd

theorem isZero_sec_empty (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    IsZero (F.obj.obj (op X)) :=
  (Sheaf.isTerminalOfBotCover F X (Scheme.bot_mem_grothendieckTopology (P := @Etale) X)).isZero

theorem isZero_free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext1
  ext1 U
  by_cases hU : IsEmpty U.unop
  · exact (isZero_sec_empty R ((free R).obj (yoneda.obj X)) U.unop).eq_of_tgt _ _
  · have hE : IsEmpty (ULift.{1} (unop U ⟶ X)) := ⟨fun f => by
      obtain ⟨x⟩ := not_isEmpty_iff.1 hU; exact IsEmpty.false (f.down.base x)⟩
    haveI : Subsingleton ↑(((freeP R).obj (yoneda.obj X)).obj U) := by
      change Subsingleton (ULift.{1} (unop U ⟶ X) →₀ ULift.{1} R); infer_instance
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

theorem isZero_chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rcases p with _ | k
    · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) 0)
    · exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro j; change -(j : ℤ) ≠ (k : ℤ) + 1; omega)
  · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) p)

theorem isIso_inr (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (hK : ∀ n, IsZero (K.X n)) :
    IsIso (mappingCone.inr φ) := by
  have : ∀ p, IsIso ((mappingCone.inr φ).f p) := fun p => ⟨⟨(mappingCone.snd φ).v p p (add_zero p), by simp, by
    rw [← mappingCone.id_X φ p (p + 1) rfl, (hK (p + 1)).eq_of_tgt ((mappingCone.fst φ).1.v p (p + 1) rfl) 0]
    simp⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem fgt_bij (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} [IsEmpty X] {E : Spc}
    (f : sch.obj X ⟶ E) (n : ℤ) : Function.Bijective (fgt R f F n) := by
  haveI := isIso_inr R ((chains R).map f) (isZero_chains_empty R X)
  exact hH.1 R (mappingCone.inr ((chains R).map f)) F n

theorem rpl_zero (hH : Hyps) (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') [IsEmpty U']
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (he : pl q i e n = 0)
    (x : Hrel (ZMod q) (sch.map f) (tw q i) n) : rpl q i f f' u e comm n x = 0 := by
  apply (fgt_bij hH (ZMod q) (tw q i) (sch.map f') n).1
  rw [map_zero]
  refine (relNat (ZMod q) (tw q i) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) n x).trans ?_
  change pl q i e n _ = 0
  rw [he]; rfl

theorem isEmpty_pullback_closed_subscheme_section_into_complement {B W Y S : Scheme.{0}} (ι : W ⟶ B) (V : B.Opens) (hVW : (V : Set B) = (Set.range ι)ᶜ)
    (p : Y ⟶ B) (s : S ⟶ B) (hs : Set.range ⇑s ⊆ (V : Set B)) :
    IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun x => by
  have h1 : (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s ≫ s) x = (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x := by
    rw [pullback.condition]
  have h2 : (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x ∈ (V : Set B) := by
    rw [← h1]; apply hs; simp only [Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
  rw [hVW] at h2; simp only [Scheme.Hom.comp_apply] at h2; exact h2 ⟨_, rfl⟩⟩

theorem LeafPtV_of : LateralTheory.E.SecondDegreeKilling.LeafPtV := by
  intro hH q _ k _ hq i B W Y Y' toK ι _ V hVW p g hp hgp U A _ t hA hV m hpl y
  haveI := isEmpty_pullback_closed_subscheme_section_into_complement ι V hVW (g ≫ p) (t ≫ U.hom) hV
  let wA : pullback (pullback.snd (g ≫ p) (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶
      pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι :=
    pullback.map _ ι _ ι (fibMap g p (t ≫ U.hom)) (𝟙 W) (𝟙 B)
      (by rw [Category.comp_id, ← Category.assoc (fibMap g p (t ≫ U.hom)), pullback.lift_snd, Category.comp_id]) (by simp)
  have commA : prS (g ≫ p) ι (t ≫ U.hom) ≫ fibMap g p (t ≫ U.hom) = wA ≫ prS p ι (t ≫ U.hom) :=
    (pullback.lift_fst _ _ _).symm
  have hA : prS p ι (t ≫ U.hom) ≫ tY p U t = tW p ι U t ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have hB : prS (g ≫ p) ι (t ≫ U.hom) ≫ tY (g ≫ p) U t = tW (g ≫ p) ι U t ≫ prU (g ≫ p) ι U :=
    (pullback.lift_fst _ _ _).symm
  have hC : prU (g ≫ p) ι U ≫ mY p g U = mW p g ι U ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have E1 : tY (g ≫ p) U t ≫ mY p g U = fibMap g p (t ≫ U.hom) ≫ tY p U t := by
    simp only [tY, mY, fibMap, pullback.map_comp, Category.id_comp, Category.comp_id]
  have c1 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (tY (g ≫ p) U t ≫ mY p g U) =
      (tW (g ≫ p) ι U t ≫ mW p g ι U) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mY p g U) hB).trans ((Category.assoc _ _ _).trans
      ((congrArg (tW (g ≫ p) ι U t ≫ ·) hC).trans (Category.assoc _ _ _).symm)))
  have c2 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (fibMap g p (t ≫ U.hom) ≫ tY p U t) =
      (wA ≫ tW p ι U t) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ tY p U t) commA).trans ((Category.assoc _ _ _).trans
      ((congrArg (wA ≫ ·) hA).trans (Category.assoc _ _ _).symm)))
  have E2 : tW (g ≫ p) ι U t ≫ mW p g ι U = wA ≫ tW p ι U t := by
    simp only [tW, mW, wA, pullback.map_comp]
    congr 1
  rw [rpl_comp q i _ _ _ _ _ _ _ _ _ c1, rpl_congr q i _ _ _ _ _ _ c1 c2 E2 E1, ← rpl_comp q i _ _ _ _ _ hA _ _ commA c2]
  exact rpl_zero hH q i _ _ _ _ commA m hpl _

end LateralTheory.E.LeafPtVPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LocSecPfC

variable (R : Type) [CommRing R] (X : Scheme.{0})

def eqv (G : Shv R) : ((free R).obj (yoneda.obj X) ⟶ G) ≃ Sec G X :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ G).trans <|
  (((ModuleCat.adj (ULift.{1} R)).whiskerRight (C := Scheme.{0}ᵒᵖ)).homEquiv (yoneda.obj X ⋙ uliftFunctor.{1}) G.obj).trans
  (uliftYonedaEquiv.{1} (X := X) (F := G.obj ⋙ forget _))

theorem eqv_apply (G : Shv R) (f : (free R).obj (yoneda.obj X) ⟶ G) :
    eqv R X G f = (f.hom.app (op X)).hom (freeGen R _ X (𝟙 X)) := by
  rfl

def eqvAdd (G : Shv R) : ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X :=
  { eqv R X G with
    map_add' := fun f g => by
      change eqv R X G (f + g) = eqv R X G f + eqv R X G g
      rw [eqv_apply, eqv_apply, eqv_apply]
      rfl }

theorem homSec : LateralTheory.E.LocSecPfB.HomSec := by
  intro R _ X
  refine ⟨eqvAdd R X, fun φ f => ?_⟩
  change eqv R X _ (f ≫ φ) = Sec.map φ (eqv R X _ f)
  rw [eqv_apply, eqv_apply]
  rfl

theorem LocSec_of (h2 : LateralTheory.E.LocSecPfB.ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPfB.LocSec_of homSec h2

end LateralTheory.E.LocSecPfC
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.ClassSecPf

section
variable {R : Type} [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ)

abbrev S : ShortComplex (ModuleCat.{1} (ULift.{1} R)) :=
  (LateralTheory.E.LeafLocPf.secCx F X).sc' (n - 1) n (n + 1)

def fz (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) : (free R).obj (yoneda.obj X) ⟶ (res R F).X n :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((free R).obj (yoneda.obj X))).inv ≫ (z : Cochain _ _ n).v 0 n (zero_add n)

theorem fz_add (z w : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    fz X F n (z + w) = fz X F n z + fz X F n w := by
  simp [fz]

theorem fz_mk (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X n) (hf : f ≫ (res R F).d n (n + 1) = 0) :
    fz X F n (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf) = f := by
  unfold fz
  rw [Cocycle.fromSingleMk_coe]
  erw [Cochain.fromSingleMk_v f (zero_add n)]
  simp

theorem exists_mk (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    ∃ (hf : fz X F n z ≫ (res R F).d n (n + 1) = 0),
      Cocycle.fromSingleMk (fz X F n z) (zero_add n) (n + 1) rfl hf = z := by
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
  rw [fz_mk]
  exact ⟨hf, rfl⟩

variable (e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X)
  (he : ∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f))

def ee (k : ℤ) : ((free R).obj (yoneda.obj X) ⟶ (res R F).X k) ≃+ (LateralTheory.E.LeafLocPf.secCx F X).X k :=
  e ((res R F).X k)

include he in
theorem ee_comp (i j : ℤ) (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X i) :
    ee X F e j (f ≫ (res R F).d i j) = ((LateralTheory.E.LeafLocPf.secCx F X).d i j).hom (ee X F e i f) :=
  he _ f

include he in
theorem mem_ker (f : (free R).obj (yoneda.obj X) ⟶ (res R F).X n) (hf : f ≫ (res R F).d n (n + 1) = 0) :
    (show (S X F n).X₂ from ee X F e n f) ∈ LinearMap.ker (S X F n).g.hom := by
  rw [LinearMap.mem_ker]
  change ((LateralTheory.E.LeafLocPf.secCx F X).d n (n + 1)).hom (ee X F e n f) = 0
  rw [← ee_comp X F e he, hf, map_zero]

def cyc (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) : LinearMap.ker (S X F n).g.hom :=
  ⟨ee X F e n (fz X F n z), mem_ker X F n e he _ (exists_mk X F n z).1⟩

theorem cyc_add (z w : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    cyc X F n e he (z + w) = cyc X F n e he z + cyc X F n e he w := by
  apply Subtype.ext
  change ee X F e n (fz X F n (z + w)) = ee X F e n (fz X F n z) + ee X F e n (fz X F n w)
  rw [fz_add, map_add (f := _)]

def phi : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n →+ (S X F n).moduleCatLeftHomologyData.H where
  toFun z := (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he z)
  map_zero' := by
    have : cyc X F n e he 0 = 0 := by
      have h := cyc_add X F n e he 0 0
      rw [add_zero] at h
      exact (add_eq_left.mp h.symm)
    rw [this, (LinearMap.range (S X F n).moduleCatToCycles).mkQ.map_zero]
  map_add' z w := by
    rw [cyc_add, (LinearMap.range (S X F n).moduleCatToCycles).mkQ.map_add]

theorem phi_eq_zero_iff (z : Cocycle (LateralTheory.E.LocSecPf.pt R X) (res R F) n) :
    phi X F n e he z = 0 ↔ z ∈ coboundaries _ _ _ := by
  obtain ⟨hf, hz⟩ := exists_mk X F n z
  have key : z ∈ coboundaries (LateralTheory.E.LocSecPf.pt R X) (res R F) n ↔
      ∃ g : (free R).obj (yoneda.obj X) ⟶ (res R F).X (n - 1), g ≫ (res R F).d (n - 1) n = fz X F n z := by
    conv_lhs => rw [← hz]
    exact Cocycle.fromSingleMk_mem_coboundaries_iff (K := res R F) (fz X F n z) (zero_add n) (n + 1) rfl hf
      (n - 1) (by omega)
  rw [key]
  change (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he z) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(ee X F e (n - 1)).symm s, (ee X F e n).injective ?_⟩
    rw [ee_comp X F e he]; erw [AddEquiv.apply_symm_apply]
    exact congrArg Subtype.val hs
  · rintro ⟨g, hg⟩
    refine ⟨ee X F e (n - 1) g, Subtype.ext ?_⟩
    change ((LateralTheory.E.LeafLocPf.secCx F X).d (n - 1) n).hom (ee X F e (n - 1) g) = ee X F e n (fz X F n z)
    rw [← ee_comp X F e he, hg]

def psi : CohomologyClass (LateralTheory.E.LocSecPf.pt R X) (res R F) n →+ (S X F n).moduleCatLeftHomologyData.H :=
  CohomologyClass.descAddMonoidHom (phi X F n e he) (fun z hz => (phi_eq_zero_iff X F n e he z).2 hz)

theorem psi_bijective : Function.Bijective (psi X F n e he) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
    rw [CohomologyClass.mk_eq_zero_iff, ← phi_eq_zero_iff X F n e he]
    exact hc
  · intro c
    obtain ⟨⟨s, hs⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hf : (ee X F e n).symm s ≫ (res R F).d n (n + 1) = 0 := by
      apply (ee X F e (n + 1)).injective
      rw [ee_comp X F e he, map_zero]; erw [AddEquiv.apply_symm_apply]
      exact hs
    refine ⟨CohomologyClass.mk (Cocycle.fromSingleMk _ (zero_add n) (n + 1) rfl hf), ?_⟩
    change (LinearMap.range (S X F n).moduleCatToCycles).mkQ (cyc X F n e he _) = Submodule.Quotient.mk _
    rw [Submodule.mkQ_apply]
    congr 1
    apply Subtype.ext
    change ee X F e n (fz X F n _) = s
    rw [fz_mk]
    exact (ee X F e n).apply_symm_apply s

end

theorem classSec : LateralTheory.E.LocSecPfB.ClassSec := by
  intro R _ X e he F n
  refine ⟨(AddEquiv.ofBijective _ (psi_bijective X F n e he)).trans ?_⟩
  exact ((LateralTheory.E.LeafLocPf.secCx F X).homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    (S X F n).moduleCatHomologyIso).toLinearEquiv.toAddEquiv.symm

theorem ClassSec_of : LateralTheory.E.LocSecPfB.ClassSec := classSec

end LateralTheory.E.ClassSecPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

theorem toR_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    toR R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [← Spec.map_comp]; rfl

theorem incl_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

abbrev cmp {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    pullback c p ⟶ pullback b p :=
  pullback.lift (pullback.fst c p ≫ a) (pullback.snd _ _)
    (by rw [Category.assoc, h]; exact pullback.condition)

theorem paste {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    IsPullback (cmp p a b c h) (pullback.fst c p) (pullback.fst b p) a := by
  subst h
  refine IsPullback.of_right (h₁₂ := pullback.snd b p) (v₁₃ := p) (h₂₂ := b) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback b p).flip
  rw [pullback.lift_snd]; exact (IsPullback.of_hasPullback (a ≫ b) p).flip

theorem LeafSpreadLQFGraph_of (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph := by
  intro k _ X p _ Ω _ _ R hRfg C0 D0 c0 q v0 f e he hf hq hpb hve hlqf
  have hLFT : LocallyOfFinitePresentation (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) := by
    infer_instance
  obtain ⟨S, hRS, hSfg, hS⟩ := hM k Ω R hRfg
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm)
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) (pullback.lift q f hf.symm) v0
    (cmp p (toR R) _ _ (toR_sk R))
    ⟨hLFT, inferInstance, inferInstance⟩ (by rw [pullback.lift_fst]; exact hq) (paste p _ _ _ (toR_sk R))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hpb) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hpb.w.symm
      · simp only [Category.assoc, pullback.lift_snd]; exact hve.symm) hlqf
  refine ⟨S, hRS, hSfg, fun R' hSR' hR E0 q' r hr hf' => ?_⟩
  refine hS R' hSR' hR E0 _ (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R'))) p)
    (pullback.lift q' (r ≫ f) hf'.symm) r (cmp p (incl hR) _ _ (incl_sk hR)) (paste p _ _ _ (incl_sk hR))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hr) ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hr.w.symm
  · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf

namespace LateralTheory.E.LeafInclDescendPf

def bcLift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R'' : Subalgebra k Ω} (h : R ≤ R'')
    {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D} (w : v ≫ q = g ≫ toR R) :
    Y ⟶ pullback q (incl h) :=
  pullback.lift v (g ≫ toR R'') (by rw [Category.assoc, toR_eq, w])

theorem bcLift_isPullback {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R'' : Subalgebra k Ω} (h : R ≤ R'')
    {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D} (hp : IsPullback v g q (toR R)) :
    IsPullback (bcLift h hp.w) g (pullback.snd q (incl h)) (toR R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h))
  dsimp only [bcLift]
  rw [pullback.lift_fst, toR_eq]
  exact hp

def LeafInclPiece : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R)),
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ ∀ (R'' : Subalgebra k Ω) (h : R ≤ R''), R' ≤ R'' →
      ∃ φ : pullback qW (incl h) ⟶ pullback qU (incl h), IsOpenImmersion φ ∧
        φ ≫ pullback.snd qU (incl h) = pullback.snd qW (incl h) ∧
        bcLift h hW.w ≫ φ = X.homOfLE hWU ≫ bcLift h hU.w

theorem LeafInclDescend_of (hP : LeafInclPiece) : LeafInclDescend := by
  intro k _ Ω _ _ X f hf U V R hR ⟨DU, qU, vU, hqU, pU⟩ ⟨DV, qV, vV, hqV, pV⟩ ⟨DW, qW, vW, hqW, pW⟩
  obtain ⟨R1, h1, hR1, H1⟩ := hP k Ω f hf U (U ⊓ V) inf_le_left R hR DU DW qU qW vU vW hqU hqW pU pW
  obtain ⟨R2, h2, hR2, H2⟩ := hP k Ω f hf V (U ⊓ V) inf_le_right R hR DV DW qV qW vV vW hqV hqW pV pW
  have hle : R ≤ R1 ⊔ R2 := h1.trans le_sup_left
  obtain ⟨φU, oU, sU, cU⟩ := H1 (R1 ⊔ R2) hle le_sup_left
  obtain ⟨φV, oV, sV, cV⟩ := H2 (R1 ⊔ R2) hle le_sup_right
  exact ⟨R1 ⊔ R2, hle, hR1.sup hR2, _, _, _, pullback.snd qU (incl hle), pullback.snd qV (incl hle),
    pullback.snd qW (incl hle), bcLift hle pU.w, bcLift hle pV.w, bcLift hle pW.w, φU, φV,
    fp_snd _ _ hqU, fp_snd _ _ hqV, fp_snd _ _ hqW, oU, oV, sU, sV,
    bcLift_isPullback hle pU, bcLift_isPullback hle pV, bcLift_isPullback hle pW, cU, cV⟩

end LateralTheory.E.LeafInclDescendPf
end
end
