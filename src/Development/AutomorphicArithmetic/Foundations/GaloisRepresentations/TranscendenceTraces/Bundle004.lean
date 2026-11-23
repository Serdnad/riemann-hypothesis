module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum Classical

namespace UpperTheory.Gal.TranscendenceTraces

variable {R : Type} [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S)

def pbm {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') : pullback p u' ⟶ pullback p u :=
  pullback.lift (pullback.fst p u') (pullback.snd p u' ≫ g) (by rw [Category.assoc, h, pullback.condition])

theorem pbm_fst {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') :
    pbm p g u u' h ≫ pullback.fst p u = pullback.fst p u' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pbm_snd {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') :
    pbm p g u u' h ≫ pullback.snd p u = pullback.snd p u' ≫ g := pullback.lift_snd _ _ _

abbrev DS (G : Shv R) (U : Scheme.{0}) : Type 1 := ⨁ u : (U ⟶ S), Sec G (pullback p u)

def inc (G : Shv R) {U : Scheme.{0}} (u : U ⟶ S) : Sec G (pullback p u) →ₗ[ULift.{1} R] DS p G U :=
  DirectSum.lof (ULift.{1} R) (U ⟶ S) (fun u => Sec G (pullback p u)) u

theorem DS.hom_ext {G : Shv R} {U : Scheme.{0}} {M : Type 1} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f f' : DS p G U →ₗ[ULift.{1} R] M} (h : ∀ u a, f (inc p G u a) = f' (inc p G u a)) : f = f' :=
  DirectSum.linearMap_ext _ fun u => LinearMap.ext fun a => h u a

theorem inc_congr (G : Shv R) {U : Scheme.{0}} {u u' : U ⟶ S} (h : u' = u) (k : pullback p u' ⟶ pullback p u)
    (h1 : k ≫ pullback.fst p u = pullback.fst p u') (h2 : k ≫ pullback.snd p u = pullback.snd p u')
    (a : Sec G (pullback p u)) : inc p G u' (Sec.res k a) = inc p G u a := by
  subst h
  have : k = 𝟙 _ := pullback.hom_ext (by simpa using h1) (by simpa using h2)
  rw [this, res_id]

def DS.res (G : Shv R) {U' U : Scheme.{0}} (g : U' ⟶ U) : DS p G U →ₗ[ULift.{1} R] DS p G U' :=
  DirectSum.toModule _ _ _ fun u => inc p G (g ≫ u) ∘ₗ (G.obj.map (pbm p g u _ rfl).op).hom

theorem DS.res_inc (G : Shv R) {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u')
    (a : Sec G (pullback p u)) : DS.res p G g (inc p G u a) = inc p G u' (Sec.res (pbm p g u u' h) a) := by
  subst h
  exact DirectSum.toModule_lof _ _ _

def DS.map {G G' : Shv R} (f : G ⟶ G') (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} R] DS p G' U :=
  DirectSum.toModule _ _ _ fun u => inc p G' u ∘ₗ (f.hom.app (op (pullback p u))).hom

theorem DS.map_inc {G G' : Shv R} (f : G ⟶ G') {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    DS.map p f U (inc p G u a) = inc p G' u (Sec.map f a) := DirectSum.toModule_lof _ _ _

def phiP (G : Shv R) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (DS p G U.unop)
  map g := ModuleCat.ofHom (DS.res p G g.unop)
  map_id U := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.res p G (𝟙 _) (inc p G u a) = inc p G u a
    rw [DS.res_inc p G _ u _ rfl]
    exact inc_congr p G (Category.id_comp u) _ (pbm_fst p _ _ _ _) (by simp) a)
  map_comp f g := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.res p G (g.unop ≫ f.unop) (inc p G u a) = DS.res p G g.unop (DS.res p G f.unop (inc p G u a))
    rw [DS.res_inc p G _ u _ (Category.assoc _ _ _), DS.res_inc p G f.unop u _ rfl, DS.res_inc p G g.unop _ _ rfl, res_res]
    congr 2
    exact pullback.hom_ext (by simp only [Category.assoc, pbm_fst]) (by simp))

def phiPF (R : Type) [CommRing R] : Shv R ⥤ (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) where
  obj G := phiP p G
  map {G G'} f :=
    { app := fun U => ModuleCat.ofHom (DS.map p f U.unop)
      naturality := fun U V g => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
        change DS.map p f _ (DS.res p G g.unop (inc p G u a)) = DS.res p G' g.unop (DS.map p f _ (inc p G u a))
        rw [DS.res_inc p G _ u _ rfl, DS.map_inc, DS.map_inc, DS.res_inc p G' _ u _ rfl, map_res]) }
  map_id G := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => DS.map_inc p (𝟙 G) u a))
  map_comp {G G' G''} f g := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.map p (f ≫ g) _ (inc p G u a) = DS.map p g _ (DS.map p f _ (inc p G u a))
    rw [DS.map_inc, DS.map_inc, DS.map_inc]
    rfl))

instance (R : Type) [CommRing R] : (phiPF p R).Additive where
  map_add {G G' f g} := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.map p (f + g) _ (inc p G u a) = DS.map p f _ (inc p G u a) + DS.map p g _ (inc p G u a)
    rw [DS.map_inc, DS.map_inc, DS.map_inc, ← map_add (f := _)]
    rfl))

def phi (R : Type) [CommRing R] : Shv R ⥤ Shv R := phiPF p R ⋙ presheafToSheaf _ _

instance (R : Type) [CommRing R] : (phi p R).Additive := by
  unfold phi
  infer_instance

def phiSec (G : Shv R) (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} R] Sec ((phi p R).obj G) U :=
  ((toSheafify Scheme.etaleTopology (phiP p G)).app (op U)).hom

theorem phiSec_res (G : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (x : DS p G U) :
    Sec.res g (phiSec p G U x) = phiSec p G V (DS.res p G g x) :=
  (congrArg (fun h => h.hom x) ((toSheafify Scheme.etaleTopology (phiP p G)).naturality g.op)).symm

theorem phiSec_map {G G' : Shv R} (f : G ⟶ G') (U : Scheme.{0}) (x : DS p G U) :
    Sec.map ((phi p R).map f) (phiSec p G U x) = phiSec p G' U (DS.map p f U x) :=
  (congrArg (fun h => (h.app (op U)).hom x) (toSheafify_naturality Scheme.etaleTopology ((phiPF p R).map f))).symm

def Sq.cmp {p : Z ⟶ S} (A : Sq p) : pullback p A.u ⟶ A.V :=
  A.pb.lift (pullback.fst p A.u) (pullback.snd p A.u) pullback.condition

theorem Sq.cmp_v {p : Z ⟶ S} (A : Sq p) : A.cmp ≫ A.v = pullback.fst p A.u := A.pb.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Sq.cmp_r {p : Z ⟶ S} (A : Sq p) : A.cmp ≫ A.r = pullback.snd p A.u := A.pb.lift_snd _ _ _

def phiE (G : Shv R) : Fam0 p G ((phi p R).obj G) where
  app A := (phiSec p G A.U ∘ₗ inc p G A.u ∘ₗ (G.obj.map A.cmp.op).hom).toAddMonoidHom
  nat {A B} t a := by
    change Sec.res t.g (phiSec p G B.U (inc p G B.u (Sec.res B.cmp a))) =
      phiSec p G A.U (inc p G A.u (Sec.res A.cmp (Sec.res t.k a)))
    rw [phiSec_res, DS.res_inc p G t.g B.u A.u t.hu, res_res, res_res]
    congr 3
    exact B.pb.hom_ext (by simp only [Category.assoc, Sq.cmp_v, pbm_fst, t.hv])
      (by simp [t.hr])

theorem phiE_app (G : Shv R) (A : Sq p) (a : Sec G A.V) :
    (phiE p G).app A a = phiSec p G A.U (inc p G A.u (Sec.res A.cmp a)) := rfl

theorem phiE_of (G : Shv R) {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    (phiE p G).app (Sq.of p u) a = phiSec p G U (inc p G u a) := by
  refine (phiE_app p G (Sq.of p u) a).trans ?_
  exact congrArg _ (inc_congr p G rfl _ (Sq.cmp_v (Sq.of p u)) (Sq.cmp_r (Sq.of p u)) a)

end UpperTheory.Gal.TranscendenceTraces

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtUnique_of :
    WtVanish → WtLin → WtUnique := by
  intro hV hL Z S p _ w w' hw hw' D hD hagree
  have hdiff : IsWt p (w.add (Wt.smul (-1) w')) := hL.1 p w _ hw (hL.2.1 p (-1) w' hw')
  have h0 := hV p _ hdiff D hD (by
    intro Ω _ _ z hz
    show w Ω z + (-1) * w' Ω z = 0
    rw [hagree Ω z hz]
    ring)
  funext Ω _ _ z
  have h := congrFun (congrFun (congrFun (congrFun h0 Ω) ‹_›) ‹_›) z
  change w Ω z + (-1) * w' Ω z = 0 at h
  linarith
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem exists_open_irreducible_nhds_of_generizations {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    [TopologicalSpace.NoetherianSpace Y] (y : Y) (hG : IsIrreducible {z | z ⤳ y}) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ IsIrreducible U := by
  have key : ∀ W ∈ irreducibleComponents Y, y ∈ W → W = closure {z | z ⤳ y} := by
    intro W hW hyW
    have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
    have hgen := hW.1.isGenericPoint_genericPoint_closure
    rw [hWc.closure_eq] at hgen
    have hcl : closure {hW.1.genericPoint} = W := hgen
    have hsub : W ⊆ closure {z | z ⤳ y} := by
      rw [← hcl]
      exact closure_mono (Set.singleton_subset_iff.mpr (hgen.specializes hyW))
    exact le_antisymm hsub (hW.2 hG.closure hsub)
  let C := irreducibleComponent y
  refine ⟨(⋃₀ (irreducibleComponents Y \ {C}))ᶜ, ?_, ?_, ?_⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  · simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_diff, Set.mem_singleton_iff,
      not_exists, not_and, and_imp]
    intro W hW hne hyW
    exact hne ((key W hW hyW).trans (key C (irreducibleComponent_mem_irreducibleComponents y)
      mem_irreducibleComponent).symm)
  · apply isIrreducible_iff_closure.mp
    rw [closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _
      (irreducibleComponent_mem_irreducibleComponents y)]
    exact isIrreducible_irreducibleComponent

private theorem isIntegrallyClosed_affine_of_stalks {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
  let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  haveI : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  change IsIntegrallyClosed (Localization.AtPrime y.asIdeal)
  exact (h _).of_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime y.asIdeal)).toRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.nmlNoeth_of :
    NmlNoeth := by
  intro S _ hN x
  haveI : ∀ z : S, IsDomain (S.presheaf.stalk z) := fun z => (hN z).1
  obtain ⟨_, ⟨V : S.Opens, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV.isCompact
  haveI : IsNoetherian V.toScheme := {}
  have hns : TopologicalSpace.NoetherianSpace V.toScheme := inferInstance
  have hqs : QuasiSober V.toScheme := inferInstance
  have hG : IsIrreducible {z | z ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    haveI : IrreducibleSpace (Spec (S.presheaf.stalk x)) := PrimeSpectrum.irreducibleSpace
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (S.fromSpecStalk x).continuous.continuousOn
  have hGV : {z | z ⤳ x} ⊆ (V : Set S) := fun z hz => hz.mem_open V.isOpen hxV
  have hG' : IsIrreducible {z : V | z ⤳ ⟨x, hxV⟩} := by
    have he : {z : V | z ⤳ ⟨x, hxV⟩} =
        Set.range (fun z : {z | z ⤳ x} => (⟨z.1, hGV z.2⟩ : V)) := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨z.1, (Topology.IsInducing.subtypeVal.specializes_iff).mpr hz⟩, rfl⟩
      · rintro ⟨w, rfl⟩
        exact (Topology.IsInducing.subtypeVal.specializes_iff).mp w.2
    rw [he, ← Set.image_univ]
    haveI : IrreducibleSpace {z | z ⤳ x} := isIrreducible_iff_irreducibleSpace.mp hG
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (by fun_prop : Continuous _).continuousOn
  obtain ⟨W, hWo, hxW, hWi⟩ := @exists_open_irreducible_nhds_of_generizations V.toScheme _ hqs hns ⟨x, hxV⟩ hG'
  have hW'o : IsOpen (Subtype.val '' W : Set S) := V.isOpen.isOpenMap_subtype_val W hWo
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hxU, hUW⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (⟨_, hxW, rfl⟩ : x ∈ Subtype.val '' W) hW'o
  have hUi : IsIrreducible (U : Set S) :=
    ⟨⟨x, hxU⟩, (hWi.image _ continuous_subtype_val.continuousOn).2.open_subset U.isOpen hUW⟩
  haveI : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hUi
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨x, hxU⟩, trivial⟩⟩
  haveI : IsDomain Γ(S, U) :=
    MulEquiv.isDomain Γ(U.toScheme, ⊤) (U.topIso).commRingCatIsoToRingEquiv.symm.toMulEquiv
  exact ⟨U, hU, hxU, inferInstance, isIntegrallyClosed_affine_of_stalks hU fun z => (hN z).2⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pullHQ_id' (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) :
    pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = (pullHQ l f n i) ∘ₗ (pullHQ l g n i) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]

private theorem existsUnique_sec {U P : Scheme.{0}} (p' : P ⟶ U) {m : ℕ} (s' : Fin m → (U ⟶ P))
    (hs : ∀ j, s' j ≫ p' = 𝟙 U) (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P))
    {Ω : Type} [Field Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P) (hy : y ≫ p' = x0) :
    ∃! j, x0 ≫ s' j = y := by
  have hι : ∀ j, Sigma.ι (fun _ : Fin m => U) j ≫ Sigma.desc s' = s' j := fun j => Sigma.ι_desc _ _
  let t : gp Ω ⟶ ∐ (fun _ : Fin m => U) := y ≫ inv (Sigma.desc s')
  obtain ⟨⟨j, u⟩, hu⟩ := (sigmaMk (fun _ : Fin m => U)).surjective (pt t)
  rw [sigmaMk_mk] at hu
  have hr : Set.range t ⊆ Set.range (Sigma.ι (fun _ : Fin m => U) j) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨u, by rw [hu, pt_eq]⟩
  let t' := IsOpenImmersion.lift (Sigma.ι (fun _ : Fin m => U) j) t hr
  have ht' : t' ≫ Sigma.ι (fun _ : Fin m => U) j = t := IsOpenImmersion.lift_fac _ _ _
  have h1 : t' ≫ s' j = y := by
    rw [← hι j, ← Category.assoc, ht']
    simp [t]
  have h2 : t' = x0 := by
    rw [← hy, ← h1, Category.assoc, hs j, Category.comp_id]
  refine ⟨j, by rw [← h2]; exact h1, fun k hk => ?_⟩
  have h3 : (x0 ≫ Sigma.ι (fun _ : Fin m => U) k) ≫ Sigma.desc s' =
      (x0 ≫ Sigma.ι (fun _ : Fin m => U) j) ≫ Sigma.desc s' := by
    rw [Category.assoc, Category.assoc, hι, hι, hk, ← h2, h1]
  have h4 := (cancel_mono (Sigma.desc s')).1 h3
  have h5 : Sigma.ι (fun _ : Fin m => U) k (pt x0) = Sigma.ι (fun _ : Fin m => U) j (pt x0) := by
    rw [← pt_comp, ← pt_comp, h4]
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ k j _ _).1 h5)

private theorem finsum_one_singleton {T : Type*} (A : Set T) (a : T) (h : A = {a}) :
    ∑ᶠ z ∈ A, (1 : ℤ) = 1 := by
  subst h
  simp

private theorem finsum_one_empty {T : Type*} (A : Set T) (h : A = ∅) :
    ∑ᶠ z ∈ A, (1 : ℤ) = 0 := by
  subst h
  simp

private theorem tr_split (hCorr : CorrEqQ) (hId : TrIdQ) (l : ℕ) [Fact l.Prime] (n i : ℤ) {U P : Scheme.{0}}
    (p' : P ⟶ U) [IsFinite p'] (wt : IsWt p' (Wt.const P 1)) (wt1 : IsWt (𝟙 U) (Wt.const U 1))
    (hl : IsUnit (l : Γ(U, ⊤))) {m : ℕ} (s' : Fin m → (U ⟶ P)) (hs : ∀ j, s' j ≫ p' = 𝟙 U)
    (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P)) :
    trHQ l p' (Wt.const P 1) n i = ∑ j, pullHQ l (sch.map (s' j)) n i := by
  classical
  let c : Option (Fin m) → Corr U P := fun o => match o with
    | none => ⟨P, p', 𝟙 P, Wt.const P 1, inferInstance, wt⟩
    | some j => ⟨U, 𝟙 U, s' j, Wt.const U 1, inferInstance, wt1⟩
  let mm : Option (Fin m) → ℤ := fun o => match o with
    | none => 1
    | some _ => -1
  have hcn : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P),
      (c none).cyc Ω x0 y = if y ≫ p' = x0 then 1 else 0 := by
    intro Ω _ _ x0 y
    split_ifs with h
    · refine finsum_one_singleton _ y ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
      exact ⟨fun hz => hz.2, fun hz => ⟨hz ▸ h, hz⟩⟩
    · refine finsum_one_empty _ ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
      rintro ⟨h1, rfl⟩
      exact h h1
  have hcs : ∀ (j : Fin m) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P),
      (c (some j)).cyc Ω x0 y = if x0 ≫ s' j = y then 1 else 0 := by
    intro j Ω _ _ x0 y
    split_ifs with h
    · refine finsum_one_singleton _ x0 ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
      exact ⟨fun hz => hz.1, fun hz => ⟨hz, hz ▸ h⟩⟩
    · refine finsum_one_empty _ ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
      rintro ⟨rfl, h1⟩
      exact h h1
  have key := hCorr l n i (𝟙 U) p' (Option (Fin m)) c mm
    (fun a => by cases a with
      | none => simp [c]
      | some j => simp [c, hs j]) hl Set.univ dense_univ
    (fun Ω _ _ x0 y _ => by
      rw [Fintype.sum_option]
      simp only [hcn, hcs, mm]
      by_cases hy : y ≫ p' = x0
      · obtain ⟨j, hj, hu⟩ := existsUnique_sec p' s' hs hiso x0 y hy
        rw [if_pos hy, Finset.sum_eq_single j]
        · simp [hj]
        · intro k _ hk
          rw [if_neg (fun e => hk (hu k e))]
          simp
        · simp
      · rw [if_neg hy]
        simp only [mul_zero, zero_add]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg]
        · simp
        · intro e
          apply hy
          rw [← e, Category.assoc, hs j, Category.comp_id])
  rw [Fintype.sum_option] at key
  have e0 : (c none).opQ l n i = trHQ l p' (Wt.const P 1) n i := by
    change trHQ l p' (Wt.const P 1) n i ∘ₗ pullHQ l (sch.map (𝟙 P)) n i = _
    rw [CategoryTheory.Functor.map_id, pullHQ_id', LinearMap.comp_id]
  have e1 : ∀ j, (c (some j)).opQ l n i = pullHQ l (sch.map (s' j)) n i := by
    intro j
    change trHQ l (𝟙 U) (Wt.const U 1) n i ∘ₗ pullHQ l (sch.map (s' j)) n i = _
    rw [hId l n i U 1 hl]
    simp
  simp only [mm, e0, e1] at key
  simp only [Int.cast_one, one_smul, Int.cast_neg, neg_smul, Finset.sum_neg_distrib] at key
  exact add_neg_eq_zero.1 key

theorem UpperTheory.Gal.TranscendenceTraces.trSplitQ_of :
    TrBCQ → CorrEqQ → TrIdQ → WtLin → WtFlat → MultBasic → TrSplitQ := by
  intro hBC hCorr hId hLin hFlat hMult l _ n i Z S p _ _ hl U x m s hs hiso
  have wtp : IsWt p (Wt.const Z 1) := by
    rw [← hMult.2.2 p]
    exact hFlat p
  have wtp' : IsWt (pullback.snd p x) (Wt.const (pullback p x) 1) := by
    rw [← hMult.2.2 (pullback.snd p x)]
    exact hFlat _
  have hlU : IsUnit (l : Γ(U, ⊤)) := by
    simpa using hl.map x.appTop.hom
  have h1 := hBC l n i (pullback.fst p x) (pullback.snd p x) p x (Wt.const Z 1)
    (IsPullback.of_hasPullback p x) wtp hl
  have h2 := tr_split hCorr hId l n i (pullback.snd p x) wtp' (hLin.2.2 (𝟙 U) 1) hlU
    (fun j => pullback.lift (s j) (𝟙 U) (by rw [hs j, Category.id_comp]))
    (fun j => pullback.lift_snd _ _ _) hiso
  rw [h1]
  change trHQ l (pullback.snd p x) (Wt.const _ 1) n i ∘ₗ _ = _
  rw [h2]
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LinearMap.comp_apply, ← pullHQ_comp', ← CategoryTheory.Functor.map_comp, pullback.lift_fst]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.isolate_of :
    Chart → IsolateSpec → Isolate := by
  intro hC hI Z S p _ z
  have hmem : p z ∈ (⊤ : S.Opens) := trivial
  obtain ⟨U, hU0, hzU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) hmem
  have hU : IsAffineOpen U := hU0
  let u0 : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.isoSpec.inv ≫ Scheme.Opens.ι U
  obtain ⟨B, iB, iAB, v0, hfin, hpb⟩ := hC p Γ(S, U) u0
  haveI := hfin
  obtain ⟨y, hy⟩ : ∃ y : (U : Scheme), Scheme.Opens.ι U y = p z := ⟨⟨p z, hzU⟩, rfl⟩
  have ha : u0 (hU.isoSpec.hom y) = p z := by
    show (hU.isoSpec.hom ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U) y = p z
    rw [Iso.hom_inv_id_assoc, hy]
  obtain ⟨w0, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := u0) z _ ha.symm
  have hw : v0 (hpb.isoPullback.inv w0) = z := by
    rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hw1]
  obtain ⟨A', W, v, hEt, hW, hvW, hvv, hiso⟩ := hI Γ(S, U) B (hpb.isoPullback.inv w0)
  haveI := hEt
  refine ⟨⟨A'.U, A'.V, A'.u ≫ u0, A'.v ≫ v0, A'.r, A'.pb.paste_horiz hpb⟩, W, v, ?_, hW, hvW, ?_, hiso⟩
  · show Etale (A'.u ≫ u0)
    infer_instance
  · show (A'.v ≫ v0) v = z
    rw [Scheme.Hom.comp_apply, hvv, hw]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.chart_of :
    Chart := by
  intro Z S p _ A _ u
  haveI : IsAffine (pullback p u) := isAffine_of_isAffineHom (pullback.snd p u)
  let V := pullback p u
  let e : Spec Γ(V, ⊤) ≅ V := V.isoSpec.symm
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := Spec.preimage (e.hom ≫ pullback.snd p u)
  have hφ : Spec.map φ = e.hom ≫ pullback.snd p u := Spec.map_preimage _
  letI alg : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = e.hom ≫ pullback.snd p u := hφ
  refine ⟨Γ(V, ⊤), inferInstance, alg, e.hom ≫ pullback.fst p u, ?_, ?_⟩
  · have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤)))) := by
      rw [hφ']; infer_instance
    have h2 := (IsFinite.SpecMap_iff _).1 hfin
    exact RingHom.finite_algebraMap.1 h2
  · rw [hφ']
    exact IsPullback.of_iso (IsPullback.of_hasPullback p u) e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
end
