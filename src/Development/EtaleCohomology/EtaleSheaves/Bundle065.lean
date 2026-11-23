module

public import Development.EtaleCohomology.EtaleSheaves.Bundle053
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.EtaleCohomology.EtaleSheaves.Bundle054
public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Presentable.Type
public import Development.EtaleCohomology.EtaleSheaves.Bundle025
public import Development.EtaleCohomology.EtaleSheaves.Bundle003
public import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
public import Mathlib.Topology.Sets.Opens
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.EtaleCohomology.EtaleSheaves.Bundle051
import Development.EtaleCohomology.EtaleSheaves.Bundle039
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

namespace LateralTheory.E.StageBPf

theorem pp {q : ℕ} {i n : ℤ} {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Ht q (sch.obj Z) n i) :
    pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) = pull _ (sch.map (a ≫ b)) (tw q i) n x := by
  rw [Functor.map_comp, pull_comp]

theorem indep {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j j' : J) :
    c.π.app j ≫ ι j = c.π.app j' ≫ ι j' := by
  rw [← c.w (IsCofiltered.minToLeft j j'), ← c.w (IsCofiltered.minToRight j j'), Category.assoc, Category.assoc, hι, hι]

theorem qc_of {X Y : Scheme.{0}} (f : X ⟶ Y) (h : IsAffineHom f) (hY : CompactSpace Y) : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace f
theorem qs_of {X Y : Scheme.{0}} (f : X ⟶ Y) (h : IsAffineHom f) (hY : QuasiSeparatedSpace Y) : QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_quasiSeparated f
theorem aff_canc {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h1 : IsAffineHom (f ≫ g)) (h2 : IsAffineHom g) : IsAffineHom f := by
  have := IsSeparated.of_isAffineHom g; exact IsAffineHom.of_comp f g
theorem aff_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h1 : IsAffineHom f) (h2 : IsAffineHom g) : IsAffineHom (f ≫ g) :=
  inferInstance

variable {A : Type} [CommRing A] [IsLocalRing A]

def DO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0})
    (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) : J ⥤ Over (Spec (CommRingCat.of A)) where
  obj j := Over.mk (ι j ≫ g)
  map f := Over.homMk (D.map f) (by dsimp; rw [← Category.assoc, hι])
  map_id := by intros; ext; simp
  map_comp := by intros; ext; simp

def CO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
    (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J) :
    Cone (DO g D ι hι) where
  pt := Over.mk ((c.π.app j0 ≫ ι j0) ≫ g)
  π := { app := fun j => Over.homMk (c.π.app j) (by show c.π.app j ≫ ι j ≫ g = _; rw [← Category.assoc, indep D c ι hι j j0]; rfl)
         naturality := by intro j k f; ext; exact (c.w f).symm }

def isLimit_CO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J)
    (hl : IsLimit c) : IsLimit (CO g D c ι hι j0) := by
  haveI := IsCofiltered.isConnected J
  exact isLimitOfReflects (Over.forget _) hl

def isLimit_fib {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J)
    (hl : IsLimit c) :
    IsLimit ((Over.forget _).mapCone ((Over.pullback (cpt A)).mapCone (CO g D c ι hι j0))) := by
  haveI := IsCofiltered.isConnected J
  haveI := (Over.mapPullbackAdj (cpt A)).rightAdjoint_preservesLimits
  exact isLimitOfPreserves _ (isLimitOfPreserves _ (isLimit_CO g D c ι hι j0 hl))

theorem fm_comp {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {U V : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (d : U ⟶ V)
    (hd : d ≫ v = u) (h : pullback (u ≫ g) (cpt A) ⟶ pullback (v ≫ g) (cpt A))
    (h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d) (h2 : h ≫ pullback.snd _ _ = pullback.snd _ _) :
    h ≫ fm v g = fm u g := by
  apply pullback.hom_ext
  · simp only [fm, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, ← Category.assoc, h1, Category.assoc, hd]
  · simp only [fm, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, Category.comp_id, Category.comp_id, h2]

end LateralTheory.E.StageBPf

namespace LateralTheory.E.StageBPf

theorem StageB_of : StageB := by
  intro hC H q i A _ _ hq Y _ _ g y J _ _ D c ι hc hp n z
  obtain ⟨⟨hl⟩, hι, hD⟩ := hc
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have hcs : ∀ j, CompactSpace (D.obj j) := fun j => by
    have := (hι j).2.1; exact QuasiCompact.compactSpace_of_compactSpace (ι j)
  have hqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => by
    have := (hι j).1; exact quasiSeparatedSpace_of_quasiSeparated (ι j)
  have hι' : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j := fun f => (hD f).1
  obtain ⟨w, hw⟩ := (hp j0 n).2 (pull _ (sch.map (fm (c.π.app j0 ≫ ι j0) g)) _ _ z)
  obtain ⟨j1, u, hu⟩ := (hC H q D c hl (fun f => (hD f).2) hcs hqs (fun j => unit_of hq (ι j ≫ g)) n i).1 w
  have hfa : ∀ j, IsAffineHom (pullback.fst (ι j ≫ g) (cpt A)) := fun j =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have hκ : IsUnit (q : IsLocalRing.ResidueField A) := by simpa using hq.map (IsLocalRing.residue A)
  let Cg := (Over.forget _).mapCone ((Over.pullback (cpt A)).mapCone (CO g D c ι hι' j0))
  have hlim : IsLimit Cg := isLimit_fib g D c ι hι' j0 hl
  have hEaff : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f) := by
    intro j k f
    have e : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.fst (ι k ≫ g) (cpt A) =
        pullback.fst (ι j ≫ g) (cpt A) ≫ D.map f := pullback.lift_fst _ _ _
    refine aff_canc _ (pullback.fst (ι k ≫ g) (cpt A)) ?_ (hfa k)
    rw [e]; exact aff_comp _ _ (hfa j) (hD f).2
  have hEc : ∀ j, CompactSpace (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j) := fun j =>
    qc_of (pullback.fst (ι j ≫ g) (cpt A)) (hfa j) (hcs j)
  have hEq : ∀ j, QuasiSeparatedSpace (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j) := fun j =>
    qs_of (pullback.fst (ι j ≫ g) (cpt A)) (hfa j) (hqs j)
  have hEu : ∀ j, IsUnit (q : Γ((((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j), ⊤)) := fun j =>
    unit_of hκ (pullback.snd (ι j ≫ g) (cpt A))
  have key1 : Cg.π.app j1 ≫ pullback.fst (ι j1 ≫ g) (cpt A) = pullback.fst _ _ ≫ c.π.app j1 := pullback.lift_fst _ _ _
  have key1s : Cg.π.app j1 ≫ pullback.snd (ι j1 ≫ g) (cpt A) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have key2 : Cg.π.app j1 ≫ fm (ι j1) g = fm (c.π.app j0 ≫ ι j0) g :=
    fm_comp g (c.π.app j0 ≫ ι j0) (ι j1) (c.π.app j1) (indep D c ι hι' j1 j0) _ key1 key1s
  have hv : pull _ (sch.map (Cg.π.app j1)) _ _ (pull _ (sch.map (pullback.fst (ι j1 ≫ g) (cpt A))) _ _ u -
      pull _ (sch.map (fm (ι j1) g)) (tw q i) n z) = 0 := by
    erw [map_sub, pp, pp, key1, key2, ← pp, hu, hw, sub_self]
  obtain ⟨k, f, hk⟩ := (hC H q _ Cg hlim hEaff hEc hEq hEu n i).2 j1 _ hv
  refine ⟨k, pull _ (sch.map (D.map f)) _ _ u, ?_⟩
  have key3 : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.fst (ι j1 ≫ g) (cpt A) =
      pullback.fst (ι k ≫ g) (cpt A) ≫ D.map f := pullback.lift_fst _ _ _
  have key5 : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.snd (ι j1 ≫ g) (cpt A) =
      pullback.snd (ι k ≫ g) (cpt A) := pullback.lift_snd _ _ _
  have key4 := fm_comp g (ι k) (ι j1) (D.map f) (hι' f) _ key3 key5
  erw [map_sub, pp, pp, key3, key4, ← pp, sub_eq_zero] at hk
  exact hk

end LateralTheory.E.StageBPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.DescEqvPf

variable {R : Type} [CommRing R]

theorem mono_sch {X Y : Scheme.{0}} (j : X ⟶ Y) [Mono j] : Mono (sch.map j) := by
  rw [NatTrans.mono_iff_mono_app]; intro n
  rw [NatTrans.mono_iff_mono_app]; intro T
  rw [mono_iff_injective]; intro a b h
  exact (cancel_mono j).1 h

theorem sub_of_iso {E E' : Spc} (i : E ≅ E') (F : Shv R) (n : ℤ) [Subsingleton (H R E' F n)] :
    Subsingleton (H R E F n) := by
  constructor; intro x y
  have hx : x = pull R i.hom F n (pull R i.inv F n x) := by rw [← pull_comp, i.hom_inv_id, pull_id]
  have hy : y = pull R i.hom F n (pull R i.inv F n y) := by rw [← pull_comp, i.hom_inv_id, pull_id]
  rw [hx, hy, Subsingleton.elim (pull R i.inv F n x) (pull R i.inv F n y)]

theorem sub_of_zero (E : Spc) (h : ∀ p, IsZero (((chains R).obj E).X p)) (F : Shv R) (n : ℤ) :
    Subsingleton (H R E F n) := by
  constructor; intro x y
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  exact (h p).eq_of_src _ _

theorem bij_of_sub {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) [Subsingleton (H R E F n)]
    [Subsingleton (H R E' F n)] : Function.Bijective (pull R f F n) :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

instance freeModPresE : PreservesColimitsOfShape (Discrete PEmpty.{1}) (ModuleCat.free.{1} (ULift.{1} R)) := by
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.free.{1} (ULift.{1} R)) :=
    (ModuleCat.adj.{1} (ULift.{1} R)).leftAdjoint_preservesColimits
  infer_instance

instance freePresE : PreservesColimitsOfShape (Discrete PEmpty.{1}) (free R) := by unfold free freeP; infer_instance

theorem chains_zero_of_initial (E : Spc) (hE : IsInitial E) (p : ℤ) : IsZero (((chains R).obj E).X p) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p
  · obtain ⟨j, hj⟩ := h
    have h1 : IsInitial (E.obj (op (SimplexCategory.mk j))) :=
      IsInitial.isInitialObj ((evaluation _ _).obj (op (SimplexCategory.mk j))) _ hE
    have h2 : IsInitial ((free R).obj (E.obj (op (SimplexCategory.mk j)))) := IsInitial.isInitialObj (free R) _ h1
    have hz : IsZero (((chainsN R).obj E).X j) := h2.isZero
    exact hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj E) ComplexShape.embeddingDownNat hj)
  · push Not at h
    exact HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p h

end LateralTheory.E.DescEqvPf

namespace LateralTheory.E.DescEqvPf

variable {A R0 R1 : Type} [CommRing A] [CommRing R0] [CommRing R1] (e : A ≃+* R0 × R1)

def psi : Spec (.of R0) ⨿ Spec (.of R1) ⟶ Spec (.of A) :=
  coprodSpec R0 R1 ≫ Spec.map (CommRingCat.ofHom e.toRingHom)

instance : IsIso (psi e) := by
  unfold psi
  have : IsIso (CommRingCat.ofHom e.toRingHom) := (e.toCommRingCatIso).isIso_hom
  infer_instance

theorem inl_psi : coprod.inl ≫ psi e = Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) := by
  rw [psi, coprodSpec_inl_assoc, ← Spec.map_comp]; rfl

theorem inr_psi : coprod.inr ≫ psi e = Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) := by
  rw [psi, coprodSpec_inr_assoc, ← Spec.map_comp]; rfl

instance oi0 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))) := by
  rw [← inl_psi]; infer_instance

instance oi1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom))) := by
  rw [← inr_psi]; infer_instance

theorem empty_pb : IsEmpty ↥(Limits.pullback (C := Scheme.{0}) (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) := by
  refine ⟨fun z => ?_⟩
  have h := pullback.condition (f := Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (g := Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))
  have k0 : Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) ≫ inv (psi e) = coprod.inl := by
    rw [← inl_psi]; simp
  have k1 : Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) ≫ inv (psi e) = coprod.inr := by
    rw [← inr_psi]; simp
  have h2 := congrArg (fun f => (f ≫ inv (psi e)).base z) h
  simp only [Category.assoc] at h2
  rw [k0, k1, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
  exact Set.disjoint_left.mp (isCompl_range_inl_inr (Spec (.of R0)) (Spec (.of R1))).disjoint ⟨_, rfl⟩ ⟨_, h2.symm⟩

end LateralTheory.E.DescEqvPf

namespace LateralTheory.E.DescEqvPf

variable {R : Type} [CommRing R]

instance schPresPb : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance

theorem eqv_id (E : Spc) (F : Shv R) : Eqv R (𝟙 E) F := fun n =>
  ⟨fun a b h => by rwa [pull_id, pull_id] at h, fun y => ⟨y, pull_id R E F n y⟩⟩

theorem loc_coprod (U V : Spc) : LateralTheory.E.D2.LocCover (coprod.inl : U ⟶ U ⨿ V) coprod.inr := by
  intro n X x
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, ?_⟩
  intro Y k _
  let G : Spc ⥤ Type := (evaluation _ _).obj (op (SimplexCategory.mk n)) ⋙ (evaluation _ _).obj (op X)
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (isColimitOfPreserves G (coprodIsCoprod U V)) x
  rcases j with ⟨(_ | _)⟩
  · left
    refine ⟨(U.obj _).map k.op y, ?_⟩
    rw [← hy]
    exact NatTrans.naturality_apply ((coprod.inl : U ⟶ U ⨿ V).app (op (SimplexCategory.mk n))) k.op y
  · right
    refine ⟨(V.obj _).map k.op y, ?_⟩
    rw [← hy]
    exact NatTrans.naturality_apply ((coprod.inr : V ⟶ U ⨿ V).app (op (SimplexCategory.mk n))) k.op y

theorem cover_coprod (U V : Spc) : Cover2 R (coprod.inl : U ⟶ U ⨿ V) coprod.inr :=
  LateralTheory.E.LeafCover2Pf.LeafCover2_of R _ _ inferInstance inferInstance (loc_coprod U V)

theorem sub_pb_coprod (U V : Spc) (F : Shv R) (n : ℤ) :
    Subsingleton (H R (pullback (coprod.inl : U ⟶ U ⨿ V) coprod.inr) F n) := by
  have hP := FinitaryExtensive.isPullback_initial_to_binaryCofan (coprodIsCoprod U V)
  have hI : IsInitial (pullback (coprod.inl : U ⟶ U ⨿ V) coprod.inr) :=
    by
      set_option synthInstance.maxHeartbeats 200000 in
        exact IsInitial.ofIso initialIsInitial hP.isoPullback
  exact sub_of_zero _ (chains_zero_of_initial _ hI) F n

variable {A R0 R1 : Type} [CommRing A] [CommRing R0] [CommRing R1] (e : A ≃+* R0 × R1)

theorem loc_sch : LateralTheory.E.D2.LocCover (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
    (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) := by
  intro n X x
  let x' : X ⟶ Spec (.of A) := x
  let C : Scheme.OpenCover.{0} X := (coprodOpenCover.{0} (Spec (.of R0)) (Spec (.of R1))).pullback₁ (x' ≫ inv (psi e))
  refine ⟨Sieve.ofArrows C.X C.f, Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro Y k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨i, h, rfl⟩ := hk
  rcases i with (_ | _)
  · left
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    have c := pullback.condition (f := x' ≫ inv (psi e)) (g := (coprod.inl : Spec (.of R0) ⟶ _))
    have c' : pullback.fst (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _) ≫ x' =
        pullback.snd (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _) ≫
          Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) := by
      rw [← inl_psi, ← Category.assoc, ← c]; simp
    change (h ≫ pullback.snd (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _)) ≫
        Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)) =
      (h ≫ pullback.fst (x' ≫ inv (psi e)) (coprod.inl : Spec (.of R0) ⟶ _)) ≫ x'
    exact (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) c'.symm).trans (Category.assoc _ _ _).symm)
  · right
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    have c := pullback.condition (f := x' ≫ inv (psi e)) (g := (coprod.inr : Spec (.of R1) ⟶ _))
    have c' : pullback.fst (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _) ≫ x' =
        pullback.snd (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _) ≫
          Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) := by
      rw [← inr_psi, ← Category.assoc, ← c]; simp
    change (h ≫ pullback.snd (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _)) ≫
        Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)) =
      (h ≫ pullback.fst (x' ≫ inv (psi e)) (coprod.inr : Spec (.of R1) ⟶ _)) ≫ x'
    exact (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) c'.symm).trans (Category.assoc _ _ _).symm)

theorem cover_sch : Cover2 R (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
    (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) :=
  LateralTheory.E.LeafCover2Pf.LeafCover2_of R _ _ (mono_sch _) (mono_sch _) (loc_sch e)

theorem sub_pb_sch (F : Shv R) (n : ℤ) :
    Subsingleton (H R (pullback (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom))))
      (sch.map (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom))))) F n) := by
  have := empty_pb e
  have := LateralTheory.E.LeafKunEmptyPf.H_sub (R := R) (Limits.pullback (C := Scheme.{0})
    (Spec.map (CommRingCat.ofHom ((RingHom.fst R0 R1).comp e.toRingHom)))
    (Spec.map (CommRingCat.ofHom ((RingHom.snd R0 R1).comp e.toRingHom)))) F n
  exact sub_of_iso (PreservesPullback.iso sch _ _).symm F n

end LateralTheory.E.DescEqvPf

theorem LateralTheory.E.BinPf.DescEqv_of : LateralTheory.E.BinPf.DescEqv := by
  intro H q A R0 R1 _ _ _ e i
  open LateralTheory.E.DescEqvPf in
  exact H.a4 (ZMod q) (coprod.inl : sp R0 ⟶ sp R0 ⨿ sp R1) coprod.inr
    (spMap ((RingHom.fst R0 R1).comp e.toRingHom)) (spMap ((RingHom.snd R0 R1).comp e.toRingHom)) _ (𝟙 _) (𝟙 _) (by rw [Category.id_comp]; exact coprod.inl_desc _ _)
    (by rw [Category.id_comp]; exact coprod.inr_desc _ _) (tw q i)
    (cover_coprod _ _) (cover_sch e) (eqv_id _ _) (eqv_id _ _)
    (fun n => by
      have := sub_pb_coprod (R := ZMod q) (sp R0) (sp R1) (tw q i) n
      have := sub_pb_sch (R := ZMod q) e (tw q i) n
      exact bij_of_sub _ _ n)
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf

namespace LateralTheory.E.KillCokPf

def Pointwise : Prop := B1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D) (O : CommRingCat.{0}) (o : D ⟶ O), IE o → BC q i φ (d ≫ o) →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (m : ℤ) (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) (Q : Ideal O), Q.IsPrime →
  ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = Q.comap o.hom ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)

def Assemble : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m),
  (∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = r ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e ∧ SpS e ∧ IsPushout φ' e u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem KillCok_of (hC : Coprod) (hP : Pointwise) (hA : Assemble) : LateralTheory.E.DescLocPf.Fine.KillCok := by
  intro hH q _ i n A Y φ hq P _ het _ D d hD hpts Y' w φ' hpo m _ y
  have hB1 : B1 := hH.2.2.2.2.2.2.1
  have hloc : ∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧
      Q₁.comap e.hom = r ∧ ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m) := by
    intro r hr
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts r hr
    obtain ⟨D₁, e, Q₁, he, hQ₁, hc, rest⟩ := hP hB1 q i φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
    exact ⟨D₁, e, Q₁, he, hQ₁, hc.trans hQr, rest⟩
  obtain ⟨E, e, Y'', u, φ'', he, hs, hpo', hy⟩ := hA hC q i φ' m y hloc
  exact ⟨E, e, Y'', u, φ'', he, hs, het d e hD he, hpo', hy⟩

end LateralTheory.E.KillCokPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.CorePf

theorem inf_nonempty {X : Type} [TopologicalSpace X] [PreirreducibleSpace X] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens X) (hU : ∀ j, (U j : Set X).Nonempty) :
    ∀ s : Finset (Fin n), s.Nonempty → ((s.inf U : TopologicalSpace.Opens X) : Set X).Nonempty := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hU a
  | cons a s ha hs ih =>
    rw [Finset.inf_cons, TopologicalSpace.Opens.coe_inf]
    exact nonempty_preirreducible_inter (U a).2 (s.inf U).2 (hU a) ih

end LateralTheory.E.CorePf

end
end
