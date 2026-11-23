module

public import Development.EtaleCohomology.EtaleSheaves.Bundle029
public import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.LevelsOfGen
import Development.EtaleCohomology.EtaleSheaves.CechLevels
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Mathlib.Topology.LocallyConstant.Algebra
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
import Development.EtaleCohomology.EtaleSheaves.Bundle028

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafEvMkPf

variable {R : Type} [CommRing R]

def preLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.ofHom (Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down))
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y'
    obtain ⟨y⟩ := y'
    have := ha V.unop U.unop g.unop y
    simp only [Sec.res, Quiver.Hom.op_unop, op_unop] at this
    dsimp [freeP]
    change (Finsupp.lift (F.obj.obj V) (ULift.{1} R) (ULift.{1} (P.obj V)) (fun y => a V.unop y.down))
        (Finsupp.mapDomain (fun x : ULift.{1} (P.obj U) => ULift.up (P.map g x.down)) (Finsupp.single (ULift.up y) 1)) =
      F.obj.map g ((Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down)) (Finsupp.single (ULift.up y) 1))
    rw [Finsupp.mapDomain_single, Finsupp.lift_apply, Finsupp.lift_apply, Finsupp.sum_single_index, Finsupp.sum_single_index]
    · simpa using this.symm
    all_goals simp

theorem preLift_app {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((preLift a ha).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = a U x := by
  show (Finsupp.lift (F.obj.obj (op U)) (ULift.{1} R) (ULift.{1} (P.obj (op U))) (fun y => a U y.down)) (Finsupp.single (ULift.up x) 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

def shLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (free R).obj P ⟶ F :=
  ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (preLift a ha) F.property)

theorem shLift_gen {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((shLift a ha).hom.app (op U)).hom (freeGen R P U x) = a U x := by
  unfold freeGen
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyLift Scheme.etaleTopology (preLift a ha) F.property).app (op U)).hom _ = _
  rw [toSheafify_sheafifyLift]
  exact preLift_app a ha U x

variable {E : Spc} {I : Cx R} {n : ℤ}

def comp (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : ((chains R).obj E).X (-(p : ℤ)) ⟶ I.X s :=
  (chainsXIso R E p).hom ≫ shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x)

theorem comp_key (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p q : ℕ) (hq : q = p) (s : ℤ) (h : -(p : ℤ) + n = s) (h' : -(q : ℤ) + n = s)
    (e : ((chains R).obj E).X (-(p : ℤ)) = ((chains R).obj E).X (-(q : ℤ))) :
    (chainsXIso R E p).inv ≫ eqToHom e ≫ comp a ha q s h' =
      shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x) := by
  subst hq
  simp [comp]

theorem LeafEvMk_of : LateralTheory.E.ChernClassExistence.LeafEvMk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk fun i j hij => if hi : i ≤ 0 then
      eqToHom (congrArg (fun k => ((chains R).obj E).X k) (by omega : i = -(((-i).toNat : ℕ) : ℤ))) ≫
        comp a ha ((-i).toNat) j (by omega) else 0, ?_⟩
  intro p s h U x
  unfold ev
  rw [Cochain.mk_v, dite_eq_left (by omega), comp_key a ha p _ (by omega) s h]
  exact shLift_gen _ _ U x

end LateralTheory.E.LeafEvMkPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.OpenCov_ptaPf

variable (R : Type) [CommRing R]

abbrev gen (P : PSh) {W : Scheme.{0}ᵒᵖ} (x : P.obj W) : ((freeP R).obj P).obj W :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj W)) (ULift.up x)

abbrev adj {P : PSh} {G : Shv R} (a : (free R).obj P ⟶ G) : (freeP R).obj P ⟶ G.obj :=
  toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ a.hom

theorem adj_inj {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G) (h : adj R a = adj R b) : a = b := by
  ext1
  exact sheafify_hom_ext _ _ _ G.property h

theorem adj_comp {P Q : PSh} {G : Shv R} (φ : P ⟶ Q) (a : (free R).obj Q ⟶ G) :
    adj R ((free R).map φ ≫ a) = (freeP R).map φ ≫ adj R a := by
  show toSheafify _ _ ≫ (sheafifyMap _ ((freeP R).map φ) ≫ a.hom) = _
  show _ = (freeP R).map φ ≫ toSheafify _ _ ≫ a.hom
  erw [toSheafify_naturality_assoc]

theorem freePresheaf_obj_map_freeMk (P : PSh) {W W' : Scheme.{0}ᵒᵖ} (h : W ⟶ W') (x : P.obj W) :
    ((freeP R).obj P).map h (gen R P x) = gen R P (P.map h x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

theorem freePresheaf_map_freeMk {P Q : PSh} (φ : P ⟶ Q) (W : Scheme.{0}ᵒᵖ) (x : P.obj W) :
    ((freeP R).map φ).app W (gen R P x) = gen R Q (φ.app W x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

theorem adj_val {X Y : Scheme.{0}} {G : Shv R} (a : (free R).obj (yoneda.obj X) ⟶ G) (x : Y ⟶ X) :
    (adj R a).app (op Y) (gen R (yoneda.obj X) (W := op Y) x) =
      G.obj.map x.op ((adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X))) := by
  rw [← ConcreteCategory.comp_apply, ← (adj R a).naturality, ConcreteCategory.comp_apply, freePresheaf_obj_map_freeMk]
  simp

theorem ext_of_cover {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hcov : Set.range f ∪ Set.range g = Set.univ) {G : Shv R} (a b : (free R).obj (yoneda.obj X) ⟶ G)
    (hf : (free R).map (yoneda.map f) ≫ a = (free R).map (yoneda.map f) ≫ b)
    (hg : (free R).map (yoneda.map g) ≫ a = (free R).map (yoneda.map g) ≫ b) : a = b := by
  let Z : Bool → Scheme.{0} := fun i => Bool.rec V U i
  let φ : ∀ i, Z i ⟶ X := fun i => Bool.rec (motive := fun i => Z i ⟶ X) g f i
  have hS : Sieve.ofArrows Z φ ∈ Scheme.etaleTopology X := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => ?_⟩
    · have hx : x ∈ Set.range f ∪ Set.range g := hcov ▸ Set.mem_univ x
      rcases hx with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩
    · cases i <;> infer_instance
  have hf' := congrArg (adj R) hf
  have hg' := congrArg (adj R) hg
  rw [adj_comp, adj_comp] at hf' hg'
  have key : (adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) =
      (adj R b).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) := by
    refine Presheaf.IsSheaf.isSeparated G.property _ _ hS _ _ ?_
    intro Y' h hh
    obtain ⟨W, k, _, ⟨i⟩, rfl⟩ := hh
    rw [← adj_val, ← adj_val]
    cases i
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj V) (W := op _) k)) hg'
      simpa [freePresheaf_map_freeMk] using this
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj U) (W := op _) k)) hf'
      simpa [freePresheaf_map_freeMk] using this
  apply adj_inj
  ext Y : 2
  induction Y with | op Y => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact (adj_val R a x).trans ((congrArg _ key).trans (adj_val R b x).symm)

theorem openCov : LateralTheory.E.MayerVietorisSequence.OpenCov := by
  intro R _ U V X f g _ _ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance
  have : sch.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  refine ⟨inferInstance, inferInstance, fun n => ⟨fun {G} a b h => ?_⟩⟩
  apply ext_of_cover R f g hcov a b
  · have h1 : (free R).map ((sch.map f).app n) ≫ a = (free R).map ((sch.map f).app n) ≫ b := by
      simpa using congrArg (biprod.inl ≫ ·) h
    exact h1
  · have h1 : (free R).map ((sch.map g).app n) ≫ a = (free R).map ((sch.map g).app n) ≫ b := by
      simpa using congrArg (biprod.inr ≫ ·) h
    exact h1

end LateralTheory.E.OpenCov_ptaPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

def IsCop {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) : Prop :=
  ∀ (R : Type) [CommRing R] (g : ι → (A' →+* R)) (c : A →+* R), (∀ i, (g i).comp φ = c) →
    ∃! h : B →+* R, (∀ i, h.comp (l i) = g i) ∧ h.comp χ = c

theorem le_l {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : I.map φ ≤ (I.map χ).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hf]

abbrev lq {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : A' ⧸ I.map φ →+* B ⧸ I.map χ :=
  Ideal.quotientMap (I.map χ) f (le_l φ χ f hf I)

def coneOf {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) :
    Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : ι => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))) :=
  WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom χ))) (fun i => yoneda.map (Spec.map (CommRingCat.ofHom (l i))))
    (fun i => by
      change yoneda.map _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom φ)) = _
      rw [← yoneda.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i])

def SpecLim : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) (n : ℕ)
  (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ), IsCop φ χ l → Nonempty (IsLimit (coneOf φ χ l hl))

def TensCop : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (n : ℕ),
  ∃ (B : Type) (_ : CommRing B) (χ : A →+* B) (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ),
    Subring.closure (⋃ i, Set.range (l i)) = ⊤ ∧ IsCop φ χ l

def QuotCop : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A), IsCop φ χ l →
    IsCop (qm φ I) (qm χ I) (fun i => lq φ χ (l i) (hl i) I)

theorem lq_hl {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A) (i : ι) :
    (lq φ χ (l i) (hl i) I).comp (qm φ I) = qm χ I := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [qm, lq, ← hl i]

theorem ysq {R S S' T : Type} [CommRing R] [CommRing S] [CommRing S'] [CommRing T] (f : R →+* S) (g : S →+* T)
    (f' : R →+* S') (g' : S' →+* T) (h : g.comp f = g'.comp f') :
    yoneda.map (Spec.map (CommRingCat.ofHom g)) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f)) =
      yoneda.map (Spec.map (CommRingCat.ofHom g')) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f')) := by
  rw [← yoneda.map_comp, ← yoneda.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, h]

theorem LevelsGen_of (hT : TensCop) (hQ : QuotCop) (hS : SpecLim) : LevelsGen := by
  intro A A' _ _ φ I p
  obtain ⟨B, _, χ, l, hl, hc, hcop⟩ := hT A A' φ (p.unop.len)
  refine ⟨B, inferInstance, χ, _, l, hl, hc, ?_⟩
  obtain ⟨L⟩ := hS A A' B φ χ _ l hl hcop
  obtain ⟨Lr⟩ := hS _ _ _ (qm φ I) (qm χ I) _ _ (lq_hl φ χ l hl I) (hQ A A' B φ χ l hl I hcop)
  let e : (cech (Spec.map (CommRingCat.ofHom φ))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of B)) := (limit.isLimit _).conePointUniqueUpToIso L
  let er : (cech (Spec.map (CommRingCat.ofHom (qm φ I)))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of (B ⧸ I.map χ))) := (limit.isLimit _).conePointUniqueUpToIso Lr
  refine ⟨Arrow.isoMk er e ?_⟩
  simp only [Arrow.mk_hom]
  apply L.hom_ext
  rintro (_|i)
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (qm χ I))) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr none
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L none
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ))
    rw [Category.assoc, Category.assoc, h2, ysq χ (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk I) (qm χ I) (qm_comp χ I).symm,
      ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_right]
    erw [WidePullback.lift_base]
    all_goals rfl
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (lq φ χ (l i) (hl i) I))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr (some i)
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L (some i)
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i)))
    rw [Category.assoc, Category.assoc, h2, ysq (l i) (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk (I.map φ))
      (lq φ χ (l i) (hl i) I) (Ideal.quotientMap_comp_mk _).symm, ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_left]
    erw [WidePullback.lift_π]
    all_goals rfl

end LateralTheory.E.LevelsGenPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartSurjCut

def Root : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  AICSch Z → IsUnit (q : A) → Nonempty (Prim q Γ(Z, ⊤))

def LCIso : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Ht q (sch.obj X) 0 i,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      pull _ (sch.map f) (tw q i) 0 (e X s g) = e Y t (g.comap f.base.hom)

end LateralTheory.E.ChartSurjCut
end
end
