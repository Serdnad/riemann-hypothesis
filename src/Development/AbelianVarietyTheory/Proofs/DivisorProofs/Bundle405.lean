module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.GrothendieckAbelian
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ShfLoc

instance wEqLB (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end GlobalTheory.EtC.ShfLoc


open GlobalTheory.EtC.ShfLoc in
theorem GlobalTheory.EtC.toSheafify_loc_bij_lift : ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ := by
  intro R _ P
  refine ⟨?_, ?_, ?_⟩
  · intro U y
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y,
      fun V g hg => hg⟩
  · intro U x hx
    have h : ((toSheafify Scheme.etaleTopology P).app (op U)).hom x =
        ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by rw [hx, map_zero]
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h,
      fun V g hg => ?_⟩
    have h' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    show (P.map g.op).hom x = 0
    rw [h', map_zero]
  · intro F φ
    refine ⟨⟨sheafifyLift Scheme.etaleTopology φ F.property⟩, toSheafify_sheafifyLift _ _ _, ?_⟩
    intro ψ hψ
    ext1
    exact sheafifyLift_unique _ _ _ _ hψ
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.BiprodPush

variable {R : Type} [CommRing R]

theorem cpush_comp (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f ≫ g) n x = cpush K g n (cpush K f n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  congr 1

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  rw [← CohomologyClass.mk_add]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem cpush_zero (K : Cx R) {I J : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  rw [← CohomologyClass.mk_zero]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_zero]

theorem cpush_id (K : Cx R) {I : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (𝟙 I) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  congr 1
  ext1
  simp [zcomp]

def cpushHom (K : Cx R) (I J : Cx R) (n : ℤ) (x : CohomologyClass K I n) : (I ⟶ J) →+ CohomologyClass K J n where
  toFun f := cpush K f n x
  map_zero' := cpush_zero K n x
  map_add' f g := cpush_add K f g n x

theorem cpush_sum (K : Cx R) {I J : Cx R} {ι : Type} (s : Finset ι) (f : ι → (I ⟶ J)) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (∑ j ∈ s, f j) n x = ∑ j ∈ s, cpush K (f j) n x :=
  map_sum (cpushHom K I J n x) f s

end GlobalTheory.BiprodPush

end

noncomputable section

namespace GlobalTheory.BiprodPush

theorem injective_of_retracts {C : Type*} [Category C] [Preadditive C] {ι : Type} [Fintype ι] {X : C} (Y : ι → C)
    [∀ j, Injective (Y j)] (p : ∀ j, X ⟶ Y j) (i : ∀ j, Y j ⟶ X) (h : ∑ j, p j ≫ i j = 𝟙 X) : Injective X := by
  refine ⟨fun {A B} g m _ => ⟨∑ j, Injective.factorThru (g ≫ p j) m ≫ i j, ?_⟩⟩
  rw [Preadditive.comp_sum]
  simp_rw [← Category.assoc, Injective.comp_factorThru, Category.assoc, ← Preadditive.comp_sum, h, Category.comp_id]

theorem biproduct_push : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (g : ∀ j, L j ⟶ C) (m : ℤ), (∀ j, (L j).IsStrictlyGE m) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) n) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpush K (g j) n (a j) := by
  intro R _ ι _ L C g m hL hI
  classical
  haveI : HasFiniteBiproducts (Cx R) := HasFiniteBiproducts.of_hasFiniteProducts
  have htot : ∀ n, ∑ j, (biproduct.π L j).f n ≫ (biproduct.ι L j).f n = 𝟙 ((⨁ L).X n) := by
    intro n
    have := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_sum (fun j => biproduct.π L j ≫ biproduct.ι L j) Finset.univ
    rw [biproduct.total] at this
    simp only [Functor.map_id, Functor.map_comp, HomologicalComplex.eval_map] at this
    exact this.symm
  refine ⟨⨁ L, biproduct.desc g, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero, ← htot i]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : IsZero ((L j).X i) := (L j).isZero_of_isStrictlyGE m i hi
    rw [show (biproduct.π L j).f i = 0 from this.eq_of_tgt _ _, zero_comp]
  · intro n
    exact injective_of_retracts (fun j => (L j).X n) (fun j => (biproduct.π L j).f n) (fun j => (biproduct.ι L j).f n) (htot n)
  · intro K n
    refine ⟨{ toFun := fun a => ∑ j, cpush K (biproduct.ι L j) n (a j)
              invFun := fun b j => cpush K (biproduct.π L j) n b
              left_inv := ?_
              right_inv := ?_ }, ?_⟩
    · intro a
      funext k

      simp only [map_sum, ← cpush_comp]
      rw [Finset.sum_eq_single k]
      · rw [biproduct.ι_π_self, cpush_id]
      · intro j _ hj
        rw [biproduct.ι_π_ne _ hj, cpush_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    · intro b
      simp only [← cpush_comp]
      rw [← cpush_sum, biproduct.total, cpush_id]
    · intro a
      change cpush K (biproduct.desc g) n (∑ j, cpush K (biproduct.ι L j) n (a j)) = _

      rw [map_sum]
      simp only [← cpush_comp, biproduct.ι_desc]

end GlobalTheory.BiprodPush

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

def unitsT : CommRingCat.{0} ⥤ Type where
  obj A := (A : Type)ˣ
  map {A B} f := TypeCat.ofHom fun (u : (A : Type)ˣ) => Units.map f.hom.toMonoidHom u
  map_id A := by ext u; rfl
  map_comp f g := by ext u; rfl

structure Trip (q : ℕ) (A : Type) [CommRing A] where
  root : Prim q A
  src : Aˣ
  tgt : Aˣ
  tgt_eq : (tgt : A) = root.1 * src

def Trip.map {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Trip q A) : Trip q B :=
  ⟨x.root.map f, Units.map f.toMonoidHom x.src, Units.map f.toMonoidHom x.tgt, by
    change f (x.tgt : A) = f x.root.1 * f (x.src : A)
    rw [x.tgt_eq, map_mul]⟩

def tripT (q : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Trip q A
  map f := TypeCat.ofHom (Trip.map f.hom)
  map_id A := by
    ext x
    cases x
    rfl
  map_comp f g := by
    ext x
    cases x
    rfl

def unitsP : PSh := Scheme.Γ ⋙ unitsT

def tripP (q : ℕ) : PSh := Scheme.Γ ⋙ tripT q

def unitsP.mk {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) : unitsP.obj (op U) := v

def tripP.mk {q : ℕ} {U : Scheme.{0}} (x : Trip q Γ(U, ⊤)) : (tripP q).obj (op U) := x

def tripP.get {q : ℕ} {U : Scheme.{0}} (x : (tripP q).obj (op U)) : Trip q Γ(U, ⊤) := x

theorem unitsP.map_mk {V U : Scheme.{0}} (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ) :
    unitsP.map g.op (unitsP.mk v) = unitsP.mk (Units.map g.appTop.hom.toMonoidHom v) := rfl

theorem smap_sum {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.map φ (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.map φ (f x) := by
  simp only [Sec.map, map_finsuppSum, map_smul]

theorem res_sum {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.res g (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.res g (f x) := by
  simp only [Sec.res, map_finsuppSum, map_smul]

theorem smap_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _

theorem res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _

theorem res_zero' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sec_eq_zero_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (s : Sec F U)
    (h : Loc U fun _ g => Sec.res g s = 0) : s = 0 := by
  obtain ⟨S, hS, hS'⟩ := h
  exact Sheaf.isSeparated F U S hS s 0 (fun V g hg => (hS' V g hg).trans (map_zero _).symm)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U)) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

end GlobalTheory.EtC.KummerSplit
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.KumPic

abbrev twZ (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def dv (q : ℕ) (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res ℤ (twZ q)).X 0) U :=
  Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v)

end GlobalTheory.EtC.KumPic

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem loc_of_forall (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := hP
  obtain ⟨T, hT, hQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT,
    fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem loc_pullback (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S.pullback k, Scheme.etaleTopology.pullback_stable k hS, fun V g hg => hP V (g ≫ k) hg⟩

theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hloc⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := fun {W W'} h hh k W'' k' => by
        simpa [Category.assoc] using hh W'' (k' ≫ k) }
  refine ⟨R, Scheme.etaleTopology.transitive hS R ?_, fun V g hg => by simpa using hg V (𝟙 V)⟩
  intro V g hg
  obtain ⟨T, hT, hP⟩ := hloc V g hg
  refine Scheme.etaleTopology.superset_covering ?_ hT
  intro W k hk W' k'
  have := hP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

theorem loc_top (U : Scheme.{0}) : Loc U fun _ _ => True :=
  loc_of_forall U _ fun _ _ => trivial

theorem loc_finset (U : Scheme.{0}) {ι : Type} (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_of_forall U _ fun V g i hi => absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  have := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U P h Finset.univ) fun V g hg i => hg i (Finset.mem_univ i)

theorem loc_of_isEmpty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) :
    Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

theorem loc_calculus :
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → Loc U P) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → (∀ V g, P V g → Q V g) → Loc U Q) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc U Q → Loc U fun V g => P V g ∧ Q V g) ∧
    (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc W fun V g => P V (g ≫ k)) ∧
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U (fun V g => Loc V fun W k => P W (k ≫ g)) → Loc U P) ∧
    (∀ (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i, Loc U (P i)) → Loc U fun V g => ∀ i, P i V g) ∧
    (∀ (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P) :=
  ⟨loc_of_forall, loc_mono, loc_and, loc_pullback, loc_trans, loc_finite, loc_of_isEmpty⟩

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem flatS_iso_and_zero : ∀ (R : Type) [CommRing R], (∀ {M N : Shv R}, (M ≅ N) → FlatS M → FlatS N) ∧ ∀ M : Shv R, IsZero M → FlatS M := by
  intro R _
  refine ⟨?_, ?_⟩
  · intro M N e ⟨P, φ, hs, hi, hf⟩
    refine ⟨P, φ ≫ e.hom.hom, ?_, ?_, hf⟩
    · intro U y
      obtain ⟨S, hS, hy⟩ := hs U (Sec.map e.inv y)
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hy V g hg
      refine ⟨x, ?_⟩
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [hx]
      have h1 := congrArg ModuleCat.Hom.hom (e.hom.hom.naturality g.op)
      have h2 := congrArg (fun (f : N ⟶ N) => (f.hom.app (op U)).hom y) e.inv_hom_id
      simp only [ModuleCat.hom_comp] at h1
      have h3 := LinearMap.congr_fun h1 ((e.inv.hom.app (op U)).hom y)
      simp only [LinearMap.comp_apply] at h3
      simp only [Sec.res, Sec.map]
      rw [h3]
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h2
      rw [h2]
    · intro U x hx
      apply hi U x
      have h2 := congrArg (fun (f : M ⟶ M) => (f.hom.app (op U)).hom ((φ.app (op U)).hom x)) e.hom_inv_id
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h2
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
      rw [← h2, hx, map_zero]
  · intro M hM
    refine ⟨(Functor.const _).obj (ModuleCat.of (ULift.{1} R) PUnit.{2}), 0, ?_, ?_, ?_⟩
    · intro U y
      refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨0, ?_⟩⟩
      have h := congrArg (fun (f : M ⟶ M) => (f.hom.app (op V)).hom (Sec.res g y)) (hM.eq_of_src (𝟙 M) 0)
      simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h
      rw [h]
      simp
    · intro U x _
      exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ => Subsingleton.elim (α := PUnit.{2}) _ _⟩
    · intro U _
      show Module.Flat (ULift.{1} R) PUnit.{2}
      infer_instance

end GlobalTheory.EtC
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

section ExtScalars
variable {R S : Type} [CommRing R] [CommRing S]

def uliftHom (φ : R →+* S) : ULift.{1} R →+* ULift.{1} S :=
  (ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)

instance extendScalars_uliftHom_additive (φ : R →+* S) :
    (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)).Additive where
  map_add {M N} g h := by
    letI := (uliftHom φ).toAlgebra
    ext m
    exact TensorProduct.tmul_add (R := ULift.{1} R) (1 : ULift.{1} S) (g.hom m) (h.hom m)

def extSh (φ : R →+* S) : Shv R ⥤ Shv S :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)) ⋙
    presheafToSheaf _ _

instance (φ : R →+* S) : (extSh φ).Additive := by
  unfold extSh; infer_instance

def extSh.sec (φ : R →+* S) (F : Shv R) (U : Scheme.{0}) : Sec F U →+ Sec ((extSh φ).obj F) U :=
  ((toSheafify Scheme.etaleTopology (F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))).app (op U)).hom.toAddMonoidHom.comp
    ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom.toAddMonoidHom

theorem extSh.sec_res (φ : R →+* S) (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (extSh.sec φ F U a) = extSh.sec φ F V (Sec.res g a) := by
  have e1 := (toSheafify Scheme.etaleTopology (F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))).naturality g.op
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.naturality (F.obj.map g.op)
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e1)
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom a)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) a
  exact h1.symm.trans (congrArg _ h2.symm)

theorem extSh.sec_map (φ : R →+* S) {F G : Shv R} (f : F ⟶ G) (U : Scheme.{0}) (a : Sec F U) :
    Sec.map ((extSh φ).map f) (extSh.sec φ F U a) = extSh.sec φ G U (Sec.map f a) := by
  have e1 := NatTrans.congr_app (toSheafify_naturality Scheme.etaleTopology
      (Functor.whiskerRight f.hom (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)))) (op U)
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.naturality (f.hom.app (op U))
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e1)
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom a)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) a
  exact h1.symm.trans (congrArg _ h2.symm)

abbrev extCx (φ : R →+* S) (I : Cx R) : Cx S := ((extSh φ).mapHomologicalComplex _).obj I

def extπ (φ : R →+* S) (I : Cx R) : SemiMap I (extCx φ I) where
  app U s := extSh.sec φ (I.X s) U
  nat g s a := extSh.sec_res φ (I.X s) g a
  comm U s t a := extSh.sec_map φ (I.d s t) U a

def extAug (φ : R →+* S) (F : Shv R) : sgl ((extSh φ).obj F) ⟶ extCx φ (res R F) :=
  (HomologicalComplex.singleMapHomologicalComplex (extSh φ) (ComplexShape.up ℤ) 0).inv.app F ≫
    ((extSh φ).mapHomologicalComplex _).map (resAug F)

end ExtScalars

end GlobalTheory.EtC

end
end
