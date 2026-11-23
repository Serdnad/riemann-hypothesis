module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.EtaleCohomology.TateTwists.Bundle001
public import Development.EtaleCohomology.TateTwists.Bundle003
public import Development.EtaleCohomology.TateTwists.Bundle002
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.cc_cup_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ}
    (h : n + m = k) (h' : m + n = k) a b, μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a

def LateralTheory.EtaleFoundations.cc_flip_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν

def LateralTheory.EtaleFoundations.cc_twpair : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair (htw : LateralTheory.EtaleFoundations.cc_twpair) (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
    (a : Ht q E n i) (b : Ht q E m j) (k : ℤ) (hk : j + i = k)
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hν : IsTwPair ν) (w : ℤ) (hw : m + n = w) :
    ν.cup E hw b a = (cup q b a).cast hw hk := by
  subst hk hw
  obtain ⟨h1, h2⟩ := htw q j i
  have := h2 (j + i) rfl ν (twPair q j i) hν h1 E (n := m) (m := n) rfl
  rw [this]
  rfl

theorem LateralTheory.EtaleFoundations.etale_twisted_cup_graded_comm_of_flip_and_unique_pairing (hflip : LateralTheory.EtaleFoundations.cc_cup_flip) (hex : LateralTheory.EtaleFoundations.cc_flip_ex)
    (htw : LateralTheory.EtaleFoundations.cc_twpair) : LateralTheory.EtaleFoundations.EtaleTwistedCupProductGradedCommutative := by
  intro q _ E n m i j a b
  obtain ⟨ν, hν⟩ := hex (ZMod q) (twPair q i j)
  have hνtw : IsTwPair ν := by
    intro U ζ
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [this, (htw q i j).1 U ζ]
    simp
  have e1 : cup q a b = (n * m).negOnePow • ν.cup E (add_comm m n) b a :=
    hflip (ZMod q) (twPair q i j) ν hν E rfl (add_comm m n) a b
  rw [e1, LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair htw q E a b (i + j) (add_comm j i) ν hνtw (n + m) (add_comm m n)]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧ (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F ∧ Mono (resι R F) ∧ resι R F ≫ (res R F).d 0 1 = 0 ∧ ∀ (G : Shv R) (φ : F ⟶ G), resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G ∧ resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε], (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m')
end

section

namespace LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
theorem etale_cochain_complex_basic_properties_of_components : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  apply LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := etale_cochain_complex_basic_properties_of_components
end LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def EtaleKummerSectionsIntoTwistEmbeddingExist : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

def EtaleTwistExtendsThroughMonoToResolutionZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j →
    ∃ e : M ⟶ (res _ (tw q 1)).X 0, j ≫ e = resι _ (tw q 1)

theorem etale_kummer_torsor_class_exists_of_tors_and_ext (h1 : EtaleKummerSectionsIntoTwistEmbeddingExist) (h2 : EtaleTwistExtendsThroughMonoToResolutionZero) : EtaleKummerTriangleExists := by
  intro q _
  apply pick_spec
  obtain ⟨M, j, hj, s, hs1, hs2⟩ := h1 q
  obtain ⟨e, he⟩ := h2 q M j hj
  refine ⟨fun U v => Sec.map e (s U v), ?_, ?_⟩
  · intro V U g v hq
    show Sec.res g (Sec.map e (s U v)) = Sec.map e (s V _)
    rw [← hs1 V U g v hq]
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality g.op)) (s U v)).symm
  · intro U ζ v w h
    show Sec.map e (s U w) = Sec.map e (s U v) + _
    rw [hs2 U ζ v w h]
    show (e.hom.app (op U)).hom (_ + _) = _
    rw [map_add (f := _)]
    congr 1
    unfold resGen
    rw [← he]
    rfl
end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def kum_exists : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def kum_nat : Prop :=
  ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def kum_add : Prop :=
  ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

theorem kum_spec_of_exists (he : kum_exists) (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ)
    (hq : IsUnit (q : Γ(X, ⊤))) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v) := by
  obtain ⟨γ, h1, h2⟩ := he q X u hq
  unfold kum
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      CohomologyClass.mk γ = c ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    ⟨CohomologyClass.mk γ, γ, rfl, h1, h2⟩

theorem etale_kummer_class_specification_of_existence_naturality_additivity (he : kum_exists) (hn : kum_nat) (ha : kum_add) : EtaleKummerClassExplicitCocycle := by
  intro q _
  exact ⟨fun X u hq => kum_spec_of_exists he q X u hq, fun f u hq => hn q f u hq, fun u v hq => ha q u v hq⟩

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ConerveIsomorphism

variable {T : Type 1} [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ)
  {U V : T} (g : U ⟶ V)

noncomputable def phi (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ⟶
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun j => (Ψ.map (WidePushout.ι _ j)).unop)
    (fun j => by
      have h := WidePushout.arrow_ι (fun _ : Fin (n+1) => g) j
      rw [← unop_comp, ← Ψ.map_comp, h])

lemma phi_π (n : ℕ) (j : Fin (n+1)) :
    phi Ψ g n ≫ WidePullback.π _ j = (Ψ.map (WidePushout.ι _ j)).unop := by
  unfold phi; erw [WidePullback.lift_π]

lemma phi_base (n : ℕ) :
    phi Ψ g n ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  unfold phi; erw [WidePullback.lift_base]

lemma aux (n : ℕ) (j : Fin (n+1)) :
    Ψ.map g ≫ (WidePullback.π (fun _ : Fin (n+1) => (Ψ.map g).unop) j).op =
      (WidePullback.base (fun _ : Fin (n+1) => (Ψ.map g).unop)).op := by
  rw [← WidePullback.π_arrow (fun _ : Fin (n+1) => (Ψ.map g).unop) j]
  rfl

noncomputable def cocone (n : ℕ) : Cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g) ⋙ Ψ) where
  pt := op (widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop))
  ι :=
    { app := fun j => match j with
        | none => (WidePullback.base _).op
        | some j => (WidePullback.π _ j).op
      naturality := by
        rintro X Y (_ | j)
        · rw [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
            Category.id_comp, Category.comp_id]
        · exact (aux Ψ g n j).trans (Category.comp_id _).symm }

lemma natural (a b : ℕ) (σ : Fin (a+1) → Fin (b+1)) :
    (Ψ.map (WidePushout.desc (WidePushout.head (fun _ : Fin (b+1) => g))
      (fun i => WidePushout.ι (fun _ : Fin (b+1) => g) (σ i))
      (fun i => WidePushout.arrow_ι (fun _ : Fin (b+1) => g) (σ i)))).unop ≫ phi Ψ g a =
    phi Ψ g b ≫ WidePullback.lift (WidePullback.base (fun _ : Fin (b+1) => (Ψ.map g).unop))
      (fun i => WidePullback.π (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i))
      (fun i => WidePullback.π_arrow (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i)) := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, Category.assoc, phi_π, WidePullback.lift_π, phi_π, ← unop_comp, ← Ψ.map_comp,
      WidePushout.ι_desc]
  · rw [Category.assoc, Category.assoc, phi_base, WidePullback.lift_base, phi_base, ← unop_comp,
      ← Ψ.map_comp, WidePushout.head_desc]

variable (hΨ : ∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ)

noncomputable def hc (n : ℕ) :
    IsColimit (Ψ.mapCocone (colimit.cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g)))) :=
  haveI := hΨ n
  isColimitOfPreserves Ψ (colimit.isColimit _)

noncomputable def psi (n : ℕ) :
    widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) ⟶
      (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop :=
  ((hc Ψ g hΨ n).desc (cocone Ψ g n)).unop

lemma desc_phi (n : ℕ) : (hc Ψ g hΨ n).desc (cocone Ψ g n) ≫ (phi Ψ g n).op = 𝟙 _ := by
  apply (hc Ψ g hΨ n).hom_ext
  rintro (_ | j)
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)).trans (Quiver.Hom.unop_inj (phi_base Ψ g n)))
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))).trans (Quiver.Hom.unop_inj (phi_π Ψ g n j)))

noncomputable def levelIso (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ≅
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) where
  hom := phi Ψ g n
  inv := psi Ψ g hΨ n
  hom_inv_id := congrArg Quiver.Hom.unop (desc_phi Ψ g hΨ n)
  inv_hom_id := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, phi_π, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))
    · rw [Category.assoc, phi_base, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)

end LateralTheory.EtaleFoundations.ConerveIsomorphism

open LateralTheory.EtaleFoundations.ConerveIsomorphism in
theorem LateralTheory.EtaleFoundations.etale_cech_conerve_image_iso_cech_nerve_of_preserves_wide_pushouts : LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨NatIso.ofComponents (fun n => levelIso Ψ g hΨ n.unop.len) ?_, ?_⟩
  · intro m n h
    exact natural Ψ g _ _ h.unop.toOrderHom
  · ext n : 1
    exact (phi_base Ψ g (unop n).len).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FreeHomPf

variable (R : Type) [CommRing R]

noncomputable def desc (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : uliftFunctor.{1}.obj (P.obj U) => a U.unop x.down)
  naturality U W g := by
    apply ModuleCat.free_hom_ext
    intro x
    have := ha W.unop U.unop g.unop x.down
    simp only [Sec.res] at this
    simp only [freeP] at *
    simp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map, Functor.whiskeringRight_obj_map,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

lemma freePresheaf_map_generator {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (f.app (op U) x)) : ((freeP R).obj Q).obj (op U)) :=
  ModuleCat.free_map_apply _ _

lemma freePresheaf_obj_map_generator (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) =
      (ModuleCat.freeMk (ULift.up (P.map g.op x)) : ((freeP R).obj P).obj (op V)) :=
  ModuleCat.free_map_apply _ _

lemma gen_eq (P : PSh) (F : Shv R) (φ : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map φ (freeGen R P U x) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ φ.hom).app (op U)).hom
        (ModuleCat.freeMk (ULift.up x)) := rfl

end LateralTheory.EtaleFoundations.FreeHomPf

open LateralTheory.EtaleFoundations.FreeHomPf in
theorem LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  intro R _ P F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    refine ⟨⟨sheafifyLift Scheme.etaleTopology (desc R P F a ha) F.property⟩, fun U x => ?_⟩
    refine (gen_eq R P F _ U x).trans ?_
    rw [toSheafify_sheafifyLift]
    exact ModuleCat.freeDesc_apply _ _
  · intro φ ψ h
    apply Sheaf.hom_ext
    apply sheafify_hom_ext Scheme.etaleTopology _ _ F.property
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    have := h U.unop x.down
    rw [gen_eq, gen_eq] at this
    exact this
  · intro V U g x
    have hn := (toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafify Scheme.etaleTopology ((freeP R).obj P)).map g.op)).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).obj P).map g.op ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
            ((((freeP R).obj P).map g.op).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_obj_map_generator]; rfl
  · intro Q f U x
    have hn := congrArg (fun η => η.app (op U))
      (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
    calc _ = (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
          (sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := rfl
      _ = ((((freeP R).map f).app (op U) ≫
          (toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U))).hom
            (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U)) := by
              simp only [NatTrans.comp_app] at hn; rw [hn]
      _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom
            ((((freeP R).map f).app (op U)).hom
              (ModuleCat.freeMk (ULift.up x) : ((freeP R).obj P).obj (op U))) := rfl
      _ = _ := by rw [freePresheaf_map_generator]; rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_cup_spec0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
    ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def t_aw_assoc0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M')
    (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w)
      (h3 : t + u = tu) (h4 : s + tu = w) a b c,
      ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
    ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
      (ab : Cochain ((chains R).obj E) M nm) (bc : Cochain ((chains R).obj E) M' mk)
      (x y : Cochain ((chains R).obj E) L w),
      μ.IsAW h1 α β ab → ν.IsAW h2 ab γ x → μ'.IsAW h3 β γ bc → ν'.IsAW h4 α bc y → x = y

theorem etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc (hs : t_cup_spec0) (ha : t_aw_assoc0) : EtaleCochainCupAssociativeOfPairing := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨ab, hab⟩ := (hs R μ (E := E) h1).1 α β
  rw [(hs R μ (E := E) h1).2 α β ab hab]
  obtain ⟨x, hx⟩ := (hs R ν (E := E) h2).1 ab γ
  rw [(hs R ν (E := E) h2).2 ab γ x hx]
  obtain ⟨bc, hbc⟩ := (hs R μ' (E := E) h3).1 β γ
  rw [(hs R μ' (E := E) h3).2 β γ bc hbc]
  obtain ⟨y, hy⟩ := (hs R ν' (E := E) h4).1 α bc
  rw [(hs R ν' (E := E) h4).2 α bc y hy]
  congr 1
  exact Subtype.ext (ha R μ ν μ' ν' hass E h1 h2 h3 h4 α.1 β.1 γ.1 ab.1 bc.1 x.1 y.1 hab hx hbc hy)

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafRestrictScalarsInjectiveResolutionHomExists : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
    ∃ m : ∀ n : ℤ, (restr φ).obj ((res S F).X n) ⟶ (res R ((restr φ).obj F)).X n,
      (∀ i j : ℤ, (restr φ).map ((res S F).d i j) ≫ m j = m i ≫ (res R ((restr φ).obj F)).d i j) ∧
      (restr φ).map (resι S F) ≫ m 0 = resι R ((restr φ).obj F)

namespace LateralTheory.EtaleFoundations

theorem etaleSheaf_restrictScalars_resolution_comparison_of_hom (hH : EtaleSheafRestrictScalarsInjectiveResolutionHomExists) : EtaleRestrictScalarsResolutionCompatible := by
  intro R S _ _ φ F U a
  obtain ⟨m, hc, h0⟩ := hH R S φ F
  have hex : ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), ∀ (U : Scheme.{0}) (a : Sec F U),
      ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
    refine ⟨⟨fun U s => ((m s).hom.app (op U)).hom.toAddMonoidHom, ?_, ?_⟩, ?_⟩
    · intro V U g s x
      have h := (m s).hom.naturality g.op
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x).symm
    · intro U s t x
      have h := congrArg (fun f : (restr φ).obj ((res S F).X s) ⟶ (res R ((restr φ).obj F)).X t => (f.hom.app (op U)).hom x) (hc s t)
      exact h.symm
    · intro U x
      exact congrArg (fun f : (restr φ).obj F ⟶ (res R ((restr φ).obj F)).X 0 => (f.hom.app (op U)).hom x) h0
  exact pick_spec hex U a

end LateralTheory.EtaleFoundations
end
