module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle031
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExtFreeEtaleSheafYoneda
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle030
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
public import Development.EtaleCohomology.EtaleSheaves.Bundle067
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.FullyFaithfulLift

private theorem cancel_comp {J C D : Type} [Category J] [Category C] [Category D] (F : C ⥤ D)
    (hobj : Function.Injective F.obj) [F.Faithful] (c c' : J ⥤ C) (h : c ⋙ F = c' ⋙ F) : c = c' := by
  have hob : ∀ j, c.obj j = c'.obj j := fun j => hobj (congrArg (fun G => G.obj j) h)
  refine CategoryTheory.Functor.ext hob ?_
  intro X Y f
  apply F.map_injective
  have e := CategoryTheory.Functor.congr_hom h f
  simp only [CategoryTheory.Functor.comp_map] at e
  rw [e]
  simp [eqToHom_map]

private theorem lift_comp {J C D : Type} [Category J] [Category C] [Category D] (F : C ⥤ D)
    [F.Full] [F.Faithful] (c : J ⥤ D) (l : J → C) (hl : ∀ j, F.obj (l j) = c.obj j) :
    ∃ c' : J ⥤ C, c' ⋙ F = c := by
  refine ⟨{ obj := l
            map := fun {i j} f => F.preimage (eqToHom (hl i) ≫ c.map f ≫ eqToHom (hl j).symm)
            map_id := fun i => F.map_injective (by simp)
            map_comp := fun f g => F.map_injective (by simp) }, ?_⟩
  refine CategoryTheory.Functor.ext hl (fun i j f => ?_)
  simp

private theorem sp_map_eq {E : Spc} {a b : Act} (φ : Act.Hom a b) {k : ℕ} {T : Scheme.{0}} (x : Sx (Sp E a) k T) :
    Sx.map (Sp.map E φ) x = ((x.1, Sx.map (spcMap φ) x.2) : Sx (Sp E b) k T) := rfl

private theorem fn_obj_inj {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (A : CommRingCat.{0}) : Function.Injective (φ.fn A).obj := by
  intro x y h
  have e : φ.d.app A x.pt = φ.d.app A y.pt := congrArg Ob.pt h
  cases x
  cases y
  congr
  exact hi A e

private theorem fn_faithful {a b : Act} (φ : Act.Hom a b) (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g))
    (A : CommRingCat.{0}) : (φ.fn A).Faithful :=
  ⟨fun {_ _} _ _ h => Subtype.ext ((hb A).1 (congrArg Subtype.val h))⟩

private theorem fn_full {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) (A : CommRingCat.{0}) : (φ.fn A).Full := by
  constructor
  intro x y u
  obtain ⟨g, hg⟩ := (hb A).2 u.1
  refine ⟨⟨g, ?_⟩, ?_⟩
  · apply hi A
    have e := φ.eq A g y.pt
    have hg' : φ.g.app A g = u.1 := hg
    rw [hg'] at e
    exact u.2.trans e.symm
  · apply Subtype.ext
    exact hg

private theorem mono_sp (E : Spc) {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Mono (Sp.map E φ) := by
  apply UpperTheory.mono_of_injective_on_simplices
  intro k T x y h
  simp only [sp_map_eq] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  haveI := fn_faithful φ hb Γ(T, ⊤)
  have h2' : (show ComposableArrows (Ob a Γ(T, ⊤)) k from x.2) ⋙ φ.fn Γ(T, ⊤) =
      (show ComposableArrows (Ob a Γ(T, ⊤)) k from y.2) ⋙ φ.fn Γ(T, ⊤) := h2
  exact Prod.ext h1 (cancel_comp (φ.fn Γ(T, ⊤)) (fn_obj_inj φ hi _) _ _ h2')

private theorem lift_sp (E : Spc) {a₁ a : Act} (φ : Act.Hom a₁ a) (hi : ∀ A, Function.Injective (fun x : a₁.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a₁.G.obj A => φ.g.app A g)) {k : ℕ} {W : Scheme.{0}} (y : Sx (Sp E a) k W)
    (y₀ : a₁.D.obj Γ(W, ⊤))
    (h0 : φ.d.app _ y₀ = ((show ComposableArrows (Ob a Γ(W, ⊤)) k from y.2).obj 0).pt) :
    ∃ x : Sx (Sp E a₁) k W, Sx.map (Sp.map E φ) x = y := by
  classical
  set c : ComposableArrows (Ob a Γ(W, ⊤)) k := y.2 with hc
  have hl : ∀ j : Fin (k + 1), ∃ o : Ob a₁ Γ(W, ⊤), (φ.fn Γ(W, ⊤)).obj o = c.obj j := by
    intro j
    have hle : (0 : Fin (k + 1)) ≤ j := Fin.zero_le _
    obtain ⟨u, hu⟩ := c.map (homOfLE hle)
    obtain ⟨g, hg⟩ := (hb Γ(W, ⊤)).2 u⁻¹
    refine ⟨⟨a₁.smul _ g y₀⟩, ?_⟩
    have e := φ.eq Γ(W, ⊤) g y₀
    have hg' : φ.g.app Γ(W, ⊤) g = u⁻¹ := hg
    have h0' : φ.d.app Γ(W, ⊤) y₀ = (c.obj 0).pt := h0
    have key : (c.obj j).pt = φ.d.app Γ(W, ⊤) (a₁.smul _ g y₀) := by
      erw [e, hg', h0', hu, ← a.mul_smul, inv_mul_cancel, a.one_smul]
    exact congrArg Ob.mk key.symm
  choose l hl' using hl
  haveI := fn_full φ hi hb Γ(W, ⊤)
  haveI := fn_faithful φ hb Γ(W, ⊤)
  obtain ⟨c', hc'⟩ := lift_comp (φ.fn Γ(W, ⊤)) c l hl'
  refine ⟨((y.1, show Sx (spc a₁) k W from c') : Sx (Sp E a₁) k W), ?_⟩
  refine (sp_map_eq φ _).trans ?_
  exact Prod.ext rfl hc'

end UpperTheory.FullyFaithfulLift

theorem UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered :
    ∀ (R : Type) [CommRing R] (E : Spc) {a₁ a₂ a : Act} (φ₁ : Act.Hom a₁ a) (φ₂ : Act.Hom a₂ a),
        (∀ A, Function.Injective (fun x : a₁.D.obj A => φ₁.d.app A x)) → (∀ A, Function.Injective (fun x : a₂.D.obj A => φ₂.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a₁.G.obj A => φ₁.g.app A g)) → (∀ A, Function.Bijective (fun g : a₂.G.obj A => φ₂.g.app A g)) →
        (∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Loc T fun V g =>
          (∃ y, φ₁.d.app _ y = a.D.map g.appTop x) ∨ (∃ y, φ₂.d.app _ y = a.D.map g.appTop x)) →
        Cover2 R (Sp.map E φ₁) (Sp.map E φ₂) := by
  intro R _ E a₁ a₂ a φ₁ φ₂ i₁ i₂ b₁ b₂ hl
  refine UpperTheory.mayerVietorisCover_of_mono_of_zariskiLocal R _ _ (UpperTheory.FullyFaithfulLift.mono_sp E φ₁ i₁ b₁) (UpperTheory.FullyFaithfulLift.mono_sp E φ₂ i₂ b₂) (fun k T y => ?_)
  obtain ⟨S, hS, hP⟩ := hl T ((show ComposableArrows (Ob a Γ(T, ⊤)) k from y.2).obj 0).pt
  refine ⟨S, hS, fun W h hh => ?_⟩
  rcases hP W h hh with ⟨y₀, e⟩ | ⟨y₀, e⟩
  · exact Or.inl (UpperTheory.FullyFaithfulLift.lift_sp E φ₁ i₁ b₁ (y.res h) y₀ e)
  · exact Or.inr (UpperTheory.FullyFaithfulLift.lift_sp E φ₂ i₂ b₂ (y.res h) y₀ e)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

section Cone

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
  (comm : φ₁ ≫ b = a ≫ φ₂)

private theorem inl_map (n m : ℤ) (h : m + (-1) = n) :
    (mappingCone.inl φ₁).v m n h ≫ (mappingCone.map φ₁ φ₂ a b comm).f n =
      a.f m ≫ (mappingCone.inl φ₂).v m n h := by
  simp [mappingCone.map, Cochain.zero_cochain_comp_v]

private theorem inr_map (n : ℤ) :
    (mappingCone.inr φ₁).f n ≫ (mappingCone.map φ₁ φ₂ a b comm).f n =
      b.f n ≫ (mappingCone.inr φ₂).f n := by
  simp [mappingCone.map]

private theorem map_fst (n m : ℤ) (h : n + 1 = m) :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫ (mappingCone.fst φ₂).1.v n m h =
      (mappingCone.fst φ₁).1.v n m h ≫ a.f m := by
  rw [mappingCone.ext_from_iff φ₁ m n h]
  constructor
  · rw [reassoc_of% (inl_map φ₁ φ₂ a b comm n m (by omega))]
    simp
  · rw [reassoc_of% (inr_map φ₁ φ₂ a b comm n)]
    simp

private theorem map_snd (n : ℤ) :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫ (mappingCone.snd φ₂).v n n (add_zero n) =
      (mappingCone.snd φ₁).v n n (add_zero n) ≫ b.f n := by
  rw [mappingCone.ext_from_iff φ₁ (n + 1) n rfl]
  constructor
  · rw [reassoc_of% (inl_map φ₁ φ₂ a b comm n (n + 1) (by omega))]
    simp
  · rw [reassoc_of% (inr_map φ₁ φ₂ a b comm n)]
    simp

end Cone

variable {B : Scheme.{0}}

private def famCh (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) : B.Etale ⥤ Cx (ZMod q) := G ⋙ sch ⋙ chains (ZMod q)

private def termIso (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) (p : ℕ) :
    G ⋙ yoneda ⋙ free (ZMod q) ≅ famCh q G ⋙ HomologicalComplex.eval _ _ (-(p : ℤ)) :=
  NatIso.ofComponents (fun U => (chainsXIso (ZMod q) (sch.obj (G.obj U)) p).symm) (by
    intro U V a
    exact (GlobalTheory.EtC.HCTerms.chainsXIso_inv_map (ZMod q) (sch.map (G.map a)) p).symm)

private theorem famCh_good (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) (h : Good (G ⋙ yoneda ⋙ free (ZMod q))) (n : ℤ) :
    Good (famCh q G ⋙ HomologicalComplex.eval _ _ n) := by
  obtain ⟨hiso, hzero, -⟩ := UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct q B
  rcases lt_or_ge 0 n with hn | hn
  · exact hzero _ fun U => GlobalTheory.EtC.HCTerms.isZero_chains_X (ZMod q) _ n hn
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
    exact hiso _ _ ⟨termIso q G p⟩ h

private theorem cone_comm {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) {U V : B.Etale} (a : U ⟶ V) :
    (chains (ZMod q)).map (sch.map (F.app U)) ≫ (chains (ZMod q)).map (sch.map (G₂.map a)) =
      (chains (ZMod q)).map (sch.map (G₁.map a)) ≫ (chains (ZMod q)).map (sch.map (F.app V)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, F.naturality]

private def coneI₁ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    famCh q G₁ ⋙ HomologicalComplex.eval _ _ (n + 1) ⟶ coneF F q ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.inl ((chains (ZMod q)).map (sch.map (F.app U)))).v (n + 1) n (by omega)
  naturality U V a := (inl_map ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n (n + 1) (by omega)).symm

private def coneR₁ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    coneF F q ⋙ HomologicalComplex.eval _ _ n ⟶ famCh q G₁ ⋙ HomologicalComplex.eval _ _ (n + 1) where
  app U := (mappingCone.fst ((chains (ZMod q)).map (sch.map (F.app U)))).1.v n (n + 1) rfl
  naturality U V a := map_fst ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n (n + 1) rfl

private def coneI₂ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    famCh q G₂ ⋙ HomologicalComplex.eval _ _ n ⟶ coneF F q ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.inr ((chains (ZMod q)).map (sch.map (F.app U)))).f n
  naturality U V a := (inr_map ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n).symm

private def coneR₂ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    coneF F q ⋙ HomologicalComplex.eval _ _ n ⟶ famCh q G₂ ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.snd ((chains (ZMod q)).map (sch.map (F.app U)))).v n n (add_zero n)
  naturality U V a := map_snd ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n

theorem UpperTheory.homAcyclic_mappingCone_chains_of_homAcyclic_free :
    ∀ (q : ℕ) {B : Scheme.{0}} {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂), Good (G₁ ⋙ yoneda ⋙ free (ZMod q)) → Good (G₂ ⋙ yoneda ⋙ free (ZMod q)) → (∀ n : ℤ, Good (coneF F q ⋙ HomologicalComplex.eval _ _ n)) ∧ ∀ (U : B.Etale) (n : ℤ), 0 < n → IsZero (((coneF F q).obj U).X n) := by
  intro q B G₁ G₂ F h₁ h₂
  refine ⟨fun n => ?_, fun U n hn => ?_⟩
  · refine (UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct q B).2.2 _ _ _ (coneI₁ F q n) (coneR₁ F q n) (coneI₂ F q n) (coneR₂ F q n)
      ?_ ?_ ?_ ?_ ?_ (famCh_good q G₁ h₁ (n + 1)) (famCh_good q G₂ h₂ n)
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.inl_v_fst_v ((chains (ZMod q)).map (sch.map (F.app U))) (n + 1) n rfl
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.inr_f_snd_v ((chains (ZMod q)).map (sch.map (F.app U))) n
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact mappingCone.inl_v_snd_v ((chains (ZMod q)).map (sch.map (F.app U))) (n + 1) n (by omega)
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact mappingCone.inr_f_fst_v ((chains (ZMod q)).map (sch.map (F.app U))) n (n + 1) rfl
    · ext U : 2
      rw [NatTrans.app_add, NatTrans.comp_app, NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.id_X ((chains (ZMod q)).map (sch.map (F.app U))) n (n + 1) rfl
  · exact (mappingCone.isZero_X_iff ((chains (ZMod q)).map (sch.map (F.app U))) n).2
      ⟨GlobalTheory.EtC.HCTerms.isZero_chains_X _ _ _ (by omega), GlobalTheory.EtC.HCTerms.isZero_chains_X _ _ _ hn⟩

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

theorem UpperTheory.exists_cohomologyClass_to_derivedHom_bijective_of_kInjective :
    ∀ (q : ℕ) (B : Scheme.{0}) (I : Cx (ZMod q)), ∃ l : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ), CohomologyClass (C.obj U) I n → ((OU B q).obj U ⟶ (CategoryTheory.shiftFunctor _ n).obj (DerivedCategory.Q.obj (TC C I h))), (∀ C h, (TC C I h).IsKInjective → ∀ U n, Function.Bijective (l C h U n)) ∧ (∀ C h (U U' : B.Etale) (a : U' ⟶ U) n x, l C h U' n (cpre (Cocycle.ofHom (C.map a)) I n n (zero_add n) x) = (OU B q).map a ≫ l C h U n x) ∧ ∀ (C C' : B.Etale ⥤ Cx (ZMod q)) h h' (φ : C' ⟶ C) U n x, l C' h' U n (cpre (Cocycle.ofHom (φ.app U)) I n n (zero_add n) x) = l C h U n x ≫ (CategoryTheory.shiftFunctor _ n).map (DerivedCategory.Q.map (TM φ I h h')) := by
  intro q B I
  obtain ⟨y, hwd, hK, hU, hT⟩ := UpperTheory.ext_free_etale_sheaf_yoneda B q
  have cz : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z : Cocycle (C.obj U) I n), dS (TC C I h) n (n + 1) U (z : Cochain (C.obj U) I n) = 0 :=
    fun C h U n z => Cocycle.δ_eq_zero z (n + 1)
  have wd : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z z' : Cocycle (C.obj U) I n), CohomologyClass.mk z = CohomologyClass.mk z' →
      y (TC C I h) U n (z : Cochain (C.obj U) I n) (cz C h U n z) =
        y (TC C I h) U n (z' : Cochain (C.obj U) I n) (cz C h U n z') := by
    intro C h U n z z' hzz
    apply hwd
    have h0 : CohomologyClass.mk (z - z') = 0 := by
      rw [CohomologyClass.mk_sub, hzz, sub_self]
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h0
    obtain ⟨β, hβ⟩ := h0
    exact ⟨β, hβ⟩
  have lmk : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z : Cocycle (C.obj U) I n),
      y (TC C I h) U n ((CohomologyClass.mk_surjective (CohomologyClass.mk z)).choose : Cochain (C.obj U) I n)
        (cz C h U n _) = y (TC C I h) U n (z : Cochain (C.obj U) I n) (cz C h U n z) :=
    fun C h U n z => wd C h U n _ _ (CohomologyClass.mk_surjective _).choose_spec
  refine ⟨fun C h U n x => y (TC C I h) U n ((CohomologyClass.mk_surjective x).choose : Cochain (C.obj U) I n)
    (cz C h U n _), ?_, ?_, ?_⟩
  · intro C h hKI U n
    constructor
    · intro x x' hxx
      obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
      obtain ⟨z', rfl⟩ := CohomologyClass.mk_surjective x'
      dsimp only at hxx
      rw [lmk, lmk] at hxx
      obtain ⟨b, hb⟩ := (hK (TC C I h) hKI U n).1 _ _ _ _ hxx
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)]
      exact ⟨b, hb⟩
    · intro x
      obtain ⟨s, hs, hsx⟩ := (hK (TC C I h) hKI U n).2 x
      refine ⟨CohomologyClass.mk (Cocycle.mk s (n + 1) rfl hs), ?_⟩
      dsimp only
      rw [lmk]
      exact hsx
  · intro C h U U' a n x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    dsimp only
    rw [cpre_mk, lmk, lmk]
    exact hU (TC C I h) U U' a n (z : Cochain (C.obj U) I n) (cz C h U n z) _
  · intro C C' h h' φ U n x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    dsimp only
    rw [cpre_mk, lmk, lmk]
    exact hT (TC C I h) (TC C' I h') (TM φ I h h') U n (z : Cochain (C.obj U) I n) (cz C h U n z) _
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private theorem tw_q_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) : q • a = 0 := by
  have h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]

private theorem tw_nsmul_mod {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) (n : ℕ) :
    n • a = (n % q) • a := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_smul, mul_smul, tw_q_nsmul, add_zero]

private theorem mod_eq_of_nsmul_eq {q : ℕ} [NeZero q] {i : ℤ} {U : Scheme.{0}} [Nonempty U]
    (ζ : Prim q Γ(U, ⊤)) {c c' : ℕ} (h : c • twGen i ζ = c' • twGen i ζ) : c % q = c' % q := by
  have key : ∀ {c c' : ℕ}, c ≤ c' → c • twGen i ζ = c' • twGen i ζ → c % q = c' % q := by
    intro c c' hle h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [add_nsmul] at h
    have h0 : d • twGen i ζ = 0 := by
      have h' := h.symm
      rwa [add_eq_left] at h'
    obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ d h0
    rw [Nat.add_mul_mod_self_left]
  rcases le_total c c' with hle | hle
  · exact key hle h
  · exact (key hle h.symm).symm

private theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem exists_prim (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω)) :
    Nonempty (Prim q Ω) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (Polynomial.degree_cyclotomic_pos q Ω (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem UpperTheory.leafH0_holds :
    LateralTheory.E.E4.H0TwistOverClosedField := by
  intro hyp q _ Ω _ _ hq i
  obtain ⟨-, e, he, -⟩ := hyp.2.2.2.2.2.2.2.1 (ZMod q) (tw q i)
  obtain ⟨ζ0⟩ := exists_prim q Ω hq
  let ζ : Prim q Γ(Sp Ω, ⊤) :=
    Prim.map (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv) ζ0
  have hsec : ∀ {X : Scheme.{0}} [ConnectedSpace X] (ξ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X),
      ∃ c < q, y = c • twGen i ξ := by
    intro X _ ξ y
    obtain ⟨c, rfl⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q i X ξ y
    exact ⟨c % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q)), tw_nsmul_mod _ c⟩
  refine ⟨?_, ?_⟩
  · have hsurj : Function.Surjective (fun k : Fin q => e (Sp Ω) ((k : ℕ) • twGen i ζ)) := by
      intro x
      obtain ⟨c, hc, hy⟩ := hsec ζ ((e (Sp Ω)).symm x)
      refine ⟨⟨c, hc⟩, ?_⟩
      show e (Sp Ω) (c • twGen i ζ) = x
      rw [← hy, AddEquiv.apply_symm_apply]
    exact Finite.of_surjective _ hsurj
  · intro X _ c
    have hcomm : ∀ s, pl q i c 0 (e (Sp Ω) s) = e X (Sec.res c s) := fun s => he c s
    have hres : Function.Bijective (Sec.res (F := tw q i) c) := by
      have ht : Sec.res c (twGen i ζ) =
          twGen i (Prim.map (CommRingCat.Hom.hom (Scheme.Hom.appTop c)) ζ) :=
        (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 X (Sp Ω) c ζ
      constructor
      · intro s s' hss
        obtain ⟨c1, -, rfl⟩ := hsec ζ s
        obtain ⟨c2, -, rfl⟩ := hsec ζ s'
        rw [res_nsmul, res_nsmul, ht] at hss
        have hm := mod_eq_of_nsmul_eq _ hss
        rw [tw_nsmul_mod _ c1, tw_nsmul_mod _ c2, hm]
      · intro y
        obtain ⟨c1, -, rfl⟩ := hsec (Prim.map (CommRingCat.Hom.hom (Scheme.Hom.appTop c)) ζ) y
        exact ⟨c1 • twGen i ζ, by rw [res_nsmul, ht]⟩
    have hfun : (pl q i c 0 : _ → _) = (e X) ∘ Sec.res c ∘ (e (Sp Ω)).symm := by
      funext x
      simp only [Function.comp]
      rw [← hcomm, AddEquiv.apply_symm_apply]
    rw [hfun]
    exact (e X).bijective.comp (hres.comp (e (Sp Ω)).symm.bijective)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem UpperTheory.integralClosure_finite_of_finiteType_domain :
    LateralTheory.E.LeafIntClosureAlgPf.LeafIntClFinite := by
  intro Ω L _ _ _ u _ hfd
  have : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    .adjoin_of_finite (Set.finite_singleton u)
  refine GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_of_forall_mvPolynomial
    Ω (Algebra.adjoin Ω {u}) (IntermediateField.adjoin Ω {u}) L ?_
  intro s L' _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists Ω
  rcases CharP.char_is_prime_or_zero Ω p with hpr | rfl
  · haveI : Fact p.Prime := ⟨hpr⟩
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charP Ω p s L'
  · haveI : CharZero Ω := CharP.charP_to_charZero Ω
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charZero Ω s L'
end
