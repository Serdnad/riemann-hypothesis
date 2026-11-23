module

public import Development.EtaleCohomology.EtaleSheaves.Bundle077
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle036
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle008
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle019
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.LocalTwistForms

set_option backward.isDefEq.respectTransparency false in
private theorem covPt {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (x : X) :
    ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V), S f ∧ f y = x := by
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact ⟨𝒰.X i, 𝒰.f i, inferInstance, y, hle _ _ ⟨i⟩, rfl⟩

private theorem res_res {R : Type} [CommRing R] {F : Shv R} {V' V U : Scheme.{0}} (g : V' ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res h x) = Sec.res (g ≫ h) x := by
  simp [Sec.res, op_comp, Functor.map_comp]

private theorem res_smul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_smul _ _ _

private theorem sec_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (x : (twF q i).obj Γ(U, ⊤)) :
    (Sec.res g (ofRings.sec (twF q i) U x) : Sec (tw q i) V) = ofRings.sec (twF q i) V ((twF q i).map g.appTop x) :=
  (NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) g.op x).symm

private theorem map_single (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (φ : A ⟶ B) (ζ : Prim q A) (b : ULift.{1} (ZMod q)) :
    (twF q i).map φ (Submodule.Quotient.mk (Finsupp.single ζ b) : (twF q i).obj A) =
      (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) b) : (twF q i).obj B) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ _) = _
  rw [Finsupp.mapDomain_single]

private theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (Prim.map g.appTop.hom ζ) := by
  exact (sec_res q i g _).trans (congrArg _ (map_single q i g.appTop ζ 1))

private theorem unit_res {X : Scheme.{0}} {A B C : X.Opens} (h₁ : B ≤ A) (h₂ : C ≤ A) (h₃ : C ≤ B) (f : Γ(X, A))
    (hu : IsUnit (X.presheaf.map (homOfLE h₁).op f)) : IsUnit (X.presheaf.map (homOfLE h₂).op f) := by
  have e : X.presheaf.map (homOfLE h₂).op = X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₃).op := by
    rw [← Functor.map_comp]; rfl
  rw [e, CommRingCat.comp_apply]
  exact hu.map _

private theorem sheafDetect (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) [Nonempty X] (ζ : Prim q Γ(X, ⊤))
    (c : ULift.{1} (ZMod q)) (h : c • twGen i ζ = 0) : c = 0 := by
  let e : (twF q i).obj Γ(X, ⊤) := c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(X, ⊤))
  have h0 : ofRings.sec (twF q i) X e = ofRings.sec (twF q i) X 0 := by
    refine Eq.trans ?_ (h.trans (map_zero _).symm)
    exact map_smul _ _ _
  have hmem := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (X := op X) e 0 h0
  obtain ⟨V, f, -, y, hf, -⟩ := covPt _ hmem (Classical.arbitrary X)
  have hf' : (twF q i).map f.appTop e = 0 := Eq.trans hf (map_zero ((twF q i).map f.appTop).hom)
  have e1 : (twF q i).map f.appTop e =
      c • (twF q i).map f.appTop (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(X, ⊤)) :=
    map_smul ((twF q i).map f.appTop).hom c _
  have : Nontrivial Γ(V, ⊤) := (V.presheaf.germ ⊤ y trivial).hom.domain_nontrivial
  rw [e1, map_single] at hf'
  exact UpperTheory.twist_generator_smul_eq_zero_imp q i Γ(V, ⊤) _ c hf'

private theorem twLocal (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ : Prim q A) (t : (twF q i).obj A)
    (p : Ideal A) [p.IsPrime] :
    ∃ f : A, f ∉ p ∧ ∀ (B : CommRingCat.{0}) (φ : A ⟶ B), IsUnit (φ f) → ∃ c : ULift.{1} (ZMod q),
      (twF q i).map φ t = c • (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) 1) : (twF q i).obj B) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  induction x using Finsupp.induction_linear with
  | zero =>
    refine ⟨1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), fun B φ _ => ⟨0, ?_⟩⟩
    rw [zero_smul]
    exact map_zero ((twF q i).map φ).hom
  | add x y hx hy =>
    obtain ⟨f, hf, H⟩ := hx
    obtain ⟨g, hg, H'⟩ := hy
    refine ⟨f * g, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hf hg, fun B φ hu => ?_⟩
    rw [map_mul] at hu
    obtain ⟨c, hc⟩ := H B φ (isUnit_of_mul_isUnit_left hu)
    obtain ⟨d, hd⟩ := H' B φ (isUnit_of_mul_isUnit_right hu)
    refine ⟨c + d, ?_⟩
    rw [add_smul, ← hc, ← hd]
    exact map_add ((twF q i).map φ).hom (Submodule.Quotient.mk x : (twF q i).obj A) (Submodule.Quotient.mk y : (twF q i).obj A)
  | single ξ b =>
    obtain ⟨f, a, hf, H⟩ := UpperTheory.primitive_root_eq_pow_locally q A ξ ζ p
    refine ⟨f, hf, fun B φ hu => ⟨b * ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q), ?_⟩⟩
    rw [map_single]
    have hmem : Finsupp.single (Prim.map φ.hom ξ) 1 - Finsupp.single (Prim.map φ.hom ζ) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))
        ∈ twRel q i B :=
      Submodule.subset_span ⟨Prim.map φ.hom ζ, Prim.map φ.hom ξ, a, H B φ.hom hu, rfl⟩
    have e1 : (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ξ) 1) : (twF q i).obj B) =
        Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
      (Submodule.Quotient.eq _).2 hmem
    have e2 : ∀ (η : Prim q B) (r : ULift.{1} (ZMod q)), (Submodule.Quotient.mk (Finsupp.single η r) : (twF q i).obj B) =
        r • (Submodule.Quotient.mk (Finsupp.single η 1) : (twF q i).obj B) := by
      intro η r
      refine Eq.trans ?_ (Submodule.Quotient.mk_smul _ _ _)
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e2 _ b, e1, e2 _ (ULift.up _), smul_smul]

private theorem formP (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) (hX : IsUnit ((q : ℕ) : Γ(X, ⊤)))
    (s : Sec (tw q i) X) (x : X) :
    ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V) (ζ : Prim q Γ(V, ⊤)) (c : ULift.{1} (ZMod q)),
      f y = x ∧ Sec.res f s = c • twGen i ζ := by
  obtain ⟨V₁, f₁, h₁, y₁, ζ₁, rfl⟩ := UpperTheory.exists_etale_nbhd_primitiveRoot_of_isUnit_natCast q X hX x
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (U := op V₁) (Sec.res f₁ s)
  obtain ⟨V₂, f₂, h₂, y₂, ⟨t, ht⟩, rfl⟩ := covPt _ hmem y₁
  let ρ : Γ(V₂, ⊤) ⟶ V₂.residueField y₂ := V₂.presheaf.germ ⊤ y₂ trivial ≫ V₂.residue y₂
  have hp : (RingHom.ker ρ.hom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hfp, H⟩ := twLocal q i Γ(V₂, ⊤) (Prim.map f₂.appTop.hom ζ₁) t (RingHom.ker ρ.hom)
  have hy : y₂ ∈ V₂.basicOpen f := by
    rw [Scheme.mem_basicOpen_top]
    have h1 : (V₂.residue y₂).hom ((V₂.presheaf.germ ⊤ y₂ trivial).hom f) ≠ 0 := fun h => hfp (RingHom.mem_ker.2 h)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1
  have hu : IsUnit ((V₂.basicOpen f).ι.appTop f) := by
    have h0 := V₂.toRingedSpace.isUnit_res_basicOpen f
    rw [Scheme.Opens.ι_appTop]
    exact unit_res _ _ (le_of_eq (by simp; rfl)) f h0
  obtain ⟨c, hc⟩ := H _ (V₂.basicOpen f).ι.appTop hu
  refine ⟨V₂.basicOpen f, (V₂.basicOpen f).ι ≫ f₂ ≫ f₁, inferInstance, ⟨y₂, hy⟩,
    Prim.map (V₂.basicOpen f).ι.appTop.hom (Prim.map f₂.appTop.hom ζ₁), c, by simp; rfl, ?_⟩
  rw [← res_res, ← res_res]
  have ht' : Sec.res f₂ (Sec.res f₁ s) = ofRings.sec (twF q i) V₂ t := ht.symm
  refine (congrArg (Sec.res (V₂.basicOpen f).ι) ht').trans ((sec_res q i _ t).trans
    ((congrArg (ofRings.sec (twF q i) _) hc).trans ?_))
  exact map_smul _ _ _

end UpperTheory.Cb.LocalTwistForms

open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafInj0WPf LateralTheory.E.LeafDegCut UpperTheory.Cb.LocalTwistForms in
theorem UpperTheory.Cb.twistedSections_of_negativeDegreeVanishing :
    LateralTheory.E.LeafDegCut.LeafNeg → LateralTheory.E.LeafInj0WPf.LeafSecTw := by
  intro _ q _ k _ hq i B W s₀ ι _ U s hs x hx
  have hX : IsUnit ((q : ℕ) : Γ(U.left, ⊤)) := by
    have h := hq.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.hom ≫ s₀).appTop).hom
    simpa using h
  obtain ⟨V, f, hf, y, ζ, c, hy, hsV⟩ := formP q i U.left hX s x
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (f ≫ U.hom) (inferInstanceAs (Etale (f ≫ U.hom)))
  let a : U' ⟶ U := MorphismProperty.Over.homMk f rfl
  refine ⟨U', a, y, hy, ?_⟩
  obtain ⟨w, hw⟩ := hx
  have hne : Nonempty ↥(pullback U'.hom ι) := by
    have e : U'.hom y = ι w := by
      rw [hw, ← hy]
      rfl
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y w e
    exact ⟨z⟩
  have hc : c = 0 := by
    have e : prB ι U' ≫ f = resBW ι a ≫ prB ι U := (pullback.lift_fst _ _ _).symm
    have h1 : Sec.res (prB ι U') (Sec.res f s) = 0 := by
      have h0 := congrArg (Sec.res (resBW ι a)) hs
      rw [res_res, ← e] at h0
      exact (res_res _ _ _).trans (h0.trans (map_zero _))
    have key : ∀ pr : pullback U'.hom ι ⟶ V, Sec.res pr (Sec.res f s) = 0 → c = 0 := fun pr h => by
      rw [hsV, res_smul, twGen_res] at h
      exact sheafDetect q i _ _ c h
    exact key (prB ι U') h1
  change Sec.res f s = 0
  rw [hsV, hc, zero_smul]
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf LateralTheory.E.LeafInclDescendPf
  LateralTheory.E.LeafInclPiecePf

namespace UpperTheory.Cb.PiLocalization₂

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)

private abbrev Lev : Type := {S : Subalgebra k Ω // R ≤ S ∧ S.FG}

private theorem lev_directed : IsDirected (Lev R) (· ≤ ·) :=
  ⟨fun a b ↦ ⟨⟨a.1 ⊔ b.1, a.2.1.trans le_sup_left, a.2.2.sup b.2.2⟩,
    (le_sup_left : a.1 ≤ a.1 ⊔ b.1), (le_sup_right : b.1 ≤ a.1 ⊔ b.1)⟩⟩

private def rings : Lev R ⥤ CommRingCat.{0} where
  obj s := .of s.1
  map {s t} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h : s.1 ≤ t.1)).toRingHom

private def ringsCocone : Cocone (rings R) where
  pt := .of Ω
  ι := { app s := CommRingCat.ofHom (algebraMap s.1 Ω) }

private def ringsIsColimit (hR : R.FG) : IsColimit (ringsCocone R) := by
  classical
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  refine isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun s a b hab ↦ ?_))
  · let x' : Ω := x
    have hx : (Algebra.adjoin k {x'}).FG := ⟨{x'}, by simp⟩
    refine ⟨⟨R ⊔ Algebra.adjoin k {x'}, le_sup_left, hR.sup hx⟩,
      (⟨x', (le_sup_right : Algebra.adjoin k {x'} ≤ R ⊔ Algebra.adjoin k {x'})
        (Algebra.subset_adjoin rfl)⟩ : (R ⊔ Algebra.adjoin k {x'} : Subalgebra k Ω)), rfl⟩
  · exact ⟨s, 𝟙 s, congrArg _ (Subtype.ext hab)⟩

variable {R} in
private theorem lvl_fst {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) : lvl h1 h h' q ≫ pullback.fst q (incl h1) = pullback.fst q (incl h) :=
  pullback.lift_fst _ _ _

variable {R} in
private theorem lvl_snd {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) :
    lvl h1 h h' q ≫ pullback.snd q (incl h1) = pullback.snd q (incl h) ≫ incl h' :=
  pullback.lift_snd _ _ _

variable {R} in
private theorem lvl_isPullback {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) :
    IsPullback (lvl h1 h h' q) (pullback.snd q (incl h)) (pullback.snd q (incl h1)) (incl h') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h1)) (v₁₃ := q) (h₂₂ := incl h1) ?_
    (lvl_snd h1 h h' q) (IsPullback.of_hasPullback q (incl h1))
  rw [lvl_fst, incl_comp h1 h h']
  exact IsPullback.of_hasPullback q (incl h)

variable {D : Scheme.{0}} (q : D ⟶ Sp R)

private def stages : (Lev R)ᵒᵖ ⥤ Scheme.{0} where
  obj s := pullback q (incl s.unop.2.1)
  map {s t} h := lvl t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q
  map_id s := by
    apply pullback.hom_ext
    · rw [lvl_fst, Category.id_comp]
    · rw [lvl_snd, Category.id_comp]
      exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
  map_comp {s t u} f g := by
    apply pullback.hom_ext
    · rw [lvl_fst, Category.assoc, lvl_fst, lvl_fst]
    · rw [lvl_snd, Category.assoc, lvl_snd, ← Category.assoc, lvl_snd, Category.assoc,
        incl_comp (leOfHom g.unop : u.unop.1 ≤ t.unop.1) (leOfHom (f ≫ g).unop : u.unop.1 ≤ s.unop.1)
          (leOfHom f.unop : t.unop.1 ≤ s.unop.1)]

private def toBase : stages R q ⟶ (rings R).op ⋙ Scheme.Spec where
  app s := pullback.snd q (incl s.unop.2.1)
  naturality s t h := lvl_snd t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q


variable {R q} in
private def stagesCone {Y : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D} (w : v ≫ q = g ≫ toR R) :
    Cone (stages R q) where
  pt := Y
  π :=
    { app s := bcLift s.unop.2.1 w
      naturality s t h := (Category.id_comp _).trans
        (bcLift_lvl t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) w).symm }


variable {R q} in
private def stagesIsLimit (hR : R.FG) {Y : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D}
    (hp : IsPullback v g q (toR R)) : IsLimit (stagesCone hp.w) := by
  classical
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  have : IsFiltered (Lev R) := isFiltered_of_directed_le_nonempty _
  have : IsConnected (Lev R)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfIsPullbackOfIsConnected (toBase R q) (stagesCone hp.w)
    (Scheme.Spec.mapCone (ringsCocone R).op)
    { hom := g
      w s := (pullback.lift_snd _ _ _).symm }
    (fun s ↦ bcLift_isPullback s.unop.2.1 hp)
    (isLimitOfPreserves Scheme.Spec (ringsIsColimit R hR).op)

private def stagesToConstantSpec : stages R q ⟶ (Functor.const _).obj (Sp R) where
  app s := pullback.fst q (incl s.unop.2.1) ≫ q
  naturality s t h := by
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact (lvl_fst t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q) =≫ q |>.trans rfl |> fun e ↦ by
      simpa [stages] using e


variable {R q} in
private theorem factor (hR : R.FG) (hq : FP q) {Y Z : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D}
    (hp : IsPullback v g q (toR R)) (qZ : Z ⟶ Sp R) (hZ : LocallyOfFinitePresentation qZ)
    (a : Y ⟶ Z) (ha : a ≫ qZ = v ≫ q) :
    ∃ (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG ∧ ∃ u : pullback q (incl h1) ⟶ Z,
      bcLift h1 hp.w ≫ u = a ∧ u ≫ qZ = pullback.fst q (incl h1) ≫ q := by
  classical
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  have : IsFiltered (Lev R) := isFiltered_of_directed_le_nonempty _
  have i1 : ∀ {s t : (Lev R)ᵒᵖ} (h : s ⟶ t), IsAffineHom ((stages R q).map h) := fun {s t} h ↦
    MorphismProperty.of_isPullback
      (lvl_isPullback t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q).flip inferInstance
  have i2 : ∀ s : (Lev R)ᵒᵖ, CompactSpace ((stages R q).obj s) := fun s ↦ by
    have h : QuasiCompact (pullback.snd q (incl s.unop.2.1)) := (fp_snd q (incl s.unop.2.1) hq).2.1
    change CompactSpace ↥(pullback q (incl s.unop.2.1))
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd q (incl s.unop.2.1))
  have i3 : ∀ s : (Lev R)ᵒᵖ, QuasiSeparatedSpace ((stages R q).obj s) := fun s ↦
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd q (incl s.unop.2.1))).mp
      (fp_snd q (incl s.unop.2.1) hq).2.2
  obtain ⟨s, u, h₁, h₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (stages R q) (stagesToConstantSpec R q) qZ (stagesCone hp.w) (stagesIsLimit hR hp) a (by
      refine NatTrans.ext (funext fun s ↦ ?_)
      change bcLift s.unop.2.1 hp.w ≫ pullback.fst q (incl s.unop.2.1) ≫ q = a ≫ qZ
      rw [ha]
      exact pullback.lift_fst_assoc _ _ _ _)
  exact ⟨s.unop.1, s.unop.2.1, s.unop.2.2, u, h₁, h₂⟩

end UpperTheory.Cb.PiLocalization₂

theorem UpperTheory.Cb.pullback_isLimit_over_fg_subalgebras :
    LateralTheory.E.LeafInclPiecePf.LeafInclMap := by
  intro k _ Ω _ _ X f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R1, h1, hR1, u, hu, hu'⟩ := UpperTheory.Cb.PiLocalization₂.factor hR hqW hW qU hqU.1 (X.homOfLE hWU ≫ vU) (by
    rw [Category.assoc, hU.w, hW.w]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc])
  refine ⟨R1, h1, hR1, pullback.lift u (pullback.snd qW (incl h1)) ?_, pullback.lift_snd _ _ _, ?_⟩
  · rw [hu', pullback.condition]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hu, Category.assoc]
      unfold bcLift
      rw [pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc]
      unfold bcLift
      rw [pullback.lift_snd, pullback.lift_snd]
      simp only [Category.assoc, Scheme.homOfLE_ι_assoc]

end
end
