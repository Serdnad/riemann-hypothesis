module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle196
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle195
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle197
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CoverLie

section Move

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem tan_up {G : Over S} [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (x' : Sp R' ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  let u : Over.mk x' ⟶ Over.mk x := Over.homMk (Spec.map (CommRingCat.ofHom φ)) h
  have e : (LieEx.zsec x' : _ ⟶ LieEx.ob x' R') ≫ LieCarrier.epsHom φ x x' h = u ≫ LieEx.zsec x := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  refine (LieEx.isTanAt_iff x' G _).2 ?_
  rw [← Category.assoc, e, Category.assoc, (LieEx.isTanAt_iff x G _).1 hv, MonObj.comp_one]

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X}
  {i : Ω →+* Ω'} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']

theorem exists_hom (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hG : IsGrpPullback G' G f φ) (M : LieModel G ξ V)
    (M' : LieModel G' ξ' V') :
    ∃ j : V →+ V', ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := by
  have hx : Spec.map (CommRingCat.ofHom i) ≫ ξ = ξ' ≫ f := hd.symm
  let P := LieMove.pushModel hG M'
  have ex : ∀ e, ∃ e', P.pt e' = LieCarrier.epsHom i ξ (ξ' ≫ f) hx ≫ M.pt e :=
    fun e => P.onto _ (tan_up i ξ (ξ' ≫ f) hx _ (M.tan e))
  choose j hj using ex
  refine ⟨AddMonoidHom.mk' j fun a b => P.inj ?_, fun e => congrArg (fun z => z.left) (hj e)⟩
  rw [P.add, hj, hj, hj, M.add, MonObj.comp_mul]

theorem map_diff {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {a : G ⟶ G} {a' : G' ⟶ G'}
    (hG : IsGrpPullback G' G f φ) (hφ : a'.left ≫ φ = φ ≫ a.left) {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    {T : V →ₗ[Ω] V} {T' : V' →ₗ[Ω'] V'} (hT : M.IsDiffOf a T) (hT' : M'.IsDiffOf a' T') (e : V) :
    j (T e) = T' (j e) := by
  refine M'.inj (Over.OverMorphism.ext (hG.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [hj, hT e, hT' (j e), Over.comp_left, Over.comp_left, Category.assoc, hφ, ← Category.assoc, ← Category.assoc, hj]

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {f' : S'' ⟶ S} (hf : f' = g ≫ f) (m : SABMap t' t f) (n : SABMap t'' t f') :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst hf
  exact sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → ∃ jA : A.Li →+ B.Li, IsExtOver i jA ∧ (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) ∧ (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) ∧ B.M.lat = A.M.lat.pull B.ξ h jA := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A B i h hd hf
  obtain ⟨m, hm⟩ := cancel hf A.m B.m
  obtain ⟨j, hj⟩ := exists_hom hd m.cart A.M B.M
  obtain ⟨hx, -, hl⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X B.X Ω₁ Ω A.ξ B.ξ h i A.t.G B.t.G m.φ A.Li B.Li A.M B.M j A.tie.gen B.tie.gen
    hd m.cart A.t.semi.smooth hj
  refine ⟨j, hx, fun e => ?_, fun a e => ?_, hl⟩
  · rw [hm, ← Category.assoc, hj, Category.assoc]
  · exact map_diff m.cart (m.act a) hj (A.act a) (B.act a) e

end GlobalTheory.CompanionTheory.Ar.CoverLie
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

section Rings

variable {S : Scheme.{0}} {A B D : Type} [CommRing A] [CommRing B] [CommRing D]

theorem dualMap_comp (f : A →+* B) (g : B →+* D) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem spec_dualMap_comp (f : A →+* B) (g : B →+* D) :
    Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) =
      Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) := by
  rw [dualMap_comp]
  exact Spec.map_comp (CommRingCat.ofHom (dualMap f)) (CommRingCat.ofHom (dualMap g))

theorem isTanAt_epsHom {G : Over S} [GrpObj G] (φ : A →+* B) (x : Spec (CommRingCat.of A) ⟶ S)
    (x' : Spec (CommRingCat.of B) ⟶ S) (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  rw [LieEx.isTanAt_iff] at hv ⊢
  have key : (LieEx.zsec x' : _ ⟶ LieEx.ob x' B) ≫ LieCarrier.epsHom φ x x' h =
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) h : Over.mk x' ⟶ Over.mk x) ≫ LieEx.zsec x := by
    ext1
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap, TrivSqZeroExt.fst_add]
  rw [← Category.assoc, key, Category.assoc, hv, MonObj.comp_one]

theorem stalk_hom_ext {X : Scheme.{0}} (c : X) (a b : X.presheaf.stalk c →+* B)
    (h : Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk c = Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecStalk c) :
    a = b := by
  have h1 := (cancel_mono (X.fromSpecStalk c)).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

end Rings

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] [IsLocalRing R] {C : Type} [Field C] [Algebra R C]

theorem centre_specializes (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) ⤳ centre z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap R C))) (IsLocalRing.closedPoint C) ⤳
      IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
  exact h.map z.continuous

theorem valAt_base (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) {e : E} (hc : genPt ξ ⤳ centre z)
    (hc' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z))
    (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G)
    (hv : M.Extends ⟨centre z, hc⟩ e v) (t : epsAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) ⟶ G)
    (u : epsAt z ⟶ G) (ht : t.left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ u.left)
    (hu : u.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left) :
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e t := by

  have hsp := centre_specializes (C := C) z
  have F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have gen_eq : (genMap ξ ⟨_, hc'⟩).comp (X.presheaf.stalkSpecializes hsp).hom = genMap ξ ⟨_, hc⟩ := by
    apply stalk_hom_ext
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, F1]
    exact (LieCarrier.genMap_fromSpecStalk ⟨_, hc'⟩).trans (LieCarrier.genMap_fromSpecStalk ⟨_, hc⟩).symm
  have s_eq : (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom.comp
      (X.presheaf.stalkSpecializes hsp).hom = (algebraMap R C).comp (Scheme.stalkClosedPointTo z).hom := by
    apply stalk_hom_ext
    have L : Spec.map (X.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo
        (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) ≫ X.fromSpecStalk (centre z) =
        Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z :=
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (Spec.map (Scheme.stalkClosedPointTo _) ≫ ·)
          (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)).trans
            (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)))
    have Rt : Spec.map (Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (algebraMap R C)) ≫
        X.fromSpecStalk (centre z) = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z :=
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        (congrArg (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ·)
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)))
    exact L.trans Rt.symm
  refine ⟨hc', LieCarrier.epsHom (X.presheaf.stalkSpecializes hsp).hom _ _ F1 ≫ v,
    ⟨isTanAt_epsHom _ _ _ _ _ hv.1, ?_⟩, ?_⟩
  · change (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ ⟨_, hc'⟩))) ≫
      Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hsp).hom)) ≫ v.left
    have e := spec_dualMap_comp (X.presheaf.stalkSpecializes hsp).hom (genMap ξ ⟨_, hc'⟩)
    rw [gen_eq] at e
    exact hv.2.trans ((congrArg (· ≫ v.left) e).trans (Category.assoc _ _ _))
  · change t.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo _).hom)) ≫
      Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hsp).hom)) ≫ v.left
    have e1 := spec_dualMap_comp (Scheme.stalkClosedPointTo z).hom (algebraMap R C)
    have e2 := spec_dualMap_comp (X.presheaf.stalkSpecializes hsp).hom
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom
    have e3 := (congrArg (fun f : X.presheaf.stalk (centre z) →+* C => Spec.map (CommRingCat.ofHom (dualMap f)))
      s_eq).symm.trans e2
    exact ht.trans ((congrArg (_ ≫ ·) hu).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ v.left) (e1.symm.trans e3)).trans (Category.assoc _ _ _))))

end GlobalTheory.CompanionTheory.Ar.LieFib

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_fibAt_iff : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (C : Type) [Field C] [Algebra R C] (EC : Type) [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC] (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC), IsCptGen ξ → Smooth G.hom → genPt ξ ⤳ centre z → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) → ∀ w : EC, w ∈ M.fibAt M.lat z MC ↔ ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ v.left := by
  intro X G _ _ Ω _ ξ E _ _ M R _ _ z C _ _ EC _ _ _ _ MC hξ hG h h' w
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G R z
  obtain ⟨ev, hev, -, hspan⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ E M R z h ER MR hξ hG
  obtain ⟨evC, hevC, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ E M C _ h' EC MC hξ hG
  have hj : ∀ u : ER, ∃ w, MC.pt w = LieCarrier.epsHom (algebraMap R C) z _ rfl ≫ MR.pt u := fun u =>
    MC.onto _ (LieFib.isTanAt_epsHom _ _ _ _ _ (MR.tan u))
  choose j hj using hj
  have hjl : ∀ u, (MC.pt (j u)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ (MR.pt u).left := fun u =>
    congrArg CommaMorphism.left (hj u)
  have hadd : ∀ u u', j (u + u') = j u + j u' := fun u u' => MC.inj (by
    rw [hj, MC.add, hj, hj, MR.add, MonObj.comp_mul])
  have hsmul : ∀ (r : R) u, j (r • u) = r • j u := fun r u => MC.inj (Over.OverMorphism.ext (by
    rw [← algebraMap_smul C r (j u), MC.smul, hjl, hjl, MR.smul]
    have e : Spec.map (CommRingCat.ofHom (epsMul (algebraMap R C r))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) =
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ Spec.map (CommRingCat.ofHom (epsMul r)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        LieCarrier.dualMap_epsMul]
    rw [← Category.assoc, ← e, Category.assoc]))
  let jL : ER →ₗ[R] EC := { toFun := j, map_add' := hadd, map_smul' := hsmul }
  have hgen : ∀ (e : E) (he : e ∈ M.lat ⟨centre z, h⟩),
      M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt (j (ev ⟨e, he⟩))) := by
    intro e he
    obtain ⟨h2, v, hv, hu⟩ := (hev e _).2 ⟨he, rfl⟩
    exact LieFib.valAt_base M z h h' v hv _ _ (hjl _) hu
  constructor
  · intro hw
    have hle : M.fibAt M.lat z MC ≤ LinearMap.range jL := by
      refine Submodule.span_le.2 ?_
      rintro w' ⟨h2, e, he, hval⟩
      obtain ⟨he', hw'⟩ := (hevC e _).1 hval
      obtain ⟨he'', hw''⟩ := (hevC e _).1 (hgen e he)
      exact ⟨ev ⟨e, he⟩, hw''.symm.trans hw'⟩
    obtain ⟨u, rfl⟩ := hle hw
    exact ⟨MR.pt u, MR.tan u, hjl u⟩
  · rintro ⟨v, hv, hw⟩
    obtain ⟨u, rfl⟩ := MR.onto v hv
    have hwu : w = j u := MC.inj (Over.OverMorphism.ext (hw.trans (hjl u).symm))
    subst hwu
    have hu : u ∈ Submodule.span R (Set.range ev) := hspan ▸ Submodule.mem_top
    have hle : (Submodule.span R (Set.range ev)).map jL ≤ M.fibAt M.lat z MC := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨h, e, he, hgen e he⟩
    exact hle (Submodule.mem_map_of_mem hu)

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

theorem exists_isTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → ∃ (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 hgen
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq Y.X _ _ 𝔐.ξ₀ (Z.ξ₀ ≫ Y.j) 𝔐.gen₀ Z.gen hgen
  have hdom' : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom (𝔐.fn.comp ψ.toRingHom)) ≫ (Z.ξ₀ ≫ Y.j) := by
    have h1 : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom 𝔐.fn) ≫ 𝔐.ξ₀ := 𝔐.fn_over
    have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (Z.ξ₀ ≫ Y.j) = 𝔐.ξ₀ := hψ
    rw [h1, ← h2, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f (𝔐.fn.comp ψ.toRingHom) := hdom'
  have key : ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F)) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    have e1 := 𝔐.cst_over
    have e2 := Z.over_inc
    have e3 := Y.jQ_over
    rw [← e1, ← Category.assoc, hdom', ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, e3, ← Category.assoc Z.ξ₀, e2]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hcst : (𝔐.fn.comp ψ.toRingHom).comp Z.inc = 𝔐.cst := by
    have k0 : Spec.map (CommRingCat.ofHom (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F))) = Spec.map (CommRingCat.ofHom (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) := key
    have k1 := congrArg CommRingCat.Hom.hom (Spec.map_injective k0)
    simp only [CommRingCat.hom_ofHom] at k1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) k1
  letI := CategoryTheory.Over.cartesianMonoidalCategory 𝔐.X
  letI := CategoryTheory.Over.cartesianMonoidalCategory Y.X
  letI : CategoryTheory.GrpObj 𝔐.t.G := 𝔐.t.grp
  letI : CategoryTheory.GrpObj Y.t.G := Y.t.grp
  letI : Group (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) := CategoryTheory.Hom.group
  letI : Group (Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  letI : Group (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  letI : Group (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  have hpb : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback 𝔐.t.G Y.t.G 𝔐.f 𝔐.m.φ := 𝔐.m.cart
  have hone : (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ = (1 : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G).left := by
    obtain ⟨o, ho⟩ : ∃ o : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, o.left = (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ :=
      ⟨Over.homMk ((1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ) (by
        rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w]; rfl), rfl⟩
    have hoo : o * o = o := by
      apply Over.OverMorphism.ext
      rw [hpb.2 (Over.mk 𝔐.ξ) 1 1 o o ho ho, mul_one, ho]
    have ho1 : o = 1 := by simpa using hoo
    rw [← ho, ho1]
  have hT : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) = Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) := by
    simp [GlobalTheory.CompanionTheory.Ar.epsAt]
  have hx0 : ∀ e : 𝔐.Li, ((𝔐.M.pt e).left ≫ 𝔐.m.φ) ≫ Y.t.G.hom = (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f)).hom := by
    intro e
    rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w]; rfl
  let x₀ : 𝔐.Li → (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := fun e => Over.homMk ((𝔐.M.pt e).left ≫ 𝔐.m.φ) (hx0 e)
  let pt' : 𝔐.Li → (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := fun e => eqToHom hT ≫ x₀ e
  have hleft : ∀ e, (pt' e).left = (𝔐.M.pt e).left ≫ 𝔐.m.φ := by
    intro e
    simp [pt', x₀]
  have hx0mul : ∀ e e', x₀ (e + e') = x₀ e * x₀ e' := by
    intro e e'
    apply Over.OverMorphism.ext
    rw [hpb.2 (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) (𝔐.M.pt e) (𝔐.M.pt e') (x₀ e) (x₀ e') rfl rfl, ← 𝔐.M.add]
    rfl
  have hadd : ∀ e e', pt' (e + e') = pt' e * pt' e' := by
    intro e e'
    simp only [pt']
    rw [hx0mul, MonObj.comp_mul]
  have htan : ∀ e, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) (pt' e) := by
    intro e
    have h := 𝔐.M.tan e
    unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at h ⊢
    rw [hleft, ← Category.assoc, h, hone]
  have hinj : Function.Injective pt' := by
    intro e e' hee
    apply 𝔐.M.inj
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [← hleft, ← hleft, hee]
    · rw [Over.w, Over.w]
  have hfa : (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom.comp (algebraMap Ω (DualNumber Ω)) = RingHom.id Ω := by
    ext r
    simp
  have honto : ∀ v : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) v → ∃ e, pt' e = v := by
    intro v hv
    have hw : v.left ≫ Y.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f := by
      rw [Over.w]
      simp [GlobalTheory.CompanionTheory.Ar.epsAt]
    obtain ⟨L, hL1, hL2⟩ : ∃ L, L ≫ 𝔐.m.φ = v.left ∧ L ≫ 𝔐.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom :=
      ⟨_, hpb.1.lift_fst _ _ hw, hpb.1.lift_snd _ _ hw⟩
    have htw : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G 𝔐.ξ (Over.homMk (U := GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) L hL2) := by
      unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at hv ⊢
      apply hpb.1.hom_ext
      · rw [Category.assoc]
        change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.m.φ = _
        rw [hL1, hv, hone]
      · rw [Category.assoc]
        change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.t.G.hom = _
        rw [hL2, Over.w]
        show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ 𝔐.ξ = 𝔐.ξ
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    obtain ⟨e, he⟩ := 𝔐.M.onto _ htw
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    rw [hleft, he]
    exact hL1
  have hsmul : ∀ (a : Ω) (e : 𝔐.Li), (pt' (a • e)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul a)) ≫ (pt' e).left := by
    intro a e
    rw [hleft, hleft, 𝔐.M.smul, Category.assoc]
  let M' : GlobalTheory.CompanionTheory.Ar.LieModel Y.t.G (𝔐.ξ ≫ 𝔐.f) 𝔐.Li := ⟨pt', htan, hinj, honto, hadd, hsmul⟩
  have hsm : AlgebraicGeometry.Smooth Y.t.G.hom := @ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth _ _ _ Y.t.semi
  obtain ⟨j, hj1, hj2, -⟩ := GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.exists_ext hsm (𝔐.fn.comp ψ.toRingHom) (Z.ξ₀ ≫ Y.j) (𝔐.ξ ≫ 𝔐.f) hdom'.symm Z.M M'
  refine ⟨𝔐.fn.comp ψ.toRingHom, j, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CptIn.IsTie
  exact ⟨hdom, hcst, hj2, fun e => (hleft (j e)).symm.trans (hj1 e)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | exact GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | (intros; apply GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem isSemiAbelian_of_isGrpPullback : ∀ (X X' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G']
    [IsCommMonObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsSemiAbelian G →
    IsSemiAbelian G' := by
  intro X X' G _ G' _ _ f φ h hG
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback f G hG)

end GlobalTheory.CompanionTheory.Ar
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.torsion_points_defined_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (t : SAB H S) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → 0 < D.p + D.q → IsProper (Limits.pullback.snd t.G.hom ξ) → (∀ (k : Type) [Field k] (f : Ω →+* k) (g : Over.mk (spMap f ≫ ξ) ⟶ t.G), g ^ n = 1 → ∃ x : Over.mk ξ ⟶ t.G, g.left = spMap f ≫ x.left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))) → ∃ (ev : D.La → (Over.mk ξ ⟶ t.G)) (ζ₀ : Ωˣ), IsPrimitiveRoot ζ₀ n ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.level_parametrisation | exact GlobalTheory.CompanionTheory.Ar.HT.level_parametrisation | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.level_parametrisation <;> assumption)
end
