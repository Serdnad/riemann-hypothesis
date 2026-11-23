module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.Field
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.FineAgree

theorem sec_hom {S : Scheme.{0}} {G : Over S} (x : 𝟙_ (Over S) ⟶ G) : x.left ≫ G.hom = 𝟙 S := Over.w x

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A] [IsDomain A] (f₁ f₂ : L.W →+* A), f₁.comp L.b = f₂.comp L.b → ∀ (B' : Over (Sp A)) [GrpObj B'] (π₁ π₂ : B'.left ⟶ L.D.P.A.left) (act' : 𝓞 E → (B'.left ⟶ B'.left)), IsGrpPullback B' L.D.P.A (spMap f₁) π₁ → IsGrpPullback B' L.D.P.A (spMap f₂) π₂ → (letI := H.starRing; ∀ x, act' x ≫ π₁ = π₁ ≫ (L.oa.onB.act x).left) → (letI := H.starRing; ∀ x, act' x ≫ π₂ = π₂ ≫ (L.oa.onB.act x).left) → (∀ x, act' x ≫ B'.hom = B'.hom) → LBIso (L.D.P.L.pull π₁) (L.D.P.L.pull π₂) → ∀ (F : Type) [Field F] (j : A →+* F), Function.Injective j → (∀ a, ∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ (L.o.etaA a).left ≫ L.φB ∧ z ≫ π₂ = spMap j ≫ spMap f₂ ≫ (L.o.etaA a).left ≫ L.φB) → (∀ y, ∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ (L.D.c y).left ∧ z ≫ π₂ = spMap j ≫ spMap f₂ ≫ (L.D.c y).left) → f₁ = f₂ ∧ π₁ = π₂ := by
  intro E _ _ _ H D' l c L A _ _ f₁ f₂ hb B' _ π₁ π₂ act' h₁ h₂ ha₁ ha₂ hab hL F _ j hj hη hc
  letI := H.starRing
  obtain ⟨o', ⟨m₁⟩⟩ := GlobalTheory.obj_pull E H D' (LowDat.lowLevel l) _ _ (baseKA _) (baseKA _) (RingHom.id _) _ _
    (lowMap c L.b) (lowMap c (f₁.comp L.b)) (spMap f₁) rfl rfl (by
      simp only [lowMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) L.o
  have hφ₁ : IsGrpPullback o'.t.G L.D.P.A (spMap f₁) (m₁.φ ≫ L.φB) :=
    (m₁.cart.comp L.ab.1).congr (Category.comp_id _) rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hφ₁ h₁
  haveI := he
  have hew : e.hom.left ≫ B'.hom = o'.t.G.hom := Over.w e.hom
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : o'.t.G.left ⟶ L.o.t.G.left, ψ ≫ L.φB = e.hom.left ≫ π₂ ∧
      ψ ≫ L.o.t.G.hom = o'.t.G.hom ≫ spMap f₂ :=
    ⟨L.ab.1.1.lift (e.hom.left ≫ π₂) (o'.t.G.hom ≫ spMap f₂) (by
      rw [Category.assoc, h₂.1.w, ← Category.assoc, hew, Category.comp_id]), IsPullback.lift_fst _ _ _ _,
      IsPullback.lift_snd _ _ _ _⟩
  have hψ : IsGrpPullback o'.t.G L.o.t.G (spMap f₂) ψ := by
    have n : IsGrpPullback o'.t.G L.D.P.A (spMap f₂ ≫ 𝟙 _) (ψ ≫ L.φB) := by
      rw [hψ₁, Category.comp_id]
      exact ((isGrpPullback_of_iso e).comp h₂).congr (Category.id_comp _) rfl
    exact L.ab.1.cancel n hψ₂
  have hact : ∀ x, (o'.t.act.act x).left ≫ ψ = ψ ≫ (L.o.t.act.act x).left := by
    intro x
    have key : (o'.t.act.act x).left ≫ e.hom.left = e.hom.left ≫ act' x := by
      apply h₁.1.hom_ext
      · have e1 : (o'.t.act.act x).left ≫ m₁.φ = m₁.φ ≫ (L.o.t.act.act x).left := m₁.act x
        calc ((o'.t.act.act x).left ≫ e.hom.left) ≫ π₁ = ((o'.t.act.act x).left ≫ m₁.φ) ≫ L.φB := by
              rw [Category.assoc, heq, Category.assoc]
          _ = m₁.φ ≫ (L.o.t.act.act x).left ≫ L.φB := by rw [e1, Category.assoc]
          _ = (m₁.φ ≫ L.φB) ≫ (L.oa.onB.act x).left := by rw [L.ab.2.1, Category.assoc]
          _ = (e.hom.left ≫ act' x) ≫ π₁ := by rw [← heq, Category.assoc, Category.assoc, ha₁]
      · rw [Category.assoc, hew, Category.assoc, hab, hew, Over.w (o'.t.act.act x)]
    apply L.ab.1.1.hom_ext
    · calc ((o'.t.act.act x).left ≫ ψ) ≫ L.φB = ((o'.t.act.act x).left ≫ e.hom.left) ≫ π₂ := by
            rw [Category.assoc, hψ₁, Category.assoc]
        _ = (ψ ≫ L.φB) ≫ (L.oa.onB.act x).left := by rw [key, Category.assoc, ha₂, hψ₁, Category.assoc]
        _ = (ψ ≫ (L.o.t.act.act x).left) ≫ L.φB := by rw [Category.assoc, Category.assoc, L.ab.2.1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (o'.t.act.act x), Category.assoc,
        Over.w (L.o.t.act.act x), hψ₂]

  have hLψ : LBIso o'.t.PP.L (L.o.t.PP.L.pull ψ) := by
    obtain ⟨w, hw, -⟩ := m₁.lin
    have K1 : LBIso o'.t.PP.L (L.D.P.L.pull (m₁.φ ≫ L.φB)) :=
      GlobalTheory.ThetaAffineGlue.lbIso_comp o'.t.PP.isLB L.o.t.PP.isLB L.D.P.isLB ⟨w, hw⟩ L.ab.2.2
    rw [← heq] at K1
    have K2 : LBIso o'.t.PP.L ((L.D.P.L.pull π₂).pull e.hom.left) :=
      GlobalTheory.ThetaAffineGlue.lbIso_cancel o'.t.PP.isLB (pull_isLB L.D.P.isLB _) L.D.P.isLB K1 hL.symm
    have K3 : LBIso o'.t.PP.L (L.D.P.L.pull (e.hom.left ≫ π₂)) :=
      GlobalTheory.ThetaAffineGlue.lbIso_comp o'.t.PP.isLB (pull_isLB L.D.P.isLB _) L.D.P.isLB K2
        (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB L.D.P.isLB _))
    rw [← hψ₁] at K3
    exact GlobalTheory.ThetaAffineGlue.lbIso_cancel o'.t.PP.isLB L.o.t.PP.isLB L.D.P.isLB K3 L.ab.2.2
  obtain ⟨n, hn⟩ := GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper o'.t L.o.t (spMap f₂) ψ L.o.proper hψ hact hLψ
  haveI : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  haveI := L.o.proper
  have transfer : ∀ (u : Sp A ⟶ o'.t.G.left) (v : Sp L.W ⟶ L.o.t.G.left), u ≫ o'.t.G.hom = 𝟙 _ →
      v ≫ L.o.t.G.hom = 𝟙 _ → u ≫ m₁.φ = spMap f₁ ≫ v →
      (∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ v ≫ L.φB ∧
        z ≫ π₂ = spMap j ≫ spMap f₂ ≫ v ≫ L.φB) → u ≫ ψ = spMap f₂ ≫ v := by
    intro u v hu hv huv ⟨z, hz0, hz1, hz2⟩
    have hz : spMap j ≫ u ≫ e.hom.left = z := by
      apply h₁.1.hom_ext
      · rw [hz1, Category.assoc, Category.assoc, heq, ← Category.assoc u, huv, Category.assoc]
      · rw [hz0, Category.assoc, Category.assoc, hew, hu, Category.comp_id]
    refine ext_of_isDominant_of_isSeparated (X := Sp A) L.o.t.G.hom ?_ (spMap j) ?_
    · rw [Category.assoc, hψ₂, ← Category.assoc, hu, Category.id_comp, Category.assoc, hv, Category.comp_id]
    · apply L.ab.1.1.hom_ext
      · rw [Category.assoc, Category.assoc, hψ₁, ← Category.assoc u, ← Category.assoc, hz, hz2,
          Category.assoc, Category.assoc]
      · rw [Category.assoc, Category.assoc, hψ₂, ← Category.assoc u, hu, Category.id_comp, Category.assoc,
          Category.assoc, hv, Category.comp_id]
  have hetaA : ∀ a, (o'.etaA a).left ≫ n.φ = spMap f₂ ≫ (L.o.etaA a).left := by
    intro a
    rw [hn]
    exact transfer _ _ (sec_hom _) (sec_hom _) (m₁.etaA a) (hη a)
  have heta := GlobalTheory.T.sabMap_keeps_levelEta c A L.W (f₁.comp L.b) L.b o' L.o f₂ hb.symm n hetaA
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ObjMap o' L.o (spMap f₂), m₂.φ = ψ := ⟨⟨n, heta, hetaA⟩, hn⟩

  have hcy : ∀ y, ∃ cy : Sp L.W ⟶ L.o.t.G.left, cy ≫ L.φB = (L.D.c y).left ∧ cy ≫ L.o.t.G.hom = 𝟙 _ := fun y =>
    ⟨L.ab.1.1.lift (L.D.c y).left (𝟙 _) (by rw [sec_hom, Category.comp_id]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  choose cy hcy₁ hcy₂ using hcy
  have hx : ∀ y, ∃ x : Sp A ⟶ o'.t.G.left, x ≫ m₁.φ = spMap f₁ ≫ cy y ∧ x ≫ o'.t.G.hom = 𝟙 _ := fun y =>
    ⟨m₁.cart.1.lift (spMap f₁ ≫ cy y) (𝟙 _) (by
      rw [Category.assoc, hcy₂, Category.comp_id, Category.id_comp]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  choose x hx₁ hx₃ using hx
  have hf : f₁ = f₂ := by
    refine L.fineRed A f₁ f₂ hb o' m₁ m₂ x (fun y => ?_) (fun y => ?_) hx₃
    · rw [← Category.assoc, hx₁, Category.assoc, hcy₁]
    · rw [hm₂, ← Category.assoc, transfer (x y) (cy y) (hx₃ y) (hcy₂ y) (hx₁ y) (by
        obtain ⟨z, hz⟩ := hc y
        exact ⟨z, by simpa only [hcy₁] using hz⟩), Category.assoc, hcy₁]
  subst hf
  refine ⟨rfl, ?_⟩
  have hu : m₁.φ = m₂.φ := GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical A
    (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) _ _ o' L.o (spMap f₁) m₁ m₂
  have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  apply (cancel_epi e.hom.left).1
  rw [heq, hu, hm₂, hψ₁]

end GlobalTheory.UCanon.FineAgree
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.PtsDescent

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') (z : Over.mk (T.hom ≫ f) ⟶ G)
    (hz : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
  have e : Φ x = z := Over.OverMorphism.ext ((hΦ x).trans hz.symm)
  rw [← hΦ, map_pow, e]

theorem degPre_c_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : D.X) (n : ℕ) :
    D.c (n • y) = D.c y ^ n := by
  have h0 : D.c 0 = 1 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, D.c_add, ih, pow_succ]; rfl

end GlobalTheory.UCanon.PtsDescent

namespace GlobalTheory.UCanon.PtsDescent

theorem pulledObj_descends_with_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (θ : o'.t.G.left ⟶ B'.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → IsGrpPullback o'.t.G B' (𝟙 _) θ → LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) → (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) → IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) ∧ LBIso o'.t.PP.L (M₀.pull (θ ≫ π₀)) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ θ ≫ π₀ = spMap k₀.subtype ≫ x₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hdiv K _ _ _ ev k₀ hk₀ o' m₁ B₀ _ _ M₀ c₀ B' _ π₁ π₀ w c' θ hB₀ hM₀ hpb1 hpb0 hw hc' hθ hL hpts
  have h1 : IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) :=
    (hθ.comp hpb0).congr (Category.id_comp _) rfl
  refine ⟨h1, ?_, ?_⟩
  · exact LBIso.trans o'.t.PP.isLB (pull_isLB Q.P.isLB _) (pull_isLB hM₀ _) hL
      (GlobalTheory.GenSpread.lbIso_pull_comp θ rfl rfl ⟨w, hw⟩)

  · intro y
    have hpb : IsGrpPullback o'.t.G L.D.P.A (spMap (ev.comp iw)) (m₁.toSABMap.φ ≫ L.φB) :=
      (m₁.cart.comp L.ab.1).congr (Category.comp_id _) rfl
    let x : Sp K ⟶ o'.t.G.left := hpb.1.lift (spMap (ev.comp iw) ≫ (L.D.c y).left) (𝟙 _)
      (by rw [Category.assoc, Over.w (L.D.c y)]; simp)
    have hx1 : x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left := hpb.1.lift_fst _ _ _
    have hx2 : x ≫ o'.t.G.hom = 𝟙 _ := hpb.1.lift_snd _ _ _
    refine ⟨x, hx2, hx1, ?_⟩
    let xp : 𝟙_ (Over (Sp K)) ⟶ o'.t.G := Over.homMk x (by simpa using hx2)
    let z : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw)) ⟶ L.D.P.A := toUnit _ ≫ L.D.c y
    have htu : (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw)))).left =
        (𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw) := by
      simpa using Over.w (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))))
    have hz : z.left = xp.left ≫ m₁.toSABMap.φ ≫ L.φB := by
      show (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))) ≫ L.D.c y).left = x ≫ m₁.toSABMap.φ ≫ L.φB
      rw [Over.comp_left, htu, hx1]; simp
    have hpow := pow_left_of_isGrpPullback hpb _ xp z hz l.M'
    have hxa : (xp ^ l.M').left ≫ m₁.toSABMap.φ ≫ L.φB =
        spMap (ev.comp iw) ≫ (L.D.c (l.M' • e (e.symm y))).left := by
      rw [LinearEquiv.apply_symm_apply, degPre_c_nsmul, ← hpow]
      show ((toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))) ≫ L.D.c y) ^ l.M').left = _
      rw [← MonObj.comp_pow, Over.comp_left, htu]; simp
    have hxs : (xp ^ l.M').left ≫ o'.t.G.hom = 𝟙 _ := by simpa using Over.w (xp ^ l.M')
    have h₁ := hpts _ (e.symm y) hxs hxa
    have hsec : (xp ^ l.M').left ≫ θ = c' (e.symm y) := by
      apply hpb1.1.hom_ext
      · rw [Category.assoc, h₁, (hc' _).2.1]
      · rw [Category.assoc, hθ.1.w, ← Category.assoc, hxs, (hc' _).1]; simp
    have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.grpPullback_point_descends_algClosed_subfield K k₀ hk₀ B₀ o'.t.G (θ ≫ π₀) hB₀ h1 l.M' hM' xp (c₀ (e.symm y))
      (by rw [← Category.assoc, hsec, (hc' _).2.2])
    exact ⟨y₀, hy₀⟩

end GlobalTheory.UCanon.PtsDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautEtaleB

theorem isEtaleCompletion_of_forall_eq_inj (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    (hAd : IsDomain (AdicCompletion (maximalIdeal A) A))
    (hAn : IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A))
    (hR : IsAdicComplete (maximalIdeal R) R) (φ : A →+* R) (hφ : IsLocalHom φ)
    (hprim : maximalIdeal R ≤ ((maximalIdeal A).map φ).radical)
    (hres : ((residue R).comp φ).Finite) (hdim : ringKrullDim R = ringKrullDim A)
    (hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R']
      [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' →
      ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g →
        f.comp φ = g.comp φ → f = g) :
    GlobalTheory.Toroidal.IsEtaleCompletion φ := by
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  obtain ⟨ψ, hψl, hψ⟩ := GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp A R hR φ hφ
  have hmap : (maximalIdeal B).map ψ = (maximalIdeal A).map φ := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]
  have hresψ : ((residue R).comp ψ).Finite := by
    have e : ((residue R).comp ψ).comp (algebraMap A B) = (residue R).comp φ := by
      rw [RingHom.comp_assoc, hψ]
    exact RingHom.Finite.of_comp_finite (e ▸ hres)
  have hfin : ψ.Finite := GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama B R ψ inferInstance hψl (hmap ▸ hprim) hresψ
  have hdB : ringKrullDim R = ringKrullDim B := by rw [hdim, UpperTheory.V.CA.g_dimcpl]
  have hi : Function.Injective ψ := GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain B R ψ hfin hdB
  have hs : Function.Surjective ψ := GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal B R ψ inferInstance hi hfin
    (fun R' _ _ _ _ _ _ hR' f g hf' hg' hf hg h => hinj R' hR' f g hf' hg' hf hg (by
      rw [← hψ, ← RingHom.comp_assoc, h, RingHom.comp_assoc]))
  refine ⟨?_, ?_, hres⟩
  · rw [← hψ]
    refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)) ?_
    exact RingHom.Flat.of_bijective ⟨hi, hs⟩
  · rw [← hmap]
    exact map_maximalIdeal_of_surjective ψ hs

theorem charZero_essFiniteType_stalk (K : Type) [Field K] [CharZero K] [FiniteDimensional ℚ K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [LocallyOfFiniteType f] (x : X) :
    CharZero (X.presheaf.stalk x) ∧ Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  let y : PrimeSpectrum K := f x
  letI : Algebra K ((Sp K).presheaf.stalk (f x)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp K).presheaf.stalk (f x)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap K ((Sp K).presheaf.stalk (f x))
  have h₁ : (f.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hσ : Function.Injective ((f.stalkMap x).hom.comp φ) := RingHom.injective _
  refine ⟨charZero_of_injective_ringHom hσ, ?_⟩
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hK : Algebra.EssFiniteType ℤ K := Algebra.EssFiniteType.comp ℤ ℚ K
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hK).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

theorem exists_fracMap {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

theorem tautB_isEtaleCompletion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT ξ hξ
  obtain ⟨hqf, hfin⟩ := GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C hT ξ hξ
  have hdimS := ringKrullDim_stalk_eq_of_isTaut hU C hT.1 ξ hξ hfin
  haveI hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  haveI : IsNoetherianRing (ChartRing k m e) := hAdm.1
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  have hRc : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) := hAdm.2.2.2
  have hdimR : ringKrullDim (ChartRing k m e) = ((m + e : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries k (Fin m ⊕ Fin e), ringKrullDim_eq_zero_of_field]
    simp [Nat.card_sum]
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, -, hji, -⟩, -⟩ := hU
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI := c.fin
  set x := ξ (closedPoint (ChartRing k m e)) with hx
  haveI : IsDomain (S.presheaf.stalk x) := hnorm.isDomain_stalk x
  haveI : IsIntegrallyClosed (S.presheaf.stalk x) := hnorm.isIntegrallyClosed_stalk x
  obtain ⟨hc0, hess⟩ := charZero_essFiniteType_stalk c.F (π ≫ zs) x
  haveI := hc0
  haveI := hess
  haveI : IsNoetherianRing (S.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨hAd, hAn⟩ := GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed (S.presheaf.stalk x)
  set ψ := (Scheme.stalkClosedPointTo ξ).hom with hψ
  have eξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hpt : ∀ p : Sp (ChartRing k m e), ξ p = S.fromSpecStalk x (Spec.map (Scheme.stalkClosedPointTo ξ) p) := by
    intro p
    conv_lhs => rw [← eξ]
    rfl
  have hprim : maximalIdeal (ChartRing k m e) ≤ ((maximalIdeal (S.presheaf.stalk x)).map ψ).radical := by
    intro r hr
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hle, hP⟩
    have hc : Ideal.comap ψ P = maximalIdeal (S.presheaf.stalk x) :=
      ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hle)).symm
    have hq : (⟨P, hP⟩ : Sp (ChartRing k m e)) = closedPoint (ChartRing k m e) := by
      refine hqf _ ((hpt _).trans (Eq.trans ?_ (hpt (closedPoint _)).symm))
      congr 1
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ψ P = Ideal.comap ψ (maximalIdeal (ChartRing k m e))
      rw [hc]
      refine le_antisymm ?_ (le_maximalIdeal (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top))
      intro a ha
      exact map_nonunit ψ a ha
    have hP' : P = maximalIdeal (ChartRing k m e) := congrArg PrimeSpectrum.asIdeal hq
    rw [hP']
    exact hr
  have hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R']
      [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' →
      ∀ f g : ChartRing k m e →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g →
        f.comp ψ = g.comp ψ → f = g := by
    intro R' _ _ _ _ _ _ hR' f g hfi hgi hfl hgl hfg
    have hB : GlobalTheory.Mum.Base R' := ⟨⟨inferInstance, inferInstance, inferInstance, hR'⟩, inferInstance⟩
    obtain ⟨fK, hfK⟩ := exists_fracMap f hfi
    obtain ⟨gK, hgK⟩ := exists_fracMap g hgi
    obtain ⟨-, -, -, hInj, -⟩ := hT.1
    refine hInj R' hB f g hfi hgi hfl hgl (spMap fK) (spMap gK) hfK hgK ?_
    have hsp : spMap f ≫ Spec.map (Scheme.stalkClosedPointTo ξ) = spMap g ≫ Spec.map (Scheme.stalkClosedPointTo ξ) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact congrArg (fun h : S.presheaf.stalk x →+* R' => h a) hfg
    have hfξ : spMap f ≫ ξ = spMap g ≫ ξ := by
      calc spMap f ≫ ξ = spMap f ≫ (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk x) := by rw [eξ]
        _ = spMap g ≫ (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk x) := by
          rw [← Category.assoc, hsp, Category.assoc]
        _ = spMap g ≫ ξ := by rw [eξ]
    rw [← cancel_mono j, Category.assoc, Category.assoc, hξ, ← Category.assoc, ← Category.assoc, hfK, hgK,
      Category.assoc, Category.assoc, hfξ]
  exact isEtaleCompletion_of_forall_eq_inj (S.presheaf.stalk x) (ChartRing k m e) hAd hAn hRc ψ inferInstance hprim hfin
    (by rw [hdimR, hdimS]) hinj

end GlobalTheory.TautEtaleB
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms


theorem _root_.GlobalTheory.T.exists_theta_witnesses_baseChange_member : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  first | exact @GlobalTheory.TermsMove.exists_witnesses | exact GlobalTheory.TermsMove.exists_witnesses | (intros; apply GlobalTheory.TermsMove.exists_witnesses <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualNumber_points_pulledBack_object_from_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (k : Type) [Field k] (f : L.W →+* DualNumber k) (o' : LowObj D' c (f.comp L.b)) (m₁ : ObjMap o' L.o (spMap f)) (m₂ : ObjMap o' L.o (spMap (GlobalTheory.RigChart.constHom f))) (n : ℕ), (n : k) ≠ 0 → (∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k), x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ) → ∀ u : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, u y ≫ o'.t.G.hom = 𝟙 _) → (∀ y, u y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c (n • y)).left) → (∀ y, u y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c (n • y)).left) → ∃ x : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) := by
  first | exact @GlobalTheory.UCanon.pts_eps_of_mul | exact GlobalTheory.UCanon.pts_eps_of_mul | (intros; apply GlobalTheory.UCanon.pts_eps_of_mul <;> assumption)
end
