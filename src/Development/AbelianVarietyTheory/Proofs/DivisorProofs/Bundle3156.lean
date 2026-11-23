module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefOverIntegral

theorem mem_of_isIntegral {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {x : K}
    (hx : IsIntegral k₀ x) : x ∈ k₀ := by
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k₀)
    (K := integralClosure k₀ K)).2 ⟨x, hx⟩
  have h1 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = x := congrArg Subtype.val ha
  have h2 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = (a : K) := rfl
  rw [← h1, h2]
  exact a.2

theorem defOver_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {K : Type} [Field K]
    (k₀ : Subfield K), IsAlgClosed k₀ → ∀ P : Sp K ⟶ X, GlobalTheory.UChart.DefOver k₀ (P ≫ f) → GlobalTheory.UChart.DefOver k₀ P := by
  intro X Y f _ K _ k₀ hk P ⟨Q₀, hQ⟩
  let g := pullback.snd f Q₀
  let Pt : Sp K ⟶ pullback f Q₀ := pullback.lift P (spMap k₀.subtype) hQ.symm
  haveI : IsAffine (pullback f Q₀) := isAffine_of_isAffineHom g
  have hint : (g.app ⊤).hom.IsIntegral := g.isIntegral_app ⊤ (isAffineOpen_top _)
  let φc : Γ(pullback f Q₀, ⊤) ⟶ CommRingCat.of K := Pt.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hPt : Pt = Spec.map φc ≫ (pullback f Q₀).isoSpec.inv := by
    have h := Scheme.isoSpec_inv_naturality Pt
    rw [Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hg : Pt ≫ g = spMap k₀.subtype := pullback.lift_snd _ _ _
  have hcomp : g.appTop ≫ φc = (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom ≫ CommRingCat.ofHom k₀.subtype := by
    have h := congrArg Scheme.Hom.appTop hg
    rw [Scheme.Hom.comp_appTop] at h
    simp only [φc, ← Category.assoc, h]
    exact Scheme.ΓSpecIso_naturality _
  have hmem : ∀ r, φc.hom r ∈ k₀ := by
    intro r
    obtain ⟨p, hpm, hp⟩ := hint r
    refine mem_of_isIntegral k₀ hk ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap k₀ K).comp (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom = φc.hom.comp (g.app ⊤).hom := by
      have := congrArg CommRingCat.Hom.hom hcomp
      exact this.symm
    rw [e]
    have h3 := Polynomial.hom_eval₂ p (g.app ⊤).hom φc.hom r
    rw [hp] at h3
    exact h3.symm.trans (RingHom.map_zero _)
  let φ₀ : Γ(pullback f Q₀, ⊤) →+* k₀ := φc.hom.codRestrict k₀ hmem
  refine ⟨Spec.map (CommRingCat.ofHom φ₀) ≫ (pullback f Q₀).isoSpec.inv ≫ pullback.fst f Q₀, ?_⟩
  have e2 : spMap k₀.subtype ≫ Spec.map (CommRingCat.ofHom φ₀) = Spec.map φc := by
    rw [spMap, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, e2, ← Category.assoc, ← hPt]
  exact pullback.lift_fst _ _ _

end GlobalTheory.DefOverIntegral
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem stalkClosedPointTo_comp_stalkMap_spec (X : Scheme.{0}) {R W : Type} [CommRing R] [IsLocalRing R]
    [CommRing W] [IsLocalRing W] (ξ : Sp R ⟶ X) (g : R →+* W)
    (hs : (spMap g ≫ ξ) (closedPoint W) ⤳ ξ (closedPoint R)) (a : X.presheaf.stalk (ξ (closedPoint R))) :
    (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((X.presheaf.stalkSpecializes hs).hom a) =
      g ((Scheme.stalkClosedPointTo ξ).hom a) := by
  have key : X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (spMap g ≫ ξ) =
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom g := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (ξ (closedPoint R))), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact congrArg (fun q => q.hom a) key

theorem bijective_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem isLocalHom_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    IsLocalHom (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact ⟨fun a ha => ha⟩

theorem stalkClosedPointTo_mem_subfield_of_definedOver {X : Scheme.{0}} {K : Type} [Field K] (k₀ : Subfield K) (Q : Sp K ⟶ X)
    (hQ : GlobalTheory.UChart.DefOver k₀ Q) (b : X.presheaf.stalk (Q (closedPoint K))) :
    (Scheme.stalkClosedPointTo Q).hom b ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hQ
  have e : (spMap k₀.subtype ≫ P₀) (closedPoint K) = P₀ (closedPoint k₀) := by
    change P₀ ((spMap k₀.subtype) (closedPoint K)) = _
    congr 1
    exact Subsingleton.elim _ _
  have hs : (spMap k₀.subtype ≫ P₀) (closedPoint K) ⤳ P₀ (closedPoint k₀) := e ▸ specializes_refl _
  obtain ⟨a, rfl⟩ := (bijective_stalkSpecializes_of_eq hs e).2 b
  rw [stalkClosedPointTo_comp_stalkMap_spec X P₀ k₀.subtype hs a]
  exact SetLike.coe_mem _

theorem stalkVal_closedPoint : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (ξ₁ : Sp R ⟶ X) (K : Type) [Field K] (ev₁ : R →+* K) (k₀ : Subfield K), (∀ p, (spMap ev₁ ≫ ξ₁) p = ξ₁ (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ ξ₁) → ∀ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev₁ h ∈ k₀ ∧ (h ∈ maximalIdeal R → ev₁ h = 0) := by
  intro X R _ _ ξ₁ K _ ev₁ k₀ hpt hdef h hh
  obtain ⟨a, rfl⟩ := hh
  have e := hpt (closedPoint K)
  have hs : (spMap ev₁ ≫ ξ₁) (closedPoint K) ⤳ ξ₁ (closedPoint R) := e ▸ specializes_refl _
  have hv := stalkClosedPointTo_comp_stalkMap_spec X ξ₁ ev₁ hs a
  refine ⟨?_, fun hm => ?_⟩
  · rw [← hv]
    exact stalkClosedPointTo_mem_subfield_of_definedOver k₀ _ hdef _
  · by_contra hne
    have hl := isLocalHom_stalkSpecializes_of_eq hs e
    have hu : IsUnit ((Scheme.stalkClosedPointTo (spMap ev₁ ≫ ξ₁)).hom
        ((X.presheaf.stalkSpecializes hs).hom a)) := by
      rw [hv]; exact Ne.isUnit hne
    have ha : IsUnit a := isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu)
    exact (mem_maximalIdeal _).1 hm (ha.map _)

end GlobalTheory.USep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DescLBExt

theorem exists_lb_extension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ M : LB G.left, M.IsLB ∧ LBIso (M.pull e) tF.PP.L := by
  intro E _ _ _ H Dw l Xo c φ h1 h2 h3 Z zs i OZ N d J S π j _ BD hU hpre tF hmap G _ _ e hsa he hch
  have hU' := hU
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU'
  have := hsa.smooth
  have := hsa.geomConnected
  have := hsa.quasiCompact
  have := hsa.separated
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  haveI := GlobalTheory.IsNormalScheme.of_pred hS
  have hst := GlobalTheory.T.exists_lineBundle_extension_at_boundaryPoint Xo c φ h1 h2 h3 zs i OZ N d J π j BD hU hpre tF hmap G e hsa he hch
  exact GlobalTheory.T.exists_rigidifiedLineBundle_extension_of_local G.hom j hdense e tF.G.hom he.1 (eSec G) (eSec tF.G) (Over.w η[G]) (cubeMapOf he).e_comm
    tF.PP.L tF.PP.isLB tF.PP.rig tF.PP.rigGen fun x hx => by
      obtain ⟨Nx, hNx, hx'⟩ := hst x hx
      exact GlobalTheory.T.exists_lineBundle_spread_from_localScheme G.hom j e tF.G.hom he.1 tF.PP.L tF.PP.isLB x Nx hNx hx'

end GlobalTheory.DescLBExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.UGZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

theorem s_ne_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V)
    (k : Fin Cm.m) : Cm.s k ≠ 0 := by
  intro hk
  have hδ : Cm.δ k ≠ 0 := Cm.cone.linearIndependent.ne_zero k
  have hsym := (Cm.cone.mem k).1
  obtain ⟨y, hy⟩ : ∃ y, Cm.δ k y y ≠ 0 := by
    by_contra h
    push_neg at h
    apply hδ
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := h (a + b)
    have h2 := h a
    have h3 := h b
    simp only [map_add (f := _), LinearMap.add_apply] at h1
    rw [hsym b a] at h1
    simp only [LinearMap.zero_apply]
    omega
  obtain ⟨u, n, hn, hc⟩ := Cm.mono y
  have hM : (0 : ℤ) < (l.M' : ℤ) := by exact_mod_cast GlobalTheory.LevelExist.M'_pos l
  have hnk : n k ≠ 0 := by
    intro h0
    have e := hn k
    rw [h0] at e
    simp only [LinearMap.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero] at e
    rcases mul_eq_zero.1 e with e | e
    · omega
    · exact hy e
  apply GlobalTheory.PsiCoordLocal.ne_zero_of_coord hc
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; exact zero_pow hnk), mul_zero]

end GlobalTheory.UGZero

namespace GlobalTheory.UGZero

theorem idlAlong_eq_span_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∃ b : Fin Cm.m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ ((l.M' : ℤ) • Cm.δ k)) ∧ idlAlong J (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) = Ideal.span {∏ k, Cm.s k ^ b k} := by
  intro E _ _ _ H Dw hpq l Xo c C φ hpf d J hJ hval S π hbl V _ _ _ Cm hV ξ hξ
  haveI : Module.Projective (𝓞 E) Cm.P.D.toPre.X := GlobalTheory.Forms.projective_of_int _ _
  have hP := hpf Cm.P.D.toPre.X Cm.rank
  have key0 : ∀ k, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • Cm.δ k) = n := fun k =>
    hP.exists_nat (Submodule.smul_mem _ _ (Cm.cone.mem k)) (fun y => by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (Cm.cone.nonneg k y))
  choose n hn using key0
  refine ⟨fun k => d * n k, fun k => by rw [hn]; push_cast; ring, ?_⟩
  set f := ∏ k, Cm.s k ^ (d * n k) with hf
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.NormBlPrincipal.idlAlong_comap_principal π _ hbl V ξ
  rw [GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc] at hg₀
  rw [hg₀]
  have hV' := hV
  obtain ⟨⟨hNoeth, -, hIC, -⟩, hchar⟩ := hV'
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : V →+* W,
      Function.Injective ψ → IsLocalHom ψ → Ideal.span {ψ g₀} = Ideal.span {ψ f} := by
    intro W _ _ _ hW ψ hψi hψl
    haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 hW).1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hw : ∀ k, ∃ w : ℕ, Associated (ψ (Cm.s k)) (ϖ ^ w) := fun k => by
      have h0 : ψ (Cm.s k) ≠ 0 := fun h => s_ne_zero Cm k (hψi (h.trans (map_zero ψ).symm))
      obtain ⟨w, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
      exact ⟨w, ⟨u⁻¹, by rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩⟩
    choose w hw using hw
    have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp ψ) :=
      (IsFractionRing.injective W (FractionRing W)).comp hψi
    obtain ⟨gam, e⟩ : ∃ gam : FractionRing V →+* FractionRing W,
        gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ψ :=
      ⟨IsFractionRing.lift hinj, RingHom.ext fun r => by
        rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj r⟩
    have hκ : spMap gam ≫ jK V = jK W ≫ spMap ψ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    obtain ⟨t, tK, P, ⟨a1⟩, ⟨a2⟩, be, hbe, hmono, hφbe⟩ :=
      GlobalTheory.UChart.pull_trait Xo c φ V hV Cm W hW ψ hψi hψl ϖ hϖ w hw (spMap gam) hκ
    have hy : (spMap gam ≫ Cm.y) ≫ C.i = jK W ≫ (spMap ψ ≫ ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) := by
      simp only [UCompact.i, Category.assoc]
      rw [reassoc_of% hξ, reassoc_of% hκ]
    obtain ⟨N, hN, hid⟩ := hval W hW ϖ hϖ _ (spMap gam ≫ Cm.y) hy t tK ⟨a1⟩ ⟨a2⟩ P be hbe hmono
    rw [GlobalTheory.TraitOrder.idlAlong_comp, hg₀, Ideal.map_span, Set.image_singleton] at hid
    rw [hid]
    have hNe : N = ∑ k, w k * (d * n k) := by
      have : (N : ℝ) = ((∑ k, w k * (d * n k) : ℕ) : ℝ) := by
        rw [hN, hφbe]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hn]; ring
      exact_mod_cast this
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    rw [hf, map_prod, hNe, ← Finset.prod_pow_eq_pow_sum]
    refine (Associated.prod Finset.univ (fun k => ψ (Cm.s k ^ (d * n k))) (fun k => ϖ ^ (w k * (d * n k)))
      fun k _ => ?_).symm
    rw [map_pow, pow_mul ϖ (w k)]
    exact (hw k).pow_pow
  haveI := hNoeth
  haveI := hIC
  haveI := hchar
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (s_ne_zero Cm k)
  have hg0 : g₀ ≠ 0 := by
    rintro rfl
    obtain ⟨W, _, _, _, ψ, hW, hψi, hψl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating V
    have := key W hW ψ hψi hψl
    rw [map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at this
    exact hf0 (hψi (this.trans (map_zero ψ).symm))
  have hkey' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
      ∀ ψ : V →+* W, Function.Injective ψ → IsLocalHom ψ → Associated (ψ g₀) (ψ f) := by
    intro W _ _ _ hc ψ hψi hψl
    have : CharZero W := charZero_of_injective_ringHom hψi
    exact Ideal.span_singleton_eq_span_singleton.1 (key W ((GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hc, this⟩) ψ hψi hψl)
  have d1 := GlobalTheory.Poinc.dvd_of_forall_complete_dvr V g₀ f hf0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).symm.dvd
  have d2 := GlobalTheory.Poinc.dvd_of_forall_complete_dvr V f g₀ hg0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).dvd
  exact Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd d2 d1)

end GlobalTheory.UGZero
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
noncomputable section

namespace GlobalTheory.PsiSqGeneric

theorem jFK_self (V : Type) [CommRing V] [IsDomain V] :
    jFK (R := V) (FractionRing V) = 𝟙 (Spec (CommRingCat.of (FractionRing V))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem cst_eq_gm {V : Type} [CommRing V] [IsDomain V] (z : Spec (CommRingCat.of (FractionRing V)))
    (k : (FractionRing V)ˣ) :
    cst (R := V) (FractionRing V) z (k : FractionRing V) =
      (gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k)).val := by
  rw [← gs_unit _ z ⊤ trivial]
  rfl

end GlobalTheory.PsiSqGeneric

namespace GlobalTheory.PsiSqGeneric

theorem core (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (hE : D.PsiEven)
    (h0 : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1)
    (τ₀ : GlobalTheory.UChart.Gens D) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ D.X)
    (hT : GlobalTheory.UChart.TauIn D τ₀ s ε) (mu : D.X) : ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i mu mu ∧
      ∀ (z : Spec (CommRingCat.of (FractionRing V)))
        (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi mu) (jFK (R := V) (FractionRing V)) z J).val ^ 2 =
          cst (R := V) (FractionRing V) z (k : FractionRing V) *
            (val D.sym ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left) z J *
              (val (τ₀ mu (-mu)) (toUnit (TF (R := V) (FractionRing V))).left z J)⁻¹ *
              (rigV D (toUnit (TF (R := V) (FractionRing V))).left z J ^ 2)⁻¹).val := by
  obtain ⟨-, k', hk', hv⟩ := hT mu (-mu)
  refine ⟨k'⁻¹, ?_, fun z J hJ => ?_⟩
  · rw [Units.val_inv_eq_inv_val, hk']
    simp only [map_neg, zpow_neg, Finset.prod_inv_distrib, inv_inv]
  · have hv' : val (D.tau mu (-mu)) (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J =
        gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k') * val (τ₀ mu (-mu)) (jK V) z J :=
      hv z J hJ
    have ev := val_corr hJ (hE mu) (𝟙 (Spec (CommRingCat.of (FractionRing V))))
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at ev
    have p0 := h0 _ (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J hJ
    have hrig : val D.rigK (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J = rigV D (jK V) z J := by
      rw [DegPre.rigK, val_pull hJ, Category.id_comp]; rfl
    have hx : D.xK mu = jK V ≫ (D.c mu).left := rfl
    unfold DegPre.tau at hv'
    rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
      congrArg (fun w => val (D.psi w) (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z J) (add_neg_cancel mu)] at hv'
    rw [hx] at ev
    rw [hrig] at p0 hv'
    rw [jFK_self, GlobalTheory.Poinc.Sep.Frames.toUnit_left_eq, cst_eq_gm]
    have hg : gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k'⁻¹) =
        (gm (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z ⊤ (unitOn k'))⁻¹ := by
      rw [← map_inv]; rfl
    rw [hg, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    have hp := eq_inv_of_mul_eq_one_left p0
    have hb := eq_mul_inv_of_mul_eq ev
    have hG := eq_mul_inv_of_mul_eq hv'.symm
    rw [hG, hp, hb]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

end GlobalTheory.PsiSqGeneric

theorem GlobalTheory.PsiSqGeneric.main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.PsiEven →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (TK V).left) (z : Z) J, Good D.P.L z J →
      val (D.psi 0) r z J * val D.rigK r z J = 1) →
    ∀ (τ₀ : GlobalTheory.UChart.Gens D) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ D.X),
    GlobalTheory.UChart.TauIn D τ₀ s ε → ∀ mu : D.X, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i mu mu ∧
      ∀ z J, Good D.P.L z J →
        (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val ^ 2 =
          cst (FractionRing V) z (k : FractionRing V) *
            (val D.sym ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left) z J *
              (val (τ₀ mu (-mu)) (toUnit (TF (R := V) (FractionRing V))).left z J)⁻¹ *
              (rigV D (toUnit (TF (R := V) (FractionRing V))).left z J ^ 2)⁻¹).val := by
  intro V _ _ D hE h0 τ₀ N s ε hT mu
  exact GlobalTheory.PsiSqGeneric.core V D hE h0 τ₀ N s ε hT mu
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.finrank_uChart_le_min_signature : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  first | exact @GlobalTheory.UChart.Fam.finrank_le_min | exact GlobalTheory.UChart.Fam.finrank_le_min | (intros; apply GlobalTheory.UChart.Fam.finrank_le_min <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_tensorData_biextension_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W), ∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  first | exact @GlobalTheory.Mum.tens_lam_core | exact GlobalTheory.Mum.tens_lam_core | (intros; apply GlobalTheory.Mum.tens_lam_core <;> assumption)
end
