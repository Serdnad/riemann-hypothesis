module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem centre_place : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
    ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  intro k K _ _ _ _ _ C _ x hx c hc
  obtain ⟨hC, hg, hstr⟩ := hx
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  haveI := hC.1
  haveI : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  haveI : GlobalTheory.IsNormalScheme C := isNormalScheme_of_smooth (strHom k C)
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  haveI := hg.2
  set p : Sp K := IsLocalRing.closedPoint K with hp
  have hη : x p = genericPoint C := by
    have hd : Dense (Set.range x) := hg.1.denseRange
    have hr : Set.range x = {x p} := by
      ext y
      exact ⟨by rintro ⟨q, rfl⟩; rw [Subsingleton.elim q p]; rfl, by rintro rfl; exact ⟨p, rfl⟩⟩
    rw [hr] at hd
    exact (IsGenericPoint.eq (isGenericPoint_def.2 hd.closure_eq) (genericPoint_spec C))
  have hco : Order.coheight c = 1 := by
    have hne : Order.coheight c ≠ 0 := by
      intro h0
      have hm : IsMax c := Order.coheight_eq_zero.1 h0
      have h3 : genericPoint C ⤳ c := genericPoint_specializes c
      apply hc
      rw [hη]
      exact ((show c ⤳ genericPoint C from hm (show c ≤ genericPoint C from h3)).antisymm h3).eq
    have hle : (Order.coheight c : WithBot ℕ∞) ≤ 1 := by
      haveI : Nonempty C := ⟨c⟩
      have hd := GlobalTheory.LieSemineg.dim_curve (k := k) (C := C) hC.1
      have h1 := (Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge
      rw [topologicalKrullDim] at hd
      rw [hd] at h1
      exact h1
    have hle' : Order.coheight c ≤ 1 := by exact_mod_cast hle
    exact le_antisymm hle' (ENat.one_le_iff_ne_zero.2 hne)
  haveI hdvr := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hco

  set A := C.presheaf.stalk c
  let P : IsDedekindDomain.HeightOneSpectrum A := IsDiscreteValuationRing.maximalIdeal A
  let ic := C.presheaf.stalkCongr (Inseparable.of_eq hη.symm)
  let ψ : C.functionField →+* K := (ic.hom ≫ Scheme.stalkClosedPointTo x).hom
  have hψ : Function.Bijective ψ := by
    refine ⟨RingHom.injective ψ, ?_⟩
    have h1 : Function.Surjective ic.hom.hom :=
      ((ConcreteCategory.isIso_iff_bijective ic.hom).1 inferInstance).2
    have h2 : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
      have h3 := x.stalkMap_surjective p
      have h4 : Function.Surjective (stalkClosedPointIso (CommRingCat.of K)).hom.hom :=
        ((ConcreteCategory.isIso_iff_bijective (stalkClosedPointIso (CommRingCat.of K)).hom).1 inferInstance).2
      exact h4.comp h3
    exact h2.comp h1
  let e : C.functionField ≃+* K := RingEquiv.ofBijective ψ hψ
  let φ : A →+* K := ψ.comp (algebraMap A C.functionField)
  have hφ : spMap φ ≫ C.fromSpecStalk c = x := by
    have h1 : φ = (C.presheaf.stalkSpecializes (hη ▸ genericPoint_specializes c : x p ⤳ c) ≫ Scheme.stalkClosedPointTo x).hom := by
      show ψ.comp (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom = _
      change (C.presheaf.stalkSpecializes _ ≫ ic.hom ≫ Scheme.stalkClosedPointTo x).hom = _
      rw [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
      erw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [h1]
    change Spec.map (CommRingCat.ofHom _) ≫ _ = x
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have hval : ∀ a : A, (P.valuation C.functionField) (e.symm (φ a)) = P.intValuation a := by
    intro a
    have : e.symm (φ a) = algebraMap A C.functionField a := e.symm_apply_apply _
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P a

  have hk : ∀ t : k, algebraMap k K t = φ (C.presheaf.germ ⊤ c trivial (algebraMap k Γ(C, ⊤) t)) := by
    have h1 : x ≫ strHom k C = spMap ((φ.comp (C.presheaf.germ ⊤ c trivial).hom).comp (algebraMap k Γ(C, ⊤))) := by
      rw [← hφ, Category.assoc, strHom, ← Category.assoc (C.fromSpecStalk c), Scheme.fromSpecStalk_toSpecΓ]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    have h2 := Spec.map_injective (hstr.symm.trans h1)
    intro t
    exact congrArg (fun f => f.hom t) h2
  let vK : Valuation K (WithZero (Multiplicative ℤ)) := (P.valuation C.functionField).comap e.symm.toRingHom
  have hvφ : ∀ a, vK (φ a) = P.intValuation a := fun a => hval a
  have hunit : ∀ a : A, IsUnit a → P.intValuation a = 1 := by
    intro a ha
    refine le_antisymm (P.intValuation_le_one a) (not_lt.1 fun h => ?_)
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ((P.intValuation_lt_one_iff_mem a).1 h) ha)
  let v : Place k K := ⟨vK, fun g => by
      obtain ⟨y, hy⟩ := P.valuation_surjective C.functionField g
      exact ⟨e y, by
        change P.valuation C.functionField (e.symm (e y)) = g
        rw [e.symm_apply_apply]; exact hy⟩,
    fun t ht => by
      rw [hk, hvφ]
      exact hunit _ (((Ne.isUnit ht).map (algebraMap k Γ(C, ⊤))).map _)⟩
  have hle : ∀ a : A, φ a ∈ v.O := fun a => by
    show vK (φ a) ≤ 1
    rw [hvφ]; exact P.intValuation_le_one a
  let ψO : A →+* v.O := φ.codRestrict v.O hle
  have hPm : P.asIdeal = IsLocalRing.maximalIdeal A := rfl
  haveI : IsLocalHom ψO := ⟨fun a ha => by
    by_contra hna
    have hm : a ∈ P.asIdeal := by rw [hPm]; exact hna
    have hlt : vK (φ a) < 1 := by rw [hvφ]; exact (P.intValuation_lt_one_iff_mem a).2 hm
    obtain ⟨u, hu⟩ := ha
    let w : v.O := ((u⁻¹ : v.Oˣ) : v.O)
    have hinv : vK (w : K) ≤ 1 := w.2
    have h1 : φ a * (w : K) = 1 := by
      have := congrArg (fun z : v.O => (z : K)) u.mul_inv
      have e1 : φ a = ((u : v.O) : K) := by rw [hu]; rfl
      rw [e1]
      exact this
    have h2 := congrArg vK h1
    rw [map_mul, map_one] at h2
    have : vK (φ a) * vK (w : K) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' hinv) hlt
    exact absurd h2 this.ne⟩
  refine ⟨v, spMap ψO ≫ C.fromSpecStalk c, ?_, ?_⟩
  · rw [← Category.assoc, ← hφ]
    congr 1
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  · have : spMap ψO (IsLocalRing.closedPoint v.O) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint ψO
    change C.fromSpecStalk c (spMap ψO (IsLocalRing.closedPoint v.O)) = c
    rw [this, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.Nef
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ScaleJet

variable {R : Type} [CommRing R]

theorem res_cst {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem appLE_cst {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

theorem app_cst {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (a : R) : (f.app U).hom (constFn q U a) = constFn q' (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE, appLE_cst q q' f hf]

def cMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : LB.Sec L) : LB.Sec L where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_cst, res_cst, s.compat, mul_left_comm]

theorem nonzeroLocus_cMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : LB.Sec L) : Out.nonzeroLocus (cMul q a s) = Out.nonzeroLocus s := by
  unfold Out.nonzeroLocus
  refine iSup_congr fun k => ?_
  have hu : IsUnit (constFn q (L.U k) a) := (ha.map _).map _
  show X.basicOpen (constFn q _ a * s.f k) = _
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hu]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem valR_cMul {A : Type} [CommRing A] {X : Scheme.{0}} (q : X ⟶ Sp R) (φ : R →+* A) (x : Sp A ⟶ X)
    (hx : x ≫ q = spMap φ) (U : X.Opens) (a : R) (f : Γ(X, U)) :
    valR x U (constFn q U a * f) = φ a * valR x U f := by
  unfold valR
  split_ifs with h
  · rw [map_mul, map_mul, appLE_cst q (spMap φ) x hx U ⊤ h]
    congr 1
    have h3 : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop :=
      (Scheme.Hom.app_eq_appLE (spMap φ) (U := ⊤)).symm
    have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
    have h2 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h1
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (((spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) = φ a
    rw [h3]
    refine h2.trans ?_
    simp
  · simp

section Twist

variable {A : Over (Sp R)} [GrpObj A] (L : LB A.left)

theorem twist_cMul {T : Over (Sp R)} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b]))
    (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) (c : R)
    (h : IsTwistPull A L ψ m hm a b α s s') :
    IsTwistPull A L ψ m hm a b α (cMul (T ⊗ A).hom c s) (cMul (T ⊗ A).hom c s') := by
  intro j
  have e := h j
  simp only [cMul]
  erw [RingHom.map_mul, res_cst, e, RingHom.map_mul, app_cst _ _ ψ.left (Over.w ψ), RingHom.map_mul, res_cst]
  exact mul_left_comm _ _ _

end Twist

end GlobalTheory.MBLow.ScaleJet

namespace GlobalTheory.MBLow.ScaleJet

theorem polAVSectionInverseImage_mulConstant {R : Type} [CommRing R] (P : PolAV (Sp R)) (T : Over (Sp R)) (s : P.L.Sec)
    (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (c : R) (h : IsPolAVSectionInverseImage P T s t) :
    IsPolAVSectionInverseImage P T (cMul P.A.hom c s) (cMul (T ⊗ P.A).hom c t) := by
  intro i hi
  have e := h i hi
  simp only [cMul]
  erw [e, RingHom.map_mul, appLE_cst P.A.hom (T ⊗ P.A).hom (snd T P.A).left (Over.w (snd T P.A))]

theorem scale_key : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (C : Type) [Field C] [CharZero C] (x : KeyIn C) (a : C), a ≠ 0 →
    ∃ (th' : x.P.L.Sec) (h' : _), a ^ 8 * (κ C ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ : C) = κ C x ∧
      ∀ (g : ℕ) (hg : x.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp C) ⟶ x.P.A)) (ϑ : I → C) (J : I → Fin g → C),
        ThJet x hg m pt ϑ J → ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ hg m pt (fun i => a * ϑ i)
          (fun i j => a * J i j) := by
  intro κ hκ C _ _ x a ha
  have hne : ∀ s : Sp C, ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus (cMul x.P.A.hom a x.th) := by
    intro s
    rw [nonzeroLocus_cMul _ ha.isUnit]
    exact x.th_ne s
  have hl : ∀ i, IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) C) i) x.v (x.v i) := by
    intro i
    have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) C) i = Pi.single i 1 := by
      ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this]
    have := x.P.isAb.comm
    exact (LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i
  refine ⟨cMul x.P.A.hom a x.th, hne, ?_, ?_⟩
  · have e := hκ C x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis (cMul x.P.A.hom a x.th) hne x.v x.basis a 1
      (fun i => rfl) hl
    simpa [Matrix.det_one] using e
  · rintro g hg m I pt ϑ J ⟨th, hon, U, t, i₀, c, hU, hi₀, hv⟩
    refine ⟨cMul (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom a th, polAVSectionInverseImage_mulConstant x.P _ x.th th a hon, U,
      fun i => cMul (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom a (t i), i₀, c, fun i => ⟨(hU i).1, ?_⟩, hi₀, fun i j => ?_⟩
    · obtain ⟨α, s₁, h1, h2, h3, h4⟩ := (hU i).2
      exact ⟨α, cMul _ a s₁, h1, h2, twist_cMul _ _ _ _ _ _ _ _ _ _ h3, twist_cMul _ _ _ _ _ _ _ _ _ _ h4⟩
    · have hx : epsLift (x.v (j.cast hg.symm)) ≫ (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom =
          spMap (algebraMap C (DualNumber C)) := Over.w _
      have e := valR_cMul _ _ _ hx _ a ((t i).f fun _ => i₀)
      refine e.trans ?_
      rw [hv i j]
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl] <;> ring

end GlobalTheory.MBLow.ScaleJet
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow.TrSec

variable {S : Scheme.{0}} (P : PolAV S)

lemma chart_le (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)).U j ≤ (snd (baseOver S) P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L _ j 0

def thSec (s : P.L.Sec) : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)) where
  f j := ReciprocityTheory.ChartRestriction.G.DVR.rs (chart_le P j) (((snd (baseOver S) P.A).left.app (P.L.U (j 0))).hom (s.f (j 0)))
  compat i j := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic (snd (baseOver S) P.A).left (chart_le P i) (chart_le P j)
      (s.f (i 0)) (s.f (j 0)) (P.L.g (i 0) (j 0)) (s.compat _ _) _ ?_
    simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
    rfl

lemma projectionPullbackSectionBaseProduct_isInverseImage (s : P.L.Sec) : IsPolAVSectionInverseImage P (baseOver S) s (thSec P s) := by
  intro i h
  rfl

lemma snd_inv (p : P.A.left) : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := by
  have e : (λ_ P.A).inv ≫ snd (baseOver S) P.A = 𝟙 P.A := (λ_ P.A).inv_hom_id
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
  rfl

lemma nonzero_thSec (s : P.L.Sec) (p : P.A.left) (hp : p ∈ nonzeroLocus s) :
    (λ_ P.A).inv.left.base p ∈ nonzeroLocus (thSec P s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, ?_⟩
  have hq : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := snd_inv P p
  show _ ∈ (baseOver S ⊗ P.A).left.basicOpen
    (((baseOver S ⊗ P.A).left.presheaf.map (homOfLE (chart_le P (fun _ => k))).op).hom
      (((snd (baseOver S) P.A).left.app (P.L.U k)).hom (s.f k)))
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
  refine ⟨?_, ?_⟩
  · show _ ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ (P.L.U k : Set P.A.left)
    rw [hq]; exact P.A.left.basicOpen_le _ hk
  · show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ P.A.left.basicOpen (s.f k)
    rw [hq]; exact hk

end GlobalTheory.MBLow.TrSec
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory

theorem encard_fibre_eq_encard_ringHom : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U →
    IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U),
    (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard =
      {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  intro k _ X Y p q π hπ U hU hV σ y hy
  have hmem : ∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z = y →
      z ∈ CxPts.ptsIn q σ (π ⁻¹ᵁ U) := by
    intro z hz
    have : PtsOver.map π hπ (spMap σ) z ∈ CxPts.ptsIn p σ U := hz ▸ hy
    exact this
  have hcomp : ∀ (z : CxPts q σ) (hz : PtsOver.map π hπ (spMap σ) z = y) (f : Γ(X, U)),
      CxPts.evHom (hmem z hz) ((π.app U).hom f) = CxPts.evHom hy f := by
    intro z hz f
    rw [← CxPts.ev_eq, ← CxPts.ev_eq, CxPts.ev_app π hπ U f z, hz]
  apply Set.encard_congr
  refine Equiv.ofBijective (fun z => ⟨CxPts.evHom (hmem z.1 z.2), RingHom.ext (hcomp z.1 z.2)⟩)
    ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩ ⟨w, hw⟩ h
    have h' : CxPts.evHom (hmem z hz) = CxPts.evHom (hmem w hw) := congrArg Subtype.val h
    refine Subtype.ext (Subtype.ext (ext_of_valR hV (hmem z hz) (hmem w hw) fun f => ?_))
    rw [valR_eq _ _ (hmem z hz), valR_eq _ _ (hmem w hw)]
    exact congrArg (fun φ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ => φ f) h'
  · rintro ⟨ψ, hψ⟩
    have hψ' : ∀ f, ψ ((π.app U).hom f) = CxPts.evHom hy f := fun f => by
      rw [← RingHom.comp_apply, hψ]
    have h₀ : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U) :=
      le_preimage_specMap_fromSpec hV (CommRingCat.ofHom ψ)
    have hv : valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) h₀ =
        CommRingCat.ofHom ψ :=
      valMap_specMap_fromSpec hV (CommRingCat.ofHom ψ) h₀
    have e : (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ≫ π = y.1 := by
      refine ext_of_valR hU h₀ hy fun f => ?_
      rw [valR_comp, valR_eq _ _ h₀, hv, valR_eq _ _ hy]
      exact hψ' f
    let z : CxPts q σ := ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, by
      rw [← hπ, ← Category.assoc, e, y.2]⟩
    have hz : PtsOver.map π hπ (spMap σ) z = y := Subtype.ext e
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    change (valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) (hmem z hz)).hom = ψ
    rw [hv]
    rfl

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem GlobalTheory.QLog.exists_int_log_of_isLie_p_smul : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  intro p _ O E _ _ _ hF G d c f l hf hl
  obtain ⟨s₁, hs₁, hl₁⟩ := (c.isLie_iff hF.inj f _).1 hl 1
  rw [pow_one] at hs₁
  have hdiv : ∀ (w : G.dual.omega) (φ : CartierDual O (G.A 1)), dUnit (R := O) φ = w.1 1 →
      (p : O) ∣ φ (c.ev 1 s₁) := by
    intro w φ hφ
    have h1 := hl₁ w φ hφ
    rw [pow_one, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (dvd_sub_right (dvd_mul_right _ _)).1 h1
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd p O G 1 (p : O) (c.ev 1 s₁) hdiv
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_integral_coboundary_divisible_of_quasiLog_defect p O E hF G d c f s₁ z hf hs₁ hz
  obtain ⟨hf0, hflin, -⟩ := hf
  choose b _ hb using hflin
  obtain ⟨g, hg0, hglin, hgcob⟩ := GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O E hF d c.μ c.isLaw (fun i => b i - lin t i)
  have hμ : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      c.isLaw.const i, map_zero]
  refine ⟨t, g, hgcob, ?_, ?_, ?_⟩
  · rw [map_sub, map_sub, hf0, hg0, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, ht0, map_zero]
    simp
  · intro i
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    have : lin (f - map (algebraMap O E) t - g) i = lin f i - algebraMap O E (lin t i) - lin g i := by
      simp [lin, coeff_map]
    rw [this, hb i, hglin i, map_sub, map_zero]
    simp
  · have hsub : f - map (algebraMap O E) t - g = (f - map (algebraMap O E) t) + (-1 : E) • g := by
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [hsub, formalCoboundary_add hμ, formalCoboundary_smul hμ, hgcob, smul_zero, add_zero]
    exact ht
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cocycle_cohomologous_of_de_rham_surjective : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), Function.Surjective (toH1O (X.hom ≫ 𝟙 _)) → ∀ u : Fn1 X, IsCoc (whole X) u → ∃ f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Cohom (whole X) u (fv f) := by
  first | exact @GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective | exact GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective | (intros; apply GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective <;> assumption)
end

section

alias GlobalTheory.T.cotVal_sub_eq_dUnit_of_d0_eq_sub :=
  GlobalTheory.PtExt.crystallineCocycleCotangentValue_sub_of_coboundary
end
