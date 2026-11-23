module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem ellPull_exists_oAct {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {g : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f g) {O : Type} [CommRing O] (o : OAct O G) :
    ∃ o' : OAct O G', ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (G' ⟶ G') := fun a => Over.homMk (hg.1.lift (g ≫ (o.act a).left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ (o.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G') a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ o.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩, ha⟩
  · have := o.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, o.one, Category.comp_id]
  · rw [← Category.id_comp (act (a * b)), pa, pa, ← Category.id_comp (act a), pa, o.mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act b)).symm
    rw [← Category.id_comp (act (a + b)), ← Category.id_comp (act a), ← Category.id_comp (act b), pa, pa, pa, o.add]
    exact MonObj.comp_mul _ _ _

theorem ellPull_prim {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {g : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f g) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (i : LBIso (L.pull g) L') {w : G ⟶ G} {w' : G' ⟶ G'} (hw : w'.left ≫ g = g ≫ w.left)
    (h : LBIso L (cubeLB G ![𝟙 G, w] L)) : LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk g hg.1.w
  have H₁ : LBIso (L.pull g) (cubeLB G' ![𝟙 G', w'] (L.pull g)) := by
    refine LBIso.chartPull (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L g U.left rfl)
      (chartPullLinComb L g _ _ _ U.left fun I => lamBC_psum_push hg _ _ U (fun k => ?_) I.down) h
    fin_cases k
    · refine Over.OverMorphism.ext ?_
      show 𝟙 _ ≫ g = g ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    · exact Over.OverMorphism.ext hw
  have hLg : (L.pull g).IsLB := DVR.linComb_isLB _ hL _ _
  exact LBIso.trans hL' hLg (DVR.linComb_isLB _ hL' _ _) i.symm
    (LBIso.trans hLg (DVR.linComb_isLB _ hLg _ _) (DVR.linComb_isLB _ hL' _ _) H₁
      (PowPrimitive.lbIso_linComb i _ _))

theorem exists_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (C' : Ell H R' (f ω)) (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ := by
  intro hB E _ _ _ H R _ ω C R' _ f
  obtain ⟨P', φ, hP⟩ := exists_isPolFibre hB f C.P
  obtain ⟨hdim, hg, hi⟩ := id hP
  obtain ⟨o', ho⟩ := ellPull_exists_oAct hg C.act
  have : IsCommMonObj P'.A := P'.isAb.comm
  have := C.P.smoothDim
  obtain ⟨v', hv', hv⟩ := exists_isLieBasis_baseChange R R' f C.P.A P'.A φ hg
    (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) 1 ![C.v] C.basis
  have ev : ![v' 0] = v' := by
    funext i
    fin_cases i
    rfl
  have hv0 : (v' 0).left ≫ φ = spMap (Chart.dualMapR f) ≫ C.v.left := hv 0
  refine ⟨⟨P', hdim.trans C.dim, o', v' 0, ev ▸ hv', ?_, fun a b hab => ?_,
    ellPull_prim hg C.P.isLB P'.isLB hi (ho _) C.prim⟩, φ, rfl, hP, hv0, ho⟩
  · have e : (fun i => f (![ω] i)) = ![f ω] := by
      funext i
      fin_cases i
      rfl
    rw [ev, ← e]
    refine (lieComb_baseChange R R' f C.P.A P'.A φ hg 1 ![C.v] _ ![ω] v' _ hv C.eig).1 ?_
    show ((v' 0).left ≫ (o'.act (wK H)).left) ≫ φ = _ ≫ C.v.left ≫ (C.act.act (wK H)).left
    rw [Category.assoc, ho, ← Category.assoc, hv0, Category.assoc]
  · have e1 : (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ = φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left := by
      show 𝟙 _ ≫ φ = φ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    exact lamEq_baseChange _ _ (spMap f) _ _ _ _ _ _ _ _ φ φ φ φ hg.1.w hg.1.w hg hg _ _ _ _ C.P.isLB C.P.isLB
      P'.isLB P'.isLB hi hi _ _ _ _ _ _ _ _ (ho a) e1 e1 (ho b) (C.adj a b hab)

end GlobalTheory.CM

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem isHolTo_comp_hom {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  have hfun : (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) :=
    funext fun b => (valAt'_comp _ φ U s).symm
  rw [hfun]
  exact h (φ ⁻¹ᵁ U) _

theorem exists_isExp_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (σ : R →+* ℂ) (T : PAT H (Sp R)) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap σ)) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (e' : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ T'.t.G)), IsExp T' (RingHom.id ℂ) D ty Pe e' → ∃ e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G), IsExp T σ D ty Pe e ∧ ∀ z, (e z).left = (e' z).left ≫ m.φ := by
  intro E _ _ _ H R _ σ T T' m D g ty Pe e' ⟨hP, hol, hadd, hon, hker, hlin, hw⟩
  have hL : LBIso T'.t.PP.L (T.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hT : (Over.mk (spMap (RingHom.id ℂ))).hom ≫ spMap σ = spMap σ := by
    show spMap (RingHom.id ℂ) ≫ spMap σ = spMap σ
    rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) (spMap σ) hT.symm
  refine ⟨fun z => p (e' z), ⟨hP, ?_, fun z w => (congrArg p (hadd z w)).trans (map_mul p _ _),
    p.surjective.comp hon, fun z => ?_, fun a z => ?_, fun k a b c hk hc => ?_⟩, fun z => hp _⟩
  · have h : (fun z => (p (e' z)).left) = fun z => (e' z).left ≫ m.φ := funext fun z => hp _
    exact h ▸ isHolTo_comp_hom hol m.φ
  · exact (map_eq_one_iff p p.injective).trans (hker z)
  · apply Over.OverMorphism.ext
    beta_reduce
    rw [Over.comp_left, hp, hp, hlin, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · have key : ∀ (y : Sp ℂ ⟶ Sp R) (_ : y = (Over.mk (spMap (RingHom.id ℂ))).hom ≫ spMap σ)
        (x₀ y₀ : Over.mk y ⟶ T.t.G) (x x' : Over.mk (spMap (RingHom.id ℂ)) ⟶ T'.t.G),
        x₀.left = x.left ≫ m.φ → y₀.left = x'.left ≫ m.φ →
        Out.WeilIs T'.t.G T'.t.PP.L k x x' (unitOn c) → Out.WeilIs T.t.G T.t.PP.L k x₀ y₀ (unitOn c) := by
      rintro y rfl x₀ y₀ x x' h₁ h₂ h₃
      exact (weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ T.t.PP.isLB T'.t.PP.isLB m.cart hL _ k x x' x₀ y₀ _
        h₁ h₂).1 h₃
    exact key _ hT.symm _ _ _ _ (hp _) (hp _) (hw k a b c hk hc)

end GlobalTheory.CM
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CM

namespace GlobalTheory.LamF

theorem exists_kronecker_logOm_re (E : Type) [Field E] [NumberField E] {d d' : ℕ} (h : d' = d) [Fact d.Prime]
    [NeZero d] (hd : d % 4 = 3) :
    ∃ (_ : NeZero d') (χ : DirichletCharacter ℂ d'), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm E χ).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) -
        (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) 1 /
          DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) 1).re := by
  subst h
  exact ⟨inferInstance, _, isKroneckerChar_quadraticChar hd, by
    rw [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]⟩

theorem exists_kronecker_logOm_eq : ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D,
    ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d),
      IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm := by
  intro D Q hp large₂
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd : D.host.d % 4 = 3 := by
    have := Q.H.d_mod
    rw [hp.1] at this
    omega
  obtain ⟨i, χ, hχ, e⟩ := exists_kronecker_logOm_re D.host.E hp.1 hd
  refine ⟨i, χ, hχ, e.trans ?_⟩
  have hv : 2 * Real.pi / rootDiscr D.host.E = Real.pi / D.host.v := by
    rw [Formalism.BasicNotions.Host.v, Formalism.BasicNotions.Host.rdE, rootDiscr_def, Int.cast_abs, one_div, div_div_eq_mul_div, mul_comm]
  rw [hv, SizeData₂.logOm, large₂.logDerivative_at_one_eq]
  rfl

end GlobalTheory.LamF
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.ThetaDegree

def IsPullOf {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (t : LB.Gen (P.L.pull (eSec P.A))) (θ : P.L.Sec) (y : KeyIn R) : Prop :=
  ∃ (ψ : y.P.A.left ⟶ P.A.left) (w : LB.Iso y.P.L (P.L.pull ψ)), y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap f) ψ ∧
    PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec y.P.A) (fun _ => eSec P.A) (fun _ => 1) y.rig t (spMap f) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ y.P.A.left) (z : Z) j k, ψ (r z) ∈ P.L.U j → r z ∈ y.P.L.U k →
      gs (r ≫ ψ) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (y.th.f k)

theorem exists_isPullOf {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (hg : 1 ≤ P.g) {t : LB.Gen (P.L.pull (eSec P.A))} (ht : t.IsGen) (θ : P.L.Sec)
    (hθ : ∀ s : Sp R, ∃ z, P.A.hom z = spMap f s ∧ z ∈ Out.nonzeroLocus θ) : ∃ y : KeyIn R, IsPullOf f P t θ y := by
  letI : (Over.pullback (spMap f)).Monoidal :=
    (Over.instBraidedPullback (f := spMap f)).toMonoidal
  letI : GrpObj ((Over.pullback (spMap f)).obj P.A) :=
    CategoryTheory.Functor.grpObjObj (F := Over.pullback (spMap f)) (G := P.A)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  have h : IsGrpPullback ((Over.pullback (spMap f)).obj P.A) P.A (spMap f) φ :=
    isGrpPullback_pullback P.A (spMap f)
  have hL' := pull_isLB P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R) :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he P.L t).IsGen :=
    Out.LBxP.isGen_pullAlong P.L φ (spMap f) (fun _ : PUnit => eSec P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) t ht
  obtain ⟨th', hth'⟩ := sec_pull_down hw P.isLB hL' θ
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis P'.A P'.smoothDim
  refine ⟨⟨P', hg, _, hr, th', fun s => ?_, v, hv⟩, φ, idIso _, rfl, h, hw,
    (maps_iff (idIso _) (fun _ => eSec P'.A) (fun _ => eSec P.A) _ _ t (spMap f) _ (rigPull_le φ (spMap f) he P.L)
      (fun _ => rfl)).1 (fun p => hr p.1 p.2), hth'⟩
  obtain ⟨z, hz, hz'⟩ := hθ s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (θ.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem IsPullOf.exists_keyPB {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [CommRing R'] {f : O →+* R}
    {g : R →+* R'} {P : Out.PolAV (Sp O)} {t : LB.Gen (P.L.pull (eSec P.A))} {θ : P.L.Sec} {y : KeyIn R} {x : KeyIn R'}
    (hy : IsPullOf f P t θ y) (hx : IsPullOf (g.comp f) P t θ x) :
    ∃ v' hv', KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv'⟩ y g := by
  obtain ⟨ψ, w, hg, hc, hw, hr, hs⟩ := hy
  obtain ⟨φ'', w'', hg'', hc'', hw'', hr'', hs''⟩ := hx
  have hsp : spMap (g.comp f) = spMap g ≫ spMap f := (spMap_comp_spMap f g).symm
  obtain ⟨φ, rfl, hw0⟩ : ∃ φ : x.P.A.left ⟶ y.P.A.left, φ ≫ ψ = φ'' ∧ φ ≫ y.P.A.hom = x.P.A.hom ≫ spMap g :=
    ⟨hc.1.lift φ'' (x.P.A.hom ≫ spMap g) (by rw [hc''.1.w, Category.assoc, hsp]), hc.1.lift_fst _ _ _,
      hc.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap g) φ := hc.cancel (hc''.congr hsp rfl) hw0
  have he : eSec x.P.A ≫ φ = spMap g ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' hw hw'' y.P.isLB x.P.isLB
  rw [hsp] at hr''
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR g) ≫ (y.v i).left) ≫ y.P.A.hom = (epsR R').hom ≫ spMap g := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR R' ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR g) ≫ (y.v i).left := fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange g h y.basis hv'
  have hg' : x.P.g = y.P.g := hg''.trans hg.symm
  refine ⟨_, hb hg', φ, he, w', hg', Chart.dualMapR g, h, (isGen_iff _).2 (T.pgen_cancel P.isLB hw hw''),
    (maps_iff w' _ (fun _ => eSec y.P.A) _ x.rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2
      (T.pmaps_cancel P.isLB (fun _ => he) hr hr''),
    KeyPow.appLE_eq_of_stalk _ y.th x.th fun z i k hi hk => ?_, fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨j, hj⟩ := exists_chart P.isLB (ψ (φ z))
    have a := hs _ (𝟙 _ ≫ φ) z j i hj hi
    have b := hs'' _ (𝟙 _) z j k hj hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_sec_generic (hT : Out.SecTwistSt) {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (P : Out.PolAV (Sp O)) {X : Scheme.{0}} {φ : X ⟶ P.A.left} {q : X ⟶ Sp K}
    (hp : IsPullback φ q P.A.hom (spMap (algebraMap O K))) : ∃ (θ : P.L.Sec) (z : X), φ z ∈ Out.nonzeroLocus θ := by
  have := P.isAb.smooth
  have := P.isAb.proper
  obtain ⟨s, hs⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨d, hd, θ, hθ⟩ := SecSpread.exists_spread hp P.isLB s
  obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hk' : φ z ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  have hu : IsUnit (gs φ z _ (θ.f (k PUnit.unit))) := by
    rw [hθ _ z hk']
    exact (SecSpread.isUnit_cst hp.w z hd).mul u
  rw [gs_stalkMap φ z _ hk', isUnit_map_iff] at hu
  exact ⟨θ, z, (mem_nonzeroLocus _ _).2 ⟨_, hk', hu⟩⟩

variable {K : Type} [Field K] [NumberField K]

theorem exists_scalar (hT : Out.SecTwistSt) (P : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ P.A.left)
    (w : LB.Iso x.P.L (P.L.pull φ)) (hg : x.P.g = P.g)
    (hφ : IsGrpPullback x.P.A P.A (spMap (algebraMap (𝓞 K) K)) φ) (hw : w.IsGen) :
    ∃ a : K, a ≠ 0 ∧ {𝔭 | ¬ ∃ M, KeyPow.IsLocalModel x 𝔭 a M}.Finite := by
  have := P.isAb.smooth
  obtain ⟨θ, z₀, hz₀⟩ := exists_sec_generic hT P hφ.1
  obtain ⟨t, ht⟩ := P.rigid
  obtain ⟨w', g', m'⟩ := KeyPow.exists_rescale P.isLB x.P.isLB ((isGen_iff _).1 hw) (p := x.P.A.hom) (Over.w η[x.P.A])
    (PolBaseChange.eSec_comm hφ) x.rig_gen ht
  obtain ⟨th', hth'⟩ := sec_pull_down g' P.isLB x.P.isLB θ
  have hne : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th' := fun s => by
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz₀
    obtain ⟨k, hk⟩ := exists_chart x.P.isLB z₀
    refine ⟨z₀, Subsingleton.elim (α := PrimeSpectrum K) _ _, (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ z₀ _ (θ.f j)) := by rw [gs_stalkMap φ z₀ _ hj]; exact u.map _
    have e := hth' _ (𝟙 _) z₀ j k hj hk
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  let x' : KeyIn K := ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hne, x.v, x.basis⟩
  have hx' : IsPullOf (algebraMap (𝓞 K) K) P t θ x' := ⟨φ, w', hg, hφ, g', m', hth'⟩
  obtain ⟨a, -, ha, -⟩ := KeyPow.exists_scalar_matrix hT x.P x.th th' x.th_ne x.basis x.basis
  obtain ⟨_, ⟨d, rfl⟩, hd, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_image_of_mem P.A.hom hz₀) (P.A.hom.isOpenMap _ (Out.nonzeroLocus θ).isOpen)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hd (Ideal.zero_mem _)
  refine ⟨a, ?_, (Ideal.finite_factors (I := Ideal.span {d}) (by simpa using hd0)).subset fun 𝔭 h𝔭 => ?_⟩
  · rintro rfl
    obtain ⟨z, -, hz⟩ := hne (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  by_contra hn
  refine h𝔭 ?_
  have hv : 𝔭.valuation K (algebraMap (𝓞 K) K d) = 1 := by
    refine (𝔭.valuation_le_one d).antisymm (not_lt.1 fun h => hn ?_)
    exact (𝔭.valuation_lt_one_iff_dvd d).1 h
  let R := (𝔭.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => 𝔭.valuation_le_one r
  have hu : IsUnit (f d) := (Valuation.integer.integers (𝔭.valuation K)).isUnit_iff_valuation_eq_one.2 hv
  obtain ⟨y, hy⟩ := exists_isPullOf f P (hg ▸ x.g_pos) ht θ fun s => by
    have hs : spMap f s ∈ (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum (𝓞 K))) := fun h =>
      s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f d ∈ s.asIdeal from h) hu)
    obtain ⟨z, h₁, h₂⟩ := hsub hs
    exact ⟨z, h₂, h₁⟩
  obtain ⟨v', hv', hPB⟩ := hy.exists_keyPB (g := algebraMap R K) (x := x') hx'
  choose M hM using fun i => (x.basis.2 _ (hv'.1 i)).exists
  exact ⟨M, R, _, inferInstance, inferInstance, _,
    inferInstanceAs (IsFractionRing (𝔭.valuation K).valuationSubring K), y, th', hne, v', hv', fun r => r.2, ha, hM, hPB⟩

theorem exists_isThetaDeg : Out.SecTwistSt → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K]
    (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth), ∃ δ : ℝ, IsThetaDeg (F.key hg rig hr th hth) δ := by
  intro hT hU K _ _ P F hg rig hr th hth
  classical
  obtain ⟨e, hφ, hL⟩ := F.fib
  obtain ⟨w, hw⟩ := LBIso.symm hL
  let x := F.key hg rig hr th hth
  obtain ⟨oa, od, hloc⟩ := KeyPow.exists_isLocalModel_of_integral hT K P x F.φ w e hφ hw
  obtain ⟨a, ha, hfin⟩ := exists_scalar hT P x F.φ w e hφ hw
  obtain ⟨nth, nη, hn⟩ := KeyPow.exists_archNorms hU x
  have hv : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.valuation K a = WithZero.exp (- -WithZero.log (𝔭.valuation K a)) :=
    fun 𝔭 => by rw [neg_neg, WithZero.exp_log (by simpa using ha)]
  refine ⟨_, fun 𝔭 => if ∃ M, KeyPow.IsLocalModel x 𝔭 a M then -WithZero.log (𝔭.valuation K a) else oa 𝔭, nth,
    fun 𝔭 => ?_, fun σ => ?_, (hfin.union (KeyPow.sum_log_norm_eq_finsum ha _ hv).1).subset fun 𝔭 h => ?_, rfl⟩
  · by_cases h : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · obtain ⟨M, hM⟩ := id h
      exact ⟨a, M, hM, by beta_reduce; rw [if_pos h]; exact hv 𝔭⟩
    · obtain ⟨a', M, hM, h₁, -⟩ := hloc 𝔭
      exact ⟨a', M, hM, by beta_reduce; rw [if_neg h]; exact h₁⟩
  · obtain ⟨x', h₁, h₂⟩ := hn σ
    exact ⟨x', _, h₁, h₂⟩
  · by_cases h' : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · exact Or.inr (by simpa only [Function.mem_support, if_pos h'] using h)
    · exact Or.inl h'

end GlobalTheory.ThetaDegree

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_of_cmTriple_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S) (t' : SAB H S') (m : SABMap t' T.t f), (∃ T' : PAT H S', T'.t = t' ∧ T'.g = T.g) ∧ LBIso (T.t.PP.L.pull m.φ) t'.PP.L := by
  first | exact @GlobalTheory.CM.PAT.exists_of_sabMap | exact GlobalTheory.CM.PAT.exists_of_sabMap | (intros; apply GlobalTheory.CM.PAT.exists_of_sabMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.isIso_of_surjective_principalPairing : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom Φ → Out.KTriv A L → LamEq M Φ Φ L (𝟙 A) (𝟙 A) → Surjective Φ.left → IsIso Φ := by
  first | exact @GlobalTheory.CM.PairingIso.isIso_of_lamEq | exact GlobalTheory.CM.PairingIso.isIso_of_lamEq | (intros; apply GlobalTheory.CM.PairingIso.isIso_of_lamEq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.cmCurve_lie_character_of_adjoinGenerator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω), ∃ τ₀ : OK H →+* R, τ₀ (wK H) = ω ∧ ∀ c, IsLieComb ![τ₀ c] ![C.v] (C.v ≫ C.act.act c) := by
  first | exact @GlobalTheory.CM.LieChar.ell_char | exact GlobalTheory.CM.LieChar.ell_char | (intros; apply GlobalTheory.CM.LieChar.ell_char <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.isCubeLBPairingIso_baseChange : ∀ (S S' : Scheme.{0}) (s : S' ⟶ S) (X Y A B : Over S) (X' Y' A' B' : Over S') [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] (x : X'.left ⟶ X.left) (y : Y'.left ⟶ Y.left) (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left),
  x ≫ X.hom = X'.hom ≫ s → y ≫ Y.hom = Y'.hom ≫ s → IsGrpPullback A' A s a → IsGrpPullback B' B s b → ∀ (L : LB A.left) (M : LB B.left) (L' : LB A'.left) (M' : LB B'.left), L.IsLB → M.IsLB → L'.IsLB → M'.IsLB → LBIso (L.pull a) L' → LBIso (M.pull b) M' →
  ∀ (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) (f₁' : X' ⟶ A') (f₂' : Y' ⟶ A') (g₁' : X' ⟶ B') (g₂' : Y' ⟶ B'),
  f₁'.left ≫ a = x ≫ f₁.left → f₂'.left ≫ a = y ≫ f₂.left → g₁'.left ≫ b = x ≫ g₁.left → g₂'.left ≫ b = y ≫ g₂.left → LamEq L f₁ f₂ M g₁ g₂ → LamEq L' f₁' f₂' M' g₁' g₂' := by
  first | exact @GlobalTheory.CM.lamEq_baseChange | exact GlobalTheory.CM.lamEq_baseChange | (intros; apply GlobalTheory.CM.lamEq_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.nonempty_polAVGenericFibreWithLieBasis : Out.PolBaseChangeSt → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))), Nonempty (GenFib P) := by
  first | exact @GlobalTheory.CM.GenFib.nonempty_of_baseChange | exact GlobalTheory.CM.GenFib.nonempty_of_baseChange | (intros; apply GlobalTheory.CM.GenFib.nonempty_of_baseChange <;> assumption)
end
