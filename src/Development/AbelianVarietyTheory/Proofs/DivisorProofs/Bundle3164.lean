module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem Tower.same : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ 𝔗 : Tower X₁ act, GlobalTheory.Poinc.Same X₁.ρ act 𝔗.X₂.ρ 𝔗.act₂ 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  intro g n F W Z i X₁ act hact 𝔗
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let P₀ : PolAV (Sp 𝔗.X₂.Ω₁) :=
    { A := (Over.pullback f₂).obj 𝔗.X₂.ρ.P.A
      isAb := TLinPf.isAb_pullback f₂ _ 𝔗.X₂.ρ.P.isAb
      g := 𝔗.X₂.ρ.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂).1 𝔗.X₂.ρ.P.smoothDim
      L := 𝔗.X₂.ρ.P.L.pull (pullback.fst 𝔗.X₂.ρ.P.A.hom f₂)
      isLB := pull_isLB 𝔗.X₂.ρ.P.isLB _
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.sym
      ample := by
        haveI := 𝔗.X₂.ρ.P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback 𝔗.X₂.ρ.P.isLB 𝔗.X₂.ρ.P.ample
          (IsPullback.of_hasPullback 𝔗.X₂.ρ.P.A.hom f₂)
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB 𝔗.X₂.ρ.P.isLB (pullback.fst 𝔗.X₂.ρ.P.A.hom f₂))
        exact kTriv_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) ((isGen_iff w).1 hw) 𝔗.X₂.ρ.P.ktriv }
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun E => (Over.pullback f₂).map (𝔗.act₂ E), ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    have h1 : ((Over.pullback f₂).map (𝔗.act₂ E)).left ≫ a' = a' ≫ (𝔗.act₂ E).left :=
      pullback.lift_fst _ _ _
    refine ⟨?_, h1⟩
    have h2 : (a' ≫ (𝔗.act₂ E).left) ≫ 𝔗.φ = a' ≫ 𝔗.φ ≫ (act E).left := by
      rw [Category.assoc, 𝔗.act_eq]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) h1).trans h2)
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _
end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.pulled_lowObj_grp_ident : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] (ev : V →+* K), ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ev) π₁ → ∃ θ : o'.t.G.left ⟶ B'.left, IsGrpPullback o'.t.G B' (𝟙 _) θ ∧ LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) ∧ (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hDiv K _ ev o' m₁ B' _ π₁ hπ
  obtain ⟨g, hD, -, hxe, -⟩ := hDiv
  have hsp : spMap ev ≫ specOf iw = spMap (ev.comp iw) := by
    simp [spMap, specOf, ← Spec.map_comp]
  have hii : IsGrpPullback Q.P.A L.D.P.A (specOf iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    GlobalTheory.UnifPullCompare.isGrpPullback_of_bc hD.e hD.e_hom
  have h₂ : IsGrpPullback B' L.D.P.A (spMap (ev.comp iw))
      (π₁ ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    (IsGrpPullback.comp hπ hii).congr hsp rfl
  have h₁ : IsGrpPullback o'.t.G L.D.P.A (spMap (ev.comp iw)) (m₁.toSABMap.φ ≫ L.φB) :=
    (IsGrpPullback.comp m₁.cart L.ab.1).congr (Category.comp_id _) rfl
  obtain ⟨θe, hθm, hθ⟩ := grpPullback_iso h₁ h₂
  refine ⟨θe.hom.left, ?_, ?_, ?_⟩
  · haveI := hθm
    exact isGrpPullback_of_iso θe
  · have A : LBIso o'.t.PP.L (L.o.t.PP.L.pull m₁.toSABMap.φ) := GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m₁.toSABMap
    have B : LBIso (L.o.t.PP.L.pull m₁.toSABMap.φ) (L.D.P.L.pull (m₁.toSABMap.φ ≫ L.φB)) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull L.ab.2.2 _ rfl
    have C : LBIso Q.P.L (L.D.P.L.pull (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw))) :=
      ⟨hD.w, hD.w_gen⟩
    have C' : LBIso (Q.P.L.pull (θe.hom.left ≫ π₁)) (L.D.P.L.pull (m₁.toSABMap.φ ≫ L.φB)) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull C _ (by rw [← hθ]; simp only [Category.assoc])
    exact LBIso.trans o'.t.PP.isLB (pull_isLB L.D.P.isLB _) (pull_isLB Q.P.isLB _)
      (LBIso.trans o'.t.PP.isLB (pull_isLB L.o.t.PP.isLB _) (pull_isLB L.D.P.isLB _) A B) C'.symm
  · intro x a hx hc
    apply hii.1.hom_ext
    · have hcp : (Q.c a).left ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
          specOf iw ≫ (L.D.c (l.M' • e a)).left := by
        have := hD.c_pr a
        rw [hxe a] at this
        exact this
      simp only [Category.assoc]
      rw [hθ, hc, hcp, ← Category.assoc, hsp]
    · have hq : (Q.c a).left ≫ Q.P.A.hom = 𝟙 _ := Over.w (Q.c a)
      have hB : θe.hom.left ≫ B'.hom = o'.t.G.hom := Over.w θe.hom
      simp only [Category.assoc]
      rw [hπ.1.w, ← Category.assoc θe.hom.left, hB, ← Category.assoc x, hx, hq]
      simp
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.MulDeg

variable {R : Type} [CommRing R] [IsDomain R]

def tau3 (D : DegPre R) (s a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi s) (LB.invGen D.P.L _ _ (D.psi a)))
      (LB.invGen D.P.L _ _ (D.psi b)))
    (LB.invGen D.P.L _ _ D.rigK)

theorem corr_even_degenerationData_negPoint (D : DegPre R) (h : D.PsiEven) (a m : D.X) (hm : m = -a) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi m) (LB.pullGen D.P.L _ _ D.sym (D.xK a))) (D.psi a) := by
  subst hm
  exact h a

theorem corr_bimultiplicative_degenerationData_sums (D : DegPre R) (h : D.TauBimult) (a a' b s t u v : D.X) (hs : s = a + a') (ht : t = a + a' + b)
    (hu : u = a + b) (hv : v = a' + b) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (tau3 D t s b)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)))
      (LB.mulGen D.P.L _ _ _ _ (tau3 D u a b) (tau3 D v a' b)) := by
  subst hs ht hu hv
  exact h a a' b

theorem corr_balanced_degenerationData_rosati (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (p q : D.X → D.X) (h : D.TauBal f g p q)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (h1 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (y y' a a' s t : D.X) (ha : a = p y) (ha' : a' = q y') (hs : s = p y + y') (ht : t = y + q y') :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (tau3 D s a y') (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (tau3 D t y a') := by
  subst ha ha' hs ht
  exact h u hu h1 y y'

variable {O : Type} [CommRing O] [StarRing O]

local instance modMul (D : DegPre R) [h : Module O D.X] (n : ℕ) : Module O (mulDeg D n).X := h

def mulAct (D : DegPre R) [Module O D.X] (oa : D.OAct O) (n : ℕ) : (mulDeg D n).OAct O where
  onB := oa.onB
  c_lin := fun a (y : D.X) => by
    show D.c (n • (a • y)) = D.c (n • y) ≫ oa.onB.act a
    rw [smul_comm n a y, oa.c_lin]
  tau_bal := fun a u hu h1 (y y' : D.X) =>
    corr_balanced_degenerationData_rosati D _ _ _ _ (oa.tau_bal a) u hu h1 (n • y) (n • y') (n • (a • y)) (n • (star a • y'))
      (n • (a • y + y')) (n • (y + star a • y')) (smul_comm n a y) (smul_comm n (star a) y')
      (by rw [nsmul_add, smul_comm n a y]) (by rw [nsmul_add, smul_comm n (star a) y'])

theorem corr_polarisationElement_degenerationData (D : DegPre R) [Module O D.X] (oa : D.OAct O) (w0 : O)
    (u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left, (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left]
      ![1, -2, -1, 2]))
    (h : ∀ y, LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau y (w0 • y)) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)) (y s b : D.X) (hb : b = w0 • y) (hs : s = y + w0 • y) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (tau3 D s y b) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK) := by
  subst hb hs
  exact h y

theorem mulDeg_laws : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O) (n : ℕ), D.PsiEven → D.TauBimult → TraceFormTwistIso D oa w0 → (∀ y, PsiUnitOn D y Set.univ) → letI : Module O (mulDeg D n).X := ‹Module O D.X›; (mulDeg D n).PsiEven ∧ (mulDeg D n).TauBimult ∧ (∀ y, PsiUnitOn (mulDeg D n) y Set.univ) ∧ ∃ oa' : (mulDeg D n).OAct O, oa'.onB = oa.onB ∧ TraceFormTwistIso (mulDeg D n) oa' w0 := by
  intro R _ _ D O _ _ _ oa w0 n he hb hw hg
  refine ⟨fun (a : D.X) => corr_even_degenerationData_negPoint D he (n • a) (n • (-a)) (neg_nsmul a n),
    fun (a a' b : D.X) => corr_bimultiplicative_degenerationData_sums D hb (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
      (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _),
    fun (y : D.X) => hg (n • y), mulAct D oa n, rfl, ?_⟩
  obtain ⟨u, hu, h1, h⟩ := hw
  exact ⟨u, hu, h1, fun (y : D.X) => corr_polarisationElement_degenerationData D oa w0 u h (n • y) (n • (y + w0 • y)) (n • (w0 • y)) (smul_comm n w0 y)
    (by rw [nsmul_add, smul_comm n w0 y])⟩

end GlobalTheory.UCanon.MulDeg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem Tower.map_mem_O (𝔗 : Tower X₁ act) {w : 𝔗.X₂.M.Z} {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p w)) :
    algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x ∈ 𝔗.X₂.M.O w := by
  obtain ⟨U, f, hz, rfl⟩ := hx
  refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, hz, ?_⟩
  refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
  rw [𝔗.p_pt]
  exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hz⟩) f

theorem Tower.stalkHom_stalkMap (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.exists_germ_eq x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz]
  refine (RatModel.stalkHom_germ (U := 𝔗.p ⁻¹ᵁ U) hz _).trans ?_
  refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
  rw [𝔗.p_pt]
  exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hz⟩) f

theorem Tower.regAt : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → RegAt 𝔗.X₂ z₂ ev₂ := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ hio hext hreg
  subst hz
  have key : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap z₂ x)
  let fm : FractionRing V →+* FractionRing V' :=
    IsLocalization.map (M := nonZeroDivisors V) (S := FractionRing V) (FractionRing V') io
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hio)
  have e1 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg (fun φ : _ →+* V' => φ x) key
  have e2 : jK V' ≫ spMap io = spMap fm ≫ jK V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    show algebraMap V' (FractionRing V') (io x) = fm (algebraMap V (FractionRing V) x)
    exact (IsLocalization.map_eq (M := nonZeroDivisors V) (S := FractionRing V) (T := nonZeroDivisors V')
      (Q := FractionRing V') (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hio) x).symm
  have hm : jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂ ≫ 𝔗.p =
      spMap fm ≫ jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e1, Category.assoc,
      ← Category.assoc (jK V'), e2, Category.assoc]
  have hpt : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    refine (Scheme.Hom.comp_apply _ 𝔗.p _).symm.trans ?_
    rw [Category.assoc, Category.assoc, hm]
    refine (Scheme.Hom.comp_apply (spMap fm) _ _).trans (congrArg _ ?_)
    exact Spec_closedPoint
  intro a ha
  set P₂ := (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))
  haveI := 𝔗.X₂.normal.isIntegrallyClosed_stalk P₂
  haveI : IsIntegrallyClosed (𝔗.X₂.M.O P₂) := IsIntegrallyClosed.of_equiv (𝔗.X₂.M.stalkEquiv P₂)
  have hmem : ∀ c : X₁.S.R, ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) c ∈ 𝔗.X₂.M.O P₂ := fun c =>
    𝔗.map_mem_O (by rw [hpt]; exact hreg c.1 c.2)
  let q : X₁.S.R →+* 𝔗.X₂.M.O P₂ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom).codRestrict _ hmem
  obtain ⟨p, hmon, hp⟩ := 𝔗.om_fin.to_isIntegral ⟨a, ha⟩
  have hq : (algebraMap (𝔗.X₂.M.O P₂) 𝔗.X₂.Ω₁).comp q = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om :=
    RingHom.ext fun c => (𝔗.om_eq c).symm
  have hia : IsIntegral (𝔗.X₂.M.O P₂) a := by
    refine ⟨p.map q, hmon.map q, ?_⟩
    rw [Polynomial.eval₂_map, hq]
    have := Polynomial.hom_eval₂ p 𝔗.om 𝔗.X₂.S.R.val.toRingHom ⟨a, ha⟩
    rw [hp, map_zero] at this
    exact this.symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hia
  rw [← hy]
  exact y.2

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.GalVal

open GlobalTheory.Points GlobalTheory.ZH

theorem valR_spMap_fromSpecStalk {X : Scheme.{0}} {x : X} {C : Type} [CommRing C] (ψ : X.presheaf.stalk x →+* C)
    {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (spMap ψ ≫ X.fromSpecStalk x) U a = ψ (X.presheaf.germ U x hU a) := by
  have h : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  refine (valR_appLE (spMap ψ) (X.fromSpecStalk x) h (le_preimage_top _) a).symm.trans ?_
  rw [e]
  exact valR_specMap (CommRingCat.ofHom ψ) _

theorem jK_spMap {V' : Type} [CommRing V'] [IsDomain V'] {X : Scheme.{0}} (z : X) (ev : X.presheaf.stalk z →+* V') :
    jK V' ≫ spMap ev = spMap ((algebraMap V' (FractionRing V')).comp ev) := by
  rw [← Spec.map_comp]; rfl

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem specializes_jK {V' : Type} [CommRing V'] [IsDomain V'] {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V')
    (w : Sp (FractionRing V')) : (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ⤳ z := by
  have : (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem val_stalkHom {V' : Type} [CommRing V'] [IsDomain V'] {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V')
    (x : M.Z.presheaf.stalk z) :
    M.val (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) (M.stalkHom z x) = algebraMap V' (FractionRing V') (ev x) := by
  obtain ⟨U, hz, f, rfl⟩ := M.Z.presheaf.germ_exist x
  have hr : Set.range (jK V' ≫ spMap ev ≫ M.Z.fromSpecStalk z) ⊆ U := by
    rintro _ ⟨w, rfl⟩
    exact (specializes_jK ev w).mem_open U.isOpen hz
  rw [RatModel.val_eq hr (RatModel.stalkHom_germ hz f).symm]
  show valR _ U f = _
  rw [← Category.assoc, jK_spMap, valR_spMap_fromSpecStalk _ hz]
  rfl

end GlobalTheory.Poinc.Sep.GalVal

namespace GlobalTheory.Poinc.Sep.GalVal
open GlobalTheory.Points GlobalTheory.ZH
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem exists_mul_eq_stalkHom {P z : M.Z} (hs : P ⤳ z) {a : Ω} (ha : a ∈ M.O P) :
    ∃ x d : M.Z.presheaf.stalk z, a * M.stalkHom z d = M.stalkHom z x ∧
      ∃ hd : M.stalkHom z d ∈ M.O P, IsUnit (⟨_, hd⟩ : M.O P) := by
  obtain ⟨U, f, hPU, rfl⟩ := ha
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  have hPV : P ∈ V := hs.mem_open V.isOpen hzV
  obtain ⟨g, hgU, hPg⟩ := hV.exists_basicOpen_le (V := U) ⟨P, hPU⟩ hPV
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨P, hPg⟩
  have hne : (V : Set M.Z).Nonempty := ⟨z, hzV⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) hb
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, ← map_pow, RatModel.res_apply,
    RatModel.res_apply] at h1
  refine ⟨M.Z.presheaf.germ V z hzV b, M.Z.presheaf.germ V z hzV (g ^ n), ?_, ?_⟩
  · rw [RatModel.stalkHom_germ, RatModel.stalkHom_germ]
    exact h1
  · rw [RatModel.stalkHom_germ]
    refine ⟨RatModel.valF_mem_O hPV _, (RatModel.isUnit_valF_iff hPV _).2 ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    · rw [Scheme.basicOpen_pow _ _ hn]; exact hPg
end GlobalTheory.Poinc.Sep.GalVal

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Points GlobalTheory.ZH GalVal

theorem val_galois_conj : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → RegAt 𝔗.X₂ z₂ ev₂ → RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by
  intro g n F W Z i X₁ act 𝔗 z₂ V' _ _ ev₂ ev₂' σ h1 h2 hr hr' a
  have ha := hr' a a.2
  obtain ⟨x, d, hxd, hd, hu⟩ := exists_mul_eq_stalkHom (specializes_jK ev₂' _) ha
  obtain ⟨x', hx'⟩ := h2 x
  obtain ⟨d', hd'⟩ := h2 d
  have ex := h1 x x' hx'
  have ed := h1 d d' hd'
  have hsp' := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have hsp := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have e1 := RatModel.val_mul hsp' ha hd
  rw [hxd, val_stalkHom, val_stalkHom] at e1
  have hne := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ _) ⟨_, hd⟩).2 hu
  rw [val_stalkHom] at hne
  have hb := hr _ (𝔗.sR σ a).2
  have hd'' := RatModel.O_le_of_specializes (specializes_jK ev₂ (IsLocalRing.closedPoint _))
    (𝔗.X₂.M.stalkEquiv z₂ d').2
  have e2 := RatModel.val_mul hsp hb hd''
  have key : σ (a : 𝔗.X₂.Ω₁) * 𝔗.X₂.M.stalkHom z₂ d' = 𝔗.X₂.M.stalkHom z₂ x' := by
    rw [hd', hx', ← map_mul, hxd]
  rw [RatModel.coe_stalkEquiv, 𝔗.sR_eq, key, val_stalkHom, val_stalkHom, ← ed, ← ex] at e2
  rw [𝔗.sR_eq]
  exact mul_right_cancel₀ hne (e1.symm.trans e2)

end GlobalTheory.Poinc.Sep
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_ample_pos : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → IsAmpleCls d → ∀ f : A ⟶ B, f ≠ 0 → 0 < inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  intro K _ A B n hdim c d hc hd f hf
  obtain ⟨m, M, hM, s, hm, hcls, hne, horig⟩ := GlobalTheory.T.exists_section_pullbackAmple_vanishing_origin K A B f d hd hf
  have htop : Out.nonzeroLocus s ≠ ⊤ := by
    intro h
    apply horig
    rw [h]
    trivial
  have hpos := GlobalTheory.T.effectiveDivisor_pos_degree_ampleClass K A n hdim c hc M hM s hne htop
  obtain ⟨⟨Φ, hΦ⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hdim])
  set x := CechPic.pull f.hom.left d
  have hcons : (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left)
      = Function.update (Fin.cons x (fun _ : Fin n => c)) 0 ((m : ℤ) • x) := by
    rw [hcls]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [natCast_zsmul]
    · simp [Function.update, Fin.succ_ne_zero]
  rw [← hΦ, hcons, Φ.map_update_smul, Fin.update_cons_zero, smul_eq_mul] at hpos
  rw [← hΦ]
  exact pos_of_mul_pos_right hpos (by simpa using Int.ofNat_nonneg m)

end GlobalTheory.AV.AbVar
end
