module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsObjectWithThetaPointOfDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle198
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_object_with_thetaPoint_of_degenerationSeries : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n j : ℕ), n.Prime → Odd n → IsUnit (n : O') → ¬ n ∣ H.d → 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  first | exact @GlobalTheory.Ex.OneLevel.exists_full_theta | exact GlobalTheory.Ex.OneLevel.exists_full_theta | (intros; apply GlobalTheory.Ex.OneLevel.exists_full_theta <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.ModelTate

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_level_down {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) (n m : ℕ) (p : QkPt D F (n * m)) :
    ∃ q : QkPt D F n, q.y = p.y ∧ GtPtF.IsNsmul m p.g q.g :=
  ⟨TorusExt.qkMk hB p.y (m • p.g) (by rw [← mul_nsmul', TorusExt.qk_nsmul hB p]), rfl,
    (TorusExt.isNsmul_iff_eq _ _ _).2 rfl⟩

theorem weilIs_of_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G' L' k x y c) : WeilIs G L k x₀ y₀ c := by
  subst hg
  exact (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).1 h

theorem exists_tateIsoQ_of_model : GlobalTheory.UT.LL → BrGtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (N' : NumD C) (_ : NumOf M.P.D.toPre C N'), ∃ I : TateIsoQ D M.P.D.toPre M.P.oD C, I.ζ = o.I.ζ ∧ ∀ k, 0 < k → ∀ x p' (z : TFK (R := M.W) C ⟶ M.P.A.A), QkPt.Equiv _ C (I.ev k x) p' → z.left = (o.I.ev k x).left ≫ M.φ → M.P.ToA C k p' z := by
  intro hL _ E _ _ _ H D C _ o M _ _
  letI := H.starRing
  have := o.closed
  have := o.P.isAb.comm
  have hB := M.P.D.tau_bimult
  obtain ⟨hA, h0⟩ := M.admissible_base_of_complete_dvr
  obtain ⟨-, l₁, l₂, l₃, l₄⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hT := GlobalTheory.UT.torsionIso_of_pelUnif hL l₁ l₂ l₃ l₄ E H M.W _ hA M.t M.P
  choose f f₁ f₂ f₃ f₄ f₅ f₆ using hT C
  have hg : jFK (R := M.W) C = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := (Category.id_comp _).symm
  obtain ⟨e, he⟩ : ∃ e : (baseOver (Sp C) ⟶ o.P.A) ≃* (TFK (R := M.W) C ⟶ M.P.A.A), ∀ x, (e x).left = x.left ≫ M.φ :=
    LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) _ hg
  have eact : ∀ c x, e (x ≫ o.oa.act c) = e x ≫ M.P.oA.act c := fun c x => Over.OverMorphism.ext (by
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, M.act, Category.assoc])
  have tors : ∀ n (hn : 0 < n) p, f n hn p ^ n = 1 := fun n hn p => by
    obtain ⟨w, hw⟩ := M.P.U.ext
    exact ((f₁ n hn p _).2 rfl w hw).1
  have hev : ∀ n a, ∃ p : QkPt M.P.D.toPre C n, ∀ hn : 0 < n, f n hn p = e (o.I.ev n a) := fun n a => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨TorusExt.qkZero hB C 0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨p, hp⟩ := f₂ n hn (e (o.I.ev n a)) (by rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one])
      exact ⟨p, fun _ => hp⟩
  choose ev evp using hev
  refine ⟨{ ζ := o.I.ζ, ζ_prim := o.I.ζ_prim, ζ_pow := o.I.ζ_pow, ev := ev
            add := fun n hn a b => ?_, lin := fun n hn c a => ?_, ker := fun n hn a b => ?_,
            onto := fun n hn p => ?_, tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ },
    rfl, fun k hk x p' z h hz => ?_⟩
  · exact (TorusExt.qkAdd_iff hB _ _ _).2 ((f₃ n hn _ _).1 (by
      rw [f₄ n hn _ _ _ (TorusExt.qkAdd_qkAdd hB _ _), evp, evp, evp, o.I.add, map_mul]))
  · obtain ⟨p, hp⟩ := qkAct_exists hL.1.globalFns hB M.P.oD c (ev n a)
    have h₁ := f₅ n hn _ _ _ hp
    obtain ⟨q, q₁, q₂, q₃⟩ := hp
    refine ⟨q, q₁, q₂, TorusExt.equiv_trans hB q₃ ((f₃ n hn _ _).1 ?_)⟩
    rw [h₁, evp, evp, o.I.lin, eact]
  · rw [← f₃ n hn, evp, evp, e.injective.eq_iff]
    have h₁ : o.I.ev n a = o.I.ev n b * o.I.ev n (a - b) := by rw [← o.I.add, add_sub_cancel]
    rw [h₁, mul_eq_left, o.I.ker n hn]
    exact exists_congr fun c => sub_eq_iff_eq_add'
  · obtain ⟨a, ha⟩ := (o.I.onto n hn (e.symm (f n hn p))).1 (by rw [← map_pow, tors, map_one])
    exact ⟨a, (f₃ n hn _ _).1 (by rw [evp, ha, MulEquiv.apply_symm_apply])⟩
  · obtain ⟨q, q₁, q₂⟩ := exists_level_down hB n m (ev (n * m) a)
    have hN := Nat.mul_pos hn hm
    have h := (GlobalTheory.LevelCompat.qkToAkU_level hL M.W _ hA M.P.D M.P.A M.t.G M.t.semi M.P.U C n m _ hn hm rfl q
      (ev (n * m) a) _).2 q₁ q₂ ((f₁ _ hN _ _).2 rfl)
    refine ⟨q, q₁, q₂, (f₃ n hn _ _).1 ?_⟩
    rw [← (f₁ n hn _ _).1 h, evp, evp, ← map_pow, o.I.tower n m hn hm]
  · refine (f₆ n hn _ _ _).2 ?_
    rw [evp, evp]
    exact weilIs_of_pull M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) _ hg n _ _ _ _ _ (he _) (he _)
      (o.I.isom n hn a b)
  · refine (f₁ k hk _ _).2 ?_
    rw [← (f₃ k hk _ _).2 h]
    exact (Over.OverMorphism.ext (hz.trans (he _).symm)).trans (evp k x hk).symm

end GlobalTheory.ModelData.ModelTate
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem baseFacts_hasGeo_exists_clos : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Big → ρ.HasU → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE ∧ ρ.HasGeo ∧ ∃ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), ex.core.HasTests ∧ ex.core.Indep ∧ ex.core.Fib ∧ ex.core.HasCharts := by
  intro hL hT o Ω _ _ _ _ S ρ M U₀ EE hB hU hO hE
  have hTests : S.HasTests := by
    intro p _ y hy
    obtain ⟨_, _, τ, _⟩ := hU p y hy ∅
    exact ⟨τ⟩
  have hF : BaseFacts S M U₀ EE := baseFacts_of_isEE o Ω S M U₀ EE hTests hO hE
  have hG : ρ.HasGeo := GlobalTheory.T.hasGeometricTest_of_hasUniformisedTest hL hT o Ω S ρ hB hU
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_abelianSchemeProjectiveClosure hL o Ω S ρ M U₀ EE hF
  obtain ⟨ex⟩ := GlobalTheory.T.nonempty_closureExtension_abelianScheme hL o Ω S ρ M U₀ EE hF Q
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.closure_tests_exist_and_reduction_independent hL o Ω S ρ M U₀ EE hF Q ex hB hG
  have h₃ : ex.core.Fib := GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep ex.core h₂
  exact ⟨hF, hG, Q, ex, h₁, h₂, h₃, GlobalTheory.T.hasGradedCharts_near_generic_point_closure hL o Ω S ρ M U₀ EE hF Q ex hB hG h₃⟩

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem isActOf_smul_of_val_eq {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {m : T ⊗ A ⟶ A} {a b : ℤ} {α α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (ea : ∀ (r : (T ⊗ A).left ⟶ (T ⊗ A).left) y J, Good L y J → val α r y J = val α' r y J)
    {θ θ' : ThetaGrp A L a T} (ept : θ.pt = θ'.pt)
    (eθ : ∀ y J, Good L y J → val θ.φ (𝟙 _) y J = val θ'.φ (𝟙 _) y J)
    {th th' : LB.Sec (LPow A L b T)} {s₀ s₁ t' : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (eth : ∀ j, th.f j = liftFun A _ c * th'.f j)
    (hs₀ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α th s₀)
    (hs₁ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α' th' s₁) (ht' : IsActOf A L a θ' s₁ t') :
    IsActOf A L a θ s₀ (SecM.toSec A (c • SecM.ofSec A t')) := by
  have f₁ : (lift (fst T A) m).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, lift_fst]
  have f₂ : (translT A θ'.pt).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, translT, lift_fst]
  refine VVRank.isTwistPull_of_sv A hL θ.isGen fun y J hJ => ?_
  rw [ThetaPtMove.sv_of_eq_mul (t := t') (c := c) (fun j => rfl) _ y hJ, VVRank.sv_of_isTwistPull A ht' _ y hJ,
    VVRank.sv_of_isTwistPull A hs₁ _ y hJ, VVRank.sv_of_isTwistPull A hs₀ _ y hJ,
    ThetaPtMove.sv_of_eq_mul eth _ y hJ, eθ y J hJ, ea _ y J hJ, ept]
  simp only [Category.assoc, f₁, f₂]
  ring

theorem isActOf_smul_of_thC (hLaw : Laws) {V : Type} [CommRing V] [IsDomain V] [CharZero V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) {F : Type} [Field F] [Algebra (FractionRing V) F]
    {ρ : LB.Gen (A.L.pull (eSec A.A))} {m : ℕ} (hm : Odd m) {th th' : SecA A F 1} {c : Γ((TFK (R := V) F).left, ⊤)}
    (eth : ∀ j, th.f j = liftFun A.A _ c * th'.f j)
    {α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])} {s₀ : SecA A F (m ^ 2)} (hα : α.IsGen)
    (hn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left)
      (rigT A.A A.L ρ (TFK (R := V) F) (((m ^ 2 : ℕ) : ℤ) - 1)))
    (hs₀ : IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₀)
    {x : TFK (R := V) F ⟶ A.A} (hx : x ^ (m ^ 2) = 1) {t' : SecA A F (m ^ 2)} {c' : F} (h : ThC A ρ m th' x t' c')
    {θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) F)} (hθ : SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ) :
    IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₀ (SecM.toSec A.A (c • SecM.ofSec A.A t')) := by
  have hL := A.isLB
  let T := TFK (R := V) F
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap V (FractionRing V))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨α', s₁, θ', hα', hn', hs₁, hθ', ht', -⟩ := h
  obtain ⟨-, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  have eθ' : ∀ y J, Good A.L y J → val θ.φ (𝟙 _) y J = val θ'.φ (𝟙 _) y J := fun y J hJ => by
    rw [val_corr hJ eθ]
  exact isActOf_smul_of_val_eq (α := α) (α' := α') (th := th) (th' := th') (s₁ := s₁) hL
    (fun r y J hJ => ea _ r y J hJ) ept eθ' eth hs₀ hs₁ ht'

theorem comb_smul {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {n : ℕ}
    {σ σ₁ : LB.Sec (LPow A L k T)} {t : Fin n → LB.Sec (LPow A L k T)} {a : Fin n → Γ(T.left, ⊤)} {c : Γ(T.left, ⊤)}
    (eσ : σ = SecM.toSec A (∑ i, a i • SecM.ofSec A (t i))) (h : ∀ j, σ₁.f j = liftFun A _ c * σ.f j) (j) :
    σ₁.f j = ∑ i, liftFun A _ (a i) * (SecM.toSec A (c • SecM.ofSec A (t i))).f j := by
  have e₀ : SecM.ofSec A σ = ∑ i, a i • SecM.ofSec A (t i) := congrArg (SecM.ofSec A) eσ
  have e₁ : SecM.ofSec A σ₁ = c • SecM.ofSec A σ := Subtype.ext (funext h)
  have e : SecM.ofSec A σ₁ = ∑ i, a i • c • SecM.ofSec A (t i) := by
    rw [e₁, e₀, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have e' := congrArg (fun q => q.1 j) e
  simp only [Submodule.coe_sum, Finset.sum_apply] at e'
  exact e'

theorem exists_isComb_translates_of_nuGe : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th' : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th' ϑ → Prim D Q v ϑ → ∀ (m N : ℕ), Odd m → IsUnit (m : V) → 3 ≤ m → N = m ^ 2 → ∀ (th : SecA A F 1) (c : F), IsComb (fun _ : Unit => th') (fun _ => c) th → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left] ![(N : ℤ), -((1 : ℕ) : ℤ)])) (s₀ : SecA A F N), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := V) F) ((N : ℤ) - 1)) → IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s₀ → ∀ (σ σ₁ : SecA A F N) (s : Fam D.toPre F N), U.ExpandsF F N w₀ σ s → NuGe D Q F v N s 0 → IsComb (fun _ : Unit => σ) (fun _ => c) σ₁ → ∃ (n : ℕ) (a : Fin n → F) (x : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F N), (∀ i, 0 ≤ v (a i) ∧ x i ^ N = 1 ∧ ∀ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := V) F), SymLift A.A A.L N N (x i) θ → IsActOf A.A A.L N θ s₀ (t i)) ∧ IsComb t a σ₁ := by
  intro hLL hBC hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th' ϑ hth hprim m N hm hmu h3
    hNm th c hthc α s₀ hα hn hs₀ σ σ₁ s hσ hs hσ₁
  subst hNm
  have hLaw : Laws := hLL.1
  obtain ⟨n, a, x, t', c', r, h, rfl⟩ := (GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates hLL hBC hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th' ϑ
    hth hprim m hm hmu h3 s).1 hs
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨hB, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hA D A G hG U
  obtain ⟨hB₁, hB₂⟩ := hB F (m ^ 2) hN1 w₀ hN.1
  let T := TFK (R := V) F
  let κ : F ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv

  have hsum : ∀ S : Finset (Fin n), U.ExpandsF F (m ^ 2) w₀
      (SecM.toSec A.A (∑ i ∈ S, κ (a i) • SecM.ofSec A.A (t' i))) (∑ i ∈ S, a i • r i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have := hlin F (m ^ 2) w₀ σ σ (SecM.toSec A.A (κ (-1) • SecM.ofSec A.A σ + SecM.ofSec A.A σ)) _ _ (-1) hσ hσ
        fun j => rfl
      rw [map_neg, map_one, neg_one_smul, neg_one_smul, neg_add_cancel, neg_add_cancel] at this
      rw [Finset.sum_empty, Finset.sum_empty]
      exact this
    | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact hlin F (m ^ 2) w₀ _ _ _ _ _ (a i) (h i).2.2.2 ih fun j => rfl
  have eth : ∀ j, th.f j = liftFun A.A _ (κ c) * th'.f j := fun j => (hthc j).trans (Fintype.sum_unique _)
  refine ⟨n, a, x, fun i => SecM.toSec A.A (κ c • SecM.ofSec A.A (t' i)), fun i => ⟨(h i).1, (h i).2.1, fun θ hθ => ?_⟩,
    fun j => ?_⟩
  · exact isActOf_smul_of_thC hLaw A hm eth hα hn hs₀ (h i).2.1 (h i).2.2.1 hθ
  · exact comb_smul (a := fun i => κ (a i)) (c := κ c) ((hB₂ _).unique hσ (hsum Finset.univ))
      (fun j => (hσ₁ j).trans (Fintype.sum_unique _)) j

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : LB.Sec (LPow G U.LG.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp V)))), NZ G U.LG.L (𝟙 (Sp V)) σ → IsGenSec G U.LG.L ((1 : ℕ) : ℤ) σ ∧ ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))), (∀ x (c : F), ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  first | exact @GlobalTheory.Ex.OnModel.theta_on_model | exact GlobalTheory.Ex.OnModel.theta_on_model | (intros; apply GlobalTheory.Ex.OnModel.theta_on_model <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem exists_nsmul_of_nsmul_eq_zero {K : Type} {r N : ℕ} (hr : 0 < r) (hN : 0 < N) (a₀ : K → ZMod (r * N))
    (h : N • a₀ = 0) : ∃ a : K → ZMod (r * N), r • a = a₀ := by
  haveI : NeZero (r * N) := ⟨(Nat.mul_pos hr hN).ne'⟩
  have key : ∀ i, ∃ b : ZMod (r * N), r • b = a₀ i := by
    intro i
    have h1 : ((N * (a₀ i).val : ℕ) : ZMod (r * N)) = 0 := by
      have := congrFun h i
      simpa [nsmul_eq_mul] using this
    rw [ZMod.natCast_eq_zero_iff, _root_.mul_comm N] at h1
    obtain ⟨d, hd⟩ := Nat.dvd_of_mul_dvd_mul_right hN h1
    refine ⟨(d : ZMod (r * N)), ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← hd, ZMod.natCast_zmod_val]
  choose a ha using key
  exact ⟨a, funext ha⟩

theorem exists_span_translates_of_eq_sq (h : Laws) (h₂ : Laws2) {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V) {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (IsLocalRing.maximalIdeal V)} {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (IsLocalRing.maximalIdeal V) D A G)
    (w₀ : W0 U.toUnifPre) (rig : LB.Gen (A.L.pull (eSec A.A))) (hw : NormW U.toUnifPre w₀ rig)
    (th th' : SecA A F 1) (ϑ : Fam D.toPre F 1) (hϑ : U.ExpandsF F 1 w₀ th' ϑ) (hP : Prim D Q v ϑ) (c : F)
    (hth : ∀ j, th.f j = liftFun A.A _ (cF V c) * th'.f j) (m : ℕ) (hm : Odd m) (hu : IsUnit (m : V)) (h3 : 3 ≤ m)
    (N : ℕ) (hN : N = m ^ 2) (Φ : Fam D.toPre F N) (hΦ : NuGe D Q F v N Φ 0) :
    ∃ (n : ℕ) (a : Fin n → F) (z : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F N)
      (r : Fin n → Fam D.toPre F N),
      (∀ i, 0 ≤ v (a i) ∧ z i ^ N = 1 ∧ U.ExpandsF F N w₀ (t i) (r i) ∧
        ∀ (s₁ σ : SecA A F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := V) F)), IsNormPull A rig m N th s₁ →
          SymLift A.A A.L (N : ℤ) N (z i) θ → IsActOf A.A A.L (N : ℤ) θ s₁ σ →
          ∀ j, σ.f j = liftFun A.A _ (cF V c) * (t i).f j) ∧ Φ = ∑ i, a i • r i := by
  subst hN
  obtain ⟨hL, h1, h2, h3', h4⟩ := laws_all h h₂
  obtain ⟨n, a, z, t, c', r, H, hs⟩ :=
    (GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates hL h1 h2 h3' h4 V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ rig hw th' ϑ hϑ hP m hm hu h3 Φ).1 hΦ
  refine ⟨n, a, z, t, r, fun i => ?_, hs⟩
  obtain ⟨ha, hz, hT, hE⟩ := H i
  exact ⟨ha, hz, hE, fun s₁ σ θ hs₁ hθ hσ =>
    GlobalTheory.T.symmetricLift_normalisedPullback_theta_smul hL V A F rig hw.2.1 m hm th th' c hth s₁ σ (t i) (z i) θ (c' i) hz hs₁ hθ hσ hT⟩

theorem IsComb.of_eq_mul {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {J : Type} [Fintype J] {s : J → SecA A F k} {b : J → F}
    {σ t : SecA A F k} (hσ : IsComb A s b σ) {c : F} (hc : c ≠ 0)
    (ht : ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j) : IsComb A s (fun l => c⁻¹ * b l) t := by
  intro j
  have hmul : ∀ x y : F, (liftFun A.A _ (cF R (x * y)) : Γ((TFK (R := R) F ⊗ A.A).left, (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U j)) = liftFun A.A _ (cF R x) * liftFun A.A _ (cF R y) := by
    intro x y
    simp only [liftFun, cF, map_mul]
  have hone : (liftFun A.A _ (cF R (1 : F)) : Γ((TFK (R := R) F ⊗ A.A).left, (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U j)) = 1 := by
    simp only [liftFun, cF, map_one]
  have h1 : t.f j = liftFun A.A _ (cF R c⁻¹) * σ.f j := by
    rw [ht j, ← _root_.mul_assoc, ← hmul, inv_mul_cancel₀ hc, hone, _root_.one_mul]
  rw [h1, hσ j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [hmul, _root_.mul_assoc]

theorem exists_isComb_expands_of_nuGe_zero : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → c ≠ 0 → ∀ Φ : Fam u.D.toPre (PadicAlgCl p) S.N, NuGe u.D Q (PadicAlgCl p) v S.N Φ 0 → ∃ (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N), (∀ j, ‖c * b j‖ ≤ 1) ∧ IsComb u.A s b σ ∧ u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ := by
  intro h h₂ _ o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs ϖ Q v lam hϖ hv hNorm w₀ th' ϑ c hw hϑ hP hth hc Φ hΦ
  obtain ⟨hchar, hun, hadm, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  obtain ⟨hadd, -, hbij, -⟩ := (GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing h o Ω S ρ p y₀ u).2 x hx
  obtain ⟨-, -, -, -, hpull, hact⟩ := hs
  obtain ⟨-, hQ, -, hle, -⟩ := hNorm
  have hN0 : 0 < S.N := lt_of_lt_of_le (by norm_num) S.N_ge
  have hn3 : 3 ≤ ρ.n := by
    have h2 := ρ.n_prime.two_le
    obtain ⟨d, hd⟩ := ρ.n_odd
    omega
  have hm3 : 3 ≤ ρ.n ^ ρ.k :=
    hn3.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  have hmu : IsUnit ((ρ.n ^ ρ.k : ℕ) : u.V) := by
    rw [Nat.cast_pow]; exact hun.pow _
  obtain ⟨n, a, z, t, r, H, hΦs⟩ := exists_span_translates_of_eq_sq h h₂ u.complete hϖ hQ hv u.semi u.U w₀ rig hw
    th th' ϑ hϑ hP c hth (ρ.n ^ ρ.k) ρ.n_odd.pow hmu hm3 S.N ρ.N_eq Φ hΦ
  have hx0 : x 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hxs : ∀ (k : ℕ) (b : S.Gam), x (k • b) = x b ^ k := by
    intro k b
    induction k with
    | zero => rw [zero_nsmul, hx0, pow_zero]
    | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hpt : ∀ i, ∃ g : S.Gam, x (S.r • g) = z i := by
    intro i
    obtain ⟨a₀, ha₀, -⟩ := hbij (z i) (by rw [_root_.mul_comm S.r, pow_mul, (H i).2.1, one_pow])
    obtain ⟨a₁, -, hu₁⟩ := hbij 1 (one_pow _)
    have h0 : S.N • a₀ = 0 :=
      (hu₁ _ (by show x _ = 1; rw [hxs, ha₀, (H i).2.1])).trans (hu₁ 0 hx0).symm
    obtain ⟨g, hg⟩ := exists_nsmul_of_nsmul_eq_zero S.r_pos hN0 a₀ h0
    exact ⟨g, by rw [← ha₀, ← hg]⟩
  choose g hg using hpt
  have ht : ∀ i, IsComb u.A s (fun j => c⁻¹ * y₀ (algebraMap o S.R (S.ρ (g i) j ρ.i₀))) (t i) := by
    intro i
    obtain ⟨θ, hθ, hθa⟩ := hact (g i)
    obtain ⟨σ, hσ, -⟩ := (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s (fun _ => 0)).2.2.2.1 θ (s ρ.i₀)
    rw [hg] at hθ
    exact IsComb.of_eq_mul (hθa _ _ hσ) hc ((H i).2.2.2 _ σ θ hpull hθ hσ)
  obtain ⟨σ, hσ⟩ := (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin n) t a).1
  refine ⟨_, σ, fun j => ?_,
    (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s (fun _ => 0)).2.2.2.2 (Fin n) _ t a σ ht hσ, ?_⟩
  · rw [Finset.mul_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [← _root_.mul_assoc, mul_inv_cancel_left₀ hc, norm_mul]
    have h1 : ‖a i‖ ≤ 1 := by
      have := (hle (a i) 0).1 (by simpa using (H i).1)
      simpa using this
    exact mul_le_one₀ (hy _) (norm_nonneg _) h1
  · rw [hΦs]
    exact (GlobalTheory.T.isFibreSectionLinearComb_iff_expansion_sum (laws_all h h₂).1 u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hN0 w₀ hw.1
      (Fin n) t r a σ fun i => (H i).2.2.1).1 hσ

end GlobalTheory.TestFibre
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.torusOperator_eigen_of_expansion_single_class : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (w₀ : W0 u.U.toUnifPre), w₀.IsGen → ∀ (α : u.D.toPre.X) (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N) (Φ : Fam u.D.toPre (PadicAlgCl p) S.N), IsComb u.A s b σ → u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ → (∀ β, (∀ z : u.D.toPre.X, β ≠ α + S.N • z) → ∀ j, (Φ.s β).f j = 0) → ∀ (t : S.perp l.yy.ker) (h : S.Gam), ∑ j, (∑ i, y₀ (algebraMap o S.R (S.ρ t j i)) * b i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩ = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val * ∑ j, b j * y₀ ⟨S.ev h j, S.ev_mem h j⟩ := by
  first | exact @GlobalTheory.TestFibre.eigen_of_expansion_in_class | exact GlobalTheory.TestFibre.eigen_of_expansion_in_class | (intros; apply GlobalTheory.TestFibre.eigen_of_expansion_in_class <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitThetaConstants_generate_integralTorsion : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (0 < S.delta y₀ ∧ AddSubgroup.closure {x | ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀} = l.yy.ker) := by
  first | exact @GlobalTheory.UnitTheta.closure_unit_theta | exact GlobalTheory.UnitTheta.closure_unit_theta | (intros; apply GlobalTheory.UnitTheta.closure_unit_theta <;> assumption)
end
