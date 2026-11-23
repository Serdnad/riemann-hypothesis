module

public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Formalism.HermitianCurvature.Bundle006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle167
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelFormCutoffTendstoBelow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftBoundOfCompactPositivity
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle164
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PictureMemStableBounded
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlaneWaveBoundOfCompactPositivity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle163
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle149
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle177
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle176
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle067
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle079
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle034
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle025
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle185
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelModuleFormEqIntegralOfCompactCoeff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CmLiftConditionOfLaws
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelAction_mem_cuspForms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.cuspA j (wtA w) w.n, actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.cuspA j (wtA w) w.n := by
  first | exact @GlobalTheory.LevelCusp.actLev_mem_cuspA | exact GlobalTheory.LevelCusp.actLev_mem_cuspA | (intros; apply GlobalTheory.LevelCusp.actLev_mem_cuspA <;> assumption)
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelAction_mem_thetaSeries : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.th j w, f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.th j w := by
  first | exact @GlobalTheory.ThetaLevelMove.actLev_mem_th | exact GlobalTheory.ThetaLevelMove.actLev_mem_th | (intros; apply GlobalTheory.ThetaLevelMove.actLev_mem_th <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem _root_.GlobalTheory.T.value_translate_pullback_eq_generator' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * l.M)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ → PullAl D' F oD' α 1 l.M θ θα → ∀ (p : QkPt D'.toPre F (1 * l.M)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * l.M)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * l.M)) (σ' : U'.toUnifPre.SecGF F (1 * l.M)) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * l.M) p w ζ → QkToAkU U'.toUnifPre F (1 * l.M) p x → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → PhiRel D'.toPre F (1 * l.M) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F (1 * l.M) σ' t → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * l.M) σ' h → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ Ppol ∈ harmA (Dw := Dw) c a n,
 letI := io.toAlgebra
 ∃ f ∈ thGen Xo c nab a n, ∃ e : F, 0 ≤ v e ∧ nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * l.M) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Ppol) = e * (∏ τ : E →+* ℂ, algebraMap T.Fr F (io (embK c τ α)) ^ (∑ i : Fin (Dw.mult τ), a (τ, i))) * algebraMap T.Fr F (evI y f) := by
  first | exact @GlobalTheory.value_translate_pullback_eq_generator | exact GlobalTheory.value_translate_pullback_eq_generator | (intros; apply GlobalTheory.value_translate_pullback_eq_generator <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GeneratorsAtPoint

theorem isUnit_of_prime_ne {V : Type} [CommRing V] [IsLocalRing V] {g g' : ℕ} (hg : g.Prime) (hg' : g'.Prime)
    (hne : g ≠ g') (hn : ¬ IsUnit ((g : ℕ) : V)) : IsUnit ((g' : ℕ) : V) := by
  have hz : IsCoprime (g : ℤ) (g' : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hg hg').2 hne)
  obtain ⟨a, b, hab⟩ : IsCoprime ((g : ℕ) : V) ((g' : ℕ) : V) := by
    simpa using hz.map (Int.castRingHom V)
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h₁ | h₁
  · exact absurd (isUnit_of_mul_isUnit_right h₁) hn
  · exact isUnit_of_mul_isUnit_right h₁

section Cast
variable {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem famCast_symm {k k' : ℕ} (e : k = k') (s : Fam Dp F k') : famCast e (famCast e.symm s) = s := by
  subst e; rfl

theorem famCast_sum {k k' : ℕ} (e : k = k') {m : ℕ} (a : Fin m → F) (b : Fin m → Fam Dp F k) :
    famCast e (∑ i, a i • b i) = ∑ i, a i • famCast e (b i) := by
  subst e; rfl

end Cast

theorem nuGe_famCast {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {Dd : DegData V (maximalIdeal V)} {Q : Dd.toPre.X → ℤ} {K : Type} [Field K] [Algebra (FractionRing V) K]
    {v : AddValuation K (WithTop ℚ)} {k k' : ℕ} (e : k = k') {s : Fam Dd.toPre K k} {r : ℚ}
    (h : NuGe Dd Q K v k s r) : NuGe Dd Q K v k' (famCast e s) r := by
  subst e; exact h

theorem unitBall_spanned (hL : Laws) (hT : TwistBaseChangeStatement)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G' : Over (Sp V)) [gr : GrpObj G'] [cm : IsCommMonObj G'] (U' : Unif (maximalIdeal V) D' A' G')
    [md : Module (𝓞 E) D'.toPre.X] :
    letI := H.starRing
    ∀ (oD' : D'.toPre.OAct (𝓞 E)) (oA' : A'.OAct (𝓞 E)) (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'),
      P'.TorsionIso → t'.G = G' → HEq t'.grp gr → HEq t'.comm cm → P'.D = D' → HEq P'.mod md → HEq P'.oD oD' →
      P'.A = A' → HEq P'.oA oA' → HEq P'.U U' →
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : D'.toPre.X → ℤ), IsQ D'.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ A'.A) (fun a g => g ≫ oA'.act a)
        (fun n g g' c => WeilIs A'.A A'.L n g g' (unitOn c))),
    ∀ θ : Fam D'.toPre F 1, NuGe D' Q F v 1 θ 0 → ThFrame D' ϖ F θ →
    ∀ θα : Fam D'.toPre F (1 * N), PullAl D' F oD' α 1 N θ θα →
    ∀ s : Fam D'.toPre F (1 * N), NuGe D' Q F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt D'.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ A'.A))
        (w : ∀ i, LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F (p i).g.b) (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam D'.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, QkToAkU U'.toUnifPre F (1 * N) (p i) (x i)) ∧
        (∀ i, x i ≫ oA'.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd D' F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam D'.toPre F (1 * N),
          PhiRel D'.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul D'.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i := by
  let _ := H.starRing
  intro oD' oA' t' P' hP e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  exact ReciprocityTheory.ChartRestriction.G.H1.cmLiftCondition_of_laws hL n1c (GlobalTheory.twisting_statements_of_laws hL hT).1
    (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H V t' P' hP

theorem main : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → GenPointT := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hTr P hP hy ϖ hϖ Q hQ g g' hg hg' hne hgo hg'o π π' hπ hπ' hcop hcop' hgnu F _ _ _ _ _ _ v hv I n
    D' A' G' _ _ pD pA pG U' PU _ oD' hx hact s s₂ p w ζ x t₀ t σ' h hbox
  obtain ⟨hs, hs₂, ⟨hw, hζ, hfo⟩, hqx, hxk, hphi, hsm, hexp, hgerm⟩ := hbox
  have hq : 1 ≤ g' * g := Nat.mul_pos hg'.pos hg.pos
  have hπb : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ
  have hπb' : star π' * star (star π') = (g' : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ'
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π) g g' hg.pos hg'.pos hπb
  obtain ⟨pl₂, -, hpl₂⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π * star π') (g' * g) 1 hq
    le_rfl (by rw [star_mul', Nat.cast_mul, ← hπb, ← hπb']; ring)
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V _ D' F (g' * g) hq p w hw
  obtain ⟨τ, hτ, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τ hτ (hτT hTr) F
    (g' * g) hq
  obtain ⟨θ, θα, hθν, hθF, hθα⟩ := PowThetaFrame.main hL hL2 hL4 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
    hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  obtain ⟨oA', hoA, hQ', ⟨Dw', ⟨I'⟩⟩, t', P', hP', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    powPEL_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
      hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv I Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  have hcopb : ∃ u u' : 𝓞 E, u * star π' + u' * star (star π') = 1 := by
    obtain ⟨u, u', hu⟩ := hcop'
    exact ⟨u', u, by rw [star_star, ← hu]; ring⟩
  obtain ⟨m, pb, xb, wb, ζb, tb, a, hpx, hxb, hwb, htb, ha, hsum⟩ :=
    unitBall_spanned hL hT E H T.V D' A' G' U' oD' oA' t' P' hP' e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ (star π') g' hg'.pos hπb' hcopb
      (isUnit_of_prime_ne hg hg' hne hgnu) ϖ hϖ _ hQ' F v hv Dw' I' θ hθν hθF θα hθα
      (famCast (Dp := D'.toPre) (F := F) (one_mul g').symm s) (nuGe_famCast _ hs)
  have hs' : s = ∑ i, a i • famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i) := by
    rw [← famCast_sum, ← hsum, famCast_symm]
  let Λ : Fam D'.toPre F g' →ₗ[F] Fam D'.toPre F (g' * g) := (ζ • Φ) ∘ₗ pl
  refine ⟨θ, pl₂ θ, m, a, fun i => gm (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i))), hθν, hθF,
    (hpl₂ _ _).2 rfl, ha, ?_, fun i => ?_⟩
  · have ht : t = Λ s := by
      rw [(DVR.isSmul_iff _ _ _).1 hsm, (hΦ _ _).1 hphi, (hpl _ _).1 hs₂]
      rfl

    rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), ht, hs', map_sum, map_sum]
    simp only [map_smul]
  · obtain ⟨tb₀, h₁, h₂⟩ := htb i
    obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
      PowDescent.descentIdF_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
        hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact oA' hoA θ θα hθα
        (pb i) (wb i) (ζb i) (xb i) tb₀ (tb i) (hpx i) (hxb i) (hwb i).1 (hwb i).2.1 (hwb i).2.2 h₁ h₂
        p w ζ x hw hζ hfo hqx hxk _ _ (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
        ((hpl _ _).2 rfl) ((hΦ _ _).2 rfl) ((DVR.isSmul_iff _ _ _).2 rfl)
    obtain ⟨σ₂, j₁, j₂⟩ := hgmex (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
    refine ⟨p₂, w₂, ζ₂, x₂, r₀, r₂, σ₂, k₂, fun b => ?_, k₄, k₅, k₆, (hpl₂ _ _).1 k₁ ▸ k₇, k₈, k₉ ▸ j₁,
      (hiff F _ σ₂ _).2 j₂⟩
    have := pA.hom b
    rw [← hoA, ← Category.assoc, k₃, MonObj.one_comp]

end GlobalTheory.GeneratorsAtPoint
end
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
open Filter Topology

namespace GlobalTheory.PointwiseBoundDecay

theorem levelZero_limit_of_xiExists (hΞ : B.XiExists) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (ε A : ℝ) (N : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimZeroN p nn (D.cutF p.T.base χ f ε) Y N := by
  obtain ⟨Cc, hCc⟩ := GlobalTheory.GivenXi.levelForm_cutoff_tendsto hΞ Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N nn Y hDD hχ hε hf hfA hA
  have hFL := (hCc Wp Wq P p f χ ε A N (cutN P.k P.r) hDD hχ hε hf hfA hA (fun _ _ => rfl)).2
  intro w hw hN
  have hT := hFL 0 w hw.1 hN [] []
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have e1 : ∀ n : ℕ, TBB.Ew p nn (apx (D.cutF p.T.base χ f ε) n) 0 w [] =
      (p.RR (fun g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g) 0 w [] []).re / TBB.normC nn w :=
    fun n => Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  have e2 : TBB.Ew p nn (D.cutF p.T.base χ f ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re / TBB.normC nn w :=
    Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  simp only [e1, e2]
  exact hre.div_const _

theorem top_threshold_le (r k N : ℕ) :
    ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have h1 : 1 ≤ n := by linarith
  have h3 : n ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h4 : (r : ℝ) * n + 1 ≤ ((r : ℝ) + 1) * n := by nlinarith
  have h5 : ((r : ℝ) + 1) ≤ ((r : ℝ) + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have h6 : n ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by
    have : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    linarith
  have h7 : ((r : ℝ) + 1) * n ≤ ((r : ℝ) + 1) ^ 2 * ((N : ℝ) * n ^ 2 + n ^ 3) :=
    mul_le_mul h5 h6 (by linarith) (by positivity)
  calc ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)
      ≤ ((r : ℝ) + 1) ^ 2 * (((r : ℝ) + 1) ^ 2 * ((N : ℝ) * n ^ 2 + n ^ 3)) :=
        mul_le_mul_of_nonneg_left (h4.trans h7) (by positivity)
    _ = _ := by ring


open GlobalTheory.PointwiseBound in
theorem ptBound_of_xiExists (hXi : B.XiExists) (hA : P5.ThmPActualCpt) : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ κ₀ : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ), 1 ≤ Λ → 0 < κ₀ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) → (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε)) → (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ F ε) Y N) → LimE p nn χ F Y N → LemB p F κ₀ → TBB.PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  have hRad := GlobalTheory.WeightedFormPos.radialModuleForm_of_xiExists hXi
  have hSS := GlobalTheory.ListDuality.listDuality_cpt hRad
  have hVI := waveIsometry_of_radial hRad
  have hFP := GlobalTheory.WeightedFormPos.formPosCpt_of_xiExists hXi
  have hI4 := GlobalTheory.LiftBoundCpt.liftBound_of_xiExists hXi hA hSS hFP
  obtain ⟨C₂, hC₂, hLS⟩ := Formalism.FourierDecayAlt.P.lemma_s_of_parts Formalism.FourierDecayAlt.P.lemma_s_induction_base
    Formalism.FourierDecayAlt.P.lemma_s_induction_up
  refine ⟨C₂, hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb hF hWG hLG hI5 hTN hZN hE hB
  refine Formalism.FourierDecayAlt.P.point_bound_of_corollary_s Wp Wq P p nn χ F Y Λ K N C₂ κ₀ hC₂.le hκ hnn
    ⟨1, one_pos, fun ε hε _ => ?_⟩ (Formalism.FourierDecayAlt.P.vector_truncation_at_place p χ F hχ.2.2)
    (Formalism.FourierDecayAlt.P.limit_zero_at_place p nn χ F Y N κ₀ hE hB)
  refine corS_of_apx p nn _ Y Λ K N C₂ (fun n => ?_) (hTN ε hε) (hZN ε hε)
  have hG := cptCoef_apx P p.T.base hχ hF hε n
  have hPos := GlobalTheory.WeightedFormPos.posAt_of_cptCoef_of_xiExists hXi hA Wp Wq P p nn _ Y N (fun y => (hnn y).le) hG
  exact Formalism.FourierDecayAlt.P.corSOfLemmaS_statement Wp Wq P p nn _ Y Λ K N C₂ hKN hC₂.le hPos
    (hLS Wp Wq P p nn _ Y Λ K N hK hΛ hPos (extension_at_zero hXi hA p nn _ Y N Cb hCb hG)
      (GlobalTheory.planeWave_bound_of_xiExists hXi hA hVI hSS hFP Wp Wq P p nn _ Y Λ K N Cb hCb hG hnn hWG)
      (hI4 Wp Wq P p nn _ Y Λ K N hG hnn hLG) (hI5 ε hε n))

theorem main : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ C₂ Cc : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ A : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ), 1 ≤ Λ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) → LimEvT p χ F Y N → LimBd p nn F Y N → TBB.PtBound p F (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  intro hA Cb
  have hXi : B.XiExists := Formalism.FourierDecayAlt.P.exists_auxiliary_xi
  obtain ⟨C₂, hC₂, hPt⟩ := ptBound_of_xiExists hXi hA
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Ca, hCa⟩ := levelZero_limit_of_xiExists hXi Cb
  obtain ⟨Ce, hE⟩ := GlobalTheory.LevelZeroLimit.limE_of_limEvT_of_xiExists hXi hA Cb
  refine ⟨C₂, max (max 0 c₃) (max Ca Ce), hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P q F Λ A χ nn Y K N hΛ hK hKN hχ hnn hCb hF hFA hth hWG hLG hI5 hLim hBd
  set C : ℝ := max (max 0 c₃) (max Ca Ce) with hC
  have hC0 : 0 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC3 : c₃ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCa' : Ca ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCe' : Ce ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hmono : ∀ c : ℝ, c ≤ C → c * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := fun c hc =>
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)).trans hth
  have hth1 : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A := by
    refine le_trans ?_ hth
    rw [mul_assoc, mul_assoc]
    exact (mul_le_mul_of_nonneg_right hC3 (by positivity)).trans
      (mul_le_mul_of_nonneg_left (top_threshold_le P.r P.k N) hC0)
  exact hPt Wp Wq P q F Λ 1 χ nn Y K N Cb hΛ one_pos hK hKN hχ hnn hCb hF hWG hLG hI5
    (hc₃ Wp Wq P q nn χ F A hth1 hχ hFA hF)
    (fun ε hε => hCa Wp Wq P q F χ ε A N nn Y hCb hχ hε hF hFA (hmono _ hCa'))
    (hE Wp Wq P q F χ nn A N Y hCb hχ (fun y => (hnn y).le) hF hFA (hmono _ hCe') hLim hBd)
    (lemB_one q F)

end GlobalTheory.PointwiseBoundDecay
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (j : ℕ) (h : C.LPt), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → j ≤ P.r → D.IsLocPt h j → Integrable (fun t : ℂ => (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)])) ∧ p.RR H j w h h = ∫ t : ℂ, (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)]) := by
  first | exact @GlobalTheory.LevelIntegralStep.levelForm_eq_integral | exact GlobalTheory.LevelIntegralStep.levelForm_eq_integral | (intros; apply GlobalTheory.LevelIntegralStep.levelForm_eq_integral <;> assumption)
end
