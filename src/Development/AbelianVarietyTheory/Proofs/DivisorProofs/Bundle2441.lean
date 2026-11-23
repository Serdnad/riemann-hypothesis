module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle138
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle177
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle079
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle061
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.JetsLevelZero

theorem jets_on_copies_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (q D : ℕ), 4 * D + 4 ≤ q → (D : ℝ) * M0 < q →
  ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f →
    ∃ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q) (g : PS F n (chD C.ch)) (lam : F),
      NuGe D' (sumQ pD.xe Q) F v q s 0 ∧ U'.toUnifPre.ExpandsG F q σ' s ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g ∧
      lam ≠ 0 ∧ (∃ ρ : ℚ, v lam = (ρ : WithTop ℚ) ∧ (ρ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / q) ∧
      ∀ e : Fin n × Fin (chD C.ch) →₀ ℕ, e.degree ≤ D →
        MvPowerSeries.coeff e g = MvPowerSeries.coeff e (lam • MvPowerSeries.map (algebraMap T.Fr F) f) := by
  obtain ⟨L1, L2, -, L4, -⟩ := GlobalTheory.firstFiveLaws
  have TB := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c inst hstar
  obtain rfl : inst = H.starRing := starSt E H inst hstar
  letI := H.starRing
  intro T io y C htr P ϖ hϖ Q hQ Φ M0 r b hΦ0 hΦ hM n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ v hv q D hq hD f hf
  choose f₀ hf₀ using hf
  obtain ⟨τ, hτ, htrunc, hgerm⟩ := frameNSt_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n (chD C.ch) pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨r', b', h1, h2⟩ := GlobalTheory.PowJets.exists_basis_bounds pD.xe Q (Q_zero hϖ P.D hQ) (RoundingSumAlt.Q_nonneg hϖ hQ) Φ M0 b hΦ hM
  have hD' : (D : ℝ) * max M0 0 < q := by
    rcases le_total M0 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact_mod_cast (by omega : 0 < q)
    · rwa [max_eq_left h]
  obtain ⟨s, σ', g, lam, a1, a2, a3, a4, a5, a6⟩ := GlobalTheory.UnifJets.jets L1 L2 L4 TB T.V ϖ hϖ D' A' G' U' (Fin n × Fin (chD C.ch))
    (zV pG C.xT) hu τ hτ (htrunc htr) (sumQ pD.xe Q) (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) Φ (max M0 0) r' b' hΦ0
    (le_max_right _ _) h1 h2 F v hv q D hq hD' (fun e => f₀ e)
  refine ⟨s, σ', g, lam, a1, a2, (hgerm F q σ' g).2 a3, a4, a5, fun e he => ?_⟩
  rw [a6 e he, map_smul, MvPowerSeries.coeff_map, ← hf₀ e, smul_eq_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem rPoint_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z)))
    (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → 1 ≤ n →
  ∀ (α : 𝓞 E) (N Dg : ℕ), α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : T.V) →
    4 * Dg + 4 ≤ N → (Dg : ℝ) * M0 < N →
  ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ →
    PullAl D' F oD' α 1 N θ θα →
  ∀ (I : Type) [Fintype I] (Pi : I → MvPolynomial (LtN Dw n) F) (a : I → F), (∀ i, 0 ≤ v (a i)) →
    (∑ i, a i • Pi i).totalDegree ≤ Dg → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∀ gm : ℚ,
    letI := io.toAlgebra
    v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) (MvPowerSeries.map (algebraMap T.Fr F) f) (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (∑ i, a i • Pi i)) = (gm : WithTop ℚ) →
    ∃ (i : I) (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F)
      (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (σ' : U'.toUnifPre.SecGF F (1 * N)) (h : PS F n (chD C.ch)) (ρ : ℚ),
      w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (1 * N) p w ζ ∧ QkToAkU U'.toUnifPre F (1 * N) p x ∧
      (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) ∧ PhiRel D'.toPre F (1 * N) p w θα t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
      U'.toUnifPre.ExpandsG F (1 * N) σ' t ∧ IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * N) σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) h (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (Pi i)) = (ρ : WithTop ℚ) ∧
      (ρ : ℝ) ≤ gm + (Dg : ℝ) ^ 2 * Φ / N := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hFT P hP ϖ hϖ Q hQ F _ _ _ _ _ _ v hv I Φ M0 r b hΦ hb hbw n D' A' G' _ _ pD pA pG U' PU _ oD' hx hoD hn
    α N Dg hα hcop hu hN hM θ θα hθ hθF hθα J _ Pi a ha hdeg f hf gm hval
  let _ := io.toAlgebra
  have hN1 : 1 ≤ 1 * N := by omega
  obtain ⟨s, σ', g, lam, hs, hσ', hg, -, ⟨ρl, hlam, hρl⟩, hjet⟩ :=
    jets_on_copies_any E H Dw l Xo c (fun _ => rfl) T io y C hFT P ϖ hϖ Q hQ Φ M0 r b hΦ hb hbw n hn D' A' G'
      pD pA pG U' PU F v hv (1 * N) Dg (by omega) (by rwa [Nat.one_mul]) f hf
  obtain ⟨m, p, x, w, ζ, t, cf, e1, e2, e3, e4, e5, e6⟩ := GlobalTheory.SmallTranslate.span_pow h1 h2 h3 h4 h5 hT T.V E H C.I.G P Dw ϖ hϖ Q hQ F v hv I
    n D' A' G' pD pA pG U' PU oD' hx hoD α N (by omega) hα hcop hu θ θα hθ hθF hθα s hs
  obtain ⟨τ, hτ, hτT, hiff⟩ := GlobalTheory.PowGerm.frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hz τ hτ F (1 * N)
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr h1 h2 h4 hT T.V D' A' G' U' F (1 * N) hN1).2
  choose σ hσ using fun j => (hbij (t j)).exists
  choose h hh using fun j => hex (hτT hFT) (σ j)
  have hsum : g = ∑ j, cf j • h j := by
    let σ₀ : U'.toUnifPre.SecGF F (1 * N) := GlobalTheory.ExpansionLinear.secComb
      (fun j => Out.scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj G')).left (cf j)) σ
    have k1 := GlobalTheory.GroupExpansionLinear.expandsG_sum T.V D' A' G' U' F (1 * N) m cf σ t σ₀ hσ (fun _ => rfl)
    rw [← e6] at k1
    have k2 : σ' = σ₀ := (hbij s).unique hσ' k1
    exact huniq σ' _ _ ((hiff F _ σ' g).1 hg) (hlin m cf σ h σ' hh (fun _ => by rw [k2]; rfl))
  obtain ⟨n1, n2, n3⟩ := GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) n
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
  have k1 := n1 (∑ i, a i • Pi i) _ _ (fun e he => hjet e (he.trans hdeg))
  have k2 := n2 (∑ i, a i • Pi i) Unit (fun _ => lam) (fun _ => MvPowerSeries.map (algebraMap T.Fr F) f)
  rw [Finset.univ_unique, Finset.sum_singleton, Finset.sum_singleton] at k2
  have k3 := n2 (∑ i, a i • Pi i) (Fin m) cf h
  rw [← hsum, k1, k2, Finset.sum_congr rfl fun j _ => congrArg (cf j * ·) (n3 (h j) J a Pi)] at k3
  have k4 := congrArg v k3
  rw [v.map_mul, hlam] at k4
  obtain ⟨i, j, ρ, hρ, hle⟩ := GlobalTheory.SmallTranslate.exists_term_le v a cf _ ha e5 (ρl + gm)
    (k4.symm.trans (by rw [WithTop.coe_add]; exact congrArg _ hval))
  obtain ⟨t₀, ht₀, ht⟩ := e4 j
  refine ⟨i, p j, w j, ζ j, x j, t₀, t j, σ j, h j, ρ, (e3 j).1, (e3 j).2.1, (e3 j).2.2, e1 j, e2 j, ht₀, ht, hσ j,
    (hiff F _ _ _).2 (hh j), hρ, ?_⟩
  rw [Nat.one_mul] at hρl
  have : (ρ : ℝ) ≤ ρl + gm := by exact_mod_cast hle
  linarith

end GlobalTheory.JetsLevelZero
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTransport

theorem cech_of_logKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → GlobalTheory.CechKS.IsCechKS A A' i (Xo.univ.t.PP.L.pull π) (fun a => ub (e.symm a).1 (e.symm a).2) (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) := by
  intro E _ _ _ H Dw l Xo c TF U n e v hv D Θ hks K _ _ P hU hb y' hU' hy' hev A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hred := GlobalTheory.T.dualNumberReduction_tangent_framedPoint E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  obtain ⟨ι, ι', h1, h2, h3, h4, h5, h6⟩ :=
    GlobalTheory.T.exists_semiAbelian_pullback_framed_tangent E H Dw l Xo c TF U n e v K P hU hb y' hy' hred A A' π π' i ub hi hπ hπ' hiπ hub
  have hint : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ LogKS.interior TF.Y := by
    intro x _
    exact ⟨(frX P).base x, rfl⟩
  exact GlobalTheory.T.cechGluing_of_kodairaSpencer_relation E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) U n v D.1 Θ hv.1 hks K (frX P ≫ TF.Y.j) hU hint
    (y' ≫ TF.Y.j) hU' hev A A' ι ι' i _ hi h1 h2 h3
    (fun a => by simpa using h4 (e.symm a).1 (e.symm a).2) _ h6 h5

end GlobalTheory.CechTransport
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem kaehlerDifferential_map_commutative_pentagon {R₁ R₂ A₁ A₂ A₃ A₄ A₅ : Type} [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [CommRing A₃] [CommRing A₄] [CommRing A₅] [Algebra R₁ A₁] [Algebra R₁ A₂] [Algebra R₁ A₃] [Algebra R₂ A₄]
    [Algebra R₂ A₅] {σ₁ σ₂ : R₁ →+* R₁} {σ₃ σ₄ : R₁ →+* R₂} {σ₅ : R₂ →+* R₂} {a : A₁ →+* A₂} {b : A₂ →+* A₃}
    {c : A₃ →+* A₄} {d : A₁ →+* A₅} {e : A₅ →+* A₄} (ha : SemiHom σ₁ a) (hb : SemiHom σ₂ b) (hc : SemiHom σ₃ c)
    (hd : SemiHom σ₄ d) (he : SemiHom σ₅ e) (h : ∀ x, c (b (a x)) = e (d x)) (x : Ω[A₁⁄R₁]) :
    hc.m1 (hb.m1 (ha.m1 x)) = he.m1 (hd.m1 x) := by
  rw [SemiHom.oneFormMap_comp_oneFormMap _ _ (hd.comp he) (fun _ ↦ rfl), SemiHom.oneFormMap_comp_oneFormMap _ _ (ha.comp hb) (fun _ ↦ rfl)]
  exact SemiHom.oneFormMap_comp_oneFormMap _ _ (hd.comp he) h x

theorem isPull1_of_pair_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z1) (k' : (KK D'.κ D'.t).Z1) (w : cechDeRhamTotalCocyclesOne (OAff D.s)) (w' : cechDeRhamTotalCocyclesOne (OAff D'.s)), Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k.1) w.1 → Λ'.Res1 (((KK D'.κ D'.t).resMap Λ'.L).p1 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D0 g = ((pairB Λ' φ m).pre θ).p1 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1 → IsPull1 hφ (Hyp1.mk _ w) (Hyp1.mk _ w') := by
  intro D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' g hg
  unfold IsPull1
  rw [pullHyp1_mk, pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨fun p ↦ (Λ'.e (Opposite.op p.unop.1.1)).symm (g p), Tot1.ext (fun p q a ↦ ?_) fun p ↦ ?_⟩
  · let B : Type := (Λ'.L.obj (Opposite.op q.unop.1.1)).B
    have e : @HSub.hSub B B B _ (g q) ((Λ'.L.map ((pairFst φ).map a)).φ (g p)) =
        @HSub.hSub B B B _ ((θ.app q).φ (k.1.1 _ _ (Λ.L.map ((pairSnd φ).map a))))
          (k'.1.1 _ _ (Λ'.L.map ((pairFst φ).map a))) :=
      congrArg (fun c ↦ c.1 p q a) hg
    have h1 : k.1.1 _ _ (Λ.L.map ((pairSnd φ).map a)) =
        Λ.e (Opposite.op q.unop.1.2) (w.1.1 _ _ ((pairSnd φ).map a)) := hw.1 _ _ _
    have h2 : k'.1.1 _ _ (Λ'.L.map ((pairFst φ).map a)) =
        Λ'.e (Opposite.op q.unop.1.1) (w'.1.1 _ _ ((pairFst φ).map a)) := hw'.1 _ _ _
    have h3 := Λ'.nat ((pairFst φ).map a) ((Λ'.e (Opposite.op p.unop.1.1)).symm (g p))
    have h4 := hθ q (w.1.1 _ _ ((pairSnd φ).map a))
    apply (Λ'.e (Opposite.op q.unop.1.1)).injective
    refine ((map_sub _ _ _).trans ?_).trans (map_sub _ _ _).symm
    refine (congrArg₂ (fun x y : B ↦ x - y) (AlgEquiv.apply_symm_apply _ _) (h3.trans
      (congrArg _ (AlgEquiv.apply_symm_apply _ _)))).trans (e.trans ?_)
    exact congrArg₂ (fun x y : B ↦ x - y) ((congrArg (θ.app q).φ h1).trans h4) h2
  · let B : Type := K1 D'.R (Λ'.L.obj (Opposite.op p.unop.1.1)).δ
    have e : kd0 D'.R (Λ'.L.obj (Opposite.op p.unop.1.1)).δ (g p) =
        @HSub.hSub B B B _ (km1 (morSemi m (Λ'.L.obj (Opposite.op p.unop.1.1))) (morDP m _)
          (km1 (SemiHom.of_algHom (θ.app p).φ) (θ.app p).dp
          (k.1.2 (Λ.L.obj (Opposite.op p.unop.1.2))))) (k'.1.2 (Λ'.L.obj (Opposite.op p.unop.1.1))) :=
      congrArg (fun c ↦ c.2 p) hg
    have h1 : k.1.2 (Λ.L.obj (Opposite.op p.unop.1.2)) =
        Submodule.Quotient.mk ((Λ.semi _).m1 (w.1.2 (Opposite.op p.unop.1.2))) := hw.2 _
    have h2 : k'.1.2 (Λ'.L.obj (Opposite.op p.unop.1.1)) =
        Submodule.Quotient.mk ((Λ'.semi _).m1 (w'.1.2 (Opposite.op p.unop.1.1))) := hw'.2 _
    rw [h1, h2] at e
    apply (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' (Opposite.op p.unop.1.1)).1.1
    have h3 : (Λ'.semi (Opposite.op p.unop.1.1)).m1 (KaehlerDifferential.D D'.R _
        ((Λ'.e (Opposite.op p.unop.1.1)).symm (g p))) = KaehlerDifferential.D D'.R _ (g p) :=
      (SemiHom.m1_D _ _).trans (congrArg _ ((Λ'.e _).apply_symm_apply _))
    have h4 := kaehlerDifferential_map_commutative_pentagon (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      (morSemi m (Λ'.L.obj (Opposite.op p.unop.1.1))) (semiHom_secPull hφ p.unop)
      (Λ'.semi (Opposite.op p.unop.1.1)) (hθ p) (w.1.2 (Opposite.op p.unop.1.2))
    have h5 : q1 (pairRes φ D'.s) p (w'.1.2 (Opposite.op p.unop.1.1)) = w'.1.2 (Opposite.op p.unop.1.1) :=
      cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff D'.s) (pairFst φ) p _
    refine (congrArg Submodule.Quotient.mk h3).trans (e.trans ?_)
    refine (Submodule.Quotient.mk_sub _).symm.trans (congrArg Submodule.Quotient.mk ?_)
    refine Eq.trans ?_ (map_sub _ _ _).symm
    exact congrArg₂ (· - ·) h4 (congrArg (Λ'.semi (Opposite.op p.unop.1.1)).m1 h5.symm)

end GlobalTheory.PDForm
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_natTrans (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R)
    (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ)
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (hi : φ₀ ≫ D.i = D'.i ≫ φ) :
    ∃ θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G, ∀ (p : (Pair φ)ᵒᵖ) a,
      (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
        Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a) := by
  choose θ hθ using GlobalTheory.T.exists_smoothLift_hom_affinePair D D' Λ Λ' σ φ φ₀ hφ m hi
  refine ⟨⟨fun p ↦ θ p.unop, fun p q a ↦ ?_⟩, fun p a ↦ hθ p.unop a⟩
  apply Thick.Hom.ext'
  apply AlgHom.ext
  intro b
  obtain ⟨x, rfl⟩ := (Λ.e (Opposite.op p.unop.1.2)).surjective b
  have h1 := Λ.nat ((pairSnd φ).map a) x
  have h2 := hθ q.unop (mp (OAff D.s) ((pairSnd φ).map a) x)
  have h3 := hθ p.unop x
  have h4 := Λ'.nat ((pairFst φ).map a) (GlobalTheory.CechDR.secPull D.s D'.s p.unop x)
  have h5 := (pairPull hφ).naturality a x
  exact ((congrArg (θ q.unop).φ h1.symm).trans h2).trans
    ((congrArg (Λ'.e (Opposite.op q.unop.1.1)) h5).trans
      (h4.trans (congrArg (Λ'.L.map ((pairFst φ).map a)).φ h3.symm)))

end GlobalTheory.PDForm
end

section


theorem _root_.GlobalTheory.T.transport_permuted_directSum_complexification : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  first | exact @GlobalTheory.DefRead.Transport.transport | exact GlobalTheory.DefRead.Transport.transport | (intros; apply GlobalTheory.DefRead.Transport.transport <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_componentStalkDerivation_of_functionField_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), (∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r)) → ∀ (d : Fin Dw.dim → Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ (d j r)) → letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j a, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField a) = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (δ j a)) ∧ ∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx (d j r) := by
  first | exact @GlobalTheory.LogKSDiv.exists_stalkDer_extend | exact GlobalTheory.LogKSDiv.exists_stalkDer_extend | (intros; apply GlobalTheory.LogKSDiv.exists_stalkDer_extend <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.boundary_componentStalk_regular_boundaryIdeal_prod_params : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1), x ∉ (j₀ TF.Y Z).opensRange → IsRegularLocalRing ((X₀ TF.Y Z).presheaf.stalk x) ∧ ∃ (n : ℕ) (f : Fin n → (X₀ TF.Y Z).presheaf.stalk x) (J : Finset (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp ((X₀ TF.Y Z).presheaf.stalk x) n f ∧ J.Nonempty ∧ Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) = Ideal.span {∏ i ∈ J, f i} := by
  first | exact @GlobalTheory.LogKSDiv.boundary_germ_snc | exact GlobalTheory.LogKSDiv.boundary_germ_snc | (intros; apply GlobalTheory.LogKSDiv.boundary_germ_snc <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.span_logDer_germs' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∈ (j₀ TF.Y Z).opensRange → Submodule.span ((X₀ TF.Y Z).presheaf.stalk x) (Set.range δ) = ⊤ := by
  first | exact @GlobalTheory.LogKSDiv.span_logDer_germs | exact GlobalTheory.LogKSDiv.span_logDer_germs | (intros; apply GlobalTheory.LogKSDiv.span_logDer_germs <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep


theorem _root_.GlobalTheory.T.topFormDerivationDetPairing_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  first | exact @GlobalTheory.LogKSDiv.topPair_change_matrix | exact GlobalTheory.LogKSDiv.topPair_change_matrix | (intros; apply GlobalTheory.LogKSDiv.topPair_change_matrix <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep


theorem _root_.GlobalTheory.T.transpose_mul_symPair_mem_span_balancedTensors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (R : Type) [CommRing R] (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (B : Matrix (Fin n) (Fin n') R), (∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0) → ∀ P : GlobalTheory.LogKSDiv.PairIx H Dw, ∃ cf : Fin Dw.dim → R, _root_.Matrix.transpose B * GlobalTheory.LogKSDiv.symPair (R := R) e P * B = ∑ k, cf k • GlobalTheory.LogKSDiv.symPair (R := R) e' (ε' k) := by
  first | exact @GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | exact GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | (intros; apply GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_logVectorField_extend_functionFieldDerivation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ {N : ℕ} (Dl : Fin N → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), ∃ D : Fin N → GlobalTheory.LogKSDiv.GenDer TF Z, letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r) := by
  first | exact @GlobalTheory.LogKSDiv.exists_genDer_extend | exact GlobalTheory.LogKSDiv.exists_genDer_extend | (intros; apply GlobalTheory.LogKSDiv.exists_genDer_extend <;> assumption)
end
