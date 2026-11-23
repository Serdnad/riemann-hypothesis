module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle066
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle135
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPelUnifOfUnifPow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle143
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle079
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle034
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle036
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle133
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.Bundle008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableWeightNormSq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle157
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle247
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053

@[expose] public section

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

namespace GlobalTheory.SmallTranslate

theorem exists_term_le {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {I J : Type} [Fintype I] [Fintype J]
    (a : I → F) (c : J → F) (x : J → I → F) (ha : ∀ i, 0 ≤ v (a i)) (hc : ∀ j, 0 ≤ v (c j)) (r : ℚ)
    (h : v (∑ j, c j * ∑ i, a i * x j i) = (r : WithTop ℚ)) :
    ∃ (i : I) (j : J) (ρ : ℚ), v (x j i) = (ρ : WithTop ℚ) ∧ ρ ≤ r := by
  by_contra hne
  have hlt : ∀ i j, (r : WithTop ℚ) < v (x j i) := fun i j => by
    by_contra hle
    obtain ⟨ρ, hρ, hρr⟩ := WithTop.le_coe_iff.1 (not_lt.1 hle)
    exact hne ⟨i, j, ρ, hρ, hρr⟩
  have : (r : WithTop ℚ) < v (∑ j, c j * ∑ i, a i * x j i) := by
    refine AddValuation.map_lt_sum v WithTop.coe_ne_top fun j _ => ?_
    rw [v.map_mul]
    refine lt_add_of_nonneg_of_lt (hc j) (AddValuation.map_lt_sum v WithTop.coe_ne_top fun i _ => ?_)
    rw [v.map_mul]
    exact lt_add_of_nonneg_of_lt (ha i) (hlt i j)
  exact absurd h this.ne'

theorem span_pow (h1 : Laws) (h2 : Laws2) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [hc : IsAdicComplete (maximalIdeal V) V] [CharZero V]
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (Dw : Datum H) (ϖ : V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
    (I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
      (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z)))
    (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V))
    [gG : GrpObj G'] [cG : IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n)
    (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) :
    letI := H.starRing
    ∀ [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : V) →
    ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ →
      PullAl D' F oD' α 1 N θ θα →
    ∀ s : Fam D'.toPre F (1 * N), NuGe D' (sumQ pD.xe Q) F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt D'.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ A'.A))
        (w : ∀ i, LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F (p i).g.b) (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam D'.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, QkToAkU U'.toUnifPre F (1 * N) (p i) (x i)) ∧
        (∀ i k, x i ≫ pA.pr k ≫ P.oA.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd D' F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam D'.toPre F (1 * N),
          PhiRel D'.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul D'.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i := by
  let _ := H.starRing
  intro md oD' hx hoD α N hN hα hcop hu θ θα hθ hθF hθα s hs
  obtain ⟨oA', hoA, t', P', hG, hgrp, hcomm, hD, hmod, hoD', hA, hoA', hU⟩ :=
    GlobalTheory.exists_pelUnif_of_unifPow h1 h2 h4 hT V E H t P n D' A' G' pD pA pG U' PU oD' hx hoD
  obtain ⟨Dw', ⟨I'⟩⟩ := GlobalTheory.exists_tateIso_of_isPowPolAV h1 h2 h4 hT E H V n P.A A' pA F P.oA.act oA'.act hoA Dw I
  have hQ' : IsQ D'.toPre ϖ (sumQ pD.xe Q) := GlobalTheory.QBox.main V ϖ hϖ n P.D D' pD Q hQ
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main h1.globalFns hT
  have hP' : P'.TorsionIso := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨h1, h2, h3, h4, h5⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
    (GlobalTheory.twisting_statements_of_laws h1 hT).1 hUU E H V _
    ⟨inferInstance, inferInstance, inferInstance, hc⟩ t' P'
  subst hG hD hA
  cases hgrp
  cases hmod
  cases hoD'
  cases hoA'
  cases hU
  obtain ⟨m, p, x, w, ζ, tt, a, e1, e2, e3, e4, e5, e6⟩ := ReciprocityTheory.ChartRestriction.G.H1.cmLiftCondition_of_laws h1 n1c (GlobalTheory.twisting_statements_of_laws h1 hT).1 hUU E H V t' P' hP' α N hN hα hcop hu ϖ hϖ _ hQ' F v hv
    Dw' I' θ hθ hθF θα hθα s hs
  refine ⟨m, p, x, w, ζ, tt, a, e1, fun i k => ?_, e3, e4, e5, e6⟩
  have := pA.toIsPowGrp.hom k
  rw [← hoA, ← Category.assoc, e2 i]
  exact MonObj.one_comp _

theorem main : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → RPointT := by
  intro h1 h2 h3 h4 h5 hT E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hFT P hP hy ϖ hϖ Q hQ F _ _ _ _ _ _ v hv I Φ M0 r b hΦ hb hbw n D' A' G' _ _ pD pA pG U' PU _ oD' hx hoD hn
    α N Dg hα hcop hu hN hM θ θα hθ hθF hθα J _ Pi a ha hdeg f hf gm hval
  let _ := io.toAlgebra
  have hN1 : 1 ≤ 1 * N := by omega
  obtain ⟨s, σ', g, lam, hs, hσ', hg, -, ⟨ρl, hlam, hρl⟩, hjet⟩ :=
    GlobalTheory.T.jets_on_copies_of_compatible_frames h1 h2 h4 hT E H Dw l Xo c (fun _ => rfl) T io y hy C hFT P ϖ hϖ Q hQ Φ M0 r b hΦ hb hbw n hn D' A' G'
      pD pA pG U' PU F v hv (1 * N) Dg (by omega) (by rwa [Nat.one_mul]) f hf
  obtain ⟨m, p, x, w, ζ, t, cf, e1, e2, e3, e4, e5, e6⟩ := span_pow h1 h2 h3 h4 h5 hT T.V E H C.I.G P Dw ϖ hϖ Q hQ F v hv I
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
  obtain ⟨i, j, ρ, hρ, hle⟩ := exists_term_le v a cf _ ha e5 (ρl + gm)
    (k4.symm.trans (by rw [WithTop.coe_add]; exact congrArg _ hval))
  obtain ⟨t₀, ht₀, ht⟩ := e4 j
  refine ⟨i, p j, w j, ζ j, x j, t₀, t j, σ j, h j, ρ, (e3 j).1, (e3 j).2.1, (e3 j).2.2, e1 j, e2 j, ht₀, ht, hσ j,
    (hiff F _ _ _).2 (hh j), hρ, ?_⟩
  rw [Nat.one_mul] at hρl
  have : (ρ : ℝ) ≤ ρl + gm := by exact_mod_cast hle
  linarith

end GlobalTheory.SmallTranslate
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowDescent

theorem eq_famCast_of_heq {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k k' : ℕ} (e : k = k') (r : Fam Dp F k') (s : Fam Dp F k) (h : HEq r s) :
    r = famCast e s := by
  subst e
  exact eq_of_heq h

theorem descent_cast (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V))
    (P : PELUnif (maximalIdeal V) t) (hP : P.TorsionIso) :
    letI := H.starRing
    ∀ (a a' : 𝓞 E) (g g' k : ℕ) (e : 1 * g' = k), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' →
      a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1)
      (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα →
    ∀ (pb : QkPt P.D.toPre F (1 * g'))
      (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g'))))
      (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')),
      P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 →
      FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ →
      Fam.IsSmul P.D.toPre F ζb tb₀ tb →
    ∀ (p : QkPt P.D.toPre F (k * g))
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (k * g))))
      (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (k * g) p w ζ →
      P.ToA F (k * g) p x → x ≫ P.oA.act (star a) = 1 →
    ∀ (s₂ t₀ r : Fam P.D.toPre F (k * g)), PullAl P.D F P.oD a k g (famCast (Dp := P.D.toPre) (F := F) e tb) s₂ →
      PhiRel P.D.toPre F (k * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r →
    ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g)))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))),
      PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧
      x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧
      PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  letI := H.starRing
  intro a a' g g' k e
  subst e
  exact descent_one_generator hL hL2 hL4 hT V E H t P hP a a' g g'

theorem descentIdF_of_laws :
    Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → DescentIdF := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c n
  letI := H.starRing
  intro T io y _ C P _ g g' hg hg' hne _ _ π π' hπ hπ' _ _ _ F _ _ _ _ _ _ v ϖ _ _ Q _ D' A' G' gr cm pD pA pG U' PU
    md oD' hx hoD oA' hoA θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb p w ζ x hw hζ hf hpx hxπ
    s₂ t₀ r hs₂ hΦ hr
  obtain ⟨oA'', hoA'', t', P', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    exists_pelUnif_of_unifPow hL hL2 hL4 hT T.V E H C.I.G P n D' A' G' pD pA pG U' PU oD' hx hoD
  have hact : ∀ a, oA'.act a = oA''.act a := fun a =>
    Fan.IsLimit.hom_ext pA.lim _ _ fun i => (hoA a i).trans (hoA'' a i).symm
  have hxa : x ≫ oA''.act (star (star π)) = 1 := by
    refine Fan.IsLimit.hom_ext pA.lim _ _ fun i => ?_
    have := pA.hom i
    change (x ≫ oA''.act (star (star π))) ≫ pA.pr i = 1 ≫ pA.pr i
    rw [star_star, Category.assoc, hoA'', hxπ, MonObj.one_comp]
  have htors : P'.TorsionIso :=
    GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨hL, hL2, hL3, hL4, hL5⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
      (twisting_statements_of_laws hL hT).1 (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H T.V (maximalIdeal T.V)
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t' P'
  rw [hact] at hxba
  simp only [hact]
  clear hoA hact hoA'' hxπ hx hoD PU pD pA pG
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
    descent_cast hL hL2 hL4 hT T.V E H t' P' htors (star π) (star π') g g' g' (one_mul g') hg.one_le hg'.one_le
      ((Nat.coprime_primes hg hg').2 hne) (by rw [star_star, _root_.mul_comm, hπ])
      (by rw [star_star, _root_.mul_comm, hπ']) F θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
      p w ζ x hw hζ hf hpx hxa s₂ t₀ r hs₂ hΦ hr
  exact ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, eq_famCast_of_heq _ _ _ k₉⟩

end GlobalTheory.PowDescent
end

section

namespace GlobalTheory.PointwiseBound

noncomputable section

section Wave

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants

theorem uInv_eq_zero {Y Z : Type} [AddCommGroup Z] [Module ℂ Z] (s : ℂ) (g : Y) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → Y → Z) (e : Wd.Ix (Fin w.length)),
      (∀ a, x a g = 0) → KB.uInv s w x e g = 0
  | [], _, e, h => h e
  | l :: w, x, e, h => by
    have h0 := uInv_eq_zero s g w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ) (fun a => h _)
    have h1 := uInv_eq_zero s g w (fun e' => x (Fin.cons 1 e')) (fun a => e a.succ) (fun a => h _)
    simp only [KB.uInv]
    by_cases h : e 0 = 0
    · simp only [if_pos h]
      exact h0
    · simp only [if_neg h, Pi.add_apply, Pi.smul_apply]
      rw [h0, h1, smul_zero, add_zero]

theorem waveG_cptCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, KB.CptCoef Bs (x e))
    (e : Wd.Ix (Fin w.length)) : KB.CptCoef Bs (KB.waveG Bs s w x e) := by
  obtain ⟨ε, hε, hn⟩ := PBL.nv_of_cv (Bs := Bs) (x := x) hx
  have hw := PBFV.waveG_nice Bs ε s w x hn e
  refine ⟨hw.1, ?_, ε, hε, hw.2.2⟩
  choose R hR using fun a => (hx a).2.1
  refine ⟨∑ a, |R a|, fun g hg hne => ?_⟩
  by_cases h0 : ∀ a, x a g = 0
  · exact absurd (by simp only [KB.waveG]; rw [uInv_eq_zero s g w x e h0, smul_zero]) hne
  · push Not at h0
    obtain ⟨a, ha⟩ := h0
    exact ((hR a g hg ha).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun a => |R a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))

theorem waveIsometry_of_radial (hRad : JC.RadialModuleForm) : KB.VIsoCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' hx hx'
  refine ⟨waveG_cptCoef _ s w x hx, ?_⟩
  obtain ⟨ε, hε, a, b, -⟩ := PBL.exists_norm_bound_three_families (Bs := p.T.bs j) (x := x) (y := x') (z := x) hx hx' hx
  exact GlobalTheory.WaveIsometry.isometry_of_bounded hRad hP Wp Wq P p j hj w hw s x x' ε hε a b
    (fun e => (hx e).2.1) (fun e => (hx' e).2.1) (fun e => (waveG_cptCoef _ s w x' hx' e).2.1)

end Wave

section Extension

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem extension_at_zero (hXi : B.XiExists) (hP : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) : TBB.HeadContinuityAtZero p nn F Y N := by
  intro j hj h hh w hw hN
  obtain ⟨φ, hφc, hφi, hφ, -⟩ := PBO.pStd_cpt_of_parts hP (FormsFromXi.radHead hXi) head_top
    (FormsFromXi.form_const_one hXi) exists_zeta_normalized_haar Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  refine ⟨fun c => ((A / TBB.normC nn w : ℝ) : ℂ) * φ c, continuous_const.mul hφc, hφi.const_mul _, ?_⟩
  intro c hc
  simp only
  rw [hφ c hc]
  have hA : 0 ≤ A := Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.NP
  rw [hn]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      push_cast
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    push_cast
    ring

end Extension

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants NumberField MeasureTheory
open scoped ComplexOrder

end

end GlobalTheory.PointwiseBound
end
