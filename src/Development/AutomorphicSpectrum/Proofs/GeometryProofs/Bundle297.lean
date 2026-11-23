module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle049
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle216
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle105
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle091
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle069
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle183
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle296
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle256
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle192
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle059
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle134
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio

@[expose] public section

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem logCard_pow_le (x : ℕ∞) {d : ℕ} (hd : 0 < d) :
    GlobalTheory.CompHt.logCard (x ^ d) ≤ (d : ℝ≥0∞) * GlobalTheory.CompHt.logCard x := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [GlobalTheory.CompHt.logCard_top, ENNReal.mul_top (Nat.cast_ne_zero.2 hd.ne')]
    exact le_top
  | coe a =>
    have h : ((a : ℕ∞) ^ d) = ((a ^ d : ℕ) : ℕ∞) := by push_cast; rfl
    rw [h, GlobalTheory.CompHt.logCard_coe, GlobalTheory.CompHt.logCard_coe, Nat.cast_pow, Real.log_pow,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem logCard_mono {x y : ℕ∞} (h : x ≤ y) : GlobalTheory.CompHt.logCard x ≤ GlobalTheory.CompHt.logCard y :=
  EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 h))

theorem natCast_shift_pow (D j k : ℕ) (hk : 0 < k) :
    ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hj : (0 : ℝ) ≤ 1 + (j : ℝ) / k := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  congr 2
  push_cast
  field_simp

theorem tendsto_shift_ratio (D j : ℕ) :
    Tendsto (fun k : ℕ => ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1))) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => (j : ℝ) / k) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have h2 : Tendsto (fun k : ℕ => (1 + (j : ℝ) / k) ^ (D + 1)) atTop (𝓝 ((1 + 0) ^ (D + 1))) :=
    (tendsto_const_nhds.add h).pow _
  have h3 := ENNReal.tendsto_ofReal h2
  simpa using h3

theorem term_le_shift (D n d j k : ℕ) (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) {x y : ℕ∞} (h : x ≤ y ^ d) :
    (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard x / (((n * d : ℕ) : ℝ≥0∞) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1)) ≤
      (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard y / ((n : ℝ≥0∞) * ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1)) *
        ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) := by
  set A : ℝ≥0∞ := ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1) with hA
  set A' : ℝ≥0∞ := ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1) with hA'
  set c : ℝ≥0∞ := ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) with hc
  have hcA : A' = c * A := natCast_shift_pow D j k hk
  have hA0 : A ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hAt : A ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hA'0 : A' ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hA't : A' ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hd0 : (d : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hdt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hL : GlobalTheory.CompHt.logCard x ≤ (d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y :=
    (logCard_mono h).trans (logCard_pow_le y hd)
  refine ENNReal.div_le_of_le_mul ?_
  have key : (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard y / ((n : ℝ≥0∞) * A') * c * (((n * d : ℕ) : ℝ≥0∞) * A) =
      (D.factorial : ℝ≥0∞) * ((d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y) := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), Nat.cast_mul]
    calc _ = (D.factorial : ℝ≥0∞) * ((d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y) * ((n : ℝ≥0∞)⁻¹ * n) * ((A')⁻¹ * (c * A)) := by
          ring
      _ = _ := by
          rw [← hcA, ENNReal.inv_mul_cancel hn0 hnt, ENNReal.inv_mul_cancel hA'0 hA't, mul_one, mul_one]
  rw [key]
  gcongr

theorem countVol_le_of_le_shift_pow : ∀ (D n d k₀ : ℕ) (m m' : ℕ → ℕ∞), 0 < n → 0 < d → 8 ∣ k₀ →
    (∀ᶠ τ : ℕ in atTop, m τ ≤ m' (τ + k₀) ^ d) →
    GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ GlobalTheory.CompHt.countVol D n 8 m' := by
  rintro D n d _ m m' hn hd ⟨j, rfl⟩ h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  set b : ℕ → ℝ≥0∞ := fun k => (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard (m' (8 * k)) /
    ((n : ℝ≥0∞) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1)) with hb
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) with hc
  have hlim : limsup c atTop = 1 := (tendsto_shift_ratio D j).limsup_eq
  have hle : GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ limsup ((fun k => b (k + j)) * c) atTop := by
    refine limsup_le_limsup ?_
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hx : m (8 * k) ≤ m' (8 * (k + j)) ^ d := by
      have := hN (8 * k) (by omega)
      rwa [show 8 * k + 8 * j = 8 * (k + j) by ring] at this
    exact term_le_shift D n d j k hn hd (by omega) hx
  refine hle.trans ((ENNReal.limsup_mul_le' (Or.inr (by simp [hlim])) (Or.inr (by simp [hlim]))).trans ?_)
  rw [hlim, mul_one, Filter.limsup_nat_add b j]
  rfl

end GlobalTheory.CompanionTheory.Ar.Plug
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

namespace VsLaws

section Laws

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem idem_val (h : GenFrEx Xo c) (Z : Comp Xo c) :
    evC h Z (GlobalTheory.FlatLine.idem Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC h Z' (GlobalTheory.FlatLine.idem Z) = 0 := by
  obtain ⟨hL, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  exact ⟨GlobalTheory.FlatLine.evR_idem (GlobalTheory.AllWt.liesOn_genFr h Z) (hL.test _ _),
    fun Z' hZ => GlobalTheory.AllWt.evC_eq_zero h hZ (GlobalTheory.FlatLine.idem_mem_suppOn Z)⟩

theorem compLaws_of (hN : N1ab) (hN' : N1c) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hF : FnAlgClosed (Xo := Xo) (c := c))
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hT : ∀ σ, GoodEmb c σ → ∀ k x,
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x))
    (hC : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1) :
    ∃ h e', CompLaws U h e' := by
  obtain ⟨h, hgt⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hTw := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨κ, hb, -⟩ := GlobalTheory.CompBij.exists_bijection (U c.F.val.toRingHom) rfl (hU _ rfl) hF h
  refine ⟨h, GlobalTheory.FlatLine.idem, ?_⟩
  exact
    { comps := by
        rw [Nat.card_congr (Equiv.ofBijective κ hb), Nat.card_eq_fintype_card]
      ne := (GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg E H Dw l Xo c hpq).1
      genT := hgt h
      evalWD := GlobalTheory.TransferCompare.evalWD_framed _ _
      unf := hU
      unTest := hT
      chiTriv := hC
      ptNe := intFrNe_of' (GlobalTheory.T.xoNumPt_of_p_add_q_pos hN' E H Dw l Xo c hpq) GlobalTheory.locFld
        (GlobalTheory.Exist.intFrExt_of_good GlobalTheory.partI_closed hN hB hTw E H Dw l Xo c hpq hg)
      intAll := GlobalTheory.IntegralFrames.intAll GlobalTheory.partI_closed hN hB hTw E H Dw l Xo c hpq hg
      e_sec := GlobalTheory.CompRestr.idem_mem_sec
      e_val := idem_val h }

end Laws

theorem lval_congr {n m : ℕ} (h : n = m) (hn : Fact n.Prime) (hm : Fact m.Prime) (zn : NeZero n) (zm : NeZero m) :
    (deriv (DirichletCharacter.LFunction
        (((quadraticChar (ZMod n)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ n)) 1 /
      DirichletCharacter.LFunction
        (((quadraticChar (ZMod n)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ n) 1).re =
    (deriv (DirichletCharacter.LFunction
        (((quadraticChar (ZMod m)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ m)) 1 /
      DirichletCharacter.LFunction
        (((quadraticChar (ZMod m)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ m) 1).re := by
  subst h
  rfl

theorem hostLval_eq (D : D7) (Q : Par D) (h : Q.H.d = D.host.d) : hostLval Q.H = dlogL D 1 :=
  lval_congr h ⟨Q.H.d_prime⟩ ⟨D.host.hyp.2.1⟩ ⟨Q.H.d_prime.ne_zero⟩ ⟨D.host.hyp.2.1.ne_zero⟩

end VsLaws

theorem vs_laws : Top.Given → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : GlobalTheory.CovTop.Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → (∃ h e', CompLaws Y.U h e') ∧ (∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p) ∧ (T.Q.Dw j).q = D.R.m - j ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ Fintype.card (CMType T.Q.H) = D.R.f ∧ hostRd D.host.E = D.host.rdE ∧ hostLval T.Q.H = dlogL D 1 := by
  intro hG D T hT j hj1 hjm Y e o hY
  obtain ⟨⟨-, hN, hN', -⟩, -⟩ := hG
  have hI : InR D j := ⟨hj1, hjm.le⟩
  obtain ⟨hH, hLv, -, hD⟩ := hT.pins
  obtain ⟨hp, hq, -⟩ := hD j hI
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    goodAt_of_two_primes hLv.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.lev.1.2.1 hg0
  have hr1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [hpq]
    simp only [Ranks.r]
    omega
  refine ⟨VsLaws.compLaws_of hN hN' Y.U hr1 hg hY.geo hY.unf hY.unTest hY.chiTriv, hg, hq, hpq, ?_, rfl,
    VsLaws.hostLval_eq D T.Q hH.1⟩
  convert SharpLaws.card_psi D T.Q

end GlobalTheory.CompanionTheory.Ar.Plug
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug



theorem bdd_mem_cuspOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (x : ℝ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ C) → f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  intro E _ _ _ H Dw l Xo c r U h e hL hp hq x Z u hu f hf hfZ hb
  have hF : FnAlgClosed (Xo := Xo) (c := c) :=
    GlobalTheory.CompanionTheory.Ar.Rec.CompOver.fnAlgClosed_of_card (U c.F.val.toRingHom) rfl (hL.unf _ rfl) h (hL.unTest _ rfl) hL.genT
      hL.comps
  refine ⟨GlobalTheory.AllWt.mem_cuspW.2 ⟨hf, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩, hfZ⟩
  have hU := hL.unf σ hσ
  have hK : Nonempty (GlobalTheory.ShFam.KeySec Xo c) := by
    obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hU
    exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F (by omega) hF
  have hdec : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (GlobalTheory.AllWt.wtOf Dw u 0).1 (τ, j) ≤ (GlobalTheory.AllWt.wtOf Dw u 0).1 (τ, i) := by
    intro τ i j hij hj
    by_cases hτ : τ (H.rt : E) = H.rt0
    · have hjp : j < Dw.p := by simpa [Datum.mult, hτ] using hj
      have e1 := GlobalTheory.AllWt.wtOf_big u 0 ⟨τ, hτ⟩ j hjp
      have e2 := GlobalTheory.AllWt.wtOf_big u 0 ⟨τ, hτ⟩ i (by omega)
      simp only at e1 e2
      rw [e1, e2]
      have := (hu ⟨τ, hτ⟩).antitone (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨j, by omega⟩ from hij)
      omega
    · have hjq : j < Dw.q := by simpa [Datum.mult, hτ] using hj
      have hc := GlobalTheory.AllWt.conj_mem hτ
      have e1 := GlobalTheory.AllWt.wtOf_small u 0 ⟨conjEmb τ, hc⟩ j hjq
      have e2 := GlobalTheory.AllWt.wtOf_small u 0 ⟨conjEmb τ, hc⟩ i (by omega)
      simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at e1 e2
      rw [e1, e2]
      have := (hu ⟨conjEmb τ, hc⟩).antitone
        (show (⟨Dw.p + (Dw.q - 1 - j), by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from
          Fin.mk_le_mk.2 (by omega))
      omega
  have hsec := GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU _ _ _ _ _ _ σ _ (U σ) hK hσ hU (by omega) _
    (GlobalTheory.AllWt.even_wtOf u 0) hdec f hf k
  have hr := hU.1
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k

  obtain ⟨t⟩ : Nonempty (GlobalTheory.AllWt.Psi H) := by
    obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hρ : ρ (H.rt : E) = H.rt0
    · exact ⟨⟨ρ, hρ⟩⟩
    · exact ⟨⟨conjEmb ρ, GlobalTheory.AllWt.conj_mem hρ⟩⟩
  have ht : relab c σ t.1 ∈ ((U σ).X k).Ψ := by
    refine (hΨ _).2 ?_
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext t.2)).trans hσ0
  have hbig : ∀ j : Fin r, ∀ hj : Dw.q ≤ (j : ℕ), GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k ⟨_, ht⟩ j =
      u t ⟨(j : ℕ) - Dw.q, by omega⟩ := by
    intro j hj
    have hjr := j.2
    have := GlobalTheory.AllWt.modelWt_wtOf_big (U σ) u 0 k hp0 t ht ((j : ℕ) - Dw.q) (by omega) (by omega)
    rwa [show (⟨Dw.q + ((j : ℕ) - Dw.q), by omega⟩ : Fin r) = j from Fin.ext (by simp only; omega)] at this
  have hsm : ∀ j : Fin r, ∀ hj : (j : ℕ) < Dw.q, GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k ⟨_, ht⟩ j =
      u t ⟨Dw.p + (j : ℕ), by omega⟩ := fun j hj =>
    GlobalTheory.AllWt.modelWt_wtOf_small (U σ) u 0 k hp0 t ht j hj j.2
  obtain ⟨C, hC⟩ := hb σ hσ
  have hpos := GlobalTheory.AllWt.lieFacZ_pos (Dw := Dw) x (GlobalTheory.AllWt.wtOf Dw u 0)
  have hbdd : ((U σ).X k).IsBddSec (GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k) (rdU (U σ) f k) := by
    refine ⟨hsec, max (C / GlobalTheory.AllWt.lieFacZ Dw x (GlobalTheory.AllWt.wtOf Dw u 0)) 0, fun y hy => ?_⟩
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ GlobalTheory.AllWt.framesOn (U σ) Z
    · refine le_max_of_le_left ((le_div_iff₀' hpos).2 ?_)
      have h1 := hC ⟨k, y⟩ hz
      simpa only [GlobalTheory.AllWt.homN, GlobalTheory.AllWt.ptN] using h1
    · have h0 : rdU (U σ) f k y = 0 := GlobalTheory.AllWt.rdU_eq_zero (U σ) hfZ hz
      refine le_max_of_le_right (le_of_eq ?_)
      simp [Data.pnorm, h0]
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.cuspStatement_holds r _ _ ⟨_, ht⟩ (by omega) (by omega) (fun i j hij hjp => ?_)
    (fun i0 i1 h0 h1 => ?_) _ hbdd
  · have hjr := j.2
    have hir := i.2
    by_cases hjq : (j : ℕ) < Dw.q
    · rw [hsm j hjq, hsm i (by omega)]
      exact (hu t).antitone (Fin.mk_le_mk.2 (by omega))
    · have hiq : Dw.q ≤ (i : ℕ) := by omega
      rw [hbig j (by omega), hbig i hiq]
      exact (hu t).antitone (Fin.mk_le_mk.2 (by omega))
  · have hi1 := i1.2
    rw [hsm i0 (by omega), hbig i1 (by omega)]
    exact (hu t) (Fin.mk_lt_mk.2 (by omega))

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem hodge_cpt_global_nefness : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → 1 ≤ D.p → 1 ≤ D.q → ∀ (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → 2 < p → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ mu : GlobalTheory.CompanionTheory.Ar.Top.Wt (CMType H) (D.p + D.q), GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold D.p p mu → M.NefAt p mu 0 := by
  intro E _ _ _ H D Xo Yl hYl l c hg Y hdom hp1 hq1 S _ M 𝔐 Fl e hRL p hp hp2 hpS hdisc mu hmu hthr
  have hfib := (GlobalTheory.T.global_model_power_free E H D Xo Yl hYl l c hg Y hdom).2 p hp
  obtain ⟨t⟩ := GlobalTheory.T.root_lines_unramified_primes E H D l (Xo l) c Y S M 𝔐 Fl e hRL p hp hpS hdisc hfib
  exact GlobalTheory.T.rootLineDeRhamModel_holds (CMType H) (D.p + D.q) M D.p p E H t hp hp2 hp1 (by omega) mu hmu hthr

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VsReg

theorem le_exp_mul_pow_of_log_le {P r A B : ℝ} {M : ℕ} (hP : 0 < P) (hr : 1 ≤ r) (hB : B ≤ M)
    (h : Real.log P ≤ A + B * Real.log r) : P ≤ Real.exp A * r ^ M := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have h1 : Real.log P ≤ A + (M : ℝ) * Real.log r := by nlinarith
  calc P = Real.exp (Real.log P) := (Real.exp_log hP).symm
    _ ≤ Real.exp (A + (M : ℝ) * Real.log r) := Real.exp_le_exp.2 h1
    _ = Real.exp A * r ^ M := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hr0]

theorem sing_prod_le_rW_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (n : RootIx Dw → ℤ), ∀ w₀ ∈ mcPts (mCoordIdeal RM.y), ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ᶠ w in 𝓝 w₀, w ∈ mcPts (mCoordIdeal RM.y) → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' → ∏ r, (Or.sing r).h w ^ n r ≤ C * ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) ^ M := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or n w₀ hw₀
  let f : CMType H → Fin (Dw.p + Dw.q) → ℝ := fun τ i => -(n (τ, i) : ℝ)
  let cf : RootIx Dw → ℝ := fun r => GlobalTheory.CompanionTheory.Ar.Small.Fund.fundCo (f r.1) r.2
  let Bf : RootIx Dw → ℝ := fun r => |Real.log ((Or.Re.ref (some r)).h w₀)| + 1
  let T : Set ((Σ k, RM.ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  have hb : ∀ r : RootIx Dw, ∀ᶠ w in 𝓝[T] w₀, |Real.log ((Or.Re.ref (some r)).h w)| ≤ Bf r := by
    intro r
    have hc : ContinuousWithinAt (Or.Re.ref (some r)).h T w₀ :=
      (Or.Re.ref_smooth (some r)).continuousOn w₀ hw₀.1
    have hc' : ContinuousWithinAt (fun w => |Real.log ((Or.Re.ref (some r)).h w)|) T w₀ :=
      (hc.log ((Or.Re.ref (some r)).pos w₀ hw₀.1).ne').abs
    exact (hc'.tendsto.eventually (Iio_mem_nhds (lt_add_one _))).mono fun _ h => le_of_lt h
  have hall : ∀ᶠ w in 𝓝 w₀, w ∈ T → ∀ r : RootIx Dw, |Real.log ((Or.Re.ref (some r)).h w)| ≤ Bf r :=
    eventually_nhdsWithin_iff.1 (Filter.eventually_all.2 hb)
  let A : ℝ := ∑ r, |cf r| * Bf r
  let Bc : ℝ := ∑ r, |cf r| * |Sys.C₅|
  refine ⟨Real.exp A, ⌈Bc⌉₊, (Real.exp_pos _).le, ?_⟩
  filter_upwards [hall] with w hw hwm x hso hop
  have hwT : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := hwm.1
  have hbd := hw hwT

  have hsum : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h w) + Sys.ph (some (τ, i)) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((Or.sing (τ, k)).h w) := by
    intro τ i
    have e := Or.fund_sing τ i x hop
    have hdeg : (Or.Re.ref (some (τ, i))).a = -∑ k ∈ Finset.Iic i, (Or.sing (τ, k)).a := by
      rw [Or.fund_deg τ i]
      simp only [Or.sing_deg]
    have b := OrArch.log_add_sum_of_sameOrbit (Finset.Iic i) (fun k => Or.sing (τ, k)) hdeg hso hwT
    linarith
  have e2 := GlobalTheory.CompanionTheory.Ar.Small.Fund.sum_neg_mul_eq_sum_fundCo f
    (fun r => Real.log ((Or.sing r).h w))
    (fun r => Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)) hsum
  have hlog : Real.log (∏ r, (Or.sing r).h w ^ n r) =
      ∑ r : RootIx Dw, -f r.1 r.2 * Real.log ((Or.sing r).h w) := by
    rw [Real.log_prod fun r _ => zpow_ne_zero _ ((Or.sing r).pos _ hwT).ne']
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.log_zpow]
    simp [f]

  set L : ℝ := Real.log (ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x)) with hL
  have hre : Real.exp 1 ≤ ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) := by
    have := Sys.norm_le (Or.Re.π x)
    unfold ReciprocityTheory.AnForm.P.rW
    linarith
  have hr1 : 1 ≤ ReciprocityTheory.AnForm.P.rW Sys.L Sys.s (Or.Re.π x) :=
    le_trans (Real.one_le_exp zero_le_one) hre
  have hL1 : 1 ≤ L := (Real.le_log_iff_exp_le (lt_of_lt_of_le one_pos hr1)).2 hre
  have hph : ∀ r : RootIx Dw, |Sys.ph (some r) (Or.Re.π x)| ≤ |Sys.C₅| * L := by
    intro r
    obtain ⟨h1, h2⟩ := (Sys.sing (some r)).2.2.2 (Or.Re.π x) hop
    have hC : Sys.C₅ ≤ |Sys.C₅| := le_abs_self _
    have hC0 : 0 ≤ |Sys.C₅| := abs_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  have hle : Real.log (∏ r, (Or.sing r).h w ^ n r) ≤ A + Bc * L := by
    rw [hlog, e2]
    have : A + Bc * L = ∑ r, |cf r| * (Bf r + |Sys.C₅| * L) := by
      simp only [A, Bc, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [this]
    refine Finset.sum_le_sum fun r _ => ?_
    have h3 : |Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)| ≤
        Bf r + |Sys.C₅| * L := (abs_add_le _ _).trans (add_le_add (hbd r) (hph r))
    calc cf r * (Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x))
        ≤ |cf r * (Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x))| := le_abs_self _
      _ = |cf r| * |Real.log ((Or.Re.ref (some r)).h w) + Sys.ph (some r) (Or.Re.π x)| := abs_mul _ _
      _ ≤ |cf r| * (Bf r + |Sys.C₅| * L) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  exact le_exp_mul_pow_of_log_le (Finset.prod_pos fun r _ => zpow_pos ((Or.sing r).pos _ hwT) _)
    hr1 (Nat.le_ceil _) hle

end GlobalTheory.CompanionTheory.Ar.VsReg
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem splitComps_of_fnAlgClosed_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), FnAlgClosed (Xo := Xo) (c := c) → SplitComps Y :=
  fun _ _ _ _ _ _ _ _ _ Y hc => GlobalTheory.CompanionTheory.Ar.SplitEx.splitComps_of_fnAlgClosed Y hc

end GlobalTheory.CompanionTheory.Ar.Plug
end
