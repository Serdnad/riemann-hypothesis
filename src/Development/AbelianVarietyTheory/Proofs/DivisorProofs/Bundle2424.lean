module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle333
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.NumPt

theorem jet_real {f m r t b g dF R : ℝ} (hf0 : 0 ≤ f) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r) (hd0 : 0 ≤ dF)
    (ht : 11 ≤ t) (hf : f ≤ t) (hm : m ≤ t) (hr : r ≤ t) (hb : t ^ 7 ≤ b) (hd : dF ≤ f * r * (2 * (2 * b) + 1))
    (hR : R ≤ b) (hg : b ^ 8 ≤ g) :
    4 * dF + 4 ≤ g ∧ dF * (2 * Real.sqrt (2 * f * m)) < g ∧
      R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) / g ≤ 1 / 2500 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hp : ∀ n : ℕ, n ≤ 7 → t ^ n ≤ b := fun n hn => (pow_le_pow_right₀ ht1 hn).trans hb
  have h100 : 100 ≤ b := by nlinarith [hp 2 (by norm_num)]
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hfr : f * r ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hr hr0 (by linarith)
  have hfm : f * m ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hm hm0 (by linarith)
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have h5 : 5 * t ^ 2 ≤ b := by
    have : t ^ 3 = t * t ^ 2 := by ring
    nlinarith [hp 3 (by norm_num)]
  have hdb : dF ≤ b ^ 2 := by
    have h1 : f * r * (2 * (2 * b) + 1) ≤ t ^ 2 * (5 * b) := mul_le_mul hfr (by linarith) (by linarith) ht2
    nlinarith
  have hN0 : 0 ≤ 2 * f * m := by positivity
  have hN : 2 * f * m ≤ b := by nlinarith
  have hN3 : (2 * f * m) ^ 3 ≤ b := by
    have h1 : (2 * f * m) ^ 3 ≤ (2 * t ^ 2) ^ 3 := pow_le_pow_left₀ hN0 (by linarith) 3
    have h2 : t ^ 7 = t * t ^ 6 := by ring
    have h3 : (2 * t ^ 2) ^ 3 = 8 * t ^ 6 := by ring
    have h4 : 0 ≤ t ^ 6 := by positivity
    nlinarith
  have hrb : r ≤ b := hr.trans (by simpa using hp 1 (by norm_num))
  have hs : Real.sqrt (2 * f * m) ≤ b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : ∀ n : ℕ, 100 * b ^ n ≤ b ^ (n + 1) := fun n => by
    rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_left h100 (by positivity)
  have e2 : 1 ≤ b ^ 2 := one_le_pow₀ hb1
  have q2 := hq 2
  have q3 := hq 3
  have q4 := hq 4
  have q5 := hq 5
  have q6 := hq 6
  have q7 := hq 7
  norm_num at q2 q3 q4 q5 q6 q7
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 : dF * (2 * Real.sqrt (2 * f * m)) ≤ b ^ 2 * (2 * b) :=
      mul_le_mul hdb (by linarith) (by positivity) (by positivity)
    have h2 : b ^ 2 * (2 * b) = 2 * b ^ 3 := by ring
    linarith
  · rw [div_le_iff₀ (by linarith)]
    have h1 : r * (2 * f * m) ≤ b ^ 2 := by rw [sq]; exact mul_le_mul hrb hN hN0 (by linarith)
    have h2 : dF ^ 2 ≤ b ^ 4 := by
      have := pow_le_pow_left₀ hd0 hdb 2
      rwa [← pow_mul] at this
    have h3 : R * (2 * f * m) ^ 3 ≤ b * b := mul_le_mul hR hN3 (by positivity) (by linarith)
    have h4 : R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) ≤ b * b * (3 * b ^ 4) :=
      mul_le_mul h3 (by linarith) (by positivity) (by positivity)
    have h5 : b * b * (3 * b ^ 4) = 3 * b ^ 6 := by ring
    linarith

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

theorem jetNum_of_sizes {D : D7} {L : SizeData₂ D} (S : SizesAt L) {dF : ℕ}
    (hd : (dF : ℝ) ≤ D.R.f * D.R.r * (2 * (2 * L.sc.b) + 1)) : JetNum D dF (1 / 2500) := by
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := D.R.two_le_m
  have a2 := D.R.m_add_three_le_k
  have a3 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have a4 : D.R.f ≤ D.R.k := D.R.f_le_k
  have a5 : D.R.k ≤ D.R.r ∧ D.R.m ≤ D.R.r ∧ 6 ≤ D.R.r := by unfold Ranks.r; omega
  have ht : (11 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 11 ≤ D.R.t)
  have hf : (D.R.f : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.f ≤ D.R.t)
  have hm : (D.R.m : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.m ≤ D.R.t)
  have hr : (D.R.r : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.r ≤ D.R.t)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : D.host.rdE ≤ szCond L := by
    unfold szCond
    have h0 : (0 : ℝ) ≤ D.host.QS := Nat.cast_nonneg _
    have : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.QS * ((D.host.q : ℝ) * D.host.d) :=
      mul_le_mul_of_nonneg_left hs h0
    nlinarith [mul_nonneg h0 (Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d))]
  have hc1 : (1 : ℝ) ≤ szCond L := h1.trans hc
  have ht1 : (1 : ℝ) ≤ D.R.t := by linarith
  have sC' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b := le_trans sC hsb
  have hb : (D.R.t : ℝ) ^ 7 ≤ L.sc.b :=
    ((pow_le_pow_right₀ ht1 (by norm_num)).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1))).trans sC'
  have hrd : D.host.rdE ^ 2 ≤ L.sc.b :=
    (((pow_le_pow_left₀ (by linarith) hc 2).trans (pow_le_pow_right₀ hc1 (by norm_num))).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1))).trans sC'
  have hR : rr0 D ≤ L.sc.b := by
    have hn1 : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
    have e : |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) = D.host.rdE ^ 2 := by
      unfold Formalism.BasicNotions.Host.rdE
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    unfold rr0
    rw [e]
    exact (div_le_self (by positivity) (by linarith)).trans hrd
  intro k
  have hg : L.sc.b ^ 8 ≤ (D.host.g k : ℝ) :=
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  obtain ⟨c1, c2, c3⟩ := jet_real (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht hf hm hr hb hd hR hg
  exact ⟨by exact_mod_cast c1, c2, c3⟩

section Cols

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) :
    D.mult τ + D.mult (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) = D.p + D.q :=
  _root_.GlobalTheory.ConjugateMultiplicitySum.mult_add_mult_conj D τ

theorem two_mul_rank_le_nCol (Dw : Datum H) : 2 * (Dw.p + Dw.q) ≤ nCol Dw := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h := mult_add_mult_conj Dw τ
  have hle : ∀ σ, Dw.mult σ ≤ Fintype.card (Lt1 Dw) := fun σ => by
    have := Fintype.card_le_of_injective (fun i : Fin (Dw.mult σ) => (⟨σ, i⟩ : Lt1 Dw))
      (@sigma_mk_injective _ (fun τ => Fin (Dw.mult τ)) σ)
    rwa [Fintype.card_fin] at this
  have h1 := hle τ
  have h2 := hle (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ)
  unfold nCol
  omega

end Cols

theorem log_g_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hL : 1 ≤ L.sc.L) (hf : 1 ≤ D.R.f) (hr : 1 ≤ D.R.r) :
    Real.log (D.host.g 0) + Real.log (D.host.g 1) ≤ (2 + 2 * P.CYL) * zBase L ^ 12 := by
  obtain ⟨Y, h1, -, h3, h4⟩ := P.g_Y
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 0 < D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hg : ∀ i, Real.log (D.host.g i) ≤ L.sc.L + P.CYL * L.sc.L := fun i => by
    have a := Real.log_le_log (hY.trans_le (h4 i).1) (h4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have := Real.log_two_lt_d9
    linarith
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hZ : L.sc.L ≤ zBase L := le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf' hr')
  have hZ' : L.sc.L ≤ zBase L ^ 12 := hZ.trans (le_self_pow₀ (hL.trans hZ) (by norm_num))
  have := mul_le_mul_of_nonneg_left hZ' (show 0 ≤ 2 + 2 * P.CYL by linarith [P.CYL_pos])
  linarith [hg 0, hg 1]

end GlobalTheory.RefSum.NumPt
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OneKernelSpan

theorem inCoefLat_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (h h' : GA D (Vc D i)) (γ : GQ (Vc D i)) (k : Bridge.Gf (Vc D i)), k ∈ dataLevel R i Q → fin (Vc D i) h = Bridge.ratF (Vc D i) γ * fin (Vc D i) h' * k → ∀ w, InCoefLat R i h w → InCoefLat R i h' ((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i Q h h' γ k hk e w hw
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  refine ⟨gramR, c0R, c0L, hT, ?_⟩
  have hst : Formalism.UG.bc (swapAE D) (k : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) := Formalism.L2.DIV.parLev_St hk.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl (fin (Vc D i) h') k hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  refine ⟨P', hP', ?_⟩
  have h1 := (hT.mapL i).1 γ γE hγ P'
  change (R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) (c0L i ((rhoVr (labLL D) (lamV D i) γE) P')) = c0L i P'
  rw [h1]
  change ((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) * (R.cV i).ρ (γ : GA D (Vc D i))) (c0L i P') = c0L i P'
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem pt_theta_of_kerDat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    {i : Fin D.R.m} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (hK : KerDat R i ξ χ ξR Q ω φ)
    (P : PolF D (Wc D i).rank (Vc D i).rank) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ P) := by
  have hθ : IsInfFam R.θ := hR.models.inf
  have hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hK.vec
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hK.weil hθ (fun _ => 1) (fun _ => 1) (R.BV i) _
      (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) _ 1 1
      (fun τ => by rw [Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one, Matrix.one_mul]) (fun _ => rfl) (fun _ => rfl) _ hφ P).1

theorem series_rat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ γ ∈ GQ (Vc D i), ∀ h w, singleSeries R i ω φ (γ * h) w = singleSeries R i ω φ h w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK γ hγ h w
  funext v g
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).1 γ hγ 1 (one_mem _) h g
  rw [one_mul] at this
  exact this

theorem series_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ κ ∈ GfC (Vc D i), fin (Vc D i) κ ∈ dataLevel R i Q → ∃ z : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ ∀ h w, singleSeries R i ω φ (h * κ) w = D.what₂.embLL z • singleSeries R i ω φ h w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK hval κ hκ hk
  obtain ⟨h1, -⟩ := GlobalTheory.T.thetaKernel_vector_moved_by_rootsOfUnity D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK hval
  obtain ⟨z, n, hn, hz, hzω⟩ := h1 κ hκ hk
  refine ⟨z, ⟨n, hn, hz⟩, fun h w => ?_⟩
  funext v g
  have hom := GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hR.models.inf hK.weil _ _ _ _ _
    (pt_theta_of_kerDat hR hK) κ hκ 1 (one_mem _) _ hzω (R.ioP i (PiTensorProduct.tprod ℂ v) w)
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).2 κ 1 _ hom h g
  rw [mul_one] at this
  exact this

theorem series_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (h u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ w, singleSeries R i ω φ (h * u) w = singleSeries R i ω φ h ((R.cV i).ρ u w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK h u hu w
  funext v g
  unfold singleSeries Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, GlobalTheory.T.weilAction_kernel_eq_base_on_realUnitaryPoints D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK u hu _ (pt_theta_of_kerDat hR hK _),
    GlobalTheory.T.realPoints_act_fock_vectors_any_datum D G Pl0 T0 A Ks R F hR i ξR Q φ hK.vec u hu]



theorem kernelSpanOverClasses_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ), KernelSpanOverClasses R i U ψ ph v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i v hv hmu hval U ψ ph ω φ hk Cl h hh
  obtain ⟨χ, ξR, hK⟩ := GlobalTheory.T.baseTuple_thetaKernel_tameCharacter D G Pl0 T0 A Ks R F hR i v hv hmu ω φ hk
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.iUnion_subset fun c x hx => ?_))
  · rintro x ⟨g, hg, w, hw, hx⟩
    obtain ⟨c, ⟨γA, hγA⟩, k, e⟩ := hh.2 (fin (Vc D i) g)
    obtain ⟨κ, hκ, hκe⟩ := GlobalTheory.TraceIncl.KernLaws.exists_finite_lift (Vc D i) (k : Bridge.Gf (Vc D i))
    obtain ⟨u, hu_def⟩ : ∃ u : GA D (Vc D i), u = κ⁻¹ * ((h c)⁻¹ * (γA⁻¹ * g)) := ⟨_, rfl⟩
    have e1 : fin (Vc D i) g = fin (Vc D i) (γA * h c * κ) := by
      refine e.trans ?_
      rw [← GlobalTheory.TraceIncl.KernLaws.fin_mul, ← GlobalTheory.TraceIncl.KernLaws.fin_mul, hκe]
      rfl
    have e2 : finHom (Vc D i) g = finHom (Vc D i) (γA * h c * κ) := congrArg Subtype.val e1
    have hu : u ∈ GinfC (Vc D i) := by
      refine MonoidHom.mem_ker.2 ?_
      rw [hu_def, map_mul, map_mul, map_mul, map_inv (finHom (Vc D i)) κ, map_inv (finHom (Vc D i)) (h c),
        map_inv (finHom (Vc D i)) γA, e2, map_mul, map_mul]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel]
    have hg' : g = γA * (h c * κ) * u := by
      rw [hu_def]
      simp only [mul_assoc, mul_inv_cancel_left]
    obtain ⟨z, ⟨n, hn, hz⟩, hzl⟩ := series_level D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK hval κ hκ (by rw [hκe]; exact k.2)
    have hρ : (R.cV i).ρ u w = (R.cV i).ρ (γA⁻¹) w := by
      have hc1 := (hR.models.cV i).1
      rw [hu_def, map_mul, Module.End.mul_apply, hc1 _ (inv_mem hκ), Module.End.one_apply, map_mul, Module.End.mul_apply,
        hc1 _ (inv_mem (hh.1 c)), Module.End.one_apply, map_mul, Module.End.mul_apply, hc1 _ hg, Module.End.one_apply]
    have key : ∀ v', singleSeries R i ω φ g w v' =
        D.what₂.embLL z • singleSeries R i ω φ (h c) ((R.cV i).ρ (γA⁻¹) w) v' := by
      intro v'
      have h1 := series_real D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK (γA * (h c * κ)) u hu w
      rw [← hg'] at h1
      have h2 := series_rat D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK γA hγA (h c * κ) ((R.cV i).ρ u w)
      have h3 := hzl (h c) ((R.cV i).ρ u w)
      rw [h1, h2, h3, hρ]
      rfl
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact zero_ne_one hz
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hn (by rw [hz]; exact isIntegral_one)
    have hx'' : z⁻¹ • x ∈ seriesAt R i U ψ ph ω φ (h c) := by
      refine ⟨_, inCoefLat_move D G Pl0 T0 A Ks R F hR i _ g (h c) ⟨γA, hγA⟩ k k.2 e w hw, fun v' => ?_⟩
      rw [adForm_smul]
      change D.what₂.embLL z⁻¹ • adForm R i x (fun ρ => v' ρ) = _
      rw [hx v', key v', map_smul, smul_comm ph, smul_smul, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_smul]
    have : x = (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) := by
      have e3 : (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) = z • (z⁻¹ • x) := rfl
      rw [e3, smul_smul, mul_inv_cancel₀ hz0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.2 ⟨c, hx''⟩))
  · obtain ⟨w, hw, hx⟩ := hx
    exact ⟨h c, hh.1 c, w, hw, hx⟩

end GlobalTheory.OneKernelSpan

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.card_rationalPoints_fixer_torusClasses_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ B : ℝ, ∀ (μ : Fin j → ℕ) (T : Finset (GAd σ J)), (∀ t ∈ T, t ∈ ratPts σ J) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ fixG σ J C → t = t') → (∀ t ∈ T, ∃ q ∈ fixG σ J C, ∃ w ∈ W, t = q * lv (tor F E fun i => (μ i : ℤ)) * w) → (T.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) := by
  first | exact @GlobalTheory.SphEis.card_ratPts_fixG_tor_le | exact GlobalTheory.SphEis.card_ratPts_fixG_tor_le | (intros; apply GlobalTheory.SphEis.card_ratPts_fixG_tor_le <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.PureAway

theorem pure_away : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (f₂ : SInf F (Fin a' × Fin (a + a'))) (φ₂ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ᶠ w in Filter.cofinite, φ₂ w = G.M'.vac w) ∧ φ₂ v = φ v ∧
      om' (g, h) (pure f φ) = pure f₂ φ₂ := by
  classical
  intro P F E _ _ _ _ _ σ B a a' G X om om' hT v g h hg hh f φ hφ hφv
  obtain ⟨S, g₁, g₂, g₃, h₁, h₂, h₃, hvS, rfl, rfl, a1, a2, b1, b2, c1, c2, c3, c4, c5, c6⟩ :=
    GlobalTheory.T.theta_local_factor_finite_place F E σ B a a' G X om om' hT v g h hg hh φ hφv
  obtain ⟨c, hc⟩ := GlobalTheory.T.theta_trivial_at_infinity_set P F E σ B a a' G X om om' hT (insert v S) g₃ h₃ c1 c2
    (fun w hw => c3 w (Finset.mem_insert.mp hw)) (fun w hw => c4 w (Finset.mem_insert.mp hw))
    (fun w hw => c5 w (fun e => hw (e ▸ Finset.mem_insert_self _ _)) (fun e => hw (Finset.mem_insert_of_mem e))) f φ hφ
    (fun w hw => c6 w (fun e => hw (e ▸ Finset.mem_insert_self _ _)) (fun e => hw (Finset.mem_insert_of_mem e)))
  obtain ⟨φ₁, hφ₁, hφ₁e, he₁⟩ := GlobalTheory.T.theta_trivial_at_finite_set P F E σ B a a' G X om om' hT S g₂ h₂ b1 b2 f φ hφ hφv
  have hφ₁v : ∀ᶠ w in Filter.cofinite, φ₁ w = G.M'.vac w := by
    filter_upwards [hφv, S.finite_toSet.compl_mem_cofinite] with w hw hwS
    rw [hφ₁e w hwS, hw]
  obtain ⟨f₂, he₂⟩ := GlobalTheory.T.archimedean_theta_local_action P F E σ B a a' G X om om' hT g₁ h₁ a1 a2 f φ₁ hφ₁ hφ₁v
  refine ⟨c • f₂, φ₁, hφ₁, hφ₁v, hφ₁e v hvS, ?_⟩
  have hmul : ((g₁ * g₂ * g₃, h₁ * h₂ * h₃) : UA σ G.V'.J × UA σ G.W.J) = (g₁, h₁) * (g₂, h₂) * (g₃, h₃) := rfl
  rw [hmul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul, he₁, map_smul, he₂]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.PureAway
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linear_weil_functional_determined_by_unramified : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) →
    GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ := by
  first | exact @GlobalTheory.WeilLinW.charW_smooth_unitary | exact GlobalTheory.WeilLinW.charW_smooth_unitary | (intros; apply GlobalTheory.WeilLinW.charW_smooth_unitary <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.triple_local_gl_embedding_theta : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (gd' : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd' : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks 1 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd') (boxFun φ₁ φ₂) (boxFun φ₁ (fun x =>
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) *
          starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x))) := by
  first | exact @GlobalTheory.DblSwap.diagR_acts | exact GlobalTheory.DblSwap.diagR_acts | (intros; apply GlobalTheory.DblSwap.diagR_acts <;> assumption)
end

section

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.exists_flatSectionValue_eq_mul_det_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ), ∃ b : c.F, b ≠ 0 ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) := by
  first | exact @GlobalTheory.FlatValue.exists_evR_mul_det | exact GlobalTheory.FlatValue.exists_evR_mul_det | (intros; apply GlobalTheory.FlatValue.exists_evR_mul_det <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.crystallineLatticeLink_of_blockData : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  first | exact @GlobalTheory.ExpLink.latticeLink_of_blockFor | exact GlobalTheory.ExpLink.latticeLink_of_blockFor | (intros; apply GlobalTheory.ExpLink.latticeLink_of_blockFor <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

theorem _root_.GlobalTheory.T.exists_cocycle_pullbackRepresentation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  first | exact @GlobalTheory.PullCocycle.exists_cocycle | exact GlobalTheory.PullCocycle.exists_cocycle | (intros; apply GlobalTheory.PullCocycle.exists_cocycle <;> assumption)
end
