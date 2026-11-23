module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqNegOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle006
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.SpanPowerMembership.LeOfEventuallyDown
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstCohomologyVanishesOfIsRelAcyclic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LimAct

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv
open ReciprocityTheory.ChartRestriction.G.TB (dAct)
open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA (dActH)

theorem exists_lim {O : Type} [CommRing O] (q : O) [IsAdicComplete (Ideal.span {q}) O] (g : ℕ → O)
    (hg : ∀ m n, m ≤ n → ∃ w, g n - g m = q ^ m * w) : ∃ L : O, ∀ n, ∃ w, L - g n = q ^ n * w := by
  have key : ∀ m n, m ≤ n → g m ≡ g n [SMOD (Ideal.span {q} ^ m • ⊤ : Submodule O O)] := by
    intro m n hmn
    obtain ⟨w, hw⟩ := hg m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨-w, by rw [← neg_sub, hw]; ring⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {q}) g (fun {m n} h => key m n h)
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨-a, by rw [← neg_sub, ← ha]; ring⟩

section Val

variable {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem isIntV_alg (o : X.O) : IsIntV (vX_vp X) (algebraMap X.O X.C o) := by
  rw [GlobalTheory.FactorDepth.isIntV_iff]; exact X.ints.map_le_one o

theorem le_v_pow_mul (N : ℕ) (o : X.O) :
    ((N : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * algebraMap X.O X.C o) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p, nsmul_one]
  have h := isIntV_alg X o
  unfold IsIntV at h
  calc ((N : ℝ) : WithTop ℝ) = (N : WithTop ℝ) := by norm_cast
    _ ≤ (N : WithTop ℝ) + vX_vp X (algebraMap X.O X.C o) := le_add_of_nonneg_right h

theorem eq_zero_of_le_v (x : X.C) (h : ∀ N : ℕ, ((N : ℝ) : WithTop ℝ) ≤ vX_vp X x) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v x : ℝ))
  have := h N
  rw [vX_vp_apply X hx, WithTop.coe_le_coe] at this
  linarith

end Val

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [inst : StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def dActXH : 𝓞 E →+* Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  dActH X.C Ch.ch.B

theorem dActX_eq (a : 𝓞 E) : dActX Ch X a = dActXH Ch X a := rfl

def entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) : X.O :=
  X.ι (coeff (Finsupp.single ((0 : Fin 1), e') 1) (Ch.actT a e))

theorem alg_entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    algebraMap X.O X.C (entO Ch X a e e') = dActX Ch X a e e' := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  rw [entO, ← X.comp]
  show _ = coeff _ (Ch.ch.B.actK X.C a e)
  unfold FB.actK
  rw [Ch.gen.1.2.1 a e, coeff_map, coeff_map]
  rfl

theorem dActX_apply (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    dActX Ch X a e e' = X.ιF (letI := io.toAlgebra; dAct T.Fr Ch.ch.B a e e') := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  show coeff _ (Ch.ch.B.actK X.C a e) = X.ιF (coeff _ (Ch.ch.B.actK T.Fr a e))
  unfold FB.actK
  rw [coeff_map, coeff_map]
  rfl

theorem dActX_mulVec_lieVec (hst : ∀ a : 𝓞 E, star a = H.bar a) (φ : 𝓞 E →+* T.V) (τ : E →+* ℂ)
    (hφ : ∀ a : 𝓞 E, algebraMap T.V T.Fr (φ a) = io (embK c τ a)) (a : 𝓞 E) (i : Fin (Dw.mult τ)) :
    (dActX Ch X a).mulVec (lieVec Ch X ⟨τ, i⟩) = jX X (φ a) • lieVec Ch X ⟨τ, i⟩ := by
  obtain rfl := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  letI := io.toAlgebra
  have h := GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ⟨τ, i⟩
  funext e
  have h3 := congrArg X.ιF (congrFun h e)

  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h3 ⊢
  simp only [dActX_apply, lieVec, jX, RingHom.comp_apply, hφ, ← Ch.gen.1.2.2.2.2.2.2]
  exact h3

end Chart

theorem cauchy_eps_mul {R V : Type} [CommRing R] [CommRing V] (φ : R →+* V) (q : R) (ε x : ℕ → R) (t : V)
    (hε : ∀ N : ℕ, (∃ z, φ (ε N) = 1 + φ q ^ N * z) ∧
      ∀ M ≤ N, ∀ a : R, (∃ z, φ a = φ q ^ M * z) → ε N * a ∈ Ideal.span {q ^ M})
    (hx : ∀ N : ℕ, ∃ z, φ (x N) = t + φ q ^ N * z) (m n : ℕ) (hmn : m ≤ n) :
    ∃ w, ε n * x n - ε m * x m = q ^ m * w := by
  have hstep : ∀ N, ε (N + 1) * x (N + 1) - ε N * x N ∈ Ideal.span {q ^ N} := by
    intro N
    obtain ⟨z0, hz0⟩ := hx N
    obtain ⟨z1, hz1⟩ := hx (N + 1)
    obtain ⟨u0, hu0⟩ := (hε N).1
    obtain ⟨u1, hu1⟩ := (hε (N + 1)).1
    have ha : ε N * (x (N + 1) - x N) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨φ q * z1 - z0, by rw [map_sub, hz0, hz1]; ring⟩
    have hb : ε (N + 1) * (1 - ε N) ∈ Ideal.span {q ^ N} :=
      (hε (N + 1)).2 N (Nat.le_succ N) _ ⟨-u0, by rw [map_sub, map_one, hu0]; ring⟩
    have hc : ε N * (1 - ε (N + 1)) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨-(φ q * u1), by rw [map_sub, map_one, hu1]; ring⟩
    have e : ε (N + 1) * x (N + 1) - ε N * x N =
        ε N * (x (N + 1) - x N) + (ε (N + 1) * (1 - ε N) - ε N * (1 - ε (N + 1))) * x (N + 1) := by ring
    rw [e]
    exact Ideal.add_mem _ ha (Ideal.mul_mem_right _ _ (Ideal.sub_mem _ hb hc))
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨0, by ring⟩
  | succ n hmn ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 (hstep n)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact ⟨w + q ^ k * w', by linear_combination hw - hw'⟩

end GlobalTheory.IsoTriv.LimAct

namespace GlobalTheory.IsoTriv

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv.LimAct

theorem limActSt_of_epsSt (hε : EpsSt) : LimActSt := by
  intro E _ _ _ H Dw l Xo c inst hst T io y Ch p _ X τ
  obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c τ))
  have hP : φ (p : 𝓞 E) = (p : T.V) := map_natCast φ p
  have hp0 : φ (p : 𝓞 E) ≠ 0 := by rw [hP]; exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpu : ¬ IsUnit (φ (p : 𝓞 E)) := by rw [hP]; exact not_isUnit_p X
  obtain ⟨ε, hεN⟩ := hε (𝓞 E) T.V φ (p : 𝓞 E) hp0 hpu
  refine ⟨ε, fun t x hx => ?_⟩
  have hxN : ∀ N : ℕ, ∃ z, φ (x N) = t + φ (p : 𝓞 E) ^ N * z := fun N => by
    obtain ⟨z, hz⟩ := hx N
    exact ⟨z, by rw [hP]; exact IsFractionRing.injective T.V T.Fr ((hφ (x N)).trans hz)⟩
  have hcau := cauchy_eps_mul φ (p : 𝓞 E) ε x t hεN hxN
  have hent : ∀ e e', ∃ L : X.O, ∀ N, ∃ w, L - entO Ch X (ε N * x N) e e' = (p : X.O) ^ N * w := by
    intro e e'
    refine exists_lim (p : X.O) (fun N => entO Ch X (ε N * x N) e e') fun m n hmn => ?_
    obtain ⟨w, hw⟩ := hcau m n hmn
    refine ⟨entO Ch X w e e', X.ints.hom_inj ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, alg_entO, alg_entO, alg_entO, dActX_eq, dActX_eq, dActX_eq,
      ← Matrix.sub_apply, ← map_sub, hw, ← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, Matrix.smul_apply, nsmul_eq_mul,
      Nat.cast_pow]
  choose L W hW using hent
  have hA : ∀ N e e', algebraMap X.O X.C (L e e') =
      dActX Ch X (ε N * x N) e e' + (p : X.C) ^ N * algebraMap X.O X.C (W e e' N) := by
    intro N e e'
    have h := congrArg (algebraMap X.O X.C) (hW e e' N)
    rw [RingHom.map_sub, map_mul, map_pow, map_natCast, alg_entO] at h
    linear_combination h
  refine ⟨Matrix.of fun e e' => algebraMap X.O X.C (L e e'), fun N e e' => ?_, fun i => ?_⟩
  · rw [Matrix.of_apply, hA N, add_sub_cancel_left]
    exact le_v_pow_mul X N _
  · funext e
    rw [← sub_eq_zero]
    refine eq_zero_of_le_v X _ fun N => ?_
    obtain ⟨z0, hz0⟩ := hxN N
    obtain ⟨u, hu⟩ := (hεN N).1
    obtain ⟨z, hz⟩ : ∃ z, φ (ε N * x N) = t + (p : T.V) ^ N * z :=
      ⟨z0 + u * t + (p : T.V) ^ N * u * z0, by rw [map_mul, hu, hz0, hP]; ring⟩
    have hj : ∀ r : T.V, jX X r = algebraMap X.O X.C (X.ι r) := fun r => X.comp r
    have he := congrFun (dActX_mulVec_lieVec Ch X hst φ τ (fun a => hφ a) (ε N * x N) i) e
    rw [hz, map_add (f := _), map_mul, map_pow, map_natCast] at he
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.of_apply] at he ⊢
    have key : ∑ e', algebraMap X.O X.C (L e e') * lieVec Ch X ⟨τ, i⟩ e' - jX X t * lieVec Ch X ⟨τ, i⟩ e =
        (p : X.C) ^ N * algebraMap X.O X.C
          (∑ e', W e e' N * X.ι (Ch.uvecT ⟨τ, i⟩ e') + X.ι z * X.ι (Ch.uvecT ⟨τ, i⟩ e)) := by

      simp only [hA N, add_mul, Finset.sum_add_distrib, he, map_add (f := _), map_sum, map_mul, ← hj, mul_add, Finset.mul_sum,
      mul_assoc]
      simp only [lieVec]
      ring
    rw [key]
    exact le_v_pow_mul X N _

end GlobalTheory.IsoTriv
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowDens

open Filter Topology Metric Set GlobalTheory.SUVol.DensOne
open scoped NNReal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lam_le_two_mul_tangentHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → lam s ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
  intro E _ _ _ r Ψ G hG lam _
  obtain ⟨hH, hD⟩ := tangentHaar_realSU_of_det Ψ G hG lam
  generalize tangentHaar (realSU Ψ G) (lam.map Subtype.val) = μ at hH hD ⊢
  let ι : realLie Ψ G →ₗᵢ[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    ⟨(incl Ψ G).toLinearMap, fun X => norm_incl Ψ G X⟩
  let L₀ : (Ψ → Matrix (Fin r) (Fin r) ℂ) →ₗ[ℝ]
      ((Ψ → Matrix (Fin r) (Fin r) ℂ) →L[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have he : Continuous (chartExp Ψ G hG) := continuous_chartExp Ψ G hG
  have he0 : chartExp Ψ G hG 0 = 1 := chartExp_zero Ψ G hG
  have hd : HasStrictFDerivAt (fun x => matR Ψ G (chartExp Ψ G hG x)) ι.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_chart Ψ G hG
  have hL : ContinuousAt (fun g => L₀ (matR Ψ G g)) 1 := (hL₀.comp (continuous_matR Ψ G)).continuousAt
  have hL1 : (fun g => L₀ (matR Ψ G g)) 1 = ContinuousLinearMap.id ℝ _ := by ext1 A; exact one_mul A
  have hm : ∀ g h, matR Ψ G (g * h) = (fun g => L₀ (matR Ψ G g)) g (matR Ψ G h) := fun g h => rfl
  have hn : ∀ ρ : ℝ, 0 < ρ → chartExp Ψ G hG '' ball 0 ρ ∈ 𝓝 (1 : realSU Ψ G) := fun ε hε =>
    (tendsto_iff_comap.1 ((continuous_matR Ψ G).tendsto 1))
      (eventually_mem_image Ψ G hG (ball_mem_nhds 0 hε))

  haveI : ProperSpace (realLie Ψ G) := FiniteDimensional.proper_real _
  obtain ⟨δ₀, hδ₀, hinj⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ InjOn (chartExp Ψ G hG) (closedBall 0 δ₀) := by
    obtain ⟨s, hs, ha⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
    obtain ⟨δ, hδ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hs
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    have h1 := ha x (hsub hx) y (hsub hy)
    simp only [hxy, sub_self, zero_sub, norm_neg, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] at h1
    have h2 : ‖x - y‖ ≤ 0 := by
      have h3 : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
      rw [h3] at h1
      linarith
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  have hK : MeasurableSet (closedBall (0 : realLie Ψ G) δ₀) := measurableSet_closedBall
  have hemb := ContinuousOn.measurableEmbedding hK he.continuousOn hinj
  set ν : Measure (realLie Ψ G) :=
    (μ.comap ((closedBall (0 : realLie Ψ G) δ₀).domRestrict (chartExp Ψ G hG))).map Subtype.val with hν
  have hνS : ∀ S : Set (realLie Ψ G), MeasurableSet S →
      ν S = μ (chartExp Ψ G hG '' (S ∩ closedBall 0 δ₀)) := by
    intro S hS
    rw [hν, Measure.map_apply measurable_subtype_coe hS, hemb.comap_apply]
    congr 1
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hνsub : ∀ S : Set (realLie Ψ G), MeasurableSet S → S ⊆ closedBall 0 δ₀ →
      ν S = μ (chartExp Ψ G hG '' S) := fun S hS h => by rw [hνS S hS, inter_eq_left.2 h]
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνS _ MeasurableSet.univ, univ_inter]
    exact ((isCompact_closedBall _ _).image he).measure_lt_top
  have hball : ∀ (X : realLie Ψ G) (ρ : ℝ), ‖X‖ + ρ ≤ δ₀ → ball X ρ ⊆ closedBall 0 δ₀ := by
    intro X ρ h y hy
    rw [mem_ball_iff_norm] at hy
    rw [mem_closedBall_zero_iff]
    have := norm_le_norm_add_norm_sub' y X
    linarith
  have hpos : ∀ ρ > 0, 0 < ν (closedBall (0 : realLie Ψ G) ρ) := by
    intro ρ hρ
    have h1 : ν (ball 0 (min ρ δ₀)) ≠ 0 := by
      rw [hνsub _ measurableSet_ball (hball 0 _ (by simp))]
      exact (μ.measure_pos_of_mem_nhds (hn _ (lt_min hρ hδ₀))).ne'
    exact pos_iff_ne_zero.2 fun h => h1 (measure_mono_null
      ((ball_subset_closedBall).trans (closedBall_subset_closedBall (min_le_left _ _))) h)

  have himg : ∀ (g : realSU Ψ G) (S : Set (realSU Ψ G)), μ ((fun h => g * h) '' S) = μ S := fun g S => by
    rw [image_mul_left, measure_preimage_mul]
  have hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, Formalism.BasicNotions.Examples₂.CD.QInv ν ε δ := by
    intro ε hε0 hε1
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.translate_chart_ball_distortion _ _ _ (chartExp Ψ G hG) (matR Ψ G) ι
      (fun g => L₀ (matR Ψ G g)) he he0 hd hL hL1 hm hn (1 + ε / 3) (by linarith)
    refine ⟨min (δ / 2) (δ₀ / 4), by positivity, fun X hX ρ hρ0 hρ => ?_⟩
    have hXδ : ‖X‖ < δ / 2 := lt_of_lt_of_le hX (min_le_left _ _)
    have hX4 : ‖X‖ < δ₀ / 4 := lt_of_lt_of_le hX (min_le_right _ _)
    have hρδ : ρ < δ / 2 := lt_of_lt_of_le hρ (min_le_left _ _)
    have hρ4 : ρ < δ₀ / 4 := lt_of_lt_of_le hρ (min_le_right _ _)
    have hXb : X ∈ ball (0 : realLie Ψ G) δ := mem_ball_zero_iff.2 (by linarith)
    have hκ0 : 0 < 1 + ε / 3 := by linarith
    have hκ2 : 1 + ε / 3 < 2 := by linarith
    have hcl0 : closedBall (0 : realLie Ψ G) ρ ⊆ closedBall 0 δ₀ :=
      closedBall_subset_closedBall (by linarith)
    constructor
    · have hr1 : 0 < ρ / (1 + ε / 3) := div_pos hρ0 hκ0
      have hr2 : ρ / (1 + ε / 3) < ρ := div_lt_self hρ0 (by linarith)
      have hr3 : (1 - ε) * ρ < ρ / (1 + ε / 3) := by
        rw [lt_div_iff₀ hκ0]; nlinarith [mul_pos hρ0 hε0, mul_pos (mul_pos hρ0 hε0) hε0]
      have H2 := (H X hXb (ρ / (1 + ε / 3)) ⟨hr1, by linarith⟩).2
      rw [mul_div_cancel₀ _ hκ0.ne'] at H2
      calc ν (closedBall X ((1 - ε) * ρ)) ≤ ν (ball X (ρ / (1 + ε / 3))) :=
            measure_mono (closedBall_subset_ball hr3)
        _ = μ (chartExp Ψ G hG '' ball X (ρ / (1 + ε / 3))) :=
            hνsub _ measurableSet_ball (hball X _ (by linarith))
        _ ≤ μ ((fun h => chartExp Ψ G hG X * h) '' (chartExp Ψ G hG '' ball 0 ρ)) := measure_mono H2
        _ = μ (chartExp Ψ G hG '' ball 0 ρ) := himg _ _
        _ ≤ μ (chartExp Ψ G hG '' closedBall 0 ρ) := measure_mono (image_mono ball_subset_closedBall)
        _ = ν (closedBall 0 ρ) := (hνsub _ measurableSet_closedBall hcl0).symm
    · have hr1 : 0 < (1 + ε / 3) * ρ := by positivity
      have hr2 : (1 + ε / 3) * ρ < δ := by nlinarith
      have H1 := (H X hXb ((1 + ε / 3) * ρ) ⟨hr1, hr2⟩).1
      have hsq : (1 + ε / 3) * ((1 + ε / 3) * ρ) ≤ (1 + ε) * ρ := by
        nlinarith [mul_pos (mul_pos hρ0 hε0) (by linarith : (0:ℝ) < 3 - ε)]
      calc ν (closedBall 0 ρ) ≤ ν (ball 0 ((1 + ε / 3) * ρ)) :=
            measure_mono (closedBall_subset_ball (by nlinarith))
        _ = μ (chartExp Ψ G hG '' ball 0 ((1 + ε / 3) * ρ)) :=
            hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; nlinarith))
        _ = μ ((fun h => chartExp Ψ G hG X * h) '' (chartExp Ψ G hG '' ball 0 ((1 + ε / 3) * ρ))) :=
            (himg _ _).symm
        _ ≤ μ (chartExp Ψ G hG '' ball X ((1 + ε / 3) * ((1 + ε / 3) * ρ))) := measure_mono H1
        _ = ν (ball X ((1 + ε / 3) * ((1 + ε / 3) * ρ))) :=
            (hνsub _ measurableSet_ball (hball X _ (by nlinarith))).symm
        _ ≤ ν (closedBall X ((1 + ε) * ρ)) :=
            measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hsq))
  obtain ⟨c, hc0, hct, hup, hdown⟩ := Formalism.BasicNotions.Examples₂.CD.exists_density lam ν hq hpos

  have hνt : ∀ ε : ℝ, 0 < ε → (lam.map Subtype.val) (tanBall Ψ r ε) = lam (ball 0 ε) := by
    intro ε hε
    rw [Measure.map_apply measurable_subtype_coe, preimage_tanBall Ψ G hε]
    rw [show tanBall Ψ r ε = ball (0 : Ψ → Fin r → Fin r → ℂ) ε by
      ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl]
    exact measurableSet_ball
  have hc : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) < c := by
    by_contra hcon
    rw [not_lt] at hcon
    have h34 : c < ((3 / 4 : ℝ≥0) : ℝ≥0∞) :=
      lt_of_le_of_lt hcon (by rw [ENNReal.coe_lt_coe]; norm_num)
    obtain ⟨δ₁, hδ₁, H1⟩ := hup (3 / 4) h34
    obtain ⟨t, ht1, htn⟩ : ∃ t : ℝ, 1 < t ∧ t ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 := by
      have h := ((continuous_pow (Module.finrank ℝ (realLie Ψ G))).tendsto (1 : ℝ)).eventually
        (gt_mem_nhds (show (1 : ℝ) ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 by norm_num))
      have h' : ∀ᶠ x in 𝓝[>] (1 : ℝ), x ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 :=
        h.filter_mono nhdsWithin_le_nhds
      obtain ⟨t, h1, h2⟩ := (h'.and self_mem_nhdsWithin).exists
      exact ⟨t, h2, h1⟩
    have ht0 : 0 < t := by linarith
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ (grpBall (realSU Ψ G) ε) / (lam.map Subtype.val) (tanBall Ψ r ε) ≤
        ((3 / 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t ^ Module.finrank ℝ (realLie Ψ G)) := by
      filter_upwards [chart_squeeze Ψ G hG ht1,
        Ioo_mem_nhdsGT (show 0 < min δ₁ δ₀ / t by positivity)] with ε hsq hε
      obtain ⟨hε0, hε1⟩ := hε
      have hte : t * ε < min δ₁ δ₀ := by rw [mul_comm]; exact (lt_div_iff₀ ht0).1 hε1
      rw [lt_min_iff] at hte
      rw [hνt ε hε0]
      refine ENNReal.div_le_of_le_mul ?_
      calc μ (grpBall (realSU Ψ G) ε) ≤ μ (chartExp Ψ G hG '' ball 0 (t * ε)) := measure_mono hsq.2
        _ = ν (ball 0 (t * ε)) :=
            (hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; linarith))).symm
        _ ≤ ((3 / 4 : ℝ≥0) : ℝ≥0∞) * lam (ball 0 (t * ε)) := H1 _ (ball_subset_ball hte.1.le)
        _ = _ := by rw [Measure.addHaar_ball_mul_of_pos lam 0 ht0 ε, mul_assoc]
    have h1 := le_of_tendsto hD hev
    have h2 : ((3 / 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t ^ Module.finrank ℝ (realLie Ψ G)) < 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_one]
      push_cast
      linarith
    exact absurd h1 (not_le.2 h2)
  obtain ⟨δ₂, hδ₂, H2⟩ := hdown 2⁻¹ hc
  refine ⟨min δ₂ δ₀, lt_min hδ₂ hδ₀, fun s hs hsub => ?_⟩
  have h1 := H2 s (hsub.trans (ball_subset_ball (min_le_left _ _)))
  have h2 : ν s = μ (chartExp Ψ G hG '' s) :=
    hνsub s hs (hsub.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall))
  rw [← h2]
  have h22 : (2 : ℝ≥0∞) * ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.coe_inv two_ne_zero]
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  calc lam s = 2 * (((2⁻¹ : ℝ≥0) : ℝ≥0∞) * lam s) := by rw [← mul_assoc, h22, one_mul]
    _ ≤ 2 * ν s := by gcongr

end GlobalTheory.CovTop.VolUp.LowDens
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → CompactSpace X → GlobalTheory.CxForm.IsRelAcyclic f f M → GlobalTheory.AbLaw.FirstCohomologyVanishes M := by
  first
  | exact @_root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic
  | exact _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic
  | (apply _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic ..)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.delOperator_dbarOperator_pullback_constantForm_holomorphic : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U → DifferentiableOn ℂ τ U →
    ∀ v ∈ U, delAt (fun x => pull (fderiv ℂ τ x) γ) v = 0 ∧ dbarAt (fun x => pull (fderiv ℂ τ x) γ) v = 0 := by
  first | exact @GlobalTheory.CxForm.PullDelClosed.delAt_dbarAt_pull_fderiv | exact GlobalTheory.CxForm.PullDelClosed.delAt_dbarAt_pull_fderiv | (intros; apply GlobalTheory.CxForm.PullDelClosed.delAt_dbarAt_pull_fderiv <;> assumption)
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.holomorphicDel_pullback_fderiv_form_eq_zero : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ γ : GlobalTheory.CxForm.Alt n, GlobalTheory.CxForm.delAt (fun w => GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) v = 0 := by
  first | exact @GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv | exact GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv | (intros; apply GlobalTheory.CxForm.DelVanish.delAt_pull_fderiv <;> assumption)
end

end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox : EpsSt → LimActSt := by
  first | exact @GlobalTheory.IsoTriv.limActSt_of_epsSt | exact GlobalTheory.IsoTriv.limActSt_of_epsSt | (intros; apply GlobalTheory.IsoTriv.limActSt_of_epsSt <;> assumption)

end
end
