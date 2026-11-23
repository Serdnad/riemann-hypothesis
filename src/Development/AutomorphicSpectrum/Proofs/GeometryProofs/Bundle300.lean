module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicElementHomogRelation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle083
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginDegreeCount
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle161
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030

@[expose] public section

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.OffForm

open AlgebraicGeometry CategoryTheory MvPolynomial GlobalTheory.CompanionTheory.Ar.Small.RepAt GlobalTheory.CompanionTheory.Ar.AlgPoly

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → ℂ}

theorem valAt_ratio (hw : CoordsAt ξ y z w) (c : ∀ k, J k) (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (p : Σ k, J k) :
    ValAt ξ z (y p / y ⟨p.1, c p.1⟩) (w p / w ⟨p.1, c p.1⟩) := by
  obtain ⟨k, i⟩ := p
  obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (hc k)).2 i
  show ValAt ξ z _ (w ⟨k, i⟩ / w ⟨k, c k⟩)
  rw [e, mul_div_cancel_right₀ _ (hc k).ne_zero]
  exact hr

theorem valAt_aeval (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (g : MRing J) :
    ValAt ξ z (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g)
      (aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) g) := by
  induction g using MvPolynomial.induction_on with
  | C n => simpa using valAt_intCast hz n
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact valAt_add ha hb
  | mul_X a p ha =>
    rw [map_mul, map_mul, aeval_X, aeval_X]
    exact valAt_mul ha (valAt_ratio hw c hc p)

theorem aeval_form_ratio {L : Type} [Field L] (v : (Σ k, J k) → L) (c : ∀ k, J k) (hv : ∀ k, v ⟨k, c k⟩ ≠ 0)
    {G : MRing J} {d : K → ℕ} (hG : IsMultiHomog G d) :
    aeval v G = aeval (fun p : Σ k, J k => v p / v ⟨p.1, c p.1⟩) G * ∏ k, v ⟨k, c k⟩ ^ d k := by
  have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled_homog (fun p : Σ k, J k => v p / v ⟨p.1, c p.1⟩)
    (fun k => v ⟨k, c k⟩) hG
  rw [← h]
  congr 2
  funext p
  exact (div_mul_cancel₀ _ (hv p.1)).symm

theorem unitAt_of_valAt (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (ha : ValAt ξ z a r) (hr : r ≠ 0) :
    unitAt ξ ⟨centre z, hz⟩ a := by
  obtain ⟨h, s, hs, hsr⟩ := valAt_iff.1 ha
  have hu : IsUnit s := GlobalTheory.CompanionTheory.Ar.CxVal.isUnit _ (by rw [show (Scheme.stalkClosedPointTo z).hom s = r from hsr]; exact hr)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  have e : a * genMap ξ ⟨centre z, hz⟩ t = 1 := by
    have := congrArg (genMap ξ ⟨centre z, hz⟩) ht
    rwa [map_mul, map_one, hs] at this
  refine ⟨left_ne_zero_of_mul_eq_one e, ⟨s, hs⟩, ⟨t, ?_⟩⟩
  exact eq_inv_of_mul_eq_one_right e

theorem unitAt_div {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a / b) := by
  refine ⟨div_ne_zero ha.1 hb.1, ?_, ?_⟩
  · rw [div_eq_mul_inv]
    exact mul_mem ha.2.1 hb.2.2
  · rw [inv_div, div_eq_mul_inv]
    exact mul_mem hb.2.1 ha.2.2

theorem unitAt_of_forms (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {d : K → ℕ} {G Hf : MRing J} (hG : IsMultiHomog G d) (hH : IsMultiHomog Hf d)
    {ε : Ω} (hHy : aeval y Hf ≠ 0) (hGy : aeval y G = ε * aeval y Hf) (hGw : aeval w G ≠ 0) (hHw : aeval w Hf ≠ 0) :
    unitAt ξ ⟨centre z, hz⟩ ε := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hw0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have uG := unitAt_of_valAt hz (valAt_aeval hz hw c hc G) (by
    intro h0
    apply hGw
    rw [aeval_form_ratio w c hw0 hG, h0, zero_mul])
  have uH := unitAt_of_valAt hz (valAt_aeval hz hw c hc Hf) (by
    intro h0
    apply hHw
    rw [aeval_form_ratio w c hw0 hH, h0, zero_mul])
  have hM : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have e : ε = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G /
      aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) Hf := by
    rw [aeval_form_ratio y c hy hG, aeval_form_ratio y c hy hH, ← mul_assoc] at hGy
    have h1 := mul_right_cancel₀ hM hGy
    rw [h1, mul_div_cancel_right₀ _ uH.1]
  rw [e]
  exact unitAt_div uG uH

end GlobalTheory.CompanionTheory.Ar.Small.OffForm


open GlobalTheory.CompanionTheory.Ar.Small.OffForm in
theorem GlobalTheory.CompanionTheory.RootForm.exists_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (GlobalTheory.CompanionTheory.Ar.CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (GlobalTheory.CompanionTheory.Ar.CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), ∃ f : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) f ∧ ∀ w ∈ mcPts (mCoordIdeal RM.y), MvPolynomial.aeval w f ≠ 0 → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or
  obtain ⟨cc, hch⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  have hy : ∀ k, RM.y ⟨k, cc k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hch.1 k (Finset.mem_univ k)
  have ya : Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) = RM.y ⟨Or.k₀, cc Or.k₀⟩ := by
    rw [← Or.y_eq, Equiv.apply_symm_apply]
  have ht0 : (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _
      (smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (Or.lines r).1)
  have hε : Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ^ Fx.q' /
      (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero ((map_ne_zero Or.g).2 Fx.sE_ne) (pow_ne_zero _ ?_)) ht0
    rw [ya]
    exact hy _
  obtain ⟨d, G, Hf, hG, hH, hHy, hGy⟩ := RM.birational (Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ^ Fx.q' /
      (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)))
  have hGy0 : MvPolynomial.aeval RM.y G ≠ 0 := by
    rw [hGy]
    exact mul_ne_zero hε hHy
  have hform := GlobalTheory.CompanionTheory.Ar.AlgPoly.form_mul (GlobalTheory.CompanionTheory.Ar.AlgPoly.form_mul hG hH)
    (GlobalTheory.CompanionTheory.Ar.Small.RepAt.form_mono cc fun _ => 1)
  refine ⟨G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1), ⟨⟨_, hform⟩, fun hm => ?_⟩, fun w hw hf x hso => ?_⟩
  · have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled RM.y (fun _ => 1) (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1))
    have h0 : mConeMap RM.y (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1)) = 0 := hm
    rw [h0, map_zero] at h
    simp only [mul_one] at h
    rw [map_mul, map_mul, GlobalTheory.CompanionTheory.Ar.Small.RepAt.aeval_mono] at h
    exact mul_ne_zero (mul_ne_zero hGy0 hHy) (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)) h
  obtain ⟨cs, hcs, he⟩ := hso
  have hw' : Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have hf' : MvPolynomial.aeval (Or.Re.R.lift x x) (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1)) ≠ 0 := by
    have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled_homog w cs hform
    have e2 : Or.Re.R.lift x x = fun p => w p * cs p.1 := by
      rw [he]
      funext p
      exact mul_comm _ _
    rw [e2, h]
    exact mul_ne_zero hf (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hcs k))
  rw [map_mul, map_mul, GlobalTheory.CompanionTheory.Ar.Small.RepAt.aeval_mono] at hf'
  have hGw := left_ne_zero_of_mul (left_ne_zero_of_mul hf')
  have hHw := right_ne_zero_of_mul (left_ne_zero_of_mul hf')
  have hcc : ∀ k, IsUnit (Or.Re.R.lift x x ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hf') k (Finset.mem_univ k)
    simpa using this)
  obtain ⟨z, hz, hco⟩ := (mem_mcPts_iff_exists_coordsAt Or.𝔐.X RM.Ω Or.𝔐.ξ RM.K RM.ι RM.y Or.𝔐.tie _).1 hw'
  have hch' := GlobalTheory.CompanionTheory.Ar.Small.RepAt.inChart_of_coords hz hco cc hcc
  have gens : ∀ r, (Or.Fl.rootLat r).IsGenAt ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) :=
    fun r => ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (Or.lines r).1,
      (Or.lines r).2 _ trivial cc hch'⟩
  have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (fun r => -Fx.n r) gens
  have hchi : InChart Or.𝔐.ξ (fun i' => Or.g (Fx.yf i')) (Or.ix.symm (cc Or.k₀)) ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ := by
    refine ⟨?_, fun j => ?_⟩
    · show Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ≠ 0
      rw [ya]
      exact hy _
    · show Or.g (Fx.yf j) / Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ∈ _
      rw [ya, ← Or.y_eq]
      exact Lat.block_ratio_mem hch' Or.k₀ (Or.ix j)
  have heff := (Or.eff ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ (fun r hr => GlobalTheory.CompanionTheory.Ar.Small.RepAt.not_inFibre hz hr) _ _ hchi ht).2
  have hu := unitAt_of_forms hz hco cc hcc hG hH hHy hGy hGw hHw
  exact (Or.interior x z hco).1 (not_not.1 fun h => heff h hu)
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def phiAlg (Rd : Reading Fr h Z) : letI := Small.cstAlg Or; Om Z →ₐ[c.F] RM.Ω :=
  letI := Small.cstAlg Or
  { Rd.φ with commutes' := fun a => Rd.φ_cst a }

def Linked (Rd : Reading Fr h Z) : Prop :=
  letI := Small.cstAlg Or
  ∃ (w : FrPt Xo c RM.Ω) (t : Ix Dw → RM.Ωˣ), FrMap (phiAlg Rd) (genFr h Z) w ∧ FrBor t w Fr.y₀

def RegAt (h : GenFrEx Xo c) (Z : Comp Xo c) {L : Type} [Field L] (io : c.F →+* L) (A : Subring (Om Z))
    (ev : A →+* L) (y : letI := io.toAlgebra; FrPt Xo c L) : Prop :=
  letI := io.toAlgebra
  (∀ a : c.F, ∃ ha : algebraMap c.F (Om Z) a ∈ A, ev ⟨_, ha⟩ = io a) ∧
  ∃ (q : TRing c.F) (φ : q.R →ₐ[c.F] Om Z) (ψ : q.R →ₐ[c.F] L) (yq : FrPt Xo c q.R) (z : FrPt Xo c L)
    (t : Ix Dw → Lˣ), FrMap φ yq (genFr h Z) ∧ FrMap ψ yq z ∧ (∀ r, ∃ hr : φ r ∈ A, ψ r = ev ⟨φ r, hr⟩) ∧ FrBor t z y

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr

theorem prod_zpow_le {R : Type} [Fintype R] (S rec : R → ℝ) (n : R → ℤ) (C : ℝ) (hS : ∀ r, 0 < S r)
    (hr : ∀ r, 0 < rec r) (h : ∀ r, |Real.log (S r) - Real.log (rec r)| ≤ C) :
    ∏ r, S r ^ n r ≤ (∏ r, rec r ^ n r) * Real.exp ((∑ r, |(n r : ℝ)|) * C) := by
  have key : ∀ r ∈ (Finset.univ : Finset R), S r ^ n r ≤ rec r ^ n r * Real.exp (|(n r : ℝ)| * C) := by
    intro r _
    rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos (hS r), Real.rpow_def_of_pos (hr r),
      ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : (n r : ℝ) * (Real.log (S r) - Real.log (rec r)) ≤ |(n r : ℝ)| * C := by
      calc (n r : ℝ) * (Real.log (S r) - Real.log (rec r))
          ≤ |(n r : ℝ) * (Real.log (S r) - Real.log (rec r))| := le_abs_self _
        _ = |(n r : ℝ)| * |Real.log (S r) - Real.log (rec r)| := abs_mul _ _
        _ ≤ |(n r : ℝ)| * C := mul_le_mul_of_nonneg_left (h r) (abs_nonneg _)
    linarith
  calc ∏ r, S r ^ n r ≤ ∏ r, rec r ^ n r * Real.exp (|(n r : ℝ)| * C) :=
        Finset.prod_le_prod₀ (fun r _ => (zpow_pos (hS r) _).le) key
    _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_mul]

theorem supMet_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {𝕜 : Type} [NormedField 𝕜]
    {R : Type} [Fintype R] (n : R → ℤ) (d : R → K → ℤ) (z : (Σ k, ι k) → 𝕜)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : Small.supMet (∑ r, n r • d r) z = ∏ r, Small.supMet (d r) z ^ n r := by
  have hN : ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun (norm_eq_zero.1 h0) i)
  unfold Small.supMet
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hs : ∀ (s : Finset R), ‖fun i : ι k => z ⟨k, i⟩‖ ^ (∑ r ∈ s, n r • d r) k =
      ∏ r ∈ s, (‖fun i : ι k => z ⟨k, i⟩‖ ^ d r k) ^ n r := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Pi.add_apply, zpow_add₀ (hN k), ih]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← zpow_mul, mul_comm (n a)]
  exact hs Finset.univ

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem nefCount : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι), 1 ≤ D → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ W, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 2 → mCoordIdeal y ≤ W → 0 ≤ geomDeg W A 1) → (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω))) ∧ Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω)) : ℝ) / (τ : ℝ) ^ D) atTop (𝓝 (geomDeg (mCoordIdeal y) A D)) := by
  intro hRR hG II _ K _ ι _ Ω _ _ y D A _ hX hB hA hnef
  obtain ⟨-, -, -, -, -, -, -, -, -, hPB, -⟩ := hG
  obtain ⟨-, ⟨-, hD, -⟩, -⟩ := hPB
  have hN : GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericDeg (mCoordIdeal y) A.a := by
    intro W hW hle
    have h := hnef W hW hle
    rw [GlobalTheory.CompanionTheory.Ar.Cusp.NineEq.geomDeg_eq hD (d := 1) hW hA] at h
    exact_mod_cast h
  have e := GlobalTheory.CompanionTheory.Ar.Cusp.NineEq.geomDeg_eq hD hX hA
  rw [e]
  exact hRR K ι Ω y D A.a hX hB hN

end GlobalTheory.CompanionTheory.Ar.Plug
end
