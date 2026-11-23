module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSection
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle024
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle024
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnVal.genRd_const : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (Λ : K → (Fin N → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Ga : AddSubgroup (Fin N → ℂ)), IsHolFam q → (∀ z k, q z ≫ φ k = (Φ.e (Λ k z)).left) → Submodule.span ℝ (Ga : Set (Fin N → ℂ)) = ⊤ → (∀ gm ∈ Ga, (∀ z, q (z + gm) = q z) ∧ ∀ k, Λ k gm ∈ Φ.lat) → (∀ z w, ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k w) = 0) → (∃ v : ℂ, v ≠ 0 ∧ ∀ z, Φ.GenRd φ ε t (q z) (fun k => Λ k z) v) ∧ ∀ gm ∈ Ga, ∏ k, Φ.χ (Λ k gm) ^ ε k = 1 := by
  intro S A _ _ L x0 g Φ Z K _ φ ε t ht N q Λ Ga hq hqe hspan hper hH
  obtain ⟨v, hv, hv0, hrd, -, hfac⟩ := GlobalTheory.T.exists_holomorphic_generator_reading_automorphy S A L x0 g Φ Z K φ ε t ht N q (fun k z => Λ k z) hq
    (fun k => (LinearMap.toContinuousLinearMap (Λ k)).differentiable) hqe
  have hprod : ∀ gm z, ∏ k, Φ.fac (Λ k gm) (Λ k z) ^ ε k = ∏ k, Φ.χ (Λ k gm) ^ ε k := by
    intro gm z
    simp only [AnFr.fac, mul_zpow, Finset.prod_mul_distrib, ← Complex.exp_int_mul, ← Complex.exp_sum]
    have h : ∑ k, (ε k : ℂ) * (Real.pi * hermForm Φ.Hm (Λ k z) (Λ k gm) +
        Real.pi / 2 * hermForm Φ.Hm (Λ k gm) (Λ k gm)) =
        Real.pi * ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k gm) +
        Real.pi / 2 * ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k gm) (Λ k gm) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h, hH, hH]
    simp
  have hstep : ∀ gm ∈ Ga, ∀ z, v (z + gm) = v z * ∏ k, Φ.χ (Λ k gm) ^ ε k := by
    intro gm hgm z
    rw [← hprod gm z]
    exact hfac z (z + gm) (fun k => Λ k gm) ((hper gm hgm).1 z)
      (fun k => ⟨(hper gm hgm).2 k, map_add _ _ _⟩)
  have hnorm : ∀ gm ∈ Ga, ∀ z, ‖v (z + gm)‖ = ‖v z‖ := by
    intro gm hgm z
    rw [hstep gm hgm z, norm_mul, norm_prod]
    have : ∀ k, ‖Φ.χ (Λ k gm) ^ ε k‖ = 1 := fun k => by
      rw [norm_zpow, Φ.χ_norm _ ((hper gm hgm).2 k), one_zpow]
    simp [this]
  have hconst : ∀ z, v z = v 0 := by
    intro z
    refine norm_periodic_const_range Ga.subtype ?_ v hv (fun z a => hnorm a a.2 z) z 0
    simpa using hspan
  refine ⟨⟨v 0, hv0 0, fun z => hconst z ▸ hrd z⟩, fun gm hgm => ?_⟩
  have h := hstep gm hgm 0
  rw [hconst] at h
  exact (mul_eq_left₀ (hv0 0)).1 h.symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isValueAt_jetPoint_cmFrame_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (m k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.Rd k F θ → Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → ∃ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y g m 1)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y g m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧ IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (Φ.jx m) τ (toΓ _ (jetOf m θ)) := by
  first | exact @GlobalTheory.JetVal.isValueAt_jetPt | exact GlobalTheory.JetVal.isValueAt_jetPt | (intros; apply GlobalTheory.JetVal.isValueAt_jetPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory



theorem exists_frames_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), IsChartG t x0 d G.F A.act tg uvec x → ∃ (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e ∧ IsPrimG t wP ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e ∧ (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) ∧ Rig0G t x0 d x A.act e wP := by
  intro E _ _ _ H X0 t S _ x0 d G A κ _ tg uvec x hc

  obtain ⟨e, hgen, htr, hax⟩ :=
    GlobalTheory.T.exists_frames_cubeDefect_along_chart_over_ring E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc

  obtain ⟨ph1, h1⟩ :=
    GlobalTheory.T.exists_firstPartialLaw_series_of_frames_alt E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax
  obtain ⟨ph2, h2⟩ :=
    GlobalTheory.T.exists_second_partial_law_alt E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨sy, hsy⟩ :=
    GlobalTheory.T.exists_symmetry_series_of_frames_alt E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨ad, hadc, had⟩ :=
    GlobalTheory.T.exists_adjointness_series_of_frames E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨wP, hP⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wP t
  exact ⟨e, wP, ph1, ph2, sy, ad, ⟨hgen, h1, h2, hsy, had⟩, hP, htr, hax, hadc,
    GlobalTheory.T.frame_rigidification_of_canonical_axes E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax wP hP⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rawChart_formalBiextension_baseChange : RawBCSt := by
  first | exact @GlobalTheory.rawChart_baseChange | exact GlobalTheory.rawChart_baseChange | (intros; apply GlobalTheory.rawChart_baseChange <;> assumption)
end
