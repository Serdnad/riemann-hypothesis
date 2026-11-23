module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle032
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.SupGeneric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frBor_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

theorem evR_of_frMap (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c} (hg : g ∈ sec Xo c a n)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c g z = φ (evR Xo c g y) := by
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test S y
  rw [evR_eq_map_of_test_point hL hg q χ y₀ y hy₀,
    evR_eq_map_of_test_point hL hg q (φ.comp χ) y₀ z (PullbackSections.frMap_trans χ φ hy₀ hyz)]
  rfl

theorem isFractionRing_chart {h : GenFrEx Xo c} (C : FChart h) : IsFractionRing C.R (Om C.Z) := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, ha, b, hb, hb0, e⟩ := C.frac x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
    change x = a / b
    rw [eq_div_iff hb0, e]⟩

section Pin

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r}
  (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) {xR : ℝ}
  {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ} (hx : 0 < xR) (hfn : FnPin U xR fn)
  {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c}

include hU hx hfn

end Pin

end GlobalTheory.SupGeneric
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_ratio_forms_at_points_alt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Pt : Type) [Finite Pt] (U : Pt → Type) [∀ ζ, Field (U ζ)] (ev : ∀ ζ, Rp X la N →+* U ζ) (ι : Type) (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) (Zc : Pt → ι) (jz : ∀ ζ, Ω (Zc ζ) →+* U ζ), (∀ ζ, ∃ k, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc wL (w k))) ≠ 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), gF (Zc ζ) (X.inc u F) = 0 → ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F)) = 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u), jz ζ (gF (Zc ζ) (X.inc u F)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F')) = jz ζ (gF (Zc ζ) (X.inc u F')) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F))) → (∀ Z, CurveLoc.BirAt X N w (gF Z)) → (∀ Z (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ F' : B.Cusp j u, gF Z (X.inc u F') = gF Z (X.inc u F) ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc u F') = 0) → ∀ a : ∀ Z, Ω Z, ∃ (k : ℕ) (F F' : B.Cusp j (addL (wt0 D j) wL k)), ∀ ζ, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) ≠ 0 ∧ ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F)) = jz ζ (a (Zc ζ)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) := by
  first | exact @GlobalTheory.exists_ratio_forms_at_points | exact GlobalTheory.exists_ratio_forms_at_points | (intros; apply GlobalTheory.exists_ratio_forms_at_points <;> assumption)
end
