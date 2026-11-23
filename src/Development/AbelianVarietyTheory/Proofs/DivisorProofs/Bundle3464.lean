module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

section


theorem _root_.GlobalTheory.T.minimalBlowup_smooth_with_semiAbelianCharts : GlobalTheory.SiegJoin.ChartSt5 := by
  first | exact @GlobalTheory.SiegJoin.chartSt5_holds | exact GlobalTheory.SiegJoin.chartSt5_holds | (intros; apply GlobalTheory.SiegJoin.chartSt5_holds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tripleChart_unitary_boundary_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x := by
  first | exact @GlobalTheory.UChart.uPre_of_boundary | exact GlobalTheory.UChart.uPre_of_boundary | (intros; apply GlobalTheory.UChart.uPre_of_boundary <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem sdRep_of_coprime : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → SDRep h M d := by
  intro h M d hh hM hodd hd hcop
  obtain ⟨O, _, bar, r, eO, W, d₀, e, jl, n, o, κ, hbar, hspan, hW, hd₀, hsum, hee, hex, huniq⟩ :=
    GlobalTheory.T.exists_zarhinTrick_family_siegel_kernelKilled h M d hh hM hodd hd hcop
  obtain ⟨H, sH, zH, actH, hpr, hra, hadj, hq, hln, hrep⟩ :=
    GlobalTheory.T.exists_rep_principalSiegel_adjoint_orderAction (8 * h) M (by omega) hM hodd O bar r eO W d₀ hbar hspan hW hd₀ hsum
  obtain ⟨Y, j, c, hj, hjq, hker, hunit, hpull, huniv⟩ :=
    GlobalTheory.T.siegel_family_idempotent_image_open_locus h (8 * h) M d O bar e jl n o κ H sH zH actH hh hM hodd hd hcop hpr hra hadj hee
  refine ⟨Y, j ≫ sH, c, hker, hunit, isQProjOver_comp_immersion j sH hj hjq hq, ?_⟩
  intro S t c' hdu hc'
  obtain ⟨z', act', hz'p, hz'r, hz'a, hz'rel⟩ := hex S t c' hdu hc'
  obtain ⟨g, ⟨hg, hgpb⟩, -⟩ := hrep S t z' act' hz'p hz'r hz'a
  obtain ⟨y, ⟨hy, hyc⟩, -⟩ := huniv S t g c' hg hdu hc' ⟨z', act', hgpb, hz'rel⟩
  refine ⟨y, ⟨by rw [← Category.assoc, hy, hg], hyc⟩, ?_⟩
  rintro f ⟨hf, hfc⟩
  obtain ⟨w, actw, hwp, hwr, hwa, hwpb, hwrel⟩ := hpull S t f c' hf hfc
  have hiso := huniq S t c' w z' actw act' hdu hc' hwp hz'p hwr hz'r hwa hz'a hwrel hz'rel
  have h2 : ActPB w actw zH actH (𝟙 S ≫ g) := hiso.trans hgpb
  rw [Category.id_comp] at h2
  have hfj : f ≫ j = g :=
    (hrep S t w actw hwp hwr hwa).unique ⟨by rw [Category.assoc]; exact hf, hwpb⟩ ⟨hg, h2⟩
  exact (huniv S t g c' hg hdu hc' ⟨z', act', hgpb, hz'rel⟩).unique ⟨hfj, hfc⟩ ⟨hy, hyc⟩

end GlobalTheory.UPel.HT
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
theorem _root_.GlobalTheory.T.projectiveBundleFormula_discrete_space : ∀ (q : ℕ) [NeZero q] (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V :=
  @GlobalTheory.EtC.pbf_disc
end
