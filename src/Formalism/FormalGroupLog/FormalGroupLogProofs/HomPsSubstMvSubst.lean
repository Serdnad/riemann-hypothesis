module

public import Formalism.FormalGroupLog.Statement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

@[expose] public section

noncomputable section

open PowerSeries

namespace Formalism.G

private theorem hom_ps_subst_mv_subst {R : Type*} [CommRing R] {σ τ : Type*}
    (g : PowerSeries R) (G : MvPowerSeries σ R) (v : σ → MvPowerSeries τ R)
    (hG : MvPowerSeries.constantCoeff G = 0) (hv : MvPowerSeries.HasSubst v) :
    MvPowerSeries.subst v (g.subst G) = g.subst (MvPowerSeries.subst v G) := by
  have hG' : MvPowerSeries.HasSubst (fun _ : Unit => G) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hG
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hG' hv]

private theorem hom_hasSubst_pair {R : Type*} [CommRing R] {τ : Type*}
    (a b : MvPowerSeries τ R) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.HasSubst ![a, b] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp [ha, hb]

private theorem hom_cc_at {R : Type*} [CommRing R] {τ : Type*} (f : PowerSeries R) (t : τ)
    (hf : constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (f.subst (MvPowerSeries.X t : MvPowerSeries τ R)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X t) f hf

theorem homComp_statement : HomComp := by
  unfold HomComp
  intro R _ F G H f g hf hg
  obtain ⟨hf0, hfe⟩ := hf
  obtain ⟨hg0, hge⟩ := hg
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hvf : MvPowerSeries.HasSubst ![atX f, atY f] :=
    hom_hasSubst_pair _ _ (hom_cc_at f 0 hf0) (hom_cc_at f 1 hf0)
  have hvg : MvPowerSeries.HasSubst ![atX g, atY g] :=
    hom_hasSubst_pair _ _ (hom_cc_at g 0 hg0) (hom_cc_at g 1 hg0)
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero hf0 g hg0, ?_⟩
  rw [PowerSeries.subst_comp_subst_apply hfs hF, hfe,
    ← hom_ps_subst_mv_subst g G.toPowerSeries _ G.zero_constantCoeff hvf, hge,
    MvPowerSeries.subst_comp_subst_apply hvg hvf]
  congr 1
  funext s

  have hcoord : ∀ t : Fin 2, MvPowerSeries.subst ![atX f, atY f]
      (g.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)) =
      PowerSeries.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R) (PowerSeries.subst f g) := by
    intro t
    rw [hom_ps_subst_mv_subst g _ _ (MvPowerSeries.constantCoeff_X t) hvf, MvPowerSeries.subst_X hvf,
      PowerSeries.subst_comp_subst_apply hfs (PowerSeries.HasSubst.X t)]
    fin_cases t <;> rfl
  fin_cases s
  · exact hcoord 0
  · exact hcoord 1

theorem log_iff_hom_additive : LogIffHomGa := by
  unfold LogIffHomGa
  intro R _ F f

  have ga : constantCoeff f = 0 →
      MvPowerSeries.subst ![atX f, atY f] (FormalGroup.𝔾ₐ (R := R)).toPowerSeries = atX f + atY f := by
    intro h0
    have hv : MvPowerSeries.HasSubst ![atX f, atY f] :=
      hom_hasSubst_pair _ _ (hom_cc_at f 0 h0) (hom_cc_at f 1 h0)
    show MvPowerSeries.subst _ (MvPowerSeries.X 0 + MvPowerSeries.X 1) = _
    rw [← MvPowerSeries.coe_substAlgHom hv, map_add (f := _), MvPowerSeries.coe_substAlgHom,
      MvPowerSeries.subst_X hv, MvPowerSeries.subst_X hv]
    rfl
  unfold IsLog IsHom
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h0, by rw [h2, ga h0]⟩, h1⟩
  · rintro ⟨⟨h0, h2⟩, h1⟩
    exact ⟨h0, h1, by rw [h2, ga h0]⟩

theorem substInjective_statement : SubstInjective := by
  unfold SubstInjective
  intro R _ ι f a b h0 h1 ha hb h
  exact _root_.Formalism.G.LogP.psubst_injective h0 h1 ha hb h

end Formalism.G
