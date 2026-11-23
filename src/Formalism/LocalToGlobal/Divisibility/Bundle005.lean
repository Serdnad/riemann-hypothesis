module

public import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.DivisionAdmissibleFamilyOfData
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.Columns.Bundle005
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.MirabolicMackeyTheory.Bundle001
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.Divisibility.HookProducts.Bundle001

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef

section Face

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem linkDIV_L2R_face [_root_.NumberField.IsTotallyComplex K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (Pk : IndefPkgR A fc cf C CH) (wf0 : (fc Pk.Zs).Df0.WF) (wf1 : (fc Pk.Zs).Df1.WF)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (u : (fc Pk.Zs).Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin ((fc Pk.Zs).Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputsR Pk.core R u Nu sg) : DivClausesR Pk.core R u Nu sg :=
  divClausesR_of wf0 wf1 Pk.core R u Nu sg I

end Face

section Fam3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

end Fam3

section Col3

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)

end Col3

end Formalism.L2.DIV
end
end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions

section Weights

variable {D : D7}

theorem lw_plEq (w : D.what₂.places.Pl) : SizeData₂.lwP w = Formalism.DivisionValues.lw (D.plEq w) := by
  rfl

theorem ramw_plEq (w : D.what₂.places.Pl) : ((D.what₂.places.ramIdx w : ℕ) : ℝ) = ((ramw (D.plEq w) : ℤ) : ℝ) := by
  rw [← lf_eW_eq_ramw, D.ram_eq w, Int.cast_natCast]
  rfl

end Weights

section Fo

variable {D : D7} {Bs : DefBase D.what₂.LL} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}

def FTie (L : SizeData₂ D) (N : IndefNum Bs) (eJ : Bs.J ≃ Fin D.R.m) : Prop :=
  ∀ y j, N.F0 y j = L.F ((eJ j).1 + 1) (D.plEq.symm y)

theorem sum_lifts_eJ (eJ : Bs.J ≃ Fin D.R.m) (f : ℕ → ℝ) :
    ∑ j ∈ SizeData₂.lifts D, f j = ∑ j : Bs.J, f ((eJ j).1 + 1) := by
  rw [Equiv.sum_comp eJ (fun i : Fin D.R.m => f (i.1 + 1)), Fin.sum_univ_eq_sum_range (fun i => f (i + 1)),
    Finset.range_eq_Ico, Finset.sum_Ico_add']
  unfold SizeData₂.lifts
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

theorem two_sumTw_eq_Fo (L : SizeData₂ D) (S0 : IndefSide Df0 N) (hU : S0.toIndefData.Untwisted N) (eJ : Bs.J ≃ Fin D.R.m)
    (hF : FTie L N eJ) :
    2 * (∑ j, ∑ y ∈ S0.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) = L.Fo := by
  classical
  have hF' : ∀ y j, N.F0 y j = L.F ((eJ j).1 + 1) (D.plEq.symm y) := hF
  unfold SizeData₂.Fo
  rw [sum_lifts_eJ eJ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ y ∈ S0.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)
      = ∑ y ∈ S0.Tw ∪ L.supp.map D.plEq.toEmbedding, lw y * ((ramw y : ℝ) * N.F0 y j) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro y _ hy
    rw [(hU y hy j).2, mul_zero, mul_zero]
  have h2 : ∑ y ∈ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j))
      = ∑ y ∈ S0.Tw ∪ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j)) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro y _ hy'
    have hw : D.plEq.symm y ∉ L.supp := by
      intro hw
      apply hy'
      rw [Finset.mem_map]
      exact ⟨_, hw, by simp⟩
    rw [hF', L.F_supp _ _ hw, mul_zero, mul_zero, mul_zero]
  have h3 : ∑ w ∈ L.supp, SizeData₂.sz w (L.F ((eJ j).1 + 1) w)
      = ∑ y ∈ L.supp.map D.plEq.toEmbedding, 2 * (lw y * ((ramw y : ℝ) * N.F0 y j)) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [hF', Equiv.symm_apply_apply, SizeData₂.sz, lw_plEq, ramw_plEq]
    ring
  rw [h1, h3, h2, Finset.mul_sum]

theorem two_FoOfR_eq_Fo (L : SizeData₂ D) (P : IndefCoreR Df0 Df1 Dc Sp N) (eJ : Bs.J ≃ Fin D.R.m) (hF : FTie L N eJ) :
    2 * FoOfR P = L.Fo := by
  unfold FoOfR
  exact two_sumTw_eq_Fo L P.base P.extra.untw eJ hF

end Fo

section Sg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

end Sg

section Mu1

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

end Mu1

end Formalism.L2.DIV

end
end

section

noncomputable section

namespace Formalism.L2.DIV.Wire

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.DIV

variable {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps}

theorem la_of (Fm : Formalism.MainNotions.FamP eps) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La :=
  ⟨Fm.x1 + 1, fun x hx i => Formalism.MainNotions.DIV.La_nonneg (Fm.L x i) (Fm.sizes x (by linarith) i).2.2.2.2.2.2.1⟩

theorem za_of (Fm : Formalism.MainNotions.FamP eps) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.L x i).ZeroAbove :=
  ⟨Fm.x1 + 1, fun x hx i => Formalism.MainNotions.WeightDegreeSizes.zero_gain_above_family Fm x (by linarith) i⟩

end Formalism.L2.DIV.Wire

end
end
