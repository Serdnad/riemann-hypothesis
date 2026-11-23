module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle684
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle359
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

noncomputable section

open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape

variable {D : D7}

def latPi (S : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.FinPl.Lat S :=
  Submodule.pi Set.univ fun _ => (I : Submodule (𝓞 D.host.E) D.host.E)


variable (D) in
def tiltSc (j : ℕ) (p : Fin (D.R.m - 1 - j)) : D.host.E :=
  if Odd j then
    (if 2 * p.1 < D.R.m - 1 - j then (D.host.xi0 ^ p.1)⁻¹ else star (D.host.xi0 ^ (D.R.m - 1 - j - 1 - p.1)))
  else 1


variable (D) in
def rowId (j : ℕ) (p : Fin (D.R.m - 1 - j)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  FractionalIdeal.spanSingleton _ (tiltSc D j p) * stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p

variable {T : Type} {L : LevCh D T} {sc : Consts}

def rowN (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (G.V (.grid D.R.m j)) :=
  if h : j < D.R.m then (G.rowDec j h).lat (G.Λ (.top j)) (rowId D j) else G.Λ (.grid D.R.m j)


variable (D) in
def lineId (j : ℕ) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  D.host.AA ^ ((D.R.m - 2 - j) / 2 + 1) * (D.host.AAbar ^ ((D.R.m - 2 - j) / 2 + 1))⁻¹


variable (D) in
def lineL (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.SeeSaw.Model.nLine D) := latPi _ (lineId D j)


variable (D) in
def topL : GlobalTheory.FinPl.Lat (GlobalTheory.RowChain.pLine D) := latPi _ 1

def coreL (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) :=
  (G.Λ (.top j)).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iA).restrictScalars
        (𝓞 D.host.E)) ⊔
    (lineL D j).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iB).restrictScalars
        (𝓞 D.host.E))

end GlobalTheory.RowShape

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.IdemSumSet

theorem subset_of_isIdemSum {D : D7} {e : Formalism.L2.Theta.AE D} {P P' : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : Formalism.IndefR.Datum.IsIdemSum e P) (h' : Formalism.IndefR.Datum.IsIdemSum e P') : P ⊆ P' := by
  intro w hw
  obtain ⟨⟨es, hes, he⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, hf⟩, -⟩ := h'
  have hw' := hes w hw

  have hpick : es w * e = es w := by
    rw [he, Finset.mul_sum, Finset.sum_eq_single w]
    · exact hw'.1.1
    · intro v hv hvw
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w v hw' (hes v hv)).2 (Ne.symm hvw)
    · intro hn
      exact absurd hw hn

  by_contra hout
  apply GlobalTheory.LevelPlaces.ne_zero_of_isIdemAt hw'
  rw [← hpick, hf, Finset.mul_sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w v hw' (hfs v hv)).2 ?_
  rintro rfl
  exact hout hv

theorem places_eq_of_isIdemSum : ∀ (D : D7) (e : AE D) (P P' : Finset (Pl D.host.E)), IsIdemSum e P → IsIdemSum e P' → P = P' := by
  intro D e P P' h h'
  ext w
  exact ⟨fun hw => subset_of_isIdemSum h h' hw, fun hw => subset_of_isIdemSum h' h hw⟩

end GlobalTheory.IdemSumSet
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.IdemSingleSum

theorem sum_mul_sum_orth {R ι : Type} [Ring R] [DecidableEq ι] (f : ι → R) (hid : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0) (S S' : Finset ι) :
    (∑ i ∈ S, f i) * (∑ j ∈ S', f j) = ∑ i ∈ S ∩ S', f i := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc ∑ i ∈ S, ∑ j ∈ S', f i * f j = ∑ i ∈ S, if i ∈ S' then f i else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S'
        · rw [if_pos hi, Finset.sum_eq_single_of_mem i hi fun j _ hji => horth i j (Ne.symm hji), hid]
        · rw [if_neg hi]
          exact Finset.sum_eq_zero fun j hj => horth i j fun hij => hi (by rw [hij]; exact hj)
    _ = ∑ i ∈ S ∩ S', f i := Finset.sum_ite_mem S S' f

theorem isIdemAt_of_single {D : D7} {a : AE D} {w : Pl D.host.E} (h : IsIdemSum a {w}) :
    Formalism.L2.NTheta.IsIdemAt a w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  simpa using hes w (Finset.mem_singleton_self w)

private theorem mul_self_eq_of_isIdemAt {D : D7} {x : AE D} {w : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) : x * x = x := by
  have h := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w} (fun _ => x) (by simpa using hx)
  simpa only [Finset.sum_singleton, Finset.mem_singleton_self, if_true] using h

private theorem mul_eq_zero_of_isIdemAt_of_ne {D : D7} {x y : AE D} {w w' : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) (hy : Formalism.L2.NTheta.IsIdemAt y w') (hne : w ≠ w') : x * y = 0 := by
  have h := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w'} (fun _ => y) (by simpa using hy)
  rwa [Finset.sum_singleton, if_neg (by simpa using hne)] at h

private theorem eq_of_isIdemAt_of_isIdemAt {D : D7} {x y : AE D} {w : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) (hy : Formalism.L2.NTheta.IsIdemAt y w) : x = y := by
  have h1 := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w} (fun _ => y) (by simpa using hy)
  have h2 := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hy {w} (fun _ => x) (by simpa using hx)
  simp only [Finset.sum_singleton, Finset.mem_singleton_self, if_true] at h1 h2
  calc x = x * y := h1.symm
    _ = y * x := mul_comm x y
    _ = y := h2

theorem sum_single : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ (eL : P → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → e = ∑ w, eL w ∧ (∀ S : Finset P, IsIdemSum (∑ w ∈ S, eL w) (S.map (Function.Embedding.subtype _))) ∧ ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := by
  intro D e P he eL hL
  obtain ⟨⟨es, hes, hsum⟩, he0⟩ := he
  have hat : ∀ w : P, Formalism.L2.NTheta.IsIdemAt (eL w) w.1 := fun w => isIdemAt_of_single (hL w)
  have hprod : ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := fun S S' =>
    sum_mul_sum_orth eL (fun w => mul_self_eq_of_isIdemAt (hat w))
      (fun w w' hne => mul_eq_zero_of_isIdemAt_of_ne (hat w) (hat w') fun h => hne (Subtype.ext h)) S S'
  have htot : e = ∑ w, eL w := by
    rw [hsum, ← Finset.sum_coe_sort P es]
    exact Finset.sum_congr rfl fun w _ => (eq_of_isIdemAt_of_isIdemAt (hat w) (hes w.1 w.2)).symm
  refine ⟨htot, fun S => ⟨⟨es, ?_, ?_⟩, ?_⟩, hprod⟩
  · intro PP hPP
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hPP
    exact hes w.1 w.2
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun w _ => eq_of_isIdemAt_of_isIdemAt (hat w) (hes w.1 w.2)
  · have hse : (∑ w ∈ S, eL w) * e = ∑ w ∈ S, eL w := by
      rw [htot, hprod, Finset.inter_univ]
    set s := ∑ w ∈ S, eL w
    calc s * cA D s = (s * e) * cA D (e * s) := by rw [hse, mul_comm e s, hse]
      _ = s * (e * cA D e) * cA D s := by rw [map_mul]; ring
      _ = 0 := by rw [he0, mul_zero, zero_mul]

end GlobalTheory.IdemSingleSum
end
