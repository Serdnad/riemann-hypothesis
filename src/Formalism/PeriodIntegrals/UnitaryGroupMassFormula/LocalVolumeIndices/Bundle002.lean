module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.MassDataKppVolLemmas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

abbrev lamS : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

abbrev KfS : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := Kf X.B.I.cm.sig X.B.I.J (lamS X)

def KppS : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := Subgroup.closure (levelUnitary X hb)

def gIdx : ℕ := (KppS X hb).relIndex (KfS X)

def KvS (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  Subgroup.closure (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)

def KppvS (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  Subgroup.closure (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)

def lIdx (p : TypX X) : ℕ := (KppvS X hb p).relIndex (KvS X p)

def GlobIdx : Prop :=
  gIdx X hb ≠ 0 → X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
    (gIdx X hb : ℝ≥0∞) * X.measG.μGf (levelUnitary X hb)

def LocIdx : Prop :=
  ∀ p : TypX X, lIdx X hb p ≠ 0 → X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1) =
    (lIdx X hb p : ℝ≥0∞) * X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)

def LocPos : Prop :=
  ∀ p : TypX X, 0 < X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1) ∧
    X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1) < ⊤ ∧ lIdx X hb p ≠ 0

def IdxProd : Prop := gIdx X hb = ∏ p : TypX X, lIdx X hb p

def GlobIdxAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → GlobIdx X hb
def LocIdxAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → LocIdx X hb
def LocPosAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → LocPos X hb
def IdxProdAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → IdxProd X hb

theorem Steps_bOf_μKpp (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn) :
    (bOf X hb hK FdN FdN' u u' X0 L A).μKpp =
      (X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal := rfl

theorem Steps_main (h1 : GlobIdx X hb) (h2 : LocIdx X hb) (h3 : LocPos X hb) (h4 : IdxProd X hb) :
    (X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal =
      (X.measG.μGf (levelUnitary X hb)).toReal := by
  have hne : ∀ p : TypX X,
      (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal ≠ 0 := fun p =>
    (ENNReal.toReal_pos (h3 p).1.ne' (h3 p).2.1.ne).ne'
  have hg : gIdx X hb ≠ 0 := by
    rw [h4]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => (h3 p).2.2
  have hprod : ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal =
      (gIdx X hb : ℝ) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal := by
    rw [h4, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [h2 p (h3 p).2.2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hP : ∏ p : TypX X,
      (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => hne p
  have hG : (gIdx X hb : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  rw [hprod, h1 hg, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_mul_left _ _ hG,
    div_mul_cancel₀ _ hP]

theorem massDataKppVol_of (h1 : GlobIdxAll) (h2 : LocIdxAll) (h3 : LocPosAll) (h4 : IdxProdAll) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X))
      (A : AnIn), KppVolAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hyp
  rw [Steps_bOf_μKpp X hb hK FdN FdN' u u' X0 L A]
  exact Steps_main X hb (h1 X hb hK hyp.1 hyp.2.1) (h2 X hb hK hyp.1 hyp.2.1)
    (h3 X hb hK hyp.1 hyp.2.1) (h4 X hb hK hyp.1 hyp.2.1)

end PI.MassDataKppVolLemmas
end
end

section

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst)

theorem Cst_inv_int (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) (hm : (m : 𝓞 I.F) ∉ v.asIdeal) :
    ((m : Fv I.F v))⁻¹ ∈ v.adicCompletionIntegers I.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
  have e1 : (m : Fv I.F v) = ((algebraMap (𝓞 I.F) I.F (m : 𝓞 I.F) : I.F) : Fv I.F v) := by
    rw [← map_natCast (algebraMap (𝓞 I.F) (Fv I.F v)) m]
    exact congrFun (HeightOneSpectrum.algebraMap_adicCompletion ..) _
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hm, inv_one]

theorem Cst_not_mem (g1 g2 : ℕ) (v : HeightOneSpectrum (𝓞 I.F)) (hv : ¬ IsTyped I.F g1 g2 v) :
    ((g1 * g2 : ℕ) : 𝓞 I.F) ∉ v.asIdeal := by
  intro h
  rw [Nat.cast_mul] at h
  exact hv (v.isPrime.mem_or_mem h)


open Classical in
def cElt (g1 g2 : ℕ) : Af I.F :=
  (⟨fun v => if IsTyped I.F g1 g2 v then 0 else (((g1 * g2 : ℕ) : Fv I.F v))⁻¹,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs with h
      · exact zero_mem _
      · exact Cst_inv_int I v _ (Cst_not_mem I g1 g2 v h)⟩ :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 I.F) => v.adicCompletion I.F)
      (fun v => v.adicCompletionIntegers I.F) Filter.cofinite)

open Classical in
theorem Cst_apply (g1 g2 : ℕ) (v : HeightOneSpectrum (𝓞 I.F)) :
    cElt I g1 g2 v = if IsTyped I.F g1 g2 v then 0 else (((g1 * g2 : ℕ) : Fv I.F v))⁻¹ := rfl

theorem Cst_int (g1 g2 : ℕ) : cElt I g1 g2 ∈ Formalism.UG.intAd I.F := by
  classical
  intro v
  show cElt I g1 g2 v ∈ _
  rw [Cst_apply]
  split_ifs with h
  · exact zero_mem _
  · exact Cst_inv_int I v _ (Cst_not_mem I g1 g2 v h)

theorem Cst_natCast_apply (m : ℕ) (v : HeightOneSpectrum (𝓞 I.F)) : (m : Af I.F) v = (m : Fv I.F v) :=
  map_natCast (evalV I.F v) m

theorem Cst_sum_apply {ι : Type} (s : Finset ι) (f : ι → Af I.F) (v : HeightOneSpectrum (𝓞 I.F)) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v :=
  map_sum (evalV I.F v) f s

theorem Cst_gc (g1 g2 : ℕ) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) :
    ((g1 * g2 : ℕ) : Af I.F) * cElt I g1 g2 = 1 - ∑ p : TypP I.F g1 g2, chi I p.1 := by
  classical
  apply FiniteAdeleRing.ext
  intro v
  rw [Comp_mul_apply, Comp_sub_apply, Comp_one_apply, Cst_natCast_apply, Cst_sum_apply, Cst_apply]
  by_cases hv : IsTyped I.F g1 g2 v
  · have hmem : v ∈ typSet I.F g1 g2 := (mem_typSet I.F g1 g2 h1 h2 v).mpr hv
    rw [if_pos hv, mul_zero, Finset.sum_eq_single (⟨v, hmem⟩ : TypP I.F g1 g2)]
    · rw [Comp_chi_same, sub_self]
    · intro b _ hb
      exact Comp_chi_ne I b.1 v (fun h => hb (Subtype.ext h.symm))
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hv, Finset.sum_eq_zero, sub_zero]
    · apply mul_inv_cancel₀
      intro h0
      have : ((g1 * g2 : ℕ) : I.F) = 0 := by
        have h3 : algebraMap I.F (Fv I.F v) ((g1 * g2 : ℕ) : I.F) = 0 := by rw [map_natCast]; exact h0
        exact (algebraMap I.F (Fv I.F v)).injective (by rw [h3, map_zero])
      exact (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero h1 h2)) this
    · intro p _
      refine Comp_chi_ne I p.1 v fun h => hv ?_
      rw [h]
      exact (mem_typSet I.F g1 g2 h1 h2 p.1).mp p.2

end PI.MassDataKppVolLemmas
end
end

section

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)

def SngSurj : Prop :=
  ∀ (I : AutInst) (p : HeightOneSpectrum (𝓞 I.F)) (k : HA (Fv I.F p) I.cm.sig I.J),
    k ∈ Kv I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) p →
    ∃ h : HA (Af I.F) I.cm.sig I.J, h ∈ Kf I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) ∧
      piV I p h = k ∧ ∀ v : HeightOneSpectrum (𝓞 I.F), v ≠ p → piV I v h = 1

end PI.MassDataKppVolLemmas
end
end
