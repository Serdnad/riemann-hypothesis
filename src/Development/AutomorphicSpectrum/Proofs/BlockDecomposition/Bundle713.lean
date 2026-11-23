module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle707
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle709
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle708
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspShuffle

open Zc.Comb

variable {α β : Type*}

theorem interleave_filter (f : β → α) (q : β → Bool) (P : List β) :
    Interleave ((P.filter q).map f) ((P.filter fun p => !q p).map f) (P.map f) := by
  induction P with
  | nil => exact Zc.Comb.Interleave.nil
  | cons p P ih =>
    cases hq : q p with
    | true =>
      simp only [List.filter_cons, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.left ih
    | false =>
      simp only [List.filter_cons, hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.right ih

theorem shuffle_range (f : β → α) (c : β → ℕ) (n : ℕ) : ∀ (s : ℕ) (P : List β),
    (∀ p ∈ P, s ≤ c p ∧ c p < s + n) →
      Shuffle ((List.range' s n).map fun i => (P.filter fun p => c p = i).map f) (P.map f) := by
  induction n with
  | zero =>
    intro s P hP
    have hnil : P = [] := List.eq_nil_iff_forall_not_mem.mpr fun p hp => by
      have := hP p hp
      omega
    subst hnil
    exact Zc.Comb.Shuffle.nil
  | succ n ih =>
    intro s P hP
    simp only [List.range'_succ, List.map_cons]
    refine Zc.Comb.Shuffle.cons (v := (P.filter fun p => !decide (c p = s)).map f) ?_
      (GlobalTheory.CompanionTheory.CuspShuffle.interleave_filter f (fun p => decide (c p = s)) P)
    have h := ih (s + 1) (P.filter fun p => !decide (c p = s)) (by
      intro p hp
      rw [List.mem_filter] at hp
      have h1 := hP p hp.1
      have hne : c p ≠ s := by simpa using hp.2
      omega)
    convert h using 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range'_1] at hi
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro p _
    by_cases hc : c p = i
    · have his : i ≠ s := by omega
      simp [hc, his]
    · simp [hc]

theorem shuffle_of_colouring {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (D : Fin h → List α)
    (hD : ∀ i, Zc.Cos.sub W c i = D i) : Shuffle (List.ofFn D) W := by
  have key := GlobalTheory.CompanionTheory.CuspShuffle.shuffle_range W.get (fun p => (c p : ℕ)) h 0 (List.finRange W.length)
    (fun p _ => ⟨Nat.zero_le _, by simpa using (c p).isLt⟩)
  convert key using 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range', ← hD]
      unfold Zc.Cos.sub
      congr 1
      apply List.filter_congr
      intro p _
      simp [Fin.ext_iff]
  · apply List.ext_getElem <;> simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decWord_eq_decW (Δ : Segment k) : Zc.Cos.decWord Δ = decW Δ := by
  unfold Zc.Cos.decWord Zc.M.decW
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    ext
    simp only [Fin.val_rev, List.length_ofFn]
    omega

theorem inShW_of_wd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : LSegJacquet k) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k) (hΔ : ∀ i, IsLSeg (Δ i) (x i).rep) (w : List (IrrGL (k := k)))
    (hc : ∀ c ∈ w, c.IsCusp) (hw : Wd (prodIrr x hd) w) : InShW (Finset.univ.val.map Δ) w := by
  obtain ⟨hsum, hne⟩ := hw
  have hmult := GlobalTheory.T.segment_product_jacquet_shuffle_count hA hL Δ x hd hΔ w hc
  have hpos : Zc.Cos.jmL w (GlobalTheory.LocGL.prodIrr x hd) ≠ 0 := by
    unfold Zc.Cos.jmL
    rw [dite_eq_left hsum]
    exact hne
  rw [hmult] at hpos
  have hcard : Zc.Cos.shuffleCount w (fun i => Zc.Cos.decWord (Δ i)) ≠ 0 := by exact_mod_cast hpos
  unfold Zc.Cos.shuffleCount at hcard
  obtain ⟨col, hcol⟩ := Finset.card_ne_zero.mp hcard
  have hcol' : ∀ i, Zc.Cos.sub w col i = Zc.Cos.decWord (Δ i) := by simpa using hcol
  unfold Zc.M.InShW
  refine ⟨List.ofFn Δ, ?_, ?_⟩
  · rw [Fin.univ_val_map]
  · rw [List.map_ofFn]
    have e : (Zc.M.decW ∘ Δ) = fun i => Zc.Cos.decWord (Δ i) :=
      funext fun i => (GlobalTheory.CompanionTheory.CuspShuffle.decWord_eq_decW (Δ i)).symm
    rw [e]
    exact GlobalTheory.CompanionTheory.CuspShuffle.shuffle_of_colouring w col _ hcol'

end GlobalTheory.CompanionTheory.CuspShuffle

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.section_invariant_heisenberg_weyl : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (x : Mx D ρ p) (h : G D n), f (M.w * M.nzx 0 x * h) = f (M.w * h) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.LawW.law_w | exact GlobalTheory.CompanionTheory.FJE.LawW.law_w | (intros; apply GlobalTheory.CompanionTheory.FJE.LawW.law_w <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_heisenberg_mul : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (z z' : hermA D ρ) (x x' : Mx D ρ p), M.nzx z x * M.nzx z' x' = M.nzx (z + z') (x + x') := by
  first | exact @GlobalTheory.CompanionTheory.NzxAdd.nzx_add | exact GlobalTheory.CompanionTheory.NzxAdd.nzx_add | (intros; apply GlobalTheory.CompanionTheory.NzxAdd.nzx_add <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.shift_commutes_levi_embedding : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ y : Mx D ρ p, M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  first | exact @GlobalTheory.CompanionTheory.PcB.sh_emb_levi | exact GlobalTheory.CompanionTheory.PcB.sh_emb_levi | (intros; apply GlobalTheory.CompanionTheory.PcB.sh_emb_levi <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.heisenberg_centre_rational_form : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ a b, M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0) ∧ (∀ z y, M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0) ∧
    (∀ z h, M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0) ∧
    ∀ l : ratHerm D ρ, M.nzx l.1 0 ∈ GF D n ∧ ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.centre_nzx | exact GlobalTheory.CompanionTheory.ZUnf.centre_nzx | (intros; apply GlobalTheory.CompanionTheory.ZUnf.centre_nzx <;> assumption)
end
end

section

open PositivityTheory.Rg.SwEis

theorem _root_.GlobalTheory.T.eisenstein_iwasawa_estimate : EIwa := by
  first | exact @GlobalTheory.CompanionTheory.SwEisIwa.eIwa | exact GlobalTheory.CompanionTheory.SwEisIwa.eIwa | (intros; apply GlobalTheory.CompanionTheory.SwEisIwa.eIwa <;> assumption)
end
