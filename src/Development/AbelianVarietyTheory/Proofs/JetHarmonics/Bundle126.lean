module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleSS
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle118
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusId
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle120
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.HermitianCurvature.Bundle009
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle121
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.hatLetters_prod_mul_multiplier_leibniz : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ hats L) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  first | exact @GlobalTheory.HatNF.prod_hats_mul_multiplier | exact GlobalTheory.HatNF.prod_hats_mul_multiplier | (intros; apply GlobalTheory.HatNF.prod_hats_mul_multiplier <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.WordL

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem mem_of_bmon (d : Q.NFData P A) {b : A} (hb : b ∈ bmon d) : b ∈ nfSpan d ∅ 0 0 0 :=
  Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩

theorem span_eq (d : Q.NFData P A) : nfSpan d ∅ 0 0 0 = Submodule.span ℂ (bmon d : Set A) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨b, hb, H, hH, -, rfl⟩
    rw [List.length_eq_zero_iff.mp hH]
    simpa using Submodule.subset_span (R := ℂ) (s := (bmon d : Set A)) hb
  · exact Submodule.span_le.mpr fun b hb => mem_of_bmon d hb

theorem span_mul (d : Q.NFData P A) {x y : A} (hx : x ∈ nfSpan d ∅ 0 0 0) (hy : y ∈ nfSpan d ∅ 0 0 0) :
    x * y ∈ nfSpan d ∅ 0 0 0 := by
  rw [span_eq] at *
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact (bmon d).mul_mem ha hb

theorem kappa_mem (d : Q.NFData P A) (f : M.Ty P → ℂ) : d.κ f ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩))))

theorem zbi_mem (d : Q.NFData P A) : d.L.ζbi ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp)))))

variable {S : Type} [Fintype S] [DecidableEq S]

def BMat (d : Q.NFData P A) (E : SlopeTestRemainingChoices S A) : Prop := ∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0

theorem BMat.mul {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E * F) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun k _ => span_mul d (hE i k) (hF k j)

theorem BMat.add {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E + F) :=
  fun i j => add_mem (hE i j) (hF i j)

theorem BMat.sub {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E - F) :=
  fun i j => sub_mem (hE i j) (hF i j)

theorem BMat.smul {d : Q.NFData P A} {E : SlopeTestRemainingChoices S A} (c : ℂ) (hE : BMat d E) : BMat d (c • E) :=
  fun i j => Submodule.smul_mem _ c (hE i j)

theorem bMat_io {d : Q.NFData P A} {a : A} (ha : a ∈ nfSpan d ∅ 0 0 0) : BMat d (io a : SlopeTestRemainingChoices S A) := fun i j => by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem io_add (a b : A) : (io (a + b) : SlopeTestRemainingChoices S A) = io a + io b := map_add (Matrix.scalar (Ix S)) a b

theorem io_mul (a b : A) : (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := map_mul (Matrix.scalar (Ix S)) a b

theorem inv_subset {r : ℕ} (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) :
    ∀ Y ∈ (ofWord L st w).inv, Y ∈ st.inv := by
  induction w with
  | nil => exact fun Y hY => hY
  | cons l w ih =>
    intro Y hY
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1

theorem comm_id {R : Type*} [Ring R] (l K E α β γ : R) (h1 : β * l = l * β) (h2 : β * K = K * β)
    (h3 : α * K = K * α) :
    α * ((l + K * E) * β - β * (l + K * E)) * γ = K * (α * (E * β - β * E) * γ) := by
  have : (l + K * E) * β - β * (l + K * E) = K * (E * β - β * E) := by
    rw [mul_add, h1, ← mul_assoc β K, h2]; noncomm_ring
  rw [this, ← mul_assoc α K, h3]; simp only [mul_assoc]

end

theorem word_l_shape : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).l L Y = io (d.L.l0 Y) + kapL d.L * E := by
  intro P A _ _ _ _ d hd L st s hT S _ _ w hA Y hY hY1
  obtain ⟨hk, h0⟩ := GlobalTheory.T.frameStart_constants_normalForm_empty_word P A d hd L st s hT
  obtain ⟨E0, hE0, e0⟩ := h0 Y (inv_subset L st w Y hY)
  obtain ⟨hH, hS, -⟩ := hT
  obtain ⟨-, -, -, -, -, -, -, s1, s2, s3, -, s4, s5⟩ := hS
  have hkap : (kapL L : SlopeTestRemainingChoices S A) = kapL d.L := by simp only [kapL, s1, s2, s4]
  have htz : (tz L : SlopeTestRemainingChoices S A) = tz d.L := by simp only [tz, s3, s5]
  have hl0 : (st.frame : FrameData S A).l L Y = io (d.L.l0 Y) + kapL d.L * io E0 := by
    show io (L.l0 Y) + io (L.ζb * L.ζi * L.GGi) * io (st.ee Y) =
      io (d.L.l0 Y) + io (d.L.ζb * d.L.ζi * d.L.GGi) * io E0
    rw [← io_mul, ← io_add, e0, io_add, io_mul]
  have hsh := (Formalism.FourierDecayAlt.P.l_shape A S P.r L st w hH.starLev hH.start hA).2.2 Y hY hY1
  rw [hl0, hkap, htz] at hsh
  have hc := hd.2.2.1.2.1
  have cζb : ∀ f, Commute (d.κ f) d.L.ζb := fun f => hc f _ (by simp [LevelData.fns])
  have cζi : ∀ f, Commute (d.κ f) d.L.ζi := fun f => hc f _ (by simp [LevelData.fns])
  have cG : ∀ f, Commute (d.κ f) d.L.GGi := fun f => hc f _ (by simp [LevelData.fns])
  have cn : ∀ f, Commute (d.κ f) d.L.nab := fun f => hc f _ (by simp)
  have cio : ∀ (a : A), (∀ f, Commute (d.κ f) a) → ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io a = io a * α := by
    intro a ha α hα
    refine (Formalism.FourierDecayAlt.P.TLA.L1.io_comm fun i j => ?_).symm.eq
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact (ha f).symm
  have cK : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * kapL d.L = kapL d.L * α :=
    cio _ fun f => ((cζb f).mul_right (cζi f)).mul_right (cG f)
  have cl : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io (d.L.l0 Y) = io (d.L.l0 Y) * α :=
    cio _ fun f => (cn f).neg_right.sub_right
      ((show Commute (d.κ f) (algebraMap ℂ A (Y + 1 / 2)) from (Algebra.commutes _ _).symm).mul_right
        ((cζb f).mul_right (cG f)))
  have hB : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → BMat d α := by
    intro α hα i j
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact kappa_mem d f
  have hE : BMat d (io E0 : SlopeTestRemainingChoices S A) := bMat_io hE0
  have key : ∀ M ∈ TL.dSpan st (io (d.L.l0 Y) + kapL d.L * io E0 : SlopeTestRemainingChoices S A) (kapL d.L) (tz d.L),
      ∃ E : SlopeTestRemainingChoices S A, BMat d E ∧ M = kapL d.L * E := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨α, β, γ, h1, h2, h3, rfl⟩ | ⟨γ, h, rfl | rfl⟩
      · exact ⟨_, ((hB α h1).mul ((hE.mul (hB β h2)).sub ((hB β h2).mul hE))).mul (hB γ h3),
          comm_id _ _ _ _ _ _ (cl β h2) (cK β h2) (cK α h1)⟩
      · exact ⟨γ, hB γ h, rfl⟩
      · exact ⟨tz d.L * γ, (bMat_io (Submodule.smul_mem _ _ (zbi_mem d))).mul (hB γ h), mul_assoc _ _ _⟩
    | zero => exact ⟨0, fun _ _ => zero_mem _, (mul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨E, hE, rfl⟩ := hx
      obtain ⟨F, hF, rfl⟩ := hy
      exact ⟨E + F, hE.add hF, (mul_add _ _ _).symm⟩
    | smul c x _ hx =>
      obtain ⟨E, hE, rfl⟩ := hx
      exact ⟨c • E, hE.smul c, (mul_smul_comm _ _ _).symm⟩
  obtain ⟨E, hE', e⟩ := key _ hsh
  refine ⟨io E0 + E, hE.add hE', ?_⟩
  rw [sub_eq_iff_eq_add.mp e, mul_add]
  abel

end GlobalTheory.HatNF.WordL
end

section

namespace GlobalTheory.HatNF.GenPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem star_inv_eq {x xi y yi : A} (h : star x = y) (hx : x * xi = 1) (hy : y * yi = 1) : star xi = yi := by
  have h1 : star xi * y = 1 := by rw [← h, ← star_mul, hx, star_one]
  calc star xi = star xi * (y * yi) := by rw [hy, mul_one]
    _ = yi := by rw [← mul_assoc, h1, one_mul]

theorem star_list_prod (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, star_mul, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

variable {P : M.Par} {d : Q.NFData P A}

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ hats d.L) : b * h ∈ nfSpan d (hats d.L) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem ahat_mem (y : ℂ) : d.L.Ahat y ∈ hats d.L := Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
theorem plusHatR_mem_hatLettersAllPoints (y : ℂ) : d.L.R0 y ∈ hats d.L := Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))

theorem kappa_comm (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahat y) ∧ Commute (d.κ f) (d.L.R0 y) := by
  obtain ⟨-, -, hR, -, -, -, hs⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nab := hR.2.1 f _ (Or.inr (by simp))
  have hp : ∀ l, Commute (d.κ f) (d.L.p l) := fun l => hs f _ (by simp [TL.siteOps])
  have hT := d.L.inv_comm_Tprod hp (fun l => hf _ (d.L.inv_mem_c l)) (fun l => hf _ (d.L.inv_mem_ci l)) y
  have hDr : Commute (d.κ f) d.L.Dr := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_c l)
  have hDrb : Commute (d.κ f) d.L.Drb := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_cb l)
  have hl0 : Commute (d.κ f) (d.L.l0 y) :=
    hn.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
      ((hf _ d.L.inv_mem_ζb).mul_right (hf _ d.L.inv_mem_GGi)))
  exact ⟨hDr.mul_right (hT 0 0),
    (hDrb.mul_right (hf _ d.L.inv_mem_GG)).mul_right ((hl0.mul_right (hT 0 0)).add_right (hT 1 0))⟩

theorem ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * ssn d l = ssn d l * d.L.Ahat (y - 1) ∧ d.L.R0 y * ssn d l = ssn d l * d.L.R0 (y - 1) := by
  obtain ⟨-, -, hR, -, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS l) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm.eq)
    (fun m => (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).symm.eq) (fun m => (hc _ (Or.inr ⟨m, rfl⟩)).symm.eq) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) y
  exact ⟨this.1, this.2.1⟩

variable [StarModule ℂ A]

theorem star_GG (h : HatHyp d) : star d.L.GG = d.L.GG := by
  obtain ⟨-, ⟨hz, -, hT⟩, -⟩ := h
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  rw [d.L.GG_def, star_sub, star_mul, hz, hzb, Algebra.algebraMap_eq_smul_one, star_smul, hT, star_one]

theorem star_GGi (h : HatHyp d) : star d.L.GGi = d.L.GGi := star_inv_eq (star_GG h) d.L.GG_GGi d.L.GG_GGi

theorem star_fns (h : HatHyp d) : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
  have hG := star_GG h
  have hGi := star_GGi h
  obtain ⟨-, ⟨hz, -, -⟩, -, -, hc, hci, -⟩ := h
  have hzi : star d.L.ζi = d.L.ζbi := star_inv_eq hz d.L.ζ_ζi d.L.ζb_ζbi
  intro x hx
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
  · rw [hc]; exact d.L.inv_mem_cb l
  · rw [hci]; exact d.L.inv_mem_cbi l
  · rw [← hc, star_star]; exact d.L.inv_mem_c l
  · rw [← hci, star_star]; exact d.L.inv_mem_ci l
  · rw [hz]; exact d.L.inv_mem_ζb
  · rw [hzi]; exact d.L.inv_mem_ζbi
  · rw [← hz, star_star]; exact d.L.inv_mem_ζ
  · rw [← hzi, star_star]; exact d.L.inv_mem_ζi
  · rw [hG]; exact d.L.inv_mem_GG
  · rw [hGi]; exact d.L.inv_mem_GGi

omit [StarModule ℂ A] in
theorem star_ssn (h : HatHyp d) (l : ℕ) : star (ssn d l) = star (d.SS l) * (d.L.Dr * d.L.Drbi) := by
  obtain ⟨-, -, -, -, hc, hci, -⟩ := h
  have h1 : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext fun m => by rw [Function.comp, ← hc, star_star]
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_c m)
  have h2 : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext hci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_cbi m)
  unfold ssn
  rw [star_mul, star_mul, h1, h2, cl_comm d.L (memDrbi d.L) (memDr d.L)]

theorem star_ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * star (ssn d l) = star (ssn d l) * d.L.Ahat (y + 1) ∧
      d.L.R0 y * star (ssn d l) = star (ssn d l) * d.L.R0 (y + 1) := by
  have hGi := star_GGi h
  have hF := star_fns h
  rw [star_ssn h]
  obtain ⟨-, ⟨hz, hn, -⟩, hR, hp, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  have hns : star d.L.nabs = d.L.nab := by rw [← hn, star_star]
  have key : ∀ x, Commute (d.SS l) (star x) → x * star (d.SS l) = star (d.SS l) * x := fun x hx => by
    have := congrArg star hx.eq
    simpa [star_mul] using this
  have hf : ∀ x ∈ d.L.fns, x * star (d.SS l) = star (d.SS l) * x :=
    fun x hx => key x (hc _ (Or.inl (Or.inl (hF x hx))))
  have hp1 : ∀ m, d.L.p m * star (d.SS l) = star (d.SS l) * d.L.p m := fun m =>
    key _ (by rw [hp]; exact (hc _ (Or.inr ⟨m, rfl⟩)).neg_right)
  have hp2 : ∀ m, d.L.pb m * star (d.SS l) = star (d.SS l) * d.L.pb m := fun m =>
    key _ (by
      have : star (d.L.pb m) = -d.L.p m := by
        have := congrArg star (hp m)
        rw [star_star, star_neg] at this
        rw [this, neg_neg]
      rw [this]; exact (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).neg_right)
  have c1 : star (d.SS l) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζb, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζb).eq]
  have c2 : star (d.SS l) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζ, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζ).eq]
  have e1 : d.L.nab * star (d.SS l) = star (d.SS l) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS l) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hns, hz, hGi] at this
    rw [← c1, this]; abel
  have e2 : d.L.nabs * star (d.SS l) = star (d.SS l) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS l) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hn, hzb, hGi] at this
    rw [← c2, this]; abel
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS l)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) hf hp1 hp2 e1 e2 y
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2.1⟩

end

theorem plus_hats_pass_generators : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ,
      d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrb : d.L.Drb * d.L.Di ∈ bmon d := by
    rw [drb_eq]; exact Submonoid.mul_mem _ mDbD mζbi
  have hbm := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · refine ⟨by rw [(hat_ζi d.L y).1]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_ζi_R]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _)) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (mem_span mDbD (ahat_mem _)))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDbD) (ahat_mem _))))
    · exact ⟨by rw [← (hat_ζbi d.L y).1]; exact mem_span hbm (ahat_mem _),
        by rw [← (hat_ζbi d.L y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
    · refine ⟨by rw [gen_DD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDD hdrb) (ahat_mem _)))
    · refine ⟨by rw [gen_DbD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DbD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDbD hdrb) (ahat_mem _)))
  · exact ⟨by rw [← (kappa_comm h f y).1.eq]; exact mem_span hbm (ahat_mem _),
      by rw [← (kappa_comm h f y).2.eq]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by rw [(ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by rw [(ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by beta_reduce; rw [(star_ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by beta_reduce; rw [(star_ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩

end GlobalTheory.HatNF.GenPlus
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.scaledThetaTranslationQuotient_elliptic : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (t : ℂ) (s : ℕ), 0 < s → Nat.Coprime s q → InOK d ((s : ℂ) * t) → let φ : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z); Ell M.L φ ∧ AnalyticAt ℂ φ 0 ∧ (∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p) ∧ (∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p) ∧ Bdd (hat M.ι (C ω * logS) φ) := by
  first | exact @GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic | exact GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic | (intros; apply GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem l2SG_of_ae_smul {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F G : Mx k r → Wp) (c : ℝ)
    (h : ∀ᵐ x ∂νq, F (Matrix.of x) = (c : ℂ) • G (Matrix.of x)) :
    PI.BesselPeriodGGP.l2SG νq F = ENNReal.ofReal (c ^ 2) * PI.BesselPeriodGGP.l2SG νq G := by
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow]
  congr 1
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg c), ← Real.norm_eq_abs, ← Complex.norm_real,
    ofReal_norm_eq_enorm]
  rfl

theorem scaled_bessel_isometric : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → IsBeL R z π μW μN l → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → NzOn R l → IsIsoB R z π νq (fun w => ((Real.sqrt dd : ℝ) : ℂ) • l w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq l dd hDS hgap hok hS hl hd hnz
  refine ⟨Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hl.1 _, fun w hw => ?_⟩
  obtain ⟨v, hv, hlv⟩ := GlobalTheory.bessel_nonzero_on_translates hH k r ε mu R Wp z π l hDS hl.1 hnz
  obtain ⟨-, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  obtain ⟨-, -, hdd, hP⟩ := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS dd hd v hv (l v)
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hn : 0 < ‖l v‖ := norm_pos_iff.mpr hlv
  have hin : ⟪l v, l v⟫_ℂ = ((‖l v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; first | rfl | norm_cast | simp
  have hbe : ∀ y ∈ R.sm, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN y v (l v) = ((‖l v‖ ^ 2 : ℝ) : ℂ) • l y := by
    intro y hy
    rw [(hl.2 y hy v hv).2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hin]
  have hre : (⟪l v, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v (l v)⟫_ℂ).re = ‖l v‖ ^ 2 * ‖l v‖ ^ 2 := by
    rw [hbe v (hTK v hv), inner_smul_right, hin, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [l2SG_of_ae_smul νq _ (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v (l v))
    (Real.sqrt dd / ‖l v‖ ^ 2), hP w hw, hre, ← ENNReal.ofReal_mul (sq_nonneg _)]
  · congr 1
    rw [div_pow, Real.sq_sqrt hdd.le]
    field_simp
  · filter_upwards [hae] with x hx
    rw [hbe _ (hsm _ hx w hw), smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos hn 2).ne']

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  first | exact @GlobalTheory.BesselOrbital.bessel_integral_eq_smul | exact GlobalTheory.BesselOrbital.bessel_integral_eq_smul | (intros; apply GlobalTheory.BesselOrbital.bessel_integral_eq_smul <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  first | exact @GlobalTheory.DualStepBound.dual_step_bound | exact GlobalTheory.DualStepBound.dual_step_bound | (intros; apply GlobalTheory.DualStepBound.dual_step_bound <;> assumption)
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem _root_.GlobalTheory.T.splitCasimir_eigenspace_irreducible_dualStandard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + (n : ℂ)) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ Module.End.eigenspace Om (β + L l + (n : ℂ)) ≤ CapSp Et (shf β (Function.update L l (L l - 1))) := by
  first | exact @GlobalTheory.casimir_eigenspace_irred_dual_standard | exact GlobalTheory.casimir_eigenspace_irred_dual_standard | (intros; apply GlobalTheory.casimir_eigenspace_irred_dual_standard <;> assumption)
end
