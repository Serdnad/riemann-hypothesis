module

public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle153
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle149
public import Formalism.HermitianCurvature.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaCapelliSymmOfXiExists
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle143
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle037
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle011
public import Formalism.HermitianCurvature.StatementD
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle161
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle159
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.wignerShiftedPlacesExist_proof

theorem gap_one {P : M.Par} (h : P.OK) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    P.u' (i + 1) + 1 ≤ P.u' i := by
  have hg := h.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  linarith

theorem gap_nat {P : M.Par} (h : P.OK) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  have h1 := gap_one h i hi
  rw [Finset.mem_Icc] at hi
  obtain ⟨a, ha⟩ := h.int_u' i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
  obtain ⟨c, hc⟩ := h.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h2 : ((0 : ℤ) : ℝ) ≤ ((a - c - 1 : ℤ) : ℝ) := by push_cast; linarith
  have h3 : (0 : ℤ) ≤ a - c - 1 := by exact_mod_cast h2
  refine ⟨(a - c - 1).toNat, ?_⟩
  have h4 : (((a - c - 1).toNat : ℤ) : ℝ) = ((a - c - 1 : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg h3]
  push_cast at h4
  linarith

theorem ok_plus {P : M.Par} (h : P.OK) (l n₀ : ℕ) (he : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i)
    (hg : 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) :
    (shP P P.u (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)))).OK := by
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨h.k_pos, h.T_pos, h.T'_pos, h.int_u, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    change ∃ n : ℤ, Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) i - P.u 1 = n
    by_cases hil : i = l + 1
    · subst hil
      refine ⟨a + n₀, ?_⟩
      rw [Function.update_self]; push_cast; linarith
    · exact ⟨a, by rw [Function.update_of_ne hil]; exact ha⟩
  · intro i hi
    have h1 := gap_one h i hi
    change i ∈ Finset.Icc 1 (P.k - 1) at hi
    rw [Finset.mem_Icc] at hi
    have e1 := he i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
    have e2 := he (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    change max (P.u (i + 1)) (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) (i + 1)) + 1 / 2 ≤
      min (P.u i) (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) i) - 1 / 2
    rw [e1, e2]
    by_cases ha : i = l
    · subst ha
      rw [Function.update_self, Function.update_of_ne (by omega), min_self, max_eq_right (by linarith)]
      linarith
    · rw [Function.update_of_ne (show i + 1 ≠ l + 1 by omega), max_self]
      by_cases hb : i = l + 1
      · subst hb
        rw [Function.update_self, min_eq_left (by linarith)]
        linarith
      · rw [Function.update_of_ne hb, min_self]
        linarith

theorem ok_minus {P : M.Par} (h : P.OK) (l n₀ : ℕ) (he : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i)
    (hg : 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) :
    (shP P P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))).OK := by
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨h.k_pos, h.T_pos, h.T'_pos, h.int_u, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    change ∃ n : ℤ, Function.update P.u' l (P.u' l - (n₀ : ℝ)) i - P.u 1 = n
    by_cases hil : i = l
    · subst hil
      refine ⟨a - n₀, ?_⟩
      rw [Function.update_self]; push_cast; linarith
    · exact ⟨a, by rw [Function.update_of_ne hil]; exact ha⟩
  · intro i hi
    have h1 := gap_one h i hi
    change i ∈ Finset.Icc 1 (P.k - 1) at hi
    rw [Finset.mem_Icc] at hi
    have e1 := he i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
    have e2 := he (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    change max (P.u (i + 1)) (Function.update P.u' l (P.u' l - (n₀ : ℝ)) (i + 1)) + 1 / 2 ≤
      min (P.u i) (Function.update P.u' l (P.u' l - (n₀ : ℝ)) i) - 1 / 2
    rw [e1, e2]
    by_cases ha : i = l
    · subst ha
      rw [Function.update_self, Function.update_of_ne (by omega), max_self, min_eq_right (by linarith)]
      linarith
    · rw [Function.update_of_ne ha, min_self]
      by_cases hb : i + 1 = l
      · subst hb
        rw [Function.update_self, max_eq_left (by linarith)]
        linarith
      · rw [Function.update_of_ne hb, max_self]
        linarith

theorem shiftExists_of (hA : GlobalTheory.WigSh.AmapsShExists) : GlobalTheory.WigSh.ShiftExists := by
  obtain ⟨c₃, hc⟩ := hA
  obtain ⟨Cb, hCb, hS⟩ := GlobalTheory.WithRightAction.exists_place_other_right_type
  refine ⟨c₃, Cb, hCb, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p l n₀ lp lm b he hl1 hl2 hg hb hn hb1 hp1 hp2 hm1 hm2
  obtain ⟨hOK, hz, hz', hT, hT', hπ, hπ'⟩ := p.hP
  obtain ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, πp, πm, -, -, htp, htm, -⟩ :=
    GlobalTheory.WigSh.exists_shifted_types_lower_bound Wq P.k P.r p.T.base.z' p.T.base.π' P.u' l n₀ b hz'
      (by rw [hT']; exact hOK.T'_pos) hπ' (gap_nat hOK) hl1 hl2 hg hb hn hb1
  obtain ⟨pp, a1, a2, a3, a4, -, a6, a7, a8⟩ := hS P Wp Wq Wqp p P.u
    (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ))) πp lp
    ⟨ok_plus hOK l n₀ he hg, hz, hz', hT, hT', hπ, htp⟩ hp1 hp2
  obtain ⟨pm, b1, b2, b3, b4, -, b6, b7, b8⟩ := hS P Wp Wq Wqm p P.u
    (Function.update P.u' l (P.u' l - (n₀ : ℝ))) πm lm
    ⟨ok_minus hOK l n₀ he hg, hz, hz', hT, hT', hπ, htm⟩ hm1 hm2
  obtain ⟨Ap, Am, ApPt, AmPt, c1, c2, c3, c4⟩ := hc P Wp Wq Wqp Wqm P.u
    (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ))) P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))
    p pp pm l n₀ b a2 a3 b2 b3 (fun h _ => congrFun a4 h) (fun h _ => congrFun b4 h) a6 a7 b6 b7 hl1 hl2 hg hb hn hb1
    (fun i _ => by
      by_cases h : i = l + 1
      · subst h; simp
      · rw [Function.update_of_ne h, if_neg h])
    (fun i _ => by
      by_cases h : i = l
      · subst h; simp
      · rw [Function.update_of_ne h, if_neg h])
  exact ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, pp, pm, Ap, Am, ApPt, AmPt, a1, b1, a2, a3, a4, b2, b3, b4, a8, b8,
    c1, c2, c3, c4⟩

theorem shiftExists : GlobalTheory.WigSh.ShiftExists := shiftExists_of GlobalTheory.T.wignerMapsThreePlaces_exists

end GlobalTheory.wignerShiftedPlacesExist_proof
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem pointwiseBound_at_place_of_locBessel : ThmBpDS → ∀ Ch : ℝ, ∃ C₄ Cg₀ : ℝ, 0 ≤ C₄ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq) (n₀ : ℕ), IsStdOf L μsec p.T.base ∧ n₀ ≤ 30 * (D.R.rS + 1) ^ 2 + 6 ∧ TBB.ThmBpAt p f b C₄ n₀ (2 * (D.R.rS + 1)) := by
  classical
  intro hT Ch
  obtain ⟨C₄, G₀, hC₄, h⟩ := hT Ch 2 (by norm_num)
  refine ⟨C₄, G₀, hC₄, fun Cg hCg D L lam0 f μsec ka b hL hg hf hsec => ?_⟩
  obtain ⟨-, hε, -, -, -, hS, -⟩ := hL
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨U, U', p, hU, hstd⟩ :=
    GlobalTheory.T.exists_place_of_localBesselDatum_interlacing D.R.k D.R.rS L μsec lam0 (by omega) hk hsec hS.2.1 hS.2.2.1
  have hu : (fun i : Fin D.R.k => U (i.val + 1)) = L.u := funext fun i => (hU i).1
  have hu' : (fun i : Fin D.R.k => U' (i.val + 1)) = L.u' := funext fun i => (hU i).2
  have he : L.ε = PI.BesselPeriodGGP.eps48 D.R.k D.R.rS := by
    rw [hε]; funext i; rfl
  obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
  have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
  refine ⟨U, U', p, if ∀ i ∈ Finset.Icc 1 D.R.k, U i = U' i then 30 * (D.R.rS + 1) ^ 2 + 6 else 0, hstd,
    by split_ifs <;> omega, ?_⟩
  refine h Cg hCg ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq p lam0 L.lam ka b _ _
    ⟨L.Hs, L.σ⟩ f ?_ hg ?_ ?_ (fun e => if_pos e) (fun e => if_neg e) ?_ ?_
  · show StdHyp Ch Cg D.R.k D.R.rS _ lam0 (fun i : Fin D.R.k => U (i.val + 1))
      (fun i : Fin D.R.k => U' (i.val + 1)) _ _ ka b
    rw [hu, hu', ← he]
    exact hS
  · show BranchingSupport.Rep.IsDS (k := D.R.k) (r := D.R.rS) ⟨L.Hs, L.σ⟩ (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) L.lam
    rw [← he]
    exact ⟨L.hlam, v1.1 L.hσ⟩
  · obtain ⟨P, Q, hQ, hP, hfe⟩ := hf
    exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
      simpa using hfe g⟩
  · show 3 * (D.R.rS + 1) ≤ 2 * (2 * (D.R.rS + 1))
    omega
  · show ((2 * (D.R.rS + 1) : ℕ) : ℝ) ≤ 2 * ((D.R.rS : ℝ) + 1) ^ 2
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    push_cast
    nlinarith

end GlobalTheory
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem levelZero_energy_le_of_eigen_sum :
    GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (s : ℂ) (nn : ℝ → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (s = 1 ∨ s = -1) → B.AB k r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w : List (Bool × ℝ), (C7.principalHermitianLattice D s w F).re ≤ (w.map fun l => nn l.2).prod * (B.beta D F F).re := by
  intro hXi k r Wp Wq _ _ _ _ _ _ D lam d A s nn F hs hA hex hnn w
  obtain ⟨N₀, Fi, ν, hν, hcl, hev, hF⟩ := hex
  obtain ⟨σ, hσs, hσ⟩ : ∃ σ : ℝ, s = (σ : ℂ) ∧ |σ| = 1 := by
    rcases hs with h | h
    · exact ⟨1, by simp [h], by simp⟩
    · exact ⟨-1, by simp [h], by simp⟩
  have h5 : ∀ i, B.InCC A 5 (Fi i) := fun i => (hcl i).2 5
  set e : Fin N₀ → ℝ → ℝ := fun i Y => ∏ t, (Y + lam t + (ν i t : ℝ)) with he
  set c : Fin N₀ → Bool × ℝ → ℝ := fun i a => σ * e i a.2 with hc
  have hF1 : ∀ g ∈ B.GV k r, F g = ∑ i ∈ Finset.univ, (1 : ℂ) • Fi i g := by
    intro g hg; simpa using hF g hg
  have hfold := GlobalTheory.foldr_capelli_sum_eigen k r Wp Wq N₀ Fi (fun i Y => ((e i Y : ℝ) : ℂ)) s F (fun i => (hcl i).1)
    (fun i Y g hg => hev i Y g hg) hF w
  have e1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ _ (fun _ => 1) Fi _ F hA h5 hfold hF1
  have e2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ (fun _ => 1) (fun _ => 1) Fi F F hA h5
    hF1 hF1
  have hcast : ∀ i, (w.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((w.map (c i)).prod : ℝ) : ℂ) := by
    intro i
    have : ∀ v : List (Bool × ℝ),
        (v.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((v.map (c i)).prod : ℝ) : ℂ) := by
      intro v
      induction v with
      | nil => simp
      | cons a v ih =>
        rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, hσs]
        simp only [hc, Complex.ofReal_mul]
    exact this w
  have key := gram_blockDiagonal_energy_bound (Fin N₀) (Bool × ℝ) (fun i j => B.beta D (Fi i) (Fi j)) c w
    (fun l => nn l.2) ?_ ?_ ?_
  · unfold C7.principalHermitianLattice
    rw [e1, e2]
    simp only [star_one, mul_one, one_mul, hcast]
    exact key
  · intro S
    have e3 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) S S (fun _ => 1) (fun _ => 1) Fi
      (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) hA h5
      (fun _ _ => rfl) (fun _ _ => rfl)
    have e4 := GlobalTheory.BetaPos.beta_self_re_nonneg k r Wp Wq D (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g)
    rw [e3] at e4
    simpa only [star_one, mul_one, one_mul] using e4
  · intro i j a _ hne
    have hne' : e i a.2 ≠ e j a.2 := fun h => hne (by simp only [hc, h])
    have hsym := GlobalTheory.beta_capelli_symm_of_bessel hXi k r Wp Wq D a.2 A (Fi i) (Fi j) hA (hcl i) (hcl j)
    have h1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => ((e i a.2 : ℝ) : ℂ)) (fun _ => 1) Fi (Q.CV k r (a.2 : ℂ) (Fi i)) (Fi j) hA h5
      (fun g hg => by rw [Finset.sum_singleton]; exact hev i a.2 g hg) (fun g _ => by simp)
    have h2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => 1) (fun _ => ((e j a.2 : ℝ) : ℂ)) Fi (Fi i) (Q.CV k r (a.2 : ℂ) (Fi j)) hA h5
      (fun g _ => by simp) (fun g hg => by rw [Finset.sum_singleton]; exact hev j a.2 g hg)
    simp only [Finset.sum_singleton, star_one, mul_one, one_mul,
      Complex.star_def, Complex.conj_ofReal] at h1 h2
    rw [h1, h2] at hsym
    have hcc : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne')
    have h0 : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) * B.beta D (Fi i) (Fi j) = 0 := by
      rw [sub_mul, hsym, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hcc
  · intro i a _
    refine le_trans ?_ (hnn a.2)
    simp only [hc, he, abs_mul, hσ, one_mul, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun t _ => (abs_add_le _ _).trans ?_)
    have : |(ν i t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν i t
    linarith

end GlobalTheory
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound : ∃ Cc : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (N : ℕ), C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → Tendsto (fun n : ℕ => B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₂ g))) atTop (𝓝 (B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((D.cutF Bs χ f ε₁)) w) (D.cutF Bs χ f ε₂))) ∧ ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g))‖ ≤ K / ((n : ℝ) + 1) := by
  first | exact @GlobalTheory.LevelZeroApprox.beta_approx | exact GlobalTheory.LevelZeroApprox.beta_approx | (intros; apply GlobalTheory.LevelZeroApprox.beta_approx <;> assumption)
end
