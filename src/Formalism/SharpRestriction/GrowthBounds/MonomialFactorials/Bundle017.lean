module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle015
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinPosEqCast
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle016
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle011
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.UTopVal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem loss_num (s t r Λ L1 U k0 : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s) (hr : 4 ≤ r) (hΛ : 1 ≤ Λ) (hL0 : 0 ≤ L1)
    (hL : L1 ≤ Λ) (hU : U ≤ (t + 1) * ((r + 1) * (Λ + 1) + 1)) (hk : 0 ≤ k0) :
    ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 + 2 * U ≤ 10 * (s + 1) * (r + 1) * Λ + k0 := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hA : 0 ≤ (((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1) := by nlinarith
  have e1 : ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 ≤
      ((2 * s + 2) * r + 3 * (s + 1)) * Λ := by
    calc ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1
        ≤ ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * Λ := mul_le_mul_of_nonneg_left hL hA
      _ ≤ ((2 * s + 2) * r + 3 * (s + 1)) * Λ := by nlinarith
  have e2 : U ≤ (s + 1) * ((r + 1) * (Λ + 1) + 1) := by
    have : 0 ≤ (r + 1) * (Λ + 1) + 1 := by nlinarith
    nlinarith
  have e3 : (s + 1) * ((r + 1) * (Λ + 1) + 1) ≤ (s + 1) * ((2 * r + 3) * Λ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  nlinarith

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restValNum_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestValNum C0 CE1 CE2 X := by
  classical
  intro aTop hT aPlus hP b hK l hl j' jp' hl' μ hw
  obtain ⟨hA1, h2, h3, h4, h5⟩ := gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop hT aPlus hP b hK
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hlok : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK l.1 l.2 := (Finset.mem_filter.1 hl).2
  have hv := val_gen X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (gB_blockOK C0 CE1 CE2 X aTop aPlus b) (aBig X)
    h2 h3 h4 h5 l.1 l.2 hlok j' jp' hl' μ hw
  have hvR : (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
      degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) ≤
      (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) +
        (((((2 * (X.s : ℝ) + 1) + 1) * (X.r : ℝ) + (((X.S C0 CE1 CE2).t : ℝ) + 1) * 2) +
          (((X.S C0 CE1 CE2).t : ℝ) + 1)) * (Nat.log X.p (8 * aBig X + X.r) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 hv
    push_cast at this
    exact this

  have hmR : (4 : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast hF.m4
  have hp25 : (25 : ℝ) ≤ (X.p : ℝ) := by nlinarith [hF.p_ge]
  have hp1 : (1 : ℝ) < (X.p : ℝ) := by linarith
  have hs0 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
  have ha1 : (1 : ℝ) ≤ (X.L.a : ℝ) := hF.a1
  have hsm : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hF.s_le
  have hsp : 3 * (X.s : ℝ) + 2 ≤ (X.p : ℝ) := by nlinarith [hF.p_ge]
  have hbase : (0 : ℝ) < 8 * (X.L.a : ℝ) + (X.r : ℝ) := by linarith
  have hΛ : 1 ≤ lgA X.p X.L.a X.r := by
    unfold lgA
    have : 0 ≤ Real.logb X.p (8 * (X.L.a : ℝ) + (X.r : ℝ)) := Real.logb_nonneg hp1 (by linarith)
    linarith
  have hbig : Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) ≤ lgA X.p X.L.a X.r := by
    have e1 : 8 * (aBig X : ℝ) + (X.r : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * (X.L.a : ℝ) + (X.r : ℝ)) := by
      unfold aBig; push_cast; nlinarith
    have e0 : (0 : ℝ) < 8 * (aBig X : ℝ) + (X.r : ℝ) := by
      have : (0 : ℝ) ≤ (aBig X : ℝ) := Nat.cast_nonneg _
      linarith
    have e2 := Real.logb_le_logb_of_le hp1 e0 e1
    rw [Real.logb_mul (by linarith) hbase.ne'] at e2
    have e3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1 := by
      rw [Real.logb_le_iff_le_rpow hp1 (by linarith), Real.rpow_one]
      exact hsp
    unfold lgA
    linarith
  have hL1 : (Nat.log X.p (8 * aBig X + X.r) : ℝ) ≤ lgA X.p X.L.a X.r := by
    have := Real.natLog_le_logb (8 * aBig X + X.r) X.p
    push_cast at this
    exact this.trans hbig
  have hU : (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
      (((X.S C0 CE1 CE2).t : ℝ) + 1) * (((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) + 1) := by
    have e1 : (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) =
        (((X.S C0 CE1 CE2).t : ℝ) + 1) * (⌈((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r⌉₊ : ℝ) := by
      unfold expU
      push_cast
      rfl
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e2 : Formalism.GM.lgV2 X.p (aBig X) X.r ≤ lgA X.p X.L.a X.r + 1 := by
      unfold Formalism.GM.lgV2
      linarith
    have e3 : 0 ≤ Formalism.GM.lgV2 X.p (aBig X) X.r := by
      unfold Formalism.GM.lgV2
      have : 0 ≤ Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) := by
        apply Real.logb_nonneg hp1
        have : (0 : ℝ) ≤ (aBig X : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have e4 := (Nat.ceil_lt_add_one (show 0 ≤ ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r by positivity)).le
    refine e4.trans ?_
    have : ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r ≤ ((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    linarith
  have hk0 : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r := by
    unfold kappaZeroExponent
    have : 0 ≤ Real.logb X.p (X.L.a : ℝ) := Real.logb_nonneg hp1 ha1
    positivity
  have hts : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ) := by
    have : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
    exact_mod_cast this
  have hfin := loss_num (X.s : ℝ) ((X.S C0 CE1 CE2).t : ℝ) (X.r : ℝ) (lgA X.p X.L.a X.r)
    (Nat.log X.p (8 * aBig X + X.r) : ℝ) (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ)
    (kappaZeroExponent X.p X.L.a X.Nt X.r) (Nat.cast_nonneg _) hts hmR hΛ (Nat.cast_nonneg _) hL1 hU hk0
  unfold levelPassageLoss
  linarith

theorem block_valuation_over_Zp_holds {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_numeric_bound C0 CE1 CE2 X hCYb hCE1 hCE2 hH (restValNum_proved C0 CE1 CE2 X hCYb hCE1 hCE2 hH)

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Gen

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem foldr_comm_of (φ : ι → V →ₗ[K] V) (ψ : V →ₗ[K] V) (l : List ι) (h : ∀ j ∈ l, ∀ x, ψ (φ j x) = φ j (ψ x))
    (x : V) : ψ ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) x) = (l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) (ψ x) := by
  induction l generalizing x with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [h j (by simp), ih (fun k hk => h k (by simp [hk]))]

theorem foldr_selfAdj (B : V → V → K) (hB : ∀ a b, B a b = B b a) (φ : ι → V →ₗ[K] V) (l : List ι)
    (hs : ∀ i ∈ l, ∀ a b, B (φ i a) b = B (φ i b) a)
    (hc : l.Pairwise (fun i j => ∀ x, φ i (φ j x) = φ j (φ i x))) (a b : V) :
    B ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) a) b = B ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) b) a := by
  induction l generalizing a b with
  | nil => simpa using hB a b
  | cons j l ih =>
    rw [List.pairwise_cons] at hc
    have hsl : ∀ i ∈ l, ∀ a b, B (φ i a) b = B (φ i b) a := fun i hi => hs i (by simp [hi])
    have hcomm := foldr_comm_of φ (φ j) l (fun i hi x => (hc.1 i hi x)) b
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [hs j (by simp), hB, ih hsl hc.2, hcomm]

end Gen

def RestTieComm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (G : Formalism.GM.M.BlockData N), G.BlockOK →
    ∀ (j : Fin G.T.t → ℕ) (jp : ℕ) (i i' : Fin G.T.t), i ≠ i' → ∀ x : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
                (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
                ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
                (G.T.z i)
        (Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i'), c))
          (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i' + 1), c))
          ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i'))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i' + 1)))
          (G.T.z i') x) =
      Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i'), c))
                (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i' + 1), c))
                ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i'))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i' + 1)))
                (G.T.z i')
        (Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
          (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
          ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
          (G.T.z i) x)

theorem phisB_selfAdj (hT : RestTieComm) (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)
    (hG : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    Formalism.GM.M.fockK (phisB p (r := r) G j jp u) v = Formalism.GM.M.fockK (phisB p (r := r) G j jp v) u := by
  have hfk : ∀ F G : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      Formalism.GM.M.fockK F G = Formalism.GM.M.fock p F G := fun F G => rfl
  unfold phisB
  rw [hfk, hfk]
  refine foldr_selfAdj (fun a b => Formalism.GM.M.fock p a b) (fun a b => by apply Formalism.GM.GammaExpansion.fock_comm) _ _
    (fun i _ a b => by apply Formalism.GM.GammaExpansion.fock_phi_symm) ?_ u v
  refine (List.nodup_finRange G.T.t).pairwise_of_forall_ne fun i _ i' _ hii' x => ?_
  exact hT p N r G hG j jp i i' hii' x

theorem restSymm_of (hT : RestTieComm) (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestSymm C0 CE1 CE2 X := by
  intro dl _ aTop _ x _ u _ v _
  unfold bePhi
  congr 1
  exact phisB_selfAdj hT X.p _ (gB_blockOK C0 CE1 CE2 X aTop 0 x.1) _ _ u v

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section N0

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem cast_sub_ge (w j : ℕ) : (w : ℝ) - j ≤ ((w - j : ℕ) : ℝ) := by
  rcases le_total j w with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (w : ℝ) ≤ j := by exact_mod_cast h
    linarith

theorem lower_bound_initial_multiplicity {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) (i : Fin (X.S C0 CE1 CE2).t) :
    (X.L.a : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) - 5 / 2 * X.L.b' ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  obtain ⟨hK, hdl, hlv⟩ := digits_of_idx hx
  have hK' := hK
  obtain ⟨hDig, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  set P := SegData.P X.p (X.S C0 CE1 CE2) u with hPdef
  have hPpos : 0 < P := twoPow_pos C0 CE1 CE2 X u
  have hj : x.2.1 i ≤ x.1.o u := (((mem_lv _ _ _).mp hlv).1 i).1
  have hA : coarseA X.p (X.S C0 CE1 CE2) x.1 u ≤ (X.S C0 CE1 CE2).bTop u / P :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hjP : x.2.1 i * P ≤ (X.S C0 CE1 CE2).bTop u :=
    (Nat.mul_le_mul_right _ ((hj.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
  have hry : x.1.ry = dl.2 := by rw [← hdl]
  have hne : (Nl C0 CE1 CE2 X dl x.2 i).Nonempty := (Wl_ne ha u).image _
  have hn0 : (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i = sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) := rfl
  have hmem : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ∈ (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) :=
    Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
  rw [Finset.mem_coe] at hmem
  obtain ⟨v, hv, hcm⟩ := Finset.mem_image.mp hmem
  simp only [Wl, Finset.mem_filter, flipOneThree.Inst.winA, Finset.mem_Icc] at hv
  obtain ⟨⟨hav, -⟩, hsv, hdvd⟩ := hv
  rw [← hu] at hsv hdvd
  rw [hn0, ← hcm]
  have hsum : ∑ c : Fin (X.r + 1), dl.2 u c ≤ (X.r + 1) * P := by
    calc ∑ c : Fin (X.r + 1), dl.2 u c ≤ ∑ _c : Fin (X.r + 1), P := by
          apply Finset.sum_le_sum
          intro c _
          rw [← hry]
          exact le_of_lt (hDig.1 u c).2
      _ = (X.r + 1) * P := by simp
  have hQ : (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P * P = v - ∑ c : Fin (X.r + 1), dl.2 u c :=
    Nat.div_mul_cancel hdvd
  have hc1 := cast_sub_ge hS ((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P) (x.2.1 i)
  have hcm' : cm C0 CE1 CE2 X dl x.2 i v = (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P - x.2.1 i := rfl
  rw [hcm']
  have hQr : (((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P : ℕ) : ℝ) * (P : ℝ) =
      (v : ℝ) - (∑ c : Fin (X.r + 1), dl.2 u c : ℕ) := by
    rw [← Nat.cast_sub hsv, ← Nat.cast_mul, hQ]
  have hsumR : ((∑ c : Fin (X.r + 1), dl.2 u c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by
    exact_mod_cast hsum
  have hjPR : ((x.2.1 i : ℕ) : ℝ) * (P : ℝ) ≤ 5 / 2 * X.L.b' := by
    have h1 : (((x.2.1 i * P : ℕ)) : ℝ) ≤ (X.S C0 CE1 CE2).bTop u := by exact_mod_cast hjP
    push_cast at h1
    linarith [hS.bTop u]
  have havR : (X.L.a : ℝ) ≤ v := by exact_mod_cast hav
  have hPR : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem restSI_proved (hFree : RestFree C0 CE1 CE2 X) : RestSI (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) := by
  intro dl hdl a ha x hx i
  have hF := hS.hF
  have hinj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
    intro k k' h
    simp only [uTop, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  set n : Fin (X.S C0 CE1 CE2).t → ℕ := fun k => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) k) with hn
  set a' := ovr (uTop (X.S C0 CE1 CE2)) a n with haeq
  have ha' : a' ∈ cbox C0 CE1 CE2 X dl := by
    have hb := cbox_eq C0 CE1 CE2 X dl a ha
    rw [hb]
    apply ovr_mem _ hinj
    · rw [← hb]
      exact ha
    · exact Fintype.mem_piFinset.mpr (fun k => topA_mem_Wl ha _)
  have hx' : x ∈ idx C0 CE1 CE2 X dl a' := by
    rw [← hFree dl hdl a ha a' ha']
    exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  obtain ⟨-, hdl0, -⟩ := digits_of_idx hx
  have hry : x.1.ry = dl.2 := by rw [← hdl0]
  have hT' := (mem_cbox' ha').1
  have hSb := S_bound hS a' hT' x.1 hK' x.2 i
  have hn0 := lower_bound_initial_multiplicity hS ha hx i
  have htop : (XMof C0 CE1 CE2 X dl a x.1 x.2).top = fun k =>
      (n k - ∑ c : Fin (X.r + 1), x.1.ry (uTop (X.S C0 CE1 CE2) k) c) /
        SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) k) - x.2.1 k := by
    funext k
    have hne : (Nl C0 CE1 CE2 X dl x.2 k).Nonempty := (Wl_ne ha _).image _
    have h1 := cm_top (dl := dl) x.2 k (Wl_ne ha _)
    have h2 : sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) ≤ (Nl C0 CE1 CE2 X dl x.2 k).sup id := by
      have hm := Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
      exact Finset.le_sup (f := id) hm
    rw [hry]
    show sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) +
        1 * ((Nl C0 CE1 CE2 X dl x.2 k).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) + 1 - 1) =
      cm C0 CE1 CE2 X dl x.2 k (n k)
    rw [h1]
    omega
  have hL : (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
      (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X a' x.1 x.2 := by
    rw [htop, haeq, lLL_ovr]
    rfl
  have hP : (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hsm : (2 * (X.s : ℝ) + 2) ≤ X.L.m := by exact_mod_cast hF.s_le
  have hpm := hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have h48 : (4 * (X.s : ℝ) + 8) ≤ X.p := by
    show (4 * (X.s : ℝ) + 8) ≤ X.L.p
    nlinarith
  have hb'p : X.L.b' ≤ (X.L.a : ℝ) / X.p := by
    rw [le_div_iff₀ hp0]
    have := hF.b_lt
    show X.L.b' * X.L.p ≤ X.L.a
    linarith
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hsum : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p) ≤ X.L.a := by
    calc (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p)
        = (4 * (X.s : ℝ) + 8) * ((X.L.a : ℝ) / X.p) := by ring
      _ ≤ (X.p : ℝ) * ((X.L.a : ℝ) / X.p) := mul_le_mul_of_nonneg_right h48 (by positivity)
      _ = X.L.a := by field_simp
  have hreal : ((GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i : ℕ) : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    linarith
  have hnat : GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i := by
    exact_mod_cast le_of_mul_le_mul_right hreal hP
  rw [hL]
  exact hnat

theorem restTMSize_proved (hFree : RestFree C0 CE1 CE2 X) : RestTMSize C0 CE1 CE2 X :=
  restTMSize_of hS hFree (restSI_proved hS hFree)

end N0

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

def OrthBasisLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∃ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) ∧ LinearIndependent ℤ_[p] f ∧
      Submodule.span ℤ_[p] (Set.range f) = L ∧ ∀ a b, a ≠ b → B (f a) (f b) = 0

def OrthCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∀ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) → LinearIndependent ℤ_[p] f →
      Submodule.span ℤ_[p] (Set.range f) = L → (∀ a b, a ≠ b → B (f a) (f b) = 0) →
      ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial σ ℚ_[p]), (∀ a, e a ∈ L) ∧ LinearIndependent ℤ_[p] e ∧
        (∀ a b, a ≠ b → B (e a) (e b) = 0) ∧ (∀ a, B (e a) (e a) ≠ 0 ∧ (B (e a) (e a)).valuation ≤ D) ∧
        n₁ ≤ Module.finrank ℤ_[p] L ∧ Module.finrank ℤ_[p] L ≤ n₁ + Formalism.GM.M.bad p B L D


open Classical in
def GoodLeSmall : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∀ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) → LinearIndependent ℤ_[p] f →
      Submodule.span ℤ_[p] (Set.range f) = L → (∀ a b, a ≠ b → B (f a) (f b) = 0) →
      Formalism.GM.M.goodCount p B L D ≤
        (Finset.univ.filter (fun a : Fin m => B (f a) (f a) ≠ 0 ∧ (B (f a) (f a)).valuation ≤ D)).card

open Classical in
theorem orthCount_of (h : GoodLeSmall) : OrthCount := by
  intro p _ σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth
  have hgood := h p σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth
  have hrank : Module.finrank ℤ_[p] L = m := by
    rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]
  set S := Finset.univ.filter
    (fun a : Fin m => B (f a) (f a) ≠ 0 ∧ (B (f a) (f a)).valuation ≤ D) with hS
  refine ⟨S.card, fun a => f (S.orderEmbOfFin rfl a), fun a => hfL _,
    hli.comp _ (S.orderEmbOfFin rfl).injective, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact horth _ _ (fun h' => hab ((S.orderEmbOfFin rfl).injective h'))
  · intro a
    have hmem := S.orderEmbOfFin_mem rfl a
    exact (Finset.mem_filter.mp hmem).2
  · rw [hrank]
    exact (Finset.card_le_univ S).trans (le_of_eq (Fintype.card_fin m))
  · unfold Formalism.GM.M.bad
    rw [hrank]
    omega

theorem orthLat_of (h1 : OrthBasisLat) (h2 : OrthCount) : OrthLat := by
  intro p _ σ B L W D hp2 hW hLW hfg hsm hadd hsym
  obtain ⟨m, f, hfL, hli, hspan, horth⟩ := h1 p σ B L W hp2 hW hLW hfg hsm hadd hsym
  exact h2 p σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth

end Formalism.MainNotions.G.SymmetricFormBlocks

end

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem orthLat_of' (h1 : OrthBasisLat) (h2 : GoodLeSmall) : OrthLat := orthLat_of h1 (orthCount_of h2)

end Formalism.MainNotions.G.SymmetricFormBlocks
end
