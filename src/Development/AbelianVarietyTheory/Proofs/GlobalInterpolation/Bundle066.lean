module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle062
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace ColSharp

variable {D : D7} {u : D.what₂.Word} (X : Ch D u)

noncomputable def colUp (i : ℕ) : Fn X 0 →ₗ[ℂ] Fn X i :=
  Nat.rec (motive := fun i => Fn X 0 →ₗ[ℂ] Fn X i) LinearMap.id (fun i g => KT X i ∘ₗ g) i

theorem colUp_eq (i : ℕ) (φ : Fn X 0) : colUp X i φ = Formalism.ThetaLiftIndependence.chainOpM X.C.wt X.C.Kmap i φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show KT X i (colUp X i φ) = _
    rw [ih]; rfl

theorem colT_eq (φ : Fn X 0) : colT X φ = colUp X D.R.m φ := (colUp_eq X _ φ).symm

theorem emb_mem (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by

  rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {X}

theorem fold_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) (l : List X.A.vT) {φ : Fn X i}
    (hφ : φ ∈ X.fm.Fi i) :
    (l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id : Fn X i →ₗ[ℂ] Fn X i) φ ∈ X.fm.Fi i := by
  induction l with
  | nil => exact hφ
  | cons v l ih => exact hF.1 i hi v _ ih

theorem Uprod_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) (w : D.what₂.places.Pl) {φ : Fn X i}
    (hφ : φ ∈ X.fm.Fi i) : Uprod X i w φ ∈ X.fm.Fi i := fold_mem hF hi _ hφ

theorem Upow_mem (hF : FormsStable X) (w : D.what₂.places.Pl) (n : ℕ) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : (Uprod X 0 w ^ n) φ ∈ X.fm.Fi 0 := by
  induction n with
  | zero => exact hφ
  | succ n ih => rw [pow_succ']; exact Uprod_mem hF (Nat.zero_le _) w ih

theorem colUp_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : colUp X i φ ∈ X.fm.Fi i := by
  induction i with
  | zero => exact hφ
  | succ i ih => exact hF.2.2 i hi _ (ih (Nat.le_of_succ_le hi))

theorem scalar_eq {s : ℕ} (hs : D.R.t + 1 = 2 * s) :
    ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ s := by
  have h : ((D.R.t : ℝ) + 1) / 2 = (s : ℝ) := by
    have : ((D.R.t + 1 : ℕ) : ℝ) = ((2 * s : ℕ) : ℝ) := by rw [hs]
    push_cast at this; linarith
  rw [h, Real.rpow_natCast]; push_cast; rfl

theorem fold_comm (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i < D.R.m) (l : List X.A.vT) {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i) :
    (l.foldr (fun v g => (Uop X (i + 1) v).comp g) LinearMap.id : Fn X (i + 1) →ₗ[ℂ] Fn X (i + 1)) (KT X i φ) =
      (X.A.T : ℂ) ^ (s * l.length) •
        KT X i ((l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id : Fn X i →ₗ[ℂ] Fn X i) φ) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.foldr_cons, List.foldr_cons, LinearMap.comp_apply, LinearMap.comp_apply, ih, map_smul,
      h4 i hi v _ (fold_mem hF hi.le l hφ), scalar_eq hs, smul_smul, ← pow_add, List.length_cons, Nat.mul_succ]

theorem Uprod_comm (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i < D.R.m) (w : D.what₂.places.Pl) {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i) :
    Uprod X (i + 1) w (KT X i φ) = (X.A.T : ℂ) ^ (s * (VVT X w).card) • KT X i (Uprod X i w φ) := by
  rw [← Finset.length_toList]; exact fold_comm hF h4 hs hi _ hφ

theorem Uprod_colUp (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i ≤ D.R.m) (w : D.what₂.places.Pl) {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) :
    Uprod X i w (colUp X i φ) = (X.A.T : ℂ) ^ (s * (VVT X w).card * i) • colUp X i (Uprod X 0 w φ) := by
  induction i with
  | zero => simp [colUp]
  | succ i ih =>
    have hi' : i < D.R.m := hi
    show Uprod X (i + 1) w (KT X i (colUp X i φ)) = _ • KT X i (colUp X i (Uprod X 0 w φ))
    rw [Uprod_comm hF h4 hs hi' w (colUp_mem hF hi'.le hφ), ih hi'.le, map_smul, smul_smul, ← pow_add,
      Nat.mul_succ, Nat.add_comm (s * _)]

theorem chain_into (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s)
    (w : D.what₂.places.Pl) (e : ℕ)
    (hU : ∀ i, i < D.R.m → Into X w (fun φ => tpow X e • Uprod X (i + 1) w (KT X i φ))
      (X.fm.S i w) (X.fm.S (i + 1) w)) {i : ℕ} (hi : i ≤ D.R.m) :
    Into X w (fun φ => (X.A.T : ℂ) ^ (i * e + s * (VVT X w).card * ∑ j ∈ Finset.range (i + 1), j) •
      colUp X i ((Uprod X 0 w ^ i) φ)) (X.fm.S 0 w) (X.fm.S i w) := by
  induction i with
  | zero => intro x hx; exact ⟨x, hx, by simp [colUp]⟩
  | succ i ih =>
    have hi' : i < D.R.m := hi
    intro x hx
    obtain ⟨y, hy, hy'⟩ := ih hi'.le x hx
    obtain ⟨z, hz, hz'⟩ := hU i hi' y hy
    refine ⟨z, hz, ?_⟩
    have hm := Upow_mem hF w i (emb_mem X 0 x)
    have key := Uprod_colUp hF h4 hs hi w hm
    have e1 : colUp X (i + 1) ((Uprod X 0 w ^ i) (X.fm.emb 0 x)) =
      KT X i (colUp X i ((Uprod X 0 w ^ i) (X.fm.emb 0 x))) := rfl
    rw [hz']
    beta_reduce at hy' ⊢
    rw [hy', map_smul, map_smul, ← e1, key, pow_succ' (Uprod X 0 w) i, Module.End.mul_apply, tpow,
      smul_smul, smul_smul, ← pow_add, ← pow_add, Finset.sum_range_succ _ (i + 1)]
    congr 2
    ring

theorem card_VVT {w : D.what₂.places.Pl} (h : X.fm.seenP w = true) : (VVT X w).card = (tops D).card := by
  unfold VVT
  rw [if_pos h]
  refine Finset.card_bij (fun v _ => X.fm.tauOf w v) (fun v hv => (Finset.mem_filter.1 hv).2)
    (fun a _ b _ hab => (X.fm.tauOf w).injective hab) (fun τ hτ => ?_)
  exact ⟨(X.fm.tauOf w).symm τ, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hτ⟩, by simp⟩

theorem expT_nonneg (hW : WtBounds X) (w : D.what₂.places.Pl) : 0 ≤ expT X w := by
  refine mul_nonneg (Int.natCast_nonneg _) (Finset.sum_nonneg fun v hv => hW.1 _ ?_)
  unfold VVT at hv
  split_ifs at hv
  · exact (Finset.mem_filter.1 hv).2
  · simp at hv

theorem val_pow {w : D.what₂.places.Pl} (hw : OverT X w) (k : ℕ) :
    D.what₂.places.val w ((X.A.T : D.what₂.LL) ^ k) = (((D.what₂.places.ramIdx w * k : ℕ) : ℤ) : WithTop ℤ) := by
  have h := D.what₂.places.val_resChar w
  rw [show D.what₂.places.resChar w = X.A.T from hw] at h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AddValuation.map_mul, ih, h, ← WithTop.coe_add]
    congr 1

theorem quot_mem {w : D.what₂.places.Pl} (hw : OverT X w) {c : D.what₂.LL} {n : ℤ}
    (hc : D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ)) (a b : ℕ)
    (h : ((D.what₂.places.ramIdx w * b : ℕ) : ℤ) ≤ n) :
    c * (X.A.T : D.what₂.LL) ^ a * ((X.A.T : D.what₂.LL) ^ b)⁻¹ ∈ Ow D w := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv, hc, val_pow hw, val_pow hw]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
  have : (0 : ℤ) ≤ ((D.what₂.places.ramIdx w * a : ℕ) : ℤ) := Int.natCast_nonneg _
  exact_mod_cast (by omega : (0 : ℤ) ≤ n + ((D.what₂.places.ramIdx w * a : ℕ) : ℤ) + -((D.what₂.places.ramIdx w * b : ℕ) : ℤ))

theorem loss_eq {s : ℕ} (hs : D.R.t + 1 = 2 * s) (w : D.what₂.places.Pl) :
    ((D.R.m * (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) +
      s * (VVT X w).card * ∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) : ℝ) = (D.R.m : ℝ) * ET X w := by
  unfold ET
  by_cases h : X.fm.seenP w = true
  · rw [if_pos h, if_pos h, card_VVT h]
    unfold ETpi
    have h1 : ((D.R.t : ℝ) + 1) = 2 * s := by exact_mod_cast hs
    have h2 : ((∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) : ℝ) * 2 = ((D.R.m : ℝ) + 1) * D.R.m := by
      have := Finset.sum_range_id_mul_two (D.R.m + 1)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    rw [h1]
    generalize (∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) = S at h2 ⊢
    push_cast
    linear_combination ((s : ℝ) * ((tops D).card : ℝ) / 2) * h2
  · have : VVT X w = ∅ := by unfold VVT; rw [if_neg h]
    rw [if_neg h, if_neg h, this]
    simp

end ColSharp


open ColSharp in
theorem levelChainSharpColumnValuation_of_stability : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u),
    FormsStable X → LevelChainUOperatorCommutation X → UKSharp X → WtBounds X → Conclusion5Sharp X := by
  intro D u X hF h4 hU hW w hw c n hc hn x' hx'
  obtain ⟨x, hx, hxx⟩ := hx'
  obtain ⟨s0, hs0⟩ := D.R.t_odd
  have hs : D.R.t + 1 = 2 * (s0 + 1) := by omega
  obtain ⟨y, hy, hy'⟩ := chain_into hF h4 hs w _ (hU w hw) (le_refl D.R.m) x hx.1
  rw [← loss_eq (X := X) hs w] at hn
  set b := D.R.m * (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) +
      (s0 + 1) * (VVT X w).card * ∑ j ∈ Finset.range (D.R.m + 1), j with hb
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (expT_nonneg hW w)
  have hmem := quot_mem hw hc a b (by exact_mod_cast hn)
  refine ⟨(⟨_, hmem⟩ : Ow D w) • y, (X.fm.S D.R.m w).smul_mem _ hy, ?_⟩
  have hT : (X.A.T : ℂ) ^ b ≠ 0 := pow_ne_zero _ (by exact_mod_cast X.A.T_prime.ne_zero)
  beta_reduce at hy' ⊢
  rw [Subring.smul_def, LinearMap.map_smulₛₗ, hy', hxx, colT_eq, ha, LinearMap.smul_apply, map_smul,
    smul_smul, smul_smul, zpow_natCast]
  congr 1
  simp only [map_mul, map_inv₀, map_pow, map_natCast]
  field_simp

end GlobalTheory.LvT
end
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwSharp

variable {D : D7} {u : D.what₂.Word}

theorem weight_eq (X Y : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j)) :
    (X.fm.lam j τ).w a = (Y.fm.lam j τ).w a := by
  have h := (X.fm.lam_eq j hj τ a).trans (Y.fm.lam_eq j hj τ a).symm
  exact_mod_cast h

theorem weightSup_eq (X Y : Ch D u) (τ : D.what₂.Tau) : TauWeight X τ = TauWeight Y τ := by
  unfold TauWeight
  refine Finset.sup_congr rfl fun i hi => Finset.sup_congr rfl fun a _ => ?_
  rw [weight_eq X Y i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) τ a]

theorem exponent_eq (X Y : Ch D u) : ETpi X = ETpi Y := by
  unfold ETpi Wt; simp only [weightSup_eq X Y]

theorem tupleChainSharpColumnValuation_of_twisted : ∀ (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup),
    Step0Tie Tw u μ → Conclusion5Sharp (tw Tw u μ) → TupleChainSharpColumnValuation Tw u μ := by
  intro D u Tw μ hT h w hw c n hc hn x hx
  have hw' : OverT (tw Tw u μ) w := hw.trans (Tw.A_T u μ).symm
  have hown : ET (own D u) w = EatT D u w := rfl
  have hE : ET (tw Tw u μ) w = EatT D u w := by
    rw [← hown]; unfold ET
    rw [exponent_eq (tw Tw u μ) (own D u)]
    show (if (Tw.fm u μ).seenP w = true then _ else _) = _
    rw [(hT w hw).1]
  obtain ⟨y, hy, e⟩ := h w hw' c n hc (hE ▸ hn) (Tw.e0 u μ x) ((hT w hw).2 x hx)
  refine ⟨y, hy, e.trans ?_⟩
  show _ • (D.chTw u μ).col ((Tw.fm u μ).emb 0 (Tw.e0 u μ x)) = _
  rw [Tw.embed_mul_block_embedding]

end GlobalTheory.LvT.TwSharp
end
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem PtModel.mem_Fi_iff_exists_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i)
    (φ : Fn X i), φ ∈ X.fm.Fi i ↔ ∃ Φ, M.IsExt φ Φ := by
  intro D u X i M φ
  rw [M.mem_Fi]
  constructor
  · intro h
    choose y hy hfix using h
    choose cl gp hp using M.rep_surj
    have key : ∀ (c c' : X.C.cls i) (g g' : M.G), g • M.rep c = g' • M.rep c' →
        M.act g (y c) = M.act g' (y c') := by
      intro c c' g g' hgg
      have h1 : (g'⁻¹ * g) • M.rep c = M.rep c' := by
        rw [mul_smul, hgg, inv_smul_smul]
      have hc := M.rep_inj c c' _ h1
      subst hc
      have h2 := hfix c _ h1
      have h3 : g = g' * (g'⁻¹ * g) := by group
      conv_lhs => rw [h3, map_mul, Module.End.mul_apply, h2]
    refine ⟨fun p => M.act (gp p) (y (cl p)), fun c => ?_, fun g p => ?_⟩
    · have := key (cl (M.rep c)) c (gp (M.rep c)) 1 (by rw [hp, one_smul])
      rw [hy c]
      simp only [this, map_one, Module.End.one_apply]
    · have := key (cl (g • p)) (cl p) (gp (g • p)) (g * gp p) (by rw [hp, mul_smul, hp])
      simp only [this, map_mul, Module.End.mul_apply]
  · rintro ⟨Φ, h1, h2⟩ c
    refine ⟨Φ (M.rep c), h1 c, fun g hg => ?_⟩
    rw [← h2, hg]

end GlobalTheory.LvT
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

variable {D : D7} {u : D.what₂.Word}

theorem natAbs_lamT_le_Wt (X : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j))
    (ha : ¬ (a.1 = 0 ∧ τ ∈ tops D)) : ((PtModel.lamT X j τ).w a).natAbs ≤ Wt X τ := by
  unfold Wt TauWeight
  refine le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  refine le_trans ?_ (Finset.le_sup (f := fun a : Fin (D.R.N j) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam j τ).w a - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_univ a))
  rw [if_neg ha]
  exact le_rfl

theorem lamT_last (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N (i + 1)))
    (ha : a.1 = D.R.N (i + 1) - 1) : (PtModel.lamT X (i + 1) τ).w a = -X.C.sDiv i τ := by
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  have hm : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + D.R.t + 1 := by ring
  have ha' : a.1 = D.R.k + (D.R.t + i * (D.R.t + 1)) := by omega
  have hk : ¬ a.1 < D.R.k := by omega
  have hq : (a.1 - D.R.k) / (D.R.t + 1) = i := by
    rw [ha', Nat.add_sub_cancel_left, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h1 := X.fm.lam_eq (i + 1) hi τ a
  rw [dite_eq_right hk] at h1
  simp only [hq] at h1
  have h2 := X.C.sDiv_eq i hi τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h3 : (i + 1) * (D.R.t + 1) / 2 = (i + 1) * (c + 1) := by
    have : (i + 1) * (D.R.t + 1) = 2 * ((i + 1) * (c + 1)) := by rw [hc]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcq : (D.R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  change (X.fm.lam (i + 1) τ).w a - (((i + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) = _
  rw [h3]
  have : (((X.fm.lam (i + 1) τ).w a - (((i + 1) * (c + 1) : ℕ) : ℤ) : ℤ) : ℚ) = ((-X.C.sDiv i τ : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  exact_mod_cast this

theorem wtBounds_of_nonneg : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u), (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) →
    (∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ) → WtBounds X := by
  intro D u X hb hs
  refine ⟨hb, fun i hi τ => ?_⟩
  have hpos := D.R.N_pos (i + 1)
  have hlast := lamT_last X i hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ rfl
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  refine ⟨hs i hi τ, ?_, ?_, fun hτ => ?_⟩
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ (fun h => by
      have := h.1
      simp only at this
      omega)
    rw [hlast] at h
    omega
  · unfold DomWeight.detShift
    rw [dite_eq_left hpos]
    exact hlast
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨0, hpos⟩ (fun h => hτ h.2)
    omega

end GlobalTheory.LvT
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.BranchBasis

theorem mem_sumLat {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 K) (Fin n → K)) (t : K)
    (x : Fin N → K) :
    x ∈ Br.sumLat hN M t ↔ (fun a => x (Br.iC hN a)) ∈ M ∧ ∃ c : 𝓞 K, x (Br.iL hN) = (c : K) * t := Iff.rfl

theorem mem_colLat {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∃ c : Fin n → 𝓞 K, ∀ a, ∑ j, (c j : K) * (B : Matrix (Fin n) (Fin n) K) a j = x a := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]

theorem colLat_block {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (t : K) (B : GL (Fin n) K)
    (B' : GL (Fin N) K) (h : IsBlock hN (B' : Matrix (Fin N) (Fin N) K) (B : Matrix (Fin n) (Fin n) K) t) :
    colLat B' = Br.sumLat hN (colLat B) t := by
  obtain ⟨h1, h2, h3⟩ := h
  ext x
  rw [mem_sumLat, mem_colLat, mem_colLat]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨fun j => c (Br.iC hN j), fun a => ?_⟩, c (Br.iL hN), ?_⟩
    · rw [← hc, sum_split hN]
      simp only [h1, (h2 _).1, mul_zero, add_zero]
    · rw [← hc, sum_split hN]
      simp only [h3, (h2 _).2, mul_zero, Finset.sum_const_zero, zero_add]
  · rintro ⟨⟨c, hc⟩, d, hd⟩
    refine ⟨fun j => if hj : j.val < n then c ⟨j.val, hj⟩ else d, fun a => ?_⟩
    rw [sum_split hN]
    have e1 : ∀ j : Fin n, (if hj : (Br.iC hN j).val < n then c ⟨(Br.iC hN j).val, hj⟩ else d) = c j :=
      fun j => dif_pos j.2
    have e2 : (if hj : (Br.iL hN).val < n then c ⟨(Br.iL hN).val, hj⟩ else d) = d := dif_neg (lt_irrefl n)
    simp only [e1, e2]
    rcases cases_idx hN a with rfl | ⟨a, rfl⟩
    · simp only [h3, (h2 _).2, mul_zero, Finset.sum_const_zero, zero_add, hd]
    · simp only [h1, (h2 _).1, mul_zero, add_zero]
      exact hc a

theorem localization_sumLat_le {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (w : HeightOneSpectrum (𝓞 K))
    (M M₂ : Submodule (𝓞 K) (Fin n → K)) (t : K) (h : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M₂) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Br.sumLat hN M t) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Br.sumLat hN M₂ t) := by
  rintro x ⟨s, hs, hx1, c, hc⟩
  have h0 : (fun a => (s • x) (Br.iC hN a)) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M :=
    ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hx1⟩
  obtain ⟨u, hu, hux⟩ := h h0
  refine ⟨u * s, Submonoid.mul_mem _ hu hs, ?_⟩
  rw [mul_smul, mem_sumLat]
  refine ⟨hux, u * c, ?_⟩
  rw [Pi.smul_apply, hc, Algebra.smul_def]
  push_cast
  exact (mul_assoc _ _ _).symm

theorem isBasisAt_block : ∀ (K : Type) [Field K] [NumberField K] (N n : ℕ) (hN : N = n + 1) (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (t : K) (B : GL (Fin n) K) (B' : GL (Fin N) K), IsBlock hN (B' : Matrix (Fin N) (Fin N) K) (B : Matrix (Fin n) (Fin n) K) t → IsBasisAt w M B → IsBasisAt w (Br.sumLat hN M t) B' := by
  intro K _ _ N n hN w M t B B' hB h
  unfold IsBasisAt at h ⊢
  rw [colLat_block hN t B B' hB]
  exact le_antisymm (localization_sumLat_le hN w _ _ t h.le) (localization_sumLat_le hN w _ _ t h.ge)

end GlobalTheory.BranchBasis
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_hermitianSpace_with_signature : ∀ (D : D7) (P Q : ℕ), ∃ U : HSpace D.host.E, U.SigOK ∧ ∀ τ, U.sig τ = (P, Q) := by
  first | exact @GlobalTheory.exists_hSpace_sigOK_sig | exact GlobalTheory.exists_hSpace_sigOK_sig | (intros; apply GlobalTheory.exists_hSpace_sigOK_sig <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_generators_mem_completedLattice_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) (u : Fin k → E ⊗[F] R), u ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ ↔ ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j := by
  first | exact @GlobalTheory.OverCompare.exists_generators_mem_latS_iff | exact GlobalTheory.OverCompare.exists_generators_mem_latS_iff | (intros; apply GlobalTheory.OverCompare.exists_generators_mem_latS_iff <;> assumption)
end
