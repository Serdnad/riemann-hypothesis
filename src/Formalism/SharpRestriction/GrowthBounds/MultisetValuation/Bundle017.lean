module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle015
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ExpansionAllPlacesOfPlace
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle016
public import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle011
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle005
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle012
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DworkExponentialRestrictions
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem en_PhAt_const (hbe : BeProp p Y.be) (j : ℕ) (v : X.Pl) : MvPowerSeries.constantCoeff (Y.PhAt j v) = 0 := by
  unfold Pend.PhAt

  rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ (th_be_const hbe)

theorem kernel_product_form (D : Formalism.BasicNotions.D7) : KernelProductForm X Y D := by
  intro hA j hj La La' h1 h2 φ
  obtain ⟨Ph, U0, hTh, hU0, _, hbe, hPh⟩ := hA.2.2.1 j hj La La' h1 h2 φ
  have hcz := charZero_K' p (K0 p)
  have hΨ : (∑ e : X.EA j, sub2 p Y.be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) :
      MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) = ∑ v, Y.PhAt j v := by
    unfold Pend.PhAt
    exact Fintype.sum_sigma _
  rw [hΨ] at hPh
  obtain ⟨hc0, h, hh0, hE⟩ := hPh
  have hE0 : E0 p (inParam p (Ph - ∑ v, Y.PhAt j v)) := ⟨th_inParam_const p hc0, h, hh0, hE⟩
  obtain ⟨w, hw⟩ := exp_neg_integral p hE0
  refine ⟨MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-(Ph - ∑ v, Y.PhAt j v))) * U0, ?_, ?_⟩
  · rw [en_inParamK_mul]
    refine en_IntR_mul ?_ hU0
    have e1 : inParam p (expS p (-(Ph - ∑ v, Y.PhAt j v))) = expK (inParam p (-(Ph - ∑ v, Y.PhAt j v))) := by
      unfold inParam
      exact th_subst_expK _ (fun i => by
        have := th_lX_const p (K0 p) i
        rwa [Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hc0, neg_zero])
    rw [th_inParamK_map p (K0 p) Y.Kc, ← th_inParam_eq, e1, th_inParam_neg, hw]
    intro n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    exact Y.witt_mem_integers_Cp _
  · have e2 : -Ph = ∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v) := by
      rw [Finset.sum_neg_distrib]; ring
    have e3 : expS p (-Ph) = (∏ v, expS p (-Y.PhAt j v)) * expS p (-(Ph - ∑ v, Y.PhAt j v)) := by
      have a1 : expK (∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v)) =
          expK (∑ v, (-Y.PhAt j v)) * expK (-(Ph - ∑ v, Y.PhAt j v)) :=
        expK_add (by

          rw [map_sum]
          exact Finset.sum_eq_zero fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero])
          (by rw [map_neg, hc0, neg_zero])
      have a2 : expK (∑ v, (-Y.PhAt j v)) = ∏ v, expK (-Y.PhAt j v) :=
        th_expK_sum _ _ fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero]
      rw [e2]
      exact a1.trans (by rw [a2]; rfl)
    rw [hTh, e3, map_mul, map_prod, mul_assoc]
    rfl

theorem restPlaces (D : Formalism.BasicNotions.D7) : RestPlaces X Y D := restPlaces_of D (kernel_product_form X Y D)

theorem restEnt_of (D : Formalism.BasicNotions.D7) (h2 : PlacewiseLowerBoundEvenShift X Y D) (hB : RestBU X Y D) (hA : admitted D X Y) : EntCondition X Y :=
  restEnt_of_rest D (restPlaces X Y D) h2 hB hA

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem ne_lamI_last (s : Fin (G.P.n' v)) : lamI (G.P.lam0 v) s (G.P.m + 1) = G.P.lam0 v s (Fin.last G.P.m) := by
  unfold lamI
  rw [dite_eq_left ⟨by omega, le_rfl⟩]
  rfl

theorem ne_lamI_le (s : Fin (G.P.n' v)) (a : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    lamI (G.P.lam0 v) s a ≤ (Fl.c : ℤ) + (if s ∈ Fl.TT v ∧ a = 1 then Fl.a v s else 0) := by
  have hc : (0 : ℤ) ≤ Fl.c := Int.natCast_nonneg _
  unfold lamI
  by_cases h : 1 ≤ a ∧ a ≤ G.P.m + 1
  · rw [dite_eq_left h]
    by_cases hs : s ∈ Fl.TT v
    · obtain ⟨h1, h2, h3⟩ := (Fl.base v s).1 hs
      by_cases ha : a = 1
      · subst ha
        rw [if_pos ⟨hs, rfl⟩]
        have : G.P.lam0 v s ⟨1 - 1, by omega⟩ = Fl.a v s := h1
        omega
      · rw [if_neg (fun h' => ha h'.2)]
        by_cases hl : a = G.P.m + 1
        · subst hl
          have : G.P.lam0 v s ⟨G.P.m + 1 - 1, by omega⟩ = -Fl.b v s := h2
          have := hb hs
          omega
        · have := (abs_le.1 (h3 ⟨a - 1, by omega⟩ (by show 0 < a - 1; omega) (by show a - 1 < G.P.m; omega))).2
          omega
    · rw [if_neg (fun h' => hs h'.1)]
      have := (abs_le.1 ((Fl.base v s).2 hs ⟨a - 1, by omega⟩)).2
      omega
  · rw [dite_eq_right h, if_neg (fun h' => h ⟨by omega, by omega⟩)]
    omega

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem ne_kaJ_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ Formalism.MainNotions.G.kaJ D j := by
  unfold Formalism.MainNotions.G.kaJ
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have : 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
  linarith

theorem ne_w''_nonneg : 0 ≤ L.sc.w'' D.R.n := by
  unfold Scale.w''
  exact div_nonneg L.sc.b'_pos.le (mul_nonneg L.sc.x_pos.le (Nat.cast_nonneg _))

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))


include hL ht0 in
theorem ne_w_non (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∉ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ L.sc.w'' D.R.n + L.etaSz := by
  obtain ⟨_, h2, _, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∉ D.host.TT := fun h => hs (h2.2 h)
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_neg (fun h => hn h.2)]
  have h5 := (X.off_thin j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))
    ⟨fun h => hn h.2, fun h => by simpa using h.1⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith


include hL ht0 in
theorem ne_w_top (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) + L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨_, h2, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj, (h3 hs).2]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∈ D.host.TT := h2.1 hs
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_pos ⟨rfl, hn⟩]
  have h5 := (X.off_top j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) ⟨rfl, hn⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith

include hL ht0 in
theorem ne_nP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
  unfold Formalism.MainNotions.G.nP
  rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]

theorem ne_Nm (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 ≤ Formalism.MainNotions.G.Nm D := by
  unfold Formalism.MainNotions.G.Nm Ranks.N
  have h1 : (j : ℝ) ≤ D.R.m := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have h2 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1),
    mul_nonneg h4 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1)]

end Orbit


open Classical in
theorem price_bound_large_primes : PriceBoundLargePrimes 1 := by
  intro D L X Y K hK _ hT hL u w hg hp t0 ht0 j hj
  have hr : (D.gat u w hg).P.r = 1 := by rw [(hL u w hg).2.2.2.1, if_neg (not_lt.2 hp)]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hA : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L := by
    have := ne_w''_nonneg (L := L)
    have := L.etaSz_pos
    have := nc_cG_nonneg (L := L)
    linarith
  rw [hr]
  have h1 := price_sum_single_edge (Y.Fl u w hg).t j ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L)
    (fun s => ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) hA
    (fun s _ => by
      have e : (D.gat u w hg).P.m + 2 - 1 = (D.gat u w hg).P.m + 1 := rfl
      rw [e, Finset.Icc_self, Finset.sum_singleton, ne_lamI_last]
      split_ifs with hs
      · rw [((Y.Fl u w hg).base (Y.vOf u w hg t0) s).1 hs |>.2.1]
        push_cast
        linarith
      · have h2 := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h3 := (abs_le.1 (((Y.Fl u w hg).base (Y.vOf u w hg t0) s).2 hs (Fin.last _))).2
        have h4 : (((D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s (Fin.last _) : ℤ) : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) := by
          exact_mod_cast h3
        push_cast
        linarith)
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr
  rw [if_pos hp, nc_topsOn X Y hT hL u w hg t0 ht0, Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf, ne_nP X Y hT hL u w hg t0 ht0, ht]
  have e1 : ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
      (((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) =
      ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
        (Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, nc_iota Y u w hg t0 s) -
          (Formalism.MainNotions.G.bL L (nc_iota Y u w hg t0 s) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨_, _, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
    rw [h4 j hj, (h3 (Finset.mem_filter.1 hs).1).2]
  rw [e1]
  have hN := ne_Nm (D := D) j hj
  have hn : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := Nat.cast_nonneg _
  have hNm : 0 ≤ Formalism.MainNotions.G.Nm D := le_trans (by positivity) hN
  have h5 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) ≤
      K.Pr1 * ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) *
        (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) := by
    have := mul_le_mul_of_nonneg_right hK
      (mul_nonneg hn (by linarith : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D))
    linarith
  have h6 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * ((1 : ℕ) : ℝ) * j * ((D.R.t : ℝ) + 1) / 2 ≤
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * Formalism.MainNotions.G.Nm D := by
    have := mul_le_mul_of_nonneg_left hN hn
    push_cast
    linarith
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {σ κ τ τ' K : Type} [Field K]

def eb_w (F : MvPowerSeries σ K) (n : σ →₀ ℕ) : K :=
  (∏ x ∈ n.support, ((n x).factorial : K)) * MvPowerSeries.coeff n F

def eb_J (F : MvPowerSeries σ K) (Q : MvPolynomial σ (MvPolynomial τ K)) : MvPolynomial τ K :=
  ∑ n ∈ Q.support, eb_w F n • AddMonoidAlgebra.coeff Q n

theorem eb_J_subset (F : MvPowerSeries σ K) (Q : MvPolynomial σ (MvPolynomial τ K)) (S : Finset (σ →₀ ℕ))
    (h : Q.support ⊆ S) : eb_J F Q = ∑ n ∈ S, eb_w F n • AddMonoidAlgebra.coeff Q n := by
  unfold eb_J
  apply Finset.sum_subset h
  intro n _ hn
  rw [MvPolynomial.notMem_support_iff.1 hn, smul_zero]

theorem eb_applyD (P : MvPolynomial σ (MvPolynomial τ ℤ)) (F : MvPowerSeries σ K) :
    applyD P F = eb_J F (MvPolynomial.map (MvPolynomial.map (Int.castRingHom K)) P) := by
  rw [eb_J_subset F _ P.support (MvPolynomial.support_map_subset _ _)]
  unfold applyD eb_w
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_map]

theorem eb_w_mapDomain (ε : κ → σ) (hε : Function.Injective ε) (F : MvPowerSeries σ K) (n : κ →₀ ℕ) :
    eb_w F (n.mapDomain ε) = eb_w (resV ε F) n := by
  classical
  unfold eb_w
  rw [Finsupp.mapDomain_support_of_injective hε, Finset.prod_image (fun a _ b _ h => hε h)]
  congr 1
  apply Finset.prod_congr rfl
  intro y _
  rw [Finsupp.mapDomain_apply_of_injective hε]

theorem eb_J_rename (ε : κ → σ) (hε : Function.Injective ε) (F : MvPowerSeries σ K)
    (Q : MvPolynomial κ (MvPolynomial τ K)) : eb_J F (MvPolynomial.rename ε Q) = eb_J (resV ε F) Q := by
  classical
  unfold eb_J
  rw [MvPolynomial.support_rename_of_injective hε,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hε h)]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_rename_mapDomain ε hε, eb_w_mapDomain ε hε]

theorem eb_J_map (φ : τ' → τ) (G : MvPowerSeries κ K) (Pc : MvPolynomial κ (MvPolynomial τ' K)) :
    eb_J G (MvPolynomial.map (MvPolynomial.rename φ : MvPolynomial τ' K →ₐ[K] MvPolynomial τ K).toRingHom Pc) =
      MvPolynomial.rename φ (Formalism.DworkPowerSeriesWeights.jetPairPoly Pc G) := by
  rw [eb_J_subset G _ Pc.support (MvPolynomial.support_map_subset _ _)]
  unfold Formalism.DworkPowerSeriesWeights.jetPairPoly

  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.rename_C, MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 2
  unfold eb_w Formalism.DworkPowerSeriesWeights.mfact Finsupp.prod
  rw [Nat.cast_prod]

end Gen

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

def eb_phi (v : X.Pl) (j : ℕ) : ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j) → X.FrI j :=
  fun y => ⟨v, ((ea_e X v).symm y.1, y.2.1.val, y.2.2)⟩

theorem eb_phi_inj (v : X.Pl) (j : ℕ) : Function.Injective (eb_phi X v j) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [eb_phi, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, Fin.ext h2, h3]

theorem eb_eps_inj (v : X.Pl) (j : ℕ) : Function.Injective (ea_eps X v j) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [ea_eps, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, h2, h3]

theorem eb_fac (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) (s : ea_S X v) (c : Fin (ea_colN X v j s)) :
    MvPolynomial.rename (ea_eps X v j) (MvPolynomial.map
      (MvPolynomial.rename (eb_phi X v j) : MvPolynomial _ K' →ₐ[K'] MvPolynomial _ K').toRingHom
      (Matrix.of fun (r r' : Fin (ea_hts X v j s c)) =>
        (∑ a : Fin (NN X.G.P.m X.t j), MvPolynomial.C (MvPolynomial.X
            (s, (⟨r.val, lt_of_lt_of_le r.isLt (ea_hp X v j s c)⟩ : Fin (NN X.G.P.m X.t j)), a)) *
          MvPolynomial.X (s, a, ea_Ic X v j I s c r') :
        MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K'))).det) =
    MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (X.colFac j I v ((ea_e X v).symm s) c.val) := by
  unfold Sys.colFac
  rw [RingHom.map_det, AlgHom.map_det, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun r r' => ?_)
  change _ = MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (∑ a : Fin (NN X.G.P.m X.t j),
    MvPolynomial.C (MvPolynomial.X (⟨v, ((ea_e X v).symm s, r.val, a)⟩ : X.FrI j)) *
      MvPolynomial.X (⟨v, ((ea_e X v).symm s, a, I v ((ea_e X v).symm s) c.val r'.val)⟩ : X.ZA j))

  simp only [RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
  MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.rename_C, MvPolynomial.rename_X, AlgHom.toRingHom_eq_coe,
  RingHom.coe_coe]
  rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_restNorm (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : ea_RestNorm Y := by
  obtain ⟨K', nf, ac, um, -, hpn, hball, vp, hvp⟩ := nm_ext Y h
  letI : Algebra (K0 p) K' := ((algebraMap Y.Kc K').comp (algebraMap (K0 p) Y.Kc)).toAlgebra
  haveI : IsScalarTower (K0 p) Y.Kc K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨ea_NormExt.mk K' vp hvp hpn hball⟩

theorem nm_restNorm_of_place (Y : Pend X) (v : X.Pl) : ea_RestNorm Y := nm_restNorm Y (nm_pinv_of_place Y v)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
