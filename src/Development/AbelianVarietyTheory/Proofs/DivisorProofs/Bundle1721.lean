module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem frame_cc_ev {C : Type} [CommRing C] {d m n : ℕ} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS C m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => a p.1 p.2)
    (hasSubst_of_constantCoeff_zero h0) h0 hf

theorem frame_subst_ev {C : Type} [CommRing C] {d m n : ℕ} {σ : Type} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t)
    (f : PS C m d) :
    subst t (ev a f) = subst (fun p : Fin m × Fin d => subst t (a p.1 p.2)) f := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact subst_comp_subst_apply (a := fun p : Fin m × Fin d => a p.1 p.2) (hasSubst_of_constantCoeff_zero h0) ht f

theorem frame_cc_pt {C : Type} [CommRing C] {d n : ℕ} (b : Fin n) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![pt C d b] : Fin 1 → Pt C n d) j i) = 0 := by
  simp [pt]

theorem frame_subst_ev_pt {C : Type} [CommRing C] {d n : ℕ} {σ : Type} (b : Fin n)
    {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t) (f : PS C 1 d) :
    subst t (ev ![pt C d b] f) = subst (fun p : Fin 1 × Fin d => t (b, p.2)) f := by
  rw [frame_subst_ev _ (frame_cc_pt b) ht]
  congr 1
  funext p
  rcases p with ⟨j, i⟩
  fin_cases j
  simpa [pt] using (subst_X (R := C) ht (b, i))

theorem frame_exp_zero {C : Type} [CommRing C] [Algebra ℚ C] {σ : Type} :
    PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  classical
  unfold PowerSeries.subst
  have e : (fun _ : Unit => (0 : MvPowerSeries σ C)) = 0 := rfl
  rw [e, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  ext x
  by_cases hx : x = 0
  · subst hx
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff,
      map_one]
    exact PowerSeries.constantCoeff_exp (A := C)
  · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_neg hx, MvPowerSeries.coeff_one, if_neg hx, map_zero]

theorem frameSt_of (hAct : ActSt) (hUnit : UnitSt) : FrameSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hh w0 n
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis hh.ax0
  have hact : ∀ i, constantCoeff (B.actK C w0 i) = 0 := fun i => by
    unfold FB.actK
    rw [constantCoeff_map, B.A.const, map_zero]
  have hpair : ∀ j i, constantCoeff
      ((![pt C d 0, comp1 (B.actK C w0) (pt C d 0)] : Fin 2 → Pt C 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · simp [pt]
    · exact frame_cc_ev _ (frame_cc_pt 0) (hact i)
  have hcL : constantCoeff (B.hL C h w0) = 0 := frame_cc_ev _ hpair hc
  have hS : constantCoeff (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) = 0 := by

    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => frame_cc_ev _ (frame_cc_pt b) hcL
  obtain ⟨-, -, -, hadd, hone, -⟩ := hUnit C v (Fin n × Fin d)
  refine ⟨hone _ hS, fun k => ?_, fun σ _ y hy => ?_⟩
  · unfold frameSer FB.expS
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, frame_exp_zero]
    | succ k ih =>
      rw [Nat.cast_succ, add_smul, one_smul, hadd _ _ _ hS, ih, pow_succ]
      rw [smul_eq_C_mul, map_mul, hS, mul_zero]
  · have ht : HasSubst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2) :=
      hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy q.1) q.2
    have key : subst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2)
        (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) =
        ∑ j, pairSer (fglOf hB) h (y j) (mv (dAct C B w0) (y j)) := by

      rw [← coe_substAlgHom ht, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hs : HasSubst (fun p : Fin 1 × Fin d => expPt (fglOf hB) (y b) p.2) :=
        hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy b) q.2
      rw [coe_substAlgHom, frame_subst_ev_pt b ht]
      unfold FB.hL pairSer
      rw [frame_subst_ev _ hpair hs, (hAct C v d R O B hB σ w0).1 (y b) (hy b)]
      congr 1
      funext ⟨j, i⟩
      fin_cases j
      · exact subst_X hs _
      · exact frame_subst_ev_pt 0 hs _
    rw [← key]
    unfold frameSer FB.expS PowerSeries.subst
    exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hS) ht _

end GlobalTheory.IsoTriv
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.GaugeBiadd

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.LawLog
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

def famPt {n : ℕ} (x : Fin n → Fin d → MvPowerSeries σ C) : Fin n × Fin d → MvPowerSeries σ C :=
  fun q => x q.1 q.2

theorem hs_famPt {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0) :
    HasSubst (famPt x) :=
  hasSubst_of_constantCoeff_zero fun q => hx q.1 q.2

theorem constantCoeff_vecCons_pair_eq_zero {τ : Type} {x y : Fin d → MvPowerSeries τ C} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (j : Fin 2) (i : Fin d) :
    constantCoeff ((![x, y] : Fin 2 → Fin d → MvPowerSeries τ C) j i) = 0 := by
  fin_cases j
  exacts [hx i, hy i]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt C d j i) = 0 := by simp [pt]

theorem constantCoeff_germEvalPair_eq_zero {n : ℕ} {x y : Pt C n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) {f : PS C 2 d} (hf : constantCoeff f = 0) :
    constantCoeff (ev ![x, y] f) = 0 :=
  constantCoeff_subst_eq_zero (hs_famPt (constantCoeff_vecCons_pair_eq_zero hx hy)) (fun q => constantCoeff_vecCons_pair_eq_zero hx hy q.1 q.2) hf

theorem cc_comp1 {n : ℕ} {x : Pt C n d} (hx : ∀ i, constantCoeff (x i) = 0)
    {φ : Pt C 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin d) :
    constantCoeff (comp1 φ x i) = 0 := by
  have h : ∀ (j : Fin 1) i, constantCoeff ((![x] : Fin 1 → Pt C n d) j i) = 0 := fun j i => by
    fin_cases j; exact hx i
  exact constantCoeff_subst_eq_zero (hs_famPt h) (fun q => h q.1 q.2) (hφ i)

theorem subst_famPt_pt {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    (j : Fin n) : (fun i => (subst (famPt x) (pt C d j i) : MvPowerSeries σ C)) = x j :=
  funext fun i => subst_X (hs_famPt hx) _

theorem subst_pointFamily_germEvalPair {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    {a b : Pt C n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (f : PS C 2 d) :
    (subst (famPt x) (ev ![a, b] f) : MvPowerSeries σ C) =
      subst (famPt ![fun i => (subst (famPt x) (a i) : MvPowerSeries σ C), fun i => subst (famPt x) (b i)]) f := by
  refine (subst_comp_subst_apply (hs_famPt (constantCoeff_vecCons_pair_eq_zero ha hb)) (hs_famPt hx) f).trans ?_
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> rfl

theorem subst_famPt_comp1 {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    (φ : Pt C 1 d) (j : Fin n) :
    (fun i => (subst (famPt x) (comp1 φ (pt C d j) i) : MvPowerSeries σ C)) =
      fun i => subst (fun q : Fin 1 × Fin d => x j q.2) (φ i) := by
  have h : ∀ (l : Fin 1) i, constantCoeff ((![pt C d j] : Fin 1 → Pt C n d) l i) = 0 := fun l i => by
    fin_cases l; exact cc_pt j i
  funext i
  refine (subst_comp_subst_apply (hs_famPt h) (hs_famPt hx) (φ i)).trans ?_
  congr 1
  funext ⟨l, e⟩
  fin_cases l
  exact subst_X (hs_famPt hx) _

theorem subst_elim_twoVars {x y : Fin d → MvPowerSeries σ C} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (f : PS C 2 d) :
    (subst (Sum.elim x y) (subst (twoVars C d) f) : MvPowerSeries σ C) = subst (famPt ![x, y]) f := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (i | i); exacts [hx i, hy i])
  rw [subst_comp_subst_apply hs_twoVars hs]
  congr 1
  funext ⟨j, i⟩
  rw [twoVars, subst_X hs]
  fin_cases j <;> simp [famPt]

theorem logUnit_subst [CharZero C] {v : AddValuation C (WithTop ℝ)} {n : ℕ}
    {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0) (hI : ∀ j i, MvIsInt v (x j i))
    {U f : PS C n d} (hU : MvIsInt v U) (hf : constantCoeff f = 0) (e : U = FB.expS C f) :
    LogUnit v (subst (famPt x) f : MvPowerSeries σ C) := by
  refine ⟨constantCoeff_subst_eq_zero (hs_famPt hx) (fun q => hx q.1 q.2) hf, ?_⟩
  have h := ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v hU (a := famPt x) (fun q => hI q.1 q.2) (fun q => hx q.1 q.2)
  rw [e] at h
  unfold FB.expS PowerSeries.subst at h
  rw [subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const (hs_famPt hx)] at h
  exact h

end

theorem biadd_of_add_of_act : AddSt → ActSt → BiaddSt := by
  intro hAdd hAct C _ _ v d R _ _ O _ _ B hB h H σ _ w w' z hw hw' hz
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis H.ax0
  have hF : ∀ i, constantCoeff (B.FK C i) = 0 := GlobalTheory.GaugeBaseChange.gp_FK B
  have hA : ∀ a i, constantCoeff (B.actK C a i) = 0 := fun a => GlobalTheory.GaugeBaseChange.gp_actK B a
  have cw := cc_expPt (fglOf hB) hw.1
  have cw' := cc_expPt (fglOf hB) hw'.1
  have cz := cc_expPt (fglOf hB) hz.1
  have hadd : expPt (fglOf hB) (w + w') =
      fun i => subst (famPt ![expPt (fglOf hB) w, expPt (fglOf hB) w']) (B.FK C i) := by
    rw [(hAdd C v d (fglOf hB) σ).2.1 w w' hw.1 hw'.1]
    funext i
    exact subst_elim_twoVars cw cw' (B.FK C i)
  have cA : ∀ {n : ℕ} (j l : Fin n) i, constantCoeff (addOf (B.FK C) (pt C d j) (pt C d l) i) = 0 :=
    fun j l i => constantCoeff_germEvalPair_eq_zero (cc_pt j) (cc_pt l) (hF i)
  have sA : ∀ {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (_ : ∀ j i, constantCoeff (x j i) = 0) (j l : Fin n),
      (fun i => (subst (famPt x) (addOf (B.FK C) (pt C d j) (pt C d l) i) : MvPowerSeries σ C)) =
        fun i => subst (famPt ![x j, x l]) (B.FK C i) := fun hx j l => by
    funext i
    unfold addOf
    rw [subst_pointFamily_germEvalPair hx (cc_pt j) (cc_pt l), subst_famPt_pt hx, subst_famPt_pt hx]
  refine ⟨constantCoeff_subst_eq_zero (hs_famPt (constantCoeff_vecCons_pair_eq_zero cw cz)) (fun q => constantCoeff_vecCons_pair_eq_zero cw cz q.1 q.2) hc, ?_, ?_,
    fun a => ?_⟩
  · have hx : ∀ (j : Fin 3) i, constantCoeff ((![expPt (fglOf hB) w, expPt (fglOf hB) w', expPt (fglOf hB) z] :
        Fin 3 → Fin d → MvPowerSeries σ C) j i) = 0 := fun j i => by
      fin_cases j; exacts [cw i, cw' i, cz i]
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hw.2 i, hw'.2 i, hz.2 i]) hB.2.2.1
      (by rw [map_sub, map_add (f := _), constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cA _ _) (cc_pt _) hc]; simp) H.ph1
    rw [subst_sub (hs_famPt hx), subst_add (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _), subst_pointFamily_germEvalPair hx (cA _ _) (cc_pt _), sA hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [hadd]
    exact k
  · have hx : ∀ (j : Fin 3) i, constantCoeff ((![expPt (fglOf hB) z, expPt (fglOf hB) w, expPt (fglOf hB) w'] :
        Fin 3 → Fin d → MvPowerSeries σ C) j i) = 0 := fun j i => by
      fin_cases j; exacts [cz i, cw i, cw' i]
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hz.2 i, hw.2 i, hw'.2 i]) hB.2.2.2.1
      (by rw [map_sub, map_add (f := _), constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cc_pt _) (cA _ _) hc]; simp) H.ph2
    rw [subst_sub (hs_famPt hx), subst_add (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _), subst_pointFamily_germEvalPair hx (cc_pt _) (cA _ _), sA hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [hadd]
    exact k
  · have hx := constantCoeff_vecCons_pair_eq_zero cw cz
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hw.2 i, hz.2 i]) (hB.2.2.2.2 a)
      (by rw [map_sub, constantCoeff_germEvalPair_eq_zero (cc_comp1 (cc_pt _) (hA _)) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_comp1 (cc_pt _) (hA _)) hc]; simp) (H.ad a)
    rw [subst_sub (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_comp1 (cc_pt _) (hA _)) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_comp1 (cc_pt _) (hA _)), subst_famPt_comp1 hx, subst_famPt_comp1 hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [(hAct C v d R O B hB σ a).1 w hw.1, (hAct C v d R O B hB σ (star a)).1 z hz.1]
    exact k

end GlobalTheory.IsoTriv.GaugeBiadd
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem exp_point_zero {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (σ : Type) : expPt G (0 : Fin d → MvPowerSeries σ C) = 0 := by
  funext i
  have h0 : ∀ j, constantCoeff ((0 : Fin d → MvPowerSeries σ C) j) = 0 := fun _ => by simp
  have hs : HasSubst (0 : Fin d → MvPowerSeries σ C) := hasSubst_of_constantCoeff_zero h0
  ext e
  simp only [expPt, Pi.zero_apply]
  rw [coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m = 0
  · subst hm
    simp [coeff_zero_eq_constantCoeff_apply, (isExp_expOf G).1 i]
  · obtain ⟨s, hsm⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc; push_neg at hc; exact hm (Finsupp.ext hc)
    have : (m.prod fun s n => ((0 : Fin d → MvPowerSeries σ C) s) ^ n) = 0 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hsm)
      simp [zero_pow hsm]
    rw [this, map_zero, smul_zero]

theorem log_sum_additive_preserves_integrality : AddSt := by
  intro C _ v d G σ _
  have hadd : ∀ w w' : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      (∀ i, constantCoeff (w' i) = 0) →
      expPt G (w + w') = fun i => subst (Sum.elim (expPt G w) (expPt G w')) (G.F i) := by
    intro w w' hw hw'
    set a : Fin d ⊕ Fin d → MvPowerSeries σ C := Sum.elim (expPt G w) (expPt G w') with ha_def
    have ha0 : ∀ s, constantCoeff (a s) = 0 := by
      rintro (b | b)
      · exact cc_expPt G hw b
      · exact cc_expPt G hw' b
    have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
    have hF : HasSubst G.F := hasSubst_of_constantCoeff_zero G.F_const
    set y : Fin d → MvPowerSeries σ C := fun i => subst a (G.F i) with hy_def
    have hy0 : ∀ i, constantCoeff (y i) = 0 := fun i =>
      constantCoeff_subst_eq_zero ha ha0 (G.F_const i)
    have hlg : lgPt G y = w + w' := by
      funext i
      have h1 := subst_comp_subst_apply hF ha (G.lg i)
      have hXl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      have hXr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      rw [G.lg_F, subst_add ha, subst_comp_subst_apply hXl ha, subst_comp_subst_apply hXr ha] at h1
      have hl : (fun s : Fin d => subst a (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w := by
        funext s; rw [subst_X ha]; rfl
      have hr : (fun s : Fin d => subst a (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w' := by
        funext s; rw [subst_X ha]; rfl
      rw [hl, hr] at h1
      have e1 : subst (expPt G w) (G.lg i) = w i := by
        have := congrFun (lgPt_expPt G hw) i; exact this
      have e2 : subst (expPt G w') (G.lg i) = w' i := by
        have := congrFun (lgPt_expPt G hw') i; exact this
      show subst y (G.lg i) = w i + w' i
      rw [hy_def, ← h1, e1, e2]
    rw [← hlg, expPt_lgPt G hy0]
  refine ⟨⟨fun i => by simp, fun i => ?_⟩, hadd, ?_⟩
  · rw [exp_point_zero G σ]; intro α; simp [IsIntV]
  · intro w w' hw hw'
    refine ⟨fun i => by simp [hw.1 i, hw'.1 i], fun i => ?_⟩
    rw [hadd w w' hw.1 hw'.1]
    refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (G.F_int i) ?_ ?_
    · rintro (b | b)
      · exact hw.2 b
      · exact hw'.2 b
    · rintro (b | b)
      · exact cc_expPt G hw.1 b
      · exact cc_expPt G hw'.1 b

end GlobalTheory.IsoTriv
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.Incl

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem subst_expAlong {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin d → C)
    (A : κ → Matrix (Fin d) (Fin d) C) (t : κ → C) (hA : ∀ b a, (A b).mulVec (u b a) = t b • u b a) (i : Fin d) :
    subst (expAlong (fun _ : κ => G) u)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C))) i) =
      subst (fun e : Fin d => ∑ ℓ : (Σ b, ι b), (t ℓ.1 * u ℓ.1 ℓ.2 e) • (X ℓ : MvPowerSeries (Σ b, ι b) C))
        (expOf G i) := by
  have hu : ∀ (b : κ) (e : Fin d),
      constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have hE : ∀ (b : κ), (fun e : Fin d => expAlong (fun _ : κ => G) u ⟨b, e⟩) =
      expPt G (fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b => rfl
  have hs : HasSubst (expAlong (fun _ : κ => G) u) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hu q.1) q.2
  have hX : ∀ (b : κ) (e : Fin d), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C) = 0 := by simp

  rw [subst_expPt G hs (fun e => by
  rw [Finset.sum_apply, map_sum]
  exact Finset.sum_eq_zero fun b _ => cc_mv _ (cc_lgPt G (hX b)) e)]
  unfold expPt
  congr 1
  funext e

  rw [Finset.sum_apply, ← coe_substAlgHom hs, map_sum, coe_substAlgHom, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv hs]
  have h1 : (fun e' => subst (expAlong (fun _ : κ => G) u)
      (lgPt G (fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C)) e')) =
      fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
    funext e'
    rw [subst_lgPt G hs (hX b)]
    simp only [subst_X hs]
    rw [hE b, lgPt_expPt G (hu b)]
  rw [h1]
  simp only [mv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact congrFun (hA b a) e

theorem isotropic_blocks {O : Type} [CommRing O] [StarRing O] (I : Ideal O) {φ : Type} {r m : φ → ℕ} {n : ℕ}
    (blk : (Σ f : φ, Fin (m f)) ↪ Fin n) (ε : φ → O) (x : ∀ f, Fin (r f) → Fin n → O)
    (h0 : ∀ f b j, j ∉ Set.range (fun j => blk ⟨f, j⟩) → x f b j = 0)
    (hiso : ∀ f b b', ∑ j, x f b j * star (x f b' j) ∈ I) (b b' : Σ f, Fin (r f)) :
    ∑ j, star (ε b.1 * x b.1 b.2 j) * (ε b'.1 * x b'.1 b'.2 j) ∈ I := by
  obtain ⟨f, β⟩ := b
  obtain ⟨f', β'⟩ := b'
  by_cases hf : f = f'
  · subst hf
    have e : ∑ j, star (ε f * x f β j) * (ε f * x f β' j) =
        (star (ε f) * ε f) * ∑ j, x f β' j * star (x f β j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul]; ring
    rw [e]
    exact I.mul_mem_left _ (hiso f β' β)
  · refine Ideal.sum_mem _ fun j _ => ?_
    by_cases h1 : j ∈ Set.range (fun j => blk ⟨f, j⟩)
    · by_cases h2 : j ∈ Set.range (fun j => blk ⟨f', j⟩)
      · obtain ⟨j1, h1⟩ := h1
        obtain ⟨j2, h2⟩ := h2
        exact absurd (congrArg Sigma.fst (blk.injective (h1.trans h2.symm))) hf
      · simp [h0 f' β' j h2]
    · simp [h0 f β j h1]

theorem inclSt_of_lim (hAct : LimActSt) (hPt : LimPtSt) (hFr : LimFrameSt) : InclSt := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ Y cx n B hB
  obtain ⟨blk, hblk⟩ := hB
  choose x hx0 hxB hxiso using fun (f : {f : Lt1 Dw // cx f ≠ 0}) (N : ℕ) => (hblk f).2.2 N
  choose ε hε using fun τ : E →+* ℂ => hAct E H Dw l Xo c hstar T io y Ch p Y τ
  choose A hAapp hAlie using fun (b : Col cx) (j : Fin n) =>
    hε b.1.1.1 (B b.1.1 b.2 j) (fun N => x b.1 N b.2 j) (fun N => hxB b.1 N b.2 j)
  letI := io.toAlgebra
  letI : Algebra T.Fr Y.C := Y.ιF.toAlgebra
  have hw : ∀ b : Col cx, IntLog (fglOf (isIntFB_chart Ch Y)) (lgPt (fgl Ch Y)
      fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) Y.C)) :=
    fun b => intLog_lgPt_X (fgl Ch Y) (fun e => (⟨b, e⟩ : Σ _ : Col cx, Fin (chD Ch.ch)))
  have hint := fun j : Fin n => hPt Y.C (vX_vp Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (Col cx) _ hw
    (fun b => A b j) (fun N b => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b => hAapp b j N)
  refine ⟨fun q => expPt (fgl Ch Y) (∑ b, mv (A b q.1) (lgPt (fgl Ch Y) fun e => X ⟨b, e⟩)) q.2,
    fun q => cc_expPt _ (hint q.1).1 q.2, fun q => (hint q.1).2 q.2, fun q => ?_, ?_⟩
  · exact subst_expAlong (fgl Ch Y) (fun b : Col cx => frame Ch Y b.1.1) (fun b => A b q.1)
      (fun b => jX Y (B b.1.1 b.2 q.1)) (fun b a => hAlie b q.1 _) q.2
  · exact hFr Y.C (vX_vp Y) p (vX_vp_p Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (gauge_chart Ch Y) _ (Col cx) _
      hw H.w0 n A (fun N b j => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b j => hAapp b j N)
      (fun N => isotropic_blocks _ blk (fun f => ε f.1.1 N) (fun f => x f N) (fun f => hx0 f N)
        (fun f b b' => by simpa only [hstar] using hxiso f N b b'))

end GlobalTheory.IsoTriv.Incl
end
end

end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.logarithm_sum_integral_additive : AddSt := by
  first | exact @GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | exact GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | (intros; apply GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality <;> assumption)

end
end
