module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AofUpdate
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle011
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InParamMap
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle006
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

def yE (hL : LinD X) (v : X.Pl) : Module.End X.G.Kf (X.Fm 0) :=
  { toFun := X.yv v, map_add' := hL.yv_add v, map_smul' := fun a F => hL.yv_smul v a F }

def PE (hL : LinD X) (vs : List X.Pl) : Module.End X.G.Kf (X.Fm 0) := (vs.map (yE hL)).prod

theorem yE_comm (hL : LinD X) (v v' : X.Pl) : Commute (yE hL v) (yE hL v') :=
  LinearMap.ext fun F => hL.yv_comm v v' F

theorem yE_PE_comm (hL : LinD X) (v : X.Pl) (ws : List X.Pl) : Commute (yE hL v) (PE hL ws) := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hy
  exact yE_comm hL v w

theorem PE_comm (hL : LinD X) (vs ws : List X.Pl) : Commute (PE hL vs) (PE hL ws) := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx
  exact yE_PE_comm hL v ws

theorem PE_cons (hL : LinD X) (v : X.Pl) (vs : List X.Pl) : PE hL (v :: vs) = yE hL v * PE hL vs := by
  simp [PE]

theorem PE_append (hL : LinD X) (vs ws : List X.Pl) : PE hL (vs ++ ws) = PE hL vs * PE hL ws := by
  simp [PE]

theorem PE_perm (hL : LinD X) {vs ws : List X.Pl} (h : vs.Perm ws) : PE hL vs = PE hL ws := by
  apply List.Perm.prod_eq' (h.map _)
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 ha
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hb
  exact yE_comm hL v w

theorem PE_mem (hL : LinD X) {S : Set (X.Fm 0)} (hy : ∀ v, ∀ F ∈ S, X.yv v F ∈ S) (vs : List X.Pl) :
    ∀ F ∈ S, PE hL vs F ∈ S := by
  induction vs with
  | nil => intro F hF; simpa [PE] using hF
  | cons v vs ih =>
    intro F hF
    rw [PE_cons]
    exact hy v _ (ih F hF)

theorem PE_pow_mem (hL : LinD X) {S : Set (X.Fm 0)} (hy : ∀ v, ∀ F ∈ S, X.yv v F ∈ S) (vs : List X.Pl) (n : ℕ) :
    ∀ F ∈ S, (PE hL vs ^ n) F ∈ S := by
  induction n with
  | zero => intro F hF; simpa using hF
  | succ n ih =>
    intro F hF
    rw [pow_succ']
    exact PE_mem hL hy vs _ (ih F hF)

theorem fold_eq (hL : LinD X) (n : ℕ) (vs : List X.Pl) (z : X.Fm 0) :
    vs.foldr (fun v F' => (X.yv v)^[n] F') z = (PE hL vs ^ n) z := by
  induction vs with
  | nil => simp [PE]
  | cons v vs ih =>
    rw [PE_cons, (yE_PE_comm hL v vs).mul_pow, List.foldr_cons, ih, Module.End.mul_apply,
      Module.End.pow_apply (yE hL v)]
    rfl

theorem yv_FQ (hL : LinD X) (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) (v : X.Pl) :
    ∀ F ∈ X.FQ 0, X.yv v F ∈ X.FQ 0 := by
  intro F hF
  unfold Sys.FQ at hF ⊢
  induction hF using Submodule.span_induction with
  | zero =>
    have := hL.yv_smul v 0 0
    simp only [zero_smul] at this
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy' => rw [hL.yv_add]; exact Submodule.add_mem _ hx hy'
  | smul c x _ hx => rw [hL.yv_smul]; exact Submodule.smul_mem _ _ hx
  | mem x hx => exact Submodule.subset_span (hy v x hx)

variable (X)

def PrS (j : ℕ) (vs : List X.Pl) : ℤ :=
  ∑ v, if v ∈ vs then PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j else 0

variable {X}

theorem PrS_cons (j : ℕ) (v : X.Pl) (vs : List X.Pl) (hv : v ∉ vs) :
    PrS X j (v :: vs) = PrS X j vs + PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j := by
  unfold PrS
  have : PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j =
      ∑ v', if v' = v then PrZ X.t X.G.P.r (X.G.P.lam0 v') (X.w v') j else 0 := by
    rw [Finset.sum_ite_eq' univ v]
    simp
  rw [this, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v' _
  by_cases h : v' = v
  · subst h
    simp [hv]
  · simp [h]

theorem ZL_chain (hp : (p : X.G.Kf) ≠ 0) (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ)
    (hCi : ∀ v, ∀ F ∈ X.FQ 0, X.Zop v (u v) (m v) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F))
    (hyQ : ∀ v, ∀ F ∈ X.FQ 0, X.yv v F ∈ X.FQ 0) (vs : List X.Pl) (hnd : vs.Nodup) (F : X.Fm 0) (hF : F ∈ X.FQ 0) :
    ZL X u m (j + 1) vs (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrS X (j + 1) vs)) • X.chainK (j + 1) (PE hL vs F) := by
  induction vs with
  | nil => simp [ZL, PrS, PE]
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    show X.Zop v (u v) (m v) (j + 1) (ZL X u m (j + 1) vs (X.chainK (j + 1) F)) = _
    rw [ih hnd.2, Zop_smul hL, hCi v _ (PE_mem hL (S := (X.FQ 0 : Set (X.Fm 0))) hyQ vs F hF), smul_smul,
      ← zpow_add₀ hp, PrS_cons _ _ _ hnd.1, PE_cons]
    rfl

theorem vGeK_vsc (g : ℝ) : X.vGeK (X.vsc g) g := (vGeK_iff X).2 ⟨1, by simp⟩

def bbJ (X : Sys p) (Lv : List X.Pl) (Gn G0n : X.Pl → ℕ → ℝ) (Q : ℕ → X.Pl → Bool) (j : ℕ) : ℝ :=
  ∑ v, (if v ∈ Lv.filter (Q j) then Gn v (j + 1) else G0n v (j + 1)) - X.dG j -
        (PrS X (j + 1) (Lv.filter (Q j)) : ℝ)

theorem main_ind {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0) (hL : LinD X)
    (hF : FormB X Y) (hE : EntCondition X Y) (u m : X.Pl → ℕ → X.G.Kf)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ j < X.mm, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, ∀ j < X.mm, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v))
    (hCi : ∀ v, ∀ j < X.mm, ∀ F ∈ X.FQ 0, X.Zop v (u v) (m v) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F))
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0)
    (Lv : List X.Pl) (hnd : Lv.Nodup) (Gn G0n : X.Pl → ℕ → ℝ) (Q : ℕ → X.Pl → Bool)
    (h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1))
    (h2 : ∀ v, ∀ j < X.mm, Y.LowAt j v (G0n v (j + 1))) :
    ∀ m' ≤ X.mm, ∀ F1 ∈ X.Int 0, X.vGe m' (X.chainK m' ((PE hL Lv ^ m') F1))
      (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) := by
  intro m'
  induction m' with
  | zero =>
    intro _ F1 hF1
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact (vGe_zero_iff X).2 hF1
  | succ m' ih =>
    intro hm F1 hF1
    have hj : m' < X.mm := hm
    set B := Lv.filter (Q m') with hB
    set C := Lv.filter (fun x => !Q m' x) with hC
    have e1 : PE hL Lv = PE hL B * PE hL C := by
      rw [← PE_append]
      exact (PE_perm hL (List.filter_append_perm (Q m') Lv)).symm
    have e2 : PE hL Lv ^ (m' + 1) = PE hL B * (PE hL Lv ^ m' * PE hL C) := by
      have e0 : PE hL Lv ^ (m' + 1) = (PE hL B * PE hL C) * PE hL Lv ^ m' := by rw [pow_succ', ← e1]
      rw [e0, mul_assoc, ((PE_comm hL C Lv).pow_right m').eq]
    have hF1' : PE hL C F1 ∈ X.Int 0 := PE_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy C F1 hF1
    set W := (PE hL Lv ^ m') (PE hL C F1) with hW
    have hWi : W ∈ X.Int 0 := PE_pow_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy Lv m' _ hF1'
    have hWQ : W ∈ X.FQ 0 := Submodule.subset_span hWi
    have hBnd : B.Nodup := hnd.filter _
    have e3 := ZL_chain hp hL u m m' (fun v => hCi v m' hj) (yv_FQ hL hy) B hBnd W hWQ
    have e4 : X.chainK (m' + 1) ((PE hL Lv ^ (m' + 1)) F1) =
        ((p : X.G.Kf) ^ (-(PrS X (m' + 1) B))) • ZL X u m (m' + 1) B (X.chainK (m' + 1) W) := by
      rw [e3, smul_smul, ← zpow_add₀ hp, neg_add_cancel, zpow_zero, one_smul, e2]
      rfl
    obtain ⟨G', hG', hG'e⟩ := (vGe_iff X).1 (ih (le_of_lt hj) _ hF1')
    have e5 : X.chainK (m' + 1) W = X.vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) • X.Kz m' G' := by
      show X.Kz m' (X.chainK m' W) = _
      rw [← hG'e, map_smul]
    rw [e4, e5, ZL_smul hL]
    have hb := ZL_bound hfr hL hF hE u m m' hj hu (fun v => hc0 v m' hj) (fun v => hcr v m' hj) B hBnd
      (fun v => if v ∈ B then Gn v (m' + 1) else G0n v (m' + 1))
      (fun v hv => by simp only [hv, if_true]; exact h1 v (List.mem_of_mem_filter hv) m' hj)
      (fun v hv => by simp only [hv, if_false]; exact h2 v m' hj) G' hG'
    have h3 := vGe_smul X hfr (vGeK_ppow X hfr (-(PrS X (m' + 1) B))) (vGe_smul X hfr (vGeK_vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j)) hb)
    rw [Finset.sum_range_succ]
    refine vGe_mono X hfr (le_of_eq ?_) h3
    conv_lhs => rw [bbJ]
    push_cast
    ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def nc_Need3 (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        nc_Size D L Y u w hg t0 j ∧
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem numerical_closed_of_threshold (C₀ : ℝ) (h9 : 9 ≤ C₀) (h : nc_Need3 C₀) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  numerical_closed_of_need C₀ fun D L X Y K h1 h2 h3 hr hs hT hL u w hg hlog t0 ht0 j hj =>
    have H := h D L X Y K h1 h2 h3 hr hs hT hL u w hg hlog t0 ht0 j hj
    ⟨nc_de X Y K hT hL u w hg t0 ht0 j hj (h9.trans h1) (h9.trans h2) hlog H.1, H.2⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem atPi_eq_rescale {σ R : Type} [CommRing R] (vp : R) (f : MvPowerSeries σ R) :
    atPi vp f = MvPowerSeries.rescale (fun _ => vp) f := by
  ext n
  rw [MvPowerSeries.coeff_rescale]
  show vp ^ n.degree * MvPowerSeries.coeff n f = _
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

private theorem atPi_sum_C_mul_X_eq_C_mul {σ R ι : Type} [CommRing R] (vp : R) (t : Finset ι) (a : ι → R)
    (g : ι → σ) :
    atPi vp (∑ i ∈ t, MvPowerSeries.C (a i) * MvPowerSeries.X (g i)) =
      MvPowerSeries.C vp * ∑ i ∈ t, MvPowerSeries.C (a i) * MvPowerSeries.X (g i) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_C_mul]
  show vp ^ n.degree * MvPowerSeries.coeff n _ = _

  simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs with h
  · subst h
    simp
  · simp

theorem atPi_coordZA (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    atPi vp (X.coordZA K' j x) = MvPowerSeries.C vp * X.coordZA K' j x := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp only [Sys.coordZA] <;> exact atPi_sum_C_mul_X_eq_C_mul _ _ _ _

theorem map_coordZA (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.map (algebraMap K1 K') (X.coordZA K1 j x) = X.coordZA K' j x := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>

    simp only [Sys.coordZA, map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X,
    ← IsScalarTower.algebraMap_apply]

theorem atPi_map_ThZA (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K') (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) K1) :
    atPi vp (MvPowerSeries.map (algebraMap K1 K') (X.ThZA K1 j U)) =
      MvPowerSeries.subst (fun x => MvPowerSeries.C vp * X.coordZA K' j x) (MvPowerSeries.map (algebraMap K1 K') U) := by
  have hA1 : MvPowerSeries.HasSubst (X.coordZA K1 j) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K1 j)
  have hA' : MvPowerSeries.HasSubst (X.coordZA K' j) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K' j)
  rw [Sys.ThZA, MvPowerSeries.map_subst hA1]
  simp only [map_coordZA X K1 K']
  rw [atPi_eq_rescale, MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.subst_comp_subst_apply hA' (MvPowerSeries.HasSubst.smul_X _)]
  refine congrArg (fun a => MvPowerSeries.subst a (MvPowerSeries.map (algebraMap K1 K') U)) (funext fun s => ?_)
  rw [← MvPowerSeries.rescale_eq_subst, ← atPi_eq_rescale, atPi_coordZA]

theorem restSIntA : RestSIntA X := by
  intro j K1 _ _ R1 U hU K' _ _ _ _ R' vp hvp hRp hR1
  rw [atPi_map_ThZA X K1 K' vp j U]
  refine genInt p K' R' vp hvp hRp _ (inParam_map p K' K1 R1 R' hR1 U hU) (X.coordZA K' j)
    (coordZA_const X K' j) ?_
  intro i
  rcases i with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp only [Sys.coordZA] <;>
    exact IntR_sum _ _ (fun s _ => IntR_mul (IntR_C (hRp (W_mem_Rp (p := p) (K' := K') vp _))) (IntR_X _))

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

namespace Gen

theorem fac_embDomain {σ τ : Type} (e : σ ↪ τ) (κ : σ →₀ ℕ) : fac (Finsupp.embDomain e κ) = fac κ := by
  classical
  unfold fac
  rw [Finsupp.support_embDomain, Finset.prod_map]
  simp [Finsupp.embDomain_apply]

theorem jp_rename {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] {ι : Pl → Type} (v : Pl)
    (P : MvPolynomial (ι v) A) (g : MvPowerSeries (ι v) K) :
    jp (MvPolynomial.rename (Sigma.mk v) P) (atP v g) = jp P g := by
  classical
  have hinj : Function.Injective (Sigma.mk v : ι v → Σ v, ι v) := sigma_mk_injective
  unfold jp atP
  rw [MvPolynomial.support_rename_of_injective hinj,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hinj h)]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have he : Finsupp.mapDomain (Sigma.mk v) κ = Finsupp.embDomain (Function.Embedding.sigmaMk v) κ :=
    by rw [Finsupp.embDomain_eq_mapDomain]; rfl
  rw [MvPolynomial.coeff_rename_mapDomain _ hinj, he, fac_embDomain, MvPowerSeries.coeff_embDomain_rename]

end Gen

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def en_mapP (Kc σ τ : Type) [Field Kc] :
    MvPolynomial σ (MvPolynomial τ ℤ) →+* MvPolynomial σ (MvPolynomial τ Kc) :=
  MvPolynomial.map (MvPolynomial.map (Int.castRingHom Kc))

theorem en_applyD_eq {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    applyD P f = Gen.jp (en_mapP Kc σ τ P) f := by
  classical
  unfold applyD Gen.jp en_mapP
  symm
  refine (Finset.sum_subset (MvPolynomial.support_map_subset _ P) ?_).trans ?_
  · intro n _ hn
    simp only [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn, smul_zero]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.coeff_map]
    unfold Gen.fac
    push_cast
    rfl

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def en_Ploc (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (MvPolynomial (X.FrI j) Y.Kc) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (X.FrI j) Y.Kc)) ^ (X.colExp j I i0 v s c) *
    Matrix.det (Matrix.of fun (i i' : Fin (X.colHt v (j + 1) s c)) =>
      ∑ a : Fin (NN X.G.P.m X.t j),
        MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : X.FrI j)) *
          MvPolynomial.X ((s, a, I v s c i'.val) :
            Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))))

theorem en_mapP_PIvS (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    en_mapP Y.Kc (X.ZA j) (X.FrI j) (PIvS X j I i0 v) =
      MvPolynomial.rename (Sigma.mk v) (en_Ploc X Y j I i0 v) := by
  unfold en_mapP PIvS en_Ploc Sys.colFac
  simp only [map_prod, map_mul, map_pow, map_natCast, RingHom.map_det, AlgHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 2
  ext i i'

  simp [Matrix.of_apply, map_sum, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
