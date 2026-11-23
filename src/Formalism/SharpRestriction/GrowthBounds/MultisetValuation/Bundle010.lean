module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle007
import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle001

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def EntCondition : Prop :=
  ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ), (∀ v, PlaceB X Y j v (i0 v) (gP v)) →
    EntB X Y j i0 (∑ v, (gP v : ℝ))

def RatCondition : Prop := ∀ v j, ∃ q : ℚ, X.g0v v j = q

def HeckeIntegralLevel : Prop :=
  ∀ v, ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, ∀ F ∈ X.Int (j + 1), X.Tt v i (j + 1) F ∈ X.Int (j + 1)

theorem sum_ite_single {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι) (a : ℝ) (f : ι → ℝ) :
    ∑ v', (if v' = v then a else f v') = a + ∑ v' ∈ univ.erase v, f v' := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), if_pos rfl]
  congr 1
  refine Finset.sum_congr rfl fun v' hv' => ?_
  rw [if_neg (Finset.ne_of_mem_erase hv')]

variable {X Y}

theorem PlaceB.mono {j : ℕ} {v : X.Pl} {i : ℕ} {g g' : ℝ} (h : g' ≤ g) (hP : PlaceB X Y j v i g) :
    PlaceB X Y j v i g' := by
  unfold PlaceB at *
  rcases hP with ⟨hi, hL | hL⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨hi, Or.inl (Pend.LowAt.mono Y h hL)⟩
  · exact Or.inl ⟨hi, Or.inr (h.trans hL)⟩
  · exact Or.inr ⟨h1, h2, h.trans h3⟩

theorem EntB.mono {j : ℕ} {i0 : X.Pl → ℕ} {g g' : ℝ} (h : g' ≤ g) (hB : EntB X Y j i0 g) : EntB X Y j i0 g' := by
  unfold EntB at *
  intro La La' h1 h2 φ I n
  exact Pend.geC_mono Y h (hB La La' h1 h2 φ I n)

theorem ent_strict (hE : EntCondition X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (gP : X.Pl → ℝ)
    (hP : ∀ v, PlaceB X Y j v (i0 v) (gP v)) (g' : ℝ) (hg : g' < ∑ v, gP v) : EntB X Y j i0 g' := by
  classical
  have hD : 0 < ∑ v, gP v - g' := sub_pos.mpr hg
  have hc : (0 : ℝ) < Fintype.card X.Pl + 1 := by positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (∑ v, gP v - g') / (Fintype.card X.Pl + 1) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hD hc
  have hεc : (Fintype.card X.Pl : ℝ) * ε < ∑ v, gP v - g' := by
    have h1 : ε * (Fintype.card X.Pl + 1) = ∑ v, gP v - g' := by
      rw [hε]; exact div_mul_cancel₀ _ hc.ne'
    nlinarith
  have hq : ∀ v, ∃ q : ℚ, gP v - ε < q ∧ (q : ℝ) < gP v := fun v => exists_rat_btwn (by linarith)
  choose q hq1 hq2 using hq
  have hsum : g' ≤ ∑ v, (q v : ℝ) := by
    have h1 : ∑ v, (gP v - ε) ≤ ∑ v, (q v : ℝ) := Finset.sum_le_sum fun v _ => (hq1 v).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    linarith
  exact EntB.mono hsum (hE j hj i0 q fun v => PlaceB.mono (hq2 v).le (hP v))

theorem formB_lim (hF : FormB X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (vs : List X.Pl) (g : ℝ) (hnd : vs.Nodup)
    (hr : ∀ v, i0 v ≤ X.G.P.r) (h0 : ∀ v, v ∉ vs → i0 v = 0) (hB : ∀ g' < g, EntB X Y j i0 g')
    (G : X.Fm j) (hG : G ∈ X.Int j) : X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (g - X.dG j) := by
  have he0 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (g - X.dG j) * (X.eO : ℝ) := ⟨_, rfl⟩
  have hc1 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hc2 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (x - ⌈x⌉ + 1) / ((X.eO : ℝ) + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) (by linarith)
  have hδe : δ * (X.eO : ℝ) < x - ⌈x⌉ + 1 := by
    have h1 : δ * ((X.eO : ℝ) + 1) = x - ⌈x⌉ + 1 := by
      rw [hδ]; exact div_mul_cancel₀ _ (by linarith)
    nlinarith
  have hlin : (g - δ - X.dG j) * (X.eO : ℝ) = x - δ * (X.eO : ℝ) := by rw [hx]; ring
  have hceil : ⌈(g - δ - X.dG j) * (X.eO : ℝ)⌉ = ⌈(g - X.dG j) * (X.eO : ℝ)⌉ := by
    rw [← hx, Int.ceil_eq_iff, hlin]
    constructor
    · linarith
    · nlinarith
  have h := hF j hj i0 vs (g - δ) hnd hr h0 (hB _ (by linarith)) G hG
  have hv : X.vsc (g - δ - X.dG j) = X.vsc (g - X.dG j) := by rw [vsc_def, vsc_def, hceil]
  unfold Sys.vGe at h ⊢
  rw [hv] at h
  exact h

theorem form_of_place (hF : FormB X Y) (hE : EntCondition X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (vs : List X.Pl)
    (gP : X.Pl → ℝ) (hnd : vs.Nodup) (hr : ∀ v, i0 v ≤ X.G.P.r) (h0 : ∀ v, v ∉ vs → i0 v = 0)
    (hP : ∀ v, PlaceB X Y j v (i0 v) (gP v)) (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (∑ v, gP v - X.dG j) :=
  formB_lim hF j hj i0 vs (∑ v, gP v) hnd hr h0 (fun g' hg' => ent_strict hE j hj i0 gP hP g' hg') G hG

theorem form_valuation_of_bound (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (h3 : adm3 D X Y) : Conclusion0 D X := by
  unfold Conclusion0
  intro j hj G hG
  have h := hF j hj (fun _ => 0) [] 0 List.nodup_nil (fun _ => Nat.zero_le _) (fun _ _ => rfl)
    (fun La La' h1 h2 φ I n => h3 j hj La La' h1 h2 φ I n) G hG
  rw [zero_sub] at h
  exact h

theorem theorem_A_entries_of_corollary (D : Formalism.BasicNotions.D7) (hE : EntCondition X Y) (hQ : RatCondition X) (h2U : VolumeRatio₂ D X Y) : projection_lemma_base_level D X Y := by
  unfold projection_lemma_base_level
  intro j hj La La' h1 h2 φ I n
  choose q hq using hQ
  have hP : ∀ v, PlaceB X Y j v 0 (q v (j + 1)) := fun v =>
    Or.inl ⟨rfl, Or.inl (by rw [← hq v (j + 1)]; exact h2U v j hj)⟩
  have h := hE j hj (fun _ => 0) (fun v => q v (j + 1)) hP La La' h1 h2 φ I n
  have hs : ∑ v, X.g0v v (j + 1) = ∑ v, ((q v (j + 1) : ℚ) : ℝ) :=
    Finset.sum_congr rfl fun v _ => hq v (j + 1)
  rw [hs]
  exact h

theorem slopeEstimate_of_lemmaB_slopeLine (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) : Conclusion2 D X := by
  unfold Conclusion2
  intro j hj G hG
  exact form_of_place hF hE j hj (fun _ => 0) [] (fun v => X.g0v v (j + 1)) List.nodup_nil
    (fun _ => Nat.zero_le _) (fun _ _ => rfl) (fun v => Or.inl ⟨rfl, Or.inl (h2U v j hj)⟩) G hG

theorem hecke_integral_of_forms (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) : MassRatio₂ D X := by
  classical
  unfold MassRatio₂
  intro v j hj G hG
  have hP : ∀ v', PlaceB X Y j v' 0
      (if v' = v then X.gv v (j + 1) - X.alEven v else X.g0v v' (j + 1)) := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      rw [if_pos rfl]
      exact Or.inl ⟨rfl, Or.inr le_rfl⟩
    · rw [if_neg hv]
      exact Or.inl ⟨rfl, Or.inl (h2U v' j hj)⟩
  have h := form_of_place hF hE j hj (fun _ => 0) []
    (fun v' => if v' = v then X.gv v (j + 1) - X.alEven v else X.g0v v' (j + 1)) List.nodup_nil
    (fun _ => Nat.zero_le _) (fun _ _ => rfl) hP G hG
  beta_reduce at h
  rw [sum_ite_single] at h
  exact h

theorem hecke_valuation_of_entries (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) (v : X.Pl) (j : ℕ)
    (hj : j < X.mm) (i : ℕ) (hi : i ∈ Icc 1 X.G.P.r) (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (X.Tt v i (j + 1) (X.Kz j G))
      (X.gv v (j + 1) + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j) := by
  classical
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have hP : ∀ v', PlaceB X Y j v' (if v' = v then i else 0)
      (if v' = v then X.gv v (j + 1) else X.g0v v' (j + 1)) := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      rw [if_pos rfl, if_pos rfl]
      exact Or.inr ⟨hi1, hi2, le_rfl⟩
    · rw [if_neg hv, if_neg hv]
      exact Or.inl ⟨rfl, Or.inl (h2U v' j hj)⟩
  have h := form_of_place hF hE j hj (fun v' => if v' = v then i else 0) [v]
    (fun v' => if v' = v then X.gv v (j + 1) else X.g0v v' (j + 1)) (List.nodup_singleton v)
    (fun v' => by split_ifs <;> omega)
    (fun v' hv' => if_neg (by simpa using hv')) hP G hG
  beta_reduce at h
  rw [sum_ite_single] at h
  simpa only [TtL, List.foldr_cons, List.foldr_nil, eq_self_iff_true, if_true, ↓reduceIte] using h

theorem latticeChain_succ_of_partial (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) (hB1 : HeckeIntegralLevel X) :
    PointsLemma D X := fun v j hj =>
  ⟨fun i hi F hF' => hB1 v j hj i hi F hF', fun i hi G hG => hecke_valuation_of_entries D hF hE h2U v j hj i hi G hG⟩

theorem ramifiedLattice_of_chain_estimates (D : Formalism.BasicNotions.D7) (h2U : VolumeRatio₂ D X Y) (h5D : LowTermBound D X Y) : Conclusion5 D X := by
  unfold Conclusion5
  refine ⟨fun v => relative_presentation_of_d7 D _ _ _ _ _ _ _ _ _ _ _ _ (X.std v), fun VV F hF => ?_⟩
  exact h5D X.gv X.g0v X.Conclusion₂ X.Svv VV (fun _ _ _ _ => le_rfl) h2U (fun _ _ _ _ => le_rfl)
    (fun _ _ => le_rfl) F hF

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF expSum eq_of_low Gser)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

section ExpFormal

variable {K : Type} [Field K]

theorem th_expK_zero {ι : Type} : expK (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_expK, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h

theorem th_subst_expSum {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries σ K) (M : ℕ) : MvPowerSeries.subst a (expSum f M) = expSum (MvPowerSeries.subst a f) M := by

  rw [expSum, expSum, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]

theorem th_subst_expK {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (expK f) = expK (MvPowerSeries.subst a f) := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hsf : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 hf
  refine eq_of_low fun M => ?_
  have h1 := Formalism.DworkPowerSeriesWeights.low_subst_of_low ha0 (low_expK_sub hf M)
  have h2 := low_expK_sub hsf M
  have e : MvPowerSeries.subst a (expK f) - expK (MvPowerSeries.subst a f) =
      MvPowerSeries.subst a (expK f - expSum f M) -
        (expK (MvPowerSeries.subst a f) - expSum (MvPowerSeries.subst a f) M) := by
    rw [← th_subst_expSum ha, ← MvPowerSeries.coe_substAlgHom ha, map_sub]
    ring
  rw [e]
  exact low_sub h1 h2

theorem th_map_expK {ι K2 : Type} [Field K2] (φ : K →+* K2) (f : MvPowerSeries ι K) :
    MvPowerSeries.map φ (expK f) = expK (MvPowerSeries.map φ f) := by
  ext n

  rw [MvPowerSeries.coeff_map, coeff_expK, coeff_expK, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_inv₀, map_natCast, ← map_pow, MvPowerSeries.coeff_map]

end ExpFormal

section Param

variable (p : ℕ) [hp : Fact p.Prime]

def E0 {ι : Type} (f : MvPowerSeries ι (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ ∃ h : MvPowerSeries ι (WW p), MvPowerSeries.constantCoeff h = 0 ∧
    expK f = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) h

theorem integralExp_zero {ι : Type} : E0 p (0 : MvPowerSeries ι (K0 p)) := by
  refine ⟨map_zero _, 0, map_zero _, ?_⟩
  rw [th_expK_zero, map_zero, add_zero]

theorem integralExp_add {ι : Type} {f g : MvPowerSeries ι (K0 p)} (hf : E0 p f) (hg : E0 p g) : E0 p (f + g) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  obtain ⟨hg0, h', hh0', hge⟩ := hg
  refine ⟨by rw [map_add (f := _), hf0, hg0, add_zero], h + h' + h * h', by simp [hh0, hh0'], ?_⟩
  rw [expK_add hf0 hg0, hfe, hge, map_add (f := _), map_add (f := _), map_mul]
  ring

theorem integralExp_sum {ι α : Type} (s : Finset α) (f : α → MvPowerSeries ι (K0 p)) (h : ∀ a ∈ s, E0 p (f a)) :
    E0 p (∑ a ∈ s, f a) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact integralExp_zero p
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact integralExp_add p (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

def ren {κ σ R : Type} [CommRing R] (φ : κ → σ) (f : MvPowerSeries κ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ R)) f

theorem integralExp_rename {κ σ : Type} [Finite κ] (φ : κ → σ) {f : MvPowerSeries κ (K0 p)} (hf : E0 p f) :
    E0 p (ren φ f) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  have hXK : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have hXW : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have haW : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXW
  have haK : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXK
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero haK hXK hf0, ren φ h,
    MvPowerSeries.constantCoeff_subst_eq_zero haW hXW hh0, ?_⟩
  unfold ren
  rw [← th_subst_expK _ hXK hf0, hfe, ← MvPowerSeries.coe_substAlgHom haK, map_add (f := _), map_one,
    MvPowerSeries.coe_substAlgHom haK, MvPowerSeries.map_subst haW]
  simp only [MvPowerSeries.map_X]

theorem exp_neg_integral {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : E0 p f) :
    ∃ w : MvPowerSeries ι (WW p), expK (-f) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  refine ⟨MvPowerSeries.invOfUnit (1 + h) 1, ?_⟩
  have hinv : (1 + h) * MvPowerSeries.invOfUnit (1 + h) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by simp [hh0])
  have hneg : expK (-f) * expK f = 1 := by
    rw [← expK_add (by simp [hf0]) hf0, neg_add_cancel, th_expK_zero]
  calc expK (-f) = expK (-f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        ((1 + h) * MvPowerSeries.invOfUnit (1 + h) 1) := by rw [hinv, map_one, mul_one]
    _ = (expK (-f) * expK f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        (MvPowerSeries.invOfUnit (1 + h) 1) := by
      rw [hfe, map_mul, map_add (f := _), map_one]
      ring
    _ = _ := by rw [hneg, one_mul]

end Param

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def nc_Size (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  (∀ s, (al ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) s : ℝ) ≤ (2 * L.sc.a) ^ 2) ∧
  (∀ s, (lsz (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j s : ℝ) ≤ (2 * L.sc.a) ^ 4)

theorem nc_a_ge : (1 : ℝ) ≤ L.sc.a := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hL : 0 ≤ L.sc.L := by
    simp only [Formalism.BasicNotions.Scale.L]
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ L.sc.b := by
    simp only [Formalism.BasicNotions.Scale.b]
    exact Real.one_le_exp hL
  simp only [Formalism.BasicNotions.Scale.a]
  exact one_le_mul_of_one_le_of_one_le hx.le hb

theorem nc_de (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (hT : GatTies D)
    (hL : Formalism.MainNotions.G.LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D)
    (h1 : 9 ≤ K.dl1) (h2 : 9 ≤ K.dl2) (hlog : 1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a))
    (hS : nc_Size D L Y u w hg t0 j) : nc_De D L X Y K u w hg t0 j := by
  have hp : 2 ≤ D.what₂.places.resChar w := hg.1.two_le
  have hA : (1 : ℝ) ≤ 2 * L.sc.a := by have := nc_a_ge (L := L); linarith
  have hmt := (hL u w hg)
  have ht : (Y.Fl u w hg).t = D.R.t := hmt.2.1
  have hk := hT.gat_k u w hg
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold NN Ranks.N
    rw [ht]
    have : (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
      rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _
    exact_mod_cast this
  have hN0 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t (j - 1) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold NN Ranks.N
    rw [ht]
    have : (D.gat u w hg).P.m + 1 + (j - 1) * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
      rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    exact_mod_cast this
  have hde := nc_de_le (D.what₂.places.resChar w) (Y.Fl u w hg).t _ _ _ j hp (2 * L.sc.a) (D.R.N D.R.m : ℝ) hA hlog
    hN1 hN0 hS.1 hS.2
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hNv : (Formalism.MainNotions.G.Nv X (D.what₂.places.resChar w) t0 : ℝ) = ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card := by
    unfold Formalism.MainNotions.G.Nv
    rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj]
  have hnP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
    unfold Formalism.MainNotions.G.nP
    rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]
  unfold nc_De Formalism.MainNotions.G.dl Formalism.MainNotions.G.Nm
  rw [hNv, hnP]
  have hl0 : 0 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) := by linarith
  have hc1 : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) * (D.R.N D.R.m : ℝ) ^ 2 *
      Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) := by positivity
  have hc2 : (0 : ℝ) ≤ (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ) *
      Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) ^ 2 := by positivity
  nlinarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
