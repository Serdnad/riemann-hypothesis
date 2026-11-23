module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle043
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConjDiEqSelf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle046
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle034

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

theorem cj_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) :
    cj k r κ τ h = h := by
  ext i j
  rw [cj_apply]
  by_cases h0 : h i j = 0
  · rw [h0, mul_zero]
  · have e := fix_gen (fun i => ((tV k r κ τ i : ℝ) : ℂ)) 1 (fun i h1 h2 => by simp [tV_wb i h1 h2]) hh.1 hh.2.1 i j h0
    have e' : tV k r κ τ i = tV k r κ τ j := by exact_mod_cast e
    rw [e', inv_mul_cancel₀ (tV_pos hκ hτ j).ne']
    simp

theorem map_cjT_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)}
    (h : IsHaarOn (UWset k r z) μ) : μ.map (cjT k r κ τ) = μ := by
  have hae : cjT k r κ τ =ᵐ[μ] id := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) h.2.2.1
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro hU
    apply hx
    funext i j
    show cj k r κ τ (Matrix.of x) i j = x i j
    rw [cj_UW hκ hτ hU]; rfl
  rw [Measure.map_congr hae, Measure.map_id]

theorem haarProb_unique {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn (UWset k r z) μ) (hμ1 : μ Set.univ = 1) (hν : IsHaarOn (UWset k r z) ν) (hν1 : ν Set.univ = 1) :
    μ = ν := by
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  have hC := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hK := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT
  have fin : ∀ (m : Measure (Mt k r)), m Set.univ = 1 → ∀ K : Set (Mt k r), IsCompact K → m K < ⊤ :=
    fun m hm K _ => (measure_mono (Set.subset_univ K)).trans_lt (by rw [hm]; exact ENNReal.one_lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 μ hC h0 hμ.2.2.1 hμ.2.2.2 (fin μ hμ1)
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 ν hC h0 hν.2.2.1 hν.2.2.2 (fin ν hν1)
  have hfin : μ0 Set.univ ≠ ⊤ := by
    have hle := measure_univ_le_add_compl (μ := μ0) (UWset k r z : Set (Mt k r))
    have hc0 : μ0 (UWset k r z : Set (Mt k r))ᶜ < ⊤ := (le_of_eq h0.conc).trans_lt ENNReal.zero_lt_top
    exact (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨h0.finite_compact _ hK, hc0⟩)).ne
  have hne : μ0 Set.univ ≠ 0 := by
    intro h; apply h0.ne_zero; rw [← Measure.measure_univ_eq_zero]; exact h
  have e1 : (c : ENNReal) * μ0 Set.univ = 1 := by rw [← hμ1, hc]; rfl
  have e2 : (d : ENNReal) * μ0 Set.univ = 1 := by rw [← hν1, hd]; rfl
  have hcd : (c : ENNReal) = d := by
    have := e1.trans e2.symm
    exact (ENNReal.mul_left_inj hne hfin).mp this
  rw [hc, hd, ENNReal.coe_injective hcd]

section Choice

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem muWc_eq (u : D.what₂.Word) (τ : D.what₂.Tau) (hz : inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ))
    (hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1) := by
  rw [map_cjT_UW (inv_pos.mpr (kaB_pos D)) one_pos (C.muW_haar u τ)]
  show (μW_exists X C u (vOf X τ)).choose = _
  obtain ⟨h1, h2⟩ := (μW_exists X C u (vOf X τ)).choose_spec
  generalize (μW_exists X C u (vOf X τ)).choose = m at h1 h2 ⊢
  have hS : UWset D.R.k D.R.rS (zc X C u (vOf X τ)) = UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [zc_vOf_eq_zB_of_inWb C u u τ hz, UWset_smul one_pos]
  rw [hS] at h1
  exact haarProb_unique hz hT h1 h2 (C.muW_haar u τ) (C.muW_one u τ)

end Choice

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.AmpWin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

def kap (τ : D.what₂.Tau) : ℝ := Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ)

def AmpWinP : Prop :=
  (∏ τ, kap u u' C hB τ) * c0X X u (Y.FN u) * c0X X u' (Y.FN u') =
    X.volK2 ^ 2 * (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u')

def MassU : Prop :=
  (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal =
    Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * ∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal

end Defs

section Lemmas

variable {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hB : WuBessel C)

theorem cOf_pos {u : D.what₂.Word} {τ : D.what₂.Tau} (h0 : l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0)
    (ht : l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤) : 0 < cOf hB u τ := by
  have hl : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos h0 ht.ne
  have hd : 0 < Module.finrank ℂ (X.Vloc u (vOf X τ)) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ (X.Vloc u (vOf X τ))) with h | h
    · exfalso
      have : Subsingleton (X.Vloc u (vOf X τ)) := Module.finrank_zero_iff.1 h
      apply h0
      unfold l2SG
      simp [Subsingleton.elim (phiOf hB u τ _) 0]
    · exact h
  unfold cOf
  exact div_pos hl (by exact_mod_cast hd)

theorem kap_eq {u u' : D.what₂.Word} {τ : D.what₂.Tau} (hc : 0 < cOf hB u τ) (hc' : 0 < cOf hB u' τ) :
    kap u u' C hB τ = 1 / (cOf hB u τ * cOf hB u' τ) := by
  unfold kap Formalism.L2.SG.Pf.LocNorm.aT sclOf
  have hb : cOf hB u' τ = (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal / ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) := rfl
  have hd0 : (0 : ℝ) ≤ ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hb] at hc' ⊢
  generalize cOf hB u τ = a at hc ⊢
  generalize (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal = L at hc' ⊢
  generalize ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℕ) : ℝ) = d at hd0 hc' ⊢
  have hd : 0 < d := lt_of_le_of_ne hd0 (fun h => by rw [← h, div_zero] at hc'; exact lt_irrefl _ hc')
  have hL : 0 < L := by
    have h1 := mul_pos hc' hd
    rwa [div_mul_cancel₀ _ hd.ne'] at h1
  have hx : 0 ≤ a * d / L := div_nonneg (mul_nonneg hc.le hd.le) hL.le
  first
    | (rw [Complex.normSq_mul, Complex.normSq_ofReal, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp; ring)
    | (simp only [Complex.normSq_mul, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp; ring)
    | (rw [Complex.normSq_mul, Complex.normSq_ofReal, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hx]; field_simp)

theorem finrank_tau (u : D.what₂.Word) :
    (Module.finrank ℂ (X.Vpi u) : ℝ) = ∏ τ, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact (Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl).symm

end Lemmas

section Main

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C)

theorem poincareConstant_of_mass (hM : MassU Y u C hB) :
    c0X X u (Y.FN u) = X.volK2 * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * ∏ τ, cOf hB u τ := by
  unfold c0X
  unfold MassU at hM
  rw [mul_assoc X.volK2, hM, finrank_tau u]
  have hP : ∏ τ, cOf hB u τ = (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) / ∏ τ, ((Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℕ) : ℝ) := by
    rw [← Finset.prod_div_distrib]
    rfl
  rw [hP]
  ring

theorem ampWin_of (hM : MassU Y u C hB) (hM' : MassU Y u' C hB)
    (hl : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤)
    (hl' : ∀ τ, l2SG (C.nuS u' τ) (phiOf hB u' τ) ≠ 0 ∧ l2SG (C.nuS u' τ) (phiOf hB u' τ) < ⊤) :
    AmpWinP Y u u' C hB := by
  unfold AmpWinP
  have hc : ∀ τ, 0 < cOf hB u τ := fun τ => cOf_pos hB (hl τ).1 (hl τ).2
  have hc' : ∀ τ, 0 < cOf hB u' τ := fun τ => cOf_pos hB (hl' τ).1 (hl' τ).2
  have hk : ∀ τ, kap u u' C hB τ = 1 / (cOf hB u τ * cOf hB u' τ) := fun τ => kap_eq hB (hc τ) (hc' τ)
  have hP : (∏ τ, kap u u' C hB τ) * (∏ τ, cOf hB u τ) * (∏ τ, cOf hB u' τ) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    have h1 := (hc τ).ne'
    have h2 := (hc' τ).ne'
    rw [hk τ]
    field_simp
  rw [poincareConstant_of_mass _ _ _ _ hM, poincareConstant_of_mass _ _ _ _ hM']
  linear_combination (X.volK2 ^ 2 * (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u')) * hP

theorem poincareConstant_nonneg (w : D.what₂.Word) : 0 ≤ c0X X w (Y.FN w) := by
  unfold c0X
  first
    | positivity
    | (have := X.levelVolume_pos; positivity)
    | (have := X.volK2_nonneg; positivity)
    | (unfold HidaSetting.volK2; positivity)
    | (unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2; done)

theorem K0_eq_covN_of_ampWin (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2) :
    Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB =
      Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u' := by
  have ha := poincareConstant_nonneg Y u
  have hb := poincareConstant_nonneg Y u'
  unfold Formalism.L2.SG.Pf.LocNorm.K0 Formalism.L2.SG.Pf.OOCore3.sclV TermOp.scl
  unfold AmpWinP at hA
  have hkap : ∀ τ, kap u u' C hB τ = Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ) := fun τ => rfl
  simp only [hkap] at hA
  generalize (∏ τ, Complex.normSq (Formalism.L2.SG.Pf.LocNorm.aT u u' C hB τ)) = P at hA ⊢
  generalize c0X X u (Y.FN u) = a at ha hA ⊢
  generalize c0X X u' (Y.FN u') = b at hb hA ⊢
  generalize Formalism.L2.SG.LoopTerm.covN (Y := Y) C u = m at hA ⊢
  generalize Formalism.L2.SG.LoopTerm.covN (Y := Y) C u' = m' at hA ⊢
  generalize X.volK2 = V at hA hV ⊢
  clear hkap
  rw [Complex.normSq_ofReal]
  rcases (mul_nonneg ha hb).eq_or_lt with h0 | h0
  · rw [← h0, Real.sqrt_zero, inv_zero, zero_mul, mul_zero, div_zero]
    have h1 : V ^ 2 * (m * m') = 0 := by rw [← hA, mul_assoc, ← h0, mul_zero]
    exact ((mul_eq_zero.mp h1).resolve_left (pow_pos hV 2).ne').symm
  · have hs : (√(a * b)) ^ 2 = a * b := Real.sq_sqrt h0.le
    have hs0 : √(a * b) ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
    have hden : (√(a * b))⁻¹ * V * ((√(a * b))⁻¹ * V) = V ^ 2 / (a * b) := by
      first
        | rw [inv_mul_eq_div, div_mul_div_comm, ← sq, ← sq, hs]
        | (field_simp; rw [hs]; ring)
        | (field_simp; rw [Real.mul_self_sqrt h0.le]; ring)
    rw [hden, div_div_eq_mul_div, div_eq_iff (pow_pos hV 2).ne']
    linarith [hA]

theorem minWeight_pos (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2)
    (hc : 0 < Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') :
    0 < Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB := by
  rw [K0_eq_covN_of_ampWin Y u u' C hB hA hV]
  exact hc

theorem K0_mem_covWin_of_ampWin (hA : AmpWinP Y u u' C hB) (hV : 0 < X.volK2) {large₂} {C1 : ℝ}
    (hW : Formalism.L2.SG.LoopTerm.CovWinN (Y := Y) C large₂ C1 u u') :
    Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB) := by
  rw [K0_eq_covN_of_ampWin Y u u' C hB hA hV]
  first
    | exact hW
    | (unfold Formalism.L2.SG.LoopTerm.CovWinN at hW; exact hW)
    | (unfold Formalism.L2.SG.LoopTerm.CovWinN at hW; done)

end Main

end Formalism.L2.SG.Pf.AmpWin
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.Pf.OOCore3 Formalism.L2.SG.Pf.LocNorm
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AmplitudeBoundsAllChoices {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ θ : ℝ, 0 < θ ∧ normWin D large₂ C1 θ ∧ ∀ (C : Choice X θ) (hB : WuBessel C),
    (∃ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl ∧ LocUniqP u u' C hB νl) ∧
    0 < K0 Y u u' C hB ∧ WinK large₂ C1 (K0 Y u u' C hB) ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

def AmplitudeBoundsAllChoicesUniform : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → AmplitudeBoundsAllChoices large₂ Y u u' ν C1 Cn Ire

end Formalism.L2.SG.Pf.ThmBChain6
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx
  Formalism.L2.SG.Pf.AllRowsKpp

variable {D : D7} (X : HidaSetting D)

theorem fr_L (ob : Bool) (j : Fin D.R.r) : fr X ob j ∈ X.B.I.Lf := by
  rcases kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩
  · rw [frame_isotropic]; exact (X.vectorsInLattice.1 a).1
  · cases ob
    · rw [fr_wf]; exact (X.vectorsInLattice.2.2 _).2
    · rw [fr_wt]; exact (X.vectorsInLattice.2.2 _).1
  · rw [frame_anisotropic]; exact X.vectorsInLattice.2.1
  · rw [fr_y]; exact (X.vectorsInLattice.1 _).2

theorem frd_L (ob : Bool) (j : Fin D.R.r) : frd X ob j ∈ X.B.I.Lf := by
  rcases kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩
  · rw [dual_frame_isotropic]; exact (X.vectorsInLattice.1 a).2
  · cases ob
    · rw [frd_wf]; exact (X.vectorsInLattice.2.2 _).1
    · rw [frd_wt]; exact (X.vectorsInLattice.2.2 _).2
  · rw [dual_frame_anisotropic]; exact neg_mem X.vectorsInLattice.2.1
  · rw [frd_y]; exact (X.vectorsInLattice.1 _).1

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)} {p : ℕ}

theorem col (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w)
    {x : X.B.I.Gf} (hx : x ∈ X.K2) (i j : Fin D.R.r)
    (hij : j.1 ≤ i.1 ∨ ((∃ l, i = wI (hrD D) l) ∧ j = zI (hrD D))) :
    CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (if i = j then 1 else 0) := by
  have hc : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := hx.2
  have hci : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x⁻¹ := ((Formalism.L2.SG.Pf.level_subgroup_character_unitary X).2.2.1 x hx).2
  have hgr := gram X ob hg hew hsew
  rcases kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨l, rfl⟩ | rfl | ⟨b, rfl⟩
  ·
    have hpos : b.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    refine cong_dir hg (frd_L X ob) hgr i (xI (hrD D) b) (S := X.e0 '' {c | c.1 < b.1}) ?_ ?_
    · rintro s ⟨c, hc', rfl⟩
      exact ⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp [xI, wI, yI, zI] at hc' ⊢; omega)⟩
    · rw [frame_isotropic]; exact hc.1 b
  ·
    have hpos : D.R.rS + l.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    ·
      rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩
      · exfalso; simp [xI, wI, yI, zI] at hpos; omega
      · simp [xI, wI, yI, zI] at hpos
        refine cong_dual hg (fr_L X false) hgr (wI (hrD D) l') (wI (hrD D) l)
          (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < (rv l').1}) ?_ ?_
        · rintro s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)
          · exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
          · exact ⟨wI (hrD D) (rv c), by rw [frd_wf, rv_rv], ne_val (by simp [xI, wI, yI, zI, rv] at hc' ⊢; omega)⟩
        · rw [frd_wf]; exact hci.2.2 (rv l')
      · refine cong_dual hg (fr_L X false) hgr (zI (hrD D)) (wI (hrD D) l) (S := Set.range X.e0) ?_ ?_
        · rintro s ⟨c, rfl⟩
          exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
        · rw [dual_frame_anisotropic, Matrix.mulVec_neg]; exact inMod_neg hci.2.1
      · refine cong_dual hg (fr_L X false) hgr (yI (hrD D) a) (wI (hrD D) l)
          (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_
        · rintro s ⟨c, -, rfl⟩
          exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
        · rw [frd_y]; exact hci.1 (rv a)
    ·
      refine cong_dir hg (frd_L X true) hgr i (wI (hrD D) l) (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < l.1}) ?_ ?_
      · rintro s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)
        · exact ⟨xI (hrD D) c, (frame_isotropic X true c).symm, ne_val (by simp [xI, wI, yI, zI]; omega)⟩
        · exact ⟨wI (hrD D) c, (fr_wt X c).symm, ne_val (by simp [xI, wI, yI, zI] at hc' ⊢; omega)⟩
      · rw [fr_wt]; exact hc.2.2 l
  ·
    have hpos : D.R.rS ≤ i.1 := by
      rcases hij with h | ⟨⟨l, rfl⟩, -⟩
      · simp [xI, wI, yI, zI] at h; omega
      · simp [xI, wI, yI, zI]
    refine cong_dir hg (frd_L X ob) hgr i (zI (hrD D)) (S := Set.range X.e0) ?_ ?_
    · rintro s ⟨c, rfl⟩
      exact ⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp [xI, wI, yI, zI]; omega)⟩
    · rw [frame_anisotropic]; exact hc.2.1
  ·
    have hpos : D.R.rS + D.R.k + 1 + b.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · simp [xI, wI, yI, zI] at hpos
      refine cong_dual hg (fr_L X ob) hgr (yI (hrD D) a) (yI (hrD D) b)
        (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_
      · rintro s ⟨c, hc', rfl⟩
        exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI, rv] at hc' ⊢; omega)⟩
      · rw [frd_y]; exact hci.1 (rv a)

theorem shape (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w)
    (hp : p.Prime) (hcard : Nat.card (𝓞 X.B.I.E ⧸ w.asIdeal) = p) (hn : 0 < X.B.I.n)
    {x : X.B.I.Gf} (hx : x ∈ X.K2) {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (N i j)) :
    JPred D.R.k D.R.rS N := by
  refine jPred_of (hrD D) (fun a b hba => ?_) (fun a => ?_) (fun l => ?_)
  · have h := col (p := p) X ob hg hew hsew hx a b (Or.inl (le_of_lt hba))
    rw [if_neg (fun h' => (ne_of_gt hba) h')] at h
    exact congW_unique hp hcard hn (hN a b) h
  · have h := col (p := p) X ob hg hew hsew hx a a (Or.inl le_rfl)
    rw [if_pos rfl] at h
    exact congW_unique hp hcard hn (hN a a) h
  · have h := col (p := p) X ob hg hew hsew hx (wI (hrD D) l) (zI (hrD D)) (Or.inr ⟨⟨l, rfl⟩, rfl⟩)
    rw [if_neg (ne_val (by simp [xI, wI, yI, zI] <;> omega))] at h
    exact congW_unique hp hcard hn (hN _ _) h

end Formalism.L2.SG.Pf.KppLoc
end
end
