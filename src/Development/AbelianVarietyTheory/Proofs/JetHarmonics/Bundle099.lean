module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AdaptExists
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.FrameInvMulVecNegativeVector
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeFrobeniusOrbitsLabelAtSplitPrime
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslate
public import Mathlib.RingTheory.FormalGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFrame

open Formalism.FourierDecayAlt.P.SettingConstruction

section forms
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)

lemma quasi_reflection (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v)
    (hne : Formalism.QuantumDeterminants.herm H u u ≠ Formalism.QuantumDeterminants.herm H u v) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  set d := u - v with hd
  set s := Formalism.QuantumDeterminants.herm H u d with hs
  have hs' : s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H u v := by rw [hs, hd, herm_sub_right]
  have hs0 : s ≠ 0 := by rw [hs']; exact sub_ne_zero.mpr hne
  have hss : star s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H v u := by
    rw [hs, herm_symm H hH, hd, herm_sub_left]
  have hq : Formalism.QuantumDeterminants.herm H d d = s + star s := by
    rw [hss, hs', hd]
    simp only [herm_sub_left, herm_sub_right]
    linear_combination -huv
  set a : ℂ := s⁻¹ with ha'
  have ha : a * s = 1 := inv_mul_cancel₀ hs0
  have hsa : star a * star s = 1 := by rw [← star_mul', ha, star_one]
  refine ⟨rk H d 1 (-a), unitary_of_form H _ fun x y => ?_, ?_, fun x hxu hxv => ?_⟩
  · rw [rk_mulVec, rk_mulVec]
    have hY : star (Formalism.QuantumDeterminants.herm H y d) = Formalism.QuantumDeterminants.herm H d y := herm_symm H hH y d
    simp only [_root_.Formalism.FourierDecayAlt.P.SettingConstruction.herm_add_left,
      _root_.Formalism.FourierDecayAlt.P.SettingConstruction.herm_add_right,
      _root_.Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_left,
      _root_.Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_right, star_mul', hY, hq,
      star_neg, star_one]
    linear_combination (star a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * ha +
      (a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * hsa
  · rw [rk_mulVec, ← hs, neg_mul, ha, hd]
    simp
  · rw [rk_mulVec, hd, herm_sub_right, hxu, hxv]
    simp

lemma exists_isometry (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v) (h0 : Formalism.QuantumDeterminants.herm H u u ≠ 0) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  apply GlobalTheory.CompanionTheory.BmuAdapt.exists_move <;> assumption

end forms

open PI.UpqRep PI.HwUniqW

variable {k r : ℕ}

lemma herm_right_bvec (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.herm (Hpk k r) y (bvec i) = epsI k r i * y (piI k r i) := by
  rw [← Hpk_mulVec_apply]
  simp [Formalism.QuantumDeterminants.herm, bvec, Pi.star_single]

lemma herm_bvec_eq_zero {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec i) y = 0 := by
  rw [← herm_symm _ Hpk_conjTranspose, herm_right_bvec, hy (piI k r i), mul_zero, star_zero]
  rw [piI_val]
  have := i.isLt
  split_ifs <;> omega

lemma exists_isFrameW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ g, IsFrameW k r z g := by
  set T := Tz k r z with hTdef
  set u : Fin (2 * r + k + 1) → ℂ := ((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) with hu
  have hw : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) = -1 := by
    have hp : piI k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
      unfold piI; rw [if_pos (by simp [wI])]
    rw [herm_right_bvec, hp, bvec_apply, if_pos rfl]
    simp [epsI, wI]
  have huu : Formalism.QuantumDeterminants.herm (Hpk k r) u u = -(T : ℂ) := by
    rw [hu, herm_smul_left, herm_smul_right, hw]
    have h1 : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := Complex.conj_ofReal _
    have h2 : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
    rw [h1]
    linear_combination -h2
  have hzz : Formalism.QuantumDeterminants.herm (Hpk k r) z z = -(T : ℂ) := by
    have h1 : star (Formalism.QuantumDeterminants.herm (Hpk k r) z z) = Formalism.QuantumDeterminants.herm (Hpk k r) z z :=
      herm_symm _ Hpk_conjTranspose z z
    have h2 : T = -(Formalism.QuantumDeterminants.herm (Hpk k r) z z).re := rfl
    rw [h2, Complex.ofReal_neg, neg_neg]
    exact (Complex.conj_eq_iff_re.mp h1).symm
  have huW : inWb k r u := by
    intro i hi
    rw [hu, Pi.smul_apply, bvec_apply, if_neg, smul_zero]
    rintro rfl
    simp [wI] at hi
  obtain ⟨g, h1, h2, h3⟩ := exists_isometry (Hpk k r) Hpk_conjTranspose u z (huu.trans hzz.symm) (by
    rw [huu, neg_ne_zero]; exact_mod_cast hT.ne')
  refine ⟨g, h1, fun a => ⟨?_, ?_⟩, h2⟩
  · have ha : (eI k r a).val < r ∨ r + k < (eI k r a).val := Or.inl a.isLt
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)
  · have ha : (esI k r a).val < r ∨ r + k < (esI k r a).val := by
      have := a.isLt
      right; simp only [esI]; omega
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)

lemma blockW_fix (x : Matrix (Fin k) (Fin k) ℂ) {j : Fin (2 * r + k + 1)} (hj : ¬ InB k r j) :
    blockW k r x *ᵥ bvec j = bvec j := by
  funext i
  rw [mulVec_bvec_apply, bvec_apply]
  by_cases hi : InB k r i
  · rw [blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj)]
  · rw [blockW_out _ hi]

lemma blockW_mem_UH {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    blockW k r x ∈ UH (Hpk k r) := by
  show (blockW k r x)ᴴ * Hpk k r * blockW k r x = Hpk k r
  rw [blockW_conjTranspose, ← Hpk_blockW_comm, Matrix.mul_assoc, blockW_mul, mem_UJset_allPos.mp hx,
    blockW_one, Matrix.mul_one]

lemma conj_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    g * blockW k r x * g⁻¹ ∈ UWset k r z := by
  refine ⟨mul_mem_UH (mul_mem_UH hg.1 (blockW_mem_UH hx)) (inv_mem_UH hg.1), fun a => ⟨?_, ?_⟩, ?_⟩
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).1,
      blockW_fix x (by unfold InB eI; simp only; omega), (hg.2.1 a).1]
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).2,
      blockW_fix x (by unfold InB esI; simp only; omega), (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frame_inv_mulVec_negativeVector hg, Matrix.mulVec_smul,
      blockW_fix x (by unfold InB wI; simp), hg.2.2]

theorem frame_exists : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∃ g, PI.UpqRep.IsFrameW k r z g ∧ (∀ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), g * PI.UpqRep.blockW k r x * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧ ∀ y ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), y = g * PI.UpqRep.blockW k r x * g⁻¹ := by
  intro k r z hz hT
  have hT' : 0 < PI.UpqRep.Tz k r z := hT
  obtain ⟨g, hg⟩ := exists_isFrameW z hz hT'
  refine ⟨g, hg, fun x hx => conj_mem_UW hg hx, fun y hy => ?_⟩
  obtain ⟨x, hx, -, e⟩ := UW_eq_conj hT' hg hy
  exact ⟨x, hx, e⟩

end GlobalTheory.BesselFrame
end
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_addValuation_mul_log {C : Type} [Field C] (v : Valuation C NNReal) (r : ℝ) (hr : r < 0) :
    ∃ w : AddValuation C (WithTop ℝ), ∀ x, x ≠ 0 → w x = ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have hpos : ∀ x : C, x ≠ 0 → (0 : ℝ) < (v x : ℝ) := fun x hx => by
    have : v x ≠ 0 := by simpa using hx
    exact_mod_cast pos_iff_ne_zero.2 this
  have hmono : ∀ x y : C, x ≠ 0 → y ≠ 0 → v x ≤ v y →
      ((r * Real.log (v y : ℝ) : ℝ) : WithTop ℝ) ≤ ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ) := by
    intro x y hx hy h
    rw [WithTop.coe_le_coe]
    exact mul_le_mul_of_nonpos_left (Real.log_le_log (hpos x hx) (by exact_mod_cast h)) hr.le
  refine ⟨AddValuation.of (fun x => if x = 0 then ⊤ else ((r * Real.log (v x : ℝ) : ℝ) : WithTop ℝ))
    (by simp) (by simp) ?_ ?_, fun x hx => by simp [hx]⟩
  · intro x y
    by_cases hxy : x + y = 0
    · simp [hxy]
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp only [if_neg hx, if_neg hy, if_neg hxy]
    rcases le_max_iff.1 (v.map_add x y) with h | h
    · exact min_le_of_left_le (hmono _ _ hxy hx h)
    · exact min_le_of_right_le (hmono _ _ hxy hy h)
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp only [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [map_mul, NNReal.coe_mul, Real.log_mul (hpos x hx).ne' (hpos y hy).ne', mul_add, WithTop.coe_add]

theorem ValExt.exists_addValuation {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (e : ℕ) (he : 0 < e) :
    ∃ w : AddValuation X.C (WithTop ℝ),
      (∀ x : X.O, ((0 : ℝ) : WithTop ℝ) ≤ w (algebraMap X.O X.C x)) ∧
      (∀ x : T.Fr, nval T.V e x = (WithBot.some (w (X.ιF x)) : WithBot (WithTop ℝ))) ∧
      ∀ (x : X.C) (A : ℝ), (X.v (p : X.C) : ℝ) ^ A ≤ (X.v x : ℝ) →
        w x ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * A : ℝ) : WithTop ℝ) := by
  have hp0 : (p : X.C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpos : ∀ x : X.C, x ≠ 0 → (0 : ℝ) < (X.v x : ℝ) := fun x hx => by
    have : X.v x ≠ 0 := by simpa using hx
    exact_mod_cast pos_iff_ne_zero.2 this
  have hle : X.v (p : X.C) ≤ 1 := by
    have := X.ints.map_le_one (p : X.O)
    rwa [map_natCast] at this
  have hne : X.v (p : X.C) ≠ 1 := fun h =>
    X.nonunit.out (X.ints.isUnit_of_one' (by rwa [map_natCast]))
  have hlt : (X.v (p : X.C) : ℝ) < 1 := by exact_mod_cast lt_of_le_of_ne hle hne
  have hlog : Real.log (X.v (p : X.C) : ℝ) < 0 := Real.log_neg (hpos _ hp0) hlt
  have hpT : (p : T.Fr) ≠ 0 := fun h => hp0 (by rw [← map_natCast X.ιF, h, map_zero])
  have he0 : (0 : ℝ) < (vV T.V (p : T.Fr) : ℝ) := by
    have h1 : 0 ≤ vV T.V (p : T.Fr) := by
      have := GlobalTheory.vV_algebraMap_nonneg_dvr T (p : T.V)
      rwa [map_natCast] at this
    refine lt_of_le_of_ne (by exact_mod_cast h1) fun h => ?_
    have h2 := X.val _ hpT
    rw [← h, div_zero, Real.rpow_zero, map_natCast] at h2
    exact hlt.ne h2
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hc : 0 < (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) := div_pos he0 heR
  have hr : (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) / Real.log (X.v (p : X.C) : ℝ) < 0 := div_neg_of_pos_of_neg hc hlog
  obtain ⟨w, hw⟩ := exists_addValuation_mul_log X.v _ hr
  refine ⟨w, fun x => ?_, fun x => ?_, fun x A hA => ?_⟩
  · by_cases hx : algebraMap X.O X.C x = 0
    · rw [hx, AddValuation.map_zero]; exact le_top
    rw [hw _ hx, WithTop.coe_le_coe]
    exact mul_nonneg_of_nonpos_of_nonpos hr.le
      (Real.log_nonpos (hpos _ hx).le (by exact_mod_cast X.ints.map_le_one x))
  · by_cases hx : x = 0
    · rw [hx, nval_zero, map_zero, AddValuation.map_zero]; rfl
    rw [nval_of_ne hx, hw _ ((map_ne_zero X.ιF).2 hx), X.val x hx, Real.log_rpow (hpos _ hp0)]
    have : (vV T.V (p : T.Fr) : ℝ) / (e : ℝ) / Real.log (X.v (p : X.C) : ℝ) *
        ((vV T.V x : ℝ) / (vV T.V (p : T.Fr) : ℝ) * Real.log (X.v (p : X.C) : ℝ)) = (vV T.V x : ℝ) / e := by
      have := hlog.ne
      field_simp
    rw [this]; rfl
  · have hA0 : 0 < (X.v (p : X.C) : ℝ) ^ A := Real.rpow_pos_of_pos (hpos _ hp0) A
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hA
      exact absurd (hA0.trans_le hA) (by simp)
    rw [hw _ hx, WithTop.coe_le_coe]
    have h1 := Real.log_le_log hA0 hA
    rw [Real.log_rpow (hpos _ hp0)] at h1
    refine (mul_le_mul_of_nonpos_left h1 hr.le).trans (le_of_eq ?_)
    have := hlog.ne
    field_simp

theorem nuLocC_le_of_value_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (B : FB X.O (chD Ch.ch) (𝓞 E)), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) → (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → ∀ (P : MvPolynomial (LtN Dw n) X.O), MvPolynomial.map (algebraMap X.O X.C) P ∈ HHa Dw.mult n X.C ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (f : PS X.O n (chD Ch.ch)) (A : ℝ), (X.v (p : X.C) : ℝ) ^ A ≤ (X.v (nabValN B X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k (MvPowerSeries.map (algebraMap X.O X.C) f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap X.O X.C (X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ i))) (MvPolynomial.map (algebraMap X.O X.C) P)) : ℝ) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * A : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X B hF hA e k n a he P hP f A hv
  letI := io.toAlgebra
  obtain ⟨w, hO, hT, hw⟩ := X.exists_addValuation e he
  have hh : MvPowerSeries.constantCoeff Ch.ch.h = 0 :=
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ Ch.ch.gauge.ax0 0 fun _ => rfl
  have hcomp : X.ιF.comp (algebraMap T.V T.Fr) = (algebraMap X.O X.C).comp X.ι := RingHom.ext X.comp
  have hmm : ∀ {m : ℕ} (g : PS T.V m (chD Ch.ch)),
      MvPowerSeries.map (algebraMap X.O X.C) (MvPowerSeries.map X.ι g) =
        MvPowerSeries.map X.ιF (MvPowerSeries.map (algebraMap T.V T.Fr) g) := fun g => by
    ext μ
    simp only [MvPowerSeries.coeff_map, X.comp]
  let R : Subring X.C :=
    { carrier := {x | ((0 : ℝ) : WithTop ℝ) ≤ w x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, WithTop.coe_zero] at *
        rw [w.map_mul]; exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => w.map_le_add ha hb
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rwa [w.map_neg] }
  have key := GlobalTheory.nabValN_lower_bound_baseChange T X.C w X.ιF R (fun x => Iff.rfl)
    (fun x => by rw [X.comp]; exact hO _) _ (𝓞 E) Ch.ch.B (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B)
    (fun i => by
      rw [Ch.gen.1.1 i, ← hmm]
      change MvPowerSeries.map _ (B.G.F i) = _
      rw [hF])
    (fun b i => by
      rw [Ch.gen.1.2.1 b i, ← hmm]
      change MvPowerSeries.map _ (B.A.act b i) = _
      rw [hA])
    Ch.ch.h hh H.w0 k (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
    (fun ℓ => ℓ.2.2) (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (nuLocC Ch e k a n)
    (by
      intro Q hQ g hg
      rw [← hT]
      unfold nuLocC
      exact iInf_le_of_le Q (iInf_le_of_le hQ (iInf_le_of_le g (iInf_le_of_le hg le_rfl))))
    (MvPolynomial.map (algebraMap X.O X.C) P)
    ⟨hP, fun m => by rw [MvPolynomial.coeff_map]; exact hO _⟩
    (MvPowerSeries.map (algebraMap X.O X.C) f)
    (fun μ => by rw [MvPowerSeries.coeff_map]; exact hO _)
  refine key.trans (WithBot.coe_le_coe.2 (le_trans (le_of_eq (congrArg w ?_)) (hw _ A hv)))
  have hu : (fun (ℓ : LtN Dw n) j => X.ιF (Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j)) =
      fun (ℓ : LtN Dw n) i => algebraMap X.O X.C (X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ i)) := by
    funext ℓ j
    rw [Ch.gen.1.2.2.2.2.2.2, X.comp]
  have h1 : (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B).FK X.C = B.FK X.C := by
    funext i
    ext μ
    simp [FB.FK, FGLaw.mapF, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapLaw, GlobalTheory.FBMap.mapPt]
  have h2 : ∀ b, (GlobalTheory.FBMap.mapFB (algebraMap X.O X.C) B).actK X.C b = B.actK X.C b := by
    intro b
    funext i
    ext μ
    simp [FB.actK, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapAct, GlobalTheory.FBMap.mapPt]
  rw [hu]
  unfold nabValN FB.hL
  rw [h1, h2]

end GlobalTheory.CharDepth
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonempty_closedValuedExtensionOfCDVR : ∀ (T : CDVR) (p : ℕ) [Fact p.Prime], ¬ IsUnit (p : T.V) → Nonempty (ValExt T p) := by
  first | exact @GlobalTheory.CharDepth.nonempty_valExt | exact GlobalTheory.CharDepth.nonempty_valExt | (intros; apply GlobalTheory.CharDepth.nonempty_valExt <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.cmType_frobenius_orbits_label_at_split_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → N.cls V.l = PrimeClass.splitK → ∀ j : ℕ, ∃ (d : ℕ) (_ : NeZero d) (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)), RF.IsReps (parAt N j d pos) Z ∧ Z.Nonempty ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod d => tauSp N pl pos x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauSp (d := d) N pl pos z g) := by
  first | exact @GlobalTheory.LabSplit.labelling_split | exact GlobalTheory.LabSplit.labelling_split | (intros; apply GlobalTheory.LabSplit.labelling_split <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  first | exact @GlobalTheory.MomOne.Transfer.shift_eq_hat_translate | exact GlobalTheory.MomOne.Transfer.shift_eq_hat_translate | (intros; apply GlobalTheory.MomOne.Transfer.shift_eq_hat_translate <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

private theorem norm_zc_eq {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  exact (PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm

private theorem zc_natCast_eq {q : ℕ} [Fact q.Prime] (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by
  simp [zc]

theorem height_one_of_split : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (F : FormalGroup 𝓞_ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) → ∃ ℓ : ℂ_[q]⟦X⟧, constantCoeff ℓ = 0 ∧ PowerSeries.subst ℓ (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = X ∧ ‖coeff q (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ = 1 ∧ ∀ k < q, ‖coeff k (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ < 1 := by
  intro d q _ M F hd hd16 hs hOK hM hF
  set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef
  have flow := uw_elliptic_flow q M hM
  have hU0 : constantCoeff U = 0 := by
    rw [hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [flow.2.2.2.2.1]

  obtain ⟨ℓ, hchart, hℓX⟩ := Basic.exists_chart M hM
  have hℓ0 : constantCoeff ℓ = 0 := hchart.2.1
  have hUℓ : U.subst ℓ = X := hℓX
  obtain ⟨P1, P2, P3⟩ := GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder q F U ℓ hU0 hℓ0 hUℓ hF
  refine ⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩
  ·

    have hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1 := by
      have := P1 (q : ℤ_[q])
      rw [zc_natCast_eq] at this
      exact this q
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have P3' := P3 hlt
    set k : ℕ := d + 3 with hk
    obtain ⟨β, N, hβ, hβ0, hβn, hN, hNle⟩ := exists_small_in_prime_pow d q M.ι hd hd16 hs k
    have ar := okArith d q M.ι hd hd16 hs
    obtain ⟨a, ha⟩ := (ar.2.1 β hβ).1
    have hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
      rw [← norm_zc_eq, ← ha]
      exact hβn
    have hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice := by
      intro l hl
      rw [hOK] at hl ⊢
      exact (ar.1.2.2 β l hβ hl).2.1
    have hu0 : AnalyticAt ℂ M.u 0 := (flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1
    have hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ) := by
      rw [(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]
      rfl
    have hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) := by
      rw [hhat]
      exact P1 a
    obtain ⟨n, hnN, hn1⟩ := GlobalTheory.T.exists_unit_coeff_mul_series_le_norm q M ℓ β N hchart hβ0 hlat hN hbd
    have hnlt : n < (2 * q) ^ k := by
      have hq : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
      have h2 : d + 3 < 2 ^ k := Nat.lt_two_pow_self
      calc n ≤ N := hnN
        _ ≤ (d + 3) * q ^ k := hNle
        _ < 2 ^ k * q ^ k := Nat.mul_lt_mul_of_pos_right h2 hq
        _ = (2 * q) ^ k := (mul_pow 2 q k).symm
    have := P3' k a hanorm n hnlt
    rw [← hhat, hn1] at this
    exact lt_irrefl _ this
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0 := by simp [hℓ0]
      rw [coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]
      exact one_pos
    · exact P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)

end GlobalTheory.MomOne
end
