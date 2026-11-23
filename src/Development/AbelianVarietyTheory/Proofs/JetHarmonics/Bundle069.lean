module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableMmRight
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle065
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormFormalGroupHeightOneTorsionTower
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle076
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.NilpotentSubgroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.DropLevelBounds.ThBounds
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Formalism.LocalToGlobal.Divisibility.Numbers
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.QuotRightInv

open PI

theorem measurable_mul_left {m : ℕ} (x : MtM m) :
    Measurable (fun s : MtM m => (fun i j => (Matrix.of s * Matrix.of x) i j : MtM m)) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurable_rmulQ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : Measurable (rmulQ g) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rmulQ, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurableSet_not_mem {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    MeasurableSet {x : MtM m | Matrix.of x ∉ G} := by
  have hc : IsClosed {x : MtM m | Matrix.of x ∈ G} := by
    have hof : Continuous (fun x : MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
    exact hG.1.preimage hof
  exact hc.measurableSet.compl

private lemma mul_not_mem_of_mem_of_not_mem {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G)
    (hSG : S ⊆ G) {s x : Matrix (Fin m) (Fin m) ℂ} (hs : s ∈ S) (hx : x ∉ G) : s * x ∉ G := by
  intro hsx
  apply hx
  obtain ⟨hinv, hone⟩ := hG.2.2.2 s (hSG hs)
  have hleft : s⁻¹ * s = 1 := mul_eq_one_comm.mp hone
  have h1 := hG.2.2.1 _ hinv _ hsx
  rwa [← Matrix.mul_assoc, hleft, Matrix.one_mul] at h1

private lemma continuous_mul_swap_pair {m : ℕ} :
    Continuous (fun p : MtM m × MtM m => (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : MtM m)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem ae_mem_of_quot {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
    (h : QuotientSetting G S μG μS ν) : ∀ᵐ x ∂ν, Matrix.of x ∈ G := by
  apply PI.QuotInvW.ae_mem_G <;> assumption

theorem lintegral_eq_cutoff {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
    (h : QuotientSetting G S μG μS ν) (φ : MtM m → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∀ x : MtM m, Matrix.of x ∈ G →
      ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1)
    (F : MtM m → ℝ≥0∞) (hF : Measurable F)
    (hFS : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  have hνG := ae_mem_of_quot h
  obtain ⟨hG, hS, hSG, hHG, hHS, hRG, hRS, hQ⟩ := h
  rw [hQ (fun x => φ x * F x) (hφ.mul hF)]
  refine lintegral_congr_ae ?_
  filter_upwards [hνG] with x hx
  have hSae : ∀ᵐ s ∂μS, Matrix.of s ∈ S := ae_iff.mpr hHS.2.2.1
  have e : ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) *
        F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS
      = ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) * F x ∂μS := by
    refine lintegral_congr_ae ?_
    filter_upwards [hSae] with s hs
    rw [hFS _ hs x hx]
  rw [e, lintegral_mul_const (f := fun s : MtM m => φ (fun i j => (Matrix.of s * Matrix.of x) i j)) _
    (hφ.comp (measurable_mul_left x)), hφ1 x hx, one_mul]

theorem quotInv : PI.QuotInv := by
  intro m G S μG μS ν h F hF hFS g hg
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_normalised_cutoff' m G S μS h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1
  have hG : IsMatGroup G := h.1
  have hxg : ∀ x : MtM m, Matrix.of x ∈ G →
      Matrix.of (fun i j => (Matrix.of x * g) i j : MtM m) ∈ G := fun x hx => hG.2.2.1 _ hx _ hg
  have hφ' : Measurable (fun x : MtM m => φ (fun i j => (Matrix.of x * g) i j)) :=
    hφ.comp (measurable_rmulQ g)
  have hφ'1 : ∀ x : MtM m, Matrix.of x ∈ G →
      ∫⁻ s, (fun x : MtM m => φ (fun i j => (Matrix.of x * g) i j))
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
    intro x hx
    rw [← hφ1 _ (hxg x hx)]
    refine lintegral_congr fun s => ?_
    show φ _ = φ _
    congr 1
    change (Matrix.of s * Matrix.of x) * g = Matrix.of s * (Matrix.of x * g)
    exact Matrix.mul_assoc _ _ _
  have hFg : Measurable (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) :=
    hF.comp (measurable_rmulQ g)
  have hFgS : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G →
      (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) (fun i j => (s * Matrix.of x) i j) =
        (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) x := by
    intro s hs x hx
    have key := hFS s hs _ (hxg x hx)
    refine Eq.trans ?_ key
    show F _ = F _
    congr 1
    change (s * Matrix.of x) * g = s * (Matrix.of x * g)
    exact Matrix.mul_assoc _ _ _
  have e1 := lintegral_eq_cutoff h _ hφ' hφ'1 _ hFg hFgS
  have e2 := lintegral_eq_cutoff h φ hφ hφ1 F hF hFS
  refine e1.trans (Eq.trans ?_ e2.symm)
  calc ∫⁻ x, φ (fun i j => (Matrix.of x * g) i j) * F (fun i j => (Matrix.of x * g) i j) ∂μG
      = ∫⁻ x, (fun y => φ y * F y) (rmulQ g x) ∂μG := rfl
    _ = ∫⁻ x, (fun y => φ y * F y) x ∂(μG.map (rmulQ g)) :=
        (lintegral_map (hφ.mul hF) (measurable_rmulQ g)).symm
    _ = ∫⁻ x, φ x * F x ∂μG := by rw [h.2.2.2.2.2.1 g hg]

end GlobalTheory.QuotRightInv
end

section

set_option autoImplicit false

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GoodDepth

theorem ramOverZ_ne_zero' {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ramOverZ la ≠ 0 := by
  apply Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.ramOverZ_ne_zero <;> assumption

theorem ereal_le_mul_of_forall_le {x : EReal} {e B : ℝ} (he : 0 < e)
    (h : ∀ ν : ℝ, ((e * ν : ℝ) : EReal) ≤ x → ν ≤ B) : x ≤ ((e * B : ℝ) : EReal) := by
  by_contra hx
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  have h1 : r / e ≤ B := h (r / e) (by rw [mul_div_cancel₀ _ he.ne']; exact hr2.le)
  have h2 : e * B < r := by exact_mod_cast hr1
  rw [div_le_iff₀ he] at h1
  linarith [mul_comm e B]

theorem nuW_bound_of_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], IntChartEx Xo c →
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (B : ℝ), 0 ≤ B →
  (∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → ∀ (C : IntChart T io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e k a n → ν ≤ B) →
  nuW Xo c la k a n ≠ ⊤ ∧ (nuW Xo c la k a n).toReal / (ramOverZ la : ℝ) ≤ B ∧ (B = 0 → nuW Xo c la k a n = 0) := by
  intro E _ _ _ H Dw lv Xo c _ hEx la k a n B hB h
  have he : (0 : ℝ) < (ramOverZ la : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (ramOverZ_ne_zero' la)
  have hsup : nuSup Xo c la k a n ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal) := by
    unfold nuSup
    refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun hO => iSup_le fun y =>
      iSup_le fun hy => ?_
    obtain ⟨C⟩ := hEx T io y hy
    exact (iInf_le (fun C : IntChart T io y => nuLocC C e k a n) C).trans
      (ereal_le_mul_of_forall_le he (h T io e hO y hy C))
  have h0 : (0 : ℝ) ≤ (ramOverZ la : ℝ) * B := mul_nonneg he.le hB
  have hW : nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal) :=
    max_le (by exact_mod_cast h0) hsup
  have hW0 : 0 ≤ nuW Xo c la k a n := le_max_left _ _
  refine ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hW, ?_, fun hB0 => ?_⟩
  · rw [div_le_iff₀ he, mul_comm]
    have := EReal.toReal_le_toReal hW (ne_bot_of_le_ne_bot EReal.zero_ne_bot hW0) (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  · rw [hB0, mul_zero, EReal.coe_zero] at hW
    exact le_antisymm hW hW0

end GlobalTheory.GoodDepth
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.norm_formalGroup_heightOne_torsion_tower : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ‖t 1‖ ^ (p - 1) = ‖(p : K)‖ ∧ ‖(p : K)‖ < 1 ∧ (∀ n j, ¬ p ^ n ∣ j → ‖t 1‖ ≤ ‖ev1 (nMul F j) (t n)‖) ∧ ∀ n, ∏ j ∈ Finset.Ico 1 (p ^ n), ‖ev1 (nMul F j) (t n)‖ = ‖(p : K)‖ ^ n := by
  first | exact @GlobalTheory.ConvSer.TowerNorm.tower_norm | exact GlobalTheory.ConvSer.TowerNorm.tower_norm | (intros; apply GlobalTheory.ConvSer.TowerNorm.tower_norm <;> assumption)
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_integral_polynomial_torsion_character_level : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ∀ (n : ℕ) (ζ : K), ζ ^ (p ^ n) = 1 → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ j : ℕ, g.eval (ev1 (nMul F j) (t n)) = ζ ^ j := by
  first | exact @GlobalTheory.ConvSer.exists_intg_polynomial_level | exact GlobalTheory.ConvSer.exists_intg_polynomial_level | (intros; apply GlobalTheory.ConvSer.exists_intg_polynomial_level <;> assumption)
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmLeftN

open Matrix in
variable {k r : ℕ} in
private lemma flagMat_mulVec_eq_sum_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]

open Matrix in
variable {k r : ℕ} in
private lemma rW_mulVec_adjugate_zhat_single_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_fvec]
  simp [mulVec_single_one, conjTranspose_apply]

open Matrix in
variable {k r : ℕ} in
private lemma conjTranspose_hpk : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose

open Matrix in
variable {k r : ℕ} in
private lemma gram_eq_upper_bounds (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_hpk,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
private lemma mul_adjugate_conjTranspose_eq_of_det_eq_one {m n : ℕ} (X : Matrix (Fin n) (Fin m) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (Y : Matrix (Fin n) (Fin m) ℂ) (hU : U.det = 1) :
    (X * U) * ((X * U)ᴴ * Y).adjugateᴴ = X * (Xᴴ * Y).adjugateᴴ := by
  rw [conjTranspose_mul, Matrix.mul_assoc Uᴴ, adjugate_mul_distrib, conjTranspose_mul,
    adjugate_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc X U,
    ← Matrix.mul_assoc U, mul_adjugate, hU, one_smul, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
private lemma det_eq_one_of_upUni {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) : U.det = 1 := by
  rw [det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]


open Matrix in
theorem _root_.GlobalTheory.WigSh.OmLeftN.omg_mul_left (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g n : _root_.Formalism.FourierDecayAlt.Q.Mx k r) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z)
    (hn : n ∈ _root_.Formalism.QuantumDeterminants.Nset k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' (n * g) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  obtain ⟨U, hU, hnF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z hz n hn
  have hnU : nᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * n = _root_.Formalism.QuantumDeterminants.Hpk k r := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff n).1 hn).1
  have hQ : _root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      _root_.Formalism.QuantumDeterminants.Hpk k r * (n * g)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z * U := by
    have key : nᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * (n * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)) =
        _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z := by
      simp only [← Matrix.mul_assoc, hnU]
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← hnF, key]
  rw [rW_mulVec_adjugate_zhat_single_last, rW_mulVec_adjugate_zhat_single_last, gram_eq_upper_bounds, gram_eq_upper_bounds, mulVec_mulVec, mulVec_mulVec, hQ,
    mul_adjugate_conjTranspose_eq_of_det_eq_one _ _ _ (det_eq_one_of_upUni hU)]

theorem omg_left_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g m : Mx k r), inWb k r z → inWb k r z' → g ∈ UH (Hpk k r) → m ∈ Formalism.QuantumDeterminants.Nset k r → GlobalTheory.WigSh.omg k r z z' (m⁻¹ * g) = GlobalTheory.WigSh.omg k r z z' g :=
  fun k r z z' g m hz _ _ hm => omg_mul_left k r z z' g m⁻¹ hz ((unipotent_subgroup_holds k r).2.2 m hm)

end GlobalTheory.WigSh.OmLeftN
end
end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

@[to_additive]
theorem minorSt_prod_range {M : Type} [CommMonoid M] {N r : ℕ} (hr : r ≤ N) (g : ℕ → M)
    (hg : ∀ s, ¬ (1 ≤ s ∧ s ≤ r) → g s = 1) :
    ∏ s ∈ Finset.range (N + 1), g s = ∏ s : Fin r, g (s.val + 1) := by
  rw [Finset.prod_range_succ', hg 0 (by omega), _root_.mul_one, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) r]
  symm
  apply Finset.prod_subset (Finset.range_subset_range.mpr hr)
  intro s _ hs
  apply hg
  rw [Finset.mem_range] at hs
  omega

theorem minorSt : MinorSt := by
  classical
  intro E _ _ _ H Dw K _ typ m n₁ n₂ hm
  let rk : (E →+* ℂ) → ℕ := fun τ => min (Dw.mult τ) (if typ τ then n₁ else n₂)
  have hrk : ∀ τ, rk τ ≤ Dw.mult τ := fun τ => min_le_left _ _
  have hrk1 : ∀ τ, typ τ → rk τ ≤ n₁ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hrk2 : ∀ τ, ¬ typ τ → rk τ ≤ n₂ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hm0 : ∀ τ s, ¬ (1 ≤ s ∧ s ≤ rk τ) → m τ s = 0 := by
    intro τ s hs
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hm τ s h
    exact hs ⟨h1, le_min h2 h3⟩
  let col : ∀ τ, Fin (rk τ) → Fin (n₁ + n₂) := fun τ i =>
    if h : typ τ then Fin.castAdd n₂ (Fin.castLE (hrk1 τ h) i) else Fin.natAdd n₁ (Fin.castLE (hrk2 τ h) i)
  refine ⟨rk, hrk, col, fun τ s => m τ (s.val + 1), ?_, ?_, ?_, ?_⟩
  · intro τ i j hij
    by_cases h : typ τ
    · simp only [col, dif_pos h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
    · simp only [col, dif_neg h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
  · intro τ i
    by_cases h : typ τ
    · have := hrk1 τ h
      have := i.isLt
      simp only [col, dif_pos h, h, iff_true, Fin.val_castAdd, Fin.val_castLE]
      omega
    · simp [col, h]
  · unfold degOf
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [minorSt_sum_range (hrk τ) (fun s => s * m τ s) (fun s hs => by simp [hm0 τ s hs])]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  · unfold minorProd FamGerm.minorsP
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod]
    by_cases h : typ τ
    · rw [if_pos h, if_neg (not_not.mpr h), _root_.mul_one,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₁ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk1 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_pos h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl
    · rw [if_neg h, if_pos h, _root_.one_mul,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₂ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk2 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_neg h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl

end GlobalTheory.PowGerm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowGerm.starRing_ext_of_star {R : Type*} [NonUnitalNonAssocSemiring R] (s t : StarRing R)
    (h : ∀ a : R, s.toStarMul.toInvolutiveStar.toStar.star a =
      t.toStarMul.toInvolutiveStar.toStar.star a) :
    s = t := by
  rcases s with @⟨@⟨@⟨@⟨s⟩, _⟩, _⟩, _⟩
  rcases t with @⟨@⟨@⟨@⟨t⟩, _⟩, _⟩, _⟩
  obtain rfl : s = t := funext h
  rfl


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowGerm.starSt : _root_.GlobalTheory.PowGerm.StarSt := by
  unfold _root_.GlobalTheory.PowGerm.StarSt
  intro E _ _ _ H inst h
  exact _root_.GlobalTheory.PowGerm.starRing_ext_of_star _ _ fun a => (h a).trans rfl

end GlobalTheory.PowGerm
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomNum

theorem mom_num : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (T : ℝ), Num k r lam u b bv ga h q0 → 0 < T → (((2 * r + k + 1) : ℝ) ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * (b ^ 2) ^ (2 * r) ≤ Hsq r T b := by
  intro k r lam u b bv ga h q0 T hN hT
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
  have ha := (h7 ⟨k, by omega⟩ (by simp)).2
  have hb := (abs_le.mp (h8 ⟨k, by omega⟩)).1
  have hbv : bv ≤ b := by linarith
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hn7 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ hn1 (by norm_num)
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = ((2 * r + k + 1) : ℝ) := by push_cast; ring
  rw [hcast] at hn1 hn7 h15
  set n : ℝ := (2 * r + k + 1 : ℝ) with hn
  have hnb : n ≤ b := by linarith
  have hbv6 : 6 ≤ bv := by linarith
  have hb6 : 6 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h6 : 6 * bv ≤ b ^ 2 := by nlinarith
  have hb0 : 0 ≤ b := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hbv0 : 0 ≤ 6 * bv := by linarith
  have hTm : T ≤ max 1 T := le_max_right _ _
  have hm0 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  unfold Hsq
  calc n ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2)) * (b ^ 2) ^ (2 * r)
      ≤ b ^ 2 * (max 1 T * b ^ 4) * (b ^ 2) ^ (2 * (2 * r + 2)) * (b ^ 2) ^ (2 * r) := by
        gcongr
    _ = max 1 T * b ^ (12 * r + 14) := by ring
    _ ≤ max 1 T * b ^ (20 * (r + 1)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by omega)) hm0

end GlobalTheory.MomNum
end
