module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.FormalDegreeBessel.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle274
public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPowLeCardFlagQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Schur

theorem avg_sq {X V ι : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (f : X → V) (hf : AEStronglyMeasurable f μ) (c : ℝ) (hn : ∀ᵐ x ∂μ, ‖f x‖ = c)
    (T : ι → V →L[ℂ] V) (hT : ∀ i a b, ⟪T i a, T i b⟫_ℂ = ⟪a, b⟫_ℂ)
    (m : ι → X → X) (hm : ∀ i, MeasurePreserving (m i) μ μ)
    (hfm : ∀ i, ∀ᵐ x ∂μ, f (m i x) = T i (f x))
    (hirr : ∀ S : Submodule ℂ V, (∀ i, ∀ v ∈ S, T i v ∈ S) → S = ⊥ ∨ S = ⊤) (w : V) :
    Integrable (fun x => ‖⟪w, f x⟫_ℂ‖ ^ 2) μ ∧
      ∫ x, ‖⟪w, f x⟫_ℂ‖ ^ 2 ∂μ = ‖w‖ ^ 2 * c ^ 2 / Module.finrank ℂ V := by
  have hci : ∀ s : V, Integrable (fun x => ‖⟪s, f x⟫_ℂ‖ ^ 2) μ := by
    intro s
    refine Integrable.of_bound (((aestronglyMeasurable_const (b := s)).inner hf).norm.pow 2)
      ((‖s‖ * c) ^ 2) ?_
    filter_upwards [hn] with x hx
    rw [norm_pow, norm_norm, ← hx]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  refine ⟨hci w, ?_⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [Subsingleton.elim w 0]; simp
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let Fy : V → X → V := fun y x => ⟪f x, y⟫_ℂ • f x
  have hFm : ∀ y, AEStronglyMeasurable (Fy y) μ := fun y =>
    (hf.inner (aestronglyMeasurable_const (b := y))).smul hf
  have hFi : ∀ y, Integrable (Fy y) μ := by
    intro y
    refine Integrable.of_bound (hFm y) (c * ‖y‖ * c) ?_
    filter_upwards [hn] with x hx
    simp only [Fy]
    rw [norm_smul, ← hx]
    exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
  let R : V →ₗ[ℂ] V :=
    { toFun := fun y => ∫ h, Fy y h ∂μ
      map_add' := by
        intro y z
        rw [← integral_add (hFi y) (hFi z)]
        congr 1; funext h; simp only [Fy, inner_add_right, add_smul]
      map_smul' := by
        intro c y
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext h; simp only [Fy, inner_smul_right, mul_smul] }
  have hRdef : ∀ y, R y = ∫ h, Fy y h ∂μ := fun _ => rfl
  have hcomm : ∀ i y, R (T i y) = T i (R y) := by
    intro i y
    rw [hRdef, hRdef, ← (T i).integral_comp_comm (hFi y)]
    have h1 : ∫ h, Fy (T i y) h ∂μ = ∫ h, Fy (T i y) (m i h) ∂μ := by
      have := integral_map (μ := μ) (φ := m i) (hm i).measurable.aemeasurable (f := Fy (T i y))
        (by rw [(hm i).map_eq]; exact hFm _)
      rwa [(hm i).map_eq] at this
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hfm i] with x hx
    simp only [Fy, hx, map_smul, hT]
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue R
  have hE : Module.End.eigenspace R lam = ⊤ :=
    (hirr _ (fun h x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hcomm, hx, map_smul])).resolve_left hlam
  have hR : ∀ y, R y = lam • y := fun y =>
    Module.End.mem_eigenspace_iff.mp (hE ▸ Submodule.mem_top)
  have h4 : ∀ s : V, lam * ((‖s‖ ^ 2 : ℝ) : ℂ) = ((∫ h, ‖⟪s, f h⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro s
    have a : ⟪s, R s⟫_ℂ = lam * ((‖s‖ ^ 2 : ℝ) : ℂ) := by
      rw [hR, inner_smul_right, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have b : ⟪s, R s⟫_ℂ = ∫ h, ⟪s, Fy s h⟫_ℂ ∂μ := (integral_inner (hFi s) s).symm
    have c : ∀ h, ⟪s, Fy s h⟫_ℂ = ((‖⟪s, f h⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro h
      simp only [Fy, inner_smul_right]
      rw [← inner_conj_symm (f h) s, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← a, b]
    simp_rw [c]
    exact integral_ofReal
  have h5 : lam * (Module.finrank ℂ V : ℂ) = ((c ^ 2 : ℝ) : ℂ) := by
    let b := stdOrthonormalBasis ℂ V
    have e1 : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = c ^ 2 := by
      have : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = ∫ _h, c ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hn] with x hx
        rw [b.sum_sq_norm_inner_right, hx]
      rw [this]; simp
    rw [← e1, integral_finsetSum _ fun i _ => hci (b i)]
    push_cast
    simp_rw [← h4]
    have hb : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
    simp [hb, mul_comm]
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  apply Complex.ofReal_injective
  rw [← h4, Complex.ofReal_div, Complex.ofReal_mul, ← h5]
  push_cast
  field_simp

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem type_irred {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} (hT : 0 < Tz k r z)
    {u : Fin k → ℝ} (hπ : IsHCTypeW k r z u π) :
    Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨h1, h2, h3, h4⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ'
  obtain ⟨g, hg, hρ⟩ := hπ
  refine ⟨hρ.1, ⟨⟨h1, h2⟩, h3, h4⟩, fun S _ hS => ?_⟩
  refine hρ.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ ?_ v hv
  have hg' : PI.UpqRep.IsFrameW k r z g := hg
  have hx' : x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k) :=
    PI.HwUniqW.mem_UJset_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp hx.1)
  exact GlobalTheory.BesselFrame.conj_mem_UW hg' hx'

theorem avg_UW [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    {μW : Measure (Mt k r)} (hU : IsURepOn (UWset k r z) π) (hI : IsIrredOn (UWset k r z) π)
    (hH : IsHaarOn (UWset k r z) μW) (h1 : μW Set.univ = 1) (w ξ : Wp) :
    ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW =
      ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) := by
  haveI : IsProbabilityMeasure μW := ⟨h1⟩
  have hW := isClosedSub_UWset (k := k) (r := r) z
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.mpr hH.2.2.1
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r)) := continuous_id
  have hf : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x) ξ) μW := by
    have hc : ContinuousOn (fun x : Mt k r => π (Matrix.of x) ξ) {x : Mt k r | Matrix.of x ∈ UWset k r z} :=
      hU.2.2 ξ
    have := hc.aestronglyMeasurable (μ := μW) (hW.2.1.preimage hof).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r z}) hae] at this
  have hlm : ∀ s : Mat k r, Continuous (lmulM s : Mt k r → Mt k r) := fun s =>
    (continuous_const (y := s)).matrix_mul hof
  obtain ⟨hi, hv⟩ := avg_sq μW (fun x : Mt k r => π (Matrix.of x) ξ) hf ‖ξ‖
    (hae.mono fun x hx => hU.2.1 _ hx ξ) (fun s : UWset k r z => π s)
    (fun s => (LinearMap.norm_map_iff_inner_map_map ((π s : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hU.2.1 s s.2))
    (fun s => lmulM (s : Mat k r))
    (fun s => ⟨(hlm s).measurable, hH.2.2.2 s s.2⟩)
    (fun s => hae.mono fun x hx => DFunLike.congr_fun (hU.1.2 s s.2 _ hx) ξ)
    (fun S hS => hI S S.closed_of_finiteDimensional fun g hg => hS ⟨g, hg⟩) w
  rw [← hv, ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

theorem type_irred_and_avg : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → (∀ u, IsHCTypeW k r z u π → Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π) ∧ ∀ μW : Measure (Mt k r), IsURepOn (UWset k r z) π → IsIrredOn (UWset k r z) π → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∀ w ξ : Wp, ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW = ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) :=
  fun _ _ _ _ _ _ _ _ _ hT => ⟨fun _ hπ => type_irred hT hπ, fun _ hU hI hH h1 w ξ => avg_UW hU hI hH h1 w ξ⟩

end GlobalTheory.Amp.Schur
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DatumOf

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul_iff (g : S.GLV) (P : Submodule L.O S.V) (x : S.V) :
    x ∈ g • P ↔ ∃ b ∈ P, g b = x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

theorem inner_le_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O ≤
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine sup_le ?_ le_sup_right
  rintro z ⟨hz1, hz2⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff S n Λ z).1 hz1
  have hyP : y ∈ perp L S.Hm Y := (hn.1 y).1 hz2
  have e : n y = y + (n y - y) := by abel
  rw [e]
  exact Submodule.add_mem_sup ⟨hy, hyP⟩ (hn.2 y hyP)

theorem inner_eq_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine le_antisymm (inner_le_of_unip S Y n hn Λ) ?_
  have h1 := inner_le_of_unip S Y n⁻¹ (inv_mem hn) (n • Λ)
  rwa [inv_smul_smul] at h1

theorem complementGroup_fixes_frameSpan {g : S.GLV} (hg : g ∈ S.H0) {x : S.V} (hx : x ∈ S.ME) : g x = x :=
  sub_eq_zero.1 ((Submodule.mem_bot E).1 (hg.2.2 x hx))

theorem X_le : S.X ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_left
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem X'_le : S.X' ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_right
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0) {y : S.V}
    (hy : y ∈ perp L S.Hm Y) : g y ∈ perp L S.Hm Y := by
  intro w hw
  have e := hg.1 y w
  rw [complementGroup_fixes_frameSpan S hg (hY hw)] at e
  rw [e]
  exact hy w hw

theorem inTh_smul (g : S.GLV) (Λ : Submodule L.O S.V) {v : S.V} (hv : S.InTh Λ v) :
    S.InTh (g • Λ) (g v) := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩, map_smul g _ y⟩

theorem smul_inner_lattice_le_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) ≤
      ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (mem_smul_iff S g _ z).1 hz
  obtain ⟨y, ⟨hy1, hy2⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hb
  rw [map_add (f := _), complementGroup_fixes_frameSpan S hg (hY hx)]
  exact Submodule.add_mem_sup ⟨(mem_smul_iff S g Λ _).2 ⟨y, hy1, rfl⟩, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S Y hY hg hy2⟩ hx

theorem smul_inner_lattice_eq_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) := by
  refine le_antisymm ?_ (smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY hg Λ)
  have h1 := smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY (inv_mem hg) (g • Λ)
  rw [inv_smul_smul] at h1
  intro z hz
  have h2 := Submodule.smul_mem_pointwise_smul _ g _ (h1 (Submodule.smul_mem_pointwise_smul z g⁻¹ _ hz))
  rwa [smul_inv_smul] at h2

theorem smul_graphOf_subset_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    g • S.graphOf Λ ⊆ S.graphOf (g • Λ) := by
  rintro _ ⟨p, ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩, rfl⟩
  refine ⟨g y', (mem_smul_iff S g Λ _).2 ⟨y', hy', rfl⟩, g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩,
    hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X'_le S) hg h1, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X_le S) hg h2, ?_, ?_, ?_⟩
  · show g y' - g p.1 ∈ S.X'
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X'_le S h3)]
    exact h3
  · show g y - g p.2 ∈ S.X
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X_le S h4)]
    exact h4
  · rw [← map_sub]
    exact inTh_smul S g Λ h5

theorem graphOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.graphOf (g • Λ) = g • S.graphOf Λ := by
  refine subset_antisymm ?_ (smul_graphOf_subset_of_mem_hermitianStabilizer S hg Λ)
  intro p hp
  have h1 := smul_graphOf_subset_of_mem_hermitianStabilizer S (inv_mem hg) (g • Λ) ⟨p, hp, rfl⟩
  rw [inv_smul_smul] at h1
  exact ⟨g⁻¹ • p, h1, smul_inv_smul g p⟩

theorem datOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.datOf (g • Λ) = g • S.datOf Λ :=
  Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X (X_le S) hg Λ)
    (Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X' (X'_le S) hg Λ) (graphOf_smul_eq_of_mem_hermitianStabilizer S hg Λ))

theorem std_inner [IsNonarchimedeanLocalField F] [CharZero F] (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hgs : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V) (hA : S.IsInner g gs A) :
    (S.stdLat g gs A ⊓ (perp L S.Hm (S.spanTo g r)).restrictScalars L.O) ⊔
      (S.spanTo g r).restrictScalars L.O = A := by
  have h3 := (StdLat.stdLat_spec L r k S g gs hgs A hA).2.2
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro y ⟨hy1, hy2⟩
      exact (h3 y).2 ⟨y, hy1, hy2, by simp⟩
    · intro x hx
      exact hA.1 x hx
  · intro x hx
    obtain ⟨y, hy, hyp, hyx⟩ := (h3 x).1 hx
    have e : x = y - (y - x) := by abel
    rw [e]
    exact Submodule.sub_mem_sup ⟨hy, hyp⟩ hyx

theorem datOf_term [IsNonarchimedeanLocalField F] [CharZero F] {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) : d = S.datOf Λ := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛ, hΛ', -, hg⟩ := h
  refine Prod.ext ?_ (Prod.ext ?_ hg)
  · show d.1 = (Λ ⊓ (perp L S.Hm S.X).restrictScalars L.O) ⊔ S.X.restrictScalars L.O
    rw [hΛ, inner_eq_of_unip S S.X n hn.2]
    exact (std_inner S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).symm
  · show d.2.1 = (Λ ⊓ (perp L S.Hm S.X').restrictScalars L.O) ⊔ S.X'.restrictScalars L.O
    rw [hΛ', inner_eq_of_unip S S.X' n' hn'.2]
    exact (std_inner S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').symm

theorem exists_unitri (g : Fin (r + 1) → S.V) (φ : S.GLV) (h : ∀ b : Fin (r + 1), φ (g b) - g b ∈ S.spanTo g b) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, φ (g j) = ∑ i, s i j • g i := by
  choose c hc0 hc using fun b : Fin (r + 1) => StdLat.exists_coef g {i | (i : ℕ) < b} (h b)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := (ne_of_lt hij).symm
    have h0 : c j i = 0 := hc0 j i fun hi => by
      have := Fin.lt_def.1 hij
      simp only [Set.mem_setOf_eq] at hi
      omega
    simp [h0, hne]
  · have h0 : c i i = 0 := hc0 i i fun hi => lt_irrefl (i : ℕ) hi
    simp [h0]
  · have e1 : ∑ i, (c j i + if i = j then (1 : E) else 0) • g i = ∑ i, c j i • g i + g j := by
      simp [add_smul, Finset.sum_add_distrib, ite_smul]
    rw [e1, ← hc j]
    abel

theorem mem_hermitianStabilizer_of_preserves_both_flags [IsNonarchimedeanLocalField F] [CharZero F] (φ : S.GLV) (hφ : φ ∈ isomG L S.Hm)
    (h1 : ∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b)
    (h2 : ∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) :
    ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨s, hs, hsφ⟩ := exists_unitri S S.f φ h1
  obtain ⟨s', hs', hsφ'⟩ := exists_unitri S S.f' φ h2
  have hz : cT L s * S.Zh * s' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S s s' a b, ← hsφ, ← hsφ']
    exact hφ _ _
  obtain ⟨h, hh, hf, hf'⟩ := ((FrameStab.stab_eq L r k S).2 s s' hs hs').1 hz
  have k1 : ∀ (g : Fin (r + 1) → S.V) (m : ℕ), (∀ i, φ (g i) = h (g i)) → ∀ v ∈ S.spanTo g m, φ v = h v := by
    intro g m hg v hv
    have hle : S.spanTo g m ≤ LinearMap.eqLocus (φ : S.V →ₗ[E] S.V) (h : S.V →ₗ[E] S.V) := by
      rw [Frames.spanTo, Submodule.span_le]
      rintro _ ⟨i, -, rfl⟩
      exact hg i
    exact hle hv
  have hfix : ∀ v ∈ S.ME, φ v = h v := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _), map_add (f := _), k1 S.f _ (fun i => by rw [hsφ, hf]) a ha,
      k1 S.f' _ (fun i => by rw [hsφ', hf']) b hb]
  have hiso : h ∈ isomG L S.Hm := hh.1.1.1
  refine ⟨h, hh, h⁻¹ * φ, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hiso) hφ, ?_⟩, (mul_inv_cancel_left h φ).symm⟩
  refine FrameStab.mem_unipOn' bot_le _ fun v hv => ?_
  show h.symm (φ v) - v ∈ (⊥ : Submodule E S.V)
  rw [hfix v hv, LinearEquiv.symm_apply_apply, sub_self]
  exact zero_mem _

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ d Λ, S.IsTerm d Λ → d = S.datOf Λ) ∧ (∀ h ∈ S.H0, ∀ Λ, S.datOf (h • Λ) = h • S.datOf Λ) ∧ (∀ n ∈ S.N, ∀ Λ, (S.datOf (n • Λ)).1 = (S.datOf Λ).1) ∧ (∀ n ∈ S.N', ∀ Λ, (S.datOf (n • Λ)).2.1 = (S.datOf Λ).2.1) ∧ ∀ φ ∈ isomG L S.Hm, (∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b) → (∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) → ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨fun d Λ h => datOf_term S h, fun g hg Λ => datOf_smul_eq_of_mem_hermitianStabilizer S hg Λ,
    fun n hn Λ => inner_eq_of_unip S S.X n hn.2 Λ, fun n hn Λ => inner_eq_of_unip S S.X' n hn.2 Λ,
    fun φ hφ h1 h2 => mem_hermitianStabilizer_of_preserves_both_flags S φ hφ h1 h2⟩

end GlobalTheory.HL.DatumOf
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.automorphicKernel_convergence_properties : KernelA := by
  first | exact @GlobalTheory.KernelConv.kernelA | exact GlobalTheory.KernelConv.kernelA | (intros; apply GlobalTheory.KernelConv.kernelA <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.convolutionSmoothL2_of_def : ConvolutionSmoothL2 := by
  first | exact @GlobalTheory.SmoothGrowth.convolutionSmoothL2 | exact GlobalTheory.SmoothGrowth.convolutionSmoothL2 | (intros; apply GlobalTheory.SmoothGrowth.convolutionSmoothL2 <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.integral_discreteSeries_unipotent_vanishes : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  first | exact @GlobalTheory.RealFibre.integral_phe_eq_zero | exact GlobalTheory.RealFibre.integral_phe_eq_zero | (intros; apply GlobalTheory.RealFibre.integral_phe_eq_zero <;> assumption)
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.bigCell_quotient_normalises_unipotent : ∀ (k r : ℕ) (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ * n * ((Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := by
  first | exact @GlobalTheory.BigConvLevi.levi_conj_mem_iff | exact GlobalTheory.BigConvLevi.levi_conj_mem_iff | (intros; apply GlobalTheory.BigConvLevi.levi_conj_mem_iff <;> assumption)
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem hcType_rep : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → Nontrivial Wp ∧ IsCRepOn (UWset k r z) π ∧ ContinuousOn π (UWset k r z) ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ (∀ S : Submodule ℂ Wp, (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤) := by
  intro k r z u Wp _ _ _ π _ hT hπ
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨h1, hmul, hunit, hcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ'
  obtain ⟨g, hg, hρ⟩ := hπ
  have hg' : PI.UpqRep.IsFrameW k r z g := hg
  refine ⟨hρ.1, ⟨h1, hmul⟩, continuousOn_clm_apply.mpr hcont, hunit, fun S hS => ?_⟩
  refine hρ.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ ?_ v hv
  exact GlobalTheory.BesselFrame.conj_mem_UW hg'
    (PI.HwUniqW.mem_UJset_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp hx.1))

end GlobalTheory.ThA
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_pow_le_card_flag_quotient : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → Gval F F' ≠ 0 → Finite (BQ Λ F F') → NE (E := E) g ^ (r + 1) ≤ (Nat.card (BQ Λ F F') : ℝ) := by
  first | exact @GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ | exact GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ | (intros; apply GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ <;> assumption)
end
