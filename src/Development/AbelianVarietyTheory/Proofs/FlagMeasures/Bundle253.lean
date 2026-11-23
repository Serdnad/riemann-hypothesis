module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.LocalRingCardinality.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle065
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.AmpTK

theorem exists_kFinCoef_torus_ne : BranchingSupport.Hyps → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H k r L l l' κ τ hκ hτ hl hl' hxe hye
  have hK : PI.KFinSmooth := H.1.2.2.1
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, L.hσ⟩
  obtain ⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩ :=
    GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v) := hmul0
  have hone : ∀ v : L.Hs, L.σ 1 v = v := hone0
  have hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := hinn0
  have hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  have hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ
  have hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ
  have hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v := by
    intro v
    rw [← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]
  have side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V),
      SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) →
      ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0 := by
    intro V _ _ _ m hm ⟨x, hxT, hx⟩
    haveI := FiniteDimensional.complete ℂ V
    refine GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V
      (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_
    · intro v hv w hw
      exact (congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans
        (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))
    · intro a v hv
      exact (congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))
    · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2
    · refine ⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩
      exact fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)
  obtain ⟨x₀, hx₀, hx₀'⟩ := side l hl hxe
  obtain ⟨y₀, hy₀, hy₀'⟩ := side l' hl' hye
  set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ
  set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'
  let P : L.Hs →L[ℂ] L.Wp := (innerSL ℂ x₀).smulRight ξ
  let Q : L.Wq →L[ℂ] L.Hs := (innerSL ℂ ξ').smulRight y₀
  let X : L.Wq →L[ℂ] L.Wp := (innerSL ℂ ξ').smulRight ξ
  have hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ := fun v => rfl
  have hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀ := fun w => rfl
  have hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ := fun w => rfl
  refine ⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩
  · intro w
    obtain ⟨S, hS, hyS, hSK⟩ := hy₀
    refine ⟨S, hS, ?_, hSK⟩
    rw [hQ]
    exact S.smul_mem _ hyS
  · intro v
    have hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀ := by
      apply ext_inner_right ℂ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    rw [hadj]
    obtain ⟨S, hS, hxS, hSK⟩ := hx₀
    exact ⟨S, hS, S.smul_mem _ hxS, hSK⟩
  · refine ⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀,
      fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩
    · intro g hg
      have key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) =
          (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ))) := by
        ext v
        show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _
        rw [hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]
        rfl
      have key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ =
          ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ := by
        intro u
        rw [← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]
      ext w
      simp only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX,
        map_smul, key2, inner_smul_right, smul_smul, mul_comm]
      exact congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)
    · simp only [Fin.sum_univ_one]
      rfl
  · rw [hX, inner_smul_right]
    exact mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')

end GlobalTheory.AmpTK
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

theorem ballMean_eLpNorm_two_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {ν : Measure α} {f : α → E} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f ν)
    (h : ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν ≤ ENNReal.ofReal (C * a ^ 2)) :
    eLpNorm f 2 ν ≤ ENNReal.ofReal (Real.sqrt C * a) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf]
  have h2 : (∫⁻ x, ‖f x‖ₑ ^ (ENNReal.toReal 2) ∂ν) = ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν := by
    congr 1; funext x
    rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rfl
  rw [h2]
  calc _ ≤ (ENNReal.ofReal (C * a ^ 2)) ^ (1 / (ENNReal.toReal 2)) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt C * a) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [show (1 / ENNReal.toReal 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
        Real.sqrt_mul' _ (by positivity), Real.sqrt_sq ha]

theorem ballMean_norm_integral_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E} {C a : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hf : AEStronglyMeasurable f ν)
    (h : ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν ≤ ENNReal.ofReal (C * a ^ 2)) :
    Integrable f ν ∧ ‖∫ x, f x ∂ν‖ ≤ Real.sqrt C * (ν Set.univ).toReal ^ (1 / 2 : ℝ) * a := by
  have h2 := ballMean_eLpNorm_two_le hC ha hf h
  have hL2 : MemLp f 2 ν := lt_of_le_of_lt h2 ENNReal.ofReal_lt_top
  refine ⟨hL2.integrable (by norm_num), ?_⟩
  have h1 : eLpNorm f 1 ν ≤ eLpNorm f 2 ν * ν Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hf
  rw [eLpNorm_one_eq_lintegral_eNorm hf] at h1
  have hexp : (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal : ℝ) = 1 / 2 := by norm_num
  rw [hexp] at h1
  have hmu : ν Set.univ ^ (1 / 2 : ℝ) = ENNReal.ofReal ((ν Set.univ).toReal ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal (measure_ne_top ν _)]
  have key : ‖∫ x, f x ∂ν‖ₑ ≤ ENNReal.ofReal (Real.sqrt C * (ν Set.univ).toReal ^ (1 / 2 : ℝ) * a) := by
    calc ‖∫ x, f x ∂ν‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ eLpNorm f 2 ν * ν Set.univ ^ (1 / 2 : ℝ) := h1
      _ ≤ ENNReal.ofReal (Real.sqrt C * a) * ENNReal.ofReal ((ν Set.univ).toReal ^ (1 / 2 : ℝ)) := by
          rw [hmu]; gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  rw [← ofReal_norm_eq_enorm] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

theorem ballMean_clm : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (T : H → Mat k r → Wp), IsHaarOn (GG k r) μG →
    (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG]
      fun x => T u (Matrix.of x) + T u' (Matrix.of x)) →
    (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) →
    (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H,
      AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧
      ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG]
      fun x => T u (Matrix.of x * y)) →
    ∀ j : ℕ, ∃ Λ : H →L[ℂ] Wp, ∀ (v : H) (x : Mt k r), Matrix.of x ∈ GG k r →
      Λ (σ (Matrix.of x) v) = avgR μG j (fun z : Mt k r => T v (Matrix.of z)) x := by
  intro k r H _ _ _ Wp _ _ _ σ μG T hμ hadd hsmul hL2 htr j
  have hBfin : μG (nbd k r j) < ⊤ := haar_compact_lt_top hμ (isCompact_nbd j)
  haveI : IsFiniteMeasure (μG.restrict (nbd k r j)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBfin⟩
  obtain ⟨C, hC⟩ := hL2 (nbd k r j) (isCompact_nbd j)
  have hb : ∀ u : H, Integrable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict (nbd k r j)) ∧
      ‖∫ x in nbd k r j, T u (Matrix.of x) ∂μG‖ ≤
        Real.sqrt (max C 0) * ((μG.restrict (nbd k r j)) Set.univ).toReal ^ (1 / 2 : ℝ) * ‖u‖ := by
    intro u
    refine ballMean_norm_integral_le (le_max_right C 0) (norm_nonneg u) (hC u).1 ?_
    refine (hC u).2.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left C 0
  set c : ℝ := ((μG (nbd k r j)).toReal)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.2 ENNReal.toReal_nonneg
  let L : H →ₗ[ℂ] Wp :=
    { toFun := fun v => c • ∫ x in nbd k r j, T v (Matrix.of x) ∂μG
      map_add' := fun u u' => by
        rw [integral_congr_ae (ae_restrict_of_ae (hadd u u')), integral_add (hb u).1 (hb u').1, smul_add]
      map_smul' := fun b u => by
        simp only [RingHom.id_apply]
        rw [integral_congr_ae (ae_restrict_of_ae (hsmul b u)), integral_smul, smul_comm] }
  refine ⟨L.mkContinuous (c * (Real.sqrt (max C 0) *
      ((μG.restrict (nbd k r j)) Set.univ).toReal ^ (1 / 2 : ℝ))) ?_, ?_⟩
  · intro v
    show ‖c • ∫ x in nbd k r j, T v (Matrix.of x) ∂μG‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hc0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v).2 hc0
  · intro v x hx
    show c • ∫ y in nbd k r j, T (σ (Matrix.of x) v) (Matrix.of y) ∂μG = _
    unfold avgR
    rw [integral_congr_ae (ae_restrict_of_ae (htr _ hx v))]
    rfl

end GlobalTheory.SgInf
end
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot

theorem hsDist_equiv_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) : hsDist (hf.equiv.symm k) = Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) := by
  have h := hf.umat_equiv (hf.equiv.symm k)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  have h' : Formalism.MainNotions.S.uMat k - 1 = Matrix.reindex f f (UpqT.mat (hf.equiv.symm k) - 1) := by
    rw [show Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.umat k from rfl, h]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  unfold hsDist Formalism.REAL.hs
  rw [h']
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  symm
  rw [← f.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← f.sum_comp]
  simp

private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (hc : GlobalTheory.Count.IsGauge ε c) :
    0 < c := by
  have hV : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hneg'
  have hneg : c ≤ 0 := not_lt.1 hneg'
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2)
        ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    exact div_nonpos_iff.2 (Or.inr ⟨mul_nonpos_iff.2 (Or.inr ⟨hneg, ENNReal.toReal_nonneg⟩),
      (pow_pos hr' _).le⟩)
  have := le_of_tendsto hc hle
  linarith

private theorem tendsto_gauge_ratio_volume_ball {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (hc : GlobalTheory.Count.IsGauge ε c)
    (hc0 : 0 < c) :
    Tendsto (fun r : ℝ =>
        c * (Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2}).toReal / r ^ (n ^ 2))
      (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := by
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef
  set A : ℝ → ℝ≥0∞ := fun r =>
    Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r} with hAdef
  set B : ℝ → ℝ≥0∞ := fun r =>
    Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2} with hBdef
  have hV : 0 < V :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hc' : Tendsto (fun r => c * (A r).toReal / r ^ (n ^ 2)) (𝓝[>] 0) (𝓝 V) := hc
  have hBA : ∀ r : ℝ, 0 < r → B r ≤ A r := by
    intro r hr
    apply measure_mono
    intro g hg
    exact ((Real.sqrt_lt' hr).2 hg).le
  have hAB : ∀ r s : ℝ, 0 < r → s < r → A s ≤ B r := by
    intro r s hr hs
    apply measure_mono
    intro g hg
    exact (Real.sqrt_lt' hr).1 (lt_of_le_of_lt hg hs)
  have hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), A r ≠ ⊤ := by
    filter_upwards [hc'.eventually (lt_mem_nhds hV)] with r hr htop
    rw [htop] at hr
    simp at hr
  have h1 : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝 0) (𝓝 ((1 - 0) ^ (n ^ 2))) :=
      ((continuous_const.sub continuous_id).pow _).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝 0) (𝓝 ((1 - 0) * 0)) :=
        ((continuous_const.sub continuous_id).mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact mul_pos (by linarith [hr.2]) hr.1
  have hlow : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2) *
      (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2))) (𝓝[>] 0) (𝓝 V) := by
    simpa using h1.mul (hc'.comp h2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hc' ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hfin] with r hr hAr
    have hr0 : 0 < r := hr.1
    have h1r : 0 < 1 - r := by linarith [hr.2]
    have hBfin : B r ≠ ⊤ := ne_top_of_le_ne_top hAr (hBA r hr0)
    have hle : (A ((1 - r) * r)).toReal ≤ (B r).toReal :=
      ENNReal.toReal_mono hBfin (hAB r _ hr0 (by nlinarith))
    have hne1 : (1 - r) ^ (n ^ 2) ≠ 0 := pow_ne_zero _ h1r.ne'
    have hne2 : r ^ (n ^ 2) ≠ 0 := pow_ne_zero _ hr0.ne'
    have heq : (1 - r) ^ (n ^ 2) * (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2)) =
        c * (A ((1 - r) * r)).toReal / r ^ (n ^ 2) := by
      rw [mul_pow]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hc0.le) (pow_pos hr0 _).le
  · filter_upwards [self_mem_nhdsWithin, hfin] with r hr hAr
    have hr0 : (0 : ℝ) < r := hr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hAr (hBA r hr0)) hc0.le) (pow_pos hr0 _).le

theorem gauge_transport : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  intro n ε c P Q f hf hc
  have hc0 : 0 < c := pos_of_isGauge' hc
  refine ⟨hc0, ?_⟩
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have hPQ : P + Q = n := Sorts.add_eq f
  have hVfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef
  have hV : 0 < V :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' hVfin
  have hlim := tendsto_gauge_ratio_volume_ball hc hc0
  have key : ∀ r : ℝ, ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) {g | hsDist g < r ^ 2} =
      ENNReal.ofReal c * Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} := by
    intro r
    rw [Measure.map_apply (show Measurable (hf.equiv.symm : Formalism.REAL.UJ ε → UpqT P Q) from
        hf.equiv.symm.continuous.measurable)
      (measurableSet_lt continuous_hsDist.measurable measurable_const), Measure.smul_apply, smul_eq_mul]
    congr 2
    ext k
    simp [hsDist_equiv_symm hf k]
  have hBfin : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} ≠ ⊤ := by
    filter_upwards [hlim.eventually (lt_mem_nhds hV)] with r hr htop
    rw [htop] at hr
    simp at hr
  have hlim' : Tendsto (fun r : ℝ => ENNReal.ofReal
      (c * (Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2}).toReal / r ^ (n ^ 2) / V))
      (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (hlim.div_const V)
    rwa [div_self hV.ne', ENNReal.ofReal_one] at this
  unfold HasEuclDensity
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hBfin] with r hr hB
  have hr0 : (0 : ℝ) < r := hr
  have hball : ballVol ((P + Q) ^ 2) r = ENNReal.ofReal (r ^ (n ^ 2)) * ENNReal.ofReal V := by
    have := ballVol_mul ((P + Q) ^ 2) r 1 hr0 one_pos
    rw [mul_one] at this
    rw [this, hPQ, hVdef, ENNReal.ofReal_toReal hVfin]
    rfl
  rw [key r, hball, ← ENNReal.ofReal_mul (pow_nonneg hr0.le _), div_div,
    ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hr0 _) hV), ENNReal.ofReal_mul hc0.le,
    ENNReal.ofReal_toReal hB]

end GlobalTheory.GaugeQuot
end
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DatumOfPeriods

section

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma dsigW_eq (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ w v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v)
    rw [ih]; rfl

lemma isBesselMapSm_smul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {l : H → Wp}
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l) (a : ℂ) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun v => a • l v) := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, ‖a‖ * C, Ws, h4, fun v hv => ?_⟩
  · simp only [h1 v hv w hw, smul_add]
  · simp only [h2 c v hv]; rw [smul_comm]
  · simp only [h3 g hg m hm v hv, map_smul]; rw [smul_comm]
  · simp only [dsigW_eq, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h5 v hv) (norm_nonneg _)

lemma l2SG_sqrt_smul_eq_ofReal_mul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (n : ℕ) (c : ℝ)
    (h : l2SG ν F = ENNReal.ofReal c) :
    l2SG ν (fun g => ((Real.sqrt n : ℝ) : ℂ) • F g) = ENNReal.ofReal (c * n) := by
  have e : ∀ y : Wp, ((‖((Real.sqrt n : ℝ) : ℂ) • y‖₊ : ℝ≥0∞)) ^ 2 = (n : ℝ≥0∞) * (‖y‖₊ : ℝ≥0∞) ^ 2 := by
    intro y
    have : ‖((Real.sqrt n : ℝ) : ℂ)‖₊ ^ 2 = (n : NNReal) := by
      apply NNReal.eq
      simp [Real.sq_sqrt, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [nnnorm_smul, ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, this, ENNReal.coe_natCast]
  unfold l2SG at h ⊢
  simp only [e]
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), h, mul_comm c, ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_natCast]

end

theorem exists_goodS : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  intro hH D τ w w' θ W lam R _ l l' dd _ _ hR hl hl' hdd hn hn'
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨P, hP, hD⟩ := hR.2
  have hD' : Formalism.MainNotions.S.IsDS (epsSH D.R) lam (fun g => R.σ (P⁻¹ * g * P)) := hD
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ hD' _ (D.s.cdScale_pos _ (epsSH D.R))
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hD'
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hvs : v ∈ R.sm :=
    ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK _ _ _ lam R hR P hP S hS.1 hS.2.1).1 v hvS).2
  refine ⟨{ H := R.H, σ := R.σ, B := fun x => ((Real.sqrt (Module.finrank ℂ W.Wp : ℕ) : ℝ) : ℂ) • l x,
            B' := fun x => ((Real.sqrt (Module.finrank ℂ W.Wq : ℕ) : ℝ) : ℂ) • l' x,
            v0 := v, cN := ‖v‖ ^ 2 / dd, deg := d },
    hR.1, hR.2, isBesselMapSm_smul hl _, isBesselMapSm_smul hl' _, hvs, hv0, ⟨P, hP, ?_⟩,
    div_pos (pow_pos (norm_pos_iff.2 hv0) 2) hdd, l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn v hvs),
    l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn' v hvs), P, hP.1, hd⟩
  exact (le_sSup (s := {S | IsKTypeOf (epsSH D.R) (fun g => R.σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (epsSH D.R) lam) S}) hS) hvS

end GlobalTheory.DatumOfPeriods
end
end

section


theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation : PI.RhsWLim.W.OrbRepY := by
  first | exact @GlobalTheory.HypOrbitUnique.orbRepY | exact GlobalTheory.HypOrbitUnique.orbRepY | (intros; apply GlobalTheory.HypOrbitUnique.orbRepY <;> assumption)
end
