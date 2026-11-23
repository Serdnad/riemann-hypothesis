module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle006

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace SchurWAux

theorem fdeg_eq_finrank {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Nontrivial H]
    (ρ : G → (H →L[ℂ] H)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖) (d : ℝ) (hd : 0 < d)
    (h : ∀ v w v' w' : H, Integrable (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) :
    (d : ℂ) = (Module.finrank ℂ H : ℂ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  set b := stdOrthonormalBasis ℂ H
  have hpt : ∀ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    have e1 : ∀ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ⟪ρ g v, b i⟫_ℂ * ⟪b i, ρ g v⟫_ℂ := by
      intro i
      rw [mul_comm]
      congr 1
      exact inner_conj_symm _ _
    simp_rw [e1]
    rw [b.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K, hiso]
    push_cast
    rfl
  have hbi : ∀ i, ⟪b i, b i⟫_ℂ = 1 := by
    intro i
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  have hL : ∫ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    simp
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => (h v (b i) v (b i)).1)] at hL
  have e2 : ∀ i, ∫ g, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) := by
    intro i
    rw [(h v (b i) v (b i)).2, hbi, mul_one, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp_rw [e2] at hL
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hL
  have hv2 : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖v‖ := norm_pos_iff.mpr hv
    exact_mod_cast (pow_pos this 2).ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [mul_div_assoc', div_eq_iff hd'] at hL
  exact (mul_right_cancel₀ hv2 (by rw [hL]; ring)).symm

end SchurWAux

theorem stSchurW (h : UnitaryGroupStructuralFacts) : StSchurW := by
  obtain ⟨hB2, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCpt, -, -, -, hHI, -, -, -, hCW, -⟩ := hB2
  intro k r Wp _ _ _ D hD v w v' w'
  rcases subsingleton_or_nontrivial Wp with hW | hW
  · rw [Subsingleton.elim w 0]
    simp
  have hU : IsClosedSubgroup (UWset k r D.z) := hCW k r D.z
  have hμ := D.haarW
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  let μ : Measure (MatrixSubsetMeasurability.SG hU) := MatrixSubsetMeasurability.nu hU D.μW
  have : μ.IsMulLeftInvariant := MatrixSubsetMeasurability.nu_left hμ
  have : μ.IsInvInvariant := MatrixSubsetMeasurability.nu_inv hHI hμ
  have hE := MatrixSubsetMeasurability.me_val hU
  have hcpt : IsCompact (Set.univ : Set (MatrixSubsetMeasurability.SG hU)) := by
    have hind : Topology.IsInducing (fun g : MatrixSubsetMeasurability.SG hU => g.1) := Topology.IsInducing.subtypeVal
    have hr : Set.range (fun g : MatrixSubsetMeasurability.SG hU => g.1) = {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} :=
      Subtype.range_coe_subtype
    rw [hind.isCompact_iff, Set.image_univ, hr]
    exact hCpt k r D.z D.z_mem D.T_pos
  have hν1 : μ Set.univ = 1 := by
    have e : ((MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1)) Set.univ = D.μW Set.univ := by
      rw [MatrixSubsetMeasurability.map_nu hμ]
    rw [Measure.map_apply hE.measurable MeasurableSet.univ, Set.preimage_univ] at e
    exact e.trans hD.mass
  have : IsProbabilityMeasure μ := ⟨hν1⟩
  have : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ hcpt (by rw [hν1]; exact one_ne_zero)
  let ρ : MatrixSubsetMeasurability.SG hU → (Wp →L[ℂ] Wp) := fun g => D.π (MatrixSubsetMeasurability.mat g)
  have h1 : ρ 1 = 1 := D.π_rep.1
  have hρm : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := fun a b => D.π_rep.2 _ a.2 _ b.2
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => D.π_unitary _ g.2 v
  have hcont : ∀ v, Continuous fun g => ρ g v := fun v =>
    (D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat MatrixSubsetMeasurability.mat_mem).clm_apply continuous_const
  have hsq : ∀ v w : Wp, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ := by
    intro v w
    refine MemLp.of_bound (continuous_const.inner (hcont v)).aestronglyMeasurable (‖w‖ * ‖v‖)
      (ae_of_all _ fun g => ?_)
    exact (norm_inner_le_norm _ _).trans (le_of_eq (by rw [hiso]))
  have hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS hst => hD.irr S hS fun g hg v hv => hst (MatrixSubsetMeasurability.mk hU g hg) v hv
  have hSq : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨h1, hρm, hiso, hcont, hsq⟩
  obtain ⟨d, hd, hrel⟩ := Formalism.MainNotions.BridgeCSchur.schur_orth hSq hirr
  have hdn := SchurWAux.fdeg_eq_finrank μ ρ hiso d hd hrel
  rw [← MatrixSubsetMeasurability.map_nu (hU := hU) hμ, hE.integral_map, ← hdn]
  exact (hrel v w v' w').2

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stCut4 (h : UnitaryGroupStructuralFacts) : StCut4 := by
  intro hS k r Wp _ _ _ D hD γ P₁ Q P₂ Q₂ hPQ
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z :=
    ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW.conc)
  have key : ∀ g ∈ UWset k r D.z, ∀ x y : Wp,
      ⟪P₁ y, D.π g (Q x)⟫_ℂ = ⟪P₂ y, D.π (th k r γ g) (Q₂ x)⟫_ℂ := by
    intro g hg x y
    have e := congrArg (fun T : Wp →L[ℂ] Wp => ⟪y, T x⟫_ℂ) (hPQ g hg)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right] using e
  have hL : ∀ x y ξ η : Wp,
      ∫ g : Mt k r, ⟪P₁ y, D.π (Matrix.of g) (Q x)⟫_ℂ * star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ / (Module.finrank ℂ Wp : ℂ) :=
    fun x y ξ η => hS k r Wp D hD (Q x) (P₁ y) η ξ
  have hE : ∀ x y ξ η : Wp,
      ∫ g : Mt k r, ⟪P₁ y, D.π (Matrix.of g) (Q x)⟫_ℂ * star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ∫ g : Mt k r, ⟪P₂ y, D.π (th k r γ (Matrix.of g)) (Q₂ x)⟫_ℂ *
          star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW := by
    intro x y ξ η
    refine integral_congr_ae (hW.mono fun g hg => ?_)
    simp only [key _ hg]
  have hdim : (Module.finrank ℂ Wp : ℂ) = 0 → ∀ v : Wp, v = 0 := fun h0 =>
    finrank_zero_iff_forall_zero.1 (by exact_mod_cast h0)
  refine ⟨fun h0 x y ξ η => ?_, fun C₀ hC x y ξ η => ?_⟩
  · have e := (hL x y ξ η).symm.trans ((hE x y ξ η).trans (h0 (Q₂ x) (P₂ y) η ξ))
    by_cases hn : (Module.finrank ℂ Wp : ℂ) = 0
    · simp [hdim hn η]
    · exact (div_eq_zero_iff.1 e).resolve_right hn
  · have e2 : ∫ g : Mt k r, ⟪P₂ y, D.π (th k r γ (Matrix.of g)) (Q₂ x)⟫_ℂ *
          star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ⟪η, C₀ (P₂ y)⟫_ℂ * ⟪C₀ (Q₂ x), ξ⟫_ℂ / (Module.finrank ℂ Wp : ℂ) := by
      rw [← hS k r Wp D hD (C₀ (P₂ y)) (C₀ (Q₂ x)) η ξ]
      refine integral_congr_ae (hW.mono fun g hg => ?_)
      simp only [hC _ hg]
    have e := (hL x y ξ η).symm.trans ((hE x y ξ η).trans e2)
    by_cases hn : (Module.finrank ℂ Wp : ℂ) = 0
    · simp [hdim hn η]
    · exact (div_left_inj' hn).1 e

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace Cut0Aux

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def lmulCLM (a : Mat k r) : Mat k r →L[ℝ] Mat k r where
  toFun y := a * y
  map_add' y y' := Matrix.mul_add a y y'
  map_smul' c y := Matrix.mul_smul a c y
  cont := continuous_const.matrix_mul continuous_id

theorem cont_lmulM (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  show Continuous fun x => a * Matrix.of x
  exact continuous_const.matrix_mul continuous_id

def lmulME (a b : Mat k r) (hab : a * b = 1) (hba : b * a = 1) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM (k := k) (r := r) a
  invFun := lmulM (k := k) (r := r) b
  left_inv x := by
    show b * (a * Matrix.of x) = x
    rw [← Matrix.mul_assoc, hba, Matrix.one_mul]
    rfl
  right_inv x := by
    show a * (b * Matrix.of x) = x
    rw [← Matrix.mul_assoc, hab, Matrix.one_mul]
    rfl
  measurable_toFun := (cont_lmulM a).measurable
  measurable_invFun := (cont_lmulM b).measurable

theorem isTestG_translate {g : Mat k r} (hg : g ∈ GV k r) {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    IsTestG (fun y => φ (g⁻¹ * y)) := by
  obtain ⟨hsm, K, hK, hKv⟩ := hφ
  have hgi : g⁻¹ ∈ GV k r := WeylGroupFacts.uh_inv hg
  have hdet := WeylGroupFacts.isUnit_of_uh hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  refine ⟨fun g₀ hg₀ => ?_, (fun y => g * y) '' K,
    hK.image (continuous_const.matrix_mul continuous_id), fun y hy hyK => ?_⟩
  · obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hsm (g⁻¹ * g₀) (WeylGroupFacts.uh_mul hgi hg₀)
    refine ⟨(fun y => g⁻¹ * y) ⁻¹' U, fun y => f' (g⁻¹ * y),
      hU.preimage (continuous_const.matrix_mul continuous_id), hgU, ?_,
      fun y hyU hyG => hfe _ hyU (WeylGroupFacts.uh_mul hgi hyG)⟩
    exact hf'.comp (lmulCLM g⁻¹).contDiff.contDiffOn (fun y hy => hy)
  · apply hKv _ (WeylGroupFacts.uh_mul hgi hy)
    intro hK'
    apply hyK
    refine ⟨g⁻¹ * y, hK', ?_⟩
    show g * (g⁻¹ * y) = y
    rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]

theorem sigInt_translate {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (X : SigData k r)
    {g : Mat k r} (hg : g ∈ GV k r) (φ : Mat k r → ℂ) :
    sigInt D X (fun y => φ (g⁻¹ * y)) X.w = X.σ g (sigInt D X φ X.w) := by
  have hdet := WeylGroupFacts.isUnit_of_uh hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  let e := lmulME (k := k) (r := r) g g⁻¹ hgg hgg'
  have hmap : D.μG.map e = D.μG := D.haarG.left g hg
  have hconc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ GV k r := ae_iff.mpr D.haarG.conc
  let L : X.Hs →ₗᵢ[ℂ] X.Hs :=
    { toLinearMap := (X.σ g).toLinearMap, norm_map' := fun v => X.rep.2.1 g hg v }
  have hL : ∀ v, L v = X.σ g v := fun v => rfl
  unfold sigInt
  conv_lhs => rw [← hmap]
  rw [integral_map_equiv, ← hL, ← LinearIsometry.integral_comp_comm]
  refine integral_congr_ae ?_
  filter_upwards [hconc] with x hx
  have h1 : Matrix.of (e x) = g * Matrix.of x := rfl
  rw [h1, ← Matrix.mul_assoc, hgg', Matrix.one_mul, X.rep.1.2 g hg _ hx, map_smul]
  rfl

end Cut0Aux

theorem stCut0 (h : UnitaryGroupStructuralFacts) : StCut0 := by
  intro k r Wp _ _ _ D X g hg v hv
  obtain ⟨φ, hφ, rfl⟩ := hv
  exact ⟨fun y => φ (g⁻¹ * y), Cut0Aux.isTestG_translate hg hφ, (Cut0Aux.sigInt_translate D X hg φ).symm⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

namespace Cut3H

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem hsVec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := rfl

theorem hsInner_smul_smul (c c' : ℂ) (A B : Wp →L[ℂ] Wp) :
    hsInner (c • A) (c' • B) = c * star c' * hsInner A B := by
  unfold hsInner
  rw [hsVec_smul, hsVec_smul, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  ring

end Cut3H

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Cut3H

theorem stCut3 (h : UnitaryGroupStructuralFacts) : StCut3 := by
  intro hInv k r Wp _ _ _ D X hD hSq γ hγ hZ a₁ b₁ a₂ b₂ X₀ p hp
  have hI := hInv k r Wp D X hD hSq γ hγ
  have hG : ∀ g ∈ GV k r, gbar k r γ g ∈ GV k r := hI.1
  have hmul : ∀ g ∈ GV k r, ∀ g' ∈ GV k r, th k r γ (g * g') = th k r γ g' * th k r γ g := hI.2.2.2.2.1
  have thG : ∀ g ∈ GV k r, th k r γ g ∈ GV k r := fun g hg => WeylGroupFacts.uh_inv (hG g hg)
  have hrep := X.rep.1.2
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have m1 : (Matrix.of p.1.1 : Mat k r) ∈ GV k r := h1.1
  have m2 : (Matrix.of p.1.2 : Mat k r) ∈ GV k r := h2.1
  have m3 : (Matrix.of p.2.1 : Mat k r) ∈ GV k r := h3.1
  have m4 : (Matrix.of p.2.2 : Mat k r) ∈ GV k r := h4.1
  set A : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hA
  set B : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hB
  have mA : A ∈ GV k r := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv m1) (WeylGroupFacts.uh_inv m2)
  have mB : B ∈ GV k r := WeylGroupFacts.uh_mul m4 m3
  set P : Wp →L[ℂ] Wp := (D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹) with hP
  set x : X.Hs := X.σ (th k r γ A) a₁ with hx
  set y : X.Hs := ContinuousLinearMap.adjoint (X.σ (th k r γ B)) b₁ with hy
  have key : ∀ g : Mat k r, g ∈ GV k r →
      hsInner (rho D p (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) g) (mc X a₂ b₂ g • X₀) =
        hsInner P X₀ * (⟪y, X.σ (th k r γ g) x⟫_ℂ * star ⟪b₂, X.σ g a₂⟫_ℂ) := by
    intro g hg
    have e1 : sgs p g = A * g * B := by simp only [sgs, hA, hB, Matrix.mul_assoc]
    have mAg : A * g ∈ GV k r := WeylGroupFacts.uh_mul mA hg
    have e2 : th k r γ (sgs p g) = th k r γ B * (th k r γ g * th k r γ A) := by
      rw [e1, hmul _ mAg _ mB, hmul _ mA _ hg]
    have e3 : X.σ (th k r γ (sgs p g)) =
        (X.σ (th k r γ B)).comp ((X.σ (th k r γ g)).comp (X.σ (th k r γ A))) := by
      rw [e2, hrep _ (thG _ mB) _ (WeylGroupFacts.uh_mul (thG _ hg) (thG _ mA)), hrep _ (thG _ hg) _ (thG _ mA)]
    have e4 : rho D p (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) g = (mc X a₁ b₁ (th k r γ (sgs p g))) • P := by
      simp only [rho, scalF, Function.comp_apply, hP, hD.π_eq, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp]
    rw [e4, hsInner_smul_smul]
    have e5 : mc X a₁ b₁ (th k r γ (sgs p g)) = ⟪y, X.σ (th k r γ g) x⟫_ℂ := by
      rw [mc, e3, hy, hx, ContinuousLinearMap.adjoint_inner_left]
      rfl
    rw [e5, mc]
    ring
  unfold Ph
  have hae : ∀ᵐ g ∂D.μG, (g : Mt k r) ∈ (GV k r : Set (Mt k r)) := mem_ae_iff.2 D.haarG.conc
  rw [integral_congr_ae (g := fun g : Mt k r =>
      hsInner P X₀ * (⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪b₂, X.σ (Matrix.of g) a₂⟫_ℂ))
    (by filter_upwards [hae] with g hg; exact key _ hg)]
  rw [integral_const_mul, hZ x y a₂ b₂, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
