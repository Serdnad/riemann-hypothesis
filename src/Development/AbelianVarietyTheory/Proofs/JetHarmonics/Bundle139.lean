module

public import Formalism.HermitianCurvature.FrameExists2
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle133
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle106
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle125
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle130
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle136
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem isType_of_irreducible_stable : ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (Y →L[ℂ] Y)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (S : Submodule ℂ Y) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → Stab (EB π B) S → S ≠ ⊥ → (∀ S' : Submodule ℂ Y, S' ≤ S → Stab (EB π B) S' → S' = ⊥ ∨ S' = S) → (∀ (w : ℂ), ∀ y ∈ S, qdet (EB π B) w y = (∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • y) → ∃ πS : Mx k r → (S →L[ℂ] S), IsType k r z πS u ∧ ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
  intro Y _ _ _ k r z π B S u hz hT hπ hn hB hS hne hirr hcap
  have hst : ∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S :=
    Formalism.FourierDecayAlt.P.lie_stabilizer Y k r z π B hz hT hπ hB S hS
  have hfr0 : ∀ {m : ℕ} (C : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsFrameOf k r [z] C → IsFrameOf k r [z, 0] C := by
    intro m C hC
    refine ⟨hC.1, hC.2.1, fun a v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hC.2.2 a _ (by simp)
    · simp [herm]
  let πS : Mx k r → (S →L[ℂ] S) := fun h => (S.orthogonalProjection).comp ((π h).comp S.subtypeL)
  have hcoe : ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
    intro h hh y
    have := Submodule.orthogonalProjection_mem_subspace_eq_self (K := S) ⟨π h y, hst h hh y y.2⟩
    exact congrArg Subtype.val this
  have hrep : IsRepW k r z πS := by
    refine ⟨⟨?_, fun a _ b hb => ?_⟩, ?_⟩
    · ext y
      simp [πS, hπ.1.1]
    · ext y
      have h1 := hcoe b hb y
      simp only [πS, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h1 ⊢
      rw [h1, hπ.1.2 a ‹_› b hb]
      rfl
    · exact continuousOn_const.clm_comp (hπ.2.clm_comp continuousOn_const)
  refine ⟨πS, ⟨Submodule.nontrivial_iff_ne_bot.2 hne, hrep.1, hrep.2, ?_, ?_, ?_⟩, hcoe⟩
  · intro h hh v
    rw [Submodule.coe_norm, Submodule.coe_norm, hcoe h hh, hn h hh]
  · intro S'' hS''
    have hstab : Stab (EB π B) (S''.map S.subtype) := by
      refine Formalism.FourierDecayAlt.P.stabilizer_lie_algebra Y k r k z 0 π B hπ (hfr0 B hB) _ ?_
      rintro h hh - _ ⟨y, hy, rfl⟩
      exact ⟨πS h y, hS'' h hh y hy, hcoe h hh y⟩
    rcases hirr _ (Submodule.map_subtype_le S S'') hstab with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_subtype_top])
  · intro B' hB' w v
    rw [(Formalism.FourierDecayAlt.P.frame_general_linear S k r k z πS B' hrep hB').2 w v]
    apply Subtype.ext
    have h1 := GlobalTheory.intertwiner_EB_of_stabiliser S Y k r k z 0 πS π S.subtypeL B' hrep hπ (hfr0 B' hB') (fun h hh _ v => hcoe h hh v)
    have h2 := GlobalTheory.qminor_intertwine Y S k k (EB π B') (EB πS B') S.subtype h1 id id w v
    have h3 := GlobalTheory.capelli_det_frame_indep Y k r z π B B' hz hT hπ hB hB' w
    refine h2.trans ?_
    have h4 := hcap w v v.2
    rw [h3] at h4
    exact h4

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem vd2_nonneg_of_D7 (D : D7) : 0 ≤ vd2 D := by
  unfold vd2
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast D.host.QS_pos)

theorem sizes_two_arith (T f q m v A S C b Sc η : ℝ) (hf : 0 ≤ f) (hq : 0 ≤ q) (hqm : q ≤ m) (hv : 0 ≤ v)
    (hC : 1 ≤ C) (hb : 0 ≤ b) (hSc : 0 ≤ Sc) (hη : 0 ≤ η) (hA : T * A = 2 * b + Sc) (hS : T * S ≤ f * η) :
    T * (f * q * (1 + v / 2) * A + q * S) ≤ C * m * (2 + v) * (2 * f * b + f * (Sc + η)) := by
  have hm : 0 ≤ m := hq.trans hqm
  have e1 : T * (f * q * (1 + v / 2) * A + q * S) = q * (f * (1 + v / 2) * (2 * b + Sc) + T * S) := by
    rw [← hA]; ring
  have h1 : f * (1 + v / 2) * (2 * b + Sc) + T * S ≤ (2 + v) * (2 * f * b + f * (Sc + η)) := by
    have p1 : 0 ≤ f * (1 + v / 2) * (2 * b + Sc) := by positivity
    have p2 : 0 ≤ (1 + v) * (f * η) := by positivity
    nlinarith
  have h0 : 0 ≤ (2 + v) * (2 * f * b + f * (Sc + η)) := by positivity
  rw [e1]
  calc q * (f * (1 + v / 2) * (2 * b + Sc) + T * S) ≤ q * ((2 + v) * (2 * f * b + f * (Sc + η))) :=
        mul_le_mul_of_nonneg_left h1 hq
    _ ≤ m * ((2 + v) * (2 * f * b + f * (Sc + η))) := mul_le_mul_of_nonneg_right hqm h0
    _ ≤ C * (m * ((2 + v) * (2 * f * b + f * (Sc + η)))) := le_mul_of_one_le_left (mul_nonneg hm h0) hC
    _ = _ := by ring

theorem sizes_bound_two : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (Q : Par D), Q.Pins → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ C : ℝ, 1 ≤ C → ∀ j, InR D j → ∃ Ap : ℝ, 0 ≤ Ap ∧ (∀ τ, InPsi Q.H τ → (wtA (lR Tp hK j) (τ, 0) : ℝ) ≤ Ap) ∧ (open Classical in (Tp.TO : ℝ) * ((D.R.f : ℝ) * (Q.Dw j).q * (1 + vd2 D / 2) * Ap + (Q.Dw j).q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi Q.H τ), (wtA (lR Tp hK j) (τ, 0) : ℝ)) ≤ C * D.R.m * (2 + vd2 D) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz))) := by
  classical
  intro D L Pm Tp hK Q hQ hx hkb C hC j hj
  obtain ⟨hSe, hw⟩ := GlobalTheory.T.cloudSizes_between_zero_and_twice_b D L Pm hx hkb
  obtain ⟨hw1, -, -⟩ := hw j hj
  obtain ⟨-, -, hP, hN, hwt⟩ := GlobalTheory.T.weightExponents_embeddings_degree D Q hQ j hj (lR Tp hK j)
  have hT : (0 : ℝ) < (Tp.TO : ℝ) := by exact_mod_cast TO_pos Tp
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hSc := L.Sc_pos.le
  have hη := L.etaSz_pos.le
  have hplus : ∀ t, (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aP t) 0 : ℝ) ≤ 2 * L.sc.b + L.Sc := by
    intro t
    unfold Formalism.L2.Pj.ext0
    split_ifs with h
    · have h1 : (Tp.TO : ℝ) * ((lR Tp hK j).aP t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aP t ⟨0, h⟩ : ℝ) := by
        exact_mod_cast (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK j t).1 ⟨0, h⟩
      obtain ⟨h2, h3, -⟩ := GlobalTheory.T.kappaRows_entries_le_sizes D L Pm Tp hK j hj t
      rcases Nat.lt_or_ge 0 (D.R.k - 1) with hk | hk
      · have := h2 ⟨0, h⟩ hk
        have := (hw1 t).2
        linarith
      · have := h3 ⟨0, h⟩ hk
        linarith
    · simp only [Nat.cast_zero, mul_zero]; linarith
  have hminus : ∀ t, (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aM t) 0 : ℝ) ≤ L.etaSz := by
    intro t
    unfold Formalism.L2.Pj.ext0
    split_ifs with h
    · have h1 : (Tp.TO : ℝ) * ((lR Tp hK j).aM t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aM t ⟨0, h⟩ : ℝ) := by
        exact_mod_cast (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK j t).2.1 ⟨0, h⟩
      exact h1.trans ((GlobalTheory.T.kappaRows_entries_le_sizes D L Pm Tp hK j hj t).2.2 _)
    · simpa using hη
  refine ⟨(2 * L.sc.b + L.Sc) / Tp.TO, by positivity, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨t, rfl⟩ := (hP τ).1 hτ
    rw [(hwt t 0).1, le_div_iff₀ hT, mul_comm]
    exact hplus t
  · have hq : (Q.Dw j).q ≤ D.R.m := by
      rw [(hQ.2.2.2 j hj).2.1]
      exact Nat.sub_le _ _
    refine sizes_two_arith _ _ _ _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hq)
      (vd2_nonneg_of_D7 D) hC hb hSc hη (by field_simp) ?_
    rw [Finset.mul_sum]
    have hcard : (Finset.univ.filter (fun τ => ¬ InPsi Q.H τ)).card ≤ D.R.f := by
      rw [← (GlobalTheory.T.realPlaceLabel_bijective_card_eq_f D).2, ← Finset.card_univ]
      refine le_trans (Finset.card_le_card ?_)
        (Finset.card_image_le (f := fun t => ComplexEmbedding.conjugate (DV.tauEmb D t)))
      intro τ hτ
      obtain ⟨t, rfl⟩ := (hN τ).1 (Finset.mem_filter.1 hτ).2
      exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩
    refine (Finset.sum_le_card_nsmul _ _ L.etaSz ?_).trans ?_
    · intro τ hτ
      obtain ⟨t, rfl⟩ := (hN τ).1 (Finset.mem_filter.1 hτ).2
      rw [(hwt t 0).2]
      exact hminus t
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hη

end GlobalTheory.RunDepth
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.degree_weightKappa_le_pageBound : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ j, InR D j → (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤ (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) ∧ ∀ i, (WeightAlgebra.DF (kaR Tp hK j) : ℝ) < ((D.host.g i : ℝ) - 2) / 2 := by
  first | exact @GlobalTheory.RunDepth.DF_kaR_le | exact GlobalTheory.RunDepth.DF_kaR_le | (intros; apply GlobalTheory.RunDepth.DF_kaR_le <;> assumption)
end
