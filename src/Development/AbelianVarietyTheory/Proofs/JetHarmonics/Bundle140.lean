module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Formalism.HermitianCurvature.FrameExists2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle106
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle122
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle108
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle134
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle139
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle117
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle125
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle138
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle113
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle079
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle137
public import Formalism.LocalRingCardinality.Bundle002
public import Formalism.HermitianCurvature.Bundle008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSection
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle130

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem adjoint_eval_subspace {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (v : V) :
    ContinuousLinearMap.adjoint
        ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin k => V) c).comp S.subtypeL) v
      = S.orthogonalProjectionOnto (PiLp.single 2 c v) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left,
    PiLp.inner_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [PiLp.single_eq_of_ne, hb]
  · simp

theorem wigner_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l + 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wP L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hπ hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB
  have hrep : IsRepW (n + 1) r z π := ⟨hπ.2.1, hπ.2.2.1⟩
  obtain ⟨πt, ht1, ht2, ht3⟩ :=
    GlobalTheory.exists_tensor_standard_rep V (n + 1) r z π B hz hT hrep hπ.2.2.2.1 hB
  have hE := GlobalTheory.TensorStd.EB_tensor_std V (n + 1) r z π B πt hz hT hrep ht1 hB ht3
  obtain ⟨S, hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.pieri_raising_submodule_glSucc V n (EB π B) (EB πt B) β L l hH hadj hE hl
  have hq : ∀ (w : ℂ), ∀ y ∈ S, qdet (EB πt B) w y = (∏ i ∈ Finset.Icc 1 (n + 1),
      (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 +
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1) i : ℝ) : ℂ))) • y := by
    intro w y hy
    have h1 := hS4 hy
    unfold CapSp at h1
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at h2
    rw [h2, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj := hu j
    by_cases hjl : j = l
    · subst hjl
      simp only [Function.update_self]
      push_cast at hj ⊢
      linear_combination -hj
    · have hne : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hjl (Fin.ext (by omega))
      rw [Function.update_of_ne hjl, Function.update_of_ne hne]
      linear_combination -hj
  obtain ⟨πS, hπS, hπS2⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S _ hz hT ht1 ht2 hB
    hS1 hS2 hS3 hq
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun c y => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.WigSh.ContrPlus.contraction_wigMap V (n + 1) r z π B S πS a hz hT hB
    (by
      intro y
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (by
      intro h hh y c
      simp only [ha]
      rw [hπS2 h hh y, ht3 h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, πS, _, hπS, hW, ?_⟩
  intro M v hv
  simp only [hA]
  rw [ha, ← hS5 M v hv]
  simp only [a]
  rw [adjoint_eval_subspace]
  rfl

end GlobalTheory.WigSh
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WignerStepLower

open Formalism.FourierDecayAlt.P

theorem comp_adjoint_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (a : S →L[ℂ] V)
    (ha : ∀ y : S, a y = (y : PiLp 2 (fun _ : Fin k => V)) c) (v : V) :
    a (ContinuousLinearMap.adjoint a v) = S.starProjection (PiLp.single 2 c v) c := by
  have h : ContinuousLinearMap.adjoint a v = S.orthogonalProjection (PiLp.single 2 c v) := by
    refine ext_inner_left ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left, ha,
      PiLp.inner_apply, Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [PiLp.single_apply, Pi.single_apply, hb]
    · simp
  rw [h, ha]
  rfl

theorem wigner_step_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l - 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wM L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hty hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hty hL hu hB
  have hR : IsRepW (n + 1) r z π := ⟨hty.2.1, hty.2.2.1⟩
  obtain ⟨πt, hRt, hnt, hft⟩ := GlobalTheory.tensor_dual_standard V (n + 1) r z π B hz hT hR hty.2.2.2.1 hB
  have hE := GlobalTheory.TensorDualDifferential.EB_tensor V (n + 1) r z π B πt hz hT hR hRt hB hft
  obtain ⟨S, hS, hS0, hirr, hcap, hw⟩ := GlobalTheory.T.pieri_lowering_step_gl_tensor_dual_standard V n (EB π B) (EB πt B) β L l hH hadj hE hl
  obtain ⟨π₂, hty₂, hπ₂⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S
    (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) hz hT hRt hnt hB hS hS0 hirr (by
      intro w y hy
      rw [mem_CapSp.1 (hcap hy) w, FrameExtension.prod_Icc_fin]
      congr 1
      unfold cpol shf
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have h1 := hu j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        push_cast at h1 ⊢
        linear_combination -h1
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        linear_combination -h1)
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun _ _ => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.ContractLinear.wigMap_contract V (n + 1) r z π B S π₂ a hz hT hB
    (fun y => by
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (fun h hh y c => by
      simp only [ha]
      rw [hπ₂ h hh y, hft h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, π₂, _, hty₂, hW, fun M v hv => ?_⟩
  simp only [hA]
  rw [comp_adjoint_apply S (Fin.last n) (a (Fin.last n)) (ha _) v]
  exact hw M v hv

end GlobalTheory.WignerStepLower
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.hatLetter_mul_boundedFactor_mem_normalFormSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ X ∈ hats d.L, ∀ b ∈ bmon d, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan | exact GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.letterCol_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (l : Letter ℂ S) (w : List (Letter ℂ S)), admitted st (l :: w) → ∀ i e e', TL.letterCol L st l w i e e' ∈ nfSpan d (hats d.L) 1 0 1 := by
  first | exact @GlobalTheory.HatNF.LetterEntries.letterCol_mem | exact GlobalTheory.HatNF.LetterEntries.letterCol_mem | (intros; apply GlobalTheory.HatNF.LetterEntries.letterCol_mem <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cm_even_theta_series_chart_coeff_integral : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → Bd 1 (hat M.ι (C ω * logS) θ) := by
  first | exact @GlobalTheory.MomOne.theta_series_integral | exact GlobalTheory.MomOne.theta_series_integral | (intros; apply GlobalTheory.MomOne.theta_series_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem goodPage_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), T.Q.Pins → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Real.log D.R.k ≤ L.sc.L → ∀ j : ℕ, InR D j →
  GoodPage (numOf D L) j (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) Tp.nWn Tp.TO 100 L.sc.b L.sc.L := by
  intro D L Pm Tp hK T hP hC h5 hx hkb hlog j hj
  obtain ⟨hfirst, hw⟩ := GlobalTheory.T.firstRows_bound_and_sizes_bounds D L Pm Tp hK j hj hx hkb
  obtain ⟨hr0, hr1⟩ := GlobalTheory.T.weight_rest_degree_after_gaps_bounds D L Pm Tp hK T hP j hj
  have hgap := fun z => GlobalTheory.T.realPlaceWeightRowGap_mul_bounds_size D L Pm Tp hK j hj z (hw z).1
  have hj1 : 1 ≤ j := hj.1
  have hj2 : j ≤ D.R.m := hj.2
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hn : 0 < D.R.n := by unfold Ranks.n; have := D.R.m_le_f; omega
  have hf : 1 ≤ D.R.f := by unfold Ranks.f; omega
  have hr : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hDp : 1 ≤ Tp.Dp := by
    rw [Tp.Dp_eq]
    exact Nat.mul_pos hf (Nat.choose_pos hr)
  have h40 := Tp.TO_40
  have hTpos : (0 : ℝ) < Tp.TO := by exact_mod_cast TO_pos Tp
  have hx0 : 0 < L.sc.x := by linarith
  have hw'' : 0 < L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.b Scale.X'
    have : (0 : ℝ) < D.R.n := by exact_mod_cast hn
    positivity
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hwj : ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
    intro z
    have h1 : j - 1 < D.R.m := by omega
    have h2 : 1 ≤ j ∧ j ≤ (numOf D L).R.m := ⟨hj1, hj2⟩
    unfold NumDatum.w NumDatum.eQ wj
    rw [dite_eq_left h1, dite_eq_left h2]
    rfl
  refine ⟨⟨((Tp.Dp : ℝ) + 4) / Tp.TO, ?_, fun z => lt_of_lt_of_le hw'' (hw z).1, fun z => (hgap z).1,
    fun z => (hgap z).2, ⟨by positivity, ?_⟩, ?_, hr0, hr1⟩, fun τ _ => hfirst τ, ?_, ?_, hlog, ?_, ?_⟩
  · exact_mod_cast TO_pos Tp
  · rw [div_le_one hTpos]
    exact_mod_cast (by omega : Tp.Dp + 4 ≤ Tp.TO)
  · show ((D.R.k : ℝ) - 1) * (((Tp.Dp : ℝ) + 4) / Tp.TO) ≤ 5 * D.R.m
    have h := Tp.TO_Dk
    rw [div_le_iff₀ hm0] at h
    rw [← mul_div_assoc, div_le_iff₀ hTpos]
    have hD : (1 : ℝ) ≤ Tp.Dp := by exact_mod_cast hDp
    have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    nlinarith [mul_nonneg (sub_nonneg.2 hD) (sub_nonneg.2 hk)]
  · refine le_trans ?_ Tp.nW_win.1
    show 10 * (D.R.r : ℝ) * (D.R.f + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) ≤ _
    unfold LevelStarExponents.nW
    have hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      linarith
    gcongr
  · refine le_trans h5 ?_
    unfold Scale.L
    have := L.sc.eps_pos
    have := L.sc.ez_le
    exact Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith)
  · intro p hp hin
    by_contra h
    have hin' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := hin
    have hne2 : p ≠ 2 := by
      rintro rfl
      have e : D.host.cls 2 = PrimeClass.ram2 := primeClass_two D.host.toHostRaw
      rw [e] at hin'
      simp at hin'
    have hp3 : p = 3 := by
      have h5 : p < 5 := not_le.1 h
      have h2 := hp.two_le
      interval_cases p
      · exact absurd rfl hne2
      · rfl
      · exact absurd hp (by norm_num)
    have hp4 : p ≤ D.host.splitBound := by
      rw [hp3]
      exact le_trans (Nat.le_floor (by exact_mod_cast h5)) L.split_tie
    have hjac := D.host.split_small p hp hne2 hp4
    rcases hin' with e | e
    · exact ((primeClass_eq_inert_iff D.host.toHostRaw).1 e).2.2.2.1 hjac
    · exact ((primeClass_eq_signal_iff D.host.toHostRaw).1 e).2.2.2.1 hjac
  · intro z z'
    rw [hwj, hwj]
    exact Pm.X''_ratio j j _ _ hj1 hj2 hj1 hj2

end GlobalTheory.GoodDepth
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowJets

theorem exists_position_basis {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {n r : ℕ} (xe : X' ≃+ (Fin n → X))
    (b : Module.Basis (Fin r) ℤ X) :
    ∃ (r' : ℕ) (b' : Module.Basis (Fin r') ℤ X'), ∀ k, ∃ i j, xe (b' k) = Pi.single i (b j) := by
  classical
  let B : Module.Basis (Σ _ : Fin n, Fin r) ℤ (Fin n → X) := Pi.basis fun _ => b
  refine ⟨_, (B.map xe.toIntLinearEquiv.symm).reindex (Fintype.equivFin _), fun k => ?_⟩
  refine ⟨((Fintype.equivFin (Σ _ : Fin n, Fin r)).symm k).1, ((Fintype.equivFin (Σ _ : Fin n, Fin r)).symm k).2, ?_⟩
  simp [B, Pi.basis_apply]

theorem sum_single_add {X : Type} [AddCommGroup X] {n : ℕ} (Q : X → ℤ) (i : Fin n) (x : X) (w : Fin n → X) :
    ∑ k, Q ((Pi.single i x + w : Fin n → X) k) = ∑ k, Q (w k) + (Q (x + w i) - Q (w i)) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ (fun k => Q (w k)) (Finset.mem_univ i),
    Finset.sum_congr rfl (g := fun k => Q (w k)) fun k hk => by
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk), zero_add]]
  simp only [Pi.add_apply, Pi.single_eq_same]
  ring

theorem exists_basis_bounds {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {n r : ℕ} (xe : X' ≃+ (Fin n → X))
    (Q : X → ℤ) (h0 : Q 0 = 0) (hQ : ∀ x, 0 ≤ Q x) (Φ M0 : ℝ) (b : Module.Basis (Fin r) ℤ X)
    (hΦ : ∀ j, (Q (b j) : ℝ) ≤ Φ) (hM : ∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) :
    ∃ (r' : ℕ) (b' : Module.Basis (Fin r') ℤ X'), (∀ j, (sumQ xe Q (b' j) : ℝ) ≤ Φ) ∧
      ∀ j w, |((sumQ xe Q (b' j + w) - sumQ xe Q (b' j) - sumQ xe Q w : ℤ) : ℝ)| ≤ max M0 0 * sumQ xe Q w := by
  obtain ⟨r', b', hb⟩ := exists_position_basis xe b
  have e1 : ∀ k i j, xe (b' k) = Pi.single i (b j) → sumQ xe Q (b' k) = Q (b j) := fun k i j h => by
    have := sum_single_add Q i (b j) 0
    simpa [sumQ, h, h0] using this
  refine ⟨r', b', fun k => ?_, fun k w => ?_⟩
  · obtain ⟨i, j, h⟩ := hb k
    rw [e1 k i j h]
    exact hΦ j
  · obtain ⟨i, j, h⟩ := hb k
    have e2 : sumQ xe Q (b' k + w) = sumQ xe Q w + (Q (b j + xe w i) - Q (xe w i)) := by
      unfold sumQ
      rw [map_add (f := _), h]
      exact sum_single_add Q i (b j) (xe w)
    have e3 : sumQ xe Q (b' k + w) - sumQ xe Q (b' k) - sumQ xe Q w = Q (b j + xe w i) - Q (b j) - Q (xe w i) := by
      rw [e1 k i j h, e2]; ring
    have e4 : Q (xe w i) ≤ sumQ xe Q w :=
      Finset.single_le_sum (f := fun k => Q (xe w k)) (fun k _ => hQ _) (Finset.mem_univ i)
    rw [e3]
    refine (hM j _).trans (mul_le_mul (le_max_left _ _) (by exact_mod_cast e4) (by exact_mod_cast hQ _) (le_max_right _ _))

theorem jets_on_copies : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → JetsOnCopiesCompatibleFrames := by
  intro L1 L2 L4 TB E _ _ _ H Dw l Xo c inst hstar
  obtain rfl : inst = H.starRing := starSt E H inst hstar
  letI := H.starRing
  intro T io y _ C htr P ϖ hϖ Q hQ Φ M0 r b hΦ0 hΦ hM n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ v hv q D hq hD f hf
  choose f₀ hf₀ using hf
  obtain ⟨τ, hτ, htrunc, hgerm⟩ := frameNSt_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n (chD C.ch) pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨r', b', h1, h2⟩ := exists_basis_bounds pD.xe Q (Q_zero hϖ P.D hQ) (RoundingSumAlt.Q_nonneg hϖ hQ) Φ M0 b hΦ hM
  have hD' : (D : ℝ) * max M0 0 < q := by
    rcases le_total M0 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact_mod_cast (by omega : 0 < q)
    · rwa [max_eq_left h]
  obtain ⟨s, σ', g, lam, a1, a2, a3, a4, a5, a6⟩ := GlobalTheory.UnifJets.jets L1 L2 L4 TB T.V ϖ hϖ D' A' G' U' (Fin n × Fin (chD C.ch))
    (zV pG C.xT) hu τ hτ (htrunc htr) (sumQ pD.xe Q) (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) Φ (max M0 0) r' b' hΦ0
    (le_max_right _ _) h1 h2 F v hv q D hq hD' (fun e => f₀ e)
  refine ⟨s, σ', g, lam, a1, a2, (hgerm F q σ' g).2 a3, a4, a5, fun e he => ?_⟩
  rw [a6 e he, map_smul, MvPowerSeries.coeff_map, ← hf₀ e, smul_eq_mul, ← IsScalarTower.algebraMap_apply]
  rfl

end GlobalTheory.PowJets
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_functional_l2_bound_and_isometry : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  first | exact @GlobalTheory.MomMass.mom_mass | exact GlobalTheory.MomMass.mom_mass | (intros; apply GlobalTheory.MomMass.mom_mass <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.exists_continuous_frame_section' : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r), D.IsBaseFrame Bs ν' m₀ → ∃ γ : (Fin (r + 1) → ℂ) → B.Mat k r, ContinuousOn γ {c | (∀ a, c a ≠ 0) ∧ Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (c (Fin.last r))} ∧ ∀ c : Fin (r + 1) → ℂ, (∀ a, c a ≠ 0) → Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (c (Fin.last r)) → γ c ∈ B.GV k r ∧ Zhat k r Bs.z Bs.z' (γ c) = D.ptMatN (TBB.bigPt r c) (r + 1) ∧ D.IsDFrame Bs ν' m₀ (γ c) := by
  first | exact @GlobalTheory.FrameSection.exists_continuous_frame_section | exact GlobalTheory.FrameSection.exists_continuous_frame_section | (intros; apply GlobalTheory.FrameSection.exists_continuous_frame_section <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_regular_rep_vec_bigPt_eq_bessel :
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ γ ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', Formalism.QuantumDeterminants.Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) ∧ ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), p.V F (TBB.bigPt P.r c) = B.JF p.T.base F γ := by
  intro P Wp Wq _ _ _ _ _ _ p d hl0 hG
  have hd : ∀ a, d a ≠ 0 := fun a =>
    (hl0.1 (1, d a) (by unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨a, rfl⟩)).2
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := hl0
  have hG' : 0 < D.ptG (Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z * Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z') P.r
      (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  obtain ⟨hγ, hZγ, -⟩ := h'.choose_spec
  have hpos : 0 < Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  refine ⟨h'.choose, ⟨hγ, fun l _ => ?_, hpos⟩, hZγ, fun F => ?_⟩
  · unfold Formalism.QuantumDeterminants.Dmin
    rw [hZγ, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hd _
  · show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d) = _
    unfold D.vecV
    rw [dite_eq_left ⟨hl, hG'⟩, dite_eq_left h']
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZγ.trans hmono) F]

end GlobalTheory
end
