module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle191
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

noncomputable section

namespace GlobalTheory.MatCoeffDeriv

open GlobalTheory.FockCompare

theorem hasDerivAt_form_heisO_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∀ w : WO S T, HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) (ℓ (heisO ψ S T w (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0)) - deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 * ℓ (heisO ψ S T w f)) 0 := by
  intro D ψ hψ θ hθ S T ℓ hℓ f hf M hM hMf w
  have hL : IsRealDir T S M := ⟨hM, hMf⟩
  have hg : IsThetaFunO ψ S T (heisO ψ S T w f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  set g := heisO ψ S T w f with hg_def
  set c : ℝ → ℂ := fun s => ψ (symplOH S T w (M s)) with hc_def

  have lsub : ∀ a b, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b → ℓ (a - b) = ℓ a - ℓ b := by
    intro a b ha hb
    have := hℓ.add (a - b) b (GlobalTheory.OrientedHeis.theta_sub ha hb) hb
    rw [sub_add_cancel] at this
    rw [this]; ring

  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hce : c = fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) *
      (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1))))) := by
    funext s
    show ψ (symplOH S T w (M s)) = _
    rw [(smooth_iff_sm_and_real_lines D θ σ h T S).2.1 M hL s, GlobalTheory.OrientedHeis.psi_symplOH h hψ, map_smul]
    rfl
  have hcd : HasDerivAt c (deriv c 0) 0 := by
    refine DifferentiableAt.hasDerivAt ?_
    have h2 : ContDiff ℝ ∞ fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) *
        (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1))))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (contDiff_id.mul contDiff_const)))
    rw [hce]
    exact h2.differentiable (by simp) 0
  have hc0 : c 0 = 1 := by
    show ψ (symplOH S T w (M 0)) = 1
    rw [M.map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, ψ.map_zero_eq_one]
  have hcne : ∀ s, c s ≠ 0 := by
    intro s; rw [hce]; exact Complex.exp_ne_zero _

  have hF : ∀ s, heisO ψ S T (w + M s) f = c s • heisO ψ S T (M s) g := by
    intro s
    rw [hg_def, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul,
      GlobalTheory.FinTranslate.symplOH_skew (S := S) (T := T) w (M s), add_neg_cancel, ψ.map_zero_eq_one, one_smul, add_comm]

  obtain ⟨U, hUo, hUl⟩ := hg.level
  obtain ⟨d, C, hC⟩ := hℓ.bound U hUo
  have key := ((GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev D ψ hψ θ hθ S T d g hg).2 M hM hMf).2
  have hmemM : ∀ t, heisO ψ S T (M t) g ∈ GlobalTheory.Size.thetaLevel ψ S T U := fun t =>
    ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (M t),
      fun u hu h0 => GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)⟩
  have hmemg : g ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hg, hUl⟩
  have hmemd : GlobalTheory.OrientedHeis.dLine ψ S T M g ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
    refine ⟨GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hg, fun u hu h0 => ?_⟩
    funext p
    have : (fun t => heisO ψ S T (M t) g p) = fun t => heisO ψ S T u (heisO ψ S T (M t) g) p := by
      funext t; rw [GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)]
    conv_rhs => unfold GlobalTheory.OrientedHeis.dLine; rw [this]
    unfold GlobalTheory.OrientedHeis.dLine
    rw [heisO, ← deriv_const_mul_field]
    rfl
  have hG : HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) (ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff, tendsto_iff_edist_tendsto_0]
    have hφ : ∀ t : ℝ, (t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g ∈
        GlobalTheory.Size.thetaLevel ψ S T U := fun t =>
      Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)) hmemd
    have he : ∀ t : ℝ, edist (slope (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) 0 t - ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0
        = ‖ℓ ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g)‖ₑ := by
      intro t
      rw [edist_zero_right, lsub _ _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)).1 hmemd.1,
        hℓ.smul _ _ (Submodule.sub_mem _ (hmemM t) hmemg).1, lsub _ _ (hmemM t).1 hg, slope_def_module,
        sub_zero, M.map_zero, GlobalTheory.WeilVacMove.heisO_zero, Complex.real_smul, Complex.ofReal_inv]
    simp_rw [he]
    have hT : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * supSob ψ θ d ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) -
        GlobalTheory.OrientedHeis.dLine ψ S T M g)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) key (Or.inr ENNReal.coe_ne_top)
      rwa [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le)
      (fun t => hC _ (hφ t))

  set f' : WO S T → ℂ := fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0 with hf'_def
  have hf'θ : IsThetaFunO ψ S T f' := GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hf
  have hdl : GlobalTheory.OrientedHeis.dLine ψ S T M g = heisO ψ S T w f' - (2 * deriv c 0) • g := by
    funext p
    set H : ℝ → ℂ := fun s => heisO ψ S T w (heisO ψ S T (M s) f) p with hH_def
    have hHd : HasDerivAt H (heisO ψ S T w f' p) 0 := by
      have hd := (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL hf (p + w) 0).differentiableAt.hasDerivAt
      exact hd.const_mul (ψ (symplOH S T p w))
    have hH0 : H 0 = g p := by
      show heisO ψ S T w (heisO ψ S T (M 0) f) p = heisO ψ S T w f p
      rw [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]
    have hEq : (fun s : ℝ => heisO ψ S T (M s) g p) = fun s => (c s)⁻¹ * ((c s)⁻¹ * H s) := by
      funext s
      have e1 : H s = c s * heisO ψ S T (w + M s) f p := by
        show heisO ψ S T w (heisO ψ S T (M s) f) p = _
        rw [GlobalTheory.OrientedHeis.heisO_heisO]; rfl
      rw [e1, hF s, Pi.smul_apply, smul_eq_mul]
      field_simp [hcne s]
    have hci := hcd.inv (by rw [hc0]; exact one_ne_zero)
    have hD := hci.mul (hci.mul hHd)
    have hD' : HasDerivAt (fun s : ℝ => heisO ψ S T (M s) g p) _ 0 :=
      hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => congrFun hEq s)
    show deriv (fun s : ℝ => heisO ψ S T (M s) g p) 0 = _
    rw [hD'.deriv]
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc0, hH0]
    ring

  have hfun : (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) = fun s => c s * ℓ (heisO ψ S T (M s) g) := by
    funext s
    rw [hF s, hℓ.smul _ _ (hmemM s).1]
  rw [hfun]
  have hP := hcd.mul hG
  refine hP.congr_deriv ?_
  rw [hdl, lsub _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf'θ w) (GlobalTheory.OrientedHeis.theta_smul _ hg),
    hℓ.smul _ _ hg, hc0]
  simp only [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  ring

end GlobalTheory.MatCoeffDeriv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.PairKeep

theorem res_zero_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c τ : k) (q : Unif k) (hτ : valuation k τ = valuation k ((q.1 : 𝒪[k]) : k)) (hc : valuation k c = 1)
    (x : k) (s : 𝒪[k]) (hs : (s : k) = c * x) :
    IsLocalRing.residue 𝒪[k] s = 0 ↔ ∃ t ∈ 𝒪[k], x = τ * t := by
  have hq := q.ne_zero
  have hvq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using hq
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, map_zero] at hτ; exact hvq hτ.symm
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  rw [IsLocalRing.residue_eq_zero_iff, q.mem_max_iff]
  constructor
  · rintro ⟨t, ht⟩
    have h1 : ((q.1 : 𝒪[k]) : k) / (c * τ) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, map_mul, hc, hτ, one_mul, div_self hvq]
    refine ⟨_, mul_mem h1 t.2, ?_⟩
    have h2 : c * x = ((q.1 : 𝒪[k]) : k) * (t : k) := by rw [← hs, ht]; rfl
    field_simp
    linear_combination h2
  · rintro ⟨t, ht, rfl⟩
    have h1 : (c * τ) / ((q.1 : 𝒪[k]) : k) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, map_mul, hc, hτ, one_mul, div_self hvq]
    refine ⟨⟨_, mul_mem h1 ht⟩, Subtype.ext ?_⟩
    rw [hs]
    change _ = ((q.1 : 𝒪[k]) : k) * (c * τ / ((q.1 : 𝒪[k]) : k) * t)
    field_simp

theorem keep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m'), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) →
    ∀ (c τ : k) (q : Unif k), valuation k τ = valuation k ((q.1 : 𝒪[k]) : k) → valuation k c = 1 →
    (∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ g : GL (Fin m') k, g • P = P →
      (b * g.val * b').reindex (finCongr hm) (finCongr hm) * (b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm) = 1 ∧
      (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], u r0 = τ * s) ↔
        ((∀ r, ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r ∈ 𝒪[k]) ∧
          ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r0 = τ * s)) ∧
      (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔
        ∀ r, (((b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm))ᵀ *ᵥ u) r ∈ 𝒪[k]) := by
  intro k _ _ _ _ m' m hm b b' hbb hb'b P hP c τ q hτ hc hval g hg
  subst hm
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hmul : ∀ g₁ g₂ : GL (Fin m') k, g₁ * g₂ = 1 → (b * g₁.val * b') * (b * g₂.val * b') = 1 := by
    intro g₁ g₂ h
    have h' : g₁.val * g₂.val = 1 := by rw [← Units.val_mul, h, Units.val_one]
    calc (b * g₁.val * b') * (b * g₂.val * b') = b * (g₁.val * (b' * b) * g₂.val) * b' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb'b, Matrix.mul_one, h', Matrix.mul_one, hbb]
  have hb' : ∀ (g : GL (Fin m') k) (u : Fin m' → k), b' *ᵥ ((b * g.val * b') *ᵥ u) = g • (b' *ᵥ u) := by
    intro g u
    change _ = g.val *ᵥ (b' *ᵥ u)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hb'b, Matrix.one_mul]
  have hlat : ∀ u : Fin m' → k, b' *ᵥ u ∈ P.lat ↔ ∀ r, u r ∈ 𝒪[k] := by
    intro u
    rw [hP, Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  have hint : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) →
      ∀ r, ((b * g.val * b') *ᵥ u) r ∈ 𝒪[k] := by
    intro g hg u hu
    rw [← hlat, hb']
    have := ((P.hasVal_fn ⟨_, (hlat u).2 hu⟩).gl_smul g)
    rw [hg] at this
    exact this.mem
  have hlast : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k,
      ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m', r0.1 + 1 = m' → ∃ s ∈ 𝒪[k], u r0 = τ * s) →
      ((∀ r, ((b * g.val * b') *ᵥ u) r ∈ 𝒪[k]) ∧
        ∀ r0 : Fin m', r0.1 + 1 = m' → ∃ s ∈ 𝒪[k], ((b * g.val * b') *ᵥ u) r0 = τ * s) := by
    intro g hg u ⟨hu, hu'⟩
    refine ⟨hint g hg u hu, fun r0 hr0 => ?_⟩
    obtain ⟨s, hs, hv⟩ := hval u hu r0 hr0
    obtain ⟨s', hs', hv'⟩ := hval _ (hint g hg u hu) r0 hr0
    have h1 := hv.gl_smul g
    rw [hg, ← hb'] at h1
    rw [← res_zero_iff c τ q hτ hc _ s' hs', hv'.unique h1, res_zero_iff c τ q hτ hc _ s hs]
    exact hu' r0 hr0
  have htr : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) →
      ∀ r, ((b * g.val * b')ᵀ *ᵥ u) r ∈ 𝒪[k] := by
    intro g hg u hu r
    have h1 := hint g hg (Pi.single r 1) (fun j => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
    rw [Matrix.mulVec_single_one] at h1
    change ∑ j, (b * g.val * b')ᵀ r j * u j ∈ 𝒪[k]
    exact sum_mem fun j _ => mul_mem (h1 j) (hu j)
  have hg' : g⁻¹ • P = P := by rw [inv_smul_eq_iff, hg]
  refine ⟨hmul _ _ (mul_inv_cancel g), fun u => ⟨hlast g hg u, fun h => ?_⟩, fun u => ⟨htr _ hg' u, fun h => ?_⟩⟩
  · have := hlast _ hg' _ h
    rwa [Matrix.mulVec_mulVec, hmul _ _ (inv_mul_cancel g), Matrix.one_mulVec] at this
  · have := htr _ hg _ h
    rwa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hmul _ _ (inv_mul_cancel g), Matrix.transpose_one,
      Matrix.one_mulVec] at this

end GlobalTheory.PairKeep
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.SplitStab

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_iff (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R))
    (hS : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) R (c : E) ∈ S)
    (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r))
    (y : Fin m → E ⊗[F] R) :
    y ∈ Formalism.UG.latS (F := F) R S Λ ↔ (∀ j, y j ∈ S) ∧
      ∀ j : Fin m, j.1 + 1 = m → ∃ s ∈ S, y j = Formalism.UG.inclE (F := F) R (t : E) * s := by
  constructor
  · intro hy
    unfold Formalism.UG.latS at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [SetLike.mem_coe, hΛ] at hx
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · obtain ⟨r, hr, -⟩ := hx j
        simp only [hr]; exact hS r
      · obtain ⟨r, hr, hd⟩ := hx j
        obtain ⟨c, rfl⟩ := hd hj
        refine ⟨_, hS c, ?_⟩
        simp only [hr]; push_cast; rw [map_mul]
    | zero => exact ⟨fun j => zero_mem _, fun j _ => ⟨0, zero_mem _, by simp⟩⟩
    | add a b _ _ ha hb =>
      refine ⟨fun j => add_mem (ha.1 j) (hb.1 j), fun j hj => ?_⟩
      obtain ⟨s1, hs1, e1⟩ := ha.2 j hj
      obtain ⟨s2, hs2, e2⟩ := hb.2 j hj
      exact ⟨s1 + s2, add_mem hs1 hs2, by simp [Pi.add_apply, e1, e2, mul_add]⟩
    | smul a b _ hb =>
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
        exact mul_mem a.2 (hb.1 j)
      · obtain ⟨s, hs, e⟩ := hb.2 j hj
        refine ⟨(a : E ⊗[F] R) * s, mul_mem a.2 hs, ?_⟩
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, e]
        ring
  · rintro ⟨h1, h2⟩
    have key : ∀ (j : Fin m) (r : 𝓞 E), (j.1 + 1 = m → t ∣ r) → ∀ s ∈ S,
        Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) ∈ Formalism.UG.latS (F := F) R S Λ := by
      intro j r hr s hs
      have hx : (Pi.single j (r : E) : Fin m → E) ∈ Λ := by
        rw [hΛ]; intro i
        by_cases hij : i = j
        · subst hij; exact ⟨r, by simp, hr⟩
        · exact ⟨0, by simp [hij], fun _ => dvd_zero _⟩
      have : (Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) : Fin m → E ⊗[F] R) =
          (⟨s, hs⟩ : S) • (fun i => Formalism.UG.inclE (F := F) R ((Pi.single j (r : E) : Fin m → E) i)) := by
        ext i; by_cases hij : i = j
        · subst hij; simp [Subring.smul_def]
        · simp [hij, Subring.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j.1 + 1 = m
    · obtain ⟨s, hs, e⟩ := h2 j hj
      rw [e, mul_comm]; exact key j t (fun _ => dvd_refl _) s hs
    · simpa using key j 1 (fun h => absurd h hj) (y j) (h1 j)

end GlobalTheory.SplitStab

theorem GlobalTheory.SplitStab.stab_of_split_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k),
    (∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k]) →
    ∀ (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E)),
    (∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r)) →
    ∀ q : Unif k, valuation k (φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E))) = valuation k ((q.1 : 𝒪[k]) : k) →
    valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1 →
    ∀ M : GL (Fin m) (E ⊗[F] v.adicCompletion F), M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 →
    ∀ h h' : Matrix (Fin m) (Fin m) k, M.val.map φ = h → h * h' = 1 →
    (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], u r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s) ↔
      ((∀ r, (h *ᵥ u) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (h *ᵥ u) r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s)) →
    (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔ ∀ r, (h'ᵀ *ᵥ u) r ∈ 𝒪[k]) →
    M ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ) := by
  intro F E _ _ _ _ _ σ v k _ _ _ _ φ hS m t Λ hΛ q hq hq' M hM h h' hh hhh' hA hB
  have hSO : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (c : E) ∈
      Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
  have ht : (t : E) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero, map_zero] at hq
    have h1 : ((q.1 : 𝒪[k]) : k) = 0 := (valuation k).zero_iff.mp hq.symm
    exact q.2.ne_zero (by simpa using h1)
  have hint : ∀ x : k, x ∈ 𝒪[k] ↔ valuation k x ≤ 1 := fun x => Valuation.mem_integer_iff (valuation k) x
  set σ' := Formalism.UG.sigR σ (v.adicCompletion F) with hσ'
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι

  have hchar : ∀ y : Fin m → E ⊗[F] v.adicCompletion F,
      y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ ↔
      (((∀ r, (fun j => φ (y j)) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (fun j => φ (y j)) r0 = φ (ι (t : E)) * s) ∧
        ∀ r, (fun j => φ (σ' (y j))) r ∈ 𝒪[k]) := by
    intro y
    rw [GlobalTheory.SplitStab.mem_latS_iff (F := F) (v.adicCompletion F) _ hSO m t Λ hΛ y]
    simp only [hS]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun r => (h1 r).1, fun r0 hr0 => ?_⟩, fun r => (h1 r).2⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      exact ⟨φ s, hs.1, by rw [e, map_mul]⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun r => ⟨h1 r, h3 r⟩, fun r0 hr0 => ?_⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      have hu : ι (t : E) * ι ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      refine ⟨ι ((t : E)⁻¹) * y r0, ?_, ?_⟩
      · constructor
        · have hu' : φ (ι ((t : E)⁻¹)) * φ (ι (t : E)) = 1 := by rw [← map_mul, mul_comm, hu, map_one]
          rw [map_mul, show φ (y r0) = φ (ι (t : E)) * s from e, ← mul_assoc, hu', one_mul]
          exact hs
        · have hu' : φ (σ' (ι ((t : E)⁻¹))) * φ (σ' (ι (t : E))) = 1 := by
            rw [← map_mul, ← map_mul, mul_comm, hu, map_one, map_one]
          have hv : valuation k (φ (σ' (ι ((t : E)⁻¹)))) = 1 := by
            have := congrArg (valuation k) hu'
            rw [map_mul, hq', mul_one, map_one] at this
            exact this
          rw [map_mul, map_mul]
          exact mul_mem ((hint _).2 hv.le) (h3 r0)
      · rw [← mul_assoc, hu, one_mul]

  have hU : (M.val.map (φ.comp σ'))ᵀ * h = 1 := by
    have h0 : Formalism.UG.cT σ' (M : Matrix (Fin m) (Fin m) _) * 1 * (M : Matrix (Fin m) (Fin m) _) = 1 := hM
    rw [Matrix.mul_one] at h0
    have := congrArg (fun X => X.map φ) h0
    simp only [Formalism.UG.cT] at this
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [← hh]
    simpa [Matrix.transpose_map] using this
  have hh'h : h' * h = 1 := mul_eq_one_comm.mp hhh'
  have hσM : M.val.map (φ.comp σ') = h'ᵀ := by
    have : (M.val.map (φ.comp σ'))ᵀ = h' := by
      calc (M.val.map (φ.comp σ'))ᵀ = (M.val.map (φ.comp σ'))ᵀ * (h * h') := by rw [hhh', Matrix.mul_one]
        _ = h' := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [← this, Matrix.transpose_transpose]
  intro y
  rw [hchar y, hchar]
  have e1 : (fun j => φ (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j)) = h *ᵥ (fun j => φ (y j)) := by
    funext j; rw [RingHom.map_mulVec, hh]; rfl
  have e2 : (fun j => φ (σ' (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j))) = h'ᵀ *ᵥ (fun j => φ (σ' (y j))) := by
    funext j
    have := RingHom.map_mulVec (φ.comp σ') (M : Matrix (Fin m) (Fin m) _) y j
    rw [← hσM]
    exact this
  rw [e1, e2]
  exact and_congr (hA _) (hB _)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc


theorem _root_.GlobalTheory.T.inert_place_local_character_conjugation_inverse : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  first | exact @GlobalTheory.InertFrameLoc.thW_conj | exact GlobalTheory.InertFrameLoc.thW_conj | (intros; apply GlobalTheory.InertFrameLoc.thW_conj <;> assumption)
end
end
