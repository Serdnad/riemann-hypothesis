module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle006
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagRatioFieldEq.proof (h₁ : RatioFieldSpan.Statement) (h₂ : HodgeFlagSpan.Statement)
    (h₃ : PivotMinorFlag.Statement) (h₄ : GenLeadMinor0NeZero.Statement) : HodgeFlagRatioFieldEq.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B c hc

  have hq : ∀ (τ : Ψ) (i : Fin (D.N - 1)),
      IntermediateField.adjoin Ω (Set.range fun m =>
          Pl.pluecker0 B τ i m / Pl.pluecker0 B τ i (c (Sum.inr (τ, i)))) =
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) := by
    intro τ i
    have hspan := h₂ II Ψ K ι Ω E D Pl H B τ i
    obtain ⟨S₀, hS₀⟩ := h₃ _ D.N (genMat0Fr Ω Ψ D.N D.j τ) i (Fin.castLE (Nat.sub_le D.N 1) i) le_rfl
    refine h₁ Ω Pl.ΩY _ _ _ _ _ _ hspan (Submodule.subset_span ⟨_, rfl⟩) ?_ (hc (Sum.inr (τ, i)))
      (h₄ Ω Ψ D.N D.j τ i)
    rw [hspan]
    exact Submodule.subset_span ⟨S₀, by rw [_root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor, hS₀]⟩
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | q, t⟩, rfl⟩
    · show Pl.ofΩ (D.y ⟨k, t⟩) / Pl.ofΩ (D.y ⟨k, c (Sum.inl k)⟩) ∈ _
      rw [PlueckerData.ofΩ_eq, PlueckerData.ofΩ_eq, ← map_div₀]
      exact IntermediateField.algebraMap_mem _ _
    · have hmem : Pl.pluecker0 B q.1 q.2 t / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2))) ∈
          IntermediateField.adjoin Ω (Set.range fun m =>
            Pl.pluecker0 B q.1 q.2 m / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2)))) :=
        IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩
      rw [hq] at hmem
      refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
      rintro _ ⟨S, rfl⟩
      exact ⟨(q.1, ⟨q.2, S⟩), rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨τ, i, S⟩, rfl⟩
    have hmem : flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i ∈
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) :=
      IntermediateField.subset_adjoin _ _ ⟨S, rfl⟩
    rw [← hq] at hmem
    refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
    rintro _ ⟨m, rfl⟩
    exact ⟨⟨Sum.inr (τ, i), m⟩, rfl⟩

theorem HodgeFlagRatioFieldEq.full : HodgeFlagRatioFieldEq.Statement :=
  HodgeFlagRatioFieldEq.proof RatioFieldSpan.full HodgeFlagSpan.full PivotMinorFlag.full GenLeadMinor0NeZero.full

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem RegAboveWeight.proof (hBd : BdPtsNull.Statement) (hDiv : DivisorPreimageNull.Statement) :
    RegAboveWeight.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, t₀, ht₀, hb⟩ := GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof
    GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof X.M.Xc D.n X.M.atlas X.S.R X.S.ρ
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < t₀ ∧ 0 ≤ X.S.K t :=
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀)).and
      (X.S_tied.K_tendsto.eventually_ge_atTop 0)
  obtain ⟨t₂, ht₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  refine ⟨t₂, ht₂, D.Bd ∪ {z | X.M.proj z ∉ X.S.R.Yo}, ?_, fun t ht htt z hz hzN => ?_⟩
  ·
    intro Ψ' hΨ'
    refine measure_mono_null (fun y hy => ?_)
      (measure_union_null (hBd II Ψ K ι Ω E D Ψ' hΨ') (hDiv K ι _ _ X.M X.S.R Ψ' hΨ'))
    obtain ⟨z, hz, hzN, hzy⟩ := hy
    rcases hzN with h | h
    · exact Or.inl ⟨z, hz, h, hzy⟩
    · exact Or.inr ⟨z, hz, h, hzy⟩
  obtain ⟨htt₀, hK⟩ : t < t₀ ∧ 0 ≤ X.S.K t := hsub ⟨ht, htt⟩
  have hBdz : z ∉ D.Bd := fun h => hzN (Or.inl h)
  have hY : X.M.proj z ∈ X.S.R.Yo := by
    by_contra h
    exact hzN (Or.inr h)
  have hXo : z ∈ D.Xo := Set.mem_sdiff_of_mem hz hBdz

  obtain ⟨k, hk⟩ := X.S.R.cover (X.M.proj z)
  have hkm := X.S.R.inner_subset_mid k hk
  have hε : 0 ≤ X.S.e1 t := ht.le.trans (X.S.e1_ge t ht)

  have h1 := ((hb t ht htt₀).2 (X.S.K t) hK k (X.M.proj z) hkm).2.2 hY

  have h2 := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue X.S.R.toPotentialCharts
    (fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x) hε hkm
  have h3 : X.S.regWeight t (X.M.proj z) = X.S.R.glue
      (fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x) (X.S.e1 t) (X.M.proj z) := rfl
  have hη := X.S.cutoff.eq_zero k (X.M.proj z) hk
  simp only [hη, mul_zero, add_zero] at h2

  have h4 := X.S.ph_eq z ⟨hXo, hz⟩ hY
  have h5 : phMu X.H z = Real.log ((muLine X.H).h z) := rfl
  rw [h3, h5]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi levi_comp)
open scoped ContDiff

theorem APrimeChartLeviLocal.proof (hP : ProjHoloLocal.Statement) : APrimeChartLeviLocal.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X kc y₀ hy₀
  classical
  set ψ := X.S.R.chart kc with hψ
  have hcompat : ReciprocityTheory.AnForm.M.IsCompatChart X.M.atlas ψ := X.S.R.compat kc
  have hsm : IsSmoothHerm D.A' := D.A'_pos.1
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (D.A'.h y) with hφ

  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := X.M.sections (ψ.symm y₀)
  set W : Set (Fin D.n → ℂ) := ψ.target ∩ ψ.symm ⁻¹' U with hW
  have hWo : IsOpen W := ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target hUo
  have hy₀W : y₀ ∈ W := ⟨hy₀, hxU⟩
  set g : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (ψ.symm u) with hg
  have hgan : ∀ u ∈ W, AnalyticAt ℂ g u := fun u hu =>
    NineStatements.APrimeLeviCharts.analyticAt_sec X.M hcompat hUo hsh hu.1 hu.2
  have hgC : ∀ u ∈ W, ContDiffAt ℝ ∞ (φ ∘ g) u := by
    intro u hu
    have hb := (hs _ hu.2).1.1
    have h1 : ContDiffAt ℝ ∞ D.A'.h (g u) :=
      (hsm.contDiffAt (NineStatements.APrimeLeviCharts.isOpen_blocks.mem_nhds hb)).of_le
        (WithTop.coe_le_coe.2 le_top)
    exact (h1.log (D.A'.pos _ hb).ne').comp u (hgan u hu).restrictScalars.contDiffAt
  refine ⟨W, hWo, hy₀W, φ ∘ g, fun u hu => (hgC u hu).contDiffWithinAt, ?_⟩
  intro z hz hzs hzW w v hv
  obtain ⟨γ, hγ0, hγw, hγev, hγv⟩ := hv
  obtain ⟨W', hWo', hzW', F, hFd, hF⟩ := hP II Ψ K ι Ω E D X.M ψ hcompat z hz hzs
  set y₁ := ψ (X.M.proj z) with hy₁

  have hWγ : ∀ᶠ t in 𝓝 (0 : ℂ), γ t ∈ W' :=
    hγw.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hWo'.mem_nhds hzW')
  obtain ⟨S, hS, hSp⟩ := (hγev.and hWγ).exists_mem
  have hγan : AnalyticAt ℂ γ 0 :=
    DifferentiableOn.analyticAt (fun t ht => (hSp t ht).1.1.differentiableWithinAt) hS
  set β : ℂ → Fin D.n → ℂ := fun t => F (γ t) with hβ
  have hβan : AnalyticAt ℂ β 0 :=
    DifferentiableOn.analyticAt (fun t ht =>
      ((hFd.differentiableAt (hWo'.mem_nhds (hSp t ht).2)).comp t (hSp t ht).1.1).differentiableWithinAt) hS
  have hβψ : ∀ t ∈ S, X.M.proj (γ t) ∈ ψ.source ∧ ψ (X.M.proj (γ t)) = β t := fun t ht =>
    hF (γ t) ⟨(hSp t ht).2, (hSp t ht).1.2⟩
  have hβ0 : β 0 = y₁ := by
    rw [← (hβψ 0 (mem_of_mem_nhds hS)).2, hγ0]
  have hβv : HasDerivAt β v 0 := by
    refine hγv.congr_of_eventuallyEq ?_
    filter_upwards [hS] with t ht
    exact (hβψ t ht).2.symm

  have hβN : ∀ᶠ t in 𝓝 (0 : ℂ), β t ∈ W :=
    hβan.continuousAt.preimage_mem_nhds (by rw [hβ0]; exact hWo.mem_nhds hzW)
  have hrelC : ∀ᶠ t in 𝓝 (0 : ℂ), (∀ k, ∃ i, g (β t) ⟨k, i⟩ ≠ 0) ∧
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ γ t = torusSmul c (g (β t)) := by
    filter_upwards [hS, hβN] with t ht htN
    have e₁ := hs _ htN.2
    have hpr : X.M.proj (γ t) = ψ.symm (β t) := by
      rw [← (hβψ t ht).2, ψ.left_inv (hβψ t ht).1]
    exact ⟨e₁.1.1, (X.M.fibre _ e₁.1 _ (hSp t ht).1.2).1 (by rw [e₁.2, hpr])⟩

  set L₁ : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0 with hL₁
  have hL0 : L₁ 0 = 0 := map_zero L₁
  have hLt : Tendsto L₁ (𝓝 0) (𝓝 0) := by
    have h := L₁.continuous.tendsto 0
    rwa [hL0] at h
  set e₁ : Fin 1 → ℂ := fun _ => 1 with he₁
  have hLe : L₁ e₁ = 1 := rfl
  have hτ₁ : AnalyticAt ℂ (γ ∘ L₁) 0 := hγan.comp_of_eq (L₁.analyticAt 0) hL0
  have hβL : AnalyticAt ℂ (β ∘ L₁) 0 := hβan.comp_of_eq (L₁.analyticAt 0) hL0
  have hβL0 : (β ∘ L₁) 0 = y₁ := by simp [hL0, hβ0]
  have hτ₂ : AnalyticAt ℂ (g ∘ (β ∘ L₁)) 0 := (hgan y₁ (hy₁ ▸ hzW)).comp_of_eq hβL hβL0

  have hγD : HasFDerivAt (γ ∘ L₁) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).comp L₁) 0 := by
    have h := hγw.hasFDerivAt
    rw [← hL0] at h
    exact h.comp 0 L₁.hasFDerivAt
  have s1 := levi_comp (φ := φ) e₁ hτ₁
    (by simp only [Function.comp_apply, hL0, hγ0]
        exact NineStatements.APrimeLeviCharts.contDiffAt_log_h hsm hz.1)
  rw [hγD.fderiv] at s1
  simp only [Function.comp_apply, hL0, hγ0, ContinuousLinearMap.coe_comp', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, hLe, one_smul] at s1

  have hβD : HasFDerivAt (β ∘ L₁) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v).comp L₁) 0 := by
    have h := hβv.hasFDerivAt
    rw [← hL0] at h
    exact h.comp 0 L₁.hasFDerivAt
  have s3 := levi_comp (φ := φ ∘ g) e₁ hβL
    (by rw [hβL0]; exact (hgC y₁ (hy₁ ▸ hzW)).of_le (WithTop.coe_le_coe.2 le_top))
  rw [hβD.fderiv, hβL0] at s3
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, hLe, one_smul] at s3

  have s2 := NineStatements.APrimeLeviCharts.levi_log_h_torus hsm hτ₁ hτ₂ (hLt.eventually hrelC) e₁
  rw [← s1]
  exact s2.trans s3

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarChartSemipos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt), ∃ c : ℝ, 0 < c ∧ ∀ (B p q : ℕ) (t δ : ℝ),
      X.M.atlas.Smooth (X.S.regWeight t) →
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) →
      (q : ℝ) * δ ≤ p * c →
      IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]


namespace Line

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) → IsSmoothHerm (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def OmNPoly.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      ∃ v d : ℕ → ℝ → ℝ,
        v 0 = (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
          (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => X.Cd.cuspWeight z / 2)) ∧
        d 0 = (fun t => geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n) ∧
        ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ),
          X.Vb B 1 q t = ∑ i ∈ Finset.range (D.n + 1), v i t * (1 / (q : ℝ)) ^ i ∧
          X.degN B 1 q t = ∑ i ∈ Finset.range (D.n + 1), d i t * (1 / (q : ℝ)) ^ i

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def StokesLimitTTop.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B → 1 ≤ p → p ≤ q →
      ∃ L : ℝ, Tendsto (X.topN B p q) (𝓝[>] 0) (𝓝 L)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def StokesLimitTVb.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    1 ≤ p → p ≤ q → ∃ L : ℝ, Tendsto (X.Vb B p q) (𝓝[>] 0) (𝓝 L)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

namespace ComponentSetting

variable (X : ComponentSetting D O Lt)

def mixN (B k : ℕ) (t : ℝ) : ℝ :=
  II K ι (mCoordIdeal D.y) (D.n + 1) fun j => if (j : ℕ) < k then muReg X.H X.S B t else D.A'

end ComponentSetting

def TopNMixedExpand.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    IsIntersectionSystem II → 1 ≤ p → p ≤ q →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), X.topN B p q t =
        ∑ k ∈ Finset.range (D.n + 2),
          ((D.n + 1).choose k : ℝ) * ((p : ℝ) / q) ^ (D.n + 1 - k) * X.mixN B k t

def TopNMixedLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      ∀ k : ℕ, k ≤ D.n → ∃ L : ℝ, Tendsto (X.mixN B k) (𝓝[>] 0) (𝓝 L)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
