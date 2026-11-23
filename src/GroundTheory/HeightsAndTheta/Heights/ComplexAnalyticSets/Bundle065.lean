module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import Mathlib.Analysis.Analytic.Order
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Length
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ) : Submonoid (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
  (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl.map
    ((Ideal.Quotient.mk M.ideal).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom)

theorem mk_rename_mem_normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    Ideal.Quotient.mk M.ideal (rename Sum.inl f) ∈ normalModelSubmonoid M q :=
  Submonoid.mem_map_of_mem _ (show f ∈ (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl from
    fun h ↦ hf (RingHom.mem_ker.1 h))

theorem zero_not_mem_normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (hq : q ∈ zeroSet J) :
    (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
  rintro ⟨f, hf, h0⟩
  apply hf
  refine RingHom.mem_ker.2 (hq f ?_)
  rw [← M.comap_eq, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  exact h0

def NormalisationModelLocalization.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime →
      ∃ e : curveNormalisation J q ≃+* Localization (normalModelSubmonoid M q),
        ∀ f : MvPolynomial (Fin n) ℂ,
          e (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)) =
            algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))
              (Ideal.Quotient.mk M.ideal (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchImageNhdOffCentre.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ c : VarBranch I 1 q, ∀ x ∈ c.image ∩ N, x ≠ q →
        ∃ U ∈ 𝓝 x, zeroSet I ∩ U ⊆ c.image

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchInCurveComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ J ∈ I.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) ∧
        ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def PrimeBranchDimOne.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedBranchInOneBranch.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q)
    (ν : VarBranch I 1 q) (ρ : ℝ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 → 0 < ρ →
    (∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → ν.toFun (fun _ ↦ τ) ∈ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ∃ b, ∃ ρ' > 0, ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ' → ν.toFun (fun _ ↦ τ) ∈ (c b).image

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

variable {n : ℕ}

def branchOrder {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (c : VarBranch I 1 q)
    (f : MvPolynomial (Fin n) ℂ) : ℕ∞ :=
  analyticOrderAt (fun τ : ℂ ↦ eval (c.toFun fun _ ↦ τ) f) 0

theorem branchOrder_eq_of_vanishesToOrder {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) (f : MvPolynomial (Fin n) ℂ) (k : ℕ)
    (h : VanishesToOrder (fun t ↦ eval (c.toFun t) f) c.radius k) : branchOrder c f = k := by
  obtain ⟨H, hHd, hH0, hF⟩ := h
  let ι : ℂ → (Fin 1 → ℂ) := fun τ _ ↦ τ
  have hιd : Differentiable ℂ ι := differentiable_pi.2 fun _ ↦ differentiable_id
  have hball : ∀ τ ∈ Metric.ball (0 : ℂ) c.radius, ι τ ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
    intro τ hτ
    simpa [ι, Metric.mem_ball, dist_zero_right, pi_norm_const] using hτ
  have hg : AnalyticAt ℂ (H ∘ ι) 0 :=
    (hHd.comp hιd.differentiableOn hball).analyticAt (Metric.ball_mem_nhds 0 c.radius_pos)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), eval (c.toFun (ι τ)) f = (τ - 0) ^ k • (H ∘ ι) τ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) c.radius_pos] with τ hτ
    refine (hF _ (hball τ hτ)).trans ?_
    simp [ι]
  have hF' : AnalyticAt ℂ (fun τ : ℂ ↦ eval (c.toFun (ι τ)) f) 0 :=
    AnalyticAt.congr (((analyticAt_id.sub analyticAt_const).pow k).smul hg) (hev.mono fun τ h ↦ h.symm)
  exact hF'.analyticOrderAt_eq_natCast.2
    ⟨H ∘ ι, hg, hH0 _ (hball 0 (Metric.mem_ball_self c.radius_pos)), hev⟩

def BranchNormalisation.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    IsRadicalAt I q → 0 < m →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ringKrullDim (curveLocalRing I q) = 1 ∧
      (∀ f : MvPolynomial (Fin n) ℂ, (∀ b, branchOrder (c b) f ≠ ⊤) →
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q)) ∧
      ∃ e : Fin m ≃ MaximalSpectrum (curveNormalisation I q), ∀ b,
        Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ (e b).asIdeal) = 1 ∧
        ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime (e b).asIdeal)
              (algebraMap (curveNormalisation I q) (Localization.AtPrime (e b).asIdeal)
                (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
            branchOrder (c b) f

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceLength.proof (hV : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement)
    (hR : SliceReducedGeneral.Statement) (hM : SliceMultGeneral.Statement) :
    SliceLength.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  obtain ⟨f₁, hf₁W, hf₁⟩ := hR n d J W u hJ hdim hu hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hM n d J W u hJ hdim hu hW
  have hf : f₁ * f₂ ∉ W := fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W
  have hUo : IsOpen {x : Fin n → ℂ | eval x (f₁ * f₂) ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f₁ * f₂)) continuous_const
  refine ⟨{x | eval x (f₁ * f₂) ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W (f₁ * f₂) x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (zeroSet W ∩ {x | eval x (f₁ * f₂) ≠ 0}) := ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro q ⟨hqW, hqf⟩
    rw [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hqf
    obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf₁ q hqW hqf.1
    obtain ⟨O₂, -, hO₂d, hO₂⟩ := hf₂ q hqW hqf.2
    exact (hO₁d.inter_of_isOpen_left hO₂d hO₁o).mono fun L (hL : L ∈ O₁ ∩ O₂) => ⟨hO₁ L hL.1, hO₂ L hL.2⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

theorem SliceBranches.proof (hI : IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement)
    (hB : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) (hM : SliceMatricesOpen.Statement)
    (hC : ImplicitCurve.Statement) : SliceBranches.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U Λ hUo hUd hΛ
  obtain ⟨N₁, hN₁, hcov₁⟩ := hcov
  obtain ⟨V, hV, hVd⟩ := hI n d J W u p m γ hJ hdim hu hW hp hsl
  have hOp : interior (N₁ ∩ V) ∈ 𝓝 p := interior_mem_nhds.2 (inter_mem hN₁ hV)
  obtain ⟨y, hyO, hyW, hyU⟩ := mem_closure_iff_nhds.1 (hUd hp) _ hOp
  obtain ⟨q, ⟨hqO, hqU⟩, hqW, hqs⟩ := mem_closure_iff_nhds.1 (hVd ⟨hyW, (interior_subset hyO).2⟩)
    (interior (N₁ ∩ V) ∩ U) (inter_mem (isOpen_interior.mem_nhds hyO) (hUo.mem_nhds hyU))
  have hqN : N₁ ∈ 𝓝 q := mem_of_superset (mem_interior_iff_mem_nhds.1 hqO) fun x hx => hx.1
  choose s hs hs0 hsq hsinj using hqs
  obtain ⟨hGo, hGne⟩ := hM n d m (fun b => (γ b).toFun) s
    (fun b => (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds (hs b))) hsinj
  obtain ⟨L, hLG, hLΛ⟩ := (hΛ q ⟨hqW, hqU⟩).inter_open_nonempty _ hGo hGne
  choose r hr φ hφd hφ0 hφ P hP hPφ using fun b =>
    hC n d (γ b).toFun (γ b).radius L (s b) (γ b).differentiableOn (hs b) (hLG b)
  choose ε hεpos hεP using fun b =>
    hB n (d + 1) J u p q m γ hJ hdim hu ⟨N₁, hqN, hcov₁⟩ hdisj b (s b) (hs b) (hsq b) (P b) (hP b)
  have hφ0' : ∀ b, ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) (r b), φ b τ 0 = τ 0 := fun b τ hτ => by
    rw [(hφ b τ hτ).2.1, hs0 b, zero_add]
  let c : Fin m → VarBranch (sliceIdeal J L q) 1 q := fun b =>
    { radius := r b
      radius_pos := hr b
      toFun := fun τ => (γ b).toFun (φ b τ)
      differentiableOn := (γ b).differentiableOn.comp (hφd b) fun τ hτ => (hφ b τ hτ).1
      injOn := fun τ hτ τ' hτ' h => by
        have h0 := congrArg (fun t => t 0) ((γ b).injOn (hφ b τ hτ).1 (hφ b τ' hτ').1 h)
        simp only [hφ0' b τ hτ, hφ0' b τ' hτ'] at h0
        funext i
        rwa [Subsingleton.elim i 0]
      map_zero := by simp only [hφ0 b, hsq b]
      mapsTo := fun τ hτ => by
        rw [zeroSet_sliceIdeal]
        exact ⟨(γ b).mapsTo (hφ b τ hτ).1, by rw [Set.mem_ofPred_eq, (hφ b τ hτ).2.2, hsq b]⟩ }
  have himg : ∀ b, (c b).image ⊆ (γ b).image := by
    rintro b _ ⟨τ, hτ, rfl⟩
    exact ⟨φ b τ, (hφ b τ hτ).1, rfl⟩
  refine ⟨q, ⟨hqW, hqU⟩, L, hLΛ, c, ⟨N₁ ∩ ⋂ b, Metric.ball q (ε b),
    inter_mem hqN (iInter_mem.2 fun b => Metric.ball_mem_nhds q (hεpos b)), ?_⟩,
    fun b b' hbb' x hx => hdisj b b' hbb' ⟨himg b hx.1, himg b' hx.2⟩, fun b => ?_⟩
  · rintro x ⟨hxs, hxN, hxε⟩
    rw [zeroSet_sliceIdeal] at hxs
    obtain ⟨b, t, ht, rfl⟩ : ∃ b, ∃ t ∈ Metric.ball 0 (γ b).radius, (γ b).toFun t = x := by
      simpa [VarBranch.image] using hcov₁ ⟨hxs.1, hxN⟩
    obtain ⟨τ, hτ, rfl⟩ := hPφ b t (hεP b t ht (Set.mem_iInter.1 hxε b))
      (by rw [hxs.2, hsq b])
    exact Set.mem_iUnion.2 ⟨b, τ, hτ, rfl⟩
  · obtain ⟨H, hHd, hH0, hHe⟩ := hord b
    refine ⟨fun τ => H (φ b τ), hHd.comp (hφd b) (fun τ hτ => (hφ b τ hτ).1),
      fun τ hτ => hH0 _ (hφ b τ hτ).1, fun τ hτ => ?_⟩
    show linEval u ((γ b).toFun (φ b τ)) = τ 0 ^ ord b * H (φ b τ)
    have h := hHe _ (hφ b τ hτ).1
    rw [hφ0' b τ hτ] at h
    exact h

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial CategoryTheory

def CMProjDimCriterion.Statement : Prop :=
  ∀ (n : ℕ) (I Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q →
    (IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q ⧸
          I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))) ℓ ∧
        (ℓ : ℕ∞) ≤ (I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))).height)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitOffZero.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    Disjoint (tsupport f) (zeroSet J ∩ {x | linEval u x = 0}) →
      Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0) (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

def CMHeightAddDim.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (J : Ideal B), J ≠ ⊤ →
    (J.height : WithBot ℕ∞) + ringKrullDim (B ⧸ J) = ringKrullDim B

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

noncomputable section

def CMLengthParameters.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime] (d : ℕ) (x : Fin d → B),
    minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
    Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
      Module.length B (B ⧸ Ideal.span (Set.range x)) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)

end

end GroundTheory.Heights₂.Heights
end
