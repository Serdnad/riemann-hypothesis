module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PrimitiveFormFullBranchConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X W N' : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ) (q : σ → Fin N → (Fin d → ℂ) → ℂ) (B O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ),
    IsOpen W → IsOpen N' → closure W ⊆ N' → (∀ i, AnalyticOnNhd ℂ (f i) N') →
    X ∩ N' = {z | z ∈ N' ∧ ∀ i, f i z = 0} →
    (∀ z ∈ X ∩ closure W, A z ∈ B → z ∈ W) →
    (∀ z ∈ X ∩ W, ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
    IsOpen B → (∀ j, AnalyticOnNhd ℂ (a j) B) → AnalyticOnNhd ℂ δ B → (∀ i j, AnalyticOnNhd ℂ (q i j) B) →
    IsOpen O → IsPreconnected O → O ⊆ B → (∀ s ∈ O, δ s ≠ 0) →
    (∀ s ∈ O, (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    AnalyticOnNhd ℂ r O → (∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0) →
    ∀ s ∈ O, ∀ s' ∈ O,
      (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ PrimitiveFormRootFull X W A ℓ δ q s' (r s'))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Finset

theorem multiset_mul_esymm_eq_sum (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map fun x => x ^ a.2).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun x : s => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum s ℂ k)

  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
  MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, MvPolynomial.psum,
  MvPolynomial.aeval_X] at h
  convert h using 4 with a _
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl

theorem PowerSumsEsymmAnalytic.proof : PowerSumsEsymmAnalytic.Statement := by
  intro σ _ V d Z hV hcard hp k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa [Multiset.esymm, Multiset.powersetCard_zero_left] using
      (analyticOnNhd_const (𝕜 := ℂ) (v := (1 : ℂ)) (s := V))
  by_cases hkd : d < k
  · refine (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ))).congr hV fun z hz => ?_
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard z hz]; exact hkd)]
  push Not at hkd
  have hsum : AnalyticOnNhd ℂ (fun z => ((k : ℂ))⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (Z z).esymm a.1 * ((Z z).map fun x => x ^ a.2).sum)) V := by
    refine analyticOnNhd_const.mul (analyticOnNhd_const.mul ?_)
    refine Finset.analyticOnNhd_fun_sum _ fun a ha => ?_
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    refine (analyticOnNhd_const.mul (ih a.1 ha.2)).mul (hp a.2 (by omega) (by omega))
  refine hsum.congr hV fun z _ => ?_
  rw [← multiset_mul_esymm_eq_sum, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), one_mul]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology MvPolynomial

theorem GridProductLowerBound.exists_grid_prod_ne_zero {σ : Type} [Fintype σ] {N k : ℕ} (hk : k ≤ N)
    (v : Fin k → σ → ℂ) (hv : ∀ m, v m ≠ 0) :
    ∃ u : σ → Fin (N + 1), ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i ≠ 0 := by
  classical
  set P : MvPolynomial σ ℂ := ∏ m, ∑ i, X i * C (v m i) with hP
  have hlin : ∀ m, ∑ i, X i * C (v m i) ≠ (0 : MvPolynomial σ ℂ) := by
    intro m h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (hv m)
    have := congrArg (eval (Pi.single i 1)) h
    simp [Pi.single_apply] at this
    exact hi this
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun m _ => hlin m
  let S : σ → Finset ℂ := fun _ => Finset.univ.image fun j : Fin (N + 1) => ((j : ℕ) : ℂ)
  have hS : ∀ i, (S i).card = N + 1 := fun i => by
    simp only [S]
    rw [Finset.card_image_of_injective _ fun a b h => Fin.ext (by exact_mod_cast h)]
    simp
  have htot : P.totalDegree ≤ k := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ m, (∑ i, X i * C (v m i) : MvPolynomial σ ℂ).totalDegree ≤ ∑ _m : Fin k, 1 :=
          Finset.sum_le_sum fun m _ => totalDegree_finsetSum_le fun j _ =>
            (totalDegree_mul _ _).trans (by simp [totalDegree_X, totalDegree_C])
      _ = k := by simp
  have hdeg : ∀ i, P.degreeOf i < (S i).card := fun i => by
    rw [hS i]
    exact Nat.lt_succ_of_le (((degreeOf_le_totalDegree _ _).trans htot).trans hk)
  by_contra hne
  push Not at hne
  refine hP0 (eq_zero_of_eval_zero_at_prod_finset P S hdeg fun x hx => ?_)
  choose u _ hu using fun i => Finset.mem_image.1 (hx i)
  have := hne u
  simp only [hu] at this
  simpa [hP, map_prod] using this

theorem GridProductLowerBound.proof : GridProductLowerBound.Statement := by
  classical
  intro σ _ N Z z₀ hZ hz₀
  obtain ⟨ε, hε, hεZ⟩ : ∃ ε > 0, ∀ x ∈ Z, ε ≤ dist z₀ x := by
    rw [Metric.mem_closure_iff] at hz₀
    push Not at hz₀
    exact hz₀
  obtain ⟨R, hR⟩ := hZ.subset_closedBall z₀
  set K : Set (σ → ℂ) := Metric.closedBall 0 (R + ε / 2) \ Metric.ball 0 (ε / 2) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hK0 : ∀ w ∈ K, w ≠ 0 := by
    rintro w hw rfl
    simp [hK, hε] at hw
  let g : (k : ℕ) → (Fin k → σ → ℂ) → ℝ := fun k v =>
    Finset.univ.sup' Finset.univ_nonempty fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖
  have hbd : ∀ k, ∃ μ > (0 : ℝ), k ≤ N → ∀ v ∈ Set.univ.pi (fun _ : Fin k => K), μ ≤ g k v := by
    intro k
    by_cases hk : k ≤ N
    · rcases (Set.univ.pi fun _ : Fin k => K).eq_empty_or_nonempty with he | hne
      · exact ⟨1, one_pos, fun _ v hv => by simp [he] at hv⟩
      have hgc : Continuous (g k) := Continuous.finset_sup'_apply
        (f := fun (u : σ → Fin (N + 1)) (v : Fin k → σ → ℂ) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖) _
        fun u _ => continuous_norm.comp (continuous_finsetProd _ fun m _ => continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((continuous_apply i).comp (continuous_apply m)))
      obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_univ_pi fun _ => hKc).exists_isMinOn hne hgc.continuousOn
      obtain ⟨u, hu⟩ := GridProductLowerBound.exists_grid_prod_ne_zero hk v₀
        fun m => hK0 _ (hv₀ m (Set.mem_univ _))
      exact ⟨g k v₀, (norm_pos_iff.2 hu).trans_le (Finset.le_sup' (fun u : σ → Fin (N + 1) =>
        ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v₀ m i‖) (Finset.mem_univ u)), fun _ v hv => isMinOn_iff.1 hmin v hv⟩
    · exact ⟨1, one_pos, fun h => absurd h hk⟩
  choose μf hμf0 hμf using hbd
  refine ⟨(Finset.range (N + 1)).inf' ⟨0, Finset.mem_range.2 N.succ_pos⟩ μf,
    (Finset.lt_inf'_iff _).2 fun k _ => hμf0 k, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  intro z hz s hs hcard
  set e := s.equivFin
  set v : Fin s.card → σ → ℂ := fun m => z - (e.symm m : σ → ℂ) with hvdef
  have hv : v ∈ Set.univ.pi fun _ : Fin s.card => K := by
    intro m _
    have hx := hs (e.symm m).2
    have h1 := hεZ _ hx
    have h2 := Metric.mem_closedBall.1 (hR hx)
    have h3 := Metric.mem_ball.1 hz
    have h4 := dist_triangle z₀ z (e.symm m : σ → ℂ)
    have h5 := dist_triangle z z₀ (e.symm m : σ → ℂ)
    rw [dist_comm z₀ z] at h4
    rw [dist_comm] at h2
    simp only [hK, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, hvdef, ← dist_eq_norm,
      not_lt]
    constructor <;> linarith
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖)
  refine ⟨u, ?_⟩
  have hprod : ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) = ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i := by
    rw [← Finset.prod_coe_sort, ← e.symm.prod_comp]
    rfl
  rw [hprod]
  have hle := (Finset.inf'_le μf (Finset.mem_range_succ_iff.2 hcard)).trans (hμf _ hcard v hv)
  simp only [g] at hle
  rwa [hu] at hle

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology
open scoped ContDiff

noncomputable section

namespace AnalyticImplicitChart

theorem pi_surjective_of_linearIndependent {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype ι] {φ : ι → E →L[ℂ] ℂ} (hφ : LinearIndependent ℂ φ) :
    Function.Surjective (LinearMap.pi fun j => (φ j : E →ₗ[ℂ] ℂ)) := by
  classical
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hfx : ∀ x : ι → ℂ, f x = ∑ j, x j * f (Pi.single j 1) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  have h0 : ∑ j, f (Pi.single j 1) • φ j = 0 := by
    ext z
    have := LinearMap.congr_fun hf z
    simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
    rw [hfx] at this
    simpa [mul_comm] using this
  have hc := Fintype.linearIndependent_iff.1 hφ _ h0
  refine LinearMap.ext fun x => ?_
  rw [hfx x]
  simp [hc]

theorem proof : AnalyticImplicitChart.Statement := by
  intro σ ι _ _ h a W hh h0 hli hW
  classical
  set φ : ι → (σ → ℂ) →L[ℂ] ℂ := fun j => fderiv ℂ (h j) a with hφ
  set L : (σ → ℂ) →ₗ[ℂ] (ι → ℂ) := LinearMap.pi fun j => (φ j : (σ → ℂ) →ₗ[ℂ] ℂ) with hL
  have hLs : Function.Surjective L := pi_surjective_of_linearIndependent hli
  set K := LinearMap.ker L with hK
  obtain ⟨q, hq⟩ := K.exists_isCompl
  set d := Module.finrank ℂ K with hd'
  have hd : d + Fintype.card ι = Fintype.card σ := by
    have := L.finrank_range_add_finrank_ker
    have hKk : Module.finrank ℂ K = Module.finrank ℂ (LinearMap.ker L) := rfl
    rw [LinearMap.range_eq_top.2 hLs, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at this
    omega
  set eK : K ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq K (Fin d → ℂ) (by simp [d]) with heK
  set A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (eK.toLinearMap ∘ₗ K.projectionOnto q hq) with hA
  set P : (σ → ℂ) →L[ℂ] (Fin d → ℂ) × (ι → ℂ) := A.prod (ContinuousLinearMap.pi φ) with hP
  have hPinj : Function.Injective P := by
    intro z w hzw
    rw [← sub_eq_zero]
    have h1 : A (z - w) = 0 := by rw [map_sub, sub_eq_zero]; exact congrArg Prod.fst hzw
    have h2 : z - w ∈ K := by
      rw [hK, LinearMap.mem_ker]
      funext j
      have := congrFun (congrArg Prod.snd hzw) j
      simp only [hP, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply] at this
      simp [hL, map_sub, this]
    have h3 : K.projectionOnto q hq (z - w) = 0 := eK.injective (by simpa [hA] using h1)
    rw [Submodule.projectionOnto_apply_of_mem_left hq h2] at h3
    simpa using congrArg Subtype.val h3
  have hPbij : Function.Bijective (P : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ) × (ι → ℂ)) :=
    ⟨hPinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_prod, hd])).1 hPinj⟩
  set Pe : (σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ) :=
    (LinearEquiv.ofBijective _ hPbij).toContinuousLinearEquiv with hPe
  have hPeP : (Pe : (σ → ℂ) →L[ℂ] (Fin d → ℂ) × (ι → ℂ)) = P := by ext1 x; rfl
  set F : (σ → ℂ) → (Fin d → ℂ) × (ι → ℂ) := fun z => (A z, fun j => h j z) with hF
  have hFan : ∀ z, (∀ j, AnalyticAt ℂ (h j) z) → AnalyticAt ℂ F z := fun z hz =>
    (A.analyticAt z).prod (analyticAt_pi_iff.2 hz)
  have hFd : HasFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    rw [hPeP]
    exact A.hasFDerivAt.prodMk (hasFDerivAt_pi.2 fun j => (hh j).differentiableAt.hasFDerivAt)
  have hst : HasStrictFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    have := (hFan a hh).hasStrictFDerivAt; rwa [hFd.fderiv] at this
  set Φ := hst.toOpenPartialHomeomorph F with hΦ
  have hev : ∀ᶠ t in 𝓝 a, (∀ j, AnalyticAt ℂ (h j) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ)) → _) := by
    refine (Filter.eventually_all.2 fun j => (hh j).eventually_analyticAt).and ((show ∀ᶠ t in 𝓝 a, t ∈ W from hW).and ?_)
    exact (hFan a hh).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨Pe, hFd.fderiv.symm⟩)
  obtain ⟨V₀, hV₀, hV₀o, haV₀⟩ := eventually_nhds_iff.1 hev
  set Ψ := Φ.restrOpen V₀ hV₀o with hΨ
  have hΨs : Ψ.source = Φ.source ∩ V₀ := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hΨF : ∀ z, Ψ z = F z := fun z => rfl
  have haΨ : a ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, haV₀⟩
  have hsrc : ∀ t ∈ Ψ.source, (∀ j, AnalyticAt ℂ (h j) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ)) → _) :=
    fun t ht => hV₀ t (hΨs ▸ ht).2
  set O : Set (Fin d → ℂ) := (fun y => (y, (0 : ι → ℂ))) ⁻¹' Ψ.target with hO
  refine ⟨d, A, O, Ψ.source, fun y => Ψ.symm (y, 0), hd,
    Ψ.open_target.preimage (continuous_id.prodMk continuous_const), Ψ.open_source, haΨ,
    fun t ht => (hsrc t ht).2.1, ?_, ?_, ?_⟩
  · intro y hy
    have hp : (y, (0 : ι → ℂ)) ∈ Ψ.target := hy
    obtain ⟨han, -, e', he'⟩ := hsrc _ (Ψ.map_target hp)
    have hFe : HasFDerivAt Ψ (e' : (σ → ℂ) →L[ℂ] _) (Ψ.symm (y, 0)) := by
      rw [he']; exact (hFan _ han).differentiableAt.hasFDerivAt
    have hc : ContDiffAt ℂ ω Ψ.symm (y, 0) :=
      Ψ.contDiffAt_symm hp hFe (hFan _ han).contDiffAt
    have hi : AnalyticAt ℂ (fun y : Fin d → ℂ => (y, (0 : ι → ℂ))) y :=
      analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (g := Ψ.symm) (f := fun y : Fin d → ℂ => (y, (0 : ι → ℂ))) (x := y)
      hc.analyticAt hi
  · intro y hy
    exact congrArg Prod.fst (Ψ.right_inv (show (y, (0 : ι → ℂ)) ∈ Ψ.target from hy))
  · ext z
    constructor
    · rintro ⟨hzV, hz0⟩
      have hFz : F z = (A z, 0) := by
        simp only [hF, Prod.mk.injEq, true_and]; funext j; exact hz0 j
      refine ⟨A z, ?_, ?_⟩
      · show (A z, (0 : ι → ℂ)) ∈ Ψ.target
        rw [← hFz, ← hΨF]; exact Ψ.map_source hzV
      · show Ψ.symm (A z, 0) = z
        rw [← hFz, ← hΨF]; exact Ψ.left_inv hzV
    · rintro ⟨y, hy, rfl⟩
      have hp : (y, (0 : ι → ℂ)) ∈ Ψ.target := hy
      refine ⟨Ψ.map_target hp, fun j => ?_⟩
      have := congrFun (congrArg Prod.snd (Ψ.right_inv hp)) j
      simpa [hΨF, hF] using this

end AnalyticImplicitChart

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormFullRootFactor.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (W : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (C E : (Fin d → ℂ) → ℂ → ℂ),
        IsOpen W ∧ w ∈ W ∧ IsOpen B ∧ A w ∈ B ∧
        (∀ t ∈ B, ∀ T : ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => C u.1 u.2) (t, T) ∧
          AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => E u.1 u.2) (t, T)) ∧
        (∀ t ∈ B, ∀ T : ℂ, C t T * E t T = T ^ N + ∑ j, a j t * T ^ (j : ℕ)) ∧
        ∀ t ∈ B, δ t ≠ 0 → ∀ τ : ℂ, τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0 →
          (C t τ = 0 ↔ PrimitiveFormRootFull X W A ℓ δ q t τ) ∧
          (E t τ = 0 ↔ ¬ PrimitiveFormRootFull X W A ℓ δ q t τ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

theorem HolomorphicIsolatedFibreOpen.proof (hPS : ProperHolomorphicSurjective.Statement) :
    HolomorphicIsolatedFibreOpen.Statement := by
  intro k U g u hU hu hg ⟨W, hW, hiso⟩ V hV
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall u r ⊆ U ∩ W ∩ V :=
    nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hu) hW) hV)
  have hgc : ContinuousOn g (closedBall u r) := hg.continuousOn.mono fun x hx => (hrsub hx).1.1

  have hSc : IsCompact (g '' sphere u r) :=
    (isCompact_sphere u r).image_of_continuousOn (hgc.mono sphere_subset_closedBall)
  have hnot : g u ∉ g '' sphere u r := by
    rintro ⟨s, hs, hgs⟩
    have hsK := hrsub (sphere_subset_closedBall hs)
    have := hiso s hsK.1.2 hsK.1.1 hgs
    subst this
    rw [mem_sphere, dist_self] at hs
    exact hr.ne' hs.symm
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hSc.isClosed.isOpen_compl (g u) hnot

  have key : ∀ v ∈ closedBall u r, g v ∈ ball (g u) ε → v ∈ ball u r := by
    intro v hv hgv
    rcases (mem_closedBall.1 hv).lt_or_eq with h | h
    · exact h
    · exact (hεsub hgv ⟨v, mem_sphere.2 h, rfl⟩).elim
  have hΩ : IsOpen (ball u r ∩ g ⁻¹' ball (g u) ε) :=
    (hgc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hproper : ∀ L ⊆ ball (g u) ε, IsCompact L →
      IsCompact ((ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L) := by
    intro L hLD hL
    have heq : (ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L = closedBall u r ∩ g ⁻¹' L := by
      ext v
      constructor
      · rintro ⟨⟨hv, _⟩, hvL⟩
        exact ⟨ball_subset_closedBall hv, hvL⟩
      · rintro ⟨hv, hvL⟩
        exact ⟨⟨key v hv (hLD hvL), hLD hvL⟩, hvL⟩
    rw [heq]
    exact (isCompact_closedBall u r).of_isClosed_subset
      (hgc.preimage_isClosed_of_isClosed isClosed_closedBall hL.isClosed) Set.inter_subset_left
  have hsurj := hPS k _ _ g hΩ ⟨u, by exact Set.mem_preimage.mpr (mem_ball_self hr), by exact Set.mem_preimage.mpr (mem_ball_self hε)⟩ isOpen_ball
    (convex_ball _ _).isPreconnected (hg.mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).1.1)
    (fun x hx => hx.2) hproper
  refine Filter.mem_of_superset (ball_mem_nhds _ hε) ?_
  rw [← hsurj]
  exact Set.image_mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalModelExists.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime → Nonempty (NormalModel J)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
