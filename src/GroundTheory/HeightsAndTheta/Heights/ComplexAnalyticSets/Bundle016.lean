module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Analysis.Analytic.Composition
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def MaximalCountUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    ∀ x ∈ Y, {x' | x' ∈ Y ∧ A x' = A x}.encard = N →
      ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y ∈ O, A (h y) = y) ∧ Y ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def OpenProjectionDominantComponents.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ w ∈ X ∩ B,
    ∃ (n : ℕ) (Y : Fin n → Set (σ → ℂ)),
      (∀ i, IsAnalyticNear (Y i) w ∧ GermIrreducibleAt (Y i) w ∧
        ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j) ∧
      ∃ W ∈ 𝓝 w, X ∩ B ∩ W = (⋃ i, Y i) ∩ W

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ParametrisationSheetsConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
    IsLocalParametrisation X w B A D δ N → GermIrreducibleAt X w →
      IsPreconnected {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def RegularLocusDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
    ∃ N : Set (σ → ℂ), IsOpen N ∧ w ∈ N ∧
      ∀ B : Set (σ → ℂ), IsOpen B → B ⊆ N → X ∩ B ⊆ closure (regLocus (X ∩ B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def SheetPieceProductAnalytic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ)
    (U V : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ),
    IsLocalParametrisation X w B A D δ N → IsOpen U → IsOpen V →
    {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V → {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅ →
    ∃ f : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ f (A ⁻¹' D) ∧
      ∀ z, A z ∈ D → δ (A z) ≠ 0 →
        f z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = A z}, (ℓ z - ℓ x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def SheetPieceReachesCentre.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ)
    (U V : Set (σ → ℂ)),
    IsLocalParametrisation X w B A D δ N → IsOpen U → IsOpen V →
    {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V → {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅ →
    ({x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U).Nonempty →
      w ∈ closure ({x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedFibreSections.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
    IsLocalParametrisation X w B A D δ N → ∀ y₀ ∈ D, δ y₀ ≠ 0 →
    ∃ (r : ℝ) (g : Fin N → (Fin d → ℂ) → σ → ℂ), 0 < r ∧ Metric.ball y₀ r ⊆ D ∧
      (∀ y ∈ Metric.ball y₀ r, δ y ≠ 0) ∧ (∀ i, AnalyticOnNhd ℂ (g i) (Metric.ball y₀ r)) ∧
      ∀ y ∈ Metric.ball y₀ r, Function.Injective (fun i => g i y) ∧
        {x | x ∈ X ∩ B ∧ A x = y} = Set.range (fun i => g i y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

def PrimitiveFormRemainder.analyticSubring (d : ℕ) (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g y₀}
  mul_mem' ha hb := ha.mul hb
  one_mem' := analyticAt_const
  add_mem' ha hb := ha.add hb
  zero_mem' := analyticAt_const
  neg_mem' ha := ha.neg

theorem PrimitiveFormRemainder.proof (hSWD : SeparateWeierstrassDivision.Statement) :
    PrimitiveFormRemainder.Statement := by
  classical
  intro σ _ w d A ℓ N δ q n c f hδ hq hc hW hf
  obtain ⟨v, r, -, hr, hev⟩ := hSWD σ d (A w) w n c (fun x => f x.2) hc hW
    (hf.comp (analyticAt_snd (p := (A w, w))))
  set S := PrimitiveFormRemainder.analyticSubring d (A w)

  let s : ((i : σ) → Fin (n i)) → ℕ := fun α => ∑ i, (α i : ℕ)
  let M : ℕ := ∑ i, n i
  have hsM : ∀ α, s α ≤ M := fun α => Finset.sum_le_sum fun i _ => (α i).isLt.le
  let Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ)
  let R : Polynomial ((Fin d → ℂ) → ℂ) :=
    ∑ α, C (r α * δ ^ (M - s α)) * ∏ i, Q i ^ (α i : ℕ)
  refine ⟨M, R, ?_, ?_⟩
  ·
    have hC : ∀ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g (A w) → C g ∈ lifts S.subtype := fun g hg =>
      C_mem_lifts S.subtype ⟨g, hg⟩
    have hR : R ∈ lifts S.subtype := by
      refine Subsemiring.sum_mem _ fun α _ => Subsemiring.mul_mem _ (hC _ ((hr α).mul (hδ.pow _)))
        (Subsemiring.prod_mem _ fun i _ => Subsemiring.pow_mem _ ?_ _)
      exact Subsemiring.sum_mem _ fun j _ =>
        Subsemiring.mul_mem _ (hC _ (hq i j)) (X_pow_mem_lifts _ _)
    intro k
    obtain ⟨g, hg⟩ := (lifts_iff_coeff_lifts R).1 hR k
    rw [← hg]
    exact g.2
  ·
    have hcont : Continuous fun z : σ → ℂ => (A z, z) := A.continuous.prodMk continuous_id
    filter_upwards [(hcont.tendsto w).eventually hev] with z hz hWz hqz
    have hf' : f z = ∑ α, r α (A z) * ∏ i, z i ^ (α i : ℕ) := by
      rw [hz]; simp [hWz]
    have hQ : ∀ i, (Q i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z) = δ (A z) * z i := by
      intro i
      simp [Q, eval₂_finsetSum, hqz i]
    simp only [R, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_finsetProd, eval₂_pow, hQ, hf', Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [Pi.evalRingHom_apply, Pi.mul_apply, Pi.pow_apply, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [← pow_mul_pow_sub (δ (A z)) (hsM α)]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem subset_closure_nonvanishing_of_open {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hDc : IsPreconnected D) (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hδ : AnalyticOnNhd ℂ δ D) (hne : ∃ y ∈ D, δ y ≠ 0) :
    Y ⊆ closure {x | x ∈ Y ∧ δ (A x) ≠ 0} := by
  obtain ⟨y₁, hy₁D, hy₁⟩ := hne
  intro x hx
  rw [mem_closure_iff_nhds]
  intro V hV
  by_contra hempty
  have hzero : δ =ᶠ[𝓝 (A x)] 0 := by
    filter_upwards [hopen x hx V hV] with y hy
    obtain ⟨x', ⟨hx'Y, hx'V⟩, rfl⟩ := hy
    by_contra h0
    exact hempty ⟨x', hx'V, hx'Y, h0⟩
  exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hmaps hx) hzero hy₁D)

theorem ProperOpenProjectionCover.proof (hbranch : ProperOpenProjectionBranchLocus.Statement)
    (hcount : UnbranchedProperCountConstant.Statement) : ProperOpenProjectionCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨δ, hδ, hne, hsec⟩ := hbranch σ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨N, hN⟩ := hcount σ (X ∩ B) d A D δ hD hDc hmaps hprop hδ (fun x hx hx0 => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hsec x hx hx0
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hXV⟩)
  exact ⟨δ, N, hδ, hne, hN, hsec, subset_closure_nonvanishing_of_open hDc hmaps hopen hδ hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem exists_forall_ne_zero_of_isOpen {E ι : Type} [TopologicalSpace E] (s : Finset ι)
    (G : ι → E → ℂ) (U : Set E) (hc : ∀ i ∈ s, ContinuousOn (G i) U)
    (hne : ∀ i ∈ s, ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, G i t ≠ 0) :
    ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, ∀ i ∈ s, G i t ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro W - - ⟨t, ht⟩
    exact ⟨t, ht, by simp⟩
  | insert a s ha ih =>
    intro W hWo hWU hW
    obtain ⟨t₀, ht₀W, ht₀⟩ := hne a (Finset.mem_insert_self a s) W hWo hWU hW
    have hW'o : IsOpen (W ∩ G a ⁻¹' {0}ᶜ) :=
      ((hc a (Finset.mem_insert_self a s)).mono hWU).isOpen_inter_preimage hWo isOpen_compl_singleton
    obtain ⟨t, ⟨htW, hta⟩, hts⟩ := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hne i (Finset.mem_insert_of_mem hi)) _ hW'o (Set.inter_subset_left.trans hWU)
      ⟨t₀, ht₀W, ht₀⟩
    refine ⟨t, htW, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hta
    · exact hts i hi

theorem ProperOpenProjectionLocalUnbranched.proof (hFin : CompactHolomorphicFibreFinite.Statement)
    (hLoc : IsolatedFibreLocalUnbranched.Statement) : ProperOpenProjectionLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A D hB hf hXB hD hAD hprop hopen y₀ hy₀
  have zerosX : ∀ z, z ∈ X ∩ B → ∀ i, f i z = 0 := fun z hz => by
    rw [hXB] at hz
    exact hz.2
  have memX : ∀ z, z ∈ B → (∀ i, f i z = 0) → z ∈ X ∩ B := fun z hz h0 => by
    rw [hXB]
    exact ⟨hz, h0⟩

  set F := {x | x ∈ X ∩ B ∧ A x = y₀} with hF
  have hFc : IsCompact F := by
    have := hprop {y₀} (Set.singleton_subset_iff.2 hy₀) isCompact_singleton
    simpa only [Set.mem_singleton_iff] using this

  set n := Fintype.card σ
  let L : (σ → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) (Fintype.equivFin σ)
  set U₀ : Set (Fin n → ℂ) := L.symm ⁻¹' B with hU₀
  set Φ : (Fin n → ℂ) → Fin (k + d) → ℂ :=
    fun v => Fin.append (fun i => f i (L.symm v)) (A (L.symm v)) with hΦ
  set yv : Fin (k + d) → ℂ := Fin.append (0 : Fin k → ℂ) y₀ with hyv
  have hU₀o : IsOpen U₀ := hB.preimage L.symm.continuous
  have hΦd : DifferentiableOn ℂ Φ U₀ := by
    refine differentiableOn_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [hΦ, Fin.append_left]
      exact (hf i).differentiableOn.comp L.symm.differentiable.differentiableOn (fun v hv => hv)
    · simp only [hΦ, Fin.append_right]
      exact ((differentiable_apply (𝕜 := ℂ) j).comp
        (A.differentiable.comp L.symm.differentiable)).differentiableOn
  have hfib : {v | v ∈ U₀ ∧ Φ v = yv} = L.symm ⁻¹' F := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hU₀, hF, hΦ, hyv]
    constructor
    · rintro ⟨hv, he⟩
      refine ⟨memX _ hv fun i => ?_, ?_⟩
      · simpa using congrFun he (Fin.castAdd d i)
      · funext j
        simpa using congrFun he (Fin.natAdd k j)
    · rintro ⟨hv, hA⟩
      refine ⟨hv.2, funext fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [zerosX _ hv i]
      · simp [hA]
  have hfibc : IsCompact {v | v ∈ U₀ ∧ Φ v = yv} := by
    rw [hfib, ← L.image_eq_preimage_symm]
    exact hFc.image L.continuous
  have hFfin : F.Finite := by
    have h1 := (hFin n (k + d) U₀ Φ yv hU₀o hΦd hfibc).image L.symm
    rwa [hfib, Set.image_preimage_eq _ L.symm.surjective] at h1

  have hloc : ∀ x ∈ F, ∃ (M : Set (σ → ℂ)) (g : (Fin d → ℂ) → ℂ), IsOpen M ∧ x ∈ M ∧
      AnalyticAt ℂ g y₀ ∧ (¬ ∀ᶠ t in 𝓝 y₀, g t = 0) ∧
      ∀ z ∈ X ∩ B ∩ M, g (A z) ≠ 0 →
        ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O := by
    intro x hx
    have hiso : ∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ B ∩ W, A x' = A x → x' = x := by
      refine ⟨(F \ {x})ᶜ, hFfin.sdiff.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl, ?_⟩
      rintro x' ⟨hx'XB, hx'W⟩ hx'A
      by_contra hne
      exact hx'W ⟨⟨hx'XB, hx'A.trans hx.2⟩, hne⟩
    obtain ⟨M, g, hM, hg, hg0, hsec⟩ := hLoc σ X B k f d A hB hf hXB hopen x hx.1 hiso
    rw [hx.2] at hg hg0
    exact ⟨interior M, g, isOpen_interior, mem_interior_iff_mem_nhds.2 hM, hg, hg0,
      fun z hz => hsec z ⟨hz.1, interior_subset hz.2⟩⟩
  choose! M g hMo hxM hga hgne hsec using hloc
  set s := hFfin.toFinset with hs
  have hsF : ∀ x, x ∈ s ↔ x ∈ F := fun x => hFfin.mem_toFinset

  obtain ⟨r₀, hr₀, hr₀D⟩ := nhds_basis_closedBall.mem_iff.1 (hD.mem_nhds hy₀)
  set Mall := ⋃ x ∈ F, M x with hMall
  have hMallo : IsOpen Mall := isOpen_biUnion fun x hx => hMo x hx
  set C := {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ r₀} \ Mall with hC
  have hCc : IsCompact C := (hprop _ hr₀D (isCompact_closedBall y₀ r₀)).diff hMallo
  have hAC : y₀ ∉ A '' C := by
    rintro ⟨c, ⟨⟨hcXB, -⟩, hcM⟩, hcA⟩
    exact hcM (Set.mem_biUnion (show c ∈ F from ⟨hcXB, hcA⟩) (hxM c ⟨hcXB, hcA⟩))
  have hev : ∀ᶠ t in 𝓝 y₀, t ∈ ball y₀ r₀ ∧ t ∉ A '' C ∧ ∀ x ∈ s, AnalyticAt ℂ (g x) t := by
    refine (show ∀ᶠ t in 𝓝 y₀, t ∈ ball y₀ r₀ from ball_mem_nhds y₀ hr₀).and
      ((show ∀ᶠ t in 𝓝 y₀, t ∉ A '' C from
        ((hCc.image A.continuous).isClosed.isOpen_compl).mem_nhds hAC).and ?_)
    exact (Filter.eventually_all_finset s).2 fun x hx => (hga x ((hsF x).1 hx)).eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hgan : ∀ x ∈ s, AnalyticOnNhd ℂ (g x) (ball y₀ r) := fun x hx t ht => (hball t ht).2.2 x hx
  refine ⟨ball y₀ r, fun t => ∏ x ∈ s, g x t, isOpen_ball, mem_ball_self hr, ?_,
    Finset.analyticOnNhd_fun_prod s hgan, ?_, ?_⟩
  · intro t ht
    exact hr₀D (ball_subset_closedBall (hball t ht).1)
  · intro W hWo hWU hW
    have hne : ∀ x ∈ s, ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ ball y₀ r → W.Nonempty →
        ∃ t ∈ W, g x t ≠ 0 := by
      intro x hx W hWo hWU hW
      by_contra hcon
      push Not at hcon
      obtain ⟨t, htW⟩ := hW
      have hzt : g x =ᶠ[𝓝 t] 0 := by
        filter_upwards [hWo.mem_nhds htW] with u hu using hcon u hu
      have hEq := (hgan x hx).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball y₀ r).isPreconnected (hWU htW) hzt
      exact hgne x ((hsF x).1 hx) (by
        filter_upwards [ball_mem_nhds y₀ hr] with u hu using hEq hu)
    obtain ⟨t, htW, ht⟩ := exists_forall_ne_zero_of_isOpen s g (ball y₀ r)
      (fun x hx => (hgan x hx).continuousOn) hne W hWo hWU hW
    exact ⟨t, htW, Finset.prod_ne_zero_iff.2 ht⟩
  · intro y hyU hgy x' hx'XB hx'A
    have hx'M : x' ∈ Mall := by
      by_contra hn
      refine (hball y hyU).2.1 ⟨x', ⟨⟨hx'XB, ?_⟩, hn⟩, hx'A⟩
      rw [hx'A]
      exact ball_subset_closedBall (hball y hyU).1
    obtain ⟨x, hxF, hx'x⟩ := Set.mem_iUnion₂.1 hx'M
    have hgx : g x (A x') ≠ 0 := by
      rw [hx'A]
      exact Finset.prod_ne_zero_iff.1 hgy x ((hsF x).2 hxF)
    exact hsec x hxF x' ⟨hx'XB, hx'x⟩ hgx

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def GermMinimalPolynomialDivides.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ) = 0) ∧
        ∀ E : Polynomial ((Fin d → ℂ) → ℂ), (∀ k, AnalyticAt ℂ (E.coeff k) (A w)) →
          (∀ᶠ z in 𝓝 w, z ∈ X → E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (g z) = 0) →
          ∀ᶠ y in 𝓝 (A w),
            (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ) ∣
              E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

def IrreducibleGermCurve.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ),
    IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) X

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
