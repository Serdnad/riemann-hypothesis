module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle201
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle220
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

@[expose] public section

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WeilM

theorem symp_fromBlocks_hyperbolic :
    ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (r₀ : ℕ) (J₀ : Matrix α α S) (K : Matrix β β S)
    (z z' : Matrix (α ⊕ (Fin r₀ ⊕ Fin r₀)) β S),
    symp c ξ (Matrix.fromBlocks J₀ 0 0 (Matrix.fromBlocks 0 1 1 0)) K z z' =
      symp c ξ J₀ K (Matrix.of fun i l => z (Sum.inl i) l) (Matrix.of fun i l => z' (Sum.inl i) l) +
      ∑ i, (Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inl i)) j * K j l * c (z' (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inr i)) j * K j l * c (z' (Sum.inr (Sum.inl i)) l))) := by
  intro R S _ _ _ c ξ α β _ _ _ _ r₀ J₀ K z z'

  simp only [symp, hTens, ← map_add (f := _), ← map_sum, ← mul_add, ← Finset.mul_sum]
  congr 2
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.of_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, Finset.sum_add_distrib]
  congr 1
  rw [add_comm]
  congr 1 <;>
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Matrix.one_apply]

end GlobalTheory.WeilM
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RestrSchA

variable {κ₁ κ : Type} {j : κ₁ → κ}

theorem extend_map {M N : Type} [Zero M] [Zero N] (hj : Function.Injective j) (φ : M → N) (h0 : φ 0 = 0)
    (y : κ₁ → M) : (fun i => φ (Function.extend j y 0 i)) = Function.extend j (fun a => φ (y a)) 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, h0]

theorem extend_add {M : Type} [AddZeroClass M] (hj : Function.Injective j) (y z : κ₁ → M) :
    Function.extend j (y + z) 0 = Function.extend j y 0 + Function.extend j z 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem extend_smul {R M : Type} [Zero M] [SMulZeroClass R M] (hj : Function.Injective j) (c : R) (y : κ₁ → M) :
    Function.extend j (c • y) 0 = c • Function.extend j y 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem continuous_extend {M : Type} [TopologicalSpace M] [Zero M] (hj : Function.Injective j) :
    Continuous (fun y : κ₁ → M => Function.extend j y 0) := by
  refine continuous_pi fun i => ?_
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp only [hj.extend_apply]
    exact continuous_apply a
  · simp only [Function.extend_apply' _ _ _ h]
    exact continuous_const

theorem isClosedEmbedding_extend {M : Type} [TopologicalSpace M] [Zero M] [T2Space M] (hj : Function.Injective j) :
    Topology.IsClosedEmbedding (fun y : κ₁ → M => Function.extend j y 0) :=
  Function.LeftInverse.isClosedEmbedding (f := fun x : κ → M => x ∘ j)
    (fun y => by funext a; simp [hj.extend_apply]) (by fun_prop) (continuous_extend hj)

end GlobalTheory.RestrSchA

namespace GlobalTheory.RestrSchA

open scoped Classical

variable {κ₁ κ : Type} {j : κ₁ → κ}

def extL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (hj : Function.Injective j) :
    (κ₁ → V) →L[ℝ] (κ → V) where
  toFun y := Function.extend j y 0
  map_add' y z := extend_add hj y z
  map_smul' c y := extend_smul hj c y
  cont := continuous_extend hj

theorem norm_le_extL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype κ₁] [Fintype κ]
    (hj : Function.Injective j) (y : κ₁ → V) : ‖y‖ ≤ ‖extL V hj y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  have h : extL V hj y (j a) = y a := by simp [extL, hj.extend_apply]
  rw [← h]
  exact norm_le_pi_norm _ _

def restrS (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j) :
    SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ₁ → NumberField.mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (extL (NumberField.mixedEmbedding.mixedSpace F) hj).hasTemperateGrowth
    ⟨1, 1, fun y => by
      have := norm_le_extL hj y
      have h0 := norm_nonneg (extL (NumberField.mixedEmbedding.mixedSpace F) hj y)
      simp only [pow_one, one_mul]
      linarith⟩

theorem restrS_apply (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (y : κ₁ → NumberField.mixedEmbedding.mixedSpace F) :
    restrS F hj f y = f (Function.extend j y 0) := by
  simp [restrS, extL]

theorem sb_comp_extend (F : Type) [Field F] [NumberField F] (hj : Function.Injective j)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y => g (Function.extend j y 0)) ∈ SB (κ₁ → FiniteAdeleRing (𝓞 F) F) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
  exact ⟨hg.1.comp_continuous (continuous_extend hj), hg.2.comp_isClosedEmbedding (isClosedEmbedding_extend hj)⟩

theorem pureA_extend (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ₁ → AdeleRing (𝓞 F) F) :
    pureA F f g (Function.extend j y 0) = pureA F (restrS F hj f) (fun z => g (Function.extend j z 0)) y := by
  simp only [pureA, restrS_apply]
  rw [extend_map hj (fun x : AdeleRing (𝓞 F) F => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
      (by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0; exact map_zero _) y,
    extend_map hj (fun x : AdeleRing (𝓞 F) F => x.2) rfl y]

theorem mem_schA_comp_extend : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ Φ ∈ schA F κ, (fun y => Φ (Function.extend j y 0)) ∈ schA F κ₁ := by
  intro F _ _ κ₁ κ _ _ j hj Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨restrS F hj f, fun z => g (Function.extend j z 0), sb_comp_extend F hj hg, ?_⟩
    funext y
    exact pureA_extend F hj f g y
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.RestrSchA

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory

theorem hTens_eq_trace {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    hTens c JA JB x y = Matrix.trace (JAᵀ * (x * JB * (y.map c)ᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_mul_left {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α α' β : Type} [Fintype α] [Fintype α'] [Fintype β]
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix α α' S) (z z' : Matrix α' β S) :
    symp c ξ JA JB (P * z) (P * z') = symp c ξ (Pᵀ * JA * P.map c) JB z z' := by
  unfold symp
  congr 2
  rw [hTens_eq_trace, hTens_eq_trace, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  conv_rhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  first | exact @GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | exact GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | (intros; apply GlobalTheory.SchANonzero.exists_mem_schA_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.star_mem_schA_main | exact GlobalTheory.star_mem_schA_main | (intros; apply GlobalTheory.star_mem_schA_main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_unitaryDoubled_blockDiag_one : ∀ (R E : Type) [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β E) (g : UG c J), ∃ gd : UG c (dbl J), ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  first | exact @GlobalTheory.unitary_diag_one_mem_dbl | exact GlobalTheory.unitary_diag_one_mem_dbl | (intros; apply GlobalTheory.unitary_diag_one_mem_dbl <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SliceSB

theorem continuous_sumElim {k : Type} [TopologicalSpace k] {κ κ' : Type} :
    Continuous (fun p : (κ → k) × (κ' → k) => (Sum.elim p.1 p.2 : κ ⊕ κ' → k)) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

theorem slice_mem : ∀ (k : Type) [TopologicalSpace k] [T2Space k] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ f ∈ SB (κ ⊕ κ' → k),
    (∀ x₁ : κ → k, (fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) ∈ SB (κ' → k)) ∧
      ∀ l : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ, (fun x₁ : κ → k => l fun x₂ => f (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
  intro k _ _ κ κ' _ _ f hf
  obtain ⟨hlc, hcs⟩ := hf
  have hΦ := continuous_sumElim (k := k) (κ := κ) (κ' := κ')
  refine ⟨fun x₁ => ?_, fun l => ?_⟩
  · have he : Continuous (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      hΦ.comp (Continuous.prodMk continuous_const continuous_id)
    have hli : Function.LeftInverse (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      fun x₂ => rfl
    have hce : Topology.IsClosedEmbedding (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      hli.isClosedEmbedding (continuous_pi fun i => continuous_apply _) he
    exact ⟨hlc.comp_continuous he, hcs.comp_isClosedEmbedding hce⟩
  · set K := (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) '' tsupport f
    have hK : IsCompact K := hcs.isCompact.image (continuous_pi fun i => continuous_apply _)
    have hloc : IsLocallyConstant (fun x₁ : κ → k => fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) := by
      rw [IsLocallyConstant.iff_eventually_eq _]
      intro x₀
      have hF : IsLocallyConstant (fun p : (κ → k) × (κ' → k) => f (Sum.elim p.1 p.2)) := hlc.comp_continuous hΦ
      have h1 : ∀ y ∈ K, ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y),
          (fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) z.1 z.2 := by
        intro y _
        have h0 := (IsLocallyConstant.iff_eventually_eq _).mp hF (x₀, y)
        have hc : Continuous (fun z : (κ → k) × (κ' → k) => (x₀, z.2)) := continuous_const.prodMk continuous_snd
        have h3 : ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y), f (Sum.elim x₀ z.2) = f (Sum.elim x₀ y) :=
          (hc.tendsto (x₀, y)).eventually h0
        filter_upwards [h0, h3] with z hz hz'
        exact hz.trans hz'.symm
      have h2 := hK.eventually_forall_of_forall_eventually (P := fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) h1
      filter_upwards [h2] with x hx
      funext y
      by_cases hy : y ∈ K
      · exact hx y hy
      · have hz : ∀ x', f (Sum.elim x' y) = 0 := by
          intro x'
          by_contra hne
          exact hy ⟨Sum.elim x' y, subset_tsupport f hne, rfl⟩
        rw [hz, hz]
    refine ⟨(hloc.comp l), ?_⟩
    refine HasCompactSupport.intro (hcs.isCompact.image (f := fun z : κ ⊕ κ' → k => z ∘ Sum.inl) (continuous_pi fun i => continuous_apply _)) ?_
    intro x hx
    have : (fun x₂ : κ' → k => f (Sum.elim x x₂)) = 0 := by
      funext x₂
      by_contra hne
      exact hx ⟨Sum.elim x x₂, subset_tsupport f hne, rfl⟩
    simp only [this, map_zero]

end GlobalTheory.SliceSB
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (cokernel)

namespace GlobalTheory

namespace Vert.Flag

variable {X Y : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N) (π : Y ⟶ X)

def pull : Flag ((Scheme.Modules.pullback π).obj E) N where
  F i := (Scheme.Modules.pullback π).obj (fl.F i)
  ι i := (Scheme.Modules.pullback π).map (fl.ι i)
  isSubbundle i := SubPull.isSubbundle_pullback X Y π _ _ _ i (fl.isVB i) (fl.isSubbundle i)
  isVB i := (fl.isVB i).pullback π
  step i := (Scheme.Modules.pullback π).map (fl.step i)
  step_ι i := by rw [← Functor.map_comp, fl.step_ι]
  isIso_last := inferInstance

end Vert.Flag

namespace VMetric

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
  {E : X.Modules} {r : ℕ} (fl : Vert.Flag E r) (π : Y ⟶ X) (i : Fin r)

variable {fl π i}

end VMetric

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.CurveDevissage

theorem interNum_one_nonneg {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k (X := V))) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : N.IsLB)
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra k Γ(Z, ⊤)],
      (∀ r : k, i.appTop (algebraMap k Γ(V, ⊤) r) = algebraMap k Γ(Z, ⊤) r) →
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection k (N.pull i) 1)
    (F : V.Modules) (hF : QCoh.IsFiniteQC F) : 0 ≤ interNum k F ![N] := by
  have := isNoetherian_of_isProjOver hp
  have hL : ∀ i, ((![N] : Fin 1 → LB V) i).IsLB := fun i => by fin_cases i; exact hN
  refine QCoh.devissage V (fun F => 0 ≤ interNum k F ![N])
    (fun F hF => (interNum_eq_zero_of_isZero k hF hL).ge) (fun S hS h₁ h₃ p₁ p₃ => ?_)
    (fun Z hZ _ G hG => ?_) F hF
  · rw [interNum_shortExact hS hL
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)]
    exact add_nonneg p₁ p₃
  · have := isIntegral_red hZ
    letI := algebraΓAlong k (redι Z)
    have hi := appTop_algebraMap_along k (redι Z)
    have hpZ : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
      rw [← comp_strHom hi]
      exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hM := LB.isLB_pull hN (redι Z)
    have e : (fun i => ((![N] : Fin 1 → LB V) i).pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    have e' : (fun _ : Fin 1 => N.pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    rw [interNum_pushforward_of_isClosedImmersion hi G hL, e]
    have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ 1 :=
      (redι Z).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hd
    rcases hdZ.eq_or_lt with h1 | h1
    · rw [VB.interNum_one_eq_genRank_mul k _ hpZ h1 G _ hM]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      have := h _ (redι Z) hi h1
      rwa [topSelf_def, e'] at this
    · refine (interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom k _) G hpZ ?_
        fun i => by fin_cases i; exact hM).ge
      rw [Fintype.card_fin]
      exact (QCoh.suppDim_le G).trans_lt h1

theorem degOfRank_nonneg : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) (X := V)) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  intro p _ V _ hp hd N hN h
  have := Twist.isFiniteQC_twist (F := structureModule V) hN
  have h1 := interNum_one_nonneg hp hd hN (fun Z i _ _ _ _ hZ => h Z i hZ)
    (twist (structureModule V) N) this
  have h2 := interNum_twist_cons (ZMod p) (structureModule V) (P := ![]) hN isEmptyElim
  have h3 : chi (ZMod p) (twist (structureModule V) N) = chi (ZMod p) (toMod N) :=
    chi_congr _ (Twist.unitTwistIso N)
  have h4 : interNum (ZMod p) (twist (structureModule V) N) ![N] =
    chi (ZMod p) (twist (structureModule V) N) - chi (ZMod p) (structureModule V) :=
    h2.trans (congrArg₂ (· - ·) (interNum_of_isEmpty _ _ _) (interNum_of_isEmpty _ _ _))
  rw [degOfRank]
  push_cast
  linarith

end GlobalTheory.CurveDevissage
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ A M : LB X, IsAmpleLB A → IsNef k M → (∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r)) → IsAmpleLB (tens A M) := by
  intro k _ _ d hd X _ _ hp hX A M hA hM hsec
  obtain ⟨r, hr, hs⟩ := hsec
  refine IsAmpleLB.tens_of_forall_isPsEff k X (strHom k X) hp A M hA hM.isLB ?_
  intro Z hZ
  by_cases hZX : (Z : Set X) = Set.univ
  · exact GlobalTheory.T.isPseudoEffective_reducedUniv_of_section_pow k X hp M hM.isLB r hr hs Z hZX
  · exact GlobalTheory.T.isPsEff_pull_reduced_closed_of_dim_le k d hd X hp M hM Z hZ (GlobalTheory.T.topologicalKrullDim_le_of_isClosed_ne_univ_integral X d hX (Z : Set X) Z.isClosed hZX)

end GlobalTheory
end
