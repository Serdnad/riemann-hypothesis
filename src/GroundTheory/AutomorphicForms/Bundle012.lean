module

public import GroundTheory.AutomorphicForms.Bundle010
public import GroundTheory.AutomorphicForms.HeckeAlgebra
public import GroundTheory.AutomorphicForms.Bundle011
public import GroundTheory.AutomorphicForms.DixmierMalliavinLine
public import GroundTheory.AutomorphicForms.DixmierMalliavinSeries
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Injective
public import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
public import GroundTheory.AutomorphicForms.HarishChandraCentre.LeadingTerm
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Symmetric
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Capelli
public import GroundTheory.AutomorphicForms.ReductionHeight
import GroundTheory.GlobalFields.Adele.Topology
public import GroundTheory.GlobalFields.TateThesis.Bundle006
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_decomp_direction {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f₁ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f₁) ∧
      HasCompactSupport f₁ ∧
      ∃ g k : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧ tsupport g ⊆ Icc (-ε) ε ∧
        tsupport k ⊆ Icc (-ε) ε ∧
        ∀ x, f x = (∫ t, g t * f₁ (h.expG (t • X) * x)) + ∫ t, k t * f (h.expG (t • X) * x) := by
  obtain ⟨M, hM, hser⟩ := h.exists_bound_dirDeriv hf hfc X
  obtain ⟨c, g, k, hg, hk, hgs, hks, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  obtain ⟨hf₁, hf₁c⟩ := hser c hc
  refine ⟨_, hf₁, hf₁c, g, k, hg, hk, hgs, hks, fun x => ?_⟩
  set F : ℝ → ℂ := fun t => f (h.expG (t • X) * x) with hFdef
  have hF : ContDiff ℝ ∞ F := h.contDiff_comp_expG_smul_mul hf X x
  have hD : ∀ p t, iteratedDeriv p F t = h.dirDeriv X p f (h.expG (t • X) * x) :=
    fun p t => h.iteratedDeriv_comp_expG_mul X p f x t
  have key := hid F hF (fun p t _ => by rw [hD]; exact hM p _)
  have hF0 : F 0 = f x := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero, one_mul]
  rw [hF0] at key
  rw [key]
  congr 1
  · have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    have hcont : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * g t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcont p).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * ‖g t‖ := by
      intro p t
      simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_assoc (|c p|)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (c p))
      have : ‖iteratedDeriv p F t‖ ≤ M p := by rw [hD]; exact hM p _
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hgi : Integrable (fun t => ‖g t‖) :=
      (hg.continuous.integrable_of_hasCompactSupport hgc).norm
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, ‖g t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e1 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e1]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    rw [← tsum_mul_left]
    congr 1
    funext p
    simp only [T, hD]
    ring
  · congr 1; funext t; rw [mul_comm]

theorem exists_decomp_iter {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤) (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        HasCompactSupport (F i)) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x) := by
  intro d
  induction d with
  | zero =>
    intro X f hf hfc
    refine ⟨1, fun _ => f, fun _ _ => 1, fun _ => ⟨hf, hfc⟩, fun _ => ⟨contDiff_const, ?_⟩,
      fun x => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp only [h.revProdExp_zero, one_mul, integral_const, hv, one_smul, Fin.sum_univ_one]
  | succ d ih =>
    intro X f hf hfc
    let := h.chartedSpace
    obtain ⟨f₁, hf₁, hf₁c, g, k, hg, hk, hgs, hks, hdec⟩ :=
      h.exists_decomp_direction hf hfc (X 0) hε
    obtain ⟨m₁, F₁, K₁, hF₁, hK₁, hd₁⟩ := ih (Fin.tail X) f₁ hf₁ hf₁c
    obtain ⟨m₂, F₂, K₂, hF₂, hK₂, hd₂⟩ := ih (Fin.tail X) f hf hfc
    refine ⟨m₁ + m₂, Fin.append F₁ F₂,
      Fin.append (fun i t => g (t 0) * K₁ i (Fin.tail t)) (fun i t => k (t 0) * K₂ i (Fin.tail t)),
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hF₁ i
      · simpa only [Fin.append_right] using hF₂ i
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨contDiff_cons_kernel hg (hK₁ i).1, tsupport_cons_kernel hε.le hgs (hK₁ i).2⟩
      · simp only [Fin.append_right]
        exact ⟨contDiff_cons_kernel hk (hK₂ i).1, tsupport_cons_kernel hε.le hks (hK₂ i).2⟩
    · intro x
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le hg.continuous hgs (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => (hF₁ i).1.continuous) hd₁ x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hk.continuous hks (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => (hF₂ i).1.continuous) hd₂ x).symm

end IsExpLieAlgebra

theorem dixmierMalliavin (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ)
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ (n : ℕ) (φ ψ : Fin n → G → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (φ i)) ∧
        HasCompactSupport (φ i) ∧
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧ HasCompactSupport (ψ i)) ∧
      f = ∑ i, groupConv μ (φ i) (ψ i) := by
  let := h.chartedSpace
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp μ b
  obtain ⟨m, F, K, hF, hK, hd⟩ := h.exists_decomp_iter hε (⇑b) f hf hfc
  have hK' : ∀ i, ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ Metric.closedBall 0 ε := by
    intro i
    refine ⟨(hK i).1.comp contDiff_neg, ?_⟩
    intro t ht
    have : -t ∈ tsupport (K i) := by
      have := tsupport_comp_subset_preimage (K i) (f := fun t : Fin _ → ℝ => -t) continuous_neg ht
      simpa using this
    have := (hK i).2 this
    simpa [mem_closedBall_zero_iff, norm_neg] using this
  choose κ hκs hκc hκ using fun i => hdens (fun t => K i (-t)) (hK' i).1 (hK' i).2
  refine ⟨m, κ, F, fun i => ⟨hκs i, hκc i, (hF i).1, (hF i).2⟩, ?_⟩
  funext x
  rw [hd x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [groupConv, hκ i (fun y => F i (y⁻¹ * x))
    ((hF i).1.continuous.comp (continuous_inv.mul continuous_const))]
  have e : ∀ t : Fin (Module.finrank ℝ 𝔤) → ℝ, K i (-t) * F i ((h.prodExp (⇑b) t)⁻¹ * x) =
      (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) (-t) := by
    intro t
    have := h.revProdExp_inv (⇑b) (-t)
    rw [neg_neg] at this
    simp only [← this, inv_inv]
  simp_rw [e]
  exact (integral_neg_eq_self (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) volume).symm

end GroundTheory.Automorphic
end

section

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

theorem harishChandraHom_mem_symmetricSubalgebra (z : Subalgebra.center ℂ (U n)) :
    harishChandraHom z ∈ symmetricSubalgebra (Fin n) ℂ :=
  harishChandraHom_isSymmetric z

noncomputable def capelliCenter (k : ℕ) : Subalgebra.center ℂ (U n) :=
  ⟨capelli (k + 1), capelli_mem_center _⟩

theorem adjoin_harishChandraHom_capelli :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => harishChandraHom (capelliCenter (n := n) k)) =
      symmetricSubalgebra (Fin n) ℂ :=
  adjoin_eq_symmetricSubalgebra _ (fun _ => harishChandraHom_isSymmetric _)
    (fun k => totalDegree_harishChandraHom_capelli_sub k)

theorem range_harishChandraHom :
    (harishChandraHom (n := n)).range = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact harishChandraHom_isSymmetric z
  · rw [← adjoin_harishChandraHom_capelli, Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

noncomputable def harishChandraEquiv :
    Subalgebra.center ℂ (U n) ≃ₐ[ℂ] symmetricSubalgebra (Fin n) ℂ :=
  (AlgEquiv.ofInjective harishChandraHom harishChandraHom_injective).trans
    (Subalgebra.equivOfEq _ _ range_harishChandraHom)

@[simp] theorem harishChandraEquiv_apply (z : Subalgebra.center ℂ (U n)) :
    (harishChandraEquiv z : MvPolynomial (Fin n) ℂ) = harishChandraHom z := rfl

end GroundTheory.Automorphic.HarishChandra
end

section

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

instance secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  have := GroundTheory.Global.countable_numberField K
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      SecondCountableTopology ↥(v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun v =>
    inferInstanceAs (SecondCountableTopology (v.adicCompletionIntegers K))
  have hemb := RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))
  set O : Set (FiniteAdeleRing (𝓞 K) K) :=
    Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) cofinite) with hO
  have hOsc : SecondCountableTopology O :=
    hemb.toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hOopen : IsOpen O := hemb.isOpen_range
  have hOmem : ∀ x : FiniteAdeleRing (𝓞 K) K, x ∈ O ↔
      x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := fun x => by
    constructor
    · rintro ⟨y, rfl⟩ v
      exact (y v).2
    · intro h
      exact ⟨fun v => ⟨x v, h v⟩, rfl⟩
  let U : K → Set (FiniteAdeleRing (𝓞 K) K) := fun k => (· - algebraMap K _ k) ⁻¹' O
  have hU : ∀ k, SecondCountableTopology (U k) := fun k => by
    have he : IsEmbedding (Set.codRestrict
        ((Homeomorph.subRight (algebraMap K (FiniteAdeleRing (𝓞 K) K) k)) ∘
          (Subtype.val : U k → FiniteAdeleRing (𝓞 K) K)) O fun x => x.2) :=
      ((Homeomorph.subRight (algebraMap K (FiniteAdeleRing (𝓞 K) K) k)).isEmbedding.comp
        IsEmbedding.subtypeVal).codRestrict _ _
    exact he.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
    (fun k => hOopen.preimage (continuous_sub_right _)) ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles x
    exact ⟨k, (hOmem _).2 hk⟩

instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸[K] :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance secondCountableTopology_matrix {R : Type*} [TopologicalSpace R] [SecondCountableTopology R]
    {n : ℕ} : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))

instance measurableSpace_adelicGL {n : ℕ} : MeasurableSpace (AdelicGLn.AdelicGL K n) := borel _

instance borelSpace_adelicGL {n : ℕ} : BorelSpace (AdelicGLn.AdelicGL K n) := ⟨rfl⟩

instance measurableSpace_finiteAdelicGL {n : ℕ} : MeasurableSpace (AdelicGLn.FiniteAdelicGL K n) :=
  borel _

instance borelSpace_finiteAdelicGL {n : ℕ} : BorelSpace (AdelicGLn.FiniteAdelicGL K n) := ⟨rfl⟩

instance measurableSpace_GL_infinitePlace {n : ℕ} (w : InfinitePlace K) :
    MeasurableSpace (GL (Fin n) w.Completion) :=
  borel _

instance borelSpace_GL_infinitePlace {n : ℕ} (w : InfinitePlace K) :
    BorelSpace (GL (Fin n) w.Completion) := ⟨rfl⟩

def infFinEquiv {n : ℕ} : AdelicGLn.AdelicGL K n ≃ₜ*
    (Π w : InfinitePlace K, GL (Fin n) w.Completion) × AdelicGLn.FiniteAdelicGL K n :=
  (AdelicGLn.prodEquiv K n).trans
    { toMulEquiv := MulEquiv.prodCongr (AdelicGLn.infiniteEquiv K n).toMulEquiv (MulEquiv.refl _)
      continuous_toFun :=
        ((AdelicGLn.infiniteEquiv K n).continuous.comp continuous_fst).prodMk continuous_snd
      continuous_invFun :=
        ((AdelicGLn.infiniteEquiv K n).symm.continuous.comp continuous_fst).prodMk continuous_snd }

theorem measure_lt_top_of_forall_mem {n : ℕ} (μ : Measure (AdelicGLn.AdelicGL K n))
    [μ.IsHaarMeasure] {E : Set (AdelicGLn.AdelicGL K n)}
    (S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion))
    (hS : ∀ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w) < ⊤)
    {F : Set (AdelicGLn.FiniteAdelicGL K n)} (hF : IsCompact F)
    (hE : ∀ g ∈ E, (∀ w, infAt w g ∈ S w) ∧ (AdelicGLn.prodEquiv K n g).2 ∈ F) : μ E < ⊤ := by
  set e := infFinEquiv (K := K) (n := n) with he
  set ρ : Measure ((Π w : InfinitePlace K, GL (Fin n) w.Completion) × AdelicGLn.FiniteAdelicGL K n) :=
    (Measure.pi fun w => (Measure.haar : Measure (GL (Fin n) w.Completion))).prod
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) with hρ
  have hν : (Measure.map e μ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ e.toMulEquiv e.continuous e.symm.continuous
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map e μ) ρ
  set T := (Set.univ.pi S) ×ˢ F with hT
  have hET : E ⊆ e ⁻¹' T := fun g hg => ⟨fun w _ => (hE g hg).1 w, (hE g hg).2⟩
  have hmap : μ (e ⁻¹' T) = Measure.map e μ T :=
    (e.toHomeomorph.toMeasurableEquiv.map_apply T).symm
  have hρT : ρ T = (∏ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w)) *
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) F := by
    rw [hρ, hT, Measure.prod_prod, Measure.pi_pi]
  set c := (Measure.map e μ).haarScalarFactor ρ with hc
  calc μ E ≤ μ (e ⁻¹' T) := measure_mono hET
    _ = Measure.map e μ T := hmap
    _ = (c • ρ) T := by rw [← heq]
    _ < ⊤ := by
      rw [Measure.smul_apply, hρT, ENNReal.smul_def, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top
        (ENNReal.prod_lt_top fun w _ => hS w) hF.measure_lt_top)

end Reduction

end

end GroundTheory.Automorphic
end

section

open NumberField Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

theorem exists_isCompact_mul_mem_of_ideleModule_mem_Icc {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ S : Set (IdeleGroup K), IsCompact S ∧ ∀ s : IdeleGroup K,
      a ≤ (ideleModule K s : ℝ) → (ideleModule K s : ℝ) ≤ b → ∃ c : Kˣ, diagonal K c * s ∈ S := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  set I : Set {r : ℝ // 0 < r} := Subtype.val ⁻¹' Icc a b with hI
  have hIc : IsCompact I := by
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' I = Icc a b := by
      ext r
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hr
        exact ⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩
    rw [this]
    exact isCompact_Icc
  refine ⟨(fun p : IdeleGroup K × {r : ℝ // 0 < r} => p.1 * moduleSection w₀ p.2) '' (D ×ˢ I),
    (hD.prod hIc).image (continuous_fst.mul ((continuous_moduleSection w₀).comp continuous_snd)),
    fun s has hsb => ?_⟩
  obtain ⟨c, hc⟩ := hxD _ (mul_inv_moduleSection_mem w₀ s)
  refine ⟨c, ⟨(diagonal K c * (s * (moduleSection w₀ (ideleModule K s))⁻¹), ideleModule K s),
    ⟨hc, has, hsb⟩, ?_⟩⟩
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end Reduction

end GroundTheory.Automorphic
end
