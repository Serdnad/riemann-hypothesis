module

public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
public import GroundTheory.AutomorphicForms.GeometricLemma
import GroundTheory.AutomorphicForms.GeometricLemmaCellKernel
import GroundTheory.AutomorphicForms.GeometricLemmaCellSurjective
import GroundTheory.AutomorphicForms.GeometricLemmaGraded
import GroundTheory.AutomorphicForms.Bundle018
import GroundTheory.LocalFields.LocalFourierHaar
public import GroundTheory.GlobalFields.Adele.Bundle001
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import GroundTheory.GlobalFields.TateThesis.AdelePoisson
public import GroundTheory.GlobalFields.TateThesis.Bundle009
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
public import GroundTheory.PAdicHodge.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.LocalFields.UnramifiedHensel
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle220
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle338
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import GroundTheory.AutomorphicForms.LocallyProfinite
public import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
import GroundTheory.AutomorphicForms.GL2.GodementSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.LocalFields.FormalGroups.Bundle001
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

@[expose] public section

section

set_option maxSynthPendingDepth 1

open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

noncomputable section

namespace GlobalTheory.CompanionTheory.GeomLemmaUniform

section Filtration

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic Matrix GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ}

theorem filtration_of_cellEnumeration {k : ℕ} (w : Fin k → Equiv.Perm (Fin n))
    (hcov : ∀ g : Matrix.GeneralLinearGroup (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (Matrix.GeneralLinearGroup (Fin n) F)) (blockUpper F n γ))
    (hanti : Antitone fun j => cellHeight β γ (permGL F (w j)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
    (hσ : IsSmooth σ) :
    ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
      V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
      ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
        ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
            ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
            (twist ((invSqrtModular F n γ).comp leviIncl)
              (indRep (cellLeviSub F β γ (w j)) (cellInducing β γ (w j) σ))),
          Function.Surjective Ψ ∧
            ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  set C : Fin k → Set (Matrix.GeneralLinearGroup (Fin n) F) := fun l =>
    doubleCoset (permGL F (w l)) (blockUpper F n β : Set (Matrix.GeneralLinearGroup (Fin n) F))
      (blockUpper F n γ)
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro g hgi hgj
    obtain ⟨l, -, hl⟩ := hcov g
    exact hij ((hl i hgi).trans (hl j hgj).symm)
  have hcov' : ∀ g, ∃ l, g ∈ C l := fun g => (hcov g).exists
  have hcl := closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨fun i => jacquetFiltration γ (σ := σ) (cellUnion C i), ?_, ?_, ?_, ?_⟩
  · show jacquetFiltration γ (cellUnion C 0) = ⊥
    rw [cellUnion_zero, jacquetFiltration_empty]
  · show jacquetFiltration γ (cellUnion C k) = ⊤
    rw [cellUnion_of_cover hcov', jacquetFiltration_univ]
  · exact fun i i' h => jacquetFiltration_mono γ (cellUnion_mono h)
  refine ⟨fun i m => jacquetFiltration_le_comap γ (cellUnion_mul_mem w i).1 m, fun j => ?_⟩
  have hYo : IsOpen (cellUnion C ((j : ℕ) + 1)) := isOpen_cellUnion hdisj hcov' hcl _
  have hCY : closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j :=
    closure_inter_cellUnion_succ hdisj hcl j
  have hYQ := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).1
  have hYP := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).2
  have hdiff : cellUnion C ((j : ℕ) + 1) \ C j = cellUnion C j := by
    rw [cellUnion_succ j, union_sdiff_right, (disjoint_cellUnion hdisj j).symm.sdiff_eq_left]
  refine ⟨⟨gradedJacquetMap γ (w j) σ hYo hCY hYQ, fun m => ?_⟩, ?_, fun x => ?_⟩
  · refine LinearMap.ext fun x => ?_
    exact gradedJacquetMap_jacquetRep σ hYo hCY hYQ m x
  · exact gradedJacquetMap_surjective σ hYo hCY hYQ (cellJacquetMap_surjective hYo hCY hYP hYQ hσ)
  · have := gradedJacquetMap_eq_zero_iff σ hYo hCY hYQ
      (fun f hf h0 => exists_sub_mem_ker_of_cellJacquet_eq_zero σ hσ hYo hCY hYQ hf h0) x
    rw [hdiff] at this
    exact this

theorem normalized_piece {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (levi F n β) W) (w : Equiv.Perm (Fin n))
    {A : Type} [AddCommGroup A] [Module ℂ A] {ρ : Representation ℂ (levi F n γ) A}
    (Ψ₀ : Representation.IntertwiningMap ρ
      (twist ((invSqrtModular F n γ).comp leviIncl)
        (indRep (cellLeviSub F β γ w) (cellInducing β γ w σ))))
    (hsurj : Function.Surjective Ψ₀) :
    ∃ Ψ : Representation.IntertwiningMap ρ (indRep (cellLeviSub F β γ w) (normInducing σ γ w)),
      Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ Ψ₀ x = 0 := by
  refine ⟨(indCongrHom σ w).comp ((indTwistHom σ w).comp Ψ₀), ?_, fun x => ?_⟩
  · exact (indCongrHom_surjective σ w).comp ((indTwistHom_surjective σ w).comp hsurj)
  · constructor
    · intro h
      apply indTwistHom_injective σ w
      apply indCongrHom_injective σ w
      rw [map_zero, map_zero]
      exact h
    · intro h
      show (indCongrHom σ w) ((indTwistHom σ w) (Ψ₀ x)) = 0
      rw [h, map_zero, map_zero]

end Filtration

theorem geometricLemma_uniform : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  intro F _ _ _ _ n β γ
  obtain ⟨k, w, hcov, hanti⟩ := GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := F) β γ
  refine ⟨k, w, hcov, fun W _ _ σ hσ => ?_⟩
  obtain ⟨V, h0, hk, hmono, hV, hΨ⟩ := filtration_of_cellEnumeration (γ := γ) w hcov hanti σ hσ
  refine ⟨V, h0, hk, hmono, hV, fun j => ?_⟩
  obtain ⟨Ψ₀, hsurj, hker⟩ := hΨ j
  obtain ⟨Ψ, hΨs, hΨk⟩ := normalized_piece σ (w j) Ψ₀ hsurj
  exact ⟨Ψ, hΨs, fun x => (hΨk x).trans (hker x)⟩

end GlobalTheory.CompanionTheory.GeomLemmaUniform
end
end

section

set_option maxSynthPendingDepth 1

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
  GroundTheory.Automorphic.GodementSection IdeleGroup

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisRk1

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def infC (a : 𝔸[K]) : mixedSpace K := GroundTheory.Global.homeomorphMixedSpace K a.1

theorem infC_mul (a b : 𝔸[K]) : infC (a * b) = infC a * infC b :=
  homeomorphMixedSpace_mul _ _

theorem infC_add (a b : 𝔸[K]) : infC (a + b) = infC a + infC b := by
  simp only [infC, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace K) a.1 b.1

theorem infC_algebraMap (x : K) : infC (algebraMap K 𝔸[K] x) = mixedEmbedding K x := by
  simp only [infC, adeleRing_algebraMap_fst, homeomorphMixedSpace_algebraMap]

theorem continuous_infC : Continuous (infC (K := K)) :=
  (homeomorphMixedSpace K).continuous.comp continuous_fst

theorem exists_ideal_of_isCompact {S : Set 𝔸ᶠ[K]} (hS : IsCompact S) :
    ∃ (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (κ₀ : ℝ), 0 < κ₀ ∧
      (∀ ξ : K, algebraMap K 𝔸ᶠ[K] ξ ∈ S → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K)) ∧
      ∀ ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K), ξ ≠ 0 →
        κ₀ ≤ mixedEmbedding.norm (mixedEmbedding K ξ) := by
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hNd : ((Algebra.norm ℚ dK : ℚ) : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 hdK
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)),
    |((Algebra.norm ℚ dK : ℚ) : ℝ)|⁻¹, inv_pos.2 (abs_pos.2 hNd), ?_, ?_⟩
  · intro ξ hmem
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]
  · intro ξ hξ hξ0
    obtain ⟨r', hr'⟩ := (FractionalIdeal.mem_spanSingleton _).1 hξ
    have hr'0 : r' ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hr'
      exact hξ0 hr'.symm
    have hmul : Algebra.norm ℚ dK * Algebra.norm ℚ ξ = Algebra.norm ℚ (r' : K) := by
      rw [← map_mul, ← hr', Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ hdK, mul_one]
    have hξN : ((Algebra.norm ℚ ξ : ℚ) : ℝ) =
        ((Algebra.norm ℚ (r' : K) : ℚ) : ℝ) * ((Algebra.norm ℚ dK : ℚ) : ℝ)⁻¹ := by
      rw [← hmul, Rat.cast_mul]
      field_simp
    rw [mixedEmbedding.norm_eq_norm, Rat.cast_abs, hξN, abs_mul, abs_inv]
    exact le_mul_of_one_le_left (by positivity) (one_le_abs_norm_of_ne_zero hr'0)

theorem norm_le_norm_infC_moduleSection_mul (w : InfinitePlace K) {t : {x : ℝ // 0 < x}}
    (ht : 1 ≤ (t : ℝ)) (x : mixedSpace K) :
    ‖x‖ ≤ ‖infC ((moduleSection w t : NumberField.IdeleGroup (𝓞 K) K) : 𝔸[K]) * x‖ := by
  set e := infC ((moduleSection w t : NumberField.IdeleGroup (𝓞 K) K) : 𝔸[K])
  set e' := infC ((moduleSection w t⁻¹ : NumberField.IdeleGroup (𝓞 K) K) : 𝔸[K])
  have hee : e' * e = 1 := by
    rw [← infC_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    simp only [infC, homeomorphMixedSpace_apply]
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  have he' : ∀ v, normAtPlace v e' ≤ 1 := by
    intro v
    simp only [e', infC]
    rw [normAtPlace_homeomorphMixedSpace]
    refine norm_moduleSection_apply_le_one w ?_ v
    change (t : ℝ)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ ht
  calc ‖x‖ = ‖e' * (e * x)‖ := by rw [← mul_assoc, hee, one_mul]
    _ ≤ ‖e * x‖ := norm_mul_le_of_normAtPlace_le_one he' _

theorem norm_infC_moduleSection (w : InfinitePlace K) (t : {x : ℝ // 0 < x}) :
    mixedEmbedding.norm (infC ((moduleSection w t : NumberField.IdeleGroup (𝓞 K) K) : 𝔸[K])) = t := by
  have h := mixedEmbedding_norm_toInfinite (moduleSection w t)
  rw [infiniteModule_moduleSection] at h
  exact h

end

end GlobalTheory.CompanionTheory.EisRk1
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem eq_one_of_pow_eq_one_of_valuation_sub_lt {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m : ℕ} {ξ : K}
    (hm : v (m : K) = 1) (hξ : ξ ^ m = 1) (h : v (ξ - 1) < 1) : ξ = 1 := by
  have hv : v ξ ≤ 1 := by
    have e : ξ = (ξ - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le h.le (by simp))
  have hp : ∀ i : ℕ, v (ξ ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : ξ ^ (i + 1) - 1 = ξ * (ξ ^ i - 1) + (ξ - 1) := by ring
      rw [e]
      refine Valuation.map_add_lt v ?_ h
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hv) ih
  have hs : v ((∑ i ∈ Finset.range m, ξ ^ i) - (m : K)) < 1 := by
    have e : (∑ i ∈ Finset.range m, ξ ^ i) - (m : K) = ∑ i ∈ Finset.range m, (ξ ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    exact Valuation.map_sum_lt v one_ne_zero fun i _ => hp i
  have hsum : (∑ i ∈ Finset.range m, ξ ^ i) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hm] at hs
    exact lt_irrefl _ hs
  have := mul_geom_sum ξ m
  rw [hξ, sub_self] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum)

theorem natCast_residue_eq_zero {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F (Om l)]
    [ValuativeExtension F (Om l)] : (l : 𝓀[F]) = 0 := by
  have hnl : ¬ ((1 : F) ≤ᵥ (l : F)) := by
    intro h
    have h2 := (ValuativeExtension.vle_iff_vle (A := F) (B := Om l)).2 h
    rw [map_one, map_natCast, GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, norm_one,
      ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends] at h2
    exact absurd (Padic.norm_natCast_lt_one_iff.mpr (dvd_refl l)) (not_lt.mpr h2)
  have hlt : valuation F (((l : 𝒪[F]) : 𝒪[F]) : F) < 1 := by
    refine not_le.mp fun h => hnl ?_
    rw [Valuation.Compatible.vle_iff_le (v := valuation F), map_one]
    simpa using h
  have hmem : (l : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
    exact ne_of_lt hlt
  rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
  exact hmem

theorem unramifiedDegree_eq_one_of_mem_inertia : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  intro l _ E Ω _ _ _ _ _ A O _ _ _ Bw hj F _ _ _ _ _ _ _ σ hσ g hg
  rw [GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  intro ζ hζ
  obtain ⟨m, hm, hζm⟩ := mem_unramifiedRoots_iff.1 hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hcop : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply hm
    rw [Nat.cast_mul, natCast_residue_eq_zero (l := l) (F := F), zero_mul]
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero m := ⟨hm0⟩
  have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ₀, h₀⟩ : ∃ z : Ω, IsPrimitiveRoot z m := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hj0 := h₀.map_of_injective Bw.j.injective
  obtain ⟨i, -, hi⟩ := hj0.eq_pow_of_pow_eq_one hζm

  obtain ⟨z, hz, hzm⟩ : ∃ z : Ω, Bw.j z = ζ ∧ z ^ m = 1 :=
    ⟨ζ₀ ^ i, by rw [map_pow, hi], by rw [← pow_mul, mul_comm, pow_mul, h₀.pow_eq_one, one_pow]⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [hm0] at hzm
  let s : G E Ω := (σ : G E Ω)
  have hgz : g ζ = Bw.j (s z) := by
    rw [hg, ← hz]
    exact Bw.e_comm σ z
  have hnorm : ‖Bw.j z‖ = 1 := by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp ?_
    rw [← norm_pow, ← map_pow, hzm, map_one, norm_one]
  have hzA : A.valuation z ≤ 1 := by
    rw [A.valuation_le_one_iff]
    exact (hj z).mpr hnorm.le
  have hzunit : A.valuation z = 1 :=
    le_antisymm hzA (not_lt.mp fun h => ((hj.valuation_lt_one_iff z).mp h).ne hnorm)
  have hlt : A.valuation (s z - z) < 1 := hσ.2 z hzA
  have hmn : ‖Bw.j (m : Ω)‖ = 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop
  have hmv : A.valuation (m : Ω) = 1 := by
    refine le_antisymm ?_ (not_lt.mp fun h => ((hj.valuation_lt_one_iff _).mp h).ne hmn)
    rw [A.valuation_le_one_iff]
    exact (hj _).mpr hmn.le
  have hsz : (s z / z) ^ m = 1 := by
    rw [div_pow, ← map_pow, hzm, map_one, div_one]
  have hone : s z / z = 1 := by
    refine eq_one_of_pow_eq_one_of_valuation_sub_lt A.valuation hmv hsz ?_
    have e : s z / z - 1 = (s z - z) / z := by field_simp
    rw [e, map_div₀, hzunit, div_one]
    exact hlt
  rw [hgz, (div_eq_one_iff_eq hz0).mp hone, hz]

end GlobalTheory.CompanionTheory.LTLink
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.smooth_monotone_cutoff_exists : ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut | exact GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut | (intros; apply GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.energy_density_pointwise_estimate : ∀ {W ι : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι] (w v : W) (Y : ι → W) (L : ι → ℝ) (A : W →L[ℝ] W) (C₁ C c φ : ℝ), 0 ≤ C₁ → C₁ * (1 + Fintype.card ι) ≤ C → c ≤ 0 → 0 ≤ φ → (∀ p, |L p| ≤ C₁) → c * C * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2) + φ * (2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ) - (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (‖A‖ + 1) * (φ * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2)) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq | exact GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles

theorem sum_locDeg_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime]
    (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) →
    ∑ v ∈ T, locDeg v = Module.finrank ℚ F := by
  intro F _ _ l _ T hT
  let _ : Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} := Fintype.subtype T hT
  rw [Finset.sum_subtype T hT]
  exact GlobalTheory.Proof.LocalDegreeSum.sum_locDeg F l

end GlobalTheory.CompanionTheory.GreenbergWiles
end
