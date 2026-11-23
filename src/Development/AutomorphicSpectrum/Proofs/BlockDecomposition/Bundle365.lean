module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle343
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalShuffleCountProduct
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle075
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle346
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.PAdicHodge.Bundle004
public import GroundTheory.PAdicHodge.NormalizedTraceTower
public import GroundTheory.PAdicHodge.SenTateCharTower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle348
public import GroundTheory.PAdicHodge.Bundle003
public import GroundTheory.PAdicHodge.UnramifiedClosure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenPeriodFiniteExtension
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle077
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle150
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle094
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle089
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle345
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.jacquet_multiplicity_transitive_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {g N : ℕ} (y : Fin g → IrrGL (k := k)) (hy : ∑ b, (y b).1 = N) (Wb : Fin g → List (IrrGL (k := k))) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → (∀ b, ∑ a, ((Wb b).get a).1 = (y b).1) → jm y hy π * ∏ b, jmL (Wb b) (y b).rep ≤ jmL (List.ofFn Wb).flatten π := by
  first | exact @GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | exact GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | (intros; apply GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.canonical_segments_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → IsRevOrdered Γ := by
  first | exact @GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | exact GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | (intros; apply GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.exists_canonical_segment_order : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), ∃ σ : Equiv.Perm (Fin h), IsCanon (Γ ∘ σ) := by
  first | exact @GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon | exact GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon | (intros; apply GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open Classical

theorem _root_.GlobalTheory.T.canonical_shuffle_count_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → shuffleCount (List.ofFn fun i => decWord (Γ i)).flatten (fun i => decWord (Γ i)) = ∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Γ j = Γ i).card := by
  first | exact @GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon | exact GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon | (intros; apply GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcMerge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def fromA (a : Comb.ASeg (CuspT k)) : Segment k := Segment.ofFirst a.start.1 a.start.2 a.len a.len_pos

theorem toA_fromA (a : Comb.ASeg (CuspT k)) : toA (fromA a) = a := rfl

theorem fromA_toA (Δ : Segment k) : fromA (toA Δ) = Δ := Segment.ext_first rfl rfl

theorem carrier_subset_of_image {Δ Δ' : Segment k} (h : (toA Δ).carrier sNu ⊆ (toA Δ').carrier sNu) :
    Δ.carrier ⊆ Δ'.carrier := by
  rw [← ZcWords.image_carrier, ← ZcWords.image_carrier]
  exact Set.image_mono h

theorem aPrecedes_of_precedes {Δ Δ' : Segment k} (h : Δ.Precedes Δ') : Comb.APrecedes sNu (toA Δ) (toA Δ') := by
  obtain ⟨⟨⟨Γ, hΓ⟩, h1, h2⟩, j, hj, hs⟩ := h
  refine ⟨⟨⟨toA Γ, ?_⟩, fun e => h1 (carrier_subset_of_image e), fun e => h2 (carrier_subset_of_image e)⟩, j, hj,
    Subtype.ext ?_⟩
  · apply Set.image_injective.2 (Subtype.val_injective (p := fun x : IrrGL (k := k) => x.IsCusp))
    rw [Set.image_union, ZcWords.image_carrier, ZcWords.image_carrier, ZcWords.image_carrier, hΓ]
  · exact hs.trans (ZcWords.val_sNu_iterate (toA Δ).start j).symm

theorem map_toA_map_fromA (L : List (Comb.ASeg (CuspT k))) : (L.map fromA).map toA = L := by
  rw [List.map_map]
  exact List.map_id'' toA_fromA L

theorem isOrderedForm_get {L : List (Comb.ASeg (CuspT k))} {𝔪 : Multiset (Segment k)}
    (hL : (L : Multiset (Comb.ASeg (CuspT k))) = 𝔪.map toA) (hO : Comb.AOrdered sNu L) :
    IsOrderedForm (L.map fromA).get 𝔪 := by
  constructor
  · rw [Fin.univ_val_map, List.ofFn_get, ← Multiset.map_coe, hL, Multiset.map_map]
    exact (Multiset.map_congr rfl fun Δ _ => fromA_toA Δ).trans (Multiset.map_id' 𝔪)
  · intro i j hij hp
    rw [Comb.AOrdered, ← map_toA_map_fromA L, List.pairwise_map] at hO
    exact List.pairwise_iff_get.1 hO i j hij (aPrecedes_of_precedes hp)

theorem wtW_get (L : List (Comb.ASeg (CuspT k))) :
    wtW (L.map fromA).get = (Comb.wt sNu L).map Subtype.val := by
  rw [ZcWords.wtW_eq, List.ofFn_get, map_toA_map_fromA]

theorem exists_common_orderedForm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)),
    ∃ (h₁ h₂ h : ℕ) (Δ₁ : Fin h₁ → Segment k) (Δ₂ : Fin h₂ → Segment k) (Δ : Fin h → Segment k),
      IsOrderedForm Δ₁ 𝔪 ∧ IsOrderedForm Δ₂ 𝔫 ∧ IsOrderedForm Δ (𝔪 + 𝔫) ∧
        Zc.Comb.Interleave (wtW Δ₁) (wtW Δ₂) (wtW Δ) := by
  intro k _ _ _ _ _ 𝔪 𝔫
  obtain ⟨L₁, L₂, L, h1, h2, h3, o1, o2, o3, hI⟩ := GlobalTheory.CompanionTheory.SegOrder.exists_common_ordered_form (sNu (k := k)) ZcWords.sNu_injective
    ZcWords.sNu_aperiodic (𝔪.map toA) (𝔫.map toA)
  refine ⟨_, _, _, (L₁.map fromA).get, (L₂.map fromA).get, (L.map fromA).get, isOrderedForm_get h1 o1,
    isOrderedForm_get h2 o2, isOrderedForm_get (by rw [h3, Multiset.map_add (f := _)]) o3, ?_⟩
  rw [wtW_get, wtW_get, wtW_get]
  exact ZcWords.interleave_map _ hI

end GlobalTheory.CompanionTheory.ZcMerge

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.ordered_forms_mutual_shuffle_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (h h' : ℕ) (Δ : Fin h → Segment k) (Γ : Fin h' → Segment k), IsOrderedForm Δ 𝔪 → IsOrderedForm Γ 𝔫 → InShW 𝔫 (wtW Δ) → InShW 𝔪 (wtW Γ) → 𝔪 = 𝔫 := by
  first | exact @GlobalTheory.CompanionTheory.ZcWords.eq_of_inShW_wtW | exact GlobalTheory.CompanionTheory.ZcWords.eq_of_inShW_wtW | (intros; apply GlobalTheory.CompanionTheory.ZcWords.eq_of_inShW_wtW <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.ordered_word_letters_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k), ∀ c ∈ wtW Δ, c.IsCusp := by
  first | exact @GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | exact GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | (intros; apply GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.word_occurs_of_subquotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth π → IsSubquotient σ π → ∀ w : List (IrrGL (k := k)), Wd σ w → Wd π w := by
  first | exact @GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient | exact GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.Words.wd_of_isSubquotient <;> assumption)
end

section

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.RmHol.GelCoef

variable {n : ℕ}

theorem Eu_of_differentiableAt {f : Mat n → ℂ} {z : Mat n} (hf : DifferentiableAt ℂ f z) (a b : Fin n) :
    Eu true a b f z = fderiv ℂ f z (z * Matrix.single a b 1) ∧ Eu false a b f z = 0 := by
  have hR : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
    (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  have hI : z * Matrix.single a b Complex.I = Complex.I • (z * Matrix.single a b (1 : ℂ)) := by
    rw [← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, if_true, hR,
      ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
    linear_combination (-(1 / 2 : ℂ) * fderiv ℂ f z (z * Matrix.single a b (1 : ℂ))) * hII
  · simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, hR, Bool.false_eq_true, if_false,
      ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
    linear_combination ((1 / 2 : ℂ) * fderiv ℂ f z (z * Matrix.single a b (1 : ℂ))) * hII

theorem Eu_congr_germ {f h : Mat n → ℂ} {g : Mat n} (e : f =ᶠ[𝓝 g] h) (s : Bool) (a b : Fin n) :
    Eu s a b f g = Eu s a b h g := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, e.fderiv_eq]

end GlobalTheory.CompanionTheory.RmHol.GelCoef
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.sen_unramified_character_period : ∀ {l : ℕ} [Fact l.Prime], ∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | exact GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | (intros; apply GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.sen_period_finite_extension : ∀ {l : ℕ} [Fact l.Prime],
    (∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x) →
    ∀ (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
      ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.cycloChar_inertia_image_infinite | exact GlobalTheory.CompanionTheory.LTPer.cycloChar_inertia_image_infinite | (intros; apply GlobalTheory.CompanionTheory.LTPer.cycloChar_inertia_image_infinite <;> assumption)
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxAbs

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (absLogNorm)

theorem absFibreSum_eq_sum_components_ae {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι} {A : HermLine ι}
    {s : MRing ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w| =
      ∑ᶠ Q ∈ (cxIdeal P).minimalPrimes, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w| := by
  classical
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hmeet := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentsMeetNull.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDimLt.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartRatioImageNull.proof K ι P e Ψ hfin.toFinset hP hΨ
    (fun W hW => hfin.mem_toFinset.1 hW)
  filter_upwards [compl_mem_ae_iff.mpr hmeet, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hone : ∀ Q ∈ (cxIdeal P).minimalPrimes, ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q →
      z ∈ conePts Q' → Ψ (segre z) = Fin.cons 1 y → Q' = Q := by
    intro Q hQ Q' hQ' z hz hz' hΨz
    by_contra hne
    refine hyN ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hΨz, Q, hfin.mem_toFinset.2 hQ, Q',
      hfin.mem_toFinset.2 hQ', fun h => hne h.symm, ?_, ?_⟩
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz.2 f hf
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz'.2 f hf
  have hunion : fibre P Ψ y = ⋃ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y := by
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz, hzw, hΨw⟩
      obtain ⟨Q, hQ, hzQ⟩ := exists_minimal_of_mem_mcPts hz
      exact ⟨Q, hQ, z, hzQ, hzw, hΨw⟩
    · rintro ⟨Q, hQ, z, hz, hzw, hΨw⟩
      exact ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hzw, hΨw⟩
  have hsub : ∀ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y ⊆ fibre P Ψ y := by
    intro Q hQ w hw
    rw [hunion]
    exact Set.mem_biUnion hQ hw
  have hdisj : ((cxIdeal P).minimalPrimes).PairwiseDisjoint fun Q => setFibre (conePts Q) Ψ y := by
    intro Q hQ Q' hQ' hne
    refine Set.disjoint_left.2 ?_
    rintro w ⟨z, hz, hzw, hΨw⟩ ⟨z', hz', hzw', -⟩
    have hzQ' : z ∈ conePts Q' := mem_conePts_of_segre_eq hP hQ' hz' hz.1 (hzw'.trans hzw.symm)
    exact hne (hone Q hQ Q' hQ' z hz hzQ' (by rw [hzw]; exact hΨw)).symm
  rw [hunion, finsum_mem_biUnion hdisj hfin
    (fun Q hQ => (fibreFinite K ι P e Ψ hP hΨ y).subset (hsub Q hQ))]
  refine finsum_mem_congr rfl fun Q hQ => finsum_mem_congr rfl fun w hw => ?_
  refine congrArg abs ?_
  have hiff : (∃ γ, IsSheet P Ψ y w γ) ↔ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ :=
    ⟨fun ⟨γ, h⟩ => ⟨γ, isSetSheet_of_isSheet hP hQ (hone Q hQ) hw h⟩,
      fun ⟨γ, h⟩ => ⟨γ, isSheet_of_isSetSheet hQ h⟩⟩
  rw [sheetDensity_eq_setSheetDensity]
  unfold setSheetDensity
  by_cases hex : ∃ γ, IsSheet P Ψ y w γ
  · have hexQ := hiff.1 hex
    have hexP : ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dite_eq_left hexP, dite_eq_left hexQ]
    exact hind w _ _ hexP.choose_spec (isSheet_of_isSetSheet hQ hexQ.choose_spec)
  · have hexQ : ¬ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ := fun h => hex (hiff.2 h)
    have hexP : ¬ ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dite_eq_right hexP, dite_eq_right hexQ]

theorem abs_setSheetDensity_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} (hS : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (A : HermLine ι) (s : MRingOver ℂ ι) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    |setSheetDensity S Ψ φ (logNormC A s) y w| =
      max (setSheetDensity S Ψ φ (absLogNorm A s) y w) 0 +
        max (setSheetDensity S Ψ φ (fun z => -absLogNorm A s z) y w) 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · have hz := hS _ hγ.choose_spec.2.self_of_nhds.2.1
    have ha : absLogNorm A s (hγ.choose y) = |logNormC A s (hγ.choose y)| := by
      simp only [absLogNorm, if_pos hz]
    beta_reduce
    rw [ha, abs_mul]
    generalize maDensity (fun j y' => φ j (hγ.choose y')) y = m
    generalize logNormC A s (hγ.choose y) = g
    have hg := abs_nonneg g
    rcases le_total 0 m with hm | hm
    · rw [abs_of_nonneg hm, max_eq_left (mul_nonneg hg hm),
        max_eq_right (by nlinarith : -|g| * m ≤ 0), add_zero]
    · rw [abs_of_nonpos hm, max_eq_right (by nlinarith : |g| * m ≤ 0),
        max_eq_left (by nlinarith : 0 ≤ -|g| * m), zero_add]
      ring
  · simp

theorem integrable_absFibreSum_of_isCxVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) (hsQ : s ∉ Q) :
    Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) := by
  classical
  have hS : ∀ z ∈ conePts Q, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun z hz => hz.1
  have hfin := GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ hQ hΨ
  have hm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.measurable_absLogNorm A hA s
  have hdeg := fun (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) =>
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.absLogNorm_blockScale A hAa hs hc z
  have h1 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm hdeg
  have h2 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm.neg
    (g := fun z => -absLogNorm A s z) (fun c z hc => by simp only [hdeg c z hc])
  have heq : (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) =
      fun y => cxPosDens (conePts Q) Ψ (pot L) (absLogNorm A s) y +
        cxPosDens (conePts Q) Ψ (pot L) (fun z => -absLogNorm A s z) y := by
    funext y
    unfold cxPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => abs_setSheetDensity_eq hS Ψ (pot L) A s y w
  refine ⟨?_, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => abs_nonneg _)).2
    (GlobalTheory.T.lintegral_fibre_logNorm_finite K ι Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ)⟩
  rw [heq]
  exact (h1.add h2).aestronglyMeasurable

theorem ptsAbsIntegrable : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hae := absFibreSum_eq_sum_components_ae hP hΨ hL hA hs
  obtain ⟨a, hAa, hsa, hsP⟩ := hs
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hsa' : IsMultiHomog (map (Int.castRingHom ℂ) s : MRingOver ℂ ι) a := fun m hm k =>
    hsa m (support_map_subset _ _ hm) k
  have hcomp : ∀ Q ∈ (cxIdeal P).minimalPrimes, Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w|) := by
    intro Q hQ
    obtain ⟨hQv, hc⟩ := isCxVar_of_mem_minimalPrimes_cxIdeal K ι P e hP Q hQ
    refine integrable_absFibreSum_of_isCxVar hQv
      (fun z hz => hΨ z (conePts_subset_mcPts_of_minimal hQ hz)) hL hA hAa hsa' fun hmem => hsP ?_
    rw [← hc]
    exact hmem
  refine (integrable_finsetSum hfin.toFinset fun Q hQ => hcomp Q (hfin.mem_toFinset.1 hQ)).congr ?_
  filter_upwards [hae] with y hy
  rw [hy]
  exact (finsum_mem_eq_finite_toFinset_sum _ hfin).symm

end GlobalTheory.CompanionTheory.Ar.Pub.CxAbs
end
end
