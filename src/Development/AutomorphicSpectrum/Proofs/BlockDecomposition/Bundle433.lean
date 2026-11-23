module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle401
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle422
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle421
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicBump

open NumberField IsDedekindDomain _root_.Topology
open scoped Classical

theorem exists_compact_open_nhds (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {w₀ : κ → FiniteAdeleRing (𝓞 F) F} {B : Set (κ → FiniteAdeleRing (𝓞 F) F)} (hB : B ∈ 𝓝 w₀) :
    ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsOpen C ∧ IsCompact C ∧ IsClosed C ∧ w₀ ∈ C ∧ C ⊆ B := by
  rw [nhds_pi, Filter.mem_pi] at hB
  obtain ⟨I, -, t, ht, hsub⟩ := hB
  have hO : (⋂ i, (fun a => w₀ i + a) ⁻¹' t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    Filter.iInter_mem.mpr fun i =>
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht i)
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  have hNF : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, mul_inv_cancel₀ hNF, map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F :=
    { toFun := fun u => c * u
      invFun := fun u => (N : FiniteAdeleRing (𝓞 F) F) * u
      left_inv := fun u => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u) = u
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u) = u
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  let D : κ → Set (FiniteAdeleRing (𝓞 F) F) := fun i =>
    (Homeomorph.subRight (w₀ i)) ⁻¹' (h ⁻¹' (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)))
  have hDc : ∀ i, IsCompact (D i) := fun i =>
    (Homeomorph.subRight (w₀ i)).isCompact_preimage.2 (h.isCompact_preimage.2 hint_c)
  have hDo : ∀ i, IsOpen (D i) := fun i =>
    (hint_o.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  have hint_l : IsClosed (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (Formalism.UG.intAd F).toAddSubgroup.isClosed_of_isOpen hint_o
  have hDl : ∀ i, IsClosed (D i) := fun i =>
    (hint_l.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  refine ⟨Set.univ.pi D, isOpen_set_pi Set.finite_univ fun i _ => hDo i, isCompact_univ_pi hDc,
    isClosed_set_pi fun i _ => hDl i, fun i _ => ?_, fun u hu => hsub fun i _ => ?_⟩
  · show c * (w₀ i - w₀ i) ∈ (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))
    rw [sub_self, mul_zero]
    exact zero_mem (Formalism.UG.intAd F)
  · have hi : c * (u i - w₀ i) ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have h1 := Set.mem_iInter.mp (hNO _ hi) i
    rw [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at h1
    simpa using h1

theorem exists_bump : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : Set (κ → AF F)), IsOpen N → ∀ z₀ ∈ N, ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N → Φ z = 0) ∧ 0 < (Φ z₀).re := by
  intro F _ _ κ _ N hN z₀ hz₀
  let P : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hP : Continuous P := continuous_pi fun i =>
    Continuous.prodMk ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst))
      ((continuous_apply i).comp continuous_snd)
  let y₀ : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1
  let w₀ : κ → FiniteAdeleRing (𝓞 F) F := fun i => (z₀ i).2
  have hPz : ∀ z : κ → AdeleRing (𝓞 F) F,
      P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) = z := fun z =>
    funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  have hmem : P ⁻¹' N ∈ 𝓝 (y₀, w₀) :=
    (hN.preimage hP).mem_nhds (by show P (y₀, w₀) ∈ N; rw [hPz z₀]; exact hz₀)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (E := κ → mixedEmbedding.mixedSpace F) (n := ⊤) hA
  obtain ⟨C, hCo, hCc, hCcl, hwC, hCB⟩ := exists_compact_open_nhds F hB
  have hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ) :=
    hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)
  have hf : ∀ y, f y = ((φ y : ℝ) : ℂ) := fun y => rfl
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator C fun _ => 1
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hCc fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ C
    · exact ⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by
        simp only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩
  have hval : ∀ z, GlobalTheory.WeilM.pureA F f g z = ((φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) : ℝ) : ℂ) *
      g (fun i => (z i).2) := fun z => rfl
  have hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ) := fun w => by
    by_cases hw : w ∈ C <;> simp [g, hw]
  have hnn : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  refine ⟨GlobalTheory.WeilM.pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, fun z => ?_, fun z hz => ?_, ?_⟩
  · rw [hval, hgval, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩
  · rw [hval]
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have h1' : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) ≠ 0 := fun h => h1 (by rw [h]; simp)
    have h2' : (fun i => (z i).2) ∈ C := by
      by_contra h
      exact h2 (Set.indicator_of_notMem h _)
    have h3 := hAB (Set.mk_mem_prod (hφs (subset_tsupport _ h1')) (hCB h2'))
    apply hz
    have h4 : P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) ∈ N := h3
    rwa [hPz z] at h4
  · rw [hval]
    have e1 : g (fun i => (z₀ i).2) = 1 := Set.indicator_of_mem (show w₀ ∈ C from hwC) _
    have e2 : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1) = 1 := hφ1
    rw [e1, e2]
    simp

end GlobalTheory.CompanionTheory.AdelicBump

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (n : ℕ) :
    HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n) where
  toFun b w := ⟨matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w, by
    refine mem_hermC.2 ?_
    ext a c
    simp only [Matrix.conjTranspose_apply, matC, RCLike.star_def]
    rw [← hconj, b.2 a c]⟩
  invFun G := ⟨fun a c => Θ.symm fun w => (G w : Matrix (Fin n) (Fin n) ℂ) a c, by
    intro a c
    apply Θ.injective
    funext w
    have h : (G w : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 (G w).2
    rw [hconj]
    simp only [RingEquiv.apply_symm_apply]
    have := congrFun (congrFun h a) c
    simpa [Matrix.conjTranspose_apply] using this⟩
  left_inv b := by
    apply Subtype.ext
    ext a c
    simp [matC]
  right_inv G := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]
  map_add' b b' := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]

theorem continuous_hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n) := by
  refine continuous_pi fun w => Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  have h1 : Continuous fun b : HermR (Ainf F) σ n =>
      (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact (continuous_apply w).comp (hΘ.comp h1)

theorem continuous_hermEquiv_symm (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ.symm) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n).symm := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  refine hΘ.comp (continuous_pi fun w => ?_)
  have h1 : Continuous fun b : hermC n => (b : Matrix (Fin n) (Fin n) ℂ) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact h1.comp (continuous_apply w)

theorem continuous_symm (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    Continuous Θ.symm := by
  have e : (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) = (hΘ.homeomorph Θ).symm := by
    funext y
    apply (hΘ.homeomorph Θ).injective
    rw [Homeomorph.apply_symm_apply]
    exact Θ.apply_symm_apply y
  rw [e]
  exact (hΘ.homeomorph Θ).symm.continuous

theorem topAddGroup_tens (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    IsTopologicalAddGroup (Ainf F ⊗[F] E) := by
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  refine { continuous_add := ?_, continuous_neg := ?_ }
  · have : (fun p : (Ainf F ⊗[F] E) × (Ainf F ⊗[F] E) => p.1 + p.2) =
        fun p => Θ.symm (Θ p.1 + Θ p.2) := by
      funext p; simp
    rw [this]
    exact c2.comp ((c1.comp continuous_fst).add (c1.comp continuous_snd))
  · have : (fun x : Ainf F ⊗[F] E => -x) = fun x => Θ.symm (-Θ x) := by
      funext x; simp
    rw [this]
    exact c2.comp c1.neg

theorem exists_hermEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  intro F E _ _ _ _ _ σ _ e τ Θ hc n
  obtain ⟨hΘ, hconj, -, -⟩ := hc
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  haveI := topAddGroup_tens Θ hΘ
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  have h1 := continuous_hermEquiv σ Θ hconj c1 n
  have h2 := continuous_hermEquiv_symm σ Θ hconj c2 n
  refine ⟨hermEquiv σ Θ hconj n, fun b w => rfl, fun ν hν => ⟨?_, fun G hG => ?_⟩⟩
  · exact AddEquiv.isAddHaarMeasure_map ν (hermEquiv σ Θ hconj n) h1 h2
  · exact hG.comp_measurable h1.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord
end
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

theorem _root_.GlobalTheory.T.cuspidal_restrict_mem_cuspidal_l2 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (φ : GA E a → ℂ), φ ∈ cuspCont E a → ∀ h : MemLp (resQ φ) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν), h.toLp (resQ φ) ∈ cuspidalL2 ν := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 | exact GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.toLp_restrict_mem_cuspidalL2 <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.convolution_maximal_compact_equivariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ), ConjInv β → ∀ (F : L2 (latticeGL E a) μ) (k : Kinf E a) (x : GA E a), convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x = convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt | exact GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.convolution_right_invariant_open_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (u : GL (Fin a) (Af E)), u ∈ U → ∀ x : GA E a, convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant | exact GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.IsomT

variable {X : Scheme.{0}}

theorem res_twice {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom (u : Γ(X, U))) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom (u : Γ(X, U))
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem units_ext_cover {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) {W : X.Opens}
    {f g : Γ(X, W)ˣ} (h : ∀ i, res (inf_le_left : W ⊓ V i ≤ W) f = res inf_le_left g) : f = g := by
  apply Units.ext
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
    fun i => ?_
  exact congrArg Units.val (h i)

theorem exists_glue {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) (W : X.Opens)
    (f : ∀ i, Γ(X, W ⊓ V i)ˣ)
    (hf : ∀ i j, res (inf_le_left : (W ⊓ V i) ⊓ (W ⊓ V j) ≤ W ⊓ V i) (f i) =
      res inf_le_right (f j)) :
    ∃ u : Γ(X, W)ˣ, ∀ i, res inf_le_left u = f i := by
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => ((f i : Γ(X, W ⊓ V i))))
    (fun i j => congrArg Units.val (hf i j))
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => (((f i)⁻¹ : Γ(X, W ⊓ V i)ˣ) : Γ(X, W ⊓ V i)))
    (fun i j => by
      have := congrArg Units.val (congrArg (·⁻¹) (hf i j))
      rw [← map_inv, ← map_inv] at this
      exact this)
  have hst : s * t = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
      fun i => ?_
    rw [map_mul, map_one, hs i, ht i]
    exact (f i).mul_inv
  refine ⟨⟨s, t, hst, by show (t : Γ(X, W)) * s = 1; rw [mul_comm]; exact hst⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem ofMem {V U : X.Opens} (h : ∀ x, x ∈ V → x ∈ U) : V ≤ U := by
  intro x hx
  exact h x hx

end GlobalTheory.CompanionTheory.MPDict.IsomT

namespace GlobalTheory.CompanionTheory.MPDict

open IsomT

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k)
    {W W' : (MP ℤ m n).Opens} (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    res h' (blockUnit i j h) = blockUnit i j (h'.trans h) := by
  unfold blockUnit
  exact res_twice _ _ _

theorem res_mul_prod (c c' : ∀ k, Bk n k) (e : Fin (m + 1) → ℤ)
    {W W' : (MP ℤ m n).Opens} (x : Γ(MP ℤ m n, W)ˣ)
    (H : ∀ k, W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) (h' : W' ≤ W) :
    res h' (x * ∏ k, blockUnit (c k) (c' k) (H k) ^ e k) =
      res h' x * ∏ k, blockUnit (c k) (c' k) (h'.trans (H k)) ^ e k := by
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, res_blockUnit]

end GlobalTheory.CompanionTheory.MPDict
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

private theorem C_mem_ptIdeal_iff_intCast_residueField_eq_zero (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (c : ℤ) :
    (MvPolynomial.C c : Geo.MRing (Bk n)) ∈ ptIdeal x ↔ ((c : ℤ) : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C, eq_intCast,
    ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField x →+* MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) c,
    MvPolynomial.C_eq_zero]

theorem ptIdeal_isHorizontal_iff (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsHorizontal (ptIdeal x) ↔ CharZero ((MP ℤ m n).residueField x) := by
  constructor
  · intro h
    have h' : (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥ := h
    refine charZero_of_inj_zero fun k hk => ?_
    have hm : ((k : ℤ)) ∈ (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) := by
      rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero]
      exact_mod_cast hk
    rw [h', Ideal.mem_bot] at hm
    exact_mod_cast hm
  · intro h
    show (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_bot]
    rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero] at hc
    exact Int.cast_eq_zero.mp hc

end GlobalTheory.CompanionTheory.MPDict
end
end

section

open GlobalTheory.DiscSpec

theorem _root_.GlobalTheory.T.multiset_of_strings_determines_points_degrees : ∀ {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X) (d' : κ → ℕ), (∀ i, 1 ≤ d i) → (∀ j, 1 ≤ d' j) → GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d' → ∃ s : ι ≃ κ, ∀ i, p i = p' (s i) ∧ d i = d' (s i) := by
  first | exact @GlobalTheory.CompanionTheory.Rigid.strings_rigid | exact GlobalTheory.CompanionTheory.Rigid.strings_rigid | (intros; apply GlobalTheory.CompanionTheory.Rigid.strings_rigid <;> assumption)
end
