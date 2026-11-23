module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinity
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle433
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle010
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.BlockMatrixIdentity.BlockMatOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle401
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec

open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

theorem real_indep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (b : Module.Basis (Fin 2) F E) (τ : E →+* ℂ) (s t : ℝ)
    (hst : (s : ℂ) * τ (b 0) + (t : ℂ) * τ (b 1) = 0) : s = 0 ∧ t = 0 := by
  obtain ⟨θ₀, hθ₀⟩ := exists_moved h
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ * b 0 = b 1 := ⟨b 1 / b 0, div_mul_cancel₀ _ hb0⟩
  have hmoved : σ θ ≠ θ := by
    intro hfix
    apply hθ₀
    obtain ⟨A, B, hAB⟩ : ∃ A B : F,
        θ₀ * b 0 = algebraMap F E A * b 0 + algebraMap F E B * b 1 :=
      ⟨_, _, by
        have := b.sum_repr (θ₀ * b 0)
        rw [Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def] at this
        exact this.symm⟩
    have h1 : θ₀ = algebraMap F E A + algebraMap F E B * θ := by
      apply mul_right_cancel₀ hb0
      rw [add_mul, mul_assoc, hθ]
      exact hAB
    rw [h1, map_add (f := _), map_mul, hfix, AlgHom.commutes, AlgHom.commutes]
  have him : (τ θ).im ≠ 0 := im_ne_zero h hmoved τ
  have hb1 : τ (b 1) = τ θ * τ (b 0) := by rw [← map_mul, hθ]
  have ht0 : τ (b 0) ≠ 0 := (map_ne_zero τ).2 hb0
  have h2 : (s : ℂ) + t * τ θ = 0 := by
    apply mul_right_cancel₀ ht0
    rw [zero_mul, add_mul, mul_assoc, ← hb1]
    exact hst
  have hi := congrArg Complex.im h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
    zero_mul, add_zero, Complex.zero_im] at hi
  have ht : t = 0 := (mul_eq_zero.1 hi).resolve_right him
  subst ht
  refine ⟨?_, rfl⟩
  simpa using h2

theorem eq_coord {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (b : Module.Basis (Fin 2) F E) (y : R ⊗[F] E) :
    y = (Algebra.TensorProduct.basis R b).repr y 0 ⊗ₜ[F] b 0 +
      (Algebra.TensorProduct.basis R b).repr y 1 ⊗ₜ[F] b 1 := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp

theorem linearIndependent_of_xw_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ X : Fin 1 → Fin M → Ainf F ⊗[F] E, (∀ w, xw e b X w ≠ 0) → LinearIndependent (Ainf F ⊗[F] E) X := by
  intro F E _ _ _ _ _ σ h M d b ρ e hρ he hx X hX
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  obtain rfl : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [h.2.2.1] at this
    simpa using this.symm
  have hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x := by
    intro w
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let t : E →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    exact ⟨t, fun x => t.commutes x⟩
  choose τ hτ using hex
  obtain ⟨Θ, hΘ⟩ := exists_hom e τ (fun x w => by rw [hx, hρ, hτ])
  have key : ∀ (y : Ainf F ⊗[F] E) (w : InfinitePlace F), Θ y w = 0 →
      ∀ k, e ((Algebra.TensorProduct.basis (Ainf F) b).repr y k) w = 0 := by
    intro y w hy k
    have h1 : Θ y w = (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 0) w : ℂ) * τ w (b 0) +
        (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 1) w : ℂ) * τ w (b 1) := by
      conv_lhs => rw [eq_coord b y, map_add (f := _), Pi.add_apply, hΘ, hΘ]
    rw [hy] at h1
    obtain ⟨h0, h1'⟩ := real_indep h b (τ w) _ _ h1.symm
    fin_cases k
    · exact h0
    · exact h1'
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hg' : ∀ j, g 0 * X 0 j = 0 := fun j => by simpa using congrFun hg j
  have hw : ∀ w, Θ (g 0) w = 0 := by
    intro w
    obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.1 (hX w)
    have hne : Θ (X 0 j) w ≠ 0 := fun h0 => hjk (key _ _ h0 k)
    have h3 := congrFun (congrArg Θ (hg' j)) w
    rw [map_mul, Pi.mul_apply, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_right hne
  refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply e.injective
  rw [map_zero]
  funext w
  exact key _ _ (hw w) k

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.HCFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mul_mem_span_zalg_mul {J : Set (Module.End ℂ (Sm E a))} {x : Module.End ℂ (Sm E a)} (hx : x ∈ Zalg E a)
    {s : Module.End ℂ (Sm E a)} (hs : s ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}) :
    x * s ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j} := by
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x', hx', j, hj, rfl⟩ := hy
    exact Submodule.subset_span ⟨x * x', Subalgebra.mul_mem _ hx hx', j, hj, (mul_assoc _ _ _).symm⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

end GlobalTheory.CompanionTheory.HCFin
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl PositivityTheory.Affgl.CT Topology Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.ConstTerm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd :
    Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.2))

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp
    (continuous_fst : Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.1)

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_of_isOpen_stab (φ : Sm E a) (hU : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g
  have hF : ContinuousAt (fun h : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) h).val)) 1 := by
    have h1 : ContinuousAt (chart φ.1 g) (toL ((GeneralLinearGroup.map (pInf E) (1 : GA E a)).val)) := by
      rw [map_one]
      exact (contDiffAt_chart φ.2 g isUnit_one).continuousAt
    have h0 : Continuous (fun h : GA E a =>
        ((GeneralLinearGroup.map (n := Fin a) (pInf E) h : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
      Units.continuous_val.comp continuous_map_pInf
    have h2 : Continuous (fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) := h0
    exact ContinuousAt.comp (f := fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) h1 h2.continuousAt
  have hev : ∀ᶠ h in 𝓝 (1 : GA E a), GeneralLinearGroup.map (pFin E) h ∈ {k | finRep E a k φ = φ} := by
    refine (continuous_map_pFin.continuousAt (x := (1 : GA E a))).eventually (hU.mem_nhds ?_)
    rw [map_one]
    change finRep E a 1 φ = φ
    simp
  have hG : ContinuousAt (fun h : GA E a => φ.1 (g * h)) 1 := by
    refine hF.congr ?_
    filter_upwards [hev] with h hh
    have e := congrArg (fun ψ : Sm E a => ψ.1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h))) hh
    change φ.1 (g * infGL E a _ * finGL E a _) = φ.1 _ at e
    rw [mul_assoc, infGL_mul_finGL] at e
    rw [e, chart_val]
  have h2 : ContinuousAt (fun x : GA E a => g⁻¹ * x) g := (continuous_const.mul continuous_id).continuousAt
  have h3 : ContinuousAt (fun h : GA E a => φ.1 (g * h)) (g⁻¹ * g) := by rwa [inv_mul_cancel]
  simpa [Function.comp_def] using h3.comp h2


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_unip : Continuous (unip : (BlockIx a r → Ad E) → GA E a) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) :=
    continuous_matrix fun i j => by
      simp only [nilM, Matrix.of_apply]
      split_ifs with h
      · exact continuous_apply _
      · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hn, continuous_const.sub hn⟩


omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_isCompact_sub_mem :
    ∃ C : Set (BlockIx a r → Ad E), IsCompact C ∧ ∀ x, ∃ n ∈ ratN E a r, x - n ∈ C := by
  obtain ⟨K, hK, h⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  choose y hy using h
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  exact ⟨fun p => algebraMap E (Ad E) (y (x p)), ⟨fun p => y (x p), rfl⟩, fun p _ => hy (x p)⟩


omit [_root_.NumberField.IsTotallyComplex E] in
theorem periodic_integrand (φ : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), φ (ratGL E a γ * g) = φ g)
    (g : GA E a) {n : BlockIx a r → Ad E} (hn : n ∈ ratN E a r) (x : BlockIx a r → Ad E) :
    φ (unip (n + x) * g) = φ (unip x * g) := by
  obtain ⟨y, rfl⟩ := hn
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) y =
      fun p => algebraMap E (Ad E) (y p) := rfl
  rw [e, unip_add, unip_algebraMap, mul_assoc, hl]

theorem integrableOn_fundamentalDomain :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
      (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) →
      IsOpen {k | finRep E a k φ = φ} →
      ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
        (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
        μ 𝓕 < ⊤ ∧ ∀ g : GA E a, IntegrableOn (fun x => φ.1 (unip x * g)) 𝓕 μ := by
  intro E _ _ _ a r φ hl hU _ _ μ 𝓕 hμ hF
  obtain ⟨C, hC, hcov⟩ := exists_isCompact_sub_mem (E := E) (a := a) (r := r)
  have hφ := continuous_of_isOpen_stab φ hU
  haveI : Countable (ratN E a r) := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
    exact Function.Surjective.countable
      (f := (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)).rangeRestrict)
      (AddMonoidHom.rangeRestrict_surjective _)
  have hfin : μ 𝓕 < ⊤ := by
    have h1 : 𝓕 ⊆ ⋃ n : ratN E a r, (n +ᵥ C) ∩ 𝓕 := fun x hx => by
      obtain ⟨n, hn, h⟩ := hcov x
      refine Set.mem_iUnion.2 ⟨⟨n, hn⟩, ⟨x - n, h, ?_⟩, hx⟩
      simp [AddSubgroup.vadd_def]
    calc μ 𝓕 ≤ ∑' n : ratN E a r, μ ((n +ᵥ C) ∩ 𝓕) := (measure_mono h1).trans (measure_iUnion_le _)
      _ = μ C := (hF.measure_eq_tsum C).symm
      _ < ⊤ := hC.measure_lt_top
  refine ⟨hfin, fun g => ?_⟩
  have hc : Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) :=
    hφ.comp (continuous_unip.mul continuous_const)
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine Measure.integrableOn_of_bounded hfin.ne hc.aestronglyMeasurable (M := B) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨n, hn, h⟩ := hcov x
  have := periodic_integrand φ.1 hl g hn (x - n)
  rw [add_sub_cancel] at this
  rw [this]
  exact hB _ h

end GlobalTheory.CompanionTheory.ConstTerm

end
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

theorem _root_.GlobalTheory.T.compact_support_split_centre_factor : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ → Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (normOneGL (K := E) (n := a)) ℂ, ∀ (K : Type) [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : GA E a → K), Continuous W → (∀ t g, W (splitCentre E a t * g) = W g) → ∫ g, f g • W g ∂μ = ∫ x, f₁ x • W (x : GA E a) ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral | exact GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre.exists_normOne_integral <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchInt

theorem continuousOn_logNorm_offSupp {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {q : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X} (ψ : GlobalTheory.Weight q σ L) (hψ : ψ.IsCInf)
    {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  intro y hy
  obtain ⟨i, hi⟩ := GlobalTheory.CxPts.exists_mem_ptsIn (p := q) (σ := σ) ψ.isLB.cover y
  have hu : GlobalTheory.Cartier.UnitAt (GlobalTheory.Cartier.under y) ((r i : X.functionField)) :=
    GlobalTheory.Cartier.IsRatSec.unitAt ψ.isLB hr hy hi
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hu
  have hgV : genericPoint X ∈ V := GlobalTheory.Cartier.gen_mem hyV
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hV
  have hyV' : y ∈ GlobalTheory.CxPts.ptsIn q σ V := GlobalTheory.CxPts.mem_ptsIn.2 hyV
  have hNo : IsOpen (GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr)) :=
    ((GlobalTheory.CxPts.isOpen_ptsIn V).inter (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
      (GlobalTheory.Cartier.isOpen_offSupp _)
  have hyN : y ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr) := ⟨⟨hyV', hi⟩, hy⟩
  have heq : ∀ z ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr),
      Real.log ‖GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2 =
        GlobalTheory.Cartier.logNorm ψ r z := by
    rintro z ⟨⟨hzV, hzi⟩, hz⟩
    rw [GlobalTheory.Cartier.logNorm_eq ψ hr hz hzi, ← ha hgV, GlobalTheory.Cartier.ratVal_fnOf hzV]
  have hne : GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) y ≠ 0 := by
    rw [← GlobalTheory.Cartier.ratVal_fnOf hyV' hgV, ha hgV]
    exact GlobalTheory.Cartier.ratVal_ne_zero hu
  have hev : ContinuousAt (GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V))) y :=
    (GlobalTheory.CxPts.continuousOn_ev _).continuousAt ((GlobalTheory.CxPts.isOpen_ptsIn V).mem_nhds hyV')
  have hφ : ContinuousAt (ψ.φ i) y := (hψ i y hi).continuousAt
  have hg : ContinuousAt (fun z => Real.log ‖GlobalTheory.CxPts.ev q σ V
      (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2) y :=
    (hev.norm.log (norm_ne_zero_iff.2 hne)).sub (hφ.div_const 2)
  exact (hg.congr (Filter.eventuallyEq_of_mem (hNo.mem_nhds hyN) heq)).continuousWithinAt

end GlobalTheory.CompanionTheory.MixZ.ArchInt
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchRep

theorem exists_local_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) (r : L.ι → X.functionFieldˣ) (y : GlobalTheory.CxPts q σ) :
    ∃ (W : X.Opens) (b : L.ι) (a d : Γ(X, W)) (h : genericPoint X ∈ W),
      y ∈ ptsIn q σ W ∧ W ≤ L.U b ∧ fnOf W h d ≠ 0 ∧
        (r b : X.functionField) * fnOf W h d = fnOf W h a := by
  have hb := mem_pick ψ.isLB y
  obtain ⟨W, hW, hyW, hWb⟩ := exists_isAffineOpen_mem_and_subset (mem_ptsIn.1 hb)
  have hg : genericPoint X ∈ W := gen_mem hyW
  haveI : Nonempty W := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  obtain ⟨a, d, hd, e⟩ := IsFractionRing.div_surjective (A := Γ(X, W)) (r (pick ψ.isLB y) : X.functionField)
  have hd0 : fnOf W hg d ≠ 0 := by
    have : algebraMap Γ(X, W) X.functionField d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    exact this
  refine ⟨W, pick ψ.isLB y, a, d, hg, mem_ptsIn.2 hyW, hWb, hd0, ?_⟩
  rw [← e]
  change algebraMap Γ(X, W) X.functionField a / algebraMap Γ(X, W) X.functionField d * fnOf W hg d = _
  have e' : algebraMap Γ(X, W) X.functionField d = fnOf W hg d := rfl
  have e'' : algebraMap Γ(X, W) X.functionField a = fnOf W hg a := rfl
  rw [e', e'', div_mul_cancel₀ _ hd0]

theorem logNorm_of_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {W : X.Opens} {b : L.ι} {a d : Γ(X, W)} {h : genericPoint X ∈ W} (hWb : W ≤ L.U b)
    (e : (r b : X.functionField) * fnOf W h d = fnOf W h a) {y : GlobalTheory.CxPts q σ} (hy : y ∈ ptsIn q σ W)
    (ho : y ∈ offSupp q σ (divOfRatSec ψ.isLB hr)) (hd : ev q σ W d y ≠ 0) :
    GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ W a y‖ - Real.log ‖ev q σ W d y‖ - ψ.φ b y / 2 := by
  have hb : y ∈ ptsIn q σ (L.U b) := mem_ptsIn.2 (hWb (mem_ptsIn.1 hy))
  have hu := IsRatSec.unitAt ψ.isLB hr ho hb
  have hv : ratVal (r b : X.functionField) y ≠ 0 := ratVal_ne_zero hu
  have ev' : ratVal (r b : X.functionField) y * ev q σ W d y = ev q σ W a y := by
    rw [← ratVal_fnOf hy h d, ← ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hy) h d), e, ratVal_fnOf hy]
  rw [logNorm_eq ψ hr ho hb, ← ev', norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 hv) (norm_ne_zero_iff.2 hd)]
  ring

theorem logNorm_finite_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ∃ (N : ℕ) (W : Fin N → X.Opens) (b : Fin N → L.ι) (a d : ∀ l, Γ(X, W l)),
      (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) ∧ (∀ l, W l ≤ L.U (b l)) ∧
      (∀ l, ∃ h : genericPoint X ∈ W l, fnOf (W l) h (d l) ≠ 0) ∧
      ∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ offSupp q σ (divOfRatSec ψ.isLB hr) → ev q σ (W l) (d l) y ≠ 0 →
        GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2 := by
  choose W₀ b₀ a₀ d₀ h₀ hy₀ hWb₀ hd₀ e₀ using exists_local_quot ψ r
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => ptsIn q σ (W₀ y))
    (fun y => isOpen_ptsIn _) fun y _ => Set.mem_iUnion.2 ⟨y, hy₀ y⟩
  let c : Fin t.card → GlobalTheory.CxPts q σ := fun l => (t.equivFin.symm l).1
  refine ⟨t.card, fun l => W₀ (c l), fun l => b₀ (c l), fun l => a₀ (c l), fun l => d₀ (c l), fun y => ?_,
    fun l => hWb₀ _, fun l => ⟨h₀ _, hd₀ _⟩, fun l y hy ho hd => logNorm_of_quot ψ hr (hWb₀ _) (e₀ _) hy ho hd⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨z, hz⟩, ?_⟩
  simpa [c] using hyz

end GlobalTheory.CompanionTheory.MixZ.ArchRep
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_nonnegative_schwartz_bump : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : Set (κ → AF F)), IsOpen N → ∀ z₀ ∈ N, ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N → Φ z = 0) ∧ 0 < (Φ z₀).re := by
  first | exact @GlobalTheory.CompanionTheory.AdelicBump.exists_bump | exact GlobalTheory.CompanionTheory.AdelicBump.exists_bump | (intros; apply GlobalTheory.CompanionTheory.AdelicBump.exists_bump <;> assumption)
end
