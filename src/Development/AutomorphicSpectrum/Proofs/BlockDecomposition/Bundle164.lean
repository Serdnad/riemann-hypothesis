module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle148
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFirstCohomologyComparison
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import GroundTheory.LocalFields.MaximalUnramified
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle152
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle133
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle151
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle064
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle058
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Formalism.ConjugateSelfDual.Bundle001
import GroundTheory.ProfiniteCohomology.Bundle001
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_semilattice_system : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s → QuasiCompact s →
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact | exact GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unique_constant_of_compatible_family : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (_ : BC F F'),
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt | exact GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt | (intros; apply GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.product_first_cohomology_comparison : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (P : Type) [SemilatticeInf P] (S : Sys A.left P),
    ∃ (Q : Type) (_ : SemilatticeInf Q) (S' : Sys (A ⊗ A).left Q)
      (m : CoefMap (RingHom.id R) (box (OSys A.hom S)) (OSys (A ⊗ A).hom S')),
      Function.Surjective m.pull1 ∧
      (∀ x c, IsPullO (wOver (fst A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxL _).pull1 ((resSys _ S).pull1 x))) ∧
      (∀ x c, IsPullO (wOver (snd A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxR _).pull1 ((resSys _ S).pull1 x))) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_boxSys | exact GlobalTheory.CompanionTheory.Axis.exists_boxSys | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_boxSys <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.Duality

theorem pi_perpCond_eq_annihilator_sumPair : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ v, Function.Injective (j v)) → ∀ L : LocCond ρ (locFam S Av), Submodule.pi Set.univ (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) = ⨅ x ∈ Submodule.pi Set.univ L, LinearMap.ker ((sumPair S Av μ j ρ hρ).flip x) := by
  classical
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hj L
  ext y
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, forall_const, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.flip_apply, ReciprocityTheory.Gal.perpCond, PositivityTheory.S2pt.sumPair, Finset.sum_apply,
    LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearMap.proj_apply]
  constructor
  · intro h x hx
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [h v (x v) (hx v), map_zero]
  · intro h v x0 hx0
    apply hj v
    rw [map_zero]
    have hs := h (Pi.single v x0) (fun w => by
      by_cases hw : w = v
      · subst hw
        simpa using hx0
      · simp [Pi.single_eq_of_ne hw])
    rw [Finset.sum_eq_single v] at hs
    · simpa using hs
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp

end GlobalTheory.CompanionTheory.Duality
end

section

namespace GlobalTheory.CompanionTheory.ExpOneParam

theorem continuous_expG_and_toM_inv :
    ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Z →
      Continuous (fun t : ℝ => Formalism.REAL.expG ε Z t) ∧
        ∀ t : ℝ, Formalism.REAL.toM (Formalism.REAL.expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  obtain ⟨h0, hadd, hcont, -⟩ := Formalism.REAL.group_exponential_facts n ε Z hZ
  refine ⟨hcont, fun t => ?_⟩
  have hinv : (Formalism.REAL.expG ε Z t)⁻¹ = Formalism.REAL.expG ε Z (-t) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← hadd, neg_add_cancel, h0]
  rw [hinv, Formalism.REAL.toM_expG ε Z (-t) hZ, Complex.ofReal_neg, neg_smul]

end GlobalTheory.CompanionTheory.ExpOneParam
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

theorem _root_.GlobalTheory.T.unramified_character_continuous : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (χ : Gal(Ω/K) → ZMod n), (∀ g h, χ (g * h) = χ g + χ h) → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → Continuous χ := by
  first | exact @GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one | exact GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one | (intros; apply GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.finite_dual_injective_equiv : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y], (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) → (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) → Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  first | exact @GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | exact GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | (intros; apply GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.isOpen_additive_character_kernel : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → IsOpen {x : k | ψ x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | exact GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | (intros; apply GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.relIndex_annihilators_duality : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) → IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) → (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by
  first | exact @GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq | exact GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq | (intros; apply GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem exists_haar_fundamentalDomain : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁), Continuous ι → Continuous π → (∀ u, π (ι u) = u) → ∀ (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ u ∈ Γ₁, ι u ∈ Γ) → (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ (ν : Measure π.ker) (𝓕N : Set π.ker) (μP : Measure P) (𝓕P : Set P), ν.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf π.ker) 𝓕N ν ∧ ν 𝓕N ≠ 0 ∧ ν 𝓕N < ⊤ ∧ μP.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕P μP ∧ μP 𝓕P < ⊤ ∧ ∀ f : P → ℝ≥0∞, Measurable f → ∫⁻ p in 𝓕P, f p ∂μP = ∫⁻ u in 𝓕₁, ∫⁻ m in 𝓕N, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hU hΓ₁ hΓ μ₁ _ 𝓕₁ h𝓕₁ hfin hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by ext; simp [MonoidHom.mem_ker]
    rw [this]; exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨D, hDm, hDu, hD⟩ := GlobalTheory.T.parabolic_fundamental_domain_split P G₁ ι π hι hπ hπι Γ hU hK
  let ν : Measure π.ker := Measure.haar
  obtain ⟨hνF, hν0, hνfin⟩ := hD ν
  obtain ⟨δ, hδm, hδΓ, hδ⟩ := GlobalTheory.T.parabolic_haar_decomposition P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν D hDm hνF hν0 hνfin
  have hδ1 := GlobalTheory.T.modular_character_trivial_finite_covolume G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin δ hδm hδΓ
  have hmap : ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν := by
    intro u; rw [hδ u, hδ1 u, one_smul]
  have hH := GlobalTheory.T.parabolic_quotient_measure P G₁ ι π hι hπ hπι ν μ₁ hmap
  obtain ⟨hnull, hint⟩ := GlobalTheory.T.parabolic_levi_integral_formula P G₁ ι π hι hπ hπι ν μ₁ D 𝓕₁ hDm h𝓕₁.nullMeasurableSet
  have hcov := GlobalTheory.T.parabolic_fundamental_domain_volume P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν μ₁ D 𝓕₁ hDu h𝓕₁
  have hdis := GlobalTheory.T.parabolic_integral_unfolding P G₁ ι π hι hπ hπι Γ Γ₁ hΓ ν μ₁ D 𝓕₁ hDu h𝓕₁
  refine ⟨ν, D, _, _, inferInstance, hνF, hν0, hνfin, hH,
    IsFundamentalDomain.mk'' hnull hcov hdis (fun γ => (measurePreserving_smul γ _).quasiMeasurePreserving), ?_, hint⟩
  have h1 := hint (fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, setLIntegral_one] at h1
  rw [h1]
  exact ENNReal.mul_lt_top hνfin hfin

end GlobalTheory.CompanionTheory.SplitExtLat
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.FieldModel

theorem exists_subfield_model : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K) (_ : IsAlgClosure K (AlgebraicClosure ℚ)) (e : F ≃+* K) (E : Ω ≃+* (AlgebraicClosure ℚ)), ∀ x : F, E (algebraMap F Ω x) = algebraMap K (AlgebraicClosure ℚ) (e x) := by
  intro F Ω _ _ _ _ _
  let σ : F →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : F ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  haveI fd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  haveI nf : NumberField σ.fieldRange := { to_charZero := inferInstance, to_finiteDimensional := fd }
  haveI alg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      (AlgebraicClosure.isAlgebraic ℚ)
    convert h
  haveI ac : IsAlgClosure σ.fieldRange (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) σ.fieldRange⟩
  refine ⟨σ.fieldRange, nf, ac, e.toRingEquiv, IsAlgClosure.equivOfEquiv Ω (AlgebraicClosure ℚ) e.toRingEquiv, fun x => ?_⟩
  exact IsAlgClosure.equivOfEquiv_algebraMap Ω (AlgebraicClosure ℚ) e.toRingEquiv x

end GlobalTheory.CompanionTheory.FieldModel
end
