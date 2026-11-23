module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapPairsContinuousDensityNearDiagonal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle127
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle129
public import Formalism.HermitianLattices.Bundle001
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Formalism.HermitianLattices.StatementLat
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.Continuity
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle128
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Divisibility.RowLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.QuotientMetricDivisors.Statement
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → IsStdX s σ J β ν → ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 ∧ IsInvTup (AF F) σ J ν ∧ OnOrbit (AF F) σ J x ν ∧ IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 := by
  first | exact @GlobalTheory.GaugeEx.StdProp.stdX_props | exact GlobalTheory.GaugeEx.StdProp.stdX_props | (intros; apply GlobalTheory.GaugeEx.StdProp.stdX_props <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.gramMap_pairs_continuous_density_near_diagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (y : Fin 1 → Fin M → E) (c : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → c ≠ 0 → hE σ J' (y 0) (y 0) = algebraMap F E c → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 (M + 1)) ν (algebraMap F R a) m → FibAt R σ J' (tupMeas lam 1 M) ν (algebraMap F R c) m' → TwoStep R σ J x B m m' N → ∀ φ : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) → ∃ (U : Set (R × (R ⊗[F] E) × R)) (D : R × (R ⊗[F] E) × R → ℝ), IsOpen U ∧ (algebraMap F R a, 0, algebraMap F R c) ∈ U ∧ ContinuousOn D U ∧ (∀ t ∈ U, 0 ≤ D t) ∧ (∀ S ⊆ U, MeasurableSet S → ∫⁻ X in gram3 R σ J ⁻¹' S, ENNReal.ofReal (φ X) ∂(tupMeas lam 2 (M + 1)) = ∫⁻ t in S, ENNReal.ofReal (D t) ∂(ν.prod (lam.prod ν))) ∧ D (algebraMap F R a, 0, algebraMap F R c) = (modu (R ⊗[F] E) (inclR R ((consCol x B).det / algebraMap F E a)) : ℝ) * ∫ X, φ X ∂N := by
  first | exact @GlobalTheory.GaugeEx.GramDensity.gram_density | exact GlobalTheory.GaugeEx.GramDensity.gram_density | (intros; apply GlobalTheory.GaugeEx.GramDensity.gram_density <;> assumption)
end

section

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | exact GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique_allPrimes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' → ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 → ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  first | exact @GlobalTheory.TwoPlaces.exists_deep_one_sub | exact GlobalTheory.TwoPlaces.exists_deep_one_sub | (intros; apply GlobalTheory.TwoPlaces.exists_deep_one_sub <;> assumption)
end

section

noncomputable section

open Module NumberField IsDedekindDomain Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.BasicNotions
open scoped Matrix InnerProductSpace ComplexOrder

namespace GlobalTheory.Mem.RowSides

section Semi

variable {K : Type} [Field K] {σ : K →+* ℂ} {U V W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]

theorem semi_injective_of_basis {ι : Type} [Fintype ι] (b : Basis ι K U) (g : U →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun i => g (b i)) : Function.Injective g := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx

  rw [← b.sum_repr x, map_sum] at hx
  simp only [map_smulₛₗ] at hx
  have := Fintype.linearIndependent_iff.1 h (fun i => σ (b.repr x i)) hx
  refine b.repr.injective (Finsupp.ext fun i => σ.injective ?_)
  simpa using this i

end Semi

section Polar

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem majAt_expand {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + a • y) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 + Formalism.HermitianLatticesTheory.normAt b X v (a • y) ^ 2 +
      2 * (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := by
  have hs : Formalism.HermitianLatticesTheory.fcoord b X v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v y := by
    have : Formalism.HermitianLatticesTheory.vecAt b v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v y := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    rw [Formalism.HermitianLatticesTheory.fcoord, this, Matrix.mulVec_smul]; rfl
  simp only [normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, hs, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul', Complex.star_def, Complex.mul_re, Complex.add_re,
    Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_eq_of_normAt [_root_.NumberField.IsTotallyComplex K] {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (v : InfinitePlace K) (e : V →ₗ[K] W)
    (h : ∀ x, Formalism.HermitianLatticesTheory.normAt b' X' v (e x) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have key : ∀ a : K, (v.embedding a * Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y)).re =
      (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := fun a => by
    have h1 := majAt_expand b X v a x y
    have h2 := majAt_expand b' X' v a (e x) (e y)
    rw [← map_smul, ← map_add (f := _), h, h, h] at h2
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hn
    push Not at hn
    have hc := IsTotallyComplex.isComplex v
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (hn x)
  have h1 := key 1
  have h2 := key a
  simp only [map_one, one_mul] at h1
  simp only [Complex.mul_re, h1] at h2
  refine Complex.ext h1 (mul_left_cancel₀ ha ?_)
  linarith

end Polar

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

variable {B ℓ} {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ)




end Block

end GlobalTheory.Mem.RowSides

end
end

section

open NumberField IsDedekindDomain IsLocalRing TensorProduct

namespace GlobalTheory.LidxBaseChange

theorem length_eq_of_residue (R O M : Type*) [CommRing R] [CommRing O] [IsLocalRing O] [Algebra R O]
    [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower R O M]
    (h1 : Module.length R (ResidueField O) = 1) : Module.length R M = Module.length O M := by
  have step : ∀ {p q : Submodule O M}, p ⋖ q → Module.length R q = Module.length R p + 1 := by
    intro p q h
    let f : p →ₗ[O] q := Submodule.inclusion h.le
    have key : IsSimpleModule O (q ⧸ f.range) := by
      rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple h.le]
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
    rw [eq_maximalIdeal hm] at e
    let g : q →ₗ[O] ResidueField O := e.comp f.range.mkQ
    have : Function.Injective f := Submodule.inclusion_injective _
    have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
    have : Function.Exact f g := LinearMap.exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
    rw [Module.length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R)
      (by simpa) (by simpa) (by simpa), h1]
  by_cases h : IsFiniteLength O M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← Module.length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, Module.length R (s k) = k by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
      exact Module.length_top.symm
    intro k
    induction k using Fin.induction with
    | zero => rw [← RelSeries.head, hs_bot]; simp
    | succ i hi => simpa [hi] using step (s.step i)
  · have : ¬ IsFiniteLength R M := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      exact h.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
    rw [← Module.length_ne_top_iff, not_ne_iff] at h this
    rw [h, this]

theorem length_residue_atPrime {R : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] :
    Module.length R (ResidueField (Localization.AtPrime P)) = 1 := by
  rw [Module.length_eq_of_surjective (S := R) (R := ResidueField (Localization.AtPrime P))
    (Ideal.algebraMap_residueField_surjective P)]
  simp

theorem mem_localization_iff {R W : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P X ↔ x ∈ Submodule.span (Localization.AtPrime P) (X : Set W) := by
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl)
    have : x = (↑u⁻¹ : Localization.AtPrime P) • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime P) s x]
      change x = _ • (algebraMap R (Localization.AtPrime P) ((⟨s, hs⟩ : P.primeCompl) : R)) • x
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, P.primeCompl.one_mem, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      obtain ⟨s, hs, hy⟩ := hy
      obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj P.primeCompl c
      refine ⟨s * t, P.primeCompl.mul_mem hs t.2, ?_⟩
      have : (s * (t : R)) • c • y = a • s • y := by
        rw [mul_smul, ← algebraMap_smul (Localization.AtPrime P) (t : R), smul_smul _ c, mul_comm _ c]
        dsimp only at h
        rw [h, algebraMap_smul, smul_comm]
      rw [this]
      exact X.smul_mem a hy

theorem length_localized_eq₂ {R W : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X Y : Submodule R W) :
    Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ P X) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P Y).comap (Formalism.HermitianLatticesTheory.localization₂ P X).subtype) =
      Module.length (Localization.AtPrime P) (↥(Submodule.span (Localization.AtPrime P) (X : Set W)) ⧸
        (Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype) := by
  rw [← length_eq_of_residue R _ _ (length_residue_atPrime P)]
  have hX : Formalism.HermitianLatticesTheory.localization₂ P X = (Submodule.span (Localization.AtPrime P) (X : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P X x
  have hY : Formalism.HermitianLatticesTheory.localization₂ P Y = (Submodule.span (Localization.AtPrime P) (Y : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P Y x
  rw [hX, hY]
  exact (Submodule.Quotient.restrictScalarsEquiv R ((Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype)).length_eq

theorem span_image_inf {A O V W : Type*} [CommRing A] [CommRing O] [Algebra A O] [Module.Flat A O]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] [Module O W] [IsScalarTower A O W]
    (φ : V →ₗ[A] W) (h : Function.Injective (φ.liftBaseChange O)) (M N : Submodule A V) :
    Submodule.span O (φ '' (M : Set V)) ⊓ Submodule.span O (φ '' (N : Set V)) =
      Submodule.span O (φ '' ((M ⊓ N : Submodule A V) : Set V)) := by
  have key : ∀ X : Submodule A V,
      Submodule.span O (φ '' (X : Set V)) = (X.baseChange O).map (φ.liftBaseChange O) := fun X => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => by simp
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ h]

theorem exists_lidx_eq_mul (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    {d d' : ℕ} (ψ : (Fin d → K) →ₗ[K] (Fin d' → K')) (hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)))
    (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')) [P'.asIdeal.LiesOver P.asIdeal] :
    ∃ e : ℕ, 0 < e ∧ ∀ A B : Submodule (𝓞 K) (Fin d → K),
      Formalism.HermitianLatticesTheory.lidx P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (A : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (B : Set (Fin d → K)))) = Formalism.HermitianLatticesTheory.lidx P.asIdeal A B * e := by
  have hPm := P.isMaximal
  have hPm' := P'.isMaximal
  let O := Localization.AtPrime P.asIdeal
  let O' := Localization.AtPrime P'.asIdeal
  letI : Algebra O K := IsLocalization.localizationAlgebraOfSubmonoidLe O K P.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K)) P.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K) O K := IsLocalization.localization_isScalarTower_of_submonoid_le O K _ _ _
  letI : Algebra O' K' := IsLocalization.localizationAlgebraOfSubmonoidLe O' K' P'.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K')) P'.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K') O' K' := IsLocalization.localization_isScalarTower_of_submonoid_le O' K' _ _ _
  have : IsFractionRing O K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl O K
  have : IsFractionRing O' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P'.asIdeal.primeCompl O' K'
  have : IsScalarTower (𝓞 K) O' K' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') O', ← IsScalarTower.algebraMap_apply (𝓞 K') O' K',
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra O O' := Localization.AtPrime.algebraOfLiesOver P.asIdeal P'.asIdeal
  have : Localization.AtPrime.IsLiesOverAlgebra P.asIdeal P'.asIdeal := inferInstance
  have : IsScalarTower (𝓞 K) O O' := inferInstance
  have : IsLocalHom (algebraMap O O') := inferInstance
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) P.ne_bot _
  have : IsDiscreteValuationRing O' :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K') P'.ne_bot _
  have : FaithfulSMul O O' := inferInstance
  have : Module.Flat O O' := inferInstance
  have : IsLocalHom (algebraMap O O) := inferInstance
  refine ⟨(maximalIdeal O').ramificationIdx O, ramificationIdx_maximalIdeal_pos O O', ?_⟩
  have hlen : ∀ M N : Submodule (𝓞 K) (Fin d → K), N ≤ M →
      Formalism.HermitianLatticesTheory.locLen P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (M : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (N : Set (Fin d → K)))) =
        Formalism.HermitianLatticesTheory.locLen P.asIdeal M N * (maximalIdeal O').ramificationIdx O := by
    intro M N hNM
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [length_localized_eq₂, length_localized_eq₂, Submodule.span_span_of_tower, Submodule.span_span_of_tower]
    have h1 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O' K') ψ _ hψ N M hNM
    have h2 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O K)
      (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K)) (Pi.basisFun K (Fin d))
      (Pi.basisFun K (Fin d)).linearIndependent N M hNM
    rw [length_fibre_eq_ramificationIdx O O'] at h1
    have h3 : Module.length O (O ⧸ (maximalIdeal O).map (algebraMap O O)) = 1 := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
      have h4 := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O 1
      rw [pow_one] at h4
      exact_mod_cast h4
    rw [h3, mul_one, LinearMap.id_coe, Set.image_id, Set.image_id] at h2
    rw [h1, h2, ENat.toNat_mul, ENat.toNat_coe]
  intro A B
  have hinj := Formalism.BasicNotions.FBC.liftBaseChange_injective_top (A := 𝓞 K) (IsFractionRing.injective (𝓞 K') K') ψ _ hψ
  have hinf := span_image_inf _ hinj A B
  unfold Formalism.HermitianLatticesTheory.lidx
  erw [hinf]
  erw [hlen A _ inf_le_left, hlen B _ inf_le_right]
  push_cast
  ring

theorem lidx_ne_zero_iff : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  intro K K' _ _ _ _ φ d d' G hG P P' hP A B _ _
  letI : Algebra K K' := φ.toAlgebra
  have : P'.asIdeal.LiesOver P.asIdeal := ⟨Ideal.ext fun x => hP x (algebraMap (𝓞 K) (𝓞 K') x) rfl⟩
  let ψ : (Fin d → K) →ₗ[K] (Fin d' → K') :=
    (G.mulVecLin.restrictScalars K) ∘ₗ (Algebra.linearMap K K').compLeft (Fin d)
  have hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)) := by
    have h := (Pi.basisFun K' (Fin d)).linearIndependent.map' G.mulVecLin (LinearMap.ker_eq_bot.2 hG.1)
    have e : ψ ∘ Pi.basisFun K (Fin d) = G.mulVecLin ∘ Pi.basisFun K' (Fin d) := by
      funext i
      simp only [ψ, Function.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      congr 1
      funext k
      by_cases hk : k = i <;> simp [hk, Pi.single_apply]
    rw [e]
    exact h
  obtain ⟨e, he, h⟩ := exists_lidx_eq_mul K K' ψ hψ P P'
  have h' := h A B
  have hf : (fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) = ψ := rfl
  rw [hf, h']
  simp [he.ne']

end GlobalTheory.LidxBaseChange
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Mem.Col2.T_notMem_QE : ∀ {X : _root_.Formalism.L2.Col.Fields} {Pr : _root_.Formalism.L2.Col.Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : _root_.Formalism.L2.DIV.Tup X.F X.E X.K S) (u : Pr.Word), Pr.Ok → _root_.Formalism.L2.Col.IsSel X sel → Pr.T u ∈ S →
      ∀ w ∈ _root_.Formalism.L2.Col.QE sel (mu : _root_.Formalism.L2.DIV.Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal := by
  classical
  intro X Pr sel S mu u hOk hsel hT w hw hmem
  unfold _root_.Formalism.L2.Col.QE at hw
  split_ifs at hw with hfin
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [Set.Finite.mem_toFinset] at hv
    have hmu := mu.2
    unfold _root_.Formalism.L2.DIV.tupGrp at hmu
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hmu
    have hA : _root_.Formalism.L2.DIV.GoodPl X.E S v := by
      by_contra hA
      exact hv (hmu.2 v hA)
    have hchar : _root_.Formalism.EigenvalueLevelCeiling.plc v ∉ S := by
      unfold _root_.Formalism.L2.DIV.GoodPl at hA
      exact hA.2.2
    have hv' : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
      rw [← hsel v, Ideal.mem_comap]
      simpa using hmem
    have hp := hOk.T_prime u
    have hzero : ((Pr.T u : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hv'
    have : Nontrivial (𝓞 X.F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have hdvd : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ Pr.T u := (ringChar.spec _ _).mp hzero
    have heq : ringChar (𝓞 X.F ⧸ v.asIdeal) = Pr.T u :=
      ((Nat.dvd_prime hp).mp hdvd).resolve_left CharP.ringChar_ne_one
    apply hchar
    unfold _root_.Formalism.EigenvalueLevelCeiling.plc
    rw [heq]
    exact hT
  · simp at hw

end GlobalTheory.Mem.Col2
end
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Mem.LiftProjOnto

theorem lPrj_surjective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (k : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A P ψ k t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W) (op : W →ₗ[ℂ] W), A.fam.Ok 1 → FormsTie D.what₂.embLL j (lH D A P ψ k t) (lE D A P ψ k t) op → Function.Surjective (lPrj D A P ψ Zs k t).mulVec := by
  intro D G _ _ Pl0 T A P ψ Zs k t W _ _ j op hOk _
  have hB : BlockHyp (A.fam.L k t) (A.fam.lvlA P ψ) A.v0 1 := ⟨hOk.conj, hOk.irr, hOk.lifts k t⟩
  exact BlockDat.lf_lPr_surj (Z := Zs.Zl k t) hB

end GlobalTheory.Mem.LiftProjOnto
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.satakeParameters_inertPlace_independent_of_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ v w, NG.OverPl w v → ∀ (Dv Dv' : InertDatum L n v w) α, NG.SatAt π Dv α → NG.SatAt π' Dv' α := by
  first | exact @GlobalTheory.SatInd.satAt_indep | exact GlobalTheory.SatInd.satAt_indep | (intros; apply GlobalTheory.SatInd.satAt_indep <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_complexLinear_extension_of_traceIsometry' : ∀ (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (ι : Type) [Fintype ι] (φ : E →+* ℂ) (emb : ι → E →+* ℂ), (∀ y, φ (cj y) = starRingEnd ℂ (φ y)) → (∀ τ y, emb τ (cj y) = starRingEnd ℂ (emb τ y)) → (∀ τ (x : K), emb τ (algebraMap K E x) = φ (algebraMap K E x)) → (∀ y, ∑ τ, emb τ y = φ (algebraMap K E (Algebra.trace K E y))) → ∀ γ : IsoKG K E cj ι, ∃ gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ), ∀ x : Fin 4 → E, gC (fun w => emb w.2 (x w.1)) = fun w => φ (algebraMap K E (γ.g x w)) := by
  first | exact @GlobalTheory.exists_complexLinear_extension_of_traceIsometry | exact GlobalTheory.exists_complexLinear_extension_of_traceIsometry | (intros; apply GlobalTheory.exists_complexLinear_extension_of_traceIsometry <;> assumption)
end
