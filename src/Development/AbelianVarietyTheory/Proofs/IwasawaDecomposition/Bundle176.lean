module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle059
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle071
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRepOfActionOnTotalFamily
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle008
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.Mem.CharAlg

theorem bijective_cmType {L : Type} [Field L] [_root_.NumberField.IsTotallyComplex L] {I : Type} (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
  have hne : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    have h1 : i = j := h.1 (by
      show InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)
      rw [hij, InfinitePlace.mk_conjugate_eq])
    subst h1
    exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.2 hij.symm)
  constructor
  · rintro (i | i) (j | j) hij
    · have hij' : φ i = φ j := hij
      exact congrArg Sum.inl (h.1 (congrArg InfinitePlace.mk hij'))
    · exact absurd hij (hne i j)
    · exact absurd hij.symm (hne j i)
    · have hij' : ComplexEmbedding.conjugate (φ i) = ComplexEmbedding.conjugate (φ j) := hij
      refine congrArg Sum.inr (h.1 ?_)
      show InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)
      rw [← InfinitePlace.mk_conjugate_eq (φ i), hij', InfinitePlace.mk_conjugate_eq]
  · intro ψ
    obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk ψ)
    rcases InfinitePlace.mk_eq_iff.1 hi with hi | hi
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨Sum.inr i, hi⟩

theorem prod_split {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) (f : (L →+* ℂ) → ℂ) :
    ∏ ψ, f ψ = ∏ i, (f (φ i) * f (ComplexEmbedding.conjugate (φ i))) := by
  rw [← (bijective_cmType φ h).prod_comp f, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  rfl

theorem isAlg_of {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (a b : I → ℤ)
    (hχ : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i k ^ a i * (starRingEnd ℂ (φ i k)) ^ b i)) :
    ∃ n, χ.IsAlg n := by
  let e := Equiv.ofBijective _ (bijective_cmType φ h)
  refine ⟨fun ψ => Sum.elim a b (e.symm ψ), fun k => ?_⟩
  rw [hχ k, prod_split φ h]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : e.symm (φ i) = Sum.inl i := e.symm_apply_eq.2 rfl
  have h2 : e.symm (ComplexEmbedding.conjugate (φ i)) = Sum.inr i := e.symm_apply_eq.2 rfl
  simp only [h1, h2, Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq]

theorem even_pow {z : ℂ} (hz : z ≠ 0) (c : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * c) = z ^ c * (starRingEnd ℂ z) ^ (-c) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
    rw [zpow_ofNat, div_pow, ← Complex.mul_conj', sq, mul_div_mul_left _ _ hz]
  rw [zpow_mul, h, div_zpow, zpow_neg, div_eq_mul_inv]

theorem odd_pow {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    ((z / ((‖z‖ : ℝ) : ℂ)) ^ (1 : ℤ))⁻¹ *
      (((‖z‖ : ℝ) : ℂ) ^ (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) *
        ((‖z‖ : ℝ) : ℂ) ^ (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) =
      z ^ (-1 - (m : ℤ)) * (starRingEnd ℂ z) ^ (-(m : ℤ)) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
  have he : (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) + (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) =
      -((2 * m + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [← Complex.cpow_add _ _ hn, he, Complex.cpow_neg, Complex.cpow_natCast, pow_succ, pow_mul,
    ← Complex.mul_conj', zpow_sub₀ hz, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_one, zpow_one, mul_pow]
  field_simp

theorem isAlg_even_odd : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), (∀ (χ : HChar H.E) (c : R.Psi → ℤ), χ.HasInf (embPsi H) (fun τ => 2 * c τ) → ∃ n, χ.IsAlg n) ∧ ∀ (η : HChar H.E), η.HasInf (embPsi H) (fun _ => 1) → ∀ r : ℕ, Odd r → ∃ n, (η⁻¹ * GlobalTheory.HeckeGal.Model.absPow H.E (-(r : ℝ) / 2)).IsAlg n := by
  intro R H
  obtain ⟨c0, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have := hcm.cplx
  have hz : ∀ (i : R.Psi) (k : (H.E)ˣ), embPsi H i (k : H.E) ≠ 0 := fun i k => by simp
  refine ⟨fun χ c hχ => isAlg_of (embPsi H) hcm.bij χ c (fun i => -c i) fun k => ?_, ?_⟩
  · rw [hχ k]
    exact Finset.prod_congr rfl fun i _ => even_pow (hz i k) (c i)
  · rintro η hη r ⟨m, rfl⟩
    refine isAlg_of (embPsi H) hcm.bij _ (fun _ => -1 - (m : ℤ)) (fun _ => -(m : ℤ)) fun k => ?_
    rw [HChar.inf_mul, HChar.inf_inv, Units.val_mul, Units.val_inv_eq_inv_val, hη k,
      (GlobalTheory.HeckeGal.Model.absPow_isAbsPow H.E _).2.2 k, prod_split (embPsi H) hcm.bij, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    exact odd_pow (hz i k) m

end GlobalTheory.Mem.CharAlg
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameRecip

theorem exists_frob_fix_of_eisenstein : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : _root_.Formalism.ConjugateSelfDual.G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  intro hG E Ω _ _ _ _ _ _ art hart v A hA ϖ hϖ hϖ2 π hπ
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  have : FiniteDimensional E (IntermediateField.adjoin E {π}) := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField (IntermediateField.adjoin E {π}) := NumberField.of_module_finite E _
  have : IsAlgClosure (IntermediateField.adjoin E {π}) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  set K := IntermediateField.adjoin E {π} with hKdef
  obtain ⟨artK, hartK⟩ := hG K Ω
  obtain ⟨W, hWv, hWuniq, hAW, hnW, hunif⟩ := GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place E Ω v A hA ϖ hϖ hϖ2 π hπ
  obtain ⟨-, hnorm⟩ := GlobalTheory.TameEis.minpoly_and_norm_of_pow_eq_uniformizer E Ω v ϖ hϖ hϖ2 π hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have hv1 : (1 : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rcases Nat.eq_zero_or_pos (normV v - 1) with h0 | h0
    · rw [h0, pow_zero] at hπ
      have : (ϖ : E) = ((1 : 𝓞 E) : E) := by
        apply (algebraMap E Ω).injective; rw [← hπ]; simp
      exact hv1 (by rw [← (RingOfIntegers.coe_injective this)]; exact hϖ)
    · rw [zero_pow h0.ne'] at hπ
      have : (ϖ : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hπ.symm
      exact hϖ2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.mp this]; exact Ideal.zero_mem _)
  have hgen0 : IntermediateField.AdjoinSimple.gen E π ≠ 0 := by
    intro h; apply hπ0
    have := congrArg (algebraMap K Ω) h
    simpa using this
  set yK : Kˣ := Units.mk0 _ hgen0 with hyK
  set cπ : (W.adicCompletion K)ˣ := Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom yK with hcπ
  have hcu : IsUnifAt W cπ := hunif cπ rfl
  obtain ⟨σ, hσF, hσA⟩ := (hartK.frob W A hAW (artK (localIdele K W cπ))).mp ⟨cπ, hcu, rfl⟩
  have hN := GlobalTheory.T.artin_restrict_eq_artin_norm_single_place E Ω K art artK hart hartK v W hWv hWuniq yK σ⁻¹ hσA
  refine ⟨σ.restrictScalars E, ?_, ?_, ?_⟩
  · rw [← hnW]; exact hσF
  · have := σ.commutes (IntermediateField.AdjoinSimple.gen E π)
    simpa using this
  · intro c hc
    have hinv : (σ.restrictScalars E)⁻¹ = (σ⁻¹).restrictScalars E := rfl
    rw [hinv, hN]
    congr 2
    ext
    rw [hc]
    simp only [Units.coe_map, MonoidHom.coe_coe, hyK, Units.val_mk0]
    rw [hnorm]
    simp

end GlobalTheory.TameRecip
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TraitProper


open GlobalTheory.ArcProper in
theorem isProper_of_lift_genericPoint : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f], (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Sp R), Set.range x ⊆ {genericPoint X} → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro k _ _ Y _ s _ _ _ H
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → Y.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : Y, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    exists_isOpenImmersion_isProper ((A i).ι ≫ s))
  choose P t j ht hj hjt using hP
  let U : Y.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint Y ∈ U := by
    have : ∀ i, genericPoint Y ∈ A i := fun i ↦
      ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨Q, q, ψ, _, hψ, hp⟩ := exists_isProper_factor P t ht (U.ι ≫ s)
    (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc])
    Finset.univ
  choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)
  obtain ⟨i₀, -⟩ := hcov (genericPoint Y)
  have : IsImmersion (ψ ≫ p i₀) := by rw [hψp]; infer_instance
  have : IsImmersion ψ := IsImmersion.of_comp ψ (p i₀)
  have : QuasiCompact (ψ ≫ q) := by rw [hψ]; infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ q
  have : IsIntegral ψ.image := isIntegral_image ψ
  let z : ψ.image ⟶ Sp k := ψ.imageι ≫ q
  have hz : ψ.toImage ≫ z = U.ι ≫ s := by rw [ψ.toImage_imageι_assoc, hψ]
  have : IsLocallyNoetherian ψ.image := LocallyOfFiniteType.isLocallyNoetherian z
  let V : T → ψ.image.Opens := fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange
  let η : U.toScheme := ⟨_, hU⟩
  have hη : ∀ u : U.toScheme, η ⤳ u := fun u ↦
    (U.ι.isEmbedding.isInducing.specializes_iff).1 (genericPoint_specializes (U.ι u))
  have hs : ∀ x : ψ.image, ψ.toImage η ⤳ x := by
    intro x
    rw [specializes_iff_mem_closure]
    refine closure_minimal ?_ isClosed_closure (ψ.toImage.denseRange x)
    rintro _ ⟨u, rfl⟩
    exact specializes_iff_mem_closure.1 ((hη u).map ψ.toImage.continuous)
  have key : ∀ x : ψ.image, ∃ i, x ∈ V i := by
    intro x
    by_cases hne : ψ.toImage η = x
    · refine ⟨i₀, Y.homOfLE (hUA i₀) η, ?_⟩
      rw [← hne, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ψ.toImage_imageι_assoc, hψp]
    obtain ⟨O, _, _, _, c, hc₀, hcx⟩ :=
      exists_complete_discreteValuationRing_of_specializes (hs x) hne
    have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
    have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hpt' : (spMap (algebraMap O (FractionRing O)) ≫ c)
        (IsLocalRing.closedPoint (FractionRing O)) = ψ.toImage η := by
      refine Eq.trans (congrArg c (PrimeSpectrum.ext ?_)) hc₀
      change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨l, hl, hlη⟩ := ValuativeGeneric.exists_lift_of_surjectiveOnStalks ψ.toImage
      (FractionRing O) _ η hpt'
    have hls : (l ≫ U.ι) ≫ s = spMap (algebraMap O (FractionRing O)) ≫ c ≫ z := by
      rw [Category.assoc, ← hz, reassoc_of% hl]
    obtain ⟨b, hb⟩ := H O (FractionRing O) (l ≫ U.ι) (c ≫ z) (by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Hom.comp_apply, hlη]
      rfl) hls
    have hbs : b ≫ s = c ≫ z := by
      refine ext_of_isDominant (spMap (algebraMap O (FractionRing O))) ?_
      rw [← Category.assoc, hb, hls]
    obtain ⟨i, hi⟩ := hcov (b (IsLocalRing.closedPoint O))
    have hr : Set.range b ⊆ Set.range (A i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨v, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi
    obtain ⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : b' ≫ j i = c ≫ ψ.imageι ≫ p i := by
      refine ext_of_isDominant_of_isSeparated (t i) ?_
        (spMap (algebraMap O (FractionRing O))) ?_
      · rw [Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt]
      · rw [← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]
    refine ⟨i, b' (IsLocalRing.closedPoint O), ?_⟩
    have e' : (b' ≫ j i) (IsLocalRing.closedPoint O) =
        (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint O) := by rw [e]
    exact e'.trans (congrArg (ψ.imageι ≫ p i) hcx)
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 (key x)
  have hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i := fun i ↦
    ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩
  choose m hm using hm
  obtain ⟨g, hg, hgU⟩ := exists_extension_of_cover z s ψ.toImage U.ι V hV
    (fun i ↦ m i ≫ (A i).ι)
    (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt])
    (fun i T a b e ↦ by
      rw [← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp,
        Category.assoc])
  have : IsProper (g ≫ s) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g s
  have : IsDominant g := ⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩
  have : Surjective g := surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have : UniversallyClosed s := .of_comp_surjective g s
  exact {}

end GlobalTheory.TraitProper
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_unitaryRep_of_action_on_total_family : ∀ (G S H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (act : G → S → S) (E : S → H), (∀ p, act 1 p = p) → (∀ g h p, act (g * h) p = act g (act h p)) → Dense (Submodule.span ℂ (Set.range E) : Set H) → (∀ g p q, inner ℂ (E (act g p)) (E (act g q)) = inner ℂ (E p) (E q)) → (∀ p q, Continuous fun g => inner ℂ (E q) (E (act g p))) → ∃ π : G →* (H →L[ℂ] H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧ ∀ g p, π g (E p) = E (act g p) := by
  first | exact @GlobalTheory.TotalFamilyRep.exists_rep | exact GlobalTheory.TotalFamilyRep.exists_rep | (intros; apply GlobalTheory.TotalFamilyRep.exists_rep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hasDerivAt_of_weak_deriv_on_invariant_total_set : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (D : Set H) (x w : H), U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ t y, ‖U t y‖ = ‖y‖) → (∀ y, Continuous fun t => U t y) → Dense (Submodule.span ℂ D : Set H) → (∀ t, ∀ y ∈ D, U t y ∈ D) → (∀ y ∈ D, HasDerivAt (fun t : ℝ => inner ℂ (U t x) y) (inner ℂ w y) 0) → HasDerivAt (fun t : ℝ => U t x) w 0 := by
  first | exact @GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total | exact GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total | (intros; apply GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions : ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → IsUnit (1 - Aᴴ * B).det := by
  first | exact @GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions | exact GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions | (intros; apply GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.LevLaws

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


omit [StarRing E] in
theorem exists_mul_mem_span (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal)
    (hq2 : q ∉ P.asIdeal ^ 2) : ∃ s ∉ P.asIdeal, ∀ r ∈ P.asIdeal, ∃ t, s * r = q * t := by
  have h1 : P.asIdeal ∣ Ideal.span {q} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨J, hJ⟩ := h1
  have h2 : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq2
    have : q ∈ P.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self q
    rw [sq]
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨s, hsP, fun r hr => ?_⟩
  have : r * s ∈ Ideal.span {q} := hJ ▸ Ideal.mul_mem_mul hr hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨t, by rw [mul_comm s r, ← ht, mul_comm]⟩

end Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

end GlobalTheory.Mem.Col2.LevLaws
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pull_ample_kTriv {S S' : Scheme.{0}} [IsAffine S] {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) :
    Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S)
    (fun _ => trivial) hA, kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem ample_kTriv_of_iso {S S' : Scheme.{0}} [IsAffine S'] {t : SAB H S} {u : SAB H S'} {j : S' ⟶ S} [IsIso j]
    (m : SABMap u t j) (hA : Out.RelAmple u.G u.PP.L) (hK : Out.KTriv u.G u.PP.L) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac m n (g := inv j) (by simp)
  exact pull_ample_kTriv m' hA hK

theorem isIso_spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (hf : Function.Bijective f) :
    IsIso (spMap f) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hf).toCommRingCatIso.isIso_hom
  unfold spMap
  infer_instance

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  exact exists_sab f t

theorem isProper_of_map {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (hp : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback m.cart.1 hp

end GlobalTheory.PolLocal

namespace GlobalTheory.PolLocal

theorem algebraMap_fractionRing_bijective (O : Type) [CommRing O] [IsDomain O] (hf : IsField O) :
    Function.Bijective (algebraMap O (FractionRing O)) := by
  refine ⟨IsFractionRing.injective O (FractionRing O), fun z => ?_⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O) z
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel (nonZeroDivisors.ne_zero y.2)
  refine ⟨x * b, ?_⟩
  calc algebraMap O (FractionRing O) (x * b) = z * algebraMap O (FractionRing O) (y * b) := by
        rw [map_mul, map_mul, ← mul_assoc, ← hxy]
    _ = z := by rw [hb, map_one, mul_one]

end GlobalTheory.PolLocal
end
end
