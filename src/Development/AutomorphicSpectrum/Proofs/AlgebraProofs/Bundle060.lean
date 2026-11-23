module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle050
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PflagInd
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.GramDet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem norm_coe_le_one {E : Type} [Field E] [NumberField E] {ℓ : Nat.Primes} (j : E →+* ℂ_[ℓ]) (b : 𝓞 E) :
    ‖j (b : E)‖ ≤ 1 :=
  ReciprocityTheory.ChartRestriction.L1.KE.norm_le_one_of_integral_int _
    (map_isIntegral_int j (RingOfIntegers.isIntegral_coe b))

theorem norm_natCast_eq_one {ℓ : Nat.Primes} {n : ℕ} (h : ¬ (ℓ : ℕ) ∣ n) : ‖(n : ℂ_[ℓ])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' (ℓ : ℕ) (n : ℚ_[ℓ])
  have h2 : ‖(n : ℚ_[ℓ])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd ℓ.2).2 h)
  rw [h2] at h1
  simpa using h1

theorem norm_det_le_one {E : Type} [Field E] [NumberField E] {ℓ : Nat.Primes} (j : E →+* ℂ_[ℓ])
    {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I E) (h : ∀ a b, ∃ t : 𝓞 E, M a b = t) :
    ‖j M.det‖ ≤ 1 := by
  rw [RingHom.map_det]
  have := GlobalTheory.T.ultrametric_det_norm_le ℂ_[ℓ] I (j.mapMatrix M) 1 zero_le_one (fun a b => by
    obtain ⟨t, ht⟩ := h a b
    simpa [ht] using norm_coe_le_one j t)
  simpa using this

theorem exists_inverse {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    {I : Type} [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : ℕ) (hx : IsLocBasis (𝓞 E) ℓ x)
    (δ : 𝓞 E) (hδ0 : δ ≠ 0) (n₁ : ℕ)
    (hgen : ∀ a ∈ differentIdeal ℤ (𝓞 E), (n₁ : 𝓞 E) * a ∈ Ideal.span {δ}) :
    ∃ (C : Matrix I I E) (N : ℕ), (∀ a b, ∃ t : 𝓞 E, C a b = t) ∧
      ((δ : E) • gramE D x) * C = (N : E) • (1 : Matrix I I E) ∧ ∃ n₀ : ℕ, ¬ ℓ ∣ n₀ ∧ N = n₀ * n₀ * n₁ := by
  obtain ⟨hli, n₀, hn₀, hspan⟩ := hx
  obtain ⟨-, hadd1, hadd2, hsm1, hsm2, -, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  obtain ⟨-, hdual⟩ := GlobalTheory.T.sesq_unimodular_dual E H D
  have hδE : (δ : E) ≠ 0 := by simpa using hδ0
  let S := Submodule.span (𝓞 E) (Set.range x)
  let b : Module.Basis I (𝓞 E) S := Module.Basis.span hli
  have hb : ∀ i, ((b i : S) : D.La) = x i := fun i => congrArg Subtype.val (Module.Basis.span_apply hli i)
  let g : D.La →ₗ[𝓞 E] S := LinearMap.codRestrict S ((n₀ : 𝓞 E) • LinearMap.id) (fun y => by
    simpa [Nat.cast_smul_eq_nsmul] using hspan y)
  have hg : ∀ y, ((g y : S) : D.La) = (n₀ : 𝓞 E) • y := fun y => by simp [g]
  let c : I → D.La →ₗ[𝓞 E] 𝓞 E := fun k => (b.coord k).comp g
  have hc : ∀ y, (n₀ : 𝓞 E) • y = ∑ m, c m y • x m := fun y => by
    calc (n₀ : 𝓞 E) • y = ((g y : S) : D.La) := (hg y).symm
      _ = ((∑ i, b.repr (g y) i • b i : S) : D.La) := by rw [b.sum_repr]
      _ = _ := by
        rw [AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun m _ => by rw [Submodule.coe_smul, hb]; rfl
  have hcx : ∀ k a, c k (x a) = if a = k then (n₀ : 𝓞 E) else 0 := fun k a => by
    have : g (x a) = (n₀ : 𝓞 E) • b a := Subtype.ext (by simp [hg, hb])
    simp [c, this, Module.Basis.coord_apply, Finsupp.single_apply]
  let f : I → D.La →ₗ[𝓞 E] E := fun k =>
    (LinearMap.mulLeft (𝓞 E) ((n₁ : E) * (δ : E)⁻¹)).comp ((Algebra.linearMap (𝓞 E) E).comp (c k))
  have hf : ∀ k y, f k y = (n₁ : E) * (δ : E)⁻¹ * (c k y : E) := fun k y => rfl
  have hex : ∀ k, ∃ y, ∀ z, f k z = sesq D z y := fun k => by
    refine hdual (f k) fun δ' hδ' z => ?_
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hgen δ' hδ')
    refine ⟨t * c k z, ?_⟩
    have ht' : (t : E) * (δ : E) = (n₁ : E) * (δ' : E) := by
      have := congrArg (fun u : 𝓞 E => (u : E)) ht
      simpa using this
    rw [hf]
    push_cast
    field_simp
    linear_combination (-(c k z : E)) * ht'
  choose y hy using hex
  let sA : D.La → D.La →+ E := fun z => AddMonoidHom.mk' (fun w => sesq D z w) (hadd2 z)
  refine ⟨Matrix.of fun m k => ((H.bar (c m (y k)) : 𝓞 E) : E), n₀ * n₀ * n₁, fun a b' => ⟨_, rfl⟩, ?_,
    n₀, hn₀, rfl⟩
  ext a k
  have key : sesq D (x a) ((n₀ : 𝓞 E) • y k) =
      ∑ m, IsCMField.complexConj E ((c m (y k) : 𝓞 E) : E) * sesq D (x a) (x m) := by
    rw [hc (y k)]
    calc sesq D (x a) (∑ m, c m (y k) • x m) = sA (x a) (∑ m, c m (y k) • x m) := rfl
      _ = ∑ m, sA (x a) (c m (y k) • x m) := map_sum _ _ _
      _ = _ := Finset.sum_congr rfl fun m _ => hsm2 _ _ _
  have h2 : sesq D (x a) ((n₀ : 𝓞 E) • y k) = (n₀ : E) * f k (x a) := by
    rw [hsm2, hy]
    simp
  rw [h2] at key
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, gramE, smul_eq_mul, H.bar_eq, Matrix.one_apply]
  have h3 : ∑ m, (δ : E) * sesq D (x a) (x m) * IsCMField.complexConj E ((c m (y k) : 𝓞 E) : E)
      = (δ : E) * ((n₀ : E) * f k (x a)) := by
    rw [key, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [h3, hf, hcx]
  by_cases hak : a = k
  · simp [hak]; field_simp
  · simp [hak]

theorem log_norm_det_gramE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x).det‖ = -(Fintype.card I : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  intro E _ _ _ H D I _ _ x ℓ hx j
  obtain ⟨δ, hδ, hδ0, ⟨n₁, hn₁, hgen⟩, hnorm⟩ :=
    GlobalTheory.T.ideal_padic_generator_log_norm E (differentIdeal ℤ (𝓞 E)) ℓ differentIdeal_ne_bot
  obtain ⟨C, N, hC, hmul, n₀, hn₀, rfl⟩ := exists_inverse H D x ℓ hx δ hδ0 n₁ hgen
  obtain ⟨-, -, -, -, -, -, hint⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  have hM : ‖j ((δ : E) • gramE D x).det‖ ≤ 1 := norm_det_le_one j _ fun a b => by
    obtain ⟨t, ht⟩ := hint δ hδ (x a) (x b)
    exact ⟨t, by simpa [gramE] using ht⟩
  have hCn : ‖j C.det‖ ≤ 1 := norm_det_le_one j C hC
  have hprod : ‖j ((δ : E) • gramE D x).det‖ * ‖j C.det‖ = 1 := by
    have hN : Matrix.det (((n₀ * n₀ * n₁ : ℕ) : E) • (1 : Matrix I I E)) = ((n₀ * n₀ * n₁ : ℕ) : E) ^ Fintype.card I := by
      rw [Matrix.det_smul, Matrix.det_one, _root_.mul_one]
    rw [← norm_mul, ← map_mul, ← Matrix.det_mul, hmul, hN, map_pow, norm_pow, map_natCast, Nat.cast_mul, Nat.cast_mul,
      norm_mul, norm_mul, norm_natCast_eq_one hn₀, norm_natCast_eq_one hn₁]
    simp
  have hu : ‖j ((δ : E) • gramE D x).det‖ = 1 := by
    refine le_antisymm hM ?_
    calc (1 : ℝ) = ‖j ((δ : E) • gramE D x).det‖ * ‖j C.det‖ := hprod.symm
      _ ≤ ‖j ((δ : E) • gramE D x).det‖ * 1 := by gcongr
      _ = _ := _root_.mul_one _
  rw [Matrix.det_smul, map_mul, norm_mul, map_pow, norm_pow] at hu
  have hj : ‖j (δ : E)‖ ≠ 0 := by
    simpa using hδ0
  have hd : ‖j (gramE D x).det‖ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hu
    exact zero_ne_one hu
  have hl := congrArg Real.log hu
  rw [Real.log_mul (pow_ne_zero _ hj) hd, Real.log_pow, Real.log_one] at hl
  rw [← hnorm j]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl.GramDet
end
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.flag_pair_base_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ) (f g : Fin N → MRing ι O), IsFlagPair ϖ x E E' w w' b b' f g → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → IsFlagPair ϖ (joinCoord x z) EB E'B w w' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ w₁' : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → (∀ i, w₁' i = bc (w' i)) → ∀ EB E'B : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsPullBC O x z bc E' E'B → IsFlagPair ϖ (bcCoord x z) EB E'B w₁ w₁' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main | exact GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.CompanionTheory.Relay.sum_intNumL_classList_eq_of_isSymmetric : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle F (segreVec y) N V) (w v : Module.Basis (Fin N) Ω V) (b u : Fin N → K → ℤ), IsFlagFrame y B w b → IsFlagFrame y B v u → ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → ∀ Y : List (K → ℤ), Y.length + c = e → ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList b μ ++ Y) = ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList u μ ++ Y) := by
  first | exact @PositivityTheory.HtPt.Pflag.field_flag_indep | exact PositivityTheory.HtPt.Pflag.field_flag_indep
end

section


theorem _root_.GlobalTheory.T.projection_formula_degree : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | exact GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | (intros; apply GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.complete_dvr_dominating_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Type) [Field l] [Algebra (IsLocalRing.ResidueField V) l] [FiniteDimensional (IsLocalRing.ResidueField V) l], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (f : V →+* R) (_ : IsLocalHom f) (s : l →+* IsLocalRing.ResidueField R), IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧ Function.Injective f ∧ s.comp (algebraMap _ l) = IsLocalRing.ResidueField.map f := by
  first | exact @GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation | exact GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation | (intros; apply GlobalTheory.CompanionTheory.Relay.complete_dvr_dominating_valuation <;> assumption)
end
