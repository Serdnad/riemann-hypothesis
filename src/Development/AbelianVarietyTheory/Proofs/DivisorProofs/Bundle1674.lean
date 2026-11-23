module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle101
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
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
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import ReciprocityTheory.SemistableReduction.Bundle002
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BoundaryForm

theorem exists_local_fun {Y : Scheme.{0}} [IrreducibleSpace Y] (Z : TopologicalSpace.Closeds Y) (hZ : Z ≠ ⊤) (y : Y) :
    ∃ (W : Y.Opens) (a : Γ(Y, W)), y ∈ W ∧ a ≠ 0 ∧ ∀ z ∈ Y.basicOpen a, z ∉ Z := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : ((Z : Set Y)ᶜ).Nonempty := Set.nonempty_compl.2 fun h => hZ (SetLike.coe_injective h)
  obtain ⟨z, hzW, hzZ⟩ := nonempty_preirreducible_inter W.isOpen Z.isClosed.isOpen_compl ⟨y, hy⟩ hne
  obtain ⟨a, ha, hz⟩ := IsAffineOpen.exists_basicOpen_le hW (V := Z.compl) ⟨z, hzZ⟩ hzW
  refine ⟨W, a, hy, ?_, fun w hw => ha hw⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hz
  exact hz

theorem exists_form_vanishing : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∃ (d : ℕ) (g : MvPolynomial (Fin T.N) F), g.IsHomogeneous d ∧ g ∉ T.imageIdeal ∧
      ∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0 := by
  intro F _ _ T hG hB
  have hV := hG.alg.variety
  have := HeightExists.isIntegral hV
  have := isNoetherian_of_isProjOver hV.proj
  have hp := HeightExists.isPrime_imageIdeal hV
  choose W a hy ha hz using exists_local_fun T.bd hG.bd_ne
  choose d P Q hP _ _ hPn hval using fun y => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F T.toLinSys hV hG.alg.bpf hB (W y) (a y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set T.Y)) (fun y => (W y).isOpen)
    fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩
  refine ⟨∑ y ∈ s, d y, ∏ y ∈ s, P y, IsHomogeneous.prod s P d fun y _ => hP y, fun h => ?_, fun K _ _ x hx => ?_⟩
  · obtain ⟨y, -, h⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hPn y (ha y) h
  · obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (ptOf x.1)))
    rw [map_prod]
    refine Finset.prod_eq_zero hys ?_
    have h0 : valR x.1 (W y) (a y) = 0 := by
      by_contra h
      exact hz y _ ((valR_ne_zero_iff x.1 hxy _).1 h) hx
    rw [← hval y K x hxy, h0, zero_mul]

end GlobalTheory.BoundaryForm
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V := by
  first | exact @GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring | exact GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring | (intros; apply GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.linearSystem_relation_of_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), AlgebraicGeometry.IsIntegral S.Y → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y), IsGenericPoint η Set.univ → ∀ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) → S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η)) (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0 → ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.Adelic.GenericRel.relation_of_generic | exact GlobalTheory.Adelic.GenericRel.relation_of_generic | (intros; apply GlobalTheory.Adelic.GenericRel.relation_of_generic <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BirFiniteFibre

open GlobalTheory.Points

theorem aeval_smul_of_isHomogeneous {F K σ : Type} [CommRing F] [CommRing K] [Algebra F K] {d : ℕ}
    {p : MvPolynomial σ F} (hp : p.IsHomogeneous d) (c : K) (y : σ → K) :
    aeval (c • y) p = c ^ d * aeval y p := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

theorem compactSpace_Y {F : Type} [Field F] (S : LinSys F) (h : S.IsVariety) : CompactSpace S.Y := by
  obtain ⟨n, i, hi, e⟩ := h.proj
  have := isProper_str F n
  have : IsProper S.str := e ▸ inferInstance
  exact ⟨by simpa using QuasiCompact.isCompact_preimage (f := S.str) Set.univ isOpen_univ isCompact_univ⟩

theorem exists_finset_separating {F : Type} [Field F] (S : LinSys F) (h : S.IsVariety) (W : S.Y.Opens)
    (hW : IsAffineOpen W) : ∃ s : Finset Γ(S.Y, W), ∀ (K : Type) [Field K] [Algebra F K] (x x' : S.Pt K),
      ptOf x.1 ∈ W → ptOf x'.1 ∈ W → (∀ a ∈ s, valR x.1 W a = valR x'.1 W a) → x = x' := by
  obtain ⟨n, i, hi, e⟩ := h.proj
  have := isProper_str F n
  have : IsProper S.str := e ▸ inferInstance
  have hle : W ≤ S.str ⁻¹ᵁ ⊤ := le_top
  have hft : (S.str.appLE ⊤ W hle).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) S.str inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hle
  letI := (S.str.appLE ⊤ W hle).hom.toAlgebra
  obtain ⟨s, hs⟩ : Algebra.FiniteType Γ(Sp F, ⊤) Γ(S.Y, W) := hft
  refine ⟨s, fun K _ _ x x' hx hx' H => Subtype.ext ?_⟩
  have h1 := (le_iff_ptOf_mem _ _).2 hx
  have h2 := (le_iff_ptOf_mem _ _).2 hx'
  refine ext_of_valR hW h1 h2 fun f => ?_
  have hf : f ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(S.Y, W)) := hs ▸ Algebra.mem_top
  induction hf using Algebra.adjoin_induction with
  | mem a ha => exact H a ha
  | algebraMap r =>
    exact (valR_appLE x.1 S.str hle h1 r).trans
      ((congrArg (fun q => valR q ⊤ r) (x.2.trans x'.2.symm)).trans (valR_appLE x'.1 S.str hle h2 r).symm)
  | add a b _ _ ha hb => rw [valR_add _ _ h1, valR_add _ _ h2, ha, hb]
  | mul a b _ _ ha hb => rw [valR_mul _ _ h1, valR_mul _ _ h2, ha, hb]

theorem exists_form_finite_fibres : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin S.N) F), g.IsHomogeneous d ∧ g ∉ S.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (y : Fin S.N → K), {x : S.Pt K | aeval (S.coords x.1) g ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y}.Finite := by
  intro F _ S hV hb hB
  classical
  haveI := compactSpace_Y S hV
  haveI := HeightExists.isPrime_imageIdeal hV
  have hcov : ∀ y : S.Y, ∃ W : S.Y.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hW hy using hcov
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set S.Y)) (fun y => (W y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  choose s hs using fun z => exists_finset_separating S hV (W z) (hW z)
  choose d P Q hP hQ hQI _ hval using fun z a => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F S hV hb hB (W z) a
  refine ⟨∑ z ∈ t, ∑ a ∈ s z, d z a, ∏ z ∈ t, ∏ a ∈ s z, Q z a, ?_, ?_, fun K _ _ y => ?_⟩
  · exact IsHomogeneous.prod _ _ _ fun z _ => IsHomogeneous.prod _ _ _ fun a _ => hQ z a
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨z, -, hz⟩
    rw [Ideal.IsPrime.prod_mem_iff] at hz
    obtain ⟨a, -, ha⟩ := hz
    exact hQI z a ha
  · have key : ∀ z ∈ t, ∀ a ∈ s z, ∀ x : S.Pt K, ptOf x.1 ∈ W z →
        aeval (S.coords x.1) (∏ z ∈ t, ∏ a ∈ s z, Q z a) ≠ 0 → (∃ c : K, S.coords x.1 = c • y) →
        valR x.1 (W z) a = aeval y (P z a) / aeval y (Q z a) := by
      rintro z hz a ha x hx hg ⟨c, hc⟩
      have h1 : aeval (S.coords x.1) (Q z a) ≠ 0 := by
        rw [map_prod, Finset.prod_ne_zero_iff] at hg
        have := hg z hz
        rw [map_prod, Finset.prod_ne_zero_iff] at this
        exact this a ha
      have h2 := hval z a K x hx
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hb.coords_ne_zero x.1 (hc.trans (zero_smul _ _))
      rw [hc, aeval_smul_of_isHomogeneous (hQ z a)] at h1 h2
      rw [aeval_smul_of_isHomogeneous (hP z a), mul_left_comm] at h2
      rw [eq_div_iff (right_ne_zero_of_mul h1)]
      exact mul_left_cancel₀ (pow_ne_zero _ hc0) h2
    refine (t.finite_toSet.biUnion (t := fun z => {x : S.Pt K | ptOf x.1 ∈ W z ∧
      aeval (S.coords x.1) (∏ z ∈ t, ∏ a ∈ s z, Q z a) ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y})
      fun z hz => Set.Subsingleton.finite fun x hx x' hx' => ?_).subset fun x hx => ?_
    · exact hs z K x x' hx.1 hx'.1 fun a ha =>
        (key z hz a ha x hx.1 hx.2.1 hx.2.2).trans (key z hz a ha x' hx'.1 hx'.2.1 hx'.2.2).symm
    · obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (ptOf x.1)))
      exact Set.mem_iUnion₂.2 ⟨z, hz, hxz, hx⟩

end GlobalTheory.BirFiniteFibre
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.CMSplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ₁ : E →+* ℂ) :
    ∃ g : E ≃ₐ[ℚ] E, ∀ x, τ₀ (g x) = τ₁ x := by
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    show algebraMap ℚ ℂ q = τ₀ (algebraMap ℚ E q)
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact ⟨(τ₁.toRatAlgHom).restrictNormal' E, fun x => (τ₁.toRatAlgHom).restrictNormal_commutes E x⟩

theorem not_isOfFinOrder_val_of_tame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (hgal : IsGalois ℚ E) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (χ : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ) (ht : ∀ v, χ.TameAt v) (hinf : χ.HasInf (fun w => (τ w).1) n)
    (hn : ∀ w, n w ≠ 0) (p : ℕ) (hp : p.Prime) (W : HeightOneSpectrum (𝓞 E)) (hN : Ideal.absNorm W.asIdeal = p)
    (hsq : (p : 𝓞 E) ∉ W.asIdeal ^ 2) : ¬ IsOfFinOrder (χ.val W) := by
  intro hfin
  classical
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht W (Formalism.L2.Host.unif W)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val W ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ₀ : E →+* ℂ := (τ w₀).1 with hτ₀
  choose g hg using fun w => exists_aut_comp τ₀ (τ w).1
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 = τ₀ (∏ w, (g w z / g w (σ z)) ^ n w) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : τ₀ (g w (σ z)) = starRingEnd ℂ (τ₀ (g w z)) := by
      rw [hg, hg]
      exact hcm.2.2.2 _ _
    have e' : (τ w).1 z = τ₀ (g w z) := (hg w z).symm
    have h0 : τ₀ (g w z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ w, (g w z / g w (σ z)) ^ n w) ^ a = 1 := by
    apply τ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := W) ha (by rw [h6, map_one])
  have hg0 : ∀ x, g w₀ x = x := fun x => τ₀.injective (hg w₀ x)
  have hres : ∀ w, (∀ f : F, τ₀ (algebraMap F E f) = w.embedding f) → w = w₀ := by
    intro w hw
    have e : w.embedding = w₀.embedding := by
      ext f
      rw [← hw f]
      exact (RingHom.congr_fun (τ w₀).2 f)
    rw [← InfinitePlace.mk_embedding w, e, InfinitePlace.mk_embedding]
  have hc : ∀ w, W.valuation E (g w (σ z)) = 1 := by
    intro w
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 ((g w : E →+* E).comp (σ : E →+* E)) fun e => ?_
    have hw : w = w₀ := hres w fun f => by
      have := RingHom.congr_fun e (algebraMap F E f)
      change g w (σ (algebraMap F E f)) = algebraMap F E f at this
      rw [← this, hg, AlgHom.commutes]
      exact RingHom.congr_fun (τ w).2 f
    subst hw
    obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
    have := RingHom.congr_fun e x
    change g w (σ x) = x at this
    rw [hg0] at this
    exact hx this
  have hgw : ∀ w, w ≠ w₀ → W.valuation E (g w z) = 1 := by
    intro w hw
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 (g w : E →+* E) fun e => hw (hres w fun f => ?_)
    have := RingHom.congr_fun e (algebraMap F E f)
    change g w (algebraMap F E f) = algebraMap F E f at this
    rw [← this, hg]
    exact RingHom.congr_fun (τ w).2 f
  rw [map_prod, Finset.prod_eq_single w₀ (fun w _ h => by rw [map_zpow₀, map_div₀, hgw w h, hc w, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hg0, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn w₀ h
  · omega
  · omega

end GlobalTheory.CMSplitValue

namespace GlobalTheory.CMSplitValue

theorem not_isOfFinOrder_val : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → IsGalois ℚ E → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ), H.HasInf (fun w => (τ w).1) n → (∀ w, n w ≠ 0) → ∀ (p : ℕ), p.Prime → ∀ W : HeightOneSpectrum (𝓞 E), Ideal.absNorm W.asIdeal = p → (p : 𝓞 E) ∉ W.asIdeal ^ 2 → ¬ IsOfFinOrder (H.val W) := by
  intro F E _ _ _ _ _ σ hcm hgal τ H n hinf hn p hp W hN hsq hfin
  obtain ⟨N, hN0, hunr⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt E H
  have ht : ∀ v, (H ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (H ^ N).HasInf (fun w => (τ w).1) (fun w => (N : ℤ) * n w) := by
    intro k
    rw [GlobalTheory.SplitValuePow.inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  refine not_isOfFinOrder_val_of_tame F E σ hcm hgal τ (H ^ N) _ ht hinf'
    (fun w => mul_ne_zero (by exact_mod_cast hN0.ne') (hn w)) p hp W hN hsq ?_
  rw [GlobalTheory.SplitValuePow.val_pow]
  exact hfin.pow

end GlobalTheory.CMSplitValue
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.satake_parameter_GL_of_conj_linear_intertwiner : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (J : V ≃ₗ⋆[ℂ] W), (∀ g x, ρ' g (J x) = J (ρ g x)) → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w ρ' (B.map star) := by
  first | exact @GlobalTheory.LFun.hasSatGL_of_conjIntertwiner | exact GlobalTheory.LFun.hasSatGL_of_conjIntertwiner | (intros; apply GlobalTheory.LFun.hasSatGL_of_conjIntertwiner <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh



theorem models_at_record_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.toCore.σ₀ → ∀ k : (T.U ((i : ℕ) + 1) σ).Comp, IsMod (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) ∧ IsONFr ((T.U ((i : ℕ) + 1) σ).X k) (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) ∧ IsInvOf (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) (cart (R.MW i (sg0 D A))) ∧ ((T.U ((i : ℕ) + 1) σ).X k).p0 = (T.Q.Dw ((i : ℕ) + 1)).q ∧ D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q ∧ (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q ∧ 1 ≤ D.R.r ∧ (T.Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ ((T.U ((i : ℕ) + 1) σ).X k).Ψ ↔ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0) ∧ (∀ hq : ((T.U ((i : ℕ) + 1) σ).X k).p0 + (T.Q.Dw ((i : ℕ) + 1)).p = D.R.r, IsBasOf (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) hq (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) (onb (R.MW i (sg0 D A)))) ∧ Dom (wtA (κ i)) (Vc D i).rank ∧ (κ i).n = (Vc D i).rank ∧ LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i σ hσ k
  subst hσ
  have hj := inR i
  have hL := hT.laws
  have hg := T.toCore.good_σ₀
  have hU := hL.unf _ hj _ hg
  have hP := hL.pins
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hP.2.2.2 _ hj).1
  have hdq : (T.Q.Dw ((i : ℕ) + 1)).q = (D.R.sigW ((i : ℕ) + 1)).2 := (hP.2.2.2 _ hj).2.1
  have hp0 := (hU.2.1 k).1
  have hΨ := (hU.2.1 k).2
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  have hε : ∀ ρ a, (R.MW i (sg0 D A)).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun ρ a => by
    rw [hC.models.order i ρ a, hdp,
      show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
  have hM : ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k) := by
    obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hg
    have hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i := hL.spaceW _ hj _ hg
    have h1 := hm k
    revert hr
    rw [hV]
    exact fun _ _ h => h
  have hn : (κ i).n = (Vc D i).rank := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    obtain ⟨τ', hτ'⟩ : ∃ τ', τ' ∈ ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ ∈ ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ, (((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).cmType τ).2 h⟩
    obtain ⟨t, -⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ' ((hΨ τ').1 hτ')
    rw [(hT.kap i t).2.2, D.sp.V_rank _ hj.1 hj.2]
  refine ⟨⟨hM, fun τ => ?_, ?_⟩, fun τ => hL.familyUniformisationBasePointOrthogonal _ hj _ hg k τ.1 τ.2, ?_, hp0, hU.1, ?_, hr1, hP.1.2.1, hΨ,
    fun hq => isBasOf_onb _ _ _ hx hq hε, hn ▸ dom_wtA (κ i), hn,
    lastPos_wtA_of_pins T.Q hP hj _ (lastPos_of_kapIs hT.kap i)⟩
  · rw [hΨ]
    exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ, fun ⟨ρ, h⟩ => h ▸ hP.1.2.2.2 ρ⟩
  · have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
    obtain ⟨w⟩ := nonempty_uw hU'
    have h1 : ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).κ0 = 2 * ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).ξ0 :=
      (GlobalTheory.Dict.uw_lattice _ _ _ _ _ _ _ _ _ ((Formalism.L2.PjFree.goodEmb_iff _).2 hg) hU' hr1 w k).1
    rw [h1, hM.2, mul_neg]
  · exact isInvOf_cart _ _ _ hx (by have := hU.1; omega) hε
  · rw [hdp, hdq]
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega

end GlobalTheory.AdTh
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertPlaces

theorem inert_places_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ _root_.Formalism.DivisionValues.conjPl P = P) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h t P
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · rintro ⟨hg, hf⟩
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hg P (Or.inl hm)).1 rfl
    have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
      refine ⟨?_, hnS⟩
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
    obtain ⟨Q, hQ⟩ := h.inert.onto P hio
    refine ⟨Q, (h.inert.tie.okI t Q).2 ⟨?_, ?_⟩, hQ⟩
    · rw [hQ]; exact hio.1
    · rw [hQ]
      rintro (hm | hm)
      · exact hnS hm
      · exact (hg P (Or.inr hm)).1 rfl

end GlobalTheory.InertPlaces
end
