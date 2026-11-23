module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
import Formalism.LocalRingCardinality.DataHost
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle012
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle400
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Bundle001
import GroundTheory.ProfiniteCohomology.Bundle001
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle389
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.AdelicDenom

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} := by
  have h := RestrictedProduct.isOpen_forall_mem (ι := HeightOneSpectrum (𝓞 F))
    (R := fun v => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)
  exact h

theorem natCast_integral (F : Type) [Field F] [NumberField F] (M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (M : Af F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
  GlobalTheory.IntegralFinAdele.natCast_apply F M v ▸
    HeightOneSpectrum.coe_mem_adicCompletionIntegers v (M : 𝓞 F)

theorem exists_common_denominator (F : Type) [Field F] [NumberField F] (K : Set (Af F))
    (hK : IsCompact K) :
    ∃ M : ℕ, 0 < M ∧ ∀ a ∈ K, ∀ v,
      ((M : Af F) * a) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  let U : {M : ℕ // 0 < M} → Set (Af F) := fun M =>
    (fun a => (M.1 : Af F) * a) ⁻¹'
      {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  have hU : ∀ M, IsOpen (U M) := fun M =>
    (isOpen_integral F).preimage (continuous_const_mul _)
  have hcov : K ⊆ ⋃ M, U M := fun a _ => by
    obtain ⟨M, hM, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a
    exact Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  refine ⟨∏ m ∈ t, m.1, Finset.prod_pos fun m _ => m.2, fun a ha v => ?_⟩
  obtain ⟨m, hm, ham⟩ := Set.mem_iUnion₂.1 (ht ha)
  obtain ⟨c, hc⟩ : m.1 ∣ ∏ m ∈ t, m.1 := Finset.dvd_prod_of_mem (fun m => m.1) hm
  have h : ((∏ m ∈ t, m.1 : ℕ) : Af F) * a = (c : Af F) * ((m.1 : Af F) * a) := by
    rw [hc, Nat.cast_mul]; ring
  rw [h, GlobalTheory.IntegralFinAdele.mul_apply']
  exact mul_mem (natCast_integral F c v) (ham v)

theorem exists_denominator_of_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (C : Set (Af F ⊗[F] E)), IsCompact C →
    ∃ d : ℕ, 0 < d ∧ ∀ x : E, (1 : Af F) ⊗ₜ[F] x ∈ C → ∃ y : 𝓞 E, (d : E) * x = y := by
  intro F E _ _ _ _ _ C hC
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let ε := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (Af F) ε
  have hcont : ∀ k, Continuous (b.coord k) := fun k =>
    IsModuleTopology.continuous_of_linearMap (b.coord k)
  have hK : IsCompact (⋃ k, (b.coord k) '' C) :=
    isCompact_iUnion fun k => hC.image (hcont k)
  obtain ⟨M, hM, hMK⟩ := exists_common_denominator F _ hK

  have : Algebra.IsAlgebraic ℤ E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).2 inferInstance
  have hm : ∀ k, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * ε k) := fun k => by
    obtain ⟨m, y, hm, hmy⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E)
      (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (ε k))
    refine ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
    rw [← nsmul_eq_mul, hmy]
    exact RingOfIntegers.isIntegral_coe y
  choose m hm0 hmi using hm
  refine ⟨M * ∏ k, m k, Nat.mul_pos hM (Finset.prod_pos fun k _ => hm0 k), fun x hx => ?_⟩

  have hcoord : ∀ k, IsIntegral ℤ ((M : F) * ε.repr x k) := fun k => by
    have hmem : b.coord k ((1 : Af F) ⊗ₜ[F] x) ∈ ⋃ k, (b.coord k) '' C :=
      Set.mem_iUnion.2 ⟨k, Set.mem_image_of_mem _ hx⟩
    have hrepr : b.coord k ((1 : Af F) ⊗ₜ[F] x) = algebraMap F (Af F) (ε.repr x k) := by
      simp [b, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]
    have h := hMK _ hmem
    rw [hrepr, ← map_natCast (algebraMap F (Af F)) M, ← map_mul] at h
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 _ h
    rw [hy]
    exact RingOfIntegers.isIntegral_coe y

  have hP : ∀ k, IsIntegral ℤ (((∏ j, m j : ℕ) : E) * ε k) := fun k => by
    obtain ⟨c, hc⟩ : m k ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ k)
    have : ((∏ j, m j : ℕ) : E) * ε k = (c : E) * ((m k : E) * ε k) := by
      rw [hc, Nat.cast_mul]; ring
    rw [this]
    exact (isIntegral_natCast c : IsIntegral ℤ (c : E)).mul (hmi k)
  have hdx : ((M * ∏ k, m k : ℕ) : E) * x =
      ∑ k, algebraMap F E ((M : F) * ε.repr x k) * (((∏ j, m j : ℕ) : E) * ε k) := by
    conv_lhs => rw [← ε.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  have hint : IsIntegral ℤ (((M * ∏ k, m k : ℕ) : E) * x) := by
    rw [hdx]
    exact IsIntegral.sum _ fun k _ => (hcoord k).algebraMap.mul (hP k)
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint
  exact ⟨y, hy.symm⟩

end GlobalTheory.CompanionTheory.AdelicDenom
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

theorem _root_.GlobalTheory.T.uniformizer_order_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | exact GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | (intros; apply GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliTrace

open Polynomial Formalism.REAL GroundTheory.BlockD.FourierDecayAlt.GaugeExists

theorem coeff_prod_lin {A : Type} [Ring A] (l : List A) (k : ℕ) (hk : k + 1 = l.length) :
    ((l.map fun b => (X + C b : A[X])).prod).coeff k = l.sum := by
  have h := prod_linear l.length (fun i => l.get i)
  have e : (List.ofFn fun i : Fin l.length => (X + C (l.get i) : A[X])) = l.map fun b => (X + C b : A[X]) := by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  rw [e] at h
  rw [h.2.2 k hk]
  conv_rhs => rw [← List.ofFn_get l, List.sum_ofFn]

theorem coeff_eq_zero_of_forall {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ) (w : ℕ → V)
    (h : ∀ u : ℂ, ∑ j ∈ Finset.range N, u ^ j • w j = 0) (i : ℕ) (hi : i < N) : w i = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  have hP : (∑ j ∈ Finset.range N, C (f (w j)) * X ^ j : ℂ[X]) = 0 := by
    refine Polynomial.funext fun u => ?_
    have := congrArg f (h u)

    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p : ℂ[X] => p.coeff i) hP
  rw [finsetSum_coeff, Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hji
    simp [coeff_C_mul_X_pow, Ne.symm hji]
  · simp [hi]

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem evU_prod_lin (l : List ℂ) (c v : ℂ) :
    evU v (((l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c)).map fun b => (X + C b)).prod) =
      algebraMap ℂ (Module.End ℂ V) (l.map (v - c + ·)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    congr 1
    simp only [evU_apply, eval₂_add, eval₂_X, eval₂_C, RingHom.id_apply, ← map_add (f := _)]
    congr 1
    ring

theorem sum_map_lin (l : List ℂ) (c : ℂ) :
    (l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c)).sum =
      algebraMap ℂ (Module.End ℂ V) (l.sum - l.length * c) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, ← map_add (f := _)]
    congr 1
    push_cast
    ring

theorem trace_of_qdet {n : ℕ} (Eo : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (l : List ℂ)
    (hl : l.length = n + 1) (φ : V)
    (h : ∀ v : ℂ, qdet Eo v φ = (l.map (v - (n : ℂ) / 2 + ·)).prod • φ) :
    (∑ i, Eo i i) φ = l.sum • φ := by
  set c : ℂ := (n : ℂ) / 2 with hc
  set L : List (Module.End ℂ V) := l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c) with hL
  set R : (Module.End ℂ V)[X] := (L.map fun b => (X + C b)).prod with hR
  set D : (Module.End ℂ V)[X] := qdetPoly Eo - R with hD
  have hev : ∀ v, (evU v D) φ = 0 := fun v => by
    rw [hD, map_sub, evU_qdetPoly, hR, hL, evU_prod_lin, LinearMap.sub_apply, h, Module.algebraMap_end_apply,
      sub_self]
  have hsum : ∀ v : ℂ, ∑ j ∈ Finset.range (D.natDegree + 1 + (n + 1)), v ^ j • (D.coeff j) φ = 0 := fun v => by
    have := hev v
    rw [evU_apply, eval₂_eq_sum_range' _ (show D.natDegree < D.natDegree + 1 + (n + 1) by omega),
      LinearMap.sum_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, RingHom.id_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
  have h0 := coeff_eq_zero_of_forall _ (fun j => (D.coeff j) φ) hsum n (by omega)
  have hq : (qdetPoly Eo).coeff n = ∑ k, Eo k k - algebraMap ℂ _ (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) := by

    rw [coeff_qdetPoly_top Eo n (by omega), (prod_linear (n + 1) _).2.2 n rfl, Finset.sum_sub_distrib, ← map_sum,
    sum_fin_cast]
  have hr : R.coeff n = algebraMap ℂ _ (l.sum - l.length * c) := by
    rw [hR, coeff_prod_lin L n (by simp [hL, hl]), hL, sum_map_lin]
  simp only [hD, coeff_sub, hq, hr] at h0
  have hs : (∑ k, Eo k k) - algebraMap ℂ (Module.End ℂ V) (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) -
      algebraMap ℂ _ (l.sum - l.length * c) = (∑ k, Eo k k) - algebraMap ℂ _ l.sum := by
    rw [sub_sub, ← map_add (f := _)]
    congr 2
    rw [hl, hc]
    push_cast
    ring
  rw [hs, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h0
  exact h0

end Gen

theorem trace_Eop_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  intro E _ _ _ a π τ m hm φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases a with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end GlobalTheory.CompanionTheory.CapelliTrace

end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

theorem _root_.GlobalTheory.T.coset_reps_of_factorization : ∀ (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop), P 1 → Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I) → (∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) → ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧ ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | exact GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | (intros; apply GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.analytic_orthogonal_vanishing : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (F : ℕ → ℝ → H) (M C : ℝ) (u : H), (∀ k t, HasDerivAt (F k) (F (k + 1) t) t) → (∀ k t, ‖F k t‖ ≤ M * C ^ k * (k.factorial : ℝ)) → (∀ k, inner ℂ u (F k 0) = 0) → ∀ t, inner ℂ u (F 0 t) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds | exact GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds | (intros; apply GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

theorem _root_.GlobalTheory.T.functional_zero_of_injective_power : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates | exact GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates | (intros; apply GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates <;> assumption)
end
