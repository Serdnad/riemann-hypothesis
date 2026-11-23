module

public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
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
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Regular.Category
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

@[expose] public section

section

open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

section Index

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]

variable [IsDomain R] [IsDiscreteValuationRing R]

end Index

section Points

variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]

theorem det_algHom_basis_ne_zero (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : (Matrix.of fun i j => P j (e i)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc, hc₀⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hli := (linearIndependent_algHom_toLinearMap R S L).comp P hP
  rw [Fintype.linearIndependent_iff] at hli
  refine hc (funext (hli c (e.ext fun i => ?_)))
  have := congrFun hc₀ i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this


omit [IsDomain L] in
theorem algHom_matrix_mul_leftMulMatrix (e : Basis ι R S) (P : ι → (S →ₐ[R] L)) (x : S) :
    (Matrix.of fun j i => P j (e i)) * (Algebra.leftMulMatrix e x).map (algebraMap R L) =
      Matrix.diagonal (fun j => P j x) * Matrix.of fun j i => P j (e i) := by
  ext j k

  rw [Matrix.diagonal_mul, Matrix.of_apply, ← map_mul, ← e.sum_repr (x * e k), map_sum,
  Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Matrix.of_apply, mul_comm]

theorem map_charpoly_leftMulMatrix_eq_prod_algHom (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    (Algebra.leftMulMatrix e x).charpoly.map (algebraMap R L) = ∏ j, (X - C (P j x)) := by
  set Q : Matrix ι ι L := Matrix.of fun j i => P j (e i) with hQ
  have hQ₀ : Q.det ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact det_algHom_basis_ne_zero e hP
  have h := algHom_matrix_mul_leftMulMatrix e P x
  rw [← hQ] at h
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal]
  set A := (Algebra.leftMulMatrix e x).map (algebraMap R L)
  set D := Matrix.diagonal fun j => P j x
  have h₁ : (C : L →+* L[X]).mapMatrix Q * A.charmatrix =
      D.charmatrix * (C : L →+* L[X]).mapMatrix Q := by
    simp only [Matrix.charmatrix, mul_sub, sub_mul, ← map_mul, h]
    congr 1
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm
  have h₂ := congrArg Matrix.det h₁
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, mul_comm] at h₂
  exact mul_right_cancel₀ (C_ne_zero.mpr hQ₀) h₂

theorem algebraMap_trace_eq_sum_algHom_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  have h := map_charpoly_leftMulMatrix_eq_prod_algHom e hP x
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal] at h
  rw [Algebra.trace_eq_matrix_trace e, ← Matrix.trace_diagonal,
    Matrix.trace_eq_neg_charpoly_nextCoeff (Matrix.diagonal _), ← h,
    ← Matrix.trace_eq_neg_charpoly_nextCoeff, AddMonoidHom.map_trace]

theorem map_traceMatrix_eq_mul_transpose_of_basis {κ : Type*} (e : Basis ι R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : κ → S) :
    (Algebra.traceMatrix R v).map (algebraMap R L) =
      (Matrix.of fun i j => P j (v i)) * (Matrix.of fun i j => P j (v i)).transpose := by
  ext i k
  simp [algebraMap_trace_eq_sum_algHom_of_basis e hP, Matrix.mul_apply]

theorem algebraMap_discr_eq_det_sq_of_basis (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (v : ι → S) :
    algebraMap R L (Algebra.discr R v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by
  rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    map_traceMatrix_eq_mul_transpose_of_basis e hP, Matrix.det_mul, Matrix.det_transpose, pow_two]

theorem algebraMap_discr_basis_ne_zero (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : algebraMap R L (Algebra.discr R e) ≠ 0 := by
  rw [algebraMap_discr_eq_det_sq_of_basis e hP]
  exact pow_ne_zero _ (det_algHom_basis_ne_zero e hP)

variable [Module.Free R S] [Module.Finite R S]



omit [DecidableEq ι] in
theorem algebraMap_trace_eq_sum_algHom_of_card (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  classical
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_trace_eq_sum_algHom_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x

end Points

section Count

theorem etale_of_isReduced_of_perfectField (K S : Type*) [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Module.Finite K S] [IsReduced S] : Algebra.Etale K S := by
  have : IsArtinianRing S := .of_finite K S
  have (I : MaximalSpectrum S) : Algebra.FormallyEtale K (S ⧸ I.asIdeal) := by
    letI := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyEtale.of_isSeparable K (S ⧸ I.asIdeal)
  exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars K).symm,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

variable (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field L] [Algebra R L]

theorem natCard_algHom_eq_finrank_of_etale_baseChange [Module.Free R S] [Module.Finite R S]
    [IsSepClosed L] [Algebra.FormallyEtale L (L ⊗[R] S)] :
    Nat.card (S →ₐ[R] L) = finrank R S := by
  have := (algebraMap R L).domain_nontrivial
  have : IsArtinianRing (L ⊗[R] S) := .of_finite L _
  have := Fintype.ofFinite (PrimeSpectrum (L ⊗[R] S))
  rw [Nat.card_congr (AlgHom.liftEquiv R L S L),
    Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[R] S)),
    ← Module.finrank_baseChange (R := L) (S := R) (M' := S),
    (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[R] S)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem natCard_algHom_eq_finrank_of_isReduced_baseChange [Module.Free R S] [Module.Finite R S]
    [IsAlgClosed L] [IsReduced (L ⊗[R] S)] : Nat.card (S →ₐ[R] L) = finrank R S :=
  have := etale_of_isReduced_of_perfectField L (L ⊗[R] S)
  natCard_algHom_eq_finrank_of_etale_baseChange R S L

end Count

section Etale

variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]


variable (S) in
theorem natCard_algHom_eq_finrank_of_etale : Nat.card (S →ₐ[K] L) = finrank K S :=
  have := Algebra.FormallyUnramified.finite_of_free K S
  natCard_algHom_eq_finrank_of_etale_baseChange K S L


variable {K L} {ι : Type*} [Fintype ι]

end Etale

section Reduced

variable {K S L ι : Type*} [Field K] [PerfectField K] [CommRing S] [Algebra K S]
  [Module.Finite K S] [IsReduced S] [Field L] [Algebra K L] [IsSepClosed L] [Fintype ι]
  [DecidableEq ι]

end Reduced

section Both

variable {R S L ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [Algebra R S] [CommRing L] [IsDomain L] [Algebra R L] [Fintype ι] [DecidableEq ι]

end Both

end GlobalTheory
end

section

open scoped PowerSeries TensorProduct

namespace GlobalTheory


open scoped PowerSeries TensorProduct in
theorem _root_.GlobalTheory.integralClosure_restrictScalars_of_isIntegral (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [Algebra.IsIntegral A A'] :
    (integralClosure A' B).restrictScalars A = integralClosure A B := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

section Contraction

variable {A : Type*} [CommRing A] (M : Submonoid A) {S : Type*} [CommRing S] [Algebra A S]
  [IsLocalization M S]

end Contraction

section PowerSeries

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

section Away

variable {ϖ : O} (hϖ : Irreducible ϖ) (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.Away (C ϖ : O⟦X⟧) S]

include hϖ

variable (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭 = Ideal.span {algebraMap O⟦X⟧ S X})
  (V : Type*) [CommRing V] [Algebra S V] [IsLocalization.AtPrime V 𝔭]

include h𝔭

end Away

end PowerSeries

universe u

end GlobalTheory
end

section

universe u_1 u_2

open CategoryTheory Abelian Limits RingTheory.Sequence Pointwise

namespace GlobalTheory.RegularElementQuotient

theorem maximalIdeal_smul_top_lt_top {R : Type u_1} [CommRing R] [IsLocalRing R]
    (M : Type u_2) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h

  have hbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
      Module.Finite.fg_top h.ge (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  exact top_ne_bot hbot

theorem exists_isRegular_quotSMulTop {R : Type u_1} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Small.{u_2, u_1} R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {xs : List R} (hxs : IsRegular M xs) {n : ℕ}
    (hn : n + 1 ≤ xs.length) {y : R} (hy : y ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M y) :
    ∃ zs : List R, zs.length = n ∧ IsRegular (QuotSMulTop y M) zs := by
  set 𝔪 := IsLocalRing.maximalIdeal R

  have : Nontrivial M :=
    (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ hxs.top_ne_smul)

  have hmem : ∀ x ∈ xs, x ∈ 𝔪 := by
    intro x hx
    by_contra hx𝔪
    have hu : IsUnit x := by
      by_contra hnu
      exact hx𝔪 ((IsLocalRing.mem_maximalIdeal x).mpr hnu)
    have htop : Ideal.ofList xs = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hx) hu
    apply hxs.top_ne_smul
    rw [htop, Submodule.top_smul]

  have : Nontrivial (QuotSMulTop y M) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    refine ne_top_of_le_ne_top (maximalIdeal_smul_top_lt_top (R := R) M).ne ?_
    rw [← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hy)
  have hltM : 𝔪 • (⊤ : Submodule R M) < ⊤ := maximalIdeal_smul_top_lt_top M
  have hltQ : 𝔪 • (⊤ : Submodule R (QuotSMulTop y M)) < ⊤ :=
    maximalIdeal_smul_top_lt_top (QuotSMulTop y M)

  have hM := (ModuleCat.exists_isRegular_tfae 𝔪 xs.length (ModuleCat.of R M) hltM).out 4 1
  have hExtM := hM.mp ⟨xs, rfl, hmem, hxs⟩

  have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg
  have supp𝔪 : Module.support R (Shrink.{u_2} (R ⧸ 𝔪)) =
      PrimeSpectrum.zeroLocus 𝔪 := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient]
  have hExtQ : ∀ i < n, Subsingleton (Abelian.Ext
      (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) (ModuleCat.of R (QuotSMulTop y M)) i) := by
    intro i hi
    have hE := Abelian.Ext.covariant_sequence_exact₃'
      (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) hS i (i + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at hE
    have h0 := hExtM (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) inferInstance inferInstance
      (by rw [supp𝔪]) i (by omega)
    have h1 := hExtM (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) inferInstance inferInstance
      (by rw [supp𝔪]) (i + 1) (by omega)
    have key : ∀ x : Abelian.Ext (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪)))
        (ModuleCat.of R (QuotSMulTop y M)) i, x = 0 := by
      intro x
      obtain ⟨w, hw⟩ := (hE x).mp (h1.elim _ _)
      rw [← hw, h0.elim w 0]
      exact map_zero _
    exact ⟨fun a b => by rw [key a, key b]⟩

  have hQ := (ModuleCat.exists_isRegular_tfae 𝔪 n
    (ModuleCat.of R (QuotSMulTop y M)) hltQ).out 2 4
  obtain ⟨zs, hlen, -, hzs⟩ := hQ.mp hExtQ
  exact ⟨zs, hlen, hzs⟩

end GlobalTheory.RegularElementQuotient
end
