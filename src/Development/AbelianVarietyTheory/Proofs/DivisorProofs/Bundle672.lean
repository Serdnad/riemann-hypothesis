module

public import Mathlib.RingTheory.Ideal.Height
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle631
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle632
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle001
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.MvPolynomial.Localization
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017

@[expose] public section

section

namespace GlobalTheory.FinTypeIntCatenary

open ReciprocityTheory.CA

theorem isCM_atPrime_of_le {S : Type*} [CommRing S] (𝔓 𝔑 : Ideal S) [𝔓.IsPrime] [𝔑.IsPrime]
    (hle : 𝔓 ≤ 𝔑) (h : IsCM (Localization.AtPrime 𝔑)) : IsCM (Localization.AtPrime 𝔓) := by
  have hdisj : Disjoint (𝔑.primeCompl : Set S) (𝔓 : Set S) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)
  let q : Ideal (Localization.AtPrime 𝔑) := 𝔓.map (algebraMap S (Localization.AtPrime 𝔑))
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔑.primeCompl _ 𝔓 inferInstance hdisj
  have h2 := h.localization_atPrime q
  have hc : q.comap (algebraMap S (Localization.AtPrime 𝔑)) = 𝔓 :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔑.primeCompl _ inferInstance hdisj
  haveI : IsLocalization 𝔓.primeCompl (Localization.AtPrime q) := by
    have h0 : IsLocalization (q.comap (algebraMap S (Localization.AtPrime 𝔑))).primeCompl
        (Localization.AtPrime q) :=
      IsLocalization.isLocalization_atPrime_localization_atPrime (M := 𝔑.primeCompl) q
    have hsub : (q.comap (algebraMap S (Localization.AtPrime 𝔑))).primeCompl = 𝔓.primeCompl :=
      Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hc]
    rw [hsub] at h0
    exact h0
  exact h2.of_ringEquiv (IsLocalization.algEquiv 𝔓.primeCompl (Localization.AtPrime q) (Localization.AtPrime 𝔓)).toRingEquiv

theorem height_comap_mk {S : Type*} [CommRing S] (Q : Ideal S) [Q.IsPrime] (J : Ideal (S ⧸ Q))
    [J.IsPrime] (h : IsCM (Localization.AtPrime (J.comap (Ideal.Quotient.mk Q)))) :
    (J.comap (Ideal.Quotient.mk Q)).height = Q.height + J.height := by
  have hle : Q ≤ J.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, J.zero_mem]
  have := height_eq_add_of_isCM_localization (J.comap (Ideal.Quotient.mk Q)) Q h hle
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this

theorem height_le_of_equidim {S : Type*} [CommRing S] (d : ℕ)
    (hS : ∀ (𝔑 : Ideal S) [𝔑.IsMaximal], IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = d)
    (Q : Ideal S) [Q.IsPrime] (P M : Ideal (S ⧸ Q)) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim ((S ⧸ Q) ⧸ P) := by
  haveI hMt : (M.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨hCM1, hd1⟩ := hS (M.comap (Ideal.Quotient.mk Q))
  have e1 := height_comap_mk Q M hCM1
  obtain ⟨M', hM', hPM'⟩ := Ideal.exists_le_maximal (P.comap (Ideal.Quotient.mk Q))
    (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨hCM2, hd2⟩ := hS M'
  have e2 := height_eq_add_of_isCM_localization M' (P.comap (Ideal.Quotient.mk Q)) hCM2 hPM'
  have e3 := height_comap_mk Q P (isCM_atPrime_of_le _ M' hPM' hCM2)
  have hQM : Q ≤ M.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M.zero_mem]
  have hQP : Q ≤ P.comap (Ideal.Quotient.mk Q) := fun x hx => by
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, P.zero_mem]
  have hQle : Q.height ≤ d := hd1 ▸ Ideal.height_mono hQM
  have hQt : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
  have key : M.height = P.height +
      (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height := by
    have hsum : Q.height + M.height = Q.height + (P.height +
        (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height) := by
      rw [← e1, hd1, ← hd2, e2, e3, add_assoc]
    exact WithTop.add_left_cancel hQt hsum
  haveI : (M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPM')
  have hb : ((M'.map (Ideal.Quotient.mk (P.comap (Ideal.Quotient.mk Q)))).height : WithBot ℕ∞) ≤
      ringKrullDim (S ⧸ P.comap (Ideal.Quotient.mk Q)) := Ideal.height_le_ringKrullDim_of_isPrime
  have hdim : ringKrullDim ((S ⧸ Q) ⧸ (P.comap (Ideal.Quotient.mk Q)).map (Ideal.Quotient.mk Q)) =
      ringKrullDim (S ⧸ P.comap (Ideal.Quotient.mk Q)) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQP)
  rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hdim
  rw [key, hdim]
  push_cast
  exact add_le_add le_rfl hb

theorem isMaximal_comap_C_int (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ)).IsMaximal := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) ℤ ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

theorem isCM_localization_int (p : Ideal ℤ) [p.IsMaximal] :
    IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = 1 := by
  have hp : p ≠ ⊥ := by
    intro h
    have : (⊥ : Ideal ℤ).IsMaximal := h ▸ inferInstance
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr this)
  haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hp _
  have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
  refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, hd⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
  refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact IsSMulRegular.of_ne_zero hϖ.ne_zero

theorem exists_maximal_mvPolynomial_localization (N : ℕ) (p : Ideal ℤ) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) ℤ) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) ℤ)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) ℤ) ∈ J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_under W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap ℤ (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) ℤ) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

theorem isCM_and_height_of_isMaximal (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = ((N + 1 : ℕ) : ℕ∞) := by
  haveI := isMaximal_comap_C_int N 𝔑
  obtain ⟨hCM, hdim⟩ := isCM_localization_int (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

theorem height_maximal_le (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (P M : Ideal A) [P.IsPrime] [M.IsMaximal] :
    (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ A›
  haveI : (RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)).IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) ℤ →+* A)) hf
  haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  have h := height_le_of_equidim (N + 1) (isCM_and_height_of_isMaximal N) _ (P.comap e) (M.comap e)
  rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
  have hdim : ringKrullDim ((MvPolynomial (Fin N) ℤ ⧸ RingHom.ker (f : MvPolynomial (Fin N) ℤ →+* A)) ⧸
      P.comap e) = ringKrullDim (A ⧸ P) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
      (Ideal.map_comap_of_surjective _ e.surjective P).symm)
  rwa [hdim] at h

end GlobalTheory.FinTypeIntCatenary
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem GlobalTheory.AbhyankarBC.nonempty_tensor_algEquiv_of_isFractionRing : ∀ (S K L F : Type) [CommRing S] [Field K] [Algebra S K] [IsFractionRing S K] [CommRing L]
    [Algebra K L] [Algebra S L] [IsScalarTower S K L] [CommRing F] [Algebra K F] [Algebra S F]
    [IsScalarTower S K F], Nonempty (F ⊗[S] L ≃ₐ[F] F ⊗[K] L) := by
  intro S K L F _ _ _ _ _ _ _ _ _ _ _ _
  have hb : IsBaseChange K (LinearMap.id : L →ₗ[S] L) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).mp
      (isLocalizedModule_id (nonZeroDivisors S) L K)
  let g : K ⊗[S] L →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) (AlgHom.id S L) (fun _ _ => Commute.all _ _)
  have hg : (g : K ⊗[S] L → L) = hb.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp [g, IsBaseChange.equiv_tmul, Algebra.smul_def]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  let e0 : K ⊗[S] L ≃ₐ[K] L := AlgEquiv.ofBijective g (by rw [hg]; exact hb.equiv.bijective)
  exact ⟨(Algebra.TensorProduct.cancelBaseChange S K F F L).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl e0)⟩

theorem GlobalTheory.AbhyankarBC.tensor_map_val_bijective_of_smul_mem : ∀ (D B F : Type) [CommRing D] [CommRing B] [Algebra D B] [CommRing F] [Algebra D F]
    (N : Subalgebra D B) (M : Submonoid D), (∀ m ∈ M, IsUnit (algebraMap D F m)) →
    (∀ b : B, ∃ m ∈ M, m • b ∈ N) →
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id F F) N.val : F ⊗[D] N →ₐ[F] F ⊗[D] B) := by
  intro D B F _ _ _ _ _ N M hM hN
  let Dm := Localization M
  have hM' : ∀ y : M, IsUnit (algebraMap D F y) := fun y => hM y y.2
  letI : Algebra Dm F := (IsLocalization.lift (M := M) (S := Dm) (g := algebraMap D F) hM').toAlgebra
  haveI : IsScalarTower D Dm F :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq (M := M) (S := Dm) hM' x).symm)
  let ι : Dm ⊗[D] N →ₐ[Dm] Dm ⊗[D] B := Algebra.TensorProduct.map (AlgHom.id Dm Dm) N.val
  have hι : Function.Bijective ι := by
    constructor
    · have := Module.Flat.lTensor_preserves_injective_linearMap (M := Dm) N.val.toLinearMap
        Subtype.val_injective
      exact this
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul a b =>
        obtain ⟨m, hm, hmb⟩ := hN b
        let u := (IsLocalization.map_units Dm (⟨m, hm⟩ : M)).unit
        refine ⟨(a * ↑u⁻¹) ⊗ₜ[D] (⟨m • b, hmb⟩ : N), ?_⟩
        simp only [ι, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
        rw [← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        have hu : (u : Dm) = algebraMap D Dm m := rfl
        rw [← hu, mul_left_comm, Units.mul_inv, mul_one]
      | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
  let eι : Dm ⊗[D] N ≃ₐ[Dm] Dm ⊗[D] B := AlgEquiv.ofBijective ι hι
  let E : F ⊗[D] N ≃ₐ[F] F ⊗[D] B :=
    (Algebra.TensorProduct.cancelBaseChange D Dm F F N).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl eι).trans
        (Algebra.TensorProduct.cancelBaseChange D Dm F F B))
  have hE : ⇑(Algebra.TensorProduct.map (AlgHom.id F F) N.val : F ⊗[D] N →ₐ[F] F ⊗[D] B) = ⇑E := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f n =>
      simp [E, eι, ι, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [hE]
  exact E.bijective

theorem GlobalTheory.AbhyankarBC.exists_smul_mem_integralClosure_tensor : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L] [Algebra.IsAlgebraic K L]
    [CommRing D] [Algebra S D], ∀ b : D ⊗[S] L,
    ∃ m ∈ Algebra.algebraMapSubmonoid D (nonZeroDivisors S), m • b ∈ integralClosure D (D ⊗[S] L) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ b
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | tmul d l =>
    obtain ⟨s, hs0, hint⟩ := IsAlgebraic.exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff S K L).mpr (Algebra.IsAlgebraic.isAlgebraic l))
    refine ⟨algebraMap S D s, ⟨s, mem_nonZeroDivisors_of_ne_zero hs0, rfl⟩, ?_⟩
    have h1 : algebraMap S D s • (d ⊗ₜ[S] l) = algebraMap D (D ⊗[S] L) d * ((1 : D) ⊗ₜ[S] (s • l)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        algebraMap_smul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, TensorProduct.tmul_smul]
    rw [h1]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ d) ?_
    exact (hint.map (Algebra.TensorProduct.includeRight : L →ₐ[S] D ⊗[S] L)).tower_top
  | add x y hx hy =>
    obtain ⟨m1, hm1, h1⟩ := hx
    obtain ⟨m2, hm2, h2⟩ := hy
    refine ⟨m1 * m2, mul_mem hm1 hm2, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Subalgebra.smul_mem _ h1 _
    · rw [mul_smul]; exact Subalgebra.smul_mem _ h2 _

theorem GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  intro S S₁ K K₁ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj q hq hqu π hπ y hy hram hsep
  let f : S[X] := X ^ q - C π
  let D := AdjoinRoot f
  have hD : Algebra.Etale D (integralClosure D (D ⊗[S] L)) :=
    GlobalTheory.T.abhyankar_dvr_of_isSeparable_alt S K L π q D ⟨AlgEquiv.refl⟩ hπ hqu hram hsep
  let φ : D →ₐ[S] S₁ := AdjoinRoot.liftAlgHom f (Algebra.ofId S S₁) y (by simp [f, hy])
  letI : Algebra D S₁ := φ.toRingHom.toAlgebra
  letI : Algebra D K₁ := ((algebraMap S₁ K₁).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower D S₁ K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower S D S₁ := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  haveI : IsScalarTower S D K₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply S S₁ K₁, IsScalarTower.algebraMap_apply S D S₁]; rfl)
  let N := integralClosure D (D ⊗[S] L)
  let T := S₁ ⊗[D] N
  haveI : Algebra.Etale S₁ T := Algebra.Etale.baseChange D N S₁
  haveI : Algebra.IsIntegral S₁ T := Algebra.IsIntegral.tensorProduct D S₁ N
  haveI hT := GlobalTheory.T.etale_integralClosure_tensor S₁ K₁ T inferInstance inferInstance
  have hunit : ∀ m ∈ Algebra.algebraMapSubmonoid D (nonZeroDivisors S), IsUnit (algebraMap D K₁ m) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S S₁ K₁]
    refine IsUnit.mk0 _ ?_
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective S₁ K₁), map_eq_zero_iff _ hinj]
    exact nonZeroDivisors.ne_zero hs
  let e1 : K₁ ⊗[S₁] T ≃ₐ[K₁] K₁ ⊗[D] N := Algebra.TensorProduct.cancelBaseChange D S₁ K₁ K₁ N
  let e2 : K₁ ⊗[D] N ≃ₐ[K₁] K₁ ⊗[D] (D ⊗[S] L) :=
    AlgEquiv.ofBijective _ (GlobalTheory.AbhyankarBC.tensor_map_val_bijective_of_smul_mem D (D ⊗[S] L) K₁ N _ hunit (GlobalTheory.AbhyankarBC.exists_smul_mem_integralClosure_tensor S K L D))
  let e3 : K₁ ⊗[D] (D ⊗[S] L) ≃ₐ[K₁] K₁ ⊗[S] L := Algebra.TensorProduct.cancelBaseChange S D K₁ K₁ L
  obtain ⟨e4⟩ := GlobalTheory.AbhyankarBC.nonempty_tensor_algEquiv_of_isFractionRing S K L K₁
  let e : K₁ ⊗[S₁] T ≃ₐ[S₁] K₁ ⊗[K] L := (((e1.trans e2).trans e3).trans e4).restrictScalars S₁
  exact Algebra.Etale.of_equiv e.mapIntegralClosure
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.smooth_bump_chart_ball_halfOne : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (i : ι) (p : V n) (ρ : ℝ), 0 < ρ → closedBall p ρ ⊆ (A.chart i).target → ∃ χ : Y → ℝ, A.SmoothFn χ ∧ tsupport χ ⊆ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball p (ρ / 2) → χ y = 1 := by
  first | exact @GlobalTheory.smooth_bump_chart_ball | exact GlobalTheory.smooth_bump_chart_ball | (intros; apply GlobalTheory.smooth_bump_chart_ball <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem _root_.GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient : ∀ (O : Type) [CommRing O] (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (act : OAct O G), IsSemiAbelian G → ∀ (T : TorusExtension G), letI := T.addCommGroup; letI := T.grpB; ∃ (actB : OAct O T.B) (actT : OAct O (splitTorus (Sp k) T.X)), (∀ a, T.q ≫ actB.act a = act.act a ≫ T.q) ∧ (∀ a, actT.act a ≫ T.i = T.i ≫ act.act a) := by
  first | exact @GlobalTheory.SemiAbAct.exists_torus_quotient_act | exact GlobalTheory.SemiAbAct.exists_torus_quotient_act | (intros; apply GlobalTheory.SemiAbAct.exists_torus_quotient_act <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.KeyFam

theorem holUnif_transport_linearEquiv : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  intro h A _ L u T
  have hc : Continuous T := T.toContinuousLinearEquiv.continuous
  have hd : Differentiable ℂ T := T.toContinuousLinearEquiv.differentiable
  let Λ' : Submodule ℤ (Fin h → ℂ) := u.Λ.comap ((T.restrictScalars ℤ).toLinearMap)
  have hmem : ∀ z, z ∈ Λ' ↔ T z ∈ u.Λ := fun z => Iff.rfl
  have hdisc : DiscreteTopology Λ' := by
    haveI := u.discrete
    let f : Λ' → u.Λ := fun z => ⟨T z, (hmem z).1 z.2⟩
    have hf : Continuous f := (hc.comp continuous_subtype_val).subtype_mk _
    have hi : Function.Injective f := fun a b hab =>
      Subtype.ext (T.injective (congrArg Subtype.val hab))
    exact DiscreteTopology.of_continuous_injective hf hi
  have hfull : Submodule.span ℝ (Λ' : Set (Fin h → ℂ)) = ⊤ := by
    have h1 : (Λ' : Set (Fin h → ℂ)) = (T.symm.restrictScalars ℝ).toLinearMap '' (u.Λ : Set (Fin h → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨T z, hz, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        refine (hmem _).2 ?_
        simpa using hw
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.restrictScalars ℝ).surjective
  refine ⟨{ ex := fun z => u.ex (T z)
            ex_add := fun z w => by rw [map_add (f := _), u.ex_add]
            ex_onto := u.ex_onto.comp T.surjective
            Λ := Λ'
            ker := fun z => u.ker (T z)
            discrete := hdisc
            full := hfull
            hol := fun U f => ⟨(u.hol U f).1.preimage hc,
              (u.hol U f).2.comp hd.differentiableOn (fun _ hz => hz)⟩
            fr := fun i z => u.fr i (T z)
            fr_hol := fun i => (u.fr_hol i).comp hd.differentiableOn (fun _ hz => hz)
            fr_ne := fun i z hz => u.fr_ne i (T z) hz
            fr_compat := fun i j z hz => u.fr_compat i j (T z) hz }, fun _ => rfl, hmem⟩

end GlobalTheory.KeyFam
end

section

open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

theorem _root_.GlobalTheory.T.eventually_posDef_hermForm_near_zero_matrix : ∀ {g : ℕ} (M₀ : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M₀ z z).re) → ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), (1 - C.map star * C).det ≠ 0 ∧ (1 - C * C.map star).det ≠ 0 ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) z z).re := by
  first | exact @GlobalTheory.PosOpen.posopen | exact GlobalTheory.PosOpen.posopen | (intros; apply GlobalTheory.PosOpen.posopen; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice : ∀ (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Function.Injective P → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  first | exact @GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate | exact GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate | (intros; apply GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate <;> assumption)
end
