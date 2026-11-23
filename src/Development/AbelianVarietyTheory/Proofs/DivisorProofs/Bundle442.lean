module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle084
public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle433
public import GroundTheory.Brauer.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle246
public import Formalism.LatticeTheta.LatticeThetaProofs.LatticeFourierSeries
public import Formalism.LatticeTheta.LatticeThetaProofs.Bundle003
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Module Polynomial TensorProduct

namespace GlobalTheory.CentSep

theorem aeval_mem_span_pow {K S : Type} [Field K] [Ring S] [Nontrivial S] [Algebra K S] (x : S)
    (hx : IsIntegral K x) (q : K[X]) :
    aeval x q ∈ Submodule.span K (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ)) := by
  have hm := minpoly.monic hx
  rw [← aeval_modByMonic_eq_self_of_root (p := q) (minpoly.aeval K x)]
  have hne : minpoly K x ≠ 1 := by
    intro h
    have := minpoly.natDegree_pos hx
    rw [h, natDegree_one] at this
    exact lt_irrefl _ this
  have hlt := natDegree_modByMonic_lt q hm hne
  rw [aeval_eq_sum_range' hlt]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨j, Finset.mem_range.mp hj⟩, rfl⟩)

theorem centralizer_toSubmodule {K S : Type} [Field K] [Ring S] [Algebra K S] (g : S) :
    Subalgebra.toSubmodule (Subalgebra.centralizer K ({g} : Set S)) =
      LinearMap.ker (LinearMap.mulLeft K g - LinearMap.mulRight K g) := by
  ext y
  simp [Subalgebra.mem_centralizer_iff, sub_eq_zero]

theorem natDegree_minpoly_le_baseChange {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  apply GlobalTheory.DescCoeff.natDegree_minpoly_le_one_tmul <;> assumption

theorem centralizer_eq_adjoin : ∀ (F B : Type) [Field F] [Ring B] [Algebra F B]
    [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ g : B, (minpoly F g).Separable →
      (minpoly F g).natDegree = n → Subalgebra.centralizer F {g} = Algebra.adjoin F {g} := by
  intro F B _ _ _ _ _ _ n hB g hsep hdeg
  classical
  obtain ⟨k, hk0, hkB, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F B
  have hkn : k = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkB.symm.trans hB)
  subst hkn
  set K := AlgebraicClosure F
  set x : K ⊗[F] B := (1 : K) ⊗ₜ[F] g with hx
  have hxi : IsIntegral K x := IsIntegral.of_finite K x

  have hxr : x = Algebra.TensorProduct.includeRight g := rfl
  have hdvd : minpoly K x ∣ (minpoly F g).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_baseChange K g hxi
  rw [hdeg] at hge
  have hle : (minpoly K x).natDegree ≤ k := by
    have hmap : (minpoly F g).map (algebraMap F K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero (IsIntegral.of_finite F g))
    calc (minpoly K x).natDegree ≤ ((minpoly F g).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap
      _ = k := by rw [natDegree_map, hdeg]
  have hxdeg : (minpoly K x).natDegree = k := le_antisymm hle hge

  set N := e x with hN
  have hmN : minpoly K N = minpoly K x := minpoly.algEquiv_eq e x
  have hchar : N.charpoly = minpoly K x := by
    have hd : minpoly K N ∣ N.charpoly := minpoly.dvd K N (Matrix.aeval_self_charpoly N)
    rw [hmN] at hd
    have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hd
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hxdeg])
    rw [this, (Matrix.charpoly_monic N).leadingCoeff, C_1, one_mul]
  have hNsep : N.charpoly.Separable := by
    rw [hchar]
    exact (hsep.map).of_dvd hdvd

  have hCK : Subalgebra.toSubmodule (Subalgebra.centralizer K ({x} : Set (K ⊗[F] B))) ≤
      Submodule.span K (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ)) := by
    intro y hy
    have hy' : x * y = y * x :=
      (Subalgebra.mem_centralizer_iff K).mp hy x (Set.mem_singleton x)
    have hcomm : Commute (e y) N := by
      change e y * e x = e x * e y
      rw [← map_mul, ← map_mul, hy']
    obtain ⟨q, hq⟩ := GlobalTheory.T.matrix_eq_aeval_of_commute_of_charpoly_separable k N (e y) hNsep hcomm
    have : y = aeval x q := by
      apply e.injective
      rw [hq, hN, ← aeval_algHom_apply]
    rw [this]
    exact aeval_mem_span_pow x hxi q
  have hfinK : finrank K (Subalgebra.toSubmodule (Subalgebra.centralizer K ({x} : Set (K ⊗[F] B))))
      ≤ k := by
    calc _ ≤ finrank K (Submodule.span K
            (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ))) :=
          Submodule.finrank_mono hCK
      _ ≤ Fintype.card (Fin (minpoly K x).natDegree) := finrank_range_le_card _
      _ = k := by rw [Fintype.card_fin, hxdeg]

  have hbc := (GlobalTheory.BadCount.finrank_iInf_ker_baseChange F K B (K ⊗[F] B) Unit
    (TensorProduct.mk F K B 1) (TensorProduct.isBaseChange F B K)
    (fun _ => LinearMap.mulLeft F g - LinearMap.mulRight F g)
    (fun _ => LinearMap.mulLeft K x - LinearMap.mulRight K x)
    (fun _ v => by
      simp [hx, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub])).1
  rw [_root_.iInf_const, _root_.iInf_const] at hbc
  rw [← centralizer_toSubmodule, ← centralizer_toSubmodule] at hbc

  have hadj : Algebra.adjoin F ({g} : Set B) ≤ Subalgebra.centralizer F {g} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      ((Subalgebra.mem_centralizer_iff F).mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]))
  have hspan : Submodule.span F (Set.range fun j : Fin (minpoly F g).natDegree => g ^ (j : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin F ({g} : Set B)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton g)) _
  have hfinS : k ≤ finrank F (Subalgebra.toSubmodule (Algebra.adjoin F ({g} : Set B))) := by
    calc k = Fintype.card (Fin (minpoly F g).natDegree) := by rw [Fintype.card_fin, hdeg]
      _ = finrank F (Submodule.span F
            (Set.range fun j : Fin (minpoly F g).natDegree => g ^ (j : ℕ))) :=
          (finrank_span_eq_card (linearIndependent_pow g)).symm
      _ ≤ _ := Submodule.finrank_mono hspan
  have heq := Submodule.eq_of_le_of_finrank_le
    (Subalgebra.toSubmodule.monotone hadj) (by rw [← hbc]; exact hfinK.trans hfinS)
  exact (Subalgebra.toSubmodule_injective heq).symm

end GlobalTheory.CentSep
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FactorAndSection

theorem exists_factor {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) : ∃ χ : A →+* R, (algebraMap R K).comp χ = ψ ∧ χ.comp φ = RingHom.id R := by
  apply GlobalTheory.RetractionLiftSection.exists_retraction <;> assumption

theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) [IsFinite p]
    (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ Z) (hy : y ≫ p = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) :
    ∃ x : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ Z.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  obtain ⟨χ, h1, h2⟩ := exists_factor (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  have h1' : CommRingCat.ofHom χ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h1
  have h2' : φ ≫ CommRingCat.ofHom χ = 𝟙 _ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, h1', hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h2', Spec.map_id]

end GlobalTheory.FactorAndSection
end
end

section

open Real

namespace GlobalTheory

theorem zetaTerm_tsum_le_two (i : ℕ) (hi : 2 ≤ i) :
    ∑' n : ℕ, 1/((n:ℝ)+1)^i ≤ 2 := by
  apply GlobalTheory.EtaValueBound.zeta_le_two <;> assumption

theorem volumeConstant_le (r : ℕ) (hr : 2 ≤ r) :
    √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by
  have hprod : ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ ∏ _i ∈ Finset.Icc 2 r, (2:ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _; exact tsum_nonneg (fun n => by positivity)
    · intro i hi; exact zetaTerm_tsum_le_two i (Finset.mem_Icc.mp hi).1
  rw [Finset.prod_const, Nat.card_Icc] at hprod
  have hexp : r + 1 - 2 ≤ r*(r-1)/2 := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : k + 2 + 1 - 2 = k + 1 := by omega
    have h' : k + 2 - 1 = k + 1 := by omega
    rw [this, h']
    nlinarith
  have hpow : (2:ℝ)^(r+1-2) ≤ 2^(r*(r-1)/2) := pow_le_pow_right₀ (by norm_num) hexp
  have hpi : (1:ℝ) ≤ (2*π)^(r-1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hsq : 0 ≤ √(r:ℝ) := Real.sqrt_nonneg _
  have h2p : (0:ℝ) ≤ 2^(r*(r-1)/2) := by positivity
  calc √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i)
      ≤ √r * 2^(r*(r-1)/2) := mul_le_mul_of_nonneg_left (hprod.trans hpow) hsq
    _ ≤ √r * (2^(r*(r-1)/2) * (2*π)^(r-1)) := by
        apply mul_le_mul_of_nonneg_left _ hsq
        nlinarith
    _ = 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by ring

end GlobalTheory
end

section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_etale_factorization_of_isIndEtale : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (P : Ideal R) [P.IsPrime]
    (φ : Localization.AtPrime P →+* O), φ.comp (algebraMap R _) = algebraMap R O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
      (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g := by
  first | exact @GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime | exact GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime | (intros; apply GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime <;> assumption)
end

section

noncomputable section
open NumberField nonZeroDivisors MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR
open GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

theorem latOf_discrete [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) :
    DiscreteTopology (latOf N) := GlobalTheory.T.discreteTopology_fractionalIdealRealLatticeImage F N

theorem latOf_isZLattice [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0)
    [DiscreteTopology (latOf N)] : IsZLattice ℝ (latOf N) := GlobalTheory.T.isZLattice_fractionalIdealRealLatticeImage F N hN

theorem covolume_latOf [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0)
    [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)] :
    ZLattice.covolume (latOf N) = covol N := GlobalTheory.T.covolume_fractionalIdealRealLatticeImage F N hN

theorem dual_latOf [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual F N hN

theorem fourier_lipschitzOneVariableKernel (k : ℕ) (hk : 2 ≤ k) (he : Even k) (w : ℂ) (hw : w.im ≠ 0) (x : ℝ) :
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) :=
  GlobalTheory.T.fourier_lipschitzOneVariableKernel_eq k hk he w hw x

theorem Phi_cont_decay (k : ℕ) (hk : 2 ≤ k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧
      ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel F k hk z hz

theorem summable_lhsTerm [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) (hM : M ≠ 0) (k : ℕ)
    (hk : 2 ≤ k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Summable (fun a : (M : Set F) => lhsTerm k z a) := GlobalTheory.T.summable_lipschitzLatticeNormPowSummand F M hM k hk z hz

theorem fourier_prod_coord (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.fourier_real_eq]
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul]

theorem remb_injective [IsTotallyReal F] : Function.Injective (remb F) := by
  intro a b h
  have hne : Nonempty (F →+* ℝ) := by
    rw [← Fintype.card_pos_iff, card_realEmb]
    exact Module.finrank_pos
  have h1 := congrArg (fun v : RSp F => v (Classical.choice hne)) h
  simp only [remb_apply] at h1
  exact (Classical.choice hne).injective h1

theorem Phi_remb (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) :
    Phi k z (remb F ν) =
      if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 := by
  unfold Phi
  by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
  · rw [if_pos hc, Finset.prod_congr rfl fun τ _ => by rw [remb_apply, phi1, if_pos (hc τ)],
      Finset.prod_mul_distrib, ← Complex.exp_sum, rhsTerm, Finset.abs_prod, ← Finset.prod_pow, Complex.ofReal_prod]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  · rw [if_neg hc]
    push Not at hc
    obtain ⟨τ, hτ⟩ := hc
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [remb_apply, phi1, if_neg (not_lt.2 hτ)])

theorem fourier_Phi (k : ℕ) (hk : 2 ≤ k) (he : Even k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0)
    (a : F) : 𝓕 (Phi k z) (remb F a) =
      (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ) *
        lhsTerm k z (-a) := by
  rw [show Phi k z = fun ξ : RSp F => ∏ τ, phi1 k (z τ) (ξ τ) from rfl, fourier_prod_coord]
  simp only [remb_apply]
  have h := fun τ : F →+* ℝ => fourier_lipschitzOneVariableKernel k hk he (z τ) (hz τ) (τ a)
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, lhsTerm, Finset.prod_zpow]
  simp [map_neg, sub_eq_add_neg]

theorem lipschitz : Lipschitz := by
  intro F _ _ _ M hM k hk he z hz
  haveI : DiscreteTopology (latOf M) := latOf_discrete M
  haveI : IsZLattice ℝ (latOf M) := latOf_isZLattice M hM
  set L := Formalism.H.dual (latOf M) with hL
  obtain ⟨h1, h2⟩ := Formalism.H.dualIsLattice (RSp F) (latOf M)
  haveI : DiscreteTopology L := h1
  haveI : IsZLattice ℝ L := h2
  have hdd : Formalism.H.dual L = latOf M := Formalism.H.dualDual (RSp F) (latOf M)
  have hcov : ZLattice.covolume L = (covol M)⁻¹ := by
    rw [Formalism.H.covolumeDual (RSp F) (latOf M), covolume_latOf M hM]
  have hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ FractionalIdeal.dual ℤ ℚ M, remb F ν = x := by
    intro x; rw [hL, dual_latOf M hM]; exact mem_latOf _ x
  have hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ M, remb F a = x := by
    intro x; rw [hdd]; exact mem_latOf _ x
  obtain ⟨hcont, hdec⟩ := Phi_cont_decay k hk z hz
  obtain ⟨hint, hsumx, hGc, hGper⟩ := Formalism.H.poisson_periodization (RSp F) L (Phi k z) hcont
    ((Module.finrank ℝ (RSp F) : ℝ) + 1) (by linarith) (hdec _)
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hD := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Phi k z ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 (Phi k z) μ :=
    fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L (Phi k z) hint D hD μ μ.2

  let eM : (M : Set F) ≃ Formalism.H.dual L := Equiv.ofBijective
    (fun a => ⟨remb F a, (hDmem _).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (remb_injective (congrArg Subtype.val h)), fun μ => by
      obtain ⟨a, ha, h⟩ := (hDmem μ).1 μ.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  let eD : (FractionalIdeal.dual ℤ ℚ M : Set F) ≃ L := Equiv.ofBijective
    (fun a => ⟨remb F a, (hLmem _).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (remb_injective (congrArg Subtype.val h)), fun μ => by
      obtain ⟨a, ha, h⟩ := (hLmem μ).1 μ.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  set cst : ℂ := (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ)
  have hsL := summable_lhsTerm M hM k hk z hz
  let eN : (M : Set F) ≃ (M : Set F) :=
    ⟨fun a => ⟨-a, (M : Submodule (𝓞 F) F).neg_mem a.2⟩, fun a => ⟨-a, (M : Submodule (𝓞 F) F).neg_mem a.2⟩, fun a => by simp, fun a => by simp⟩
  have hsLn : Summable (fun a : (M : Set F) => lhsTerm k z (-(a : F))) :=
    (eN.summable_iff (f := fun a : (M : Set F) => lhsTerm k z a)).2 hsL
  have hFM : ∀ a : (M : Set F), 𝓕 (Phi k z) (eM a) = cst * lhsTerm k z (-(a : F)) :=
    fun a => fourier_Phi k hk he z hz a
  have hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Phi k z ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) := by
    simp only [hcoef]
    rw [← eM.summable_iff]
    exact (hsLn.mul_left cst).congr fun a => (hFM a).symm
  have H4 := Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Phi k z ((l : RSp F) + x))
    hGc hGper D hD hsumc 0
  simp only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    add_zero] at H4
  rw [← eM.hasSum_iff] at H4
  have H4' : HasSum (fun a : (M : Set F) => (covol M : ℂ) * cst * lhsTerm k z (-(a : F)))
      (∑' l : L, Phi k z (l : RSp F)) := by
    refine H4.congr_fun fun a => ?_
    simp only [Function.comp_apply, hFM, hcov, Complex.ofReal_inv, inv_inv]
    ring
  have hs0 : Summable (fun l : L => Phi k z (l : RSp F)) := by
    simpa using hsumx 0
  set g : F → ℂ := fun ν =>
    if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 with hg
  have hind : (FractionalIdeal.dual ℤ ℚ M : Set F).indicator g = (dualCone M z).indicator (rhsTerm k z) := by
    funext ν
    by_cases hν : ν ∈ (FractionalIdeal.dual ℤ ℚ M : Set F)
    · have hν' : ν ∈ traceDual M := (mem_traceDual_iff hM ν).2 hν
      by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
      · rw [Set.indicator_of_mem hν, Set.indicator_of_mem (show ν ∈ dualCone M z from ⟨hν', hc⟩), hg]
        simp [hc]
      · rw [Set.indicator_of_mem hν, Set.indicator_of_notMem (show ν ∉ dualCone M z from fun h => hc h.2), hg]
        simp [hc]
    · have hν' : ν ∉ dualCone M z := fun h => hν ((mem_traceDual_iff hM ν).1 h.1)
      rw [Set.indicator_of_notMem hν, Set.indicator_of_notMem hν']
  have hPg : ∀ ν : (FractionalIdeal.dual ℤ ℚ M : Set F), Phi k z (eD ν) = g ν := fun ν => Phi_remb k z ν
  have hsD : Summable (fun ν : (FractionalIdeal.dual ℤ ℚ M : Set F) => g ν) := by
    rw [← eD.summable_iff] at hs0
    exact hs0.congr fun ν => hPg ν
  have hsR : Summable (fun ν : dualCone M z => rhsTerm k z ν) := by
    have h3 := (summable_subtype_iff_indicator (s := (FractionalIdeal.dual ℤ ℚ M : Set F)) (f := g)).1 hsD
    rw [hind] at h3
    exact (summable_subtype_iff_indicator (s := dualCone M z) (f := rhsTerm k z)).2 h3
  have hR : ∑' l : L, Phi k z (l : RSp F) = ∑' ν : dualCone M z, rhsTerm k z ν := by
    rw [← eD.tsum_eq, tsum_subtype (dualCone M z) (rhsTerm k z), ← hind, ← tsum_subtype]
    exact tsum_congr fun ν => hPg ν
  have hLn : ∑' a : (M : Set F), lhsTerm k z (-(a : F)) = ∑' a : (M : Set F), lhsTerm k z a :=
    eN.tsum_eq (fun a : (M : Set F) => lhsTerm k z a)
  have hmain := H4'.tsum_eq
  rw [tsum_mul_left, hLn, hR] at hmain
  refine ⟨hsL, hsR, ?_⟩
  rw [← hmain]
  have hc0 : (covol M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (covol_pos hM).ne'
  have hf0 : ((k - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [lipConst, cst, card_realEmb, div_pow, pow_mul]
  field_simp

end GlobalTheory.LipschitzTR
end
end

section

open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
  ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k →
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z) ∧
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z c)
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z c) := by
  first | exact @GlobalTheory.EisNonConst.nonconst_terms | exact GlobalTheory.EisNonConst.nonconst_terms | (intros; apply GlobalTheory.EisNonConst.nonconst_terms <;> assumption)
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.exists_jet_extension_square_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C), f₁.deg = f₂.deg → (∀ a, n a ∈ T.J) → (∀ a b, n a * n b = 0) → (∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) → ∃ χ : K.jet k ⟶ T, χ.deg = f₁.deg ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧ ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), χ.φ x = f₁.φ (x.fst : Hol (K.W k)) + ∑ a, f₁.φ (x.snd a : Hol (K.W k)) * n a := by
  first | exact @GlobalTheory.AnPer.Charts.exists_jet_factor | exact GlobalTheory.AnPer.Charts.exists_jet_factor | (intros; apply GlobalTheory.AnPer.Charts.exists_jet_factor <;> assumption)
end
