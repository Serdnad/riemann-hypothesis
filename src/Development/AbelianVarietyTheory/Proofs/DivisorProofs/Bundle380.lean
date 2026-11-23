module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle311
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle310
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle225
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle322
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle313
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle103
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle107
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.Analysis.Normed.Group.Ultra
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

section

open Matrix Polynomial

namespace GlobalTheory.SimSep

theorem mulVec_aeval_eq_zero_iff {R : Type} [Field R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (v : Fin m → R) (hv : ∀ u : Fin m → R, ∃ p : R[X], u = aeval A p *ᵥ v) (p : R[X]) :
    aeval A p *ᵥ v = 0 ↔ A.charpoly ∣ p := by
  constructor
  · intro h
    have hA : aeval A p = 0 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
      obtain ⟨q, rfl⟩ := hv u
      simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, Matrix.mulVec_mulVec]
      rw [← map_mul, mul_comm, map_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    have hmin : minpoly R A ∣ p := minpoly.dvd R A hA
    have hmon : (minpoly R A).Monic := minpoly.monic (Matrix.isIntegral A)

    set d := (minpoly R A).natDegree with hd
    let ψ : (Fin d → R) →ₗ[R] (Fin m → R) :=
      { toFun := fun c => aeval A (((degreeLTEquiv R d).symm c : degreeLT R d) : R[X]) *ᵥ v
        map_add' := fun a b => by simp [Matrix.add_mulVec]
        map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
    have hψ : Function.Surjective ψ := by
      intro u
      obtain ⟨q, rfl⟩ := hv u
      have hq : q %ₘ minpoly R A ∈ degreeLT R d := by
        rw [mem_degreeLT]
        exact lt_of_lt_of_le (degree_modByMonic_lt q hmon) (degree_le_natDegree)
      refine ⟨degreeLTEquiv R d ⟨_, hq⟩, ?_⟩
      simp [ψ, Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval R A)]
    have hle : m ≤ d := by
      have := LinearMap.finrank_range_le ψ
      rw [LinearMap.range_eq_top.mpr hψ, finrank_top] at this
      simpa using this
    have heq : minpoly R A = A.charpoly := by
      refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic A)
        (Matrix.minpoly_dvd_charpoly A) ?_).symm
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      exact hle
    rwa [heq] at hmin
  · rintro ⟨q, rfl⟩
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul, Matrix.zero_mulVec]

end GlobalTheory.SimSep

namespace GlobalTheory.SimSep

theorem conj_of_charpoly_eq_of_separable : ∀ (R : Type) [Field R] (m : ℕ)
    (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable →
    ∃ P : GL (Fin m) R, N * P.val = P.val * U := by
  intro R _ m N U hc hs
  obtain ⟨v, hv⟩ := GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly m N hs
  obtain ⟨w, hw⟩ := GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly m U (hc ▸ hs)
  let φ : R[X] →ₗ[R] (Fin m → R) :=
    { toFun := fun p => aeval N p *ᵥ v
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  let ψ : R[X] →ₗ[R] (Fin m → R) :=
    { toFun := fun p => aeval U p *ᵥ w
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  have hφ : Function.Surjective φ := fun u => let ⟨p, hp⟩ := hv u; ⟨p, hp.symm⟩
  have hψ : Function.Surjective ψ := fun u => let ⟨p, hp⟩ := hw u; ⟨p, hp.symm⟩
  have hker : LinearMap.ker ψ = LinearMap.ker φ := by
    ext p
    simp only [LinearMap.mem_ker]
    show aeval U p *ᵥ w = 0 ↔ aeval N p *ᵥ v = 0
    rw [mulVec_aeval_eq_zero_iff U w hw, mulVec_aeval_eq_zero_iff N v hv, hc]
  let T : (Fin m → R) ≃ₗ[R] (Fin m → R) :=
    ((ψ.quotKerEquivOfSurjective hψ).symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
      (φ.quotKerEquivOfSurjective hφ)
  have hT : ∀ p, T (ψ p) = φ p := by
    intro p
    have h1 : (ψ.quotKerEquivOfSurjective hψ).symm (ψ p) = Submodule.Quotient.mk p := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [T, LinearEquiv.trans_apply, h1, Submodule.quotEquivOfEq_mk]
    rfl
  have hcomm : ∀ x, T (U *ᵥ x) = N *ᵥ T x := by
    intro x
    obtain ⟨p, rfl⟩ := hψ x
    have e1 : U *ᵥ ψ p = ψ (X * p) := by
      show U *ᵥ (aeval U p *ᵥ w) = aeval U (X * p) *ᵥ w
      rw [map_mul, aeval_X, Matrix.mulVec_mulVec]
    have e2 : N *ᵥ φ p = φ (X * p) := by
      show N *ᵥ (aeval N p *ᵥ v) = aeval N (X * p) *ᵥ v
      rw [map_mul, aeval_X, Matrix.mulVec_mulVec]
    rw [e1, hT, hT, e2]
  have hl : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  have hr : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  let P : GL (Fin m) R :=
    ⟨LinearMap.toMatrix' T.toLinearMap, LinearMap.toMatrix' T.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp, hl, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hr, LinearMap.toMatrix'_id]⟩
  refine ⟨P, Matrix.toLin'.injective (LinearMap.ext fun x => ?_)⟩
  simp only [P, Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
    Matrix.toLin'_apply, LinearEquiv.coe_coe]
  exact (hcomm x).symm

end GlobalTheory.SimSep
end

section

open IsLocalRing



namespace GlobalTheory.LocNormDVR

theorem artinian (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D]
    [Module.Finite S D] : IsArtinianRing (TensorProduct S D L) := by
  haveI : IsArtinianRing (TensorProduct S L D) := IsArtinianRing.of_finite L _
  exact RingEquiv.isArtinianRing (Algebra.TensorProduct.comm S L D).toRingEquiv

theorem main : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∃ _ : IsDomain (Localization.AtPrime Q), IsDiscreteValuationRing (Localization.AtPrime Q) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he _ _ Q _
  obtain ⟨φ⟩ := hD
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he
    · exact h
  haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite
  haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv
  haveI : FaithfulSMul S D := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 : algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) a =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) b := by
      rw [← φ.commutes, ← φ.commutes, hab]
    set pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne') with hpb
    have hd : 0 < pb.dim := by
      rw [hpb, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C _]; exact he0
    have h0 : pb.basis ⟨0, hd⟩ = 1 := by rw [PowerBasis.coe_basis]; simp
    have key : ∀ s : S, pb.basis.repr (algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) s)
        ⟨0, hd⟩ = s := by
      intro s
      rw [Algebra.algebraMap_eq_smul_one, ← h0, map_smul, Module.Basis.repr_self]
      simp
    rw [← key a, ← key b, h1]
  haveI : Module.Finite D (integralClosure D (TensorProduct S D L)) := GlobalTheory.T.normalisation_dvr_tensor_separable_finite S K L D
  haveI : IsArtinianRing (TensorProduct S D L) := artinian S L D
  haveI : IsReduced (TensorProduct S D L) := GlobalTheory.T.kummer_uniformiser_adjoinRoot_tensor_isReduced S K L π e D ⟨φ⟩ hπ he
  obtain ⟨hdom, hic⟩ := GlobalTheory.T.localization_integralClosure_artinian_reduced_domain D (TensorProduct S D L) Q
  refine ⟨hdom, ?_⟩
  haveI : IsNoetherianRing (integralClosure D (TensorProduct S D L)) :=
    IsNoetherianRing.of_finite D _
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  have htf : ∀ a : D, a ≠ 0 → ∀ x : integralClosure D (TensorProduct S D L), a • x = 0 → x = 0 := by
    intro a ha x hax
    have hinj : Function.Injective (LinearMap.rTensor L (LinearMap.mulLeft S a)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun y z h => (mul_right_injective₀ ha) h)
    have hsmul : ∀ z : TensorProduct S D L,
        a • z = LinearMap.rTensor L (LinearMap.mulLeft S a) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul y l => simp [TensorProduct.smul_tmul']
      | add u v hu hv => rw [smul_add, map_add (f := _), hu, hv]
    have h1 : a • (x : TensorProduct S D L) = 0 := congrArg Subtype.val hax
    rw [hsmul, ← map_zero (LinearMap.rTensor L (LinearMap.mulLeft S a))] at h1
    exact Subtype.ext (hinj h1)
  have hQu : Q.comap (algebraMap D (integralClosure D (TensorProduct S D L))) = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := D) Q)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hϖQ : algebraMap D (integralClosure D (TensorProduct S D L)) ϖ ∈ Q := by
    rw [← Ideal.mem_comap, hQu]; exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hnf : ¬ IsField (Localization.AtPrime Q) := by
    intro hF
    have hmax : maximalIdeal (Localization.AtPrime Q) = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).1 hF
    have hmem : algebraMap _ (Localization.AtPrime Q)
        (algebraMap D (integralClosure D (TensorProduct S D L)) ϖ) ∈
        maximalIdeal (Localization.AtPrime Q) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hϖQ
    rw [hmax, Ideal.mem_bot, IsLocalization.map_eq_zero_iff Q.primeCompl] at hmem
    obtain ⟨⟨t, ht⟩, hts⟩ := hmem
    have ht0 : t = 0 := htf ϖ hϖ.ne_zero t (by rw [Algebra.smul_def, mul_comm]; exact hts)
    exact ht (ht0 ▸ Q.zero_mem)
  refine ((IsDiscreteValuationRing.TFAE (Localization.AtPrime Q) hnf).out 1 4).2
    (⟨hic, ?_⟩ : IsIntegrallyClosed (Localization.AtPrime Q) ∧
      ∃! P : Ideal (Localization.AtPrime Q), P ≠ ⊥ ∧ P.IsPrime)
  refine ⟨maximalIdeal _, ⟨⟨?_, inferInstance⟩, ?_⟩⟩
  · intro h; exact hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  · rintro P ⟨hP0, hP⟩
    by_contra hne
    have hlt : P < maximalIdeal _ := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP.ne_top) hne
    have hbl : (⊥ : Ideal (Localization.AtPrime Q)) < P := bot_lt_iff_ne_bot.2 hP0
    have h1 : (⊥ : Ideal (Localization.AtPrime Q)).comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) <
        P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) := (IsLocalization.orderEmbedding Q.primeCompl (Localization.AtPrime Q)).strictMono hbl
    have h2 : P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) <
        (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) :=
      (IsLocalization.orderEmbedding Q.primeCompl (Localization.AtPrime Q)).strictMono hlt
    have hc : (maximalIdeal (Localization.AtPrime Q)).comap
        (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.under_maximalIdeal
    rw [hc] at h2
    haveI : ((⊥ : Ideal (Localization.AtPrime Q)).comap
        (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).IsPrime := Ideal.comap_isPrime _ _
    haveI : (P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).IsPrime := Ideal.comap_isPrime _ _
    have k1 := Ideal.IsIntegral.comap_lt_comap (R := D) h1
    have k2 := Ideal.IsIntegral.comap_lt_comap (R := D) h2
    change _ < Q.comap (algebraMap D (integralClosure D (TensorProduct S D L))) at k2
    rw [hQu] at k2
    have hp1 : ((P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).comap
        (algebraMap D (integralClosure D (TensorProduct S D L)))).IsPrime := Ideal.comap_isPrime _ _
    have hmx := hp1.isMaximal (ne_bot_of_gt k1)
    exact (ne_of_lt k2) (IsLocalRing.eq_maximalIdeal hmx)

end GlobalTheory.LocNormDVR
end

section

open scoped TensorProduct Classical

namespace GlobalTheory.LocalApprox

theorem isUnit_of_isUnit_one_tmul (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (b : E) (hb : IsUnit ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b)) : IsUnit b := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ ℚ_[ℓ]).injective
  have h1 : Function.Injective (LinearMap.mulLeft ℚ b) := by
    intro x y hxy
    apply hinj
    have h := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) hxy
    simp only [LinearMap.mulLeft_apply, map_mul] at h
    exact hb.mul_left_cancel h
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.1 h1 1
  have hw' : b * w = 1 := hw
  exact ⟨⟨b, w, hw', by rw [mul_comm]; exact hw'⟩, rfl⟩

theorem exists_rat_mul_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℚ_[ℓ]ˣ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ r : ℤ_[ℓ]ˣ, (u : ℚ_[ℓ]) = algebraMap ℚ ℚ_[ℓ] c * ((r : ℤ_[ℓ]) : ℚ_[ℓ]) := by
  have hu : 0 < ‖(u : ℚ_[ℓ])‖ := norm_pos_iff.2 u.ne_zero
  obtain ⟨c, hc⟩ := Padic.rat_dense ℓ (u : ℚ_[ℓ]) hu
  have hn : ‖(c : ℚ_[ℓ])‖ = ‖(u : ℚ_[ℓ])‖ := by
    have h : (c : ℚ_[ℓ]) = (u : ℚ_[ℓ]) + -((u : ℚ_[ℓ]) - c) := by ring
    have hlt : ‖-((u : ℚ_[ℓ]) - c)‖ < ‖(u : ℚ_[ℓ])‖ := by rwa [norm_neg]
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
  have hc0 : (c : ℚ_[ℓ]) ≠ 0 := norm_pos_iff.1 (hn ▸ hu)
  have h1 : ‖(u : ℚ_[ℓ]) / c‖ = 1 := by rw [norm_div, hn, div_self hu.ne']
  refine ⟨c, fun h => hc0 (by simp [h]), PadicInt.mkUnits h1, ?_⟩
  rw [PadicInt.mkUnits_eq, eq_ratCast, mul_div_cancel₀ _ hc0]

theorem main : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E →ₐ[ℚ] E) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : E) (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), IsUnit a →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] E) (u : ℚ_[ℓ]) *
      ((z : ℚ_[ℓ] ⊗[ℚ] E) * Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ (z : ℚ_[ℓ] ⊗[ℚ] E)) →
    ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y) := by
  intro E _ _ _ τ ℓ _ a u z ha hau
  set S := ℚ_[ℓ] ⊗[ℚ] E
  set τℓ : S →ₐ[ℚ_[ℓ]] S := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ with hτℓ
  set ι : E →ₐ[ℚ] S := Algebra.TensorProduct.includeRight with hι
  have hιapp : ∀ w : E, ι w = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w := fun w => rfl
  have hτι : ∀ w : E, τℓ (ι w) = ι (τ w) := fun w => by
    show Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] τ w
    rw [Algebra.TensorProduct.map_tmul]; rfl
  have hιq : ∀ q : ℚ, ι (algebraMap ℚ E q) = algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] q) := fun q => by
    rw [ι.commutes, IsScalarTower.algebraMap_apply ℚ ℚ_[ℓ] S]
  have hint : ∀ t : ℤ_[ℓ], IsIntegral ℤ_[ℓ] (algebraMap ℚ_[ℓ] S (t : ℚ_[ℓ])) := fun t => by
    rw [show (t : ℚ_[ℓ]) = algebraMap ℤ_[ℓ] ℚ_[ℓ] t from rfl, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have hτint : ∀ w : S, IsIntegral ℤ_[ℓ] w → IsIntegral ℤ_[ℓ] (τℓ w) := fun w hw =>
    hw.map (τℓ.restrictScalars ℤ_[ℓ])
  obtain ⟨c, hc0, r, hur⟩ := exists_rat_mul_unit ℓ u
  obtain ⟨b, s, hs, hb⟩ := GlobalTheory.T.exists_approx_unit_padic_tensor E ℓ z
  obtain ⟨ρ, hρ, hρint⟩ := GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic ℓ S s hs
  set v : S := 1 + (ℓ : S) * s with hv
  have hvint : IsIntegral ℤ_[ℓ] v := by
    refine isIntegral_one.add (IsIntegral.mul ?_ hs)
    rw [show (ℓ : S) = algebraMap ℤ_[ℓ] S ℓ by simp]
    exact isIntegral_algebraMap
  have hbU : IsUnit b := isUnit_of_isUnit_one_tmul E ℓ b (by
    rw [hb]; exact z.isUnit.mul ⟨⟨_, ρ, hρ, by rw [mul_comm]; exact hρ⟩, rfl⟩)
  set m : E := algebraMap ℚ E c * (b * τ b) with hm
  have hmU : IsUnit m := ((isUnit_iff_ne_zero.2 hc0).map (algebraMap ℚ E)).mul (hbU.mul (hbU.map τ))
  obtain ⟨mi, hmi⟩ : ∃ mi : E, m * mi = 1 := ⟨_, hmU.mul_val_inv⟩
  obtain ⟨ai, hai⟩ : ∃ ai : E, a * ai = 1 := ⟨_, ha.mul_val_inv⟩

  set R : S := algebraMap ℚ_[ℓ] S ((r : ℤ_[ℓ]) : ℚ_[ℓ]) with hR
  set Ri : S := algebraMap ℚ_[ℓ] S (((r⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) with hRi
  set C : S := algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] c) with hC
  set U : S := algebraMap ℚ_[ℓ] S (u : ℚ_[ℓ]) with hU
  have hUCR : U = C * R := by rw [hU, hur, map_mul]
  have hRRi : R * Ri = 1 := by
    rw [hR, hRi, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      PadicInt.coe_one, map_one]
  have h1 : ι a = U * ((z : S) * τℓ z) := hau
  have h2 : ι m = C * (((z : S) * v) * (τℓ z * τℓ v)) := by
    rw [hm, map_mul, map_mul, hιq, hτι b |>.symm, hιapp b, hb, map_mul]
  have h4 : v * ρ = 1 := hρ
  have h5 : τℓ v * τℓ ρ = 1 := by rw [← map_mul, h4, map_one]
  have h3 : ι m * ι mi = 1 := by rw [← map_mul, hmi, map_one]
  have h3' : ι a * ι ai = 1 := by rw [← map_mul, hai, map_one]
  have hx : ι (a * mi) = R * ρ * τℓ ρ := by
    have hK : R * ρ * τℓ ρ * ι m = ι a := by
      rw [h2, h1, hUCR]
      linear_combination (C * R * (z : S) * τℓ z * τℓ v * τℓ ρ) * h4 + (C * R * (z : S) * τℓ z) * h5
    rw [map_mul]
    linear_combination (-ι mi) * hK + (R * ρ * τℓ ρ) * h3
  have hy : ι (m * ai) = Ri * v * τℓ v := by
    have hK : Ri * v * τℓ v * ι a = ι m := by
      rw [h2, h1, hUCR]
      linear_combination (C * (z : S) * v * τℓ z * τℓ v) * hRRi
    rw [map_mul]
    linear_combination (-ι ai) * hK + (Ri * v * τℓ v) * h3'
  obtain ⟨d1, hd1, hx1⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (a * mi) (by
    rw [← hιapp, hx]
    exact ((hint _).mul hρint).mul (hτint _ hρint))
  obtain ⟨d2, hd2, hy2⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (m * ai) (by
    rw [← hιapp, hy]
    exact ((hint _).mul hvint).mul (hτint _ hvint))
  refine ⟨c, b, a * mi, m * ai, hc0, hbU, ?_, ?_, d1 * d2, ?_, ?_, ?_⟩
  · linear_combination (-a) * hmi
  · linear_combination (-m) * hai
  · intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).1 h with h | h
    · exact hd1 h
    · exact hd2 h
  · have : ((d1 * d2 : ℕ) : E) * (a * mi) = (d2 : E) * ((d1 : E) * (a * mi)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d2 : ℤ))).mul hx1
  · have : ((d1 * d2 : ℕ) : E) * (m * ai) = (d1 : E) * ((d2 : E) * (m * ai)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d1 : ℤ))).mul hy2

end GlobalTheory.LocalApprox
end

section

open IsLocalRing

namespace GlobalTheory.AnnRegSeq

theorem free_of_free_quotient_map (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) (hf : f ∈ maximalIdeal R)
    (reg : IsSMulRegular A f)
    (hfree : Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) :
    Module.Free R A := by
  set I : Ideal R := Ideal.span {f}
  have hsub : I • (⊤ : Submodule R A) = (I.map (algebraMap R A)).restrictScalars R :=
    Ideal.smul_top_eq_map I
  let e0 : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R] (A ⧸ I.map (algebraMap R A)) :=
    (Submodule.quotEquivOfEq _ _ hsub).trans
      (Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R A)))
  let e : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R ⧸ I] (A ⧸ I.map (algebraMap R A)) :=
    { e0.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show e0 (Ideal.Quotient.mk I c • Submodule.Quotient.mk x) = Ideal.Quotient.mk I c • e0 (Submodule.Quotient.mk x)
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul] }
  haveI := hfree
  haveI : Module.Free (R ⧸ I) (A ⧸ I • (⊤ : Submodule R A)) := Module.Free.of_equiv e.symm
  exact free_of_free_quotient hf reg

end GlobalTheory.AnnRegSeq
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_admissible_isUnit_det_local_involution : ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.LocalLift.exists_admissible_isUnit_det | exact GlobalTheory.LocalLift.exists_admissible_isUnit_det | (intros; apply GlobalTheory.LocalLift.exists_admissible_isUnit_det <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.lintegral_sublevel_tail_le_of_finite : ∀ (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞) (x : Y → ℝ), Measurable x → ∫⁻ y, g y ∂μ < ⊤ → Measurable g → ∀ ε : ℝ≥0∞, 0 < ε → ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  first | exact @GlobalTheory.lintegral_sublevel_tail_le | exact GlobalTheory.lintegral_sublevel_tail_le | (intros; apply GlobalTheory.lintegral_sublevel_tail_le <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic : ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 → y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  first | exact @GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime | exact GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime | (intros; apply GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime <;> assumption)
end
