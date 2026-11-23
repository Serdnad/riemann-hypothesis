module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigma
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntUnitOfMulLat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle167
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100

@[expose] public section

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

theorem finite_between (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (R : Submodule O A) (hR : R.FG)
    (a : O) (ha : a ≠ 0) : Finite {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Finite (O ⧸ Ideal.span {a}) := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k
  haveI : Module.Finite O R := Module.Finite.iff_fg.2 hR
  set J : Submodule O R := Ideal.span {a} • (⊤ : Submodule O R) with hJ
  haveI hQ : Finite (R ⧸ J) := Submodule.finite_quotient_smul (Ideal.span {a}) (N := ⊤) Module.Finite.fg_top
  have hJle : ∀ N : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N}, J ≤ N.1.comap R.subtype := by
    intro N x hx
    rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_smul]
    exact N.2.2 _ y.2
  let φ : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} → Set (R ⧸ J) := fun N =>
    ((N.1.comap R.subtype).map J.mkQ : Set (R ⧸ J))
  refine Finite.of_injective φ ?_
  intro N N' h
  have h1 : (N.1.comap R.subtype).map J.mkQ = (N'.1.comap R.subtype).map J.mkQ := SetLike.coe_injective h
  have h2 := congrArg (Submodule.comap J.mkQ) h1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.2 (hJle N),
    sup_eq_right.2 (hJle N')] at h2
  have h3 := congrArg (Submodule.map R.subtype) h2
  rw [Submodule.map_comap_eq, Submodule.map_comap_eq, Submodule.range_subtype,
    inf_eq_right.2 N.2.1, inf_eq_right.2 N'.2.1] at h3
  exact Subtype.ext h3

theorem isIntegral_sigma (K : UQ) (B : InvAlg K) (y : B.A) (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  apply GlobalTheory.UnitLemma.UnitBase.isIntegral_σ <;> assumption

theorem finite_rhoSet (K : UQ) (B : InvAlg K) (hsep : B.P.Separable) (a : K.O) (ha : K.Small a) (k : ℕ) :
    Finite {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} := by
  classical
  set R : Submodule K.O B.A := (integralClosure K.O B.A).toSubmodule with hR
  have hRfg : R.FG := by
    have := GlobalTheory.T.finite_integralClosure_of_separable_involution_algebra K B hsep
    have h2 := Module.Finite.fg_top (R := K.O) (M := integralClosure K.O B.A)
    have h3 := h2.map (integralClosure K.O B.A).val.toLinearMap
    convert h3 using 1
    ext x; simp [hR]
  have ha0 : a ^ (2 * k) ≠ 0 := pow_ne_zero _ ha.1
  have hfin := finite_between K.O B.A R hRfg (a ^ (2 * k)) ha0
  have hσα : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]
  have hαu : IsUnit (algebraMap K.O B.A a) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    intro h0
    exact ha.1 ((injective_iff_map_eq_zero (algebraMap K.O K.E)).1 (IsFractionRing.injective K.O K.E) a h0)
  set αu : B.Aˣ := hαu.unit with hαudef
  have hαeq : (αu : B.A) = algebraMap K.O B.A a := hαu.unit_spec
  have hmem : ∀ (u : B.A) (y : B.A), y ∈ mulLat K.O u R ↔ ∃ r ∈ R, u * r = y := by
    intro u y
    simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]

  have hσinv : ∀ t : B.T, B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) = ((t : B.Aˣ) : B.A) := by
    intro t
    have ht : ((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := t.2
    have h1 : B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A)
        = B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * (((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A)) := by rw [ht, mul_one]
      _ = ((t : B.Aˣ) : B.A) * (B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A)) := by ring
      _ = ((t : B.Aˣ) : B.A) := by rw [h1, mul_one]
  let φ : {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} →
      {N : Submodule K.O B.A // N ≤ R ∧ ∀ x ∈ R, a ^ (2 * k) • x ∈ N} := fun c =>
    ⟨mulLat K.O ((((Quotient.out c.1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) R, by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := (hmem _ _).1 hy
      exact c.2.mul hr, by
      intro x hx
      set t : B.T := Quotient.out c.1
      have h2 : IsIntegral K.O (((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) := by
        have := isIntegral_sigma K B _ c.2
        rwa [map_mul, map_pow, hσα, hσinv] at this
      refine (hmem _ _).2 ⟨((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k * x, h2.mul hx, ?_⟩
      rw [Algebra.smul_def, map_pow, pow_mul]
      have : (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((t : B.Aˣ) : B.A) = 1 := Units.inv_mul _
      linear_combination (algebraMap K.O B.A a ^ k * algebraMap K.O B.A a ^ k * x) * this⟩
  refine Finite.of_injective φ ?_
  rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
  have hN := congrArg Subtype.val h
  simp only [φ] at hN
  set t : B.T := Quotient.out c with htdef
  set t' : B.T := Quotient.out c' with ht'def
  have h1R : (1 : B.A) ∈ R := (integralClosure K.O B.A).one_mem

  have key : ∀ (s s' : B.T), mulLat K.O ((((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R =
      mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R →
      IsIntegral K.O ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) := by
    intro s s' hss
    have : (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k ∈
        mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R := by
      rw [← hss]; exact (hmem _ _).2 ⟨1, h1R, mul_one _⟩
    obtain ⟨r, hr, hr'⟩ := (hmem _ _).1 this
    have h1 : ((s' : B.Aˣ) : B.A) * (((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv _
    have h2 : algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) = 1 := by
      rw [← hαeq, ← Units.val_pow_eq_pow_val, Units.mul_inv]
    have : ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) = r := by
      rw [Units.val_mul]
      linear_combination -(((s' : B.Aˣ) : B.A) * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * hr' - r * algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * h1 - r * h2 + (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((s' : B.Aˣ) : B.A) * h2)
    rw [this]; exact hr
  have hA := key t t' hN
  have hB := key t' t hN.symm
  have hmemU : (t : B.Aˣ)⁻¹ * (t' : B.Aˣ) ∈ intUnits K.O B.A := by
    refine ⟨hA, ?_⟩
    have : ((t : B.Aˣ)⁻¹ * (t' : B.Aˣ))⁻¹ = ((t' : B.Aˣ)⁻¹ * (t : B.Aˣ)) := by
      rw [mul_inv_rev, inv_inv]
    rw [this]; exact hB
  have : c = c' := by
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hmemU
  subst this
  rfl

theorem rho_lower : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ k : ℕ, (k + 1) ^ (Fintype.card ι - S.card) ≤ B.rho (algebraMap K.O B.A a ^ k) := by
  intro K B ι _ e π S a hsep ha hF k
  classical
  have hfin := finite_rhoSet K B hsep a ha k
  obtain ⟨f, hf, hint⟩ := GlobalTheory.T.exists_injective_torus_classes_of_idempotent_decomposition K B ι e S a ha hF.1 k
  let g : ({i // i ∉ S} → Fin (k + 1)) → {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} :=
    fun n => ⟨f n, hint n⟩
  have hg : Function.Injective g := fun n n' h => hf (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective g hg
  unfold InvAlg.rho
  refine le_trans (le_of_eq ?_) h
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_coe]

end GlobalTheory.UnitLemma.Desc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l], ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 → ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  first | exact @GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | exact GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | (intros; apply GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty → K.eta (B.gramDet x) = 1 := by
  first | exact @GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | exact GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | (intros; apply GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.HullClasses

theorem exists_unit_mulLat_mem_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x →
    ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S :=
  fun K B hsep x _ _ c hc0 =>
    finite_mod_T_of K B (GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra K B hsep) (GlobalTheory.T.exists_finset_cosets_integral_norm_units K B hsep) (GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B) x c hc0

end GlobalTheory.HullClasses
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem torus_mod_intUnits_structure : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  intro K B hL a ha
  have hred : IsReduced B.A := GlobalTheory.T.isReduced_of_lieReg' K B hL
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  have hv : ∀ m : MaximalSpectrum B.A, ∃ v : (B.A ⧸ m.asIdeal)ˣ →* Multiplicative ℤ,
      Function.Surjective v ∧ ∀ x : (B.A ⧸ m.asIdeal)ˣ,
        IsIntegral K.O (x : B.A ⧸ m.asIdeal) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
    intro m
    haveI := m.isMaximal
    letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    haveI : FiniteDimensional K.E (B.A ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E m.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K.E m.asIdeal)
    exact GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg K (B.A ⧸ m.asIdeal)
  choose v hvs hvi using hv
  let w : MaximalSpectrum B.A → B.Aˣ →* Multiplicative ℤ := fun m =>
    (v m).comp (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal))
  have hw : ∀ m (x : B.Aˣ), IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (x : B.A)) ↔
      0 ≤ Multiplicative.toAdd (w m x) := fun m x =>
    hvi m (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) x)
  have hP : ∀ x : B.Aˣ, IsIntegral K.O (x : B.A) ↔ ∀ m, 0 ≤ Multiplicative.toAdd (w m x) := by
    intro x
    rw [GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue K B hred]
    exact forall_congr' fun m => hw m x
  let τ : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)
  have hτ : ∀ x, τ (τ x) = x := fun x => Units.ext (B.σ_σ _)
  have hT : ∀ t, t ∈ B.T ↔ t * τ t = 1 := by
    intro t
    rw [Units.ext_iff]
    rfl
  let s : MaximalSpectrum B.A → MaximalSpectrum B.A := fun m =>
    ⟨m.asIdeal.comap B.σ, Ideal.comap_isMaximal_of_surjective B.σ B.σ.surjective⟩
  have hs : ∀ m, s (s m) = m := by
    intro m
    ext y
    show B.σ (B.σ y) ∈ m.asIdeal ↔ y ∈ m.asIdeal
    rw [B.σ_σ]
  have hswap : ∀ m x, 0 ≤ Multiplicative.toAdd (w (s m) x) ↔ 0 ≤ Multiplicative.toAdd (w m (τ x)) := by
    intro m x
    rw [← hw, ← hw]
    exact GlobalTheory.T.isIntegral_residue_comap_involution_iff K B m x
  have hsupp : ∀ m (n : ℤ), ∃ y : B.Aˣ, w m y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ m → w j y = 1 := by
    intro m n
    obtain ⟨z, hz⟩ := hvs m (Multiplicative.ofAdd n)
    obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra K B hred m (z : B.A ⧸ m.asIdeal) z.ne_zero
    refine ⟨y, ?_, fun j hj => ?_⟩
    · have : Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) y = z := Units.ext hy1
      show v m _ = _
      rw [this, hz]
    · have : Units.map (Ideal.Quotient.mk j.asIdeal : B.A →* B.A ⧸ j.asIdeal) y = 1 := Units.ext (hy2 j hj)
      show v j _ = _
      rw [this, map_one]
  have hne : algebraMap K.O K.E a ≠ 0 := by
    intro h
    exact ha.1 (IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm))
  let α : B.Aˣ := Units.map (algebraMap K.E B.A : K.E →* B.A) (Units.mk0 _ hne)
  have hαv : (α : B.A) = algebraMap K.O B.A a := (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hτα : τ α = α := by
    apply Units.ext
    show B.σ (algebraMap K.E B.A (algebraMap K.O K.E a)) = algebraMap K.E B.A (algebraMap K.O K.E a)
    rw [B.σ_alg, ha.2.2]
  have hαpos : ∀ m, 0 < Multiplicative.toAdd (w m α) := by
    intro m
    by_contra hle
    push_neg at hle
    have h1 : 0 ≤ Multiplicative.toAdd (w m α⁻¹) := by
      rw [map_inv, toAdd_inv]
      linarith
    rw [← hw] at h1
    apply GlobalTheory.T.not_isIntegral_residue_inv_small_integer K B a ha m
    convert h1 using 1
    show _ = Ideal.Quotient.mk m.asIdeal (algebraMap K.E B.A (algebraMap K.O K.E a)⁻¹)
    rw [Ideal.Quotient.mk_algebraMap]
  obtain ⟨r, e, he1, he2, he3⟩ := GlobalTheory.T.exists_representatives_two_element_orbits_involution (MaximalSpectrum B.A) s hs
  refine ⟨r, ((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp B.T.subtype, fun j => (Multiplicative.toAdd (w (e j) α)).toNat,
    GlobalTheory.T.zValuationsAtIndices_torus_surjective B.Aˣ τ hτ B.T hT _ s w hswap hsupp r e he1 he2, fun t => ?_, fun j => ?_, fun t k => ?_⟩
  · rw [GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff B.Aˣ τ B.T hT _ s w hswap r e he3]
    show _ ↔ IsIntegral K.O ((t : B.Aˣ) : B.A) ∧ IsIntegral K.O (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A)
    rw [hP, hP]
    constructor
    · intro h
      exact ⟨fun m => (h m).ge, fun m => by rw [map_inv, toAdd_inv, h m, neg_zero]⟩
    · rintro ⟨ha1, ha2⟩ m
      have := ha2 m
      rw [map_inv, toAdd_inv] at this
      linarith [ha1 m]
  · exact Int.lt_toNat.mpr (hαpos (e j))
  · rw [← GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff B.Aˣ τ B.T hT _ s w hswap r e he3 α hτα hαpos, ← hP]
    congr 2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hαv]

end GlobalTheory.UnitLemma
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.truncatedIntegral_eq_vol_mul_orbitalIntegral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (y₀ : A.L), IsUnit y₀ → ∀ (D : AddSubgroup A.K), IsOpen (D : Set A.K) → IsCompact (D : Set A.K) → ∀ φ : A.L → ℂ, IsTest φ → (∀ b ∈ D, ∃ s s' : A.K, s ∈ A.OK ∧ s' ∈ A.OK ∧ s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse ((x : A.K) * A.NL y₀) * b ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y) → ∫ y, φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - (x : A.K) * A.NL y₀) ∂(m.μL x) = ((m.μK D).toReal : ℂ) * A.orbL m.ν φ y₀ := by
  first | exact @GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL | exact GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL | (intros; apply GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.etaK_eq_neg_one_of_not_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  first | exact @GlobalTheory.JR.NonNorm.etaK_eq_neg_one | exact GlobalTheory.JR.NonNorm.etaK_eq_neg_one | (intros; apply GlobalTheory.JR.NonNorm.etaK_eq_neg_one <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hermitianTraceDual_integers_eq_uniformizer_pow : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → IsField A.L → ∀ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) → (∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O) → ∀ a : A.Kˣ, ∃ e : ℤ, {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((ϖ ^ e : A.Kˣ) : A.K) * z} := by
  first | exact @GlobalTheory.JR.DualLattice.dual_eq_zpow | exact GlobalTheory.JR.DualLattice.dual_eq_zpow | (intros; apply GlobalTheory.JR.DualLattice.dual_eq_zpow <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.DualScaledIntegers

theorem exists_open_compact_annihilator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by
  intro F E _ _ _ _ U A ψ hψ c hc
  have := U.ultraF
  have := U.lcF
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hop, hcp, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  let D : AddSubgroup A.K :=
    { carrier := {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
      zero_mem' := by
        intro z _
        simp [Et.psiK]
      add_mem' := by
        intro a b ha hb z hz
        have h1 := ha z hz
        have h2 := hb z hz
        simp only [Et.psiK] at h1 h2 ⊢
        rw [mul_add, map_add (f := _), AddChar.map_add_eq_mul, h1, h2, one_mul]
      neg_mem' := by
        intro a ha z hz
        have h1 := ha z hz
        simp only [Et.psiK] at h1 ⊢
        rw [mul_neg, map_neg, AddChar.map_neg_eq_inv, h1, inv_one] }
  have hcs : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hM : IsCompact {z : A.K | c • z ∈ A.OK} := by
    have : {z : A.K | c • z ∈ A.OK} = (fun z : A.K => c⁻¹ • z) '' A.OK := by
      ext z
      constructor
      · intro hz
        exact ⟨c • z, hz, inv_smul_smul₀ hc z⟩
      · rintro ⟨w, hw, rfl⟩
        show c • c⁻¹ • w ∈ A.OK
        rwa [smul_inv_smul₀ hc]
    rw [this]
    exact hcp.image (continuous_const_smul _)
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hDo : IsOpen (D : Set A.K) := by
    refine AddSubgroup.isOpen_of_mem_nhds D (g := 0) ?_
    have h := hM.eventually_forall_of_forall_eventually (x₀ := (0 : A.K))
      (P := fun b z => A.psiK ψ (z * b) = 1) (fun y _ => by
        have hc2 : Continuous fun p : A.K × A.K => Algebra.trace F A.K (p.2 * p.1) :=
          htr.comp (continuous_snd.mul continuous_fst)
        have h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (((0 : A.K), y).2 * ((0 : A.K), y).1)) := by
          simpa using Metric.closedBall_mem_nhds (0 : F) one_pos
        filter_upwards [hc2.continuousAt.preimage_mem_nhds h0] with p hp
        exact hψ.1 _ (by simpa using hp))
    exact h
  refine ⟨D, rfl, hDo, ?_⟩
  have hU : {z : A.K | c • z ∈ A.OK} ∈ 𝓝 (0 : A.K) := by
    refine (hop.preimage hcs).mem_nhds ?_
    show c • (0 : A.K) ∈ A.OK
    rw [smul_zero, ← hR]
    exact R.zero_mem
  obtain ⟨M, N, hMU, -, -, -, hN, hMN, -⟩ :=
    (exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 _ hU
  refine hN.of_isClosed_subset (D.isClosed_of_isOpen hDo) fun b hb => ?_
  exact (hMN b).2 fun x hx => hb x (hMU hx)

end GlobalTheory.JR.DualScaledIntegers
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.annihilator_small : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by
  intro F E _ _ _ _ hU A ψ hψ U hUmem
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  have hfacts := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hnd : (Algebra.traceForm F A.K).Nondegenerate := hfacts.2.2.1
  have hOKopen : IsOpen A.OK := hfacts.2.2.2.2.2.2.2.2.2.1
  obtain ⟨R, hR⟩ := hfacts.2.2.2.2.2.2.2.2.2.2.2
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K)
    (Algebra.traceForm_isSymm F (S := A.K)) hnd
  obtain ⟨M, N, hMU, -, -, -, hNc, -, hM⟩ := hsmall U hUmem
  have hev : ∀ᶠ c in 𝓝 (0 : F), ∀ y ∈ (N : Set A.K), c • y ∈ A.OK := by
    refine hNc.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : ContinuousAt (fun p : F × A.K => p.1 • p.2) ((0 : F), y) := continuous_smul.continuousAt
    have : A.OK ∈ 𝓝 ((fun p : F × A.K => p.1 • p.2) ((0 : F), y)) := by
      simpa using hOKopen.mem_nhds h0
    exact hc this
  filter_upwards [nhdsWithin_le_nhds hev] with c hc b hb
  apply hMU
  rw [SetLike.mem_coe, hM]
  intro y hy
  have := hb y (hc y hy)
  simpa [Et.psiK, Algebra.traceForm_apply, mul_comm] using this
end
