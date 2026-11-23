module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle002
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
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.gVanish : UpperTheory.V.Z.Sym.Loc.GVanish := by
  intro O K _ _ _ _ _ Δ τ hL j hj χ z hz hne
  haveI := hL.frac
  obtain ⟨s, u, t, hn, ht⟩ := exists_of_gOrb_ne (O := O) hj hne
  have hu : algebraMap O K ↑u⁻¹ * algebraMap O K ↑u = 1 := by
    rw [← map_mul]
    simp
  rcases hz with h | h
  · rw [h] at hn ht
    simp [trace, QuadraticAlgebra.norm] at hn ht
    have h2 : (s : K) ^ 2 = algebraMap O K ↑u⁻¹ := by
      calc (s : K) ^ 2 = algebraMap O K ↑u⁻¹ * (algebraMap O K ↑u * s ^ 2) := by
            rw [← mul_assoc, hu, one_mul]
        _ = _ := by rw [← hn, mul_one]
    have hi : IsIntegral O (s : K) :=
      IsIntegral.of_pow two_pos (h2 ▸ isIntegral_algebraMap)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨y * t, by rw [map_mul, hy, ht]⟩
  · rw [h] at hn ht
    simp [trace, QuadraticAlgebra.norm] at hn ht
    have e : algebraMap O K t = algebraMap O K ↑u * s := by
      apply mul_left_cancel₀ s.ne_zero
      linear_combination hn - ht
    have hs : (s : K) = algebraMap O K (↑u⁻¹ * t) := by
      rw [map_mul, e, ← mul_assoc, hu, one_mul]
    refine ⟨↑u⁻¹ * t * t - 2, ?_⟩
    rw [map_sub, map_mul, ← hs, map_ofNat]
    linear_combination -ht
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem map_two_add_smul_eq (O K : Type) [CommRing O] [Field K] [Algebra O K] (π : O)
    (X : Matrix (Fin 2) (Fin 2) O) :
    (1 + 1 + π • X).map (algebraMap O K) = 1 + 1 + algebraMap O K π • X.map (algebraMap O K) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply] <;> rw [Algebra.smul_def]

theorem UpperTheory.V.Z.Sym.Loc.stabG : UpperTheory.V.Z.Sym.Loc.StabG := by
  classical
  intro O K _ _ _ _ _ Δ τ L hτ j hj y
  haveI := L.frac
  set H := Subgroup.comap (jU j) (Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj y⁻¹)) (ZK O K)) with hH
  have memH : ∀ z, z ∈ H ↔ y⁻¹ * jU j z * y ∈ ZK O K := by
    intro z
    simp [hH]
  have Q : ∀ z : (Etau K τ)ˣ, trace (quo z) = trace (z : Etau K τ) ^ 2 * norm (↑z⁻¹ : Etau K τ) - 2 ∧
      norm (quo z) = 1 ∧ norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by
    intro z
    have hzw : (z : Etau K τ) * ↑z⁻¹ = 1 := z.mul_inv
    have hn : norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by rw [← map_mul, hzw, map_one]
    have h1 : quo z = algebraMap K (Etau K τ) (trace (↑z⁻¹ : Etau K τ)) * z - 1 := by
      rw [quo, star_eq (↑z⁻¹ : Etau K τ), mul_sub, hzw, mul_comm]
    have h2 : trace (z : Etau K τ) = norm (z : Etau K τ) * trace (↑z⁻¹ : Etau K τ) := by
      have e : algebraMap K (Etau K τ) (norm (z : Etau K τ)) * ↑z⁻¹ = star (z : Etau K τ) := by
        rw [algebraMap_norm_eq_mul_star, mul_comm (z : Etau K τ), mul_assoc, hzw, mul_one]
      have := congrArg trace e
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, trace_star] at this
      exact this.symm
    refine ⟨?_, ?_, hn⟩
    · rw [h1, map_sub, ← Algebra.smul_def, map_smul, smul_eq_mul, trace_one]
      linear_combination (-(trace (z : Etau K τ)) * trace (↑z⁻¹ : Etau K τ)) * hn +
        (-(trace (z : Etau K τ)) * norm (↑z⁻¹ : Etau K τ)) * h2
    · rw [quo, map_mul, QuadraticAlgebra.norm_star, hn]
  have P1 : ∀ z ∈ H, IsIntegral O (quo z) := by
    intro z hz
    rw [memH] at hz
    obtain ⟨c, k, hck⟩ := mem_ZK.mp hz
    have hM := congrArg Units.val hck
    rw [Units.val_mul, Units.val_mul, Units.val_mul] at hM
    have e0 : ((jU j z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = j ↑z := rfl
    rw [e0] at hM
    have htr : trace (z : Etau K τ) = c * algebraMap O K (Matrix.trace (k : Matrix (Fin 2) (Fin 2) O)) := by
      rw [← j_trace j hj, ← Matrix.trace_units_conj' y (j z), hM]
      simp [Matrix.trace_fin_two, Matrix.GeneralLinearGroup.map_apply] <;> ring
    have hdet : norm (z : Etau K τ) = c ^ 2 * algebraMap O K (Matrix.det (k : Matrix (Fin 2) (Fin 2) O)) := by
      rw [← j_det j hj, ← Matrix.det_units_conj' y (j z), hM]
      simp [Matrix.det_fin_two, Matrix.GeneralLinearGroup.map_apply] <;> ring
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mp k.isUnit
    have hunit : algebraMap O K ↑u⁻¹ * algebraMap O K ↑u = 1 := by
      rw [← map_mul]
      simp
    have hn' := (Q z).2.2
    rw [hdet, ← hu] at hn'
    refine isIntegral_of_trace_norm (x := quo z) ((k : Matrix (Fin 2) (Fin 2) O).trace ^ 2 * ↑u⁻¹ - 2) 1 ?_ ?_
    · rw [(Q z).1, htr]
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap O K (k : Matrix (Fin 2) (Fin 2) O).trace) ^ 2 *
        (-((c : K) ^ 2 * norm (↑z⁻¹ : Etau K τ)) * hunit + algebraMap O K ↑u⁻¹ * hn')
    · rw [(Q z).2.1, map_one]
  refine ⟨fun z hz => ⟨P1 z hz, P1 _ (H.inv_mem hz)⟩, ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨s, hs⟩ := intE_fg L hτ
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (s.biUnion fun g => Finset.univ.image fun p : Fin 2 × Fin 2 =>
      (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j g * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) p.1 p.2)
  have hint : ∀ x ∈ Submodule.span O (s : Set (Etau K τ)), ∀ a b,
      IsLocalization.IsInteger O ((d : O) • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) a b) := by
    intro x hx a b
    induction hx using Submodule.span_induction with
    | mem g hg =>
      exact hd _ (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩⟩)
    | zero => simpa using IsLocalization.isInteger_zero
    | add x x' _ _ h1 h2 =>
      rw [map_add (f := _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, smul_add]
      exact IsLocalization.isInteger_add h1 h2
    | smul o x _ h =>
      rw [← algebraMap_smul K o x, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
        algebraMap_smul, smul_comm]
      exact IsLocalization.isInteger_smul h
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hd0 : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hm : π * (d : O) ≠ 0 := mul_ne_zero hπ0 hd0
  refine cint_relIndex_ne_zero L hτ hm H ?_
  intro z _ r hr hq
  have hrs : r ∈ Submodule.span O (s : Set (Etau K τ)) := by
    rw [hs, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
    exact hr
  let X : Matrix (Fin 2) (Fin 2) O := Matrix.of fun a b => (hint r hrs a b).choose
  have hX : ∀ a b, algebraMap O K (X a b) = (d : O) • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j r * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) a b :=
    fun a b => (hint r hrs a b).choose_spec
  have hzw : (z : Etau K τ) * ↑z⁻¹ = 1 := z.mul_inv
  have hn : norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by rw [← map_mul, hzw, map_one]
  have hN0 : norm (z : Etau K τ) ≠ 0 := left_ne_zero_of_mul_eq_one hn
  have hsw : star (z : Etau K τ) * star (↑z⁻¹ : Etau K τ) = 1 := by
    rw [← star_mul, z.inv_mul, star_one]
  have hkey : algebraMap K (Etau K τ) (trace (z : Etau K τ)) * z =
      algebraMap K (Etau K τ) (norm (z : Etau K τ)) * (1 + quo z) := by
    rw [algebraMap_trace_eq_add_star, algebraMap_norm_eq_mul_star, quo]
    linear_combination (-((z : Etau K τ) * z)) * hsw
  have h2 : IsUnit (2 : O) := L.two
  have hm' : algebraMap O K (π * d) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hm
  have htr0 : trace (z : Etau K τ) ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hkey
    have hu : algebraMap K (Etau K τ) (norm (z : Etau K τ)) * algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ)) = 1 := by
      rw [← map_mul, hn, map_one]
    have h1q : (1 : Etau K τ) + quo z = 0 := by
      calc (1 : Etau K τ) + quo z = algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ)) *
            (algebraMap K (Etau K τ) (norm (z : Etau K τ)) * (1 + quo z)) := by
            rw [← mul_assoc, mul_comm (algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ))), hu, one_mul]
        _ = 0 := by rw [← hkey, mul_zero]
    rw [hq] at h1q
    have e : algebraMap O K (π * d) • r = algebraMap K (Etau K τ) (-2) := by
      rw [map_neg, map_ofNat]
      linear_combination h1q
    have hr' : r = algebraMap K (Etau K τ) (-2 / algebraMap O K (π * d)) := by
      calc r = (algebraMap O K (π * d))⁻¹ • (algebraMap O K (π * d) • r) := by
            rw [smul_smul, inv_mul_cancel₀ hm', one_smul]
        _ = _ := by rw [e, Algebra.smul_def, ← map_mul, div_eq_inv_mul]
    rw [hr'] at hr
    have hI : IsIntegral O (-2 / algebraMap O K (π * d)) :=
      (isIntegral_algebraMap_iff ).mp hr
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI
    have h4 : (-2 : O) = π * d * o := by
      apply IsFractionRing.injective O K
      rw [map_mul (algebraMap O K) (π * d) o, ho, mul_div_assoc', mul_comm, mul_div_assoc, div_self hm',
        mul_one, map_neg, map_ofNat]
    exact hπ.not_isUnit (isUnit_of_mul_isUnit_left (x := π) (y := (d : O) * o)
      (by rw [← mul_assoc, ← h4]; exact h2.neg))
  have ha : norm (z : Etau K τ) / trace (z : Etau K τ) ≠ 0 := div_ne_zero hN0 htr0
  have hz_eq : (z : Etau K τ) = algebraMap K (Etau K τ) (norm (z : Etau K τ) / trace (z : Etau K τ)) *
      (1 + (1 + algebraMap O K (π * d) • r)) := by
    rw [← hq]
    calc (z : Etau K τ) = algebraMap K (Etau K τ) (trace (z : Etau K τ))⁻¹ *
          (algebraMap K (Etau K τ) (trace (z : Etau K τ)) * z) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ htr0, map_one, one_mul]
      _ = _ := by rw [hkey, ← mul_assoc, ← map_mul, div_eq_mul_inv, mul_comm (trace (z : Etau K τ))⁻¹]
  have hYY : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have φmul : ∀ (b : K) (x : Etau K τ), ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (algebraMap K (Etau K τ) b * x) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro b x
    rw [map_mul, j.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have φadd : ∀ x x' : Etau K τ, ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (x + x') * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) + ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x' * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro x x'
    rw [map_add (f := _), Matrix.mul_add, Matrix.add_mul]
  have φone : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j 1 * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [map_one, Matrix.mul_one, hYY]
  have φsmul : ∀ (b : K) (x : Etau K τ), ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (b • x) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro b x
    rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hXm : X.map (algebraMap O K) = algebraMap O K d • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j r * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    ext a b
    rw [Matrix.map_apply, hX, Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]
  let km : Matrix (Fin 2) (Fin 2) O := 1 + 1 + π • X
  have hkm : km.map (algebraMap O K) = 1 + 1 + algebraMap O K π • X.map (algebraMap O K) := by
    exact map_two_add_smul_eq O K π X
  have hdet : km.det = 4 + π * (2 * X 0 0 + 2 * X 1 1 + π * (X 0 0 * X 1 1 - X 0 1 * X 1 0)) := by
    simp [km, Matrix.det_fin_two, Matrix.one_apply]
    ring
  have hdu : IsUnit km.det := by
    by_contra hnu
    have hπm : π ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
    have hdm : km.det ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have h4m : (4 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hdm (Ideal.mul_mem_right (2 * X 0 0 + 2 * X 1 1 + π * (X 0 0 * X 1 1 - X 0 1 * X 1 0)) _ hπm)
      rwa [hdet, add_sub_cancel_right] at this
    apply mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h4m)
    rw [show (4 : O) = 2 * 2 by norm_num]
    exact h2.mul h2
  let kk : GL (Fin 2) O := ((Matrix.isUnit_iff_isUnit_det _).mpr hdu).unit
  have hA : ((Matrix.GeneralLinearGroup.map (algebraMap O K) kk : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      km.map (algebraMap O K) := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl
  rw [memH]
  apply mem_ZK.mpr
  refine ⟨Units.mk0 _ ha, kk, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  change ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [Matrix.GeneralLinearGroup.coe_scalar, hA, hkm, hXm, Units.val_mk0, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]
  conv_lhs => rw [hz_eq]
  rw [φmul, φadd, φone, φadd, φone, φsmul, map_mul, smul_smul, add_assoc]
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem isIntegral_entry_zero_zero_of_mem_kd {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K} {t : DX Δ}
    (ht : t ∈ KD Δ O) :
    IsIntegral O (((t : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) := by
  rw [KD, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at ht
  obtain ⟨N, hN⟩ := ht
  rw [← hN, Matrix.GeneralLinearGroup.map_apply]
  exact (N.1 0 0).2

private theorem inv_mul_scal_entry_zero_zero_eq {K : Type} [Field K] {Δ : K} {z z' : Kˣ} {s s' : DX Δ}
    (hs : IsScal z s) (hs' : IsScal z' s') :
    (((s'⁻¹ * s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0
      = algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) := by
  have e : s = s' * (s'⁻¹ * s) := by group
  have hmat : Glob.mt s = Glob.mt s' * Glob.mt (s'⁻¹ * s) := by
    conv_lhs => rw [e]
    rfl
  unfold IsScal at hs hs'
  rw [hs, hs'] at hmat
  have e2 := congrFun (congrFun hmat 0) 0
  simp only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.diagonal_apply_eq] at e2
  show Glob.mt (s'⁻¹ * s) 0 0 = _
  set M := Glob.mt (s'⁻¹ * s) 0 0
  have h1 : algebraMap K (Lsq K Δ) (z' : K)⁻¹ * algebraMap K (Lsq K Δ) (z' : K) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ z'.ne_zero, map_one]
  rw [map_mul]
  linear_combination (-(algebraMap K (Lsq K Δ) (z' : K)⁻¹)) * e2 + (-M) * h1

theorem UpperTheory.V.Z.Sym.Loc.fzdLaw : UpperTheory.V.Z.Sym.Loc.FzdLaw := by
  intro O K _ _ _ _ _ Δ hL χ hχ
  haveI := hL.frac
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [fZD, dite_eq_right]
    rintro ⟨z, s, hs, hk⟩
    apply hg
    have hsZ : s ∈ ZD Δ := by
      rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨z, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
      have h := congrFun (congrFun hs i) j
      rw [show (((s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j
        = Glob.mt s i j from rfl, h]
      simp [Matrix.scalar_apply]
    have e : g = s * (s⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hsZ hk
  · intro z s k hs hk
    have hex : ∃ z s', IsScal z s' ∧ s'⁻¹ * (s * k) ∈ KD Δ O :=
      ⟨z, s, hs, by rwa [inv_mul_cancel_left]⟩
    rw [fZD, dite_eq_left hex]
    obtain ⟨hs', hk'⟩ := hex.choose_spec.choose_spec
    set z' := hex.choose
    set s' := hex.choose_spec.choose
    have ht : s'⁻¹ * s ∈ KD Δ O := by
      have e : s'⁻¹ * s = (s'⁻¹ * (s * k)) * k⁻¹ := by group
      rw [e]
      exact mul_mem hk' (inv_mem hk)
    have ht' : s⁻¹ * s' ∈ KD Δ O := by
      have e : s⁻¹ * s' = (s'⁻¹ * s)⁻¹ := by group
      rw [e]
      exact inv_mem ht
    have i1 := isIntegral_entry_zero_zero_of_mem_kd ht
    rw [inv_mul_scal_entry_zero_zero_eq hs hs'] at i1
    have i2 := isIntegral_entry_zero_zero_of_mem_kd ht'
    rw [inv_mul_scal_entry_zero_zero_eq hs' hs] at i2
    let f : K →ₐ[O] Lsq K Δ := IsScalarTower.toAlgHom O K (Lsq K Δ)
    have hf : Function.Injective f := (algebraMap K (Lsq K Δ)).injective
    rw [show algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) = f ((z' : K)⁻¹ * z) from rfl,
      isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)] at i1
    rw [show algebraMap K (Lsq K Δ) ((z : K)⁻¹ * z') = f ((z : K)⁻¹ * z') from rfl,
      isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)] at i2
    obtain ⟨a, ha⟩ := i1
    obtain ⟨b, hb⟩ := i2
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one]
      field_simp
    have hu := hχ ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
    have hmap : (Units.map (algebraMap O K : O →* K)) ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
        = z'⁻¹ * z := Units.ext (by simp [ha])
    rw [hmap, map_mul, map_inv, inv_mul_eq_one] at hu
    rw [hu]
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem two_ne {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have h := L.two.map (algebraMap O K)
  rw [map_ofNat] at h
  exact h.ne_zero

theorem UpperTheory.V.Z.Sym.Loc.datFormM : UpperTheory.V.Z.Sym.Loc.DatFormM := by
  intro O K _ _ _ _ _ Δ τ hL c u hu2 hnu ν hν s hs
  have h2 : (2 : K) ≠ 0 := two_ne hL
  have ofE_sm : ∀ (r : K) (y : Etau K τ),
      ofE Δ (algebraMap K (Etau K τ) r * y) = (algebraMap K (Lsq K Δ) r) • ofE Δ y := by
    intro r y
    ext <;> simp [ofE]
  have ofE_mul : ∀ x y : Etau K τ, ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
    intro x y
    ext <;> simp [ofE] <;> ring
  have sig_ofE : ∀ y : Etau K τ, sigL (ofE Δ y) = ofE Δ y := by
    intro y
    ext <;> simp [sigL, ofE]
  have star_ofE : ∀ y : Etau K τ, star (ofE Δ y) = ofE Δ (star y) := by
    intro y
    ext <;> simp [ofE]
  have sig_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), sigL (a • y) = star a • sigL y := by
    intro a y
    ext <;> simp [sigL]
  have star_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), star (a • y) = a • star y := by
    intro a y
    ext <;> simp <;> ring
  have hν' : ν * star ν = algebraMap K (Lsq K Δ) (-1) := by
    rw [← algebraMap_norm_eq_mul_star, hν]
  have hus : u * star u = algebraMap K (Etau K τ) 1 := by
    rw [← algebraMap_norm_eq_mul_star, hnu]
  refine ⟨?_, ?_⟩
  · rw [sig_sm, sig_ofE, smul_mul_smul_comm, hν', ← ofE_mul, ← ofE_sm, ← sq, hu2]
    congr 1
    rw [map_neg, map_one]
    ring
  · intro m hm
    have hd : ν • ofE Δ u * star (sigL (ν • ofE Δ u)) = -1 := by
      rw [sig_sm, sig_ofE, star_sm, star_ofE, smul_mul_smul_comm, hν', ← ofE_mul, ← ofE_sm, hus]
      ext <;> simp [ofE]
    have hsig : sigL m = -m := by
      rw [hm.m_sig, mul_assoc, hd, mul_neg_one]
    have hst : star m = -m := by
      have h := hm.m_star
      rw [hsig, star_neg] at h
      exact neg_eq_iff_eq_neg.mp h
    have e1 : m.re.re = 0 := by
      have h := congrArg (fun y : EL Δ τ => y.re.re) hsig
      simp [sigL] at h
      have h' : 2 * m.re.re = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left h2
    have e2 : m.im.re = 0 := by
      have h := congrArg (fun y : EL Δ τ => y.im.re) hsig
      simp [sigL] at h
      have h' : 2 * m.im.re = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left h2
    have e3 : 2 * m.re.im = -τ * m.im.im := by
      have h := congrArg (fun y : EL Δ τ => y.re.im) hst
      simp at h
      linear_combination h
    have hq : m.im.im ≠ 0 := by
      intro hq0
      have e4 : m.re.im = 0 := by
        have h' : 2 * m.re.im = 0 := by rw [e3, hq0, mul_zero]
        exact (mul_eq_zero.mp h').resolve_left h2
      have hm0 : m = 0 := by
        ext
        · exact e1
        · exact e4
        · exact e2
        · exact hq0
      exact not_isUnit_zero (hm0 ▸ hm.m_unit)
    refine ⟨Units.mk0 (m.im.im / (2 * s)) (div_ne_zero hq (mul_ne_zero h2 hs)), ?_⟩
    ext
    · simp [ofE, e1]
    · simp [ofE]
      field_simp
      linear_combination e3
    · simp [ofE, e2]
    · simp [ofE]
      field_simp
      norm_num
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.gOdd : UpperTheory.V.Z.Sym.Loc.GOdd := by
  intro O K _ _ _ _ _ Δ τ L j χ z _ hj h
  by_contra h'
  obtain ⟨s, u, t, h1, -⟩ := exists_of_gOrb_ne hj h'
  exact h ⟨u, s, s.ne_zero, h1⟩
end
