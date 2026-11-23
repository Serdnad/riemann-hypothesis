module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle106
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle104
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

open Polynomial

namespace GlobalTheory.JR.Et.Idem

theorem isIntegral_of_forall {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

theorem isIntegral_single {O : Type} [CommRing O] {ι : Type} [Finite ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (i : ι) (z : R i) (hz : IsIntegral O z) :
    IsIntegral O (Pi.single i z : ∀ j, R j) := by
  refine isIntegral_of_forall _ fun j => ?_
  by_cases h : j = i
  · subst h; simpa using hz
  · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero

theorem single_mul_single_of_ne {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroClass (R i)] {i j : ι}
    (h : i ≠ j) (a : R i) (b : R j) : (Pi.single i a : ∀ k, R k) * Pi.single j b = 0 := by
  funext k
  rw [Pi.mul_apply, Pi.zero_apply]
  by_cases hk : k = i
  · subst hk; rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hk, zero_mul]

theorem single_one_mul {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroOneClass (R i)] (i : ι)
    (x : ∀ j, R j) : (Pi.single i 1 : ∀ j, R j) * x = Pi.single i (x i) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [Pi.single_eq_of_ne hk]

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] [IsUltrametricDist F] (A : Et F E),
    (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
      IsIntegral (NormedField.valuation (K := F)).integer y ∨
        IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) →
    ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧
      (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧
      ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by
  intro F E _ _ _ _ _ _ A hval
  classical
  haveI : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  let ψ : A.K ≃ₐ[F] (∀ I : MaximalSpectrum A.K, A.K ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A.K).restrictScalars F
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (MaximalSpectrum A.K)
  let f : Fin m → A.K := fun i => ψ.symm (Pi.single (e.symm i) 1)
  have hf : ∀ i, ψ (f i) = Pi.single (e.symm i) 1 := fun i => ψ.apply_symm_apply _
  haveI : Fintype (MaximalSpectrum A.K) := Fintype.ofFinite _
  have hOK : ∀ x : (∀ I : MaximalSpectrum A.K, A.K ⧸ I.asIdeal),
      IsIntegral (NormedField.valuation (K := F)).integer x → ψ.symm x ∈ A.OK := fun x hx =>
    (mem_OK_iff_isIntegral A _).2 (hx.map (ψ.symm.restrictScalars (NormedField.valuation (K := F)).integer))
  refine ⟨m, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply ψ.injective
    rw [map_mul, hf, ← Pi.single_mul, mul_one]
  · intro i j hij
    apply ψ.injective
    rw [map_mul, hf, hf, map_zero]
    exact single_mul_single_of_ne (e.symm.injective.ne hij) _ _
  · apply ψ.injective

    rw [map_sum, map_one]
    simp_rw [hf]
    rw [Equiv.sum_comp e.symm (fun I => (Pi.single I 1 : ∀ J : MaximalSpectrum A.K, A.K ⧸ J.asIdeal))]
    exact Finset.univ_sum_single 1
  · intro i c hc h
    rw [mem_OK_iff_isIntegral] at h
    haveI := (e.symm i).isMaximal
    letI : Field (A.K ⧸ (e.symm i).asIdeal) := Ideal.Quotient.field _
    have h1 := h.map (((Pi.evalAlgHom F (fun J : MaximalSpectrum A.K => A.K ⧸ J.asIdeal) (e.symm i)).comp
      ψ.toAlgHom).restrictScalars (NormedField.valuation (K := F)).integer)
    have h2 : (((Pi.evalAlgHom F (fun J : MaximalSpectrum A.K => A.K ⧸ J.asIdeal) (e.symm i)).comp
      ψ.toAlgHom).restrictScalars (NormedField.valuation (K := F)).integer) (algebraMap F A.K c * f i) =
        algebraMap F (A.K ⧸ (e.symm i).asIdeal) c := by
      change ψ (algebraMap F A.K c * f i) (e.symm i) = _
      rw [map_mul, AlgEquiv.commutes, hf, Pi.mul_apply, Pi.single_eq_same, mul_one, Pi.algebraMap_apply]
    rw [h2] at h1
    have h3 := (isIntegral_algebraMap_iff ).1 h1
    have h4 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h3
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h4
    have h5 : ‖c‖ ≤ 1 := by exact_mod_cast h4
    linarith
  · intro i y hy
    haveI := (e.symm i).isMaximal
    letI : Field (A.K ⧸ (e.symm i).asIdeal) := Ideal.Quotient.field _
    haveI : FiniteDimensional F (A.K ⧸ (e.symm i).asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F (e.symm i).asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hfy : ψ (f i * y) = Pi.single (e.symm i) (ψ y (e.symm i)) := by
      rw [map_mul, hf, single_one_mul]
    have hfy' : f i * y = ψ.symm (Pi.single (e.symm i) (ψ y (e.symm i))) := by
      rw [← hfy, ψ.symm_apply_apply]
    by_cases hz : ψ y (e.symm i) = 0
    · exact absurd (by rw [hfy', hz, Pi.single_zero, map_zero]; exact (mem_OK_iff_isIntegral A 0).2 isIntegral_zero) hy
    rcases hval (A.K ⧸ (e.symm i).asIdeal) (ψ y (e.symm i)) hz with h | h
    · exact absurd (by rw [hfy']; exact hOK _ (isIntegral_single _ _ h)) hy
    · refine ⟨ψ.symm (Pi.single (e.symm i) (ψ y (e.symm i))⁻¹), hOK _ (isIntegral_single _ _ h), ?_⟩
      apply ψ.injective
      rw [map_mul, ψ.apply_symm_apply, hfy, hf, ← Pi.single_mul, inv_mul_cancel₀ hz]

end GlobalTheory.JR.Et.Idem
end
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.weierstrass_division_eisensteinPow_integral : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  first | exact @GlobalTheory.weierstrassDiv_E_pow | exact GlobalTheory.weierstrassDiv_E_pow | (intros; apply GlobalTheory.weierstrassDiv_E_pow <;> assumption)
end

section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem _root_.GlobalTheory.T.exists_variable_pow_smul_eq_zero_of_finiteLength : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (M : Type) [AddCommGroup M] [Module (A O K) M], IsFiniteLength (A O K) M → ∃ n : ℕ, ∀ x : M, (uIn (A O K)) ^ n • x = 0 := by
  first | exact @GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero | exact GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero | (intros; apply GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero <;> assumption)
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.gammaCondition_shift_and_divVariable_mem : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ a : ℤ, CondC g (sh a N) ∧ ∀ x ∈ sh a N, nab g x ∈ sh a N := by
  first | exact @GlobalTheory.PhiGam.condC_sh_and_nab_mem | exact GlobalTheory.PhiGam.condC_sh_and_nab_mem | (intros; apply GlobalTheory.PhiGam.condC_sh_and_nab_mem <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

private theorem coe_powerSeries_smul_eq_smul {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] (a : k⟦X⟧) (x : V) : (a : k⸨X⸩) • x = a • x := by
  rw [← algebraMap_smul (k⸨X⸩) a x, LaurentSeries.coe_algebraMap]

private theorem powerSeries_smul_mem_of_mem {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] (N : Submodule k⟦X⟧ V) {x : V} (hx : x ∈ N)
    (a : k⟦X⟧) : (a : k⸨X⸩) • x ∈ N := by
  rw [coe_powerSeries_smul_eq_smul]; exact N.smul_mem a hx

private theorem mem_of_gmult_eq_zero_of_sub_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U]
    (T : Module.End k U) (P Q : Submodule k U) (x : k) (s : Set U) (hs : s.Finite)
    (hP : P ≤ Submodule.span k s ⊔ Q) (h0 : gmult T P Q x = 0) (y : U) (hy : y ∈ P)
    (hT : (T - algebraMap k (Module.End k U) x) y ∈ Q) : y ∈ Q := by
  set E : Submodule k U := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hE
  have hyE : y ∈ E := by
    refine Submodule.mem_inf.mpr ⟨hy, Submodule.mem_iSup_of_mem 1 ?_⟩
    rw [Submodule.mem_comap, pow_one]; exact hT
  let f : E →ₗ[k] U ⧸ Q := Q.mkQ ∘ₗ E.subtype
  let W : Submodule k (U ⧸ Q) := (Submodule.span k s).map Q.mkQ
  have hWfg : W.FG := (Submodule.fg_span hs).map _
  have : Module.Finite k W := Module.Finite.iff_fg.mpr hWfg
  have hrange : ∀ z : E, f z ∈ W := by
    intro z
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp (hP z.2.1)
    refine ⟨a, ha, ?_⟩
    show Q.mkQ a = Q.mkQ (z : U)
    have hc0 : Q.mkQ c = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hc
    rw [← hac, map_add (f := _), hc0, add_zero]
  have hker : LinearMap.ker f = Q.submoduleOf E := by
    ext z
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap]
  have hker' : LinearMap.ker (f.codRestrict W hrange) = Q.submoduleOf E := by
    rw [LinearMap.ker_codRestrict, hker]
  let g := (Q.submoduleOf E).liftQ (f.codRestrict W hrange) hker'.ge
  have hg : LinearMap.ker g = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ hker'.le
  have : IsNoetherian k W := IsNoetherian.iff_fg.mpr inferInstance
  have : Module.Finite k (E ⧸ Q.submoduleOf E) := Module.Finite.of_injective g (LinearMap.ker_eq_bot.mp hg)
  have hq : Module.finrank k (E ⧸ Q.submoduleOf E) = 0 := h0
  have := Module.finrank_zero_iff.mp hq
  have h1 : (Submodule.Quotient.mk (⟨y, hyE⟩ : E) : E ⧸ Q.submoduleOf E) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact h1

private theorem exists_finite_span_sup_shift_of_isLat {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]
    [IsScalarTower k k⟦X⟧ V] (N : Submodule k⟦X⟧ V) (hN : IsLat N) :
    ∃ s : Set V, s.Finite ∧ N.restrictScalars k ≤ Submodule.span k s ⊔ (sh 1 N).restrictScalars k := by
  obtain ⟨t, ht⟩ := hN.1
  refine ⟨↑t, t.finite_toSet, ?_⟩
  intro x hx
  rw [Submodule.restrictScalars_mem, ← ht] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.mem_sup_left (Submodule.subset_span hy)
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y hy0 hy =>
    have hyN : y ∈ N := by rw [ht] at hy0; exact hy0
    obtain ⟨a', ha'⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
      rw [PowerSeries.X_dvd_iff]; simp
    have hsplit : a = PowerSeries.C (PowerSeries.constantCoeff a) + PowerSeries.X * a' := by
      rw [← ha']; ring
    rw [hsplit, add_smul, mul_smul]
    refine add_mem ?_ (Submodule.mem_sup_right ?_)
    · have hc : (PowerSeries.C (PowerSeries.constantCoeff a) : k⟦X⟧) • y = (PowerSeries.constantCoeff a) • y := by
        rw [← algebraMap_smul (k⟦X⟧) (PowerSeries.constantCoeff a) y]; rfl
      rw [hc]; exact Submodule.smul_mem _ _ hy
    · rw [Submodule.restrictScalars_mem, mem_sh_iff_exists]
      exact ⟨a' • y, N.smul_mem a' hyN, by rw [zpow_one, vv_eq_coe_X, coe_powerSeries_smul_eq_smul]⟩

private theorem vv_pow_smul_mem_of_sen_eq_zero {k : Type} [Field k] {l : ℕ} (R : RingPG k l) {V : Type} [AddCommGroup V]
    [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]
    [IsScalarTower k k⟦X⟧ V] (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V) (hN : IsLat N)
    (s : ℕ) (hsen : sen g N (-((s + 1 : ℕ) : k)) = 0) (b : V) (hb : vv k ^ (s + 1) • b ∈ N)
    (hw : g b - b ∈ sh 1 N) : vv k ^ s • b ∈ N := by
  have hv : vv k ≠ 0 := vv_ne_zero k
  obtain ⟨κ, hκ0, hκ⟩ := R.γ_v
  obtain ⟨κ₁, hκ₁⟩ : PowerSeries.X ∣ κ - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [hκ0]
  have hE : ∀ t : ℕ, ∃ e : k⟦X⟧,
      (1 - κ * PowerSeries.X) ^ t - 1 + (t : k⟦X⟧) * PowerSeries.X = PowerSeries.X ^ 2 * e := by
    intro t
    induction t with
    | zero => exact ⟨0, by simp⟩
    | succ t ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c * (1 - κ * PowerSeries.X) - κ₁ + (t : k⟦X⟧) * κ, ?_⟩
      push_cast
      linear_combination (1 - κ * PowerSeries.X) * hc - PowerSeries.X * hκ₁
  obtain ⟨e, he⟩ := hE (s + 1)
  have he' : (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) - 1 + ((s + 1 : ℕ) : k⸨X⸩) * vv k
      = vv k ^ 2 * (e : k⸨X⸩) := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ k) he
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, map_natCast] at h
    rw [← vv_eq_coe_X] at h
    exact h
  have hw' : (vv k)⁻¹ • (g b - b) ∈ N := by
    have h := (mem_sh_iff_smul_mem (a := 1)).mp hw
    rwa [zpow_neg_one] at h
  have hgy : g (vv k ^ (s + 1) • b) = (vv k * (1 - (κ : k⸨X⸩) * vv k)) ^ (s + 1) • g b := by
    rw [show g (vv k ^ (s + 1) • b) = R.γ (vv k ^ (s + 1)) • g b from hg _ _, map_pow, hκ]
  have hz : nab g (vv k ^ (s + 1) • b) + ((s + 1 : ℕ) : k) • (vv k ^ (s + 1) • b) ∈ sh 1 N := by
    rw [mem_sh_iff_smul_mem]
    have hid : vv k ^ (-(1 : ℤ)) • (nab g (vv k ^ (s + 1) • b) + ((s + 1 : ℕ) : k) • (vv k ^ (s + 1) • b))
        = (e : k⸨X⸩) • (vv k ^ (s + 1) • b) + (((1 - κ * PowerSeries.X) ^ (s + 1) * PowerSeries.X ^ s : k⟦X⟧) : k⸨X⸩) • ((vv k)⁻¹ • (g b - b)) := by
      rw [nab_apply_eq, hgy, Nat.cast_smul_eq_nsmul k, ← Nat.cast_smul_eq_nsmul k⸨X⸩]
      simp only [map_mul, map_pow, map_sub, map_one]
      rw [← vv_eq_coe_X, zpow_neg_one]
      have hvi : vv k * (vv k)⁻¹ = 1 := mul_inv_cancel₀ hv
      set vi := (vv k)⁻¹
      generalize ((s + 1 : ℕ) : k⸨X⸩) = c' at he' ⊢
      generalize (e : k⸨X⸩) = E at he' ⊢
      have hA : vi * (vi * (vv k * (1 - (κ : k⸨X⸩) * vv k)) ^ (s + 1))
          = (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s * vi := by
        rw [mul_pow]
        linear_combination (vi * (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s) * hvi
      have hB : E * vv k ^ (s + 1) = -(vi * (vi * vv k ^ (s + 1))) + vi * (c' * vv k ^ (s + 1))
          + (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s * vi := by
        linear_combination (-(vv k ^ s * vi)) * he' - (E * vv k ^ (s + 1) - vi * vv k ^ s) * hvi
      simp only [smul_add, smul_sub, smul_smul]
      rw [hA, hB]
      simp only [add_smul, neg_smul]
      abel
    rw [hid]
    exact add_mem (powerSeries_smul_mem_of_mem N hb _) (powerSeries_smul_mem_of_mem N hw' _)
  have hkey : vv k ^ (s + 1) • b ∈ sh 1 N := by
    obtain ⟨t, ht, hsp⟩ := exists_finite_span_sup_shift_of_isLat N hN
    exact mem_of_gmult_eq_zero_of_sub_mem (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
      (-((s + 1 : ℕ) : k)) t ht hsp hsen _ hb (by
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply, neg_smul, sub_neg_eq_add]; exact hz)
  have h := (mem_sh_iff_smul_mem (a := 1)).mp hkey
  rw [smul_smul, zpow_neg_one, pow_succ', inv_mul_cancel_left₀ hv] at h
  exact h

theorem cocycle_split_of_contracting : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (N : ZMod n → Submodule k⟦X⟧ V) (J : ZMod n → ℕ), (∀ i, IsLat (N i)) → (∀ i, CondC (D.γ i) (N i)) → (∀ i, pull (D.φ i) (N (i - 1)) ≤ sh 1 (N i)) → (∀ i (j : ℕ), 1 ≤ j → j ≤ J i → sen (D.γ i) (N i) (-(j : k)) = 0) → ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i) → (∀ i, g i ∈ sh 1 (N i)) → (∀ i, b i ∈ sh (-(J i)) (N i)) → ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧ g i = D.γ i (m i) - m i := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D N J hlat hC hφ hsen b g hcoc hg hb
  have hsub : ∀ i, sh 1 (N i) ≤ N i := by
    intro i
    have h := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) (N i)
    rwa [sh_zero_eq] at h
  have hφ' : ∀ i, ∀ x ∈ N (i - 1), D.φ i x ∈ sh 1 (N i) := fun i x hx =>
    hφ i (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hw : ∀ i, D.γ i (b i) - b i ∈ sh 1 (N i) := by
    intro i
    rw [hcoc i]
    exact sub_mem (hφ' i _ (hsub (i - 1) (hg (i - 1)))) (hg i)
  have hbN : ∀ i, b i ∈ N i := by
    intro i
    have key : ∀ d, d ≤ J i → vv k ^ (J i - d) • b i ∈ N i := by
      intro d
      induction d with
      | zero => intro _; simpa using (mem_sh_iff_smul_mem).mp (hb i)
      | succ d ih =>
        intro hd
        have e : J i - d = (J i - (d + 1)) + 1 := by omega
        have h1 := ih (by omega)
        rw [e] at h1
        have h2 := hsen i (J i - d) (by omega) (by omega)
        rw [e] at h2
        exact vv_pow_smul_mem_of_sen_eq_zero R (D.γ i) (D.γ_semi i) (N i) (hlat i) _ h2 (b i) h1 (hw i)
    simpa using key (J i) le_rfl
  obtain ⟨m, hmN, hm⟩ := (one_sub_frob_bij R D N hlat hφ').1 b hbN
  have hhN : ∀ i, D.γ i (m i) - m i - g i ∈ N i := fun i =>
    sub_mem (hsub i (hC i (m i) (hmN i))) (hsub i (hg i))
  have hhφ : ∀ i, D.φ i (D.γ (i - 1) (m (i - 1)) - m (i - 1) - g (i - 1)) = D.γ i (m i) - m i - g i := by
    intro i
    have e1 : D.φ i (m (i - 1)) = b i + m i := by rw [← hm i]; abel
    have e2 : D.φ i (g (i - 1)) = D.γ i (b i) - b i + g i := by rw [hcoc i]; abel
    rw [map_sub, map_sub, D.comm, e1, e2, map_add (f := _)]
    abel
  have h0 := (one_sub_frob_bij R D N hlat hφ').2 (fun i => D.γ i (m i) - m i - g i) hhN hhφ
  refine ⟨m, hmN, fun i => ⟨(hm i).symm, ?_⟩⟩
  have h3 := congrFun h0 i
  simp only [Pi.zero_apply] at h3
  exact (sub_eq_zero.mp h3).symm

end GlobalTheory.PhiGam
end
end

section

noncomputable section
namespace GlobalTheory.PhiGam.TrivCocycle
open scoped LaurentSeries PowerSeries

theorem frob_sub_one_bij {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] (R : RingPG k l) {n : ℕ} [NeZero n] :
    (∀ s : ZMod n → k⟦X⟧, ∃ m : ZMod n → k⟦X⟧,
      ∀ i, R.φ (vv k * (m (i - 1) : k⸨X⸩)) - vv k * (m i : k⸨X⸩) = vv k * (s i : k⸨X⸩)) ∧
    ∀ m : ZMod n → k⟦X⟧, (∀ i, R.φ (vv k * (m (i - 1) : k⸨X⸩)) = vv k * (m i : k⸨X⸩)) → m = 0 := by
  have inj : Function.Injective (fun a : k⟦X⟧ => (a : k⸨X⸩)) := HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  have hX := vv_eq_coe_X k
  have hv := vv_ne_zero k
  choose f hf using R.φ_int
  obtain ⟨u, hu⟩ := R.φ_v
  obtain ⟨l', hl'⟩ := Nat.exists_eq_add_of_le hl.out.two_le
  let T : (ZMod n → k⟦X⟧) →+ (ZMod n → k⟦X⟧) :=
    { toFun := fun m i => (u : k⟦X⟧) * PowerSeries.X ^ (l' + 1) * f (m (i - 1))
      map_zero' := by
        funext i
        apply inj
        simp [← hf]
      map_add' := by
        intro a b
        funext i
        apply inj
        simp only [Pi.add_apply, map_add (f := _), map_mul, ← hf, mul_add] }
  have hT : ∀ m i, T m i = (u : k⟦X⟧) * PowerSeries.X ^ (l' + 1) * f (m (i - 1)) := fun _ _ => rfl
  have hT' : ∀ m i, vv k * (T m i : k⸨X⸩) = R.φ (vv k * (m (i - 1) : k⸨X⸩)) := by
    intro m i
    rw [hT, map_mul R.φ, hu, hf, map_mul, map_mul, map_pow, ← hX, hl']
    ring
  haveI : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (ZMod n → k⟦X⟧) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _
  haveI : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (ZMod n → k⟦X⟧) := by
    rw [← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have key := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T
    (contracting_of_semi PowerSeries.X ((u : k⟦X⟧) * PowerSeries.X ^ (l' + 1)) T ?_ ?_)
  · constructor
    · intro s
      obtain ⟨m, hm⟩ := key.1 s
      refine ⟨m, fun i => ?_⟩
      rw [← hT', ← hm, Pi.sub_apply, map_sub, mul_sub]
    · intro m h
      refine key.2 m ?_
      funext i
      apply inj
      apply mul_left_cancel₀ hv
      rw [hT', h]
  · intro m
    funext i
    apply inj
    simp only [hT, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hf, ← hX, hu, hl']
    ring
  · intro m
    refine ⟨fun i => (u : k⟦X⟧) * PowerSeries.X ^ l' * f (m (i - 1)), ?_⟩
    funext i
    simp only [hT, Pi.smul_apply, smul_eq_mul]
    ring

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] (b g : ZMod n → k⟦X⟧), (∀ i, PowerSeries.constantCoeff (g i) = 0) → (∀ i, R.γ (b i : k⸨X⸩) - (b i : k⸨X⸩) = R.φ (g (i - 1) : k⸨X⸩) - (g i : k⸨X⸩)) → ∃ (m : ZMod n → k⟦X⟧) (c : ZMod n → k), ∀ i, (b i : k⸨X⸩) = R.φ (m (i - 1) : k⸨X⸩) - (m i : k⸨X⸩) + algebraMap k k⸨X⸩ (c i) ∧ (g i : k⸨X⸩) = R.γ (m i : k⸨X⸩) - (m i : k⸨X⸩) := by
  intro k _ l _ _ R n _ b g hg hc
  have hX := vv_eq_coe_X k
  obtain ⟨h1, h2⟩ := frob_sub_one_bij R (n := n)
  choose g' hg' using fun i => PowerSeries.X_dvd_iff.2 (hg i)
  let s : ZMod n → k⟦X⟧ := fun i => PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (b i)
  have hb : ∀ i, (b i : k⸨X⸩) =
      vv k * (s i : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff (b i)) := by
    intro i
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (b i), map_add (f := _), map_mul, ← vv_eq_coe_X]
    rfl
  obtain ⟨m, hm⟩ := h1 s
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  choose t ht using R.γ_int
  have hd : ∀ i, vv k * ((g' i - ((1 - κ * PowerSeries.X) * t (m i) - m i) : k⟦X⟧) : k⸨X⸩) =
      (g i : k⸨X⸩) - (R.γ (vv k * (m i : k⸨X⸩)) - vv k * (m i : k⸨X⸩)) := by
    intro i
    rw [hg' i, map_mul R.γ, hκ, ht]
    simp only [map_sub, map_mul, map_one, ← hX]
    ring
  have h0 := h2 (fun i => g' i - ((1 - κ * PowerSeries.X) * t (m i) - m i)) (by
    intro i
    rw [hd, hd, map_sub, map_sub, R.comm]
    have e := hc i
    rw [hb i, ← hm i, map_add R.γ, map_sub R.γ, AlgHom.commutes] at e
    linear_combination -e)
  refine ⟨fun i => PowerSeries.X * m i, fun i => PowerSeries.constantCoeff (b i), fun i => ?_⟩
  have e1 : ∀ j, ((PowerSeries.X * m j : k⟦X⟧) : k⸨X⸩) = vv k * (m j : k⸨X⸩) := fun j => by
    rw [map_mul, ← hX]
  simp only [e1]
  refine ⟨by rw [hm, ← hb], ?_⟩
  have e := hd i
  rw [congrFun h0 i, Pi.zero_apply, map_zero, mul_zero] at e
  exact sub_eq_zero.1 e.symm

end GlobalTheory.PhiGam.TrivCocycle
end
end
