module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle550
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_uniformiser_eisenstein_not_in_X_pow : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∃ (π : O) (Ep : Polynomial (Wq l a)), Irreducible π ∧ (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) ∧ (∃ i, ¬ l ∣ i ∧ Ep.coeff i ≠ 0) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  first | exact @GlobalTheory.EisShift.exists_uniformiser | exact GlobalTheory.EisShift.exists_uniformiser | (intros; apply GlobalTheory.EisShift.exists_uniformiser <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.bcris_periodMatrix_over_acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), C.t ^ N • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • Z) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  first | exact @GlobalTheory.CrisPeriods.periods_over_Acris | exact GlobalTheory.CrisPeriods.periods_over_Acris | (intros; apply GlobalTheory.CrisPeriods.periods_over_Acris <;> assumption)
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.OEmod

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

def ψ : bk.S →+* Cb l := (WittVector.constantCoeff (p := l) (R := Cb l)).comp bk.evW

theorem ψ_apply (s : bk.S) : ψ bk s = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
  simp [ψ, BK.evW, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem ψ_X : ψ bk X = algebraMap (OCb l) (Cb l) bk.flat := by
  rw [ψ_apply, bk.ev_X, WittVector.teichmuller_coeff_zero]

theorem cc_evW_X : WittVector.constantCoeff (bk.evW X) = algebraMap (OCb l) (Cb l) bk.flat := ψ_X bk

theorem cc_l_mul (y : WCb l) : WittVector.constantCoeff ((l : WCb l) * y) = 0 := by
  rw [WittVector.constantCoeff_apply, mul_comm]
  exact WittVector.mul_charP_coeff_zero y

theorem evW_X_eq : bk.evW X = WittVector.teichmuller l (algebraMap (OCb l) (Cb l) bk.flat) := by
  simp [BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]

theorem l_dvd_of_not_isUnit (a : ℕ) [NeZero a] (x : Wq l a) (h : ¬ IsUnit x) : (l : Wq l a) ∣ x := by
  by_cases h0 : x = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero => exact absurd (by simpa using WittVector.isUnit_of_coeff_zero_ne_zero b hb) h
  | succ m => exact Dvd.intro _ (by rw [pow_succ', mul_assoc])

theorem exists_unit (s : bk.S) (hs : ψ bk s ≠ 0) :
    ∃ (k : ℕ) (s₁ : bk.S), IsUnit s₁ ∧ ψ bk s = ψ bk X ^ k * ψ bk s₁ := by
  have hex : ∃ i, IsUnit (coeff i s) := by
    by_contra hno
    push_neg at hno
    have hd : ∀ i, (l : Wq l bk.a) ∣ coeff i s := fun i => l_dvd_of_not_isUnit bk.a _ (hno i)
    choose c hc using hd
    have : s = (l : bk.S) * PowerSeries.mk c := by
      ext i
      rw [← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, hc i]
    apply hs
    rw [this, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  classical
  let k := Nat.find hex
  have hk : IsUnit (coeff k s) := Nat.find_spec hex
  have hlt : ∀ i < k, (l : Wq l bk.a) ∣ coeff i s := fun i hi =>
    l_dvd_of_not_isUnit bk.a _ (Nat.find_min hex hi)
  choose! c hc using hlt
  let s₁ : bk.S := PowerSeries.mk fun i => coeff (i + k) s
  let s₂ : bk.S := PowerSeries.mk fun i => if i < k then c i else 0
  have hs₁ : IsUnit s₁ := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
    exact hk
  have hsplit : s = X ^ k * s₁ + (l : bk.S) * s₂ := by
    ext i
    rw [map_add (f := _), coeff_X_pow_mul', ← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, coeff_mk]
    by_cases hi : i < k
    · rw [if_neg (by omega), if_pos hi, zero_add, hc i hi]
    · rw [if_pos (by omega), if_neg hi, mul_zero, add_zero, Nat.sub_add_cancel (by omega)]
  refine ⟨k, s₁, hs₁, ?_⟩
  conv_lhs => rw [hsplit]
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]

end GlobalTheory.BSP.OEmod

open GlobalTheory.BSP.OEmod in
theorem GlobalTheory.BSP.oe_mod_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)) ∧ (∀ s : bk.S, bk.evW s ∈ bk.OE) ∧ IsUnit (bk.evW X) ∧ (∀ w : WCb l, bk.evW X * w ∈ bk.OE → w ∈ bk.OE) ∧ ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), y⁻¹ ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk
  have hflat : bk.flat ≠ 0 := (GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk).2.2.2.1
  have hf : algebraMap (OCb l) (Cb l) bk.flat ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hflat
  have hunit : IsUnit (bk.evW X) := by
    rw [evW_X_eq]
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [WittVector.teichmuller_coeff_zero]
    exact hf
  have h1 : ∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S),
      algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
    intro y
    rw [Subring.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨m, s, z, h⟩ := hw 1
      refine ⟨m, s, ?_⟩
      have := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) h
      rw [map_mul, map_pow, map_add (f := _), pow_one, cc_l_mul, add_zero, cc_evW_X] at this
      rw [this, ← ψ_apply]
      rfl
    · rintro ⟨m, s, h⟩
      obtain ⟨u, hu⟩ := hunit
      refine ⟨(↑(u⁻¹) : WCb l) ^ m * bk.evW s, fun n => ⟨m, s, 0, ?_⟩, ?_⟩
      · rw [mul_zero, add_zero, ← mul_assoc, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_mul]
      · have hc : WittVector.constantCoeff (bk.evW X) * WittVector.constantCoeff ((↑(u⁻¹) : WCb l)) = 1 := by
          rw [← map_mul, ← hu, Units.mul_inv, map_one]
        rw [cc_evW_X] at hc
        rw [map_mul, map_pow]
        have hs : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := ψ_apply bk s
        rw [hs, ← h, ← mul_assoc, ← mul_pow, mul_comm _ (algebraMap (OCb l) (Cb l) bk.flat), hc, one_pow, one_mul]
  refine ⟨h1, fun s n => ⟨0, s, 0, by simp⟩, hunit, fun w hw n => ?_, fun y hy => ?_⟩
  · obtain ⟨m, s, z, h⟩ := hw n
    exact ⟨m + 1, s, z, by rw [pow_succ, mul_assoc, h]⟩
  · by_cases hy0 : y = 0
    · rw [hy0, inv_zero]; exact Subring.zero_mem _
    obtain ⟨m, s, h⟩ := (h1 y).1 hy
    rw [← ψ_apply] at h
    have hs : ψ bk s ≠ 0 := by rw [← h]; exact mul_ne_zero (pow_ne_zero _ hf) hy0
    obtain ⟨k, s₁, ⟨t, rfl⟩, hk⟩ := exists_unit bk s hs
    rw [h1]
    refine ⟨k, ((X : bk.S) ^ m * ↑(t⁻¹) : bk.S), ?_⟩
    rw [← ψ_apply, map_mul, map_pow, ψ_X]
    rw [hk, ψ_X] at h
    have ht : ψ bk ↑t * ψ bk ↑(t⁻¹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ht0 : ψ bk ↑t ≠ 0 := left_ne_zero_of_mul_eq_one ht
    have hinv : ψ bk ↑(t⁻¹) = (ψ bk ↑t)⁻¹ := eq_inv_of_mul_eq_one_right ht
    rw [hinv]
    field_simp
    linear_combination -h
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  first | (exact @GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (exact GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (intros; apply GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.dvd_iff_dvd_coeff {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (tb : TopBasis s I ι) (hI : IsHausdorff I S) (p : S)
    (hp : ∀ (n : ℕ) (y : S), p * y ∈ I ^ (2 * n + 2) → y ∈ I ^ n) (x : A) :
    s p ∣ x ↔ ∀ i, p ∣ tb.c i x := by
  obtain ⟨h0, -, h2⟩ := GlobalTheory.T.coeff_zero_map_pow_null_facts S A ι s I tb
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨_, tb.c_mul i p y⟩
  · choose a ha using h
    obtain ⟨y, hy⟩ := h2 hI a fun n => (tb.fin x (2 * n + 2)).subset fun i hi hi' =>
      hi (hp n _ (ha i ▸ hi'))
    refine ⟨y, sub_eq_zero.1 (h0 _ fun i => ?_)⟩
    rw [map_sub, tb.c_mul, hy, ha, sub_self]

theorem TopBasis.mod_props {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (tb : TopBasis s I ι) (hI : IsHausdorff I S) (l : ℕ) (u : S)
    (hp : ∀ (n : ℕ) (y : S), (l : S) * y ∈ I ^ (2 * n + 2) → y ∈ I ^ n)
    (h1 : ∀ y : S, (l : S) * y = 0 → y = 0) (h2 : ∀ y : S, (l : S) ∣ u * y → (l : S) ∣ y)
    (h3 : ∀ y : S, (∀ m : ℕ, ∃ z, (l : S) ∣ y - u ^ m * z) → (l : S) ∣ y) :
    (∀ x : A, (l : A) * x = 0 → x = 0) ∧ (∀ x : A, (l : A) ∣ s u * x → (l : A) ∣ x) ∧
      ∀ x : A, (∀ m : ℕ, ∃ z, (l : A) ∣ x - s u ^ m * z) → (l : A) ∣ x := by
  have key := tb.dvd_iff_dvd_coeff hI (l : S) hp
  rw [← map_natCast s l]
  refine ⟨fun x hx => (GlobalTheory.T.coeff_zero_map_pow_null_facts S A ι s I tb).1 x fun i => h1 _ ?_, fun x hx => (key x).2 fun i => h2 _ ?_,
    fun x hx => (key x).2 fun i => h3 _ fun m => ?_⟩
  · rw [← tb.c_mul, hx, map_zero]
  · rw [← tb.c_mul]
    exact (key _).1 hx i
  · obtain ⟨z, hz⟩ := hx m
    refine ⟨tb.c i z, ?_⟩
    rw [← tb.c_mul, ← map_sub, map_pow]
    exact (key _).1 hz i

theorem env_ainf_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)), (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) * x = 0 → x = 0) ∧ (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) ∣ En.inl.f (bk.ev X) * x → ((l : ℕ) : En.Q.A) ∣ x) ∧ ∀ x : En.Q.A, (∀ m : ℕ, ∃ z, ((l : ℕ) : En.Q.A) ∣ x - En.inl.f (bk.ev X) ^ m * z) → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En
  obtain ⟨hp, h2, h3, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  exact En.tb.mod_props (ainfObj K).complete.toIsHausdorff l (bk.ev X) hp ainf_torsionFree h2 h3

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.AinfTopBasis

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ ι : Type, Nonempty (TopBasis bk.ev bk.J ι) := by
  intro l _ K bk
  obtain ⟨h0, hu, -, hJ⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  obtain ⟨ι, b, i₀, hb, hspan, hind⟩ := GlobalTheory.T.ideal_span_prime_variable_basis l K bk
  have he := bk.deg_pos
  have hstrict := GlobalTheory.T.strict_indep_pow_of_regular_pair bk.S (Ainf l) bk.ev (l : bk.S) X ι b
    (fun x hx => by
      rw [map_natCast, mul_comm] at hx
      exact WittVector.eq_zero_of_p_mul_eq_zero x hx)
    (fun x hx => by
      rw [map_natCast, ← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker] at hx ⊢
      rw [map_mul, bk.ev_X, WittVector.constantCoeff_apply (x := WittVector.teichmuller l _),
        WittVector.teichmuller_coeff_zero] at hx
      exact (mul_eq_zero.1 hx).resolve_left h0) hind
  have hS : IsAdicComplete (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}) bk.S := by
    have h := ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff (Ideal.span {(l : Wq l bk.a)})
    rwa [← ReciprocityTheory.P1.map_C_sup_span_X, Ideal.map_span, Set.image_singleton, map_natCast] at h
  have hA : IsAdicComplete ((Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) (Ainf l) := by
    rw [← Ideal.span_insert, Ideal.map_span, Set.image_pair, map_natCast]
    refine (GlobalTheory.Per.AinfComplete.main l _ fun h => hu ?_).1
    have h2 := h.map (WittVector.constantCoeff (p := l) (R := OCb l))
    rwa [bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h2
  obtain ⟨TB, -⟩ := GlobalTheory.T.exists_adicTopologicalBasis_of_span_of_strict bk.S (Ainf l) bk.ev _ ι b i₀ hb
    (Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)) hS hA hspan hstrict
  obtain ⟨TB', -⟩ := GlobalTheory.T.exists_of_pow_le_of_pow_le_same_adicTopology bk.S (Ainf l) bk.ev _ ι TB bk.J (1 + bk.Ep.natDegree) 1
    hS.toIsHausdorff (by omega) one_pos
    (by
      rw [← hJ]
      refine Ideal.sup_pow_add_le_pow_sup_pow.trans ?_
      rw [pow_one, Ideal.span_singleton_pow])
    (by
      rw [pow_one, ← hJ]
      refine sup_le_sup_left ?_ _
      rw [Ideal.span_singleton_le_span_singleton]
      exact dvd_pow_self _ he.ne')
  exact ⟨ι, ⟨TB'⟩⟩

end GlobalTheory.BSP.AinfTopBasis
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.acris_torsionFree_complete_frobenius_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∃ v : (Per.Acris l)ˣ, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) = (l : Per.Acris l) * v) ∧ (∀ a : Ainf l, phiA l ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (WittVector.frobenius a)) ∧ ∀ (g : GQ l) (a : Ainf l), sigA g ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (Per.σA g a) := by
  first | exact @GlobalTheory.AcrisFrobE.main | exact GlobalTheory.AcrisFrobE.main | (intros; apply GlobalTheory.AcrisFrobE.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  first | (exact @GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub) | (exact GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub) | (intros; apply GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n c : ℕ), Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c})) := by
  first | exact @GlobalTheory.BKFin.finite_quot | exact GlobalTheory.BKFin.finite_quot | (intros; apply GlobalTheory.BKFin.finite_quot <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isUnit_bdRPlus_matrix_of_congr_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) → (∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l 1) → IsUnit B := by
  first | (exact @GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one) | (exact GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one) | (intros; apply GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_prism_hom_ext_of_X : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (g g' : Hom bk.prism C), BK.hf g X = BK.hf g' X → g = g' := by
  first | exact @GlobalTheory.BSP.BK.hom_ext_of_hf_X | exact GlobalTheory.BSP.BK.hom_ext_of_hf_X | (intros; apply GlobalTheory.BSP.BK.hom_ext_of_hf_X <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (En₂ : Env bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)), Nonempty (TopBasis (BK.hf En.inl) bk.J (Digits l)) ∧ ∃ ι : Type, Nonempty (TopBasis (BK.hf (En₂.inl.comp En.inl)) bk.J ι) := by
  first | exact @GlobalTheory.BSP.envelopes_topBasis | exact GlobalTheory.BSP.envelopes_topBasis | (intros; apply GlobalTheory.BSP.envelopes_topBasis <;> assumption)
end
