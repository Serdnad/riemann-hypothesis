module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle060
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.FourierTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem finite_F_L [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  haveI : Module.Finite A.K A.L := Module.Finite.equiv A.push.symm.out.equiv
  exact Module.Finite.trans A.K A.L

theorem star_smul_F (A : Et F E) (c : F) (y : A.L) : star (c • y) = c • star y := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, mul_comm, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]

def beta (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.L :=
  LinearMap.mk₂ F (fun y' y => Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)))
    (by intro a b c; simp only [star_add, add_mul, map_add (f := _), mul_add])
    (by intro c a b
        rw [star_smul_F, smul_mul_assoc, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])
    (by intro a b c; simp only [mul_add, map_add (f := _)])
    (by intro c a b
        rw [mul_smul_comm, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])

theorem beta_apply (A : Et F E) (x : A.K) (y' y : A.L) :
    beta A x y' y = Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)) := rfl

theorem algMap_inj (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    Function.Injective (algebraMap A.K A.L) := by
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro k hk
  by_contra hne
  obtain ⟨k', hk'⟩ := hK.mul_inv_cancel hne
  have h : algebraMap A.K A.L (k * k') = 0 := by rw [map_mul, hk, zero_mul]
  rw [hk', map_one] at h
  exact one_ne_zero h

theorem beta_symm [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    ∀ a b, beta A x a b = beta A x b a := by
  intro a b
  rw [beta_apply, beta_apply]
  congr 2
  apply algMap_inj A hK hL
  rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, star_mul, star_mul, star_star, star_star]
  ring

theorem trace_algMap [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (c : A.K) :
    Algebra.trace A.K A.L (algebraMap A.K A.L c) = 2 * c := by
  apply algMap_inj A hK hL
  rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, A.star_K, map_mul, map_ofNat]
  ring

theorem beta_sepLeft [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).SeparatingLeft := by
  haveI : Nontrivial A.K := ⟨hK.exists_pair_ne⟩
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  intro a ha
  by_contra hne
  have hsa : star a ≠ 0 := by
    intro h; apply hne; simpa using congrArg star h
  obtain ⟨u, hu⟩ := hL.mul_inv_cancel hsa
  have h2 : (2 : A.K) ≠ 0 := by
    have : (2 : A.K) = algebraMap F A.K 2 := by rw [map_ofNat]
    rw [this]
    intro h
    exact two_ne_zero ((injective_iff_map_eq_zero (algebraMap F A.K)).1 (algebraMap F A.K).injective _ h)
  obtain ⟨t, ht⟩ := hK.mul_inv_cancel h2
  have htr : ∀ k : A.K, Algebra.trace F A.K k = 0 := by
    intro k
    have := ha (u * algebraMap A.K A.L (((x⁻¹ : A.Kˣ) : A.K) * t * k))
    rw [beta_apply, ← mul_assoc, hu, one_mul, trace_algMap A hK hL] at this
    have e : (x : A.K) * (2 * (((x⁻¹ : A.Kˣ) : A.K) * t * k)) = k := by
      calc (x : A.K) * (2 * (((x⁻¹ : A.Kˣ) : A.K) * t * k))
          = ((x : A.K) * ((x⁻¹ : A.Kˣ) : A.K)) * (2 * t) * k := by ring
        _ = k := by rw [Units.mul_inv, ht, one_mul, one_mul]
    rwa [e] at this
  have h1 : (1 : A.K) = 0 :=
    (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1.1 1 (fun n => by rw [Algebra.traceForm_apply, one_mul]; exact htr n)
  exact one_ne_zero h1

theorem beta_isSymm [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    (beta A x).IsSymm := LinearMap.BilinForm.isSymm_def.2 (beta_symm A hK hL x)

theorem beta_nondeg [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).Nondegenerate :=
  ((beta_isSymm A hK hL x).isRefl.nondegenerate_iff_separatingLeft).2 (beta_sepLeft A hK hL x)

theorem cont_psi {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  have h : (fun b => ψ b) =ᶠ[𝓝 a] fun _ => ψ a := by
    filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
    have h1 : ψ (b - a) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact le_of_lt hb)
    calc ψ b = ψ (a + (b - a)) := by rw [add_sub_cancel]
      _ = ψ a * ψ (b - a) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ a := by rw [h1, mul_one]
  exact continuousAt_const.congr h.symm

end GlobalTheory.JR.WeilQuad.FourierTest


open GlobalTheory.JR.WeilQuad.FourierTest in
theorem GlobalTheory.JR.WeilQuad.fOp_isTest_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → IsTest (fOp A ψ x μ φ) ∧
      ∀ φ' : A.L → ℂ, IsTest φ' → fOp A ψ x μ (φ + φ') = fOp A ψ x μ φ + fOp A ψ x μ φ' := by
  intro F E _ _ _ _ _ A ψ x μ ω h φ hφ
  obtain ⟨hK, hL, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI := finite_F_L A
  have hker : A.kerL ψ (x : A.K) = fun a b => ψ (beta A x a b) := rfl
  have hint : ∀ f : A.L → ℂ, IsTest f → ∀ y, Integrable (fun y' => f y' * A.kerL ψ (x : A.K) y' y) μ := by
    intro f hf y
    rw [hker]
    refine Continuous.integrable_of_hasCompactSupport ?_ (hf.2.mul_right)
    exact hf.1.continuous.mul
      ((cont_psi hψ).comp (IsModuleTopology.continuous_of_linearMap ((beta A x).flip y)))
  refine ⟨?_, fun φ' hφ' => ?_⟩
  · have := (GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.L (beta A x)
      (beta_isSymm A hK hL x) (beta_nondeg A hK hL x)).2 μ hsd.1 φ hφ
    unfold fOp
    rw [hker]
    exact this
  · funext y
    simp only [fOp, fourB, Pi.add_apply, add_mul]
    exact integral_add (hint φ hφ y) (hint φ' hφ' y)
end
end

section

noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Matrix

section Cz

variable {L : Type} [Field L]

theorem cz_neg (f : PowerSeries L) {k : ℤ} (hk : k < 0) : cz f k = 0 := by
  simp [cz, not_le.mpr hk]

theorem cz_nat (f : PowerSeries L) (k : ℕ) : cz f (k : ℤ) = PowerSeries.coeff k f := by
  simp [cz]

theorem cz_add (f g : PowerSeries L) (k : ℤ) : cz (f + g) k = cz f k + cz g k := by
  unfold cz; split_ifs <;> simp

theorem cz_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries L) (k : ℤ) :
    cz (∑ i ∈ s, f i) k = ∑ i ∈ s, cz (f i) k := by
  unfold cz; split_ifs <;> simp

theorem cz_C_mul (c : L) (f : PowerSeries L) (k : ℤ) : cz (PowerSeries.C c * f) k = c * cz f k := by
  unfold cz; split_ifs <;> simp

theorem cz_rescale (c : L) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.rescale c f) k = c ^ k * cz f k := by
  rcases lt_or_ge k 0 with h | h
  · simp [cz_neg _ h]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [cz_nat, PowerSeries.coeff_rescale]

theorem cz_X_pow_mul (w : ℕ) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.X ^ w * f) (k + (w : ℤ)) = cz f k := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    rcases lt_or_ge (k + (w : ℤ)) 0 with h' | h'
    · exact cz_neg _ h'
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h'
      rw [hm, cz_nat, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [← Nat.cast_add, cz_nat, cz_nat, PowerSeries.coeff_X_pow_mul]

theorem cz_mul (g f : PowerSeries L) (k : ℤ) (N : ℕ) (hN : k < (N : ℤ)) :
    cz (g * f) k = ∑ i ∈ Finset.range N, PowerSeries.coeff i g * cz f (k - (i : ℤ)) := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [cz_neg _ (by omega), mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [cz_nat, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show m + 1 ≤ N by omega))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
      rw [← Nat.cast_sub this, cz_nat]
    · intro i _ hi
      have : m < i := by simpa using hi
      rw [cz_neg _ (by omega), mul_zero]

theorem series_transport {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
    {r r' : ℕ} (w w' : ℕ) (A : Fin r' → PowerSeries L) (Bs : Fin r → PowerSeries L) (κ : L) (hκ : κ ≠ 0)
    (g : PowerSeries L) (c : Fin r' → Fin r → L)
    (hA : ∀ j, (PowerSeries.C κ * PowerSeries.X) ^ w * A j =
      PowerSeries.X ^ w' * (g * ∑ p, PowerSeries.C (c j p) * PowerSeries.rescale κ (Bs p)))
    (h : M →ₗ[L] M') (D : Fin r → M) (D' : Fin r' → M') (hD : ∀ p, h (D p) = ∑ j, c j p • D' j) (k : ℤ) :
    ∑ j, cz (A j) (k + (w' : ℤ)) • D' j = ∑ᶠ i : ℕ, PowerSeries.coeff i g •
      (κ ^ (k - (i : ℤ)) • h (∑ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) • D p)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k + (w : ℤ) < (N : ℤ) := ⟨(k + (w : ℤ)).toNat + 1, by omega⟩
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
  · have key : ∀ j, cz (A j) (k + (w' : ℤ)) = ∑ i ∈ Finset.range N, ∑ p, PowerSeries.coeff i g *
        (κ ^ (k - (i : ℤ)) * (cz (Bs p) (k - (i : ℤ) + (w : ℤ)) * c j p)) := by
      intro j
      have h1 := congrArg (fun f => cz f (k + (w : ℤ) + (w' : ℤ))) (hA j)
      rw [cz_X_pow_mul, mul_pow, ← map_pow, mul_assoc, cz_C_mul, add_right_comm, cz_X_pow_mul,
        cz_mul _ _ _ N hN] at h1
      apply mul_left_cancel₀ (pow_ne_zero w hκ)
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cz_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [cz_C_mul, cz_rescale, show k + (w : ℤ) - (i : ℤ) = k - (i : ℤ) + (w : ℤ) by ring, zpow_add₀ hκ,
        zpow_natCast]
      ring

    simp only [key, Finset.sum_smul, map_sum, map_smul, hD, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · intro i hi
    by_contra hc
    apply hi
    have : N ≤ i := by simpa using hc
    have hz : ∀ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) = 0 := fun p => cz_neg _ (by omega)
    simp [hz]

end Cz

theorem basis_transport {C S : Type} [CommRing C] [CommRing S] (J : C →+* S) (σ : C →+* C) (σS : S →+* S)
    (hJ : ∀ a, J (σ a) = σS (J a)) {M M' : Type} [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    (h : M →+ M') (hh : ∀ (a : S) m, h (a • m) = σS a • h m) (t q : C) (ht : IsUnit (J t)) (hq : IsUnit (J q))
    {r r' : ℕ} (w w' : ℕ) (bn d : Fin r → M) (bn' d' : Fin r' → M') (U : Fin r → Fin r → C)
    (U' : Fin r' → Fin r' → C) (H Cm : Fin r' → Fin r → C)
    (hd : ∀ j, J t ^ w • d j = ∑ i, J (U i j) • bn i) (hd' : ∀ j, J t ^ w' • d' j = ∑ i, J (U' i j) • bn' i)
    (hH : ∀ j, J q • h (bn j) = ∑ i, J (H i j) • bn' i)
    (hU : ∀ k p, t ^ w' * ∑ i, H k i * σ (U i p) = σ t ^ w * q * ∑ j, U' k j * Cm j p) (p : Fin r) :
    h (d p) = ∑ j, J (Cm j p) • d' j := by
  have hu : IsUnit (J t ^ w' * σS (J t) ^ w * J q) := ((ht.pow _).mul ((ht.map σS).pow _)).mul hq
  apply hu.smul_left_cancel.mp
  have e1 : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) =
      ∑ k, J (t ^ w' * ∑ i, H k i * σ (U i p)) • bn' k := by
    have : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) = J t ^ w' • J q • h (J t ^ w • d p) := by
      rw [hh, map_pow, smul_smul, smul_smul]
      congr 1
      ring

    rw [this, hd, map_sum, Finset.smul_sum, Finset.smul_sum]

    simp only [hh, smul_comm (J q), hH, Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
    Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have e2 : (J t ^ w' * σS (J t) ^ w * J q) • ∑ j, J (Cm j p) • d' j =
      ∑ k, J (σ t ^ w * q * ∑ j, U' k j * Cm j p) • bn' k := by
    have : ∀ j, (J t ^ w' * σS (J t) ^ w * J q) • J (Cm j p) • d' j =
        (σS (J t) ^ w * J q * J (Cm j p)) • J t ^ w' • d' j := by
      intro j
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [Finset.smul_sum]

    simp only [this, hd', Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
    Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  rw [e1, e2]
  simp only [hU]

theorem coord_transport {A : Type} [CommRing A] (σ : A →+* A) {r r' : ℕ} (U V : Matrix (Fin r) (Fin r) A)
    (U' V' : Matrix (Fin r') (Fin r') A) (H Cm : Matrix (Fin r') (Fin r) A) (q q' : A)
    (hq : ∀ a, q * a = 0 → a = 0) (hUV : U * V = 1) (hUV' : U' * V' = 1)
    (hU : H * U.map σ = q • (U' * Cm)) (c : Fin r → A) (c' : Fin r' → A)
    (hc : q • c' = q' • H *ᵥ (σ ∘ c)) : V' *ᵥ c' = q' • Cm *ᵥ (σ ∘ (V *ᵥ c)) := by
  have h1 : V' * H = q • (Cm * V.map σ) := by
    have h2 : U.map σ * V.map σ = 1 := by
      rw [← Matrix.map_mul, hUV, Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc V' * H = V' * (H * U.map σ) * V.map σ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = q • (Cm * V.map σ) := by
          rw [hU, Matrix.mul_smul, ← Matrix.mul_assoc, mul_eq_one_comm.mp hUV', Matrix.one_mul, Matrix.smul_mul]
  have h3 : σ ∘ (V *ᵥ c) = V.map σ *ᵥ (σ ∘ c) := by
    funext i
    exact RingHom.map_mulVec σ V c i
  have h4 : q • (V' *ᵥ c') = q • (q' • Cm *ᵥ (σ ∘ (V *ᵥ c))) := by
    rw [← Matrix.mulVec_smul, hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1, h3, Matrix.mulVec_mulVec,
      Matrix.smul_mulVec, smul_comm]
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.smul_apply, smul_eq_mul] at h5 ⊢
  exact sub_eq_zero.mp (hq _ (by rw [mul_sub, h5, sub_self]))

end GlobalTheory.HWL.Cmp
end
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransport

open scoped Pointwise

section Transport

variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']

theorem valuation_le_one_comap (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') (y : Ω) :
    (A'.comap φ.toRingHom).valuation y ≤ 1 ↔ A'.valuation (φ y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
  exact ValuationSubring.mem_comap

theorem valuation_lt_one_comap (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') (y : Ω) :
    (A'.comap φ.toRingHom).valuation y < 1 ↔ A'.valuation (φ y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    map_eq_zero_iff _ φ.injective]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀]

variable [NumberField E] [NumberField E'] (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') {σ : G E Ω} {τ : G E' Ω'}

theorem mem_Dec_comap (h : ∀ z, φ (σ z) = τ (φ z)) (hτ : τ ∈ Dec (F := E') A') :
    σ ∈ Dec (F := E) (A'.comap φ.toRingHom) := by
  have hx : ∀ x, σ x ∈ A'.comap φ.toRingHom ↔ x ∈ A'.comap φ.toRingHom := by
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    show φ (σ x) ∈ A' ↔ φ x ∈ A'
    rw [h]
    exact apply_mem_iff_of_mem_Dec hτ (φ x)
  show σ • A'.comap φ.toRingHom = A'.comap φ.toRingHom
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hx, mul_inv_apply]

theorem isFrob_comap (h : ∀ z, φ (σ z) = τ (φ z)) {q : ℕ} (hτ : IsFrob (F := E') A' q τ) :
    IsFrob (F := E) (A'.comap φ.toRingHom) q σ := by
  refine ⟨mem_Dec_comap A' φ h hτ.1, fun x hx => ?_⟩
  rw [valuation_lt_one_comap, map_sub, map_pow, h]
  exact hτ.2 _ ((valuation_le_one_comap A' φ x).mp hx)

theorem mem_Ine_comap (h : ∀ z, φ (σ z) = τ (φ z)) (hτ : τ ∈ Ine (F := E') A') :
    σ ∈ Ine (F := E) (A'.comap φ.toRingHom) := by
  refine ⟨mem_Dec_comap A' φ h hτ.1, fun x hx => ?_⟩
  rw [valuation_lt_one_comap, map_sub, h]
  exact hτ.2 _ ((valuation_le_one_comap A' φ x).mp hx)

end Transport

variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω'] [Algebra E E']

theorem exists_conj (φ : Ω ≃+* Ω') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    (τ : G E' Ω') : ∃ σ : G E Ω, ∀ z, φ (σ z) = τ (φ z) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (φ.trans τ.toRingEquiv).trans φ.symm) fun x => ?_, fun z => ?_⟩
  · show φ.symm (τ (φ (algebraMap E Ω x))) = algebraMap E Ω x
    rw [hφ, AlgEquiv.commutes, ← hφ, φ.symm_apply_apply]
  · show φ (φ.symm (τ (φ z))) = τ (φ z)
    exact φ.apply_symm_apply _

theorem isPlaceOver_comap [NumberField E] [NumberField E'] (φ : Ω ≃+* Ω')
    (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) {A' : ValuationSubring Ω'}
    (hA : IsPlaceOver A' w) : IsPlaceOver (A'.comap φ.toRingHom) v := by
  intro x
  rw [valuation_lt_one_comap, hφ, ← hwv, Ideal.mem_comap, ← hA (algebraMap (𝓞 E) (𝓞 E') x)]
  rfl

theorem normV_eq_pow [NumberField E] [NumberField E'] {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) :
    normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

end GlobalTheory.ArtinTransport

namespace GlobalTheory.ArtinTransport

theorem chi_artin_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] [Algebra E E'] (φ : Ω ≃+* Ω'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x)) → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω), (∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ) → ∀ (B : Type) [CommGroup B] (χ : GlobalTheory.HeckeGal.Gab E Ω →* B) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')), w.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = v.asIdeal → (∀ x, Formalism.L2.Host.IsUnitAt v x → χ (art (Neutral.B1.localIdele E v x)) = 1) → (∀ x, Formalism.L2.Host.IsUnitAt w x → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = 1) ∧ ∀ x ϖ, Formalism.L2.Host.IsUnifAt w x → Formalism.L2.Host.IsUnifAt v ϖ → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = χ (art (Neutral.B1.localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers E) := by
  intro E Ω _ _ _ _ _ E' Ω' _ _ _ _ _ _ φ hφ art art' ha ha' ρ hρ B _ χ v w hwv hχ
  obtain ⟨A', hA'⟩ := exists_isPlaceOver (F := E') Ω' w
  have hA : IsPlaceOver (A'.comap φ.toRingHom) v := isPlaceOver_comap φ hφ hwv hA'

  have hI : ∀ ι ∈ Ine (F := E) (A'.comap φ.toRingHom), χ (toAb E Ω ι) = 1 := by
    intro ι hι
    obtain ⟨u, hu, e⟩ := (ha.ine v _ hA (toAb E Ω ι)).mpr ⟨ι, hι, rfl⟩
    rw [← e]
    exact hχ u hu
  refine ⟨fun x hx => ?_, fun x ϖ hx hϖ => ?_⟩
  · obtain ⟨τ, hτ, e⟩ := (ha'.ine w A' hA' _).mp ⟨x, hx, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_conj φ hφ τ
    rw [← e, hρ τ σ hσ]
    exact hI σ (mem_Ine_comap A' φ hσ hτ)
  · obtain ⟨τ, hτ, e⟩ := (ha'.frob w A' hA' _).mp ⟨x, hx, rfl⟩
    obtain ⟨σ₀, hσ₀, e₀⟩ := (ha.frob v _ hA _).mp ⟨ϖ, hϖ, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_conj φ hφ τ
    have hσi : ∀ z, φ (σ⁻¹ z) = τ⁻¹ (φ z) := by
      intro z
      have h1 : τ (τ⁻¹ (φ z)) = τ (φ (σ⁻¹ z)) := by
        rw [mul_inv_apply, ← hσ, mul_inv_apply]
      exact (τ.injective h1).symm
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hF : IsFrob (F := E) (A'.comap φ.toRingHom) (normV v ^ f) σ := by
      rw [← normV_eq_pow hwv]
      exact isFrob_comap A' φ hσ hτ
    have hm := hI _ (inv_mul_mem_Ine_of_isFrob (GlobalTheory.FrobRestrict.isFrob_pow hσ₀ f) hF)
    rw [← e, hρ _ _ hσi, ← e₀, map_inv, map_inv, map_inv, map_inv, inv_pow, inv_inj]
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at hm
    exact (inv_mul_eq_one.mp hm).symm

end GlobalTheory.ArtinTransport
end
end

section

open NumberField

namespace GlobalTheory

theorem hwAt_conj_swap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) :=
  PI.UnitaryGroupMassFormula.HwConjInf.conjugation_swap

end GlobalTheory
end
