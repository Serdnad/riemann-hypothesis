module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowDescentCyclotomic
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle038
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle036
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle039
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle040
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle041
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle042
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle029
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open NumberField

theorem _root_.GlobalTheory.T.exists_pow_descent_cyclotomic' : ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u → ∃ v : E, v ^ (l ^ r) = u := by
  first | exact @GlobalTheory.exists_pow_descent_cyclotomic | exact GlobalTheory.exists_pow_descent_cyclotomic | (intros; apply GlobalTheory.exists_pow_descent_cyclotomic <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.addValuation_nonneg_ringOfIntegers_numberField : ∀ (L : Type) [Field L] [NumberField L] (v : AddValuation L (WithTop ℤ)) (a : 𝓞 L), 0 ≤ v (a : L) := by
  first | exact @GlobalTheory.addValuation_nonneg_of_ringOfIntegers | exact GlobalTheory.addValuation_nonneg_of_ringOfIntegers | (intros; apply GlobalTheory.addValuation_nonneg_of_ringOfIntegers <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.isTotallyComplex_of_root_quadratic_neg_disc : ∀ (K : Type) [Field K] [NumberField K] (x : K) (a b : ℤ), x ^ 2 + (a : K) * x + (b : K) = 0 →
    a ^ 2 < 4 * b → NumberField.IsTotallyComplex K := by
  first | exact @GlobalTheory.totallyComplex_of_root_quadratic_neg_disc | exact GlobalTheory.totallyComplex_of_root_quadratic_neg_disc | (intros; apply GlobalTheory.totallyComplex_of_root_quadratic_neg_disc <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.isTotallyComplex_of_primitiveRoot_three_le : ∀ (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ), IsPrimitiveRoot ζ m → 3 ≤ m →
    NumberField.IsTotallyComplex K := by
  first | exact @GlobalTheory.tcroot | exact GlobalTheory.tcroot | (intros; apply GlobalTheory.tcroot <;> assumption)
end

section


theorem _root_.GlobalTheory.T.padicInt_continuous_hom_normalize_one : ∀ {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ_[p]), Continuous χ → (∀ g h, χ (g * h) = χ g + χ h) → ∀ (g₀ : G), χ g₀ ≠ 0 → ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧ (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 := by
  first | exact @GlobalTheory.padicInt_hom_normalize | exact GlobalTheory.padicInt_hom_normalize | (intros; apply GlobalTheory.padicInt_hom_normalize <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_padicInt_of_compatible_zmod_pow' : ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)), (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) → ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  first | exact @GlobalTheory.exists_padicInt_of_compatible_zmod_pow | exact GlobalTheory.exists_padicInt_of_compatible_zmod_pow | (intros; apply GlobalTheory.exists_padicInt_of_compatible_zmod_pow <;> assumption)
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem isLocallyConstant_orbit_of_inv_pow_character :
    ∀ {p : ℕ} {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ),
    (∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))) →
    ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ (m : M) (N : ℕ), (p : O) ^ N • m = 0 →
    IsLocallyConstant (fun g => ρ g m) := by
  intro p O _ G _ _ ε hε e M _ _ ρ hρ m N hm
  have key : ∀ g g' : G,
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O) =
        Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g' : Oˣ) : O) → ρ g m = ρ g' m := by
    intro g g' h
    have h1 : Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g) ^ e : Oˣ) : O) =
        Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g') ^ e : Oˣ) : O) := by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, h]
    rw [hρ, hρ]
    generalize (ε g) ^ e = u at h1 ⊢
    generalize (ε g') ^ e = v at h1 ⊢
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    have h2 : ((v⁻¹ : Oˣ) : O) - ((u⁻¹ : Oˣ) : O) =
        (((u⁻¹ : Oˣ) : O) * ((v⁻¹ : Oˣ) : O) * b) * (p : O) ^ N := by
      rw [mul_assoc, hb]
      have hu : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
      have hv : ((v⁻¹ : Oˣ) : O) * (v : O) = 1 := v.inv_mul
      linear_combination (-((v⁻¹ : Oˣ) : O)) * hu + ((u⁻¹ : Oˣ) : O) * hv
    symm
    rw [← sub_eq_zero, ← sub_smul, h2, mul_smul, hm, smul_zero]
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  obtain ⟨U, hU, hg, hc⟩ := ((IsLocallyConstant.iff_exists_open _).1 (hε N)) g₀
  exact ⟨U, hU, hg, fun g hgU => key g g₀ (hc g hgU)⟩

end GlobalTheory.ShapeNeg
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  first | exact @GlobalTheory.adicCompletion_valuationRing_props | exact GlobalTheory.adicCompletion_valuationRing_props | (intros; apply GlobalTheory.adicCompletion_valuationRing_props <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_adic_coordinates_of_basis_mod_p : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  first | exact @GlobalTheory.AdicCoord.exists_coord | exact GlobalTheory.AdicCoord.exists_coord | (intros; apply GlobalTheory.AdicCoord.exists_coord <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_unit_frobenius_iterate_product_eq : ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A → ∀ (φ : A →+* A) (u : A), IsUnit u → (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) → ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  first | exact @GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | exact GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | (intros; apply GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq <;> assumption)
end

section

open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Chevalley

end GlobalTheory.Chevalley

namespace GlobalTheory.Chevalley

end GlobalTheory.Chevalley

namespace GlobalTheory.Chevalley

open TensorProduct Polynomial IsLocalRing in
private theorem isArtinian_quotient_maximalIdeal_pow_succ_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (n : ℕ) : IsArtinian B (M ⧸ (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M))) := by
  have hmin : maximalIdeal B ∈ (maximalIdeal B ^ (n + 1)).minimalPrimes := by
    refine ⟨⟨(maximalIdeal.isMaximal B).isPrime, Ideal.pow_le_self (Nat.succ_ne_zero n)⟩, ?_⟩
    rintro q ⟨hq, hle⟩ -
    exact hq.le_of_pow_le hle
  have : IsArtinianRing (B ⧸ maximalIdeal B ^ (n + 1)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  exact isArtinian_of_surjective_algebraMap
    (Ideal.Quotient.mk_surjective (I := maximalIdeal B ^ (n + 1)))

open TensorProduct Polynomial IsLocalRing in
private theorem mem_of_forall_mem_sup_maximalIdeal_pow_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (K : Submodule B M) (x : M)
    (h : ∀ n, x ∈ K ⊔ maximalIdeal B ^ n • (⊤ : Submodule B M)) : x ∈ K := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⧸ K) (maximalIdeal B)
    (maximalIdeal.isMaximal B).ne_top
  have hx : K.mkQ x ∈ ⨅ n, maximalIdeal B ^ n • (⊤ : Submodule B (M ⧸ K)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h n)
    have hmap : (maximalIdeal B ^ n • (⊤ : Submodule B M)).map K.mkQ ≤
        maximalIdeal B ^ n • (⊤ : Submodule B (M ⧸ K)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    have hzq := hmap (Submodule.mem_map_of_mem hz)
    have hy0 : K.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hy
    rw [map_add (f := _), hy0, zero_add]
    exact hzq
  rw [hbot, Submodule.mem_bot] at hx
  exact (Submodule.Quotient.mk_eq_zero K).mp hx

open TensorProduct Polynomial IsLocalRing in
private theorem exists_limit_of_sub_mem_maximalIdeal_pow_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M]
    [Module B M] [Module.Finite B M] (s : ℕ) (y : ℕ → M)
    (hy : ∀ k, y (k + 1) - y k ∈ maximalIdeal B ^ (s + k) • (⊤ : Submodule B M)) :
    ∃ x, ∀ k, x - y k ∈ maximalIdeal B ^ (s + k) • (⊤ : Submodule B M) := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := B) (M := M)
  have hlift : ∀ (J : Ideal B) (z : M), z ∈ J • (⊤ : Submodule B M) →
      ∃ c : Fin m → B, (∀ l, c l ∈ J) ∧ ∑ l, c l • g l = z := by
    intro J z hz
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ha, (Finsupp.sum_fintype a (fun i c => c • g i) fun i => zero_smul B (g i)).symm⟩
  choose c hcI hcsum using fun k => hlift _ _ (hy k)
  obtain ⟨S, hS⟩ : ∃ S : Fin m → ℕ → B, ∀ l n, S l n = ∑ k ∈ Finset.range n, c k l :=
    ⟨_, fun _ _ => rfl⟩
  have hSdiff : ∀ l n p, n ≤ p → S l p - S l n ∈ maximalIdeal B ^ (s + n) := by
    intro l n p hnp
    rw [hS, hS, ← Finset.sum_range_add_sum_Ico _ hnp, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk' := (Finset.mem_Ico.mp hk).1
    exact Ideal.pow_le_pow_right (by omega) (hcI k l)
  have hprec : IsPrecomplete (maximalIdeal B) B := inferInstance
  have hlim : ∀ l, ∃ L, ∀ n, S l n - L ∈ maximalIdeal B ^ (s + n) := by
    intro l
    obtain ⟨L, hL⟩ := hprec.prec (f := S l) (fun {a b} hab => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, Submodule.neg_mem_iff]
      exact Ideal.pow_le_pow_right (by omega) (hSdiff l a b hab))
    refine ⟨L, fun n => ?_⟩
    have h1 := hL (s + n)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := hSdiff l n (s + n) (by omega)
    have e : S l n - L = (S l (s + n) - L) - (S l (s + n) - S l n) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (by omega) h1) h2
  choose L hL using hlim
  refine ⟨y 0 + ∑ l, L l • g l, fun k => ?_⟩
  have htel : ∑ l, S l k • g l = y k - y 0 := by
    simp only [hS, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp_rw [hcsum]
    exact Finset.sum_range_sub y k
  have e : y 0 + ∑ l, L l • g l - y k = -∑ l, (S l k - L l) • g l := by
    simp only [sub_smul, Finset.sum_sub_distrib, htel]
    abel
  rw [e, Submodule.neg_mem_iff]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem_smul (hL l k) Submodule.mem_top


open TensorProduct Polynomial IsLocalRing in
theorem _root_.GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed :
    ∀ (B M ι : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M] [Module B M] [Module.Finite B M]
      (K : ι → Submodule B M), Nonempty ι → Directed (· ≥ ·) K → (⨅ i, K i) = ⊥ →
      ∀ N : ℕ, ∃ i, K i ≤ maximalIdeal B ^ N • (⊤ : Submodule B M) := by
  intro B M ι _ _ _ _ _ _ _ K hne hdir hbot N
  haveI := hne
  have hmin : ∀ n, ∃ j, ∀ i, K j ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) ≤
      K i ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n
    haveI := isArtinian_quotient_maximalIdeal_pow_succ_smul B M n
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ :=
      (wellFounded_lt (α := Submodule B (M ⧸ (maximalIdeal B ^ (n + 1) •
        (⊤ : Submodule B M))))).has_min
        (Set.range fun i => (K i).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ)
        (Set.range_nonempty _)
    refine ⟨j, fun i => ?_⟩
    obtain ⟨k, hki, hkj⟩ := hdir i j
    have hle := Submodule.map_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hkj
    have heq : (K k).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ =
        (K j).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ := by
      by_contra hne'
      exact hj _ ⟨k, rfl⟩ (lt_of_le_of_ne hle hne')
    have hji := Submodule.map_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hki
    rw [heq] at hji
    have hc := Submodule.comap_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hji
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ] at hc
    rwa [sup_comm (K j), sup_comm (K i)]
  choose j hj using hmin
  by_contra hcon
  push_neg at hcon
  have hE_step : ∀ n, ∀ x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M),
      ∃ x' ∈ K (j (n + 1)) ⊔ maximalIdeal B ^ (n + 1 + 1) • (⊤ : Submodule B M),
        x - x' ∈ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hj n (j (n + 1)) hx)
    exact ⟨a, Submodule.mem_sup_left ha, by simpa using hb⟩
  have hE_anti : ∀ n, K (j (n + 1)) ⊔ maximalIdeal B ^ (n + 1 + 1) • (⊤ : Submodule B M) ≤
      K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := fun n =>
    (hj (n + 1) (j n)).trans
      (sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) _)
  have hE_mono : ∀ n p, n ≤ p → K (j p) ⊔ maximalIdeal B ^ (p + 1) • (⊤ : Submodule B M) ≤
      K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n p hnp
    induction hnp with
    | refl => exact le_rfl
    | step _ ih => exact (hE_anti _).trans ih
  have hE_zero : ∀ x, (∀ n, x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)) →
      x = 0 := by
    intro x hx
    have hmem : x ∈ ⨅ i, K i := Submodule.mem_iInf _ |>.mpr fun i =>
      mem_of_forall_mem_sup_maximalIdeal_pow_smul B M (K i) x fun n => by
        have hle : K i ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) ≤
            K i ⊔ maximalIdeal B ^ n • (⊤ : Submodule B M) :=
          sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) _
        exact hle (hj n i (hx n))
    rwa [hbot, Submodule.mem_bot] at hmem
  have hnot : ¬ K (j N) ⊔ maximalIdeal B ^ (N + 1) • (⊤ : Submodule B M) ≤
      maximalIdeal B ^ (N + 1) • (⊤ : Submodule B M) := fun h =>
    hcon (j N) ((le_sup_left.trans h).trans
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))))
  obtain ⟨x0, hx0, hx0P⟩ := SetLike.not_le_iff_exists.mp hnot
  choose f hf1 hf2 using hE_step
  let y : (k : ℕ) → {x // x ∈ K (j (N + k)) ⊔ maximalIdeal B ^ (N + k + 1) • (⊤ : Submodule B M)} :=
    fun k => Nat.rec (motive := fun k =>
        {x // x ∈ K (j (N + k)) ⊔ maximalIdeal B ^ (N + k + 1) • (⊤ : Submodule B M)})
      ⟨x0, hx0⟩ (fun k z => ⟨f (N + k) z.1 z.2, hf1 _ _ _⟩) k
  have hy_succ : ∀ k, (y (k + 1)).1 = f (N + k) (y k).1 (y k).2 := fun k => rfl
  obtain ⟨x, hx⟩ := exists_limit_of_sub_mem_maximalIdeal_pow_smul B M (N + 1)
    (fun k => (y k).1) (fun k => by
      have e : N + 1 + k = N + k + 1 := by omega
      rw [hy_succ, e, ← neg_sub, Submodule.neg_mem_iff]
      exact hf2 (N + k) (y k).1 (y k).2)
  have hxE : ∀ n, x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n
    have e : N + 1 + n = N + n + 1 := by omega
    have hd := hx n
    rw [e] at hd
    have hk := Submodule.add_mem _ (y n).2 (Submodule.mem_sup_right hd)
    rw [add_sub_cancel] at hk
    exact hE_mono n (N + n) (by omega) hk
  have hx0' := hE_zero x hxE
  apply hx0P
  have h0 := hx 0
  rw [hx0', zero_sub, Submodule.neg_mem_iff] at h0
  exact h0

end GlobalTheory.Chevalley
end

section

noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT


open scoped PowerSeries.WithPiTopology in
theorem exists_algHom_X_add_C {O : Type} [CommRing O] (I : Ideal O) [h : IsAdicComplete I O]
    (c : O) (hc : c ∈ I) : ∃ t : O⟦X⟧ →ₐ[O] O⟦X⟧, t X = X + C c := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval c := WithIdeal.isTopologicallyNilpotent_of_mem hc
  have hC : PowerSeries.HasEval (C c : O⟦X⟧) :=
    ha.map (φ := (C : O →+* O⟦X⟧)) PowerSeries.WithPiTopology.continuous_C
  have : IsLinearTopology O⟦X⟧ O⟦X⟧ :=
    inferInstance
  have hX : PowerSeries.HasEval (X + C c : O⟦X⟧) := PowerSeries.HasEval.X.add hC
  have : ContinuousSMul O O⟦X⟧ := ⟨by
    have : (fun p : O × O⟦X⟧ => p.1 • p.2) = fun p => C p.1 * p.2 := by
      funext p; rw [smul_eq_C_mul]
    rw [this]
    exact (PowerSeries.WithPiTopology.continuous_C.comp continuous_fst).mul continuous_snd⟩
  refine ⟨PowerSeries.aeval hX, ?_⟩
  rw [PowerSeries.coe_aeval, PowerSeries.eval₂_X]

theorem exists_algEquiv_X_add_C : ∀ {O : Type} [CommRing O] (I : Ideal O) [IsAdicComplete I O] (c : O), c ∈ I → ∃ lev : O⟦X⟧ ≃ₐ[O] O⟦X⟧, lev X = X + C c := by
  intro O _ I _ c hc
  obtain ⟨s, hs⟩ := exists_algHom_X_add_C I c hc
  obtain ⟨t, ht⟩ := exists_algHom_X_add_C I (-c) (neg_mem hc)
  have hC : ∀ (u : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O), u (C a) = C a := fun u a => u.commutes a
  have h1 : (s.comp t) X = X := by
    rw [AlgHom.comp_apply, ht, map_add (f := _), hs, hC, map_neg]; ring
  have h2 : (t.comp s) X = X := by
    rw [AlgHom.comp_apply, hs, map_add (f := _), ht, hC, map_neg]; ring
  exact ⟨AlgEquiv.ofAlgHom s t (algHom_ext_X _ _ h1 (by rw [h1])) (algHom_ext_X _ _ h2 (by rw [h2])), hs⟩

end GlobalTheory.NB.LT
end
end
