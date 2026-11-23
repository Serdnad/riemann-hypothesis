module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle076
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle030
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.SubmoduleCount

section Abstract

variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]

end Abstract

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D] in
private theorem exists_finite_generators_of_isPrincipalIdealRing [IsPrincipalIdealRing R] :
    ∀ (g : ℕ) (M : Type) [AddCommGroup M] [Module R M] (x : Fin g → M),
      Submodule.span R (Set.range x) = ⊤ →
        ∀ N : Submodule R M, ∃ v : Fin g → M, N = Submodule.span R (Set.range v) := by
  intro g
  induction g with
  | zero =>
    intro M _ _ x hx N
    refine ⟨Fin.elim0, ?_⟩
    have hbot : (⊤ : Submodule R M) = ⊥ := by
      rw [← hx, Set.range_eq_empty, Submodule.span_empty]
    rw [Set.range_eq_empty, Submodule.span_empty, eq_bot_iff, ← hbot]
    exact le_top
  | succ g ih =>
    intro M _ _ x hx N
    set P := Submodule.span R (Set.range (fun i : Fin g => x i.succ)) with hPdef
    let x' : Fin g → P := fun i => ⟨x i.succ, Submodule.subset_span ⟨i, rfl⟩⟩
    have hx' : Submodule.span R (Set.range x') = ⊤ := by
      apply Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      rfl
    obtain ⟨w, hw⟩ := ih P x' hx' (N.comap P.subtype)
    set I : Ideal R := (N ⊔ P).comap (LinearMap.toSpanSingleton R M (x 0)) with hIdef
    set a := Submodule.IsPrincipal.generator I
    have ha : a ∈ I := Submodule.IsPrincipal.generator_mem I
    rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_sup] at ha
    obtain ⟨n, hn, p, hp, hnp⟩ := ha
    refine ⟨Fin.cons n (fun i => (w i : M)), le_antisymm ?_ ?_⟩
    · intro m hm
      have hmtop : m ∈ Submodule.span R (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmtop
      rw [Fin.sum_univ_succ] at hm ⊢
      set q := ∑ i : Fin g, c i.succ • x i.succ with hqdef
      have hq : q ∈ P := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hc0 : c 0 ∈ I := by
        rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
        have := sub_mem (Submodule.mem_sup_left hm : _ ∈ N ⊔ P) (Submodule.mem_sup_right hq : _ ∈ N ⊔ P)
        simpa using this
      rw [← Submodule.IsPrincipal.span_singleton_generator I, Submodule.mem_span_singleton] at hc0
      obtain ⟨t, ht⟩ := hc0
      have hdiff : c 0 • x 0 + q - t • n = q + t • p := by
        rw [← ht, smul_assoc, ← hnp, smul_add]; abel
      have hdP : c 0 • x 0 + q - t • n ∈ P := by
        rw [hdiff]; exact add_mem hq (Submodule.smul_mem _ _ hp)
      have hdN : c 0 • x 0 + q - t • n ∈ N := sub_mem hm (Submodule.smul_mem _ _ hn)
      have hmem : (⟨_, hdP⟩ : P) ∈ Submodule.span R (Set.range w) := hw ▸ hdN
      have hle : Submodule.span R (Set.range w) ≤ (Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M))).comap P.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i.succ, by simp⟩
      have h1 := hle hmem
      rw [Submodule.mem_comap, Submodule.coe_subtype] at h1
      have h2 : t • n ∈ Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M)) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
      simpa using add_mem h1 h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hn
      · have : w i ∈ N.comap P.subtype := hw ▸ Submodule.subset_span ⟨i, rfl⟩
        simpa using this


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.SubmoduleCount.card_submodule_and_hom_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D] (g : ℕ) (x : Fin g → D), Submodule.span L.O (Set.range x) = ⊤ → Nat.card (Submodule L.O D) ≤ Nat.card D ^ g ∧ ∀ (D' : Type) [AddCommGroup D'] [Module L.O D'] [Finite D'], Nat.card (D →ₗ[L.O] D') ≤ Nat.card D' ^ g := by
  intro F _ _ _ _ _ E _ _ _ L D _ _ _ g x hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation F).integer
  haveI : IsPrincipalIdealRing L.O := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  refine ⟨?_, fun D' _ _ _ => ?_⟩
  · have hsurj : Function.Surjective (fun v : Fin g → D => Submodule.span L.O (Set.range v)) := by
      intro N
      obtain ⟨v, hv⟩ := exists_finite_generators_of_isPrincipalIdealRing g D x hx N
      exact ⟨v, hv.symm⟩
    calc Nat.card (Submodule L.O D) ≤ Nat.card (Fin g → D) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card D ^ g := by simp [Nat.card_fun]
  · have hinj : Function.Injective (fun f : D →ₗ[L.O] D' => fun i => f (x i)) := by
      intro f f' h
      exact LinearMap.ext_on_range hx (fun i => congrFun h i)
    calc Nat.card (D →ₗ[L.O] D') ≤ Nat.card (Fin g → D') := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card D' ^ g := by simp [Nat.card_fun]

end GlobalTheory.SubmoduleCount
end

section

open Matrix Filter Topology

namespace GlobalTheory.ExpStrictUpper

theorem conj_diagonal_eq {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0)
    {τ : ℂ} (hτ : τ ≠ 0) :
    (Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹) * X *
      (Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ)) =
      Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases h : j ≤ i
  · simp [hX i j h]
  · have hij : (i : ℕ) ≤ (j : ℕ) := by
      have := Fin.lt_def.mp (not_le.mp h)
      omega
    have hp : τ ^ (j : ℕ) = τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)) := by
      rw [← pow_add, Nat.add_sub_cancel' hij]
    rw [hp]
    calc (τ ^ (i : ℕ))⁻¹ * X i j * (τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)))
        = ((τ ^ (i : ℕ))⁻¹ * τ ^ (i : ℕ)) * (τ ^ ((j : ℕ) - (i : ℕ)) * X i j) := by ring
      _ = τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hτ), one_mul]

theorem tendsto_scale {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0) :
    Tendsto (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j))
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j)) :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      exact (continuous_pow _).mul continuous_const
  have h0 : (Matrix.of fun i j : Fin m => (0 : ℂ) ^ ((j : ℕ) - (i : ℕ)) * X i j) = 0 := by
    ext i j
    rw [Matrix.of_apply, Matrix.zero_apply]
    by_cases h : j ≤ i
    · rw [hX i j h, mul_zero]
    · have hn : (j : ℕ) - (i : ℕ) ≠ 0 := by
        have := Fin.lt_def.mp (not_le.mp h)
        omega
      rw [zero_pow hn, zero_mul]
  simpa only [h0] using hc.tendsto 0

theorem exp_inj_strictUpper : ∀ (m : ℕ) (X Y : Matrix (Fin m) (Fin m) ℂ),
    (∀ i j, j ≤ i → X i j = 0) → (∀ i j, j ≤ i → Y i j = 0) →
    NormedSpace.exp X = NormedSpace.exp Y → X = Y := by
  intro m X Y hX hY hXY
  obtain ⟨S, hS, hinj⟩ := (GlobalTheory.ExpBallNhds.exp_local_matrix (Fin m)).1
  have h1 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ),
      (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j) ∈ S ∧
        (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * Y i j) ∈ S :=
    nhdsWithin_le_nhds (((tendsto_scale X hX).eventually_mem hS).and
      ((tendsto_scale Y hY).eventually_mem hS))
  have h2 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ≠ 0 := self_mem_nhdsWithin
  have hev := h1.and h2
  obtain ⟨τ, ⟨hxS, hyS⟩, hτ⟩ := hev.exists
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ) with hD
  set E : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹ with hE
  have hDE : D * E = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (pow_ne_zero _ hτ)
  have hED : E * D = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (pow_ne_zero _ hτ)
  have hU : IsUnit D := ⟨⟨D, E, hDE, hED⟩, rfl⟩
  have hinv : D⁻¹ = E := Matrix.inv_eq_left_inv hED
  have hexp : ∀ Z : Matrix (Fin m) (Fin m) ℂ,
      NormedSpace.exp (E * Z * D) = E * NormedSpace.exp Z * D := by
    intro Z
    rw [← hinv]
    exact Matrix.exp_conj' D Z hU
  have hxS' : E * X * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq X hX hτ]
    exact hxS
  have hyS' : E * Y * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq Y hY hτ]
    exact hyS
  have key : E * X * D = E * Y * D :=
    hinj hxS' hyS' (by rw [hexp, hexp, hXY])
  calc X = (D * E) * X * (D * E) := by rw [hDE, one_mul, mul_one]
    _ = D * (E * X * D) * E := by simp only [mul_assoc]
    _ = D * (E * Y * D) * E := by rw [key]
    _ = (D * E) * Y * (D * E) := by simp only [mul_assoc]
    _ = Y := by rw [hDE, one_mul, mul_one]

end GlobalTheory.ExpStrictUpper
end

section

open Matrix Finset Real

namespace GlobalTheory

private theorem trace_sub_one_pow_eq_zero_of_trace_pow_eq (K : Type) [Field K] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, 1 ≤ j → j ≤ n → (A ^ j).trace = n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((A - 1) ^ k).trace = 0 := by
  have hc : Commute A (-1 : Matrix (Fin n) (Fin n) K) := (Commute.one_right A).neg_right
  have hall : ∀ m ∈ Finset.range (k + 1), (A ^ m).trace = (n : K) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · exact h m hm0 (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hkn)
  rw [sub_eq_add_neg, hc.add_pow, Matrix.trace_sum]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      (A ^ m * (-1 : Matrix (Fin n) (Fin n) K) ^ (k - m) * (k.choose m : Matrix (Fin n) (Fin n) K)).trace
        = (n : K) * ((1 : K) ^ m * (-1 : K) ^ (k - m) * (k.choose m : K)) := by
    intro m hm
    have e1 : (-1 : Matrix (Fin n) (Fin n) K) ^ (k - m) = ((-1 : K) ^ (k - m)) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [← neg_one_smul K (1 : Matrix (Fin n) (Fin n) K), smul_pow, one_pow]
    have e2 : ((k.choose m : ℕ) : Matrix (Fin n) (Fin n) K) = (k.choose m : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_one]
    rw [e1, e2, Matrix.mul_smul, mul_one, Matrix.mul_smul, mul_one, smul_smul,
      Matrix.trace_smul, hall m hm, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
  simp [Nat.pos_iff_ne_zero.mp hk1]

theorem unipotent_of_trace_pow_eq_size (K : Type) [Field K] [CharZero K] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, 1 ≤ j → j ≤ n → (A ^ j).trace = n) :
    A.charpoly = (Polynomial.X - 1) ^ n ∧ (A - 1) ^ n = 0 := by
  have htr : ∀ k, 1 ≤ k → k ≤ n → ((A - 1) ^ k).trace = 0 :=
    fun k hk1 hkn => trace_sub_one_pow_eq_zero_of_trace_pow_eq K n A h k hk1 hkn
  have hB : IsNilpotent (A - 1) :=
    ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow n (A - 1) htr
  have hchar : (A - 1).charpoly = Polynomial.X ^ n := by
    have := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hB).eq_zero
    simpa [sub_eq_zero] using this
  refine ⟨?_, ?_⟩
  · have e : A - 1 - Matrix.scalar (Fin n) (-1 : K) = A := by
      rw [map_neg, map_one, sub_neg_eq_add, sub_add_cancel]
    have hs := Matrix.charpoly_sub_scalar (A - 1) (-1 : K)
    rw [e, hchar] at hs
    rw [hs, Polynomial.pow_comp, Polynomial.X_comp, map_neg, map_one, ← sub_eq_add_neg]
  · have := Matrix.aeval_self_charpoly (A - 1)
    rwa [hchar, map_pow, Polynomial.aeval_X] at this

end GlobalTheory
end

section

open MeasureTheory NumberField Finset

namespace GlobalTheory

theorem log_pow_div_factorial_le_rpow_of_one_le {u s : ℝ} (hu : 1 ≤ u) (hs : 1 ≤ s) (r : ℕ) :
    Real.log u ^ r / (r.factorial : ℝ) ≤ u ^ s := by
  have h := Real.pow_div_factorial_le_exp (Real.log u) (Real.log_nonneg hu) r
  rw [Real.exp_log (by linarith)] at h
  refine h.trans ?_
  calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
    _ ≤ u ^ s := Real.rpow_le_rpow_of_exponent_le hu hs

theorem classNumber_mul_regulator_le_sqrt_discr_rpow :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ s : ℝ, 1 < s →
      (classNumber K : ℝ) * Units.regulator K ≤
        Real.sqrt |(discr K : ℝ)| ^ s * (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ hK s hs
  classical
  set Y : ℝ := Real.sqrt |(discr K : ℝ)| with hY
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hfin : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}.Finite := by
    refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊Y⌋₊).subset fun I hI => ?_
    exact Nat.le_floor hI.2
  set T := hfin.toFinset with hT
  have hmem : ∀ I, I ∈ T ↔ I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y := fun I => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  let cls : Ideal (𝓞 K) → ClassGroup (𝓞 K) := fun I =>
    if h : I ∈ nonZeroDivisors (Ideal (𝓞 K)) then ClassGroup.mk0 ⟨I, h⟩ else 1
  let g : Ideal (𝓞 K) → ℝ := fun I =>
    Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ)
  have h1 : ∀ C : ClassGroup (𝓞 K),
      Units.regulator K ≤ ∑ I ∈ T.filter (fun I => cls I = C), g I := by
    intro C
    refine GlobalTheory.T.regulator_le_sum_small_ideals_in_class K hK C _ fun I => ?_
    rw [Finset.mem_filter, hmem]
    constructor
    · rintro ⟨⟨h0, hle⟩, hc⟩
      have hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero h0
      refine ⟨hI, ?_, hle⟩
      simpa only [cls, dif_pos hI] using hc
    · rintro ⟨hI, hc, hle⟩
      refine ⟨⟨nonZeroDivisors.ne_zero hI, hle⟩, ?_⟩
      simpa only [cls, dif_pos hI] using hc
  have h2 : ∀ I ∈ T, g I ≤ Y ^ s * (Ideal.absNorm I : ℝ) ^ (-s) := by
    intro I hI
    obtain ⟨h0, hle⟩ := (hmem I).1 hI
    have hN : (0 : ℝ) < Ideal.absNorm I := by
      have : Ideal.absNorm I ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hu : 1 ≤ Y / Ideal.absNorm I := (one_le_div hN).2 hle
    refine (log_pow_div_factorial_le_rpow_of_one_le hu hs.le _).trans (le_of_eq ?_)
    rw [Real.div_rpow hY0 hN.le, Real.rpow_neg hN.le, div_eq_mul_inv]
  calc (classNumber K : ℝ) * Units.regulator K
      = ∑ _C : ClassGroup (𝓞 K), Units.regulator K := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, classNumber]
    _ ≤ ∑ C : ClassGroup (𝓞 K), ∑ I ∈ T.filter (fun I => cls I = C), g I :=
        Finset.sum_le_sum fun C _ => h1 C
    _ = ∑ I ∈ T, g I := Finset.sum_fiberwise T cls g
    _ ≤ ∑ I ∈ T, Y ^ s * (Ideal.absNorm I : ℝ) ^ (-s) := Finset.sum_le_sum h2
    _ = Y ^ s * ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) := (Finset.mul_sum _ _ _).symm
    _ ≤ Y ^ s * (s / (s - 1)) ^ Module.finrank ℚ K :=
        mul_le_mul_of_nonneg_left
          (GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound K s hs T fun I hI => ((hmem I).1 hI).1) (Real.rpow_nonneg hY0 s)

end GlobalTheory
end
