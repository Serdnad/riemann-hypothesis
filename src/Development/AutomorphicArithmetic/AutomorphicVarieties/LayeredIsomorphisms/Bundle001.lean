module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle001
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Formalism.GaloisCohomology.Statement
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem act_root {K : Type} [Field K] {N : ℕ} [NeZero N] {ζ x : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) (hx : x ^ N = 1) : σ x = x ^ a := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hσ, pow_right_comm]

private theorem exists_pow {N : ℕ} [NeZero N] {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N)
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) : ∃ a : ℕ, τ ζ = ζ ^ a := by
  obtain ⟨i, -, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  exact ⟨i, h.symm⟩

private theorem mem_fix {E K : Type} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] (j : E →ₐ[ℚ] K)
    (τ : K ≃ₐ[ℚ] K) : τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ x : E, τ (j x) = j x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x => h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) (hb : A.ker b) : A.ker a := by
  obtain ⟨u, hu, e⟩ := hb
  exact ⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩

private theorem exists_res {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Normal ℚ K]
    (f : K →ₐ[ℚ] L) (σ : L ≃ₐ[ℚ] L) : ∃ τ : K ≃ₐ[ℚ] K, ∀ x : K, σ (f x) = f (τ x) := by
  letI : Algebra K L := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact ⟨σ.restrictNormal K, fun x => (σ.restrictNormal_commutes K x).symm⟩

private theorem equiv_of_range {F L L' Ω : Type} [Field F] [Field L] [Field L'] [Field Ω] [Algebra F L]
    [Algebra F L'] [Algebra F Ω] (g : L →ₐ[F] Ω) (g' : L' →ₐ[F] Ω) (e : g.fieldRange = g'.fieldRange) :
    Nonempty (L ≃+* L') :=
  ⟨((g.equivFieldRange.trans (IntermediateField.equivOfEq e)).trans g'.equivFieldRange.symm).toRingEquiv⟩

private theorem equiv_of_fix {L L' Ω : Type} [Field L] [Field L'] [Field Ω] [Algebra ℚ L] [Algebra ℚ L']
    [Algebra ℚ Ω] [IsGalois ℚ Ω] (g : L →ₐ[ℚ] Ω) (g' : L' →ₐ[ℚ] Ω)
    (h : ∀ σ : Ω ≃ₐ[ℚ] Ω, (∀ x, σ (g x) = g x) ↔ ∀ x, σ (g' x) = g' x) : Nonempty (L ≃+* L') := by
  have e : g.fieldRange = g'.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup g'.fieldRange]
    congr 1
    ext σ
    rw [mem_fix, mem_fix, h]
  exact equiv_of_range g g' e

theorem UpperTheory.V.Win.abiso :
    ∀ (A : AbF) (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'],
      IsAbField A L → IsAbField A L' → Nonempty (L ≃+* L') := by
  intro A L L' _ _ _ _ hL hL'
  obtain ⟨N, hN, i, ζ, hm, hζ, H0⟩ := hL
  obtain ⟨N', hN', j, ζ', hm', hζ', H⟩ := hL'
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ _
  haveI : IsAbelianGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isAbelianGalois {N'} ℚ _
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := by
    first
      | exact @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
      | convert @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
  let f : CyclotomicField N ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f' : CyclotomicField N' ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine equiv_of_fix (f.comp i) (f'.comp j) fun σ => ?_
  obtain ⟨τ, hσ⟩ := exists_res f σ
  obtain ⟨τ', hσ'⟩ := exists_res f' σ
  obtain ⟨a, hτ⟩ := exists_pow hζ τ
  obtain ⟨b, hb⟩ := exists_pow hζ' τ'
  obtain ⟨k, hk⟩ := id hm
  obtain ⟨k', hk'⟩ := id hm'
  have hω : IsPrimitiveRoot (f (ζ ^ k)) A.m :=
    (hζ.pow (NeZero.pos N) (by rw [hk, mul_comm])).map_of_injective f.injective
  have hω' : IsPrimitiveRoot (f' (ζ' ^ k')) A.m :=
    (hζ'.pow (NeZero.pos N') (by rw [hk', mul_comm])).map_of_injective f'.injective
  have h1 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ a := by
    rw [hσ, map_pow τ, hτ, pow_right_comm, map_pow f]
  have h2 : σ (f' (ζ' ^ k')) = f' (ζ' ^ k') ^ b := by
    rw [hσ', map_pow τ', hb, pow_right_comm, map_pow f']
  have h3 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ b :=
    act_root hω' (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) h2 hω.pow_eq_one
  have hab : a ≡ b [MOD A.m] := by
    have := ((hω.isOfFinOrder A.pos.ne').pow_eq_pow_iff_modEq).1 (h1.symm.trans h3)
    rwa [← hω.eq_orderOf] at this
  have h4 : A.ker a ↔ A.ker b := ⟨ker_congr A hab.symm, ker_congr A hab⟩
  have e1 : (∀ x, σ ((f.comp i) x) = (f.comp i) x) ↔ ∀ x, τ (i x) = i x := by
    refine forall_congr' fun x => ?_
    show σ (f (i x)) = f (i x) ↔ _
    rw [hσ]
    exact f.injective.eq_iff
  have e2 : (∀ x, σ ((f'.comp j) x) = (f'.comp j) x) ↔ ∀ x, τ' (j x) = j x := by
    refine forall_congr' fun x => ?_
    show σ (f' (j x)) = f' (j x) ↔ _
    rw [hσ']
    exact f'.injective.eq_iff
  rw [e1, e2, H0 τ a hτ, H τ' b hb, h4]
end

section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem nonempty_ringEquiv_of_isCyclotomic_finrank_eq (l j k k' : ℕ) (hl : l.Prime) (hk : k ≤ k') (L₀ L₀' L₁ L₁' : Type)
    [Field L₀] [Field L₀'] [Field L₁] [Field L₁'] [Algebra L₀ L₁] [Algebra L₀' L₁']
    (e : L₀ ≃+* L₀') (h₁ : IsCyclotomicExtension {l ^ k} L₀ L₁)
    (h₁' : IsCyclotomicExtension {l ^ k'} L₀' L₁')
    (d₁ : Module.finrank L₀ L₁ = l ^ j) (d₁' : Module.finrank L₀' L₁' = l ^ j) :
    Nonempty (L₁ ≃+* L₁') := by
  haveI : NeZero (l ^ k') := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))) (l ^ k) :=
    (IsCyclotomicExtension.zeta_spec (l ^ k') L₀' L₁').pow (pow_pos hl.pos _)
      (by rw [← pow_add, Nat.sub_add_cancel hk])
  letI : Algebra L₀ L₀' := e.toRingHom.toAlgebra
  letI : Algebra L₀ L₁' := ((algebraMap L₀' L₁').comp e.toRingHom).toAlgebra
  haveI : IsScalarTower L₀ L₀' L₁' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h1 : Module.finrank L₀ L₀' = 1 := by
    rw [← (AlgEquiv.ofRingEquiv (R := L₀) (A₁ := L₀) (A₂ := L₀') (f := e)
      (fun _ => rfl)).toLinearEquiv.finrank_eq, Module.finrank_self]
  have h2 : Module.finrank L₀ L₁' = l ^ j := by
    rw [← Module.finrank_mul_finrank L₀ L₀' L₁', h1, one_mul, d₁']
  haveI : FiniteDimensional L₀ L₁' :=
    Module.finite_of_finrank_pos (by rw [h2]; exact pow_pos hl.pos _)
  haveI : Algebra.IsIntegral L₀ L₁' := Algebra.IsIntegral.of_finite L₀ L₁'
  haveI := hζ.intermediateField_adjoin_isCyclotomicExtension L₀
  let φ := IsCyclotomicExtension.algEquiv {l ^ k} L₀ L₁
    (IntermediateField.adjoin L₀ {IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))})
  have htop : IntermediateField.adjoin L₀
      {IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))} = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [IntermediateField.finrank_top', ← φ.toLinearEquiv.finrank_eq, d₁, h2])
  exact ⟨φ.toRingEquiv.trans ((IntermediateField.equivOfEq htop).toRingEquiv.trans
    IntermediateField.topEquiv.toRingEquiv)⟩

theorem UpperTheory.V.Win.layeriso :
    ∀ (l j : ℕ), l.Prime → ∀ (L₀ L₀' L₁ L₁' : Type) [Field L₀] [NumberField L₀] [Field L₀'] [NumberField L₀']
      [Field L₁] [NumberField L₁] [Field L₁'] [NumberField L₁'] [Algebra L₀ L₁] [Algebra L₀' L₁'],
        Nonempty (L₀ ≃+* L₀') → IsLayer l j L₀ L₁ → IsLayer l j L₀' L₁' → Nonempty (L₁ ≃+* L₁') := by
  intro l j hl L₀ L₀' L₁ L₁' _ _ _ _ _ _ _ _ _ _ ⟨e⟩ ⟨⟨k, hk⟩, d⟩ ⟨⟨k', hk'⟩, d'⟩
  rcases le_total k k' with h | h
  · exact nonempty_ringEquiv_of_isCyclotomic_finrank_eq l j k k' hl h L₀ L₀' L₁ L₁' e hk hk' d d'
  · obtain ⟨f⟩ := nonempty_ringEquiv_of_isCyclotomic_finrank_eq l j k' k hl h L₀' L₀ L₁' L₁ e.symm hk' hk d' d
    exact ⟨f.symm⟩
end

section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.kmono :
    ∀ C C' : ℝ, C ≤ C' → LemmaK C → LemmaK C' := by
  intro C C' hCC hK
  unfold LemmaK at hK ⊢
  intro l _ L Ω _ _ _ _ _ D hL hMu e he
  obtain ⟨hf, hb⟩ := hK l L Ω D hL hMu e he
  refine ⟨hf, hb.trans ?_⟩
  unfold kBound
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right
  · apply Real.rpow_le_rpow_of_exponent_le _ hCC
    have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
    have h1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have h2 : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) := by exact_mod_cast hn
    nlinarith
  · rcases Nat.eq_zero_or_pos (discr L).natAbs with h0 | h0
    · rw [h0]
      simp
    · apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by exact_mod_cast h0
      linarith
end

section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.kexp :
    ∀ (CK eps c0 x : ℝ) (e n n0 D : ℕ), 0 < CK → 0 < eps → 0 ≤ c0 → 1 ≤ x → (e : ℝ) ≤ x ^ (eps / (2 * CK)) → n ≤ n0 →
      Real.log (2 * (D : ℝ)) ≤ c0 * x ^ (eps / 4) →
        kBound CK e n D ≤ Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by
  intro CK eps c0 x e n n0 D hCK heps hc0 hx he hn hD
  have hx0 : 0 < x := by linarith
  have hn' : (n : ℝ) ≤ n0 := by exact_mod_cast hn
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn00 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  have hy : 0 ≤ x ^ (eps / (2 * CK)) := Real.rpow_nonneg hx0.le _
  have h1 : 2 * (e : ℝ) * n ≤ (2 * (n0 : ℝ)) * x ^ (eps / (2 * CK)) := by
    have := mul_le_mul he hn' hn0 hy
    nlinarith
  have h2 : (2 * (e : ℝ) * n) ^ CK ≤ (2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2) := by
    calc (2 * (e : ℝ) * n) ^ CK ≤ ((2 * (n0 : ℝ)) * x ^ (eps / (2 * CK))) ^ CK :=
          Real.rpow_le_rpow (by positivity) h1 hCK.le
      _ = (2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2) := by
          rw [Real.mul_rpow (by positivity) hy, ← Real.rpow_mul hx0.le]
          congr 2
          field_simp
  have h3 : x ^ (3 * eps / 4) = x ^ (eps / 2) * x ^ (eps / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  unfold kBound
  apply Real.exp_le_exp.mpr
  have ha : 0 ≤ (2 * (e : ℝ) * n) ^ CK := Real.rpow_nonneg (by positivity) _
  have hb : 0 ≤ c0 * x ^ (eps / 4) := mul_nonneg hc0 (Real.rpow_nonneg hx0.le _)
  calc (2 * (e : ℝ) * n) ^ CK * Real.log (2 * (D : ℝ))
      ≤ (2 * (e : ℝ) * n) ^ CK * (c0 * x ^ (eps / 4)) := mul_le_mul_of_nonneg_left hD ha
    _ ≤ ((2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2)) * (c0 * x ^ (eps / 4)) := mul_le_mul_of_nonneg_right h2 hb
    _ = (2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4) := by rw [h3]; ring
end

section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
open Polynomial

private theorem winlx_up {K : Type} [Field K] {l m : ℕ} (hl : l.Prime) {b : K}
    (h : IsPrimitiveRoot (b ^ l) (l ^ (m + 1))) : IsPrimitiveRoot b (l ^ (m + 2)) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h1 : ¬ b ^ (l ^ (m + 1)) = 1 := by
    intro e
    have : (b ^ l) ^ (l ^ m) = 1 := by rw [← pow_mul, ← pow_succ']; exact e
    exact h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
      (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self m)) this
  have h2 : b ^ (l ^ (m + 1 + 1)) = 1 := by
    rw [pow_succ' l (m + 1), pow_mul]; exact h.pow_eq_one
  have h3 := orderOf_eq_prime_pow h1 h2
  have := IsPrimitiveRoot.orderOf b
  rwa [h3] at this

private theorem winlx_max (K : Type) [Field K] [NumberField K] {l k : ℕ} (hl : l.Prime)
    (h : ∃ z : K, IsPrimitiveRoot z (l ^ (k + 1))) :
    ∃ m, k ≤ m ∧ (∃ z : K, IsPrimitiveRoot z (l ^ (m + 1))) ∧
      ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2)) := by
  by_contra hc
  push Not at hc
  have key : ∀ n, ∃ z : K, IsPrimitiveRoot z (l ^ (k + n + 1)) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact hc (k + n) (by omega) ih
  obtain ⟨z, hz⟩ := key (Module.finrank ℚ K)
  have hpos : 0 < Nat.lcm (l ^ (k + Module.finrank ℚ K + 1)) (l ^ (k + Module.finrank ℚ K + 1)) := by
    rw [Nat.lcm_self]; exact pow_pos hl.pos _
  have h1 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz (Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hl] at h1
  have h2 : k + Module.finrank ℚ K < l ^ (k + Module.finrank ℚ K) := Nat.lt_pow_self hl.one_lt
  have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
  have h4 := Nat.mul_le_mul_left (l ^ (k + Module.finrank ℚ K)) h3
  omega

private theorem winlx_step (K : Type) [Field K] [NumberField K] {l m : ℕ} (hl : l.Prime)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (m + 1))) (hn : ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2))) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K'),
      IsCyclotomicExtension {l ^ (m + 2)} K K' ∧ Module.finrank K K' = l := by
  have hirr : Irreducible (X ^ l - C z : K[X]) :=
    X_pow_sub_C_irreducible_of_prime hl (fun b hb => hn ⟨b, winlx_up hl (hb ▸ hz)⟩)
  haveI : Fact (Irreducible (X ^ l - C z : K[X])) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot (X ^ l - C z : K[X])) := pb.finite
  haveI : NeZero (l ^ (m + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hr : IsPrimitiveRoot (AdjoinRoot.root (X ^ l - C z : K[X])) (l ^ (m + 2)) := by
    apply winlx_up hl
    rw [root_X_pow_sub_C_pow]
    exact hz.map_of_injective (AdjoinRoot.of (X ^ l - C z : K[X])).injective
  refine ⟨AdjoinRoot (X ^ l - C z : K[X]), inferInstance, NumberField.of_module_finite K _, inferInstance, ?_, ?_⟩
  · rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hr⟩, fun x => ?_⟩
    have : x ∈ Algebra.adjoin K {AdjoinRoot.root (X ^ l - C z : K[X])} := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    refine Algebra.adjoin_mono ?_ this
    rintro _ rfl
    exact hr.pow_eq_one
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]

theorem UpperTheory.V.Win.layerex :
    ∀ (l j : ℕ), l.Prime → ∀ (L : Type) [Field L] [NumberField L], HasMuQ l L →
      ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'), IsLayer l j L L' := by
  intro l j hl L _ _ hq
  have hz : ∃ z : L, IsPrimitiveRoot z l := by
    obtain ⟨ζ, hζ⟩ := hq
    by_cases h2 : l = 2
    · subst h2
      rw [if_pos rfl] at hζ
      exact ⟨ζ ^ 2, hζ.pow (by norm_num) (by norm_num)⟩
    · rw [if_neg h2] at hζ
      exact ⟨ζ, hζ⟩
  have key : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'),
      (∃ k : ℕ, IsCyclotomicExtension {l ^ (k + 1)} L L') ∧ Module.finrank L L' = l ^ j := by
    induction j with
    | zero =>
      refine ⟨L, inferInstance, inferInstance, inferInstance, ⟨0, ?_⟩, by simp⟩
      haveI : NeZero (l ^ (0 + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      rw [IsCyclotomicExtension.iff_singleton]
      exact ⟨by simpa using hz, fun x => Subalgebra.algebraMap_mem _ x⟩
    | succ j ih =>
      obtain ⟨K, _, _, _, ⟨k, hk⟩, hd⟩ := ih
      obtain ⟨m, hkm, ⟨z, hz⟩, hn⟩ := winlx_max K (k := k) hl
        (hk.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hl.ne_zero))
      obtain ⟨K', _, _, _, hc, hd'⟩ := winlx_step K hl hz hn
      letI : Algebra L K' := ((algebraMap K K').comp (algebraMap L K)).toAlgebra
      haveI : IsScalarTower L K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine ⟨K', inferInstance, inferInstance, inferInstance, ⟨m + 1, ?_⟩, ?_⟩
      · haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
        have h1 := IsCyclotomicExtension.trans {l ^ (k + 1)} {l ^ (m + 2)} L K K' (algebraMap K K').injective
        rw [Set.union_comm] at h1
        exact (IsCyclotomicExtension.iff_union_of_dvd L K'
          ⟨l ^ (m + 2), Set.mem_singleton _, pow_ne_zero _ hl.ne_zero, pow_dvd_pow _ (by omega)⟩).2 h1
      · rw [← Module.finrank_mul_finrank L K K', hd, hd', pow_succ]
  obtain ⟨L', _, _, _, ⟨k, hk⟩, hd⟩ := key
  exact ⟨L', inferInstance, inferInstance, inferInstance, ⟨k + 1, hk⟩, hd⟩
end

section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem isTotallyComplex_of_hasMuQ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] (h : HasMuQ l L) :
    IsTotallyComplex L := by
  obtain ⟨ζ, hζ⟩ := h
  set n := if l = 2 then 4 else l with hn
  have hn2 : 2 < n := by
    have := (Fact.out : l.Prime).two_le
    rw [hn]; split_ifs with h2
    · norm_num
    · omega
  have : NeZero n := ⟨by omega⟩
  have : IsCyclotomicExtension {n} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsTotallyComplex (IntermediateField.adjoin ℚ {ζ}) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (IntermediateField.adjoin ℚ {ζ}) hn2
  exact isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {ζ}) L

theorem UpperTheory.V.Win.klen :
    ∀ CK : ℝ, LemmaK CK → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
      [IsAlgClosure L Ω] (D : LData L Ω l), HasMuQ l L → ∀ e : ℕ, 1 ≤ e →
        VLen D e ≠ ⊤ ∧ ((VLen D e).toNat : ℝ) ≤ 2 * kBound CK e (Module.finrank ℚ L) (discr L).natAbs := by
  intro CK hK l _ L Ω _ _ _ _ _ D hmu e he
  have htc := isTotallyComplex_of_hasMuQ l L hmu
  obtain ⟨hfin, hlog⟩ := hK l L Ω D htc hmu e he
  obtain ⟨k, hlen, hcard⟩ := Kum.lenOfCard l (ReciprocityTheory.Gal.H2 (zlTw D ((e : ℤ) + 1)))
  have hV : VLen D e = (k : ℕ∞) := hlen
  refine ⟨by rw [hV]; exact ENat.coe_ne_top k, ?_⟩
  rw [hV, ENat.toNat_coe]
  rw [hcard] at hlog
  push_cast at hlog
  rw [Real.log_pow] at hlog
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hlogl : (1 / 2 : ℝ) ≤ Real.log l := by
    have h1 : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl2
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkB : (0 : ℝ) ≤ kBound CK e (Module.finrank ℚ L) (discr L).natAbs := by
    unfold kBound; exact (Real.exp_pos _).le
  nlinarith
end

section

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.near1 :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K] [IsUltrametricDist K] (s : K) (Z a b : ℕ),
      1 ≤ a → a ≤ Z → 1 ≤ b → b ≤ Z → ‖s - (a : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)) →
        ‖s - (b : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)) → a = b := by
  intro l _ K _ _ _ s Z a b ha1 haZ hb1 hbZ hsa hsb
  by_contra hab
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  set k := Nat.log l Z with hk
  set d : ℤ := (a : ℤ) - b with hd
  have hd0 : d ≠ 0 := by omega
  have hK : ‖(d : ℚ_[l])‖ < (l : ℝ) ^ (-(k : ℤ)) := by
    have h1 : algebraMap ℚ_[l] K (d : ℚ_[l]) = (s - b) + -(s - a) := by
      rw [map_intCast, hd]
      push_cast
      ring
    rw [← norm_algebraMap' K, h1]
    calc ‖(s - b) + -(s - a)‖ ≤ max ‖s - b‖ ‖-(s - a)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < _ := by
        rw [norm_neg]
        exact max_lt hsb hsa
  have hdq : (d : ℚ_[l]) ≠ 0 := by exact_mod_cast hd0
  rw [Padic.norm_eq_zpow_neg_valuation hdq] at hK
  have hlt := (zpow_lt_zpow_iff_right₀ hl1).mp hK
  have hle : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hdq]
    apply zpow_le_zpow_right₀ hl1.le
    push_cast
    omega
  have hdvd := (Padic.norm_int_le_pow_iff_dvd d (k + 1)).mp hle
  have hZ := Nat.lt_pow_succ_log_self hlp.one_lt Z
  have habs : d.natAbs ≤ Z := by
    rw [hd]
    omega
  have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact lt_of_le_of_lt habs hZ)
  exact hd0 h0
end
