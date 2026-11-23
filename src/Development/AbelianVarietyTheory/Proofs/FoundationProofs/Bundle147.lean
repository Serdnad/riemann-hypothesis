module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle001
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle142
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle143
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
public import Mathlib.NumberTheory.ModularForms.Discriminant
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
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

section

open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem pieceTRaw_eq (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (x y : ℤ) (r : ℕ) :
    pieceTRaw N p m m k ψ (x, 0) (y, 0) ζ (unitSet p m) r = -((p : K) ^ ((m : ℤ) * ((k : ℤ) - 4))) *
      ∑ i ∈ range (r + 1),
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i)) := by
  unfold pieceTRaw cmul
  congr 1
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h := drop_const p m N k hm hpN hk ψ hψ ζ x y 0 0 i (r - i)
  simp only [mul_zero, add_zero] at h
  rw [← h]
  have e := sum_unitSet p m ψ (fun u a v b =>
    eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i *
        eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i))
  rw [← e]
  refine sum_congr rfl fun γ _ => ?_
  simp [rowT]

theorem coef_eq (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m))
    (a₀ b₀ t : ℤ) (ht : (p : ℤ) ^ m * t ≡ 1 [ZMOD N]) (r : ℕ) :
    pieceTRaw N p m m k ψ (a₀ * t, 0) (b₀ * t, 0) ζ (unitSet p m) r =
      if p ^ m ∣ r then -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
        (N : K) ^ ((2 : ℤ) - k) * coPtMu N p m k ψ a₀ b₀ r else 0 := by
  have hp : p.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [pieceTRaw_eq p m N k hm hpN hk ψ hψ ζ]
  rw [sum_congr rfl fun i hi => by
    rw [GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product p m N k K hm hN hpN hk ψ hψ ζ hζ a₀ b₀ t ht,
      Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hi))]]
  split_ifs with h
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have e' : (p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m *
        ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹ = (p : K) ^ (-(m : ℤ)) * (N : K) ^ ((2 : ℤ) - ((k' + 2 : ℕ) : ℤ)) := by
      rw [Nat.add_sub_cancel, zpow_mul]
      push_cast
      rw [show ((k' : ℤ) + 2 - 4) = (k' : ℤ) - 2 by ring, show (2 : ℤ) - (k' + 2) = -(k' : ℤ) by ring,
        zpow_sub₀ (zpow_ne_zero _ hpK), zpow_neg, zpow_neg]
      simp only [zpow_natCast]
      field_simp
      ring
    unfold coPtMu cmul
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    calc _ = -((p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m *
        ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
          (ffMu N p m (k' + 2) ψ a₀ i * eeMu N p m ψ b₀ (r - i)) := by ring
      _ = _ := by rw [e']; ring
  · simp

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu

theorem GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq : ∀ (p : ℕ) [Fact p.Prime] (N m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (a b t : ℤ) (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ m) → 0 < N → ¬ p ∣ N → 1 ≤ m → 3 ≤ k → ψ.IsPrimitive → (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → Integral (p ^ m) (pieceTRaw N p m m k ψ (a * t, 0) (b * t, 0) ζ (unitSet p m)) ∧ ∀ r : ℕ, toQ (p ^ m) (pieceTRaw N p m m k ψ (a * t, 0) (b * t, 0) ζ (unitSet p m)) r = -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (N : K) ^ ((2 : ℤ) - k) * up (p ^ m) (coPtMu N p m k ψ a b) r := by
  intro p _ N m k K _ _ ψ a b t ζ _ hζ hN hpN hm hk hψ ht
  refine ⟨fun r hr => ?_, fun r => ?_⟩
  · rw [GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_neg hr]
  · unfold toQ up
    rw [GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_pos (dvd_mul_right _ _)]
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def clearCoeff (n M w : ℕ) (c : Fin n → Polynomial ℂ) (i : ℕ) (τ : ℍ) : ℂ :=
  if h : i < n then
    DD τ ^ (w * (n - i)) * ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k))
  else DD τ ^ M

theorem dd_pow_mul_eval_jT (p : Polynomial ℂ) (M : ℕ) (hp : p.natDegree ≤ M) (τ : ℍ) :
    DD τ ^ M * p.eval (jT τ) =
      ∑ k ∈ Finset.range (M + 1), p.coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hD := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have hsplit : DD τ ^ M = DD τ ^ (M - k) * DD τ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hsplit]
  simp only [ReciprocityTheory.ChartRestriction.L1.jT, ReciprocityTheory.ChartRestriction.L1.AA]
  rw [div_pow, pow_mul]
  field_simp

theorem sum_clearCoeff_eq_zero (n M w : ℕ) (c : Fin n → Polynomial ℂ) (hM : ∀ i, (c i).natDegree ≤ M)
    (f : ℍ → ℂ) (h : ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0) (τ : ℍ) :
    ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i = 0 := by
  have key : ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i =
      DD τ ^ (w * n + M) * (f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range (fun i => clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i),
      mul_add, Finset.mul_sum, add_comm]
    congr 1
    · simp only [clearCoeff, lt_irrefl, dite_false]
      rw [mul_pow, ← pow_mul, pow_add]
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [clearCoeff, Fin.is_lt, dite_true, Fin.eta]
      rw [← dd_pow_mul_eval_jT _ M (hM i), mul_pow, ← pow_mul]
      have e : w * (n - i) + M + w * i = w * n + M := by
        rw [add_right_comm, ← mul_add, Nat.sub_add_cancel i.isLt.le]
      rw [← e, pow_add, pow_add]
      ring
  rw [key, h τ, mul_zero]

theorem qall_clearCoeff (R : Subring ℂ) (N : ℕ) (hN : 0 < N) (n M w : ℕ) (c : Fin n → Polynomial ℂ)
    (hc : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R) (i : ℕ) :
    QAll (· ∈ R) N (clearCoeff n M w c i) := by
  obtain ⟨hcst, -, -, hmul, hpow, hsum⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hDD : QAll (· ∈ R) N DD := ((GlobalTheory.T.eisenstein_delta_qExpansion_integrality N hN DD (Or.inr (Or.inr rfl))).2.1) R
  have hE : QAll (· ∈ R) N ⇑E₄ := ((GlobalTheory.T.eisenstein_delta_qExpansion_integrality N hN ⇑E₄ (Or.inl rfl)).2.1) R
  by_cases h : i < n
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ (w * (n - i)) *
        ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
      funext τ; simp [clearCoeff, h]
    rw [hf]
    refine hmul _ _ (hpow _ _ hDD) ?_
    refine (hsum ℕ (Finset.range (M + 1)) _ fun k hk => ?_).1
    exact hmul _ _ (hcst _ (hc _ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))))
      (hmul _ _ (hpow _ _ hE) (hpow _ _ hDD))
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff, h]
    rw [hf]
    exact hpow _ _ hDD

theorem powerSeries_map_mk {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (g : ℕ → Ω) :
    PowerSeries.map ε (PowerSeries.mk g) = PowerSeries.mk fun k => ε (g k) := by
  ext k; simp [PowerSeries.coeff_map]

theorem qcoeff_finitelyGenerated : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N w : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω),
    0 < N → Lv ε.range N w f → HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) →
      ∃ S : Finset Ω, ∀ k, a k ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε N w f a hN hLv hF
  classical
  haveI : CharZero Ω := ε.charZero
  obtain ⟨n, c, hc, hrel⟩ := GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver ε.range f ⟨N, w, hN, hLv⟩
  set M := ∑ i, (c i).natDegree with hMdef
  have hM : ∀ i, (c i).natDegree ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => (c i).natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpre : ∀ (i : Fin n) (k : ℕ), ∃ x : Ω, ε x = (c i).coeff k := fun i k => RingHom.mem_range.1 (hc i k)
  choose e he using hpre
  set S₀ : Finset Ω := Finset.univ.image (fun p : Fin n × Fin (M + 1) => e p.1 p.2) with hS₀
  set A : Subring Ω := Subring.closure (S₀ : Set Ω) with hA
  set R : Subring ℂ := A.map ε with hR
  have hcR : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R := fun i k hk =>
    Subring.mem_map.2 ⟨e i k, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_image.2
      ⟨(i, ⟨k, Nat.lt_succ_of_le hk⟩), Finset.mem_univ _, rfl⟩)), he i k⟩
  have hP : ∀ i, QAll (· ∈ R) N (clearCoeff n M w c i) := qall_clearCoeff R N hN n M w c hcR
  choose c' hc'Q hc'R using hP
  have hser := GlobalTheory.T.polynomial_relation_passes_to_qExpansions N n (fun τ => DD τ ^ w * f τ) (fun k => ε (a k)) (clearCoeff n M w c) c' hN hF hc'Q
    (sum_clearCoeff_eq_zero n M w c hM f hrel)
  have hpre2 : ∀ i k, ∃ x ∈ A, ε x = c' i k := fun i k => Subring.mem_map.1 (hc'R i k)
  choose d hdA hd using hpre2
  set Q : Polynomial (PowerSeries Ω) :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (d i)) with hQdef
  have hmap : PowerSeries.map ε (Q.eval (PowerSeries.mk a)) =
      (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c' i))).eval
        (PowerSeries.mk fun k => ε (a k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hQdef, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum, map_mul, map_pow,
      powerSeries_map_mk, hd]
  rw [hser] at hmap
  have hQ : Q.eval (PowerSeries.mk a) = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff k) hmap
    simpa [PowerSeries.coeff_map] using this
  have hcoef : ∀ i, Q.coeff i = if i ∈ Finset.range (n + 1) then PowerSeries.mk (d i) else 0 := fun i => by
    simp only [hQdef, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    simp [Finsupp.single_apply]
  have hQne : Q ≠ 0 := by
    intro h0
    have hn := hcoef n
    rw [h0, Polynomial.coeff_zero, if_pos (Finset.self_mem_range_succ n)] at hn
    have hc0 : c' n = 0 := funext fun k => by
      have h1 := congrArg (PowerSeries.coeff k) hn
      rw [PowerSeries.coeff_mk, map_zero] at h1
      rw [← hd n k, ← h1, map_zero]; rfl
    have hq := hc'Q n
    have hPn : clearCoeff n M w c n = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff]
    rw [hPn, hc0] at hq
    have hz : HasQ N (fun _ : ℍ => (0 : ℂ)) (0 : ℕ → ℂ) := fun τ => by simpa using hasSum_zero
    have := (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).2 N _ _ 0 hq hz
    exact pow_ne_zero M (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero UpperHalfPlane.I) (congrFun this UpperHalfPlane.I)
  have hcA : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A := fun i k => by
    rw [hcoef i]
    split_ifs
    · rw [PowerSeries.coeff_mk]; exact hdA i k
    · simp
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.eisenstein_algebraic_powerSeries_coeff_closure Ω A (PowerSeries.mk a) Q hQne hcA hQ
  refine ⟨S₀ ∪ S₁, fun k => ?_⟩
  have hk := hS₁ k
  rw [PowerSeries.coeff_mk] at hk
  refine (Subring.closure_le.2 ?_) hk
  rintro x (hx | hx)
  · exact Subring.closure_mono (by simp [Finset.coe_union]) hx
  · exact Subring.subset_closure (by simp [hx])

end GlobalTheory.FN
end
end

section

open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

noncomputable section

namespace GlobalTheory.Sieg.ThInv

open GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv

theorem exp_pi_I_half : cexp (π * I / 2) = I := by
  rw [show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]

theorem oddTheta_eq (τ : ℍ) (z : ℂ) : oddTheta τ z = I * ModularForm.eta (τ : ℂ) * th z τ := by
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have hC := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have hP : ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) =
      tailProd τ (cexp (2 * π * I * z)) * tailProd τ (cexp (-(2 * π * I * z))) := by
    rw [← (hB.mul hC).tprod_eq]
    refine tprod_congr fun n => ?_
    rw [ModularForm.eta_q_eq_pow, Complex.exp_neg]
    rfl
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have h1 : cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) =
      I * Function.Periodic.qParam 24 (τ : ℂ) * ee ((τ : ℂ) / 12) * ee (z / 2) := by
    rw [Function.Periodic.qParam, ee, ee]
    conv_rhs => rw [← exp_pi_I_half]
    rw [exp_pi_I_half]
    nth_rewrite 3 [← exp_pi_I_half]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h2 : ee (-z / 2) = ee (z / 2) * cexp (-(2 * π * I * z)) := by
    rw [ee, ee, ← Complex.exp_add]
    congr 1; ring
  rw [oddTheta, jacobiTheta₂_shift GlobalTheory.JacobiTriple.tripleProduct, th, hP, ModularForm.eta, ← hT1, h1, h2]
  ring

theorem sqrt_eq (τ : ℍ) : (Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : -I * (τ : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ
  have hre : 0 < (-I * (τ : ℂ)).re := by simpa using τ.im_pos
  have ha := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))
  have hl : log (I * (-I * (τ : ℂ))) = log I + log (-I * (τ : ℂ)) := by
    rw [Complex.log_mul_eq_add_log_iff I_ne_zero h0, Complex.arg_I]
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [show I * (-I * (τ : ℂ)) = τ by linear_combination (-(τ : ℂ)) * I_sq] at hl
  rw [Complex.sqrt, Complex.sqrt, Complex.cpow_def_of_ne_zero I_ne_zero, Complex.cpow_def_of_ne_zero hτ,
    Complex.cpow_def_of_ne_zero h0, hl,
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1; ring

theorem eta_S (τ : ℍ) :
    ModularForm.eta (-1 / (τ : ℂ)) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ModularForm.eta (τ : ℂ) := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  rw [← sqrt_eq, mul_assoc]
  simpa using h

theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [neg_div]

theorem oddTheta_S (τ : ℍ) (z : ℂ) :
    oddTheta (ModularGroup.S • τ) (z / (τ : ℂ)) =
      -I * (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ee (z ^ 2 / (2 * (τ : ℂ))) * oddTheta τ z := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ h.1
  have hI : -I = cexp (-(π * I / 2)) := by
    rw [Complex.exp_neg, exp_pi_I_half, Complex.inv_I]
  rw [oddTheta, oddTheta, coe_S_smul, jacobiTheta₂_functional_equation (z + ((τ : ℂ) + 1) / 2) τ,
    show z / (τ : ℂ) + (-1 / (τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) / τ + -1 / (τ : ℂ) by
      field_simp; ring, jacobiTheta₂_add_left']
  generalize jacobiTheta₂ ((z + ((τ : ℂ) + 1) / 2) / τ) (-1 / (τ : ℂ)) = J
  generalize (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = s at h0 ⊢
  have hE : ∀ A B C D : ℂ, cexp A * s * cexp B * (cexp C * (1 / s * cexp D * J)) =
      cexp (A + B + C + D) * J := by
    intro A B C D
    simp only [Complex.exp_add]
    field_simp
  rw [ee]
  conv_rhs => rw [hI]
  rw [hE, ← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

theorem th_S : ∀ (τ : ℍ) (z : ℂ), th (z / (τ : ℂ)) (ModularGroup.S • τ) =
    -Complex.I * ee (z ^ 2 / (2 * (τ : ℂ))) * th z τ := by
  intro τ z
  have h := oddTheta_S τ z
  rw [oddTheta_eq, oddTheta_eq] at h
  have hne : I * ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (ModularForm.eta_ne_zero (ModularGroup.S • τ).2)
  refine mul_left_cancel₀ hne ?_
  rw [h, coe_S_smul, eta_S]
  ring

end GlobalTheory.Sieg.ThInv
end
end

section

open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square.Ratio

open Formalism.DivisionValues.ValuationRepresentative (vw_mul vw_inv)

theorem away {K : Type} [Field K] [NumberField K] [StarRing K] {w : Pl K} {Qn : ℕ}
    (hQ : (Qn : 𝓞 K) ∉ w.asIdeal) {x : K} (h : IsAwayUnit Qn x) : x ≠ 0 ∧ vw w x = 0 := by
  obtain ⟨a, k, k', hd, hx⟩ := h
  have hQk : ∀ k, (Qn : 𝓞 K) ^ k ∉ w.asIdeal := fun k h => hQ (w.isPrime.mem_of_pow_mem k h)
  have ha : a ∉ w.asIdeal := fun h => hQk k' (Ideal.mem_of_dvd _ hd h)
  have ha0 : (a : K) ≠ 0 := by
    intro h; apply ha
    have : a = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  rw [← hx] at ha0
  have h1 := Formalism.DivisionValues.ReductionFirst.vw_unit w a ha
  have h2 := Formalism.DivisionValues.ReductionFirst.vw_unit w _ (hQk k)
  have e : (((Qn : 𝓞 K) ^ k : 𝓞 K) : K) = (Qn : K) ^ k := by simp
  rw [e] at h2
  rw [← hx, vw_mul w _ _ (left_ne_zero_of_mul ha0) (right_ne_zero_of_mul ha0), h2] at h1
  exact ⟨left_ne_zero_of_mul ha0, by simpa using h1⟩

theorem exists_ratios : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (w : Pl K) (Qn : ℕ), (Qn : 𝓞 K) ∉ w.asIdeal → ∀ (e0 h : ℕ), e0 ≤ h → ∀ (L0 L1 : ℤ → ℂ) (zT zTd zψ Ep : ℤ → K) (gT : ℤ → ℤ) (n0 : ℤ → ℝ) (er : ℝ), (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ h → L0 s ≠ 0 ∧ L1 s ≠ 0) → (∀ s : ℤ, 1 ≤ s → s ≤ h → zT s ≠ 0 ∧ zTd s ≠ 0 ∧ σ₀ (zψ s) * L0 s = σ₀ (zT s) * L1 s ∧ -(n0 s) ≤ ((vw w (zψ s) + gT s : ℤ) : ℝ) ∧ (vw w (zψ s) : ℝ) ≤ (vw w (zTd s) : ℝ) + er) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → IsAwayUnit Qn (Ep s) ∧ L1 s * L0 (1 - s) = σ₀ (Ep s) * (L1 (1 - s) * L0 s)) → ∃ ρ : ℤ → K, (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ h → ρ s ≠ 0 ∧ σ₀ (ρ s) * L0 s = L1 s) ∧ (∀ s : ℤ, 1 ≤ s → s ≤ h → (vw w (ρ s) : ℝ) ≤ |((vw w (zT s) + gT s : ℤ) : ℝ)| + |((vw w (zTd s) + gT s : ℤ) : ℝ)| + er ∧ -(vw w (ρ s) : ℝ) ≤ |((vw w (zT s) + gT s : ℤ) : ℝ)| + n0 s) ∧ (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) := by
  intro K _ _ _ σ₀ w Qn hQ e0 h he L0 L1 zT zTd zψ Ep gT n0 er hL hpos hneg
  have he' : (e0 : ℤ) ≤ h := by exact_mod_cast he
  have key : ∀ s : ℤ, 1 ≤ s → s ≤ h → zψ s ≠ 0 ∧ zψ s / zT s ≠ 0 ∧
      σ₀ (zψ s / zT s) * L0 s = L1 s := by
    intro s h1 h2
    obtain ⟨hT, -, hrel, -, -⟩ := hpos s h1 h2
    obtain ⟨-, hL1⟩ := hL s (by omega) h2
    have hT' : σ₀ (zT s) ≠ 0 := (map_ne_zero σ₀).2 hT
    have hψ : zψ s ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hrel
      exact mul_ne_zero hT' hL1 hrel.symm
    refine ⟨hψ, div_ne_zero hψ hT, ?_⟩
    rw [map_div₀]
    field_simp
    linear_combination hrel
  refine ⟨fun s => if 1 ≤ s then zψ s / zT s else Ep s * (zψ (1 - s) / zT (1 - s)), ?_, ?_, ?_⟩
  · intro s h1 h2
    by_cases hs : 1 ≤ s
    · simp only [hs, if_true]
      exact (key s hs h2).2
    · simp only [hs, if_false]
      obtain ⟨hu, hrel⟩ := hneg s h1 (by omega)
      obtain ⟨-, hne, hk⟩ := key (1 - s) (by omega) (by omega)
      refine ⟨mul_ne_zero (away hQ hu).1 hne, ?_⟩
      have hL0 := (hL (1 - s) (by omega) (by omega)).1
      apply mul_right_cancel₀ hL0
      rw [hrel, map_mul, ← hk]
      ring
  · intro s h1 h2
    simp only [h1, if_true]
    obtain ⟨hT, -, -, hb1, hb2⟩ := hpos s h1 h2
    have hψ := (key s h1 h2).1
    have hv : vw w (zψ s / zT s) = vw w (zψ s) - vw w (zT s) := by
      rw [div_eq_mul_inv, vw_mul w _ _ hψ (inv_ne_zero hT), vw_inv]; ring
    rw [hv]
    have a1 := le_abs_self ((vw w (zT s) + gT s : ℤ) : ℝ)
    have a2 := neg_abs_le ((vw w (zT s) + gT s : ℤ) : ℝ)
    have a3 := le_abs_self ((vw w (zTd s) + gT s : ℤ) : ℝ)
    generalize |((vw w (zT s) + gT s : ℤ) : ℝ)| = A at *
    generalize |((vw w (zTd s) + gT s : ℤ) : ℝ)| = B at *
    push_cast at *
    constructor <;> linarith
  · intro s h1 h2
    have hs : ¬ 1 ≤ s := by omega
    have hs' : 1 ≤ 1 - s := by omega
    simp only [hs, hs', if_true, if_false]
    obtain ⟨hu, -⟩ := hneg s h1 h2
    obtain ⟨hE, hv⟩ := away hQ hu
    rw [vw_mul w _ _ hE (key (1 - s) hs' (by omega)).2.1, hv, zero_add]

end GlobalTheory.Square.Ratio
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.qz_torsion_and_exists_zmod_pow_embedding : ∀ (l : ℕ) [Fact l.Prime], (∀ a : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) ∧ ∀ r : ℕ, ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧ (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧ ∀ (x : ℤ_[l]) (y : ZMod (l ^ r)), ι (PadicInt.toZModPow r x * y) = x • ι y := by
  first | exact @GlobalTheory.qz_torsion_zmod_embedding | exact GlobalTheory.qz_torsion_zmod_embedding | (intros; apply GlobalTheory.qz_torsion_zmod_embedding <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.exists_decompositionGroup_cyclotomicCharacter_zpow_ne_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∀ n : ℤ, n ≠ 0 → ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  first | exact @GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one | exact GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one | (intros; apply GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one <;> assumption)
end
