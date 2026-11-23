module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle169
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle172
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

private theorem multiset_range_map_eq_sum_singleton (f : ℕ → ℂˣ) (N : ℕ) :
    (Multiset.range N).map f = ∑ j ∈ Finset.range N, ({f j} : Multiset ℂˣ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ← ih, add_comm, Multiset.singleton_add]

theorem str_eq_sum (q : ℂˣ) (t : ℤ) :
    str q t = ∑ j ∈ Finset.range t.toNat, ({q ^ (2 * (j : ℤ) - (t - 1))} : Multiset ℂˣ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str]
  exact multiset_range_map_eq_sum_singleton _ _

theorem str_even (q : ℂˣ) (d : ℕ) (t : ℤ) (ht : t = 2 * d) :
    str q t = ∑ k ∈ Finset.range d, ({q ^ (t - 1 - 2 * (k : ℤ)), q ^ (-(t - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) := by
  rw [str_eq_sum, show t.toNat = d + d by omega, Finset.sum_range_add]
  conv_lhs => arg 2; rw [← Finset.sum_range_reflect]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < d := Finset.mem_range.mp hk
  rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
  congr 3 <;> omega

theorem str_odd (q : ℂˣ) (d : ℕ) (t : ℤ) (ht : t = 2 * d + 1) :
    str q t = ∑ k ∈ Finset.range d, ({q ^ (t - 1 - 2 * (k : ℤ)), q ^ (-(t - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) + {1} := by
  rw [str_eq_sum, show t.toNat = d + (d + 1) by omega, Finset.sum_range_add, Finset.sum_range_succ']
  conv_lhs => arg 2; arg 1; rw [← Finset.sum_range_reflect]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < d := Finset.mem_range.mp hk
    rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
    congr 3 <;> omega
  · rw [← zpow_zero q]
    congr 2
    omega

theorem lift_key (q : ℂˣ) (n n' : ℕ) (h : n ≤ n') :
    ∑ k ∈ Finset.range (n' / 2 - n / 2),
        ({q ^ ((n' : ℤ) - n - 1 - 2 * (k : ℤ)), q ^ (-((n' : ℤ) - n - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) +
      Multiset.replicate (n' % 2) ((-1 : ℂˣ) ^ n)⁻¹ =
    Multiset.replicate (n % 2) ((-1 : ℂˣ) ^ n')⁻¹ + str q ((n' : ℤ) - n) := by
  have hsq : ∀ m : ℕ, (-1 : ℂˣ) ^ (2 * m) = 1 := fun m => by rw [pow_mul, neg_one_sq, one_pow]
  rcases Nat.even_or_odd' n with ⟨a, rfl | rfl⟩ <;> rcases Nat.even_or_odd' n' with ⟨b, rfl | rfl⟩
  · rw [str_even q (b - a) _ (by omega), show 2 * b / 2 - 2 * a / 2 = b - a by omega,
      show 2 * b % 2 = 0 by omega, show 2 * a % 2 = 0 by omega]
    simp only [Multiset.replicate_zero, add_zero, zero_add]
  · rw [str_odd q (b - a) _ (by omega), show (2 * b + 1) / 2 - 2 * a / 2 = b - a by omega,
      show (2 * b + 1) % 2 = 1 by omega, show 2 * a % 2 = 0 by omega, hsq, inv_one]
    simp only [Multiset.replicate_zero, Multiset.replicate_one, zero_add]
  · have e0 : ((2 * b : ℕ) : ℤ) - ((2 * a + 1 : ℕ) : ℤ) - 1 - 2 * ((b - a - 1 : ℕ) : ℤ) = 0 := by omega
    rw [str_odd q (b - a - 1) _ (by omega), show 2 * b / 2 - (2 * a + 1) / 2 = b - a - 1 + 1 by omega,
      Finset.sum_range_succ, e0, neg_zero, zpow_zero,
      show 2 * b % 2 = 0 by omega, show (2 * a + 1) % 2 = 1 by omega, hsq, inv_one]
    simp only [Multiset.replicate_zero, Multiset.replicate_one, add_zero, Multiset.insert_eq_cons,
      ← Multiset.singleton_add]
    abel
  · have hodd : ∀ m : ℕ, (-1 : ℂˣ) ^ (2 * m + 1) = -1 := fun m => by rw [pow_succ, hsq, one_mul]
    rw [str_even q (b - a) _ (by omega), show (2 * b + 1) / 2 - (2 * a + 1) / 2 = b - a by omega,
      show (2 * b + 1) % 2 = 1 by omega, show (2 * a + 1) % 2 = 1 by omega, hodd, hodd, add_comm]

private theorem sum_pi_single_one_smul {ι : Type} (s : Finset ι) (f : ι → ℂˣ) :
    ∑ i ∈ s, ({f i} : Multiset ℂˣ) = s.val.map f := by
  rw [Finset.sum_eq_multiset_sum]
  generalize s.val = m
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, Multiset.singleton_add]


open GlobalTheory.LGrp (bcParam) in
theorem bcParam_map_mul (c : ℂˣ) (N : ℕ) (γ : Fin (N / 2) → ℂˣ) :
    (bcParam N γ).map (fun x => c * x) =
      ∑ i, ({c * γ i, c * (γ i)⁻¹} : Multiset ℂˣ) + Multiset.replicate (N % 2) c := by
  have hpair : ∀ i, ({c * γ i, c * (γ i)⁻¹} : Multiset ℂˣ) = {c * γ i} + {c * (γ i)⁻¹} := fun i => by
    rw [Multiset.insert_eq_cons, Multiset.singleton_add]
  simp only [hpair, Finset.sum_add_distrib, sum_pi_single_one_smul, bcParam, Multiset.map_add (f := _), Multiset.map_map,
    Multiset.map_replicate, mul_one]
  rfl

theorem neg_one_pow_inv (k : ℕ) : ((-1 : ℂˣ) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow, inv_neg_one]

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂˣ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem pair_inv_mul_eq_of_mul_self_eq_one (s t a : ℂˣ) (hs : s * s = 1) (ht : t * t = 1) :
    ({s⁻¹ * (s * t * a⁻¹), s⁻¹ * (s * t * a⁻¹)⁻¹} : Multiset ℂˣ) = {t⁻¹ * a, t⁻¹ * a⁻¹} := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e1 : s⁻¹ * (s * t * a⁻¹) = t⁻¹ * a⁻¹ := by rw [mul_assoc, inv_mul_cancel_left, ht']
  have e2 : s⁻¹ * (s * t * a⁻¹)⁻¹ = t⁻¹ * a := by
    simp only [mul_inv, inv_inv]
    rw [hs', ← mul_assoc, ← mul_assoc, hs, one_mul]
  rw [e1, e2, Multiset.pair_comm]

theorem bcParam_liftPar (q : ℂˣ) (n n' : ℕ) (h : n ≤ n') (α : Fin (n / 2) → ℂˣ) :
    (bcParam n' (liftPar q n n' α)).map (fun x => ((-1 : ℂˣ) ^ n)⁻¹ * x) =
      (bcParam n α).map (fun x => ((-1 : ℂˣ) ^ n')⁻¹ * x) + str q ((n' : ℤ) - n) := by
  have hD : n' / 2 - n / 2 + n / 2 = n' / 2 := by omega
  have hs : (-1 : ℂˣ) ^ n * (-1) ^ n = 1 := neg_one_pow_mul_self n
  have hsum : (∑ i : Fin (n' / 2), ({((-1 : ℂˣ) ^ n)⁻¹ * liftPar q n n' α i,
        ((-1 : ℂˣ) ^ n)⁻¹ * (liftPar q n n' α i)⁻¹} : Multiset ℂˣ)) =
      ∑ k ∈ Finset.range (n' / 2 - n / 2),
        ({q ^ ((n' : ℤ) - n - 1 - 2 * (k : ℤ)), q ^ (-((n' : ℤ) - n - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) +
      ∑ i : Fin (n / 2), ({((-1 : ℂˣ) ^ n')⁻¹ * α i, ((-1 : ℂˣ) ^ n')⁻¹ * (α i)⁻¹} : Multiset ℂˣ) := by
    rw [← Equiv.sum_comp (finCongr hD), Fin.sum_univ_add, ← Fin.sum_univ_eq_sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hL : liftPar q n n' α (finCongr hD (Fin.castAdd (n / 2) i)) =
          (-1) ^ n * q ^ ((n' : ℤ) - n - 1 - 2 * ((i : ℕ) : ℤ)) := by
        unfold liftPar
        rw [dite_eq_left (by simp)]
        simp
      rw [hL, mul_inv, inv_mul_cancel_left, neg_one_pow_inv, ← mul_assoc, hs, one_mul, ← _root_.zpow_neg]
    · refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
      have hL : liftPar q n n' α (finCongr hD (Fin.natAdd (n' / 2 - n / 2) j)) =
          (-1) ^ n * (-1) ^ n' * (α (Fin.revPerm j))⁻¹ := by
        unfold liftPar
        rw [dite_eq_right (by simp), pow_add]
        congr 3
        ext
        simp
        omega
      rw [hL]
      exact pair_inv_mul_eq_of_mul_self_eq_one _ _ _ hs (neg_one_pow_mul_self n')
  rw [bcParam_map_mul, bcParam_map_mul, hsum, add_assoc _ (Multiset.replicate (n % 2) _), ← lift_key q n n' h]
  abel

end GlobalTheory.SphTheta
end
end

section

noncomputable section

namespace GlobalTheory.BorelChar

open Matrix Formalism.UG

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

local notation "⟪" x "⟫" => (((x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem ext_mat {g h : GU σ n} (e : ⟪g⟫ = ⟪h⟫) : g = h := Subtype.ext (Units.ext e)

theorem exists_conj_mem_K {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {u : GU σ n} (hu : IsUnipU u) :
    ∃ s : GU σ n, IsBorelU s ∧ s * u * s⁻¹ ∈ KU σ n := by
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set U := ⟪u⟫ with hUdef
  obtain ⟨M, hM⟩ := GlobalTheory.UnitarySwap.exists_pow_mem hϖ' U
  let b : Fin n → ℤ := fun i => (M : ℤ) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))
  have hb : ∀ i : Fin n, b i.rev = -b i := by
    intro i
    have := i.isLt
    simp only [b, Fin.val_rev]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσϖ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hpow : ∀ k : ℤ, 0 ≤ k → Valued.v (ϖ ^ k) ≤ 1 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, map_pow]
    exact pow_le_one₀ zero_le hϖ1
  set k := s * u * s⁻¹ with hkdef
  have hkm : ⟪k⟫ = Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹) := by
    rw [hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']
  have hI : Formalism.UG.P.fIwasawaInt ⟪k⟫ := by
    intro i j
    rw [hkm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hle : (M : ℤ) ≤ b i - b j := by
        have : (i.val : ℤ) + 1 ≤ j.val := by exact_mod_cast hij
        simp only [b]
        nlinarith
      have e : ϖ ^ b i * U i j * (ϖ ^ b j)⁻¹ = ϖ ^ (b i - b j - M) * (ϖ ^ M * U i j) := by
        rw [zpow_sub₀ h0, zpow_sub₀ h0, zpow_natCast]
        field_simp
      rw [e, map_mul]
      exact mul_le_one' (hpow _ (by omega)) (hM i j)
    · have e1 : U i i = 1 := hu.2 i
      rw [e1, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ h0), map_one]
    · have e1 : U i j = 0 := hu.1 i j hij
      rw [e1, mul_zero, zero_mul, map_zero]; exact zero_le
  have hkK : k ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ k) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ k) = k := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  exact ⟨s, Formalism.UG.P.fSatake_borel_of_diag hs, hkK⟩

theorem tMat_add (ϖ : L) (h0 : ϖ ≠ 0) (m : ℕ) (a c : Fin m → ℤ) :
    tMat ϖ n m (a + c) = tMat ϖ n m a * tMat ϖ n m c := by
  unfold tMat
  rw [diagonal_mul_diagonal]
  congr 1; funext i
  split_ifs <;> simp [zpow_add₀ h0, neg_add] <;> ring

theorem tMat_zero (ϖ : L) (m : ℕ) : tMat ϖ n m 0 = 1 := by
  unfold tMat
  rw [← diagonal_one]
  congr 1; funext i
  split_ifs <;> simp

theorem borel_char : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (f : GU σ n → ℂ), (∀ b b', IsBorelU b → IsBorelU b' → f (b * b') = f b * f b') →
    (∀ k ∈ KU σ n, IsBorelU k → f k = 1) → ∀ y : Fin (n / 2) → ℂ,
    (∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → f t = y k) →
    ∀ b, IsBorelU b → f b = ∏ k, y k ^ ordL (b.1.1 (GlobalTheory.SphTheta.lo n k) (GlobalTheory.SphTheta.lo n k)) := by
  intro L _ _ ϖ σ q hU n f hmul hK y hy b hb
  have hϖ0 : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact absurd this WithZero.zero_ne_coe
  have h1 : f 1 = 1 := hK 1 (one_mem _) Formalism.UG.P.fSatake_borel_one
  have hinv : ∀ b, IsBorelU b → f b * f b⁻¹ = 1 := fun b hb => by
    rw [← hmul _ _ hb (Formalism.UG.P.fSatake_borel_inv hb), mul_inv_cancel, h1]

  have hunip : ∀ u, IsUnipU u → f u = 1 := by
    intro u hu
    obtain ⟨s, hs, hsK⟩ := exists_conj_mem_K hU hu
    have hsu := Formalism.UG.P.fSatake_borel_mul hs hu.1
    have := hK _ hsK (Formalism.UG.P.fSatake_borel_mul hsu (Formalism.UG.P.fSatake_borel_inv hs))
    rw [hmul _ _ hsu (Formalism.UG.P.fSatake_borel_inv hs), hmul _ _ hs hu.1] at this
    calc f u = f u * (f s * f s⁻¹) := by rw [hinv s hs, mul_one]
      _ = f s * f u * f s⁻¹ := by ring
      _ = 1 := this

  have hm : 2 * (n / 2) ≤ n := by omega
  have hT : ∀ a : Fin (n / 2) → ℤ, ∃ t : GU σ n, (t).1.1 = tMat ϖ n (n / 2) a :=
    fun a => Formalism.UG.P.fSatake_tMat_exists hU hm a
  choose T hTm using hT
  have hTb : ∀ a, IsBorelU (T a) := fun a => Formalism.UG.P.fSatake_borel_tMat (hTm a)
  have hTadd : ∀ a c, T (a + c) = T a * T c := fun a c => ext_mat (by
    rw [Subgroup.coe_mul, Units.val_mul, hTm, hTm, hTm, tMat_add ϖ hϖ0])
  have hT0 : T 0 = 1 := ext_mat (by rw [hTm, tMat_zero]; rfl)
  have hg : ∀ a c, f (T (a + c)) = f (T a) * f (T c) := fun a c => by
    rw [hTadd, hmul _ _ (hTb a) (hTb c)]
  have hgu : ∀ a, f (T a) * f (T (-a)) = 1 := fun a => by
    rw [← hg, add_neg_cancel, hT0, h1]
  let G : Multiplicative (Fin (n / 2) → ℤ) →* ℂˣ := MonoidHom.mk'
    (fun a => ⟨f (T a.toAdd), f (T (-a.toAdd)), hgu _, by rw [mul_comm]; exact hgu _⟩)
    (fun a c => Units.ext (by simp only [toAdd_mul, Units.val_mul]; exact hg _ _))
  have hGs : ∀ k, (G (Multiplicative.ofAdd (Pi.single k 1)) : ℂ) = y k := fun k => hy k _ (hTm _)
  have hTval : ∀ a, f (T a) = ∏ k, y k ^ a k := by
    intro a
    have ea : Multiplicative.ofAdd a = ∏ k, (Multiplicative.ofAdd (Pi.single k (1 : ℤ))) ^ a k := by
      simp_rw [← ofAdd_zsmul, ← ofAdd_sum]
      congr 1
      conv_lhs => rw [← Finset.univ_sum_single a]
      refine Finset.sum_congr rfl fun k _ => ?_
      funext j
      simp [Pi.single_apply]
    have := congrArg (fun z => (G z : ℂ)) ea
    simp only [map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hGs] at this
    exact this

  obtain ⟨a, u, hu, k', hk', he⟩ := Formalism.UG.P.fSatake_cell_exists hU hm (by omega) hb (one_mem (KU σ n))
  have hbe : b = T a * u * k' := ext_mat (by
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, hTm, ← he, mul_one])
  have htu := Formalism.UG.P.fSatake_borel_mul (hTb a) hu.1
  have hkb : IsBorelU k' := by
    have e : k' = (T a * u)⁻¹ * b := by rw [hbe]; group
    rw [e]; exact Formalism.UG.P.fSatake_borel_mul (Formalism.UG.P.fSatake_borel_inv htu) hb
  have hfb : f b = f (T a) := by
    rw [hbe, hmul _ _ htu hkb, hmul _ _ (hTb a) hu.1, hunip u hu, hK k' hk' hkb, mul_one, mul_one]
  rw [hfb, hTval]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1

  have hj : (j : ℕ) < n := by omega
  have hd : (b).1.1 ⟨j, hj⟩ ⟨j, hj⟩ = ϖ ^ (a j) * (k').1.1 ⟨j, hj⟩ ⟨j, hj⟩ := by
    rw [hbe, Formalism.UG.P.fSatake_borel_diag_mul htu hkb, Formalism.UG.P.fSatake_borel_diag_mul (hTb a) hu.1, hu.2, mul_one,
      hTm, Formalism.UG.P.fSatake_tMat_apply_lt ϖ a j hj]
  have hw0 := Formalism.UG.P.fSatake_ne_zero_of_borel hkb ⟨j, hj⟩
  have hwr0 := Formalism.UG.P.fSatake_ne_zero_of_borel hkb (⟨j, hj⟩ : Fin n).rev
  have hpair := congrArg ordL (Formalism.UG.P.fSatake_unit_diag hkb ⟨j, hj⟩)
  rw [Formalism.UG.P.fSatake_ord_mul ((map_ne_zero σ).2 hw0) hwr0, Formalism.UG.P.fSatake_ord_of_v (hU.2.1 _),
    Formalism.UG.P.fSatake_ord_one] at hpair
  have hn1 := Formalism.UG.P.fSatake_ord_nonneg hw0 (Formalism.UG.P.fSatake_K_int hk' _ _)
  have hn2 := Formalism.UG.P.fSatake_ord_nonneg hwr0 (Formalism.UG.P.fSatake_K_int hk' _ _)
  have h3 := congrArg ordL hd
  rw [Formalism.UG.P.fSatake_ord_mul (zpow_ne_zero _ hϖ0) hw0, Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1] at h3
  show a j = ordL ((b).1.1 ⟨j, hj⟩ ⟨j, hj⟩)
  omega

end GlobalTheory.BorelChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isOfFinOrder_of_conj_mem_selfDualLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), IsDefUnimod hc J Λ → IsFrame β Λ → ∀ (u : UR hc J) (x : UA hc J), conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ St β → IsOfFinOrder u := by
  first | exact @GlobalTheory.DefFree.isOfFinOrder_of_conjIn_mem_St | exact GlobalTheory.DefFree.isOfFinOrder_of_conjIn_mem_St | (intros; apply GlobalTheory.DefFree.isOfFinOrder_of_conjIn_mem_St <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedHeis

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  rw [GfC, MonoidHom.mem_ker] at hk
  unfold compAt Formalism.L2.Theta.mt
  unfold infHom at hk
  unfold infPart
  rw [MonoidHom.comp_apply] at hk
  have e := congrArg (fun g => (Units.val g).map (θ τ)) hk
  simp only [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)] at e
  rw [← e]
  rfl

theorem om_fin_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ κ ∈ GfC S, ∀ κ' ∈ GfC T, ∀ sS sT BS BT f P, IsThetaFunO ψ S T f → om (κ, κ') (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (κ, κ') f) P := by
  intro D ψ S T χS χT om hW θ hθ κ hκ κ' hκ' sS sT BS BT f P hf
  have h1 := fun τ => compAt_mt_of_mem_GfC θ S hκ τ
  have h2 := fun τ => compAt_mt_of_mem_GfC θ T hκ' τ
  have := (om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT κ κ' (fun τ => by rw [h1 τ, one_mul, mul_one]) (fun τ => by rw [h2 τ, one_mul, mul_one]) (fun τ => by rw [h1 τ, one_mul]) (fun τ => by rw [h2 τ, one_mul]) f hf P).2
  exact this

end GlobalTheory.OrientedHeis
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeClassSums

section Linear

variable {L : Type} [Field L] {σ : L →+* ℂ} {H : Type} [AddCommGroup H] [Module ℂ H]

end Linear

section Group

open Formalism.IndefR.Bridge

variable {G : Type} [Group G]

end Group

section Row

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {R}



theorem span_jV (hV : R.models_HV) (hj : R.models_jV) (i : Fin D.R.m) (t : T0) : Submodule.span ℂ (Set.range (R.jV i t)) = ⊤ := by
  apply Submodule.map_injective_of_injective (hV i t).1
  rw [Submodule.map_span, Submodule.map_top, (hV i t).2.1, ← Set.range_comp]
  have h1 : (⇑(R.HV i t).e ∘ ⇑(R.jV i t)) = ⇑((R.B.L i t).pres.extL) := funext fun x => hj i t x
  rw [h1]
  exact GlobalTheory.PresBasic.ext_span (R.B.L i t).pres

end Local

section Comparison₂

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

end Comparison₂

end Row

end GlobalTheory.HeckeClassSums
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → (∀ γ ∈ ratL T S, ∀ w, ‖F (γ + w)‖ = ‖F w‖) ∧ ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≠ ⊤ ∧ ∫ x in 𝓕, F x * starRingEnd ℂ (F x) ∂μ = (((∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ThetaSqInt.thetaO_norm_fin | exact GlobalTheory.ThetaSqInt.thetaO_norm_fin | (intros; apply GlobalTheory.ThetaSqInt.thetaO_norm_fin <;> assumption)
end
