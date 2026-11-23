module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.GradedWeylDivisibility.Bundle001
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle014
public import Formalism.GradedWeylDivisibility.FinalC
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle175
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle176
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product : ∀ (k l j : ℕ) (u w A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zm k l u w (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1)) (dep l (eis (j + 1) c' A' w)) := by
  first | exact @GlobalTheory.zm_eq_mul_dep_eis | exact GlobalTheory.zm_eq_mul_dep_eis | (intros; apply GlobalTheory.zm_eq_mul_dep_eis <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters : ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ, tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  first | exact @GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum | exact GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum | (intros; apply GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum <;> assumption)
end

section

namespace GlobalTheory.BoundedScalarNorm

theorem norm_smul_le_self {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) (y : PadicAlgCl l) : ‖a • y‖ ≤ ‖y‖ := by
  have h : a • y = (a : ℚ_[l]) • y := by
    rw [← IsScalarTower.algebraMap_smul ℚ_[l] a y]; rfl
  rw [h, norm_smul]
  have h1 : ‖(a : ℚ_[l])‖ ≤ 1 := a.2
  exact mul_le_of_le_one_left (norm_nonneg _) h1

theorem bounded {l : ℕ} [Fact l.Prime] (M : Submodule ℤ_[l] (PadicAlgCl l)) (h : M.FG) :
    ∃ C : ℝ, ∀ y ∈ M, ‖y‖ ≤ C := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨∑ z ∈ s, ‖z‖, fun y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem z hz => exact Finset.single_le_sum (f := fun z => ‖z‖) (fun _ _ => norm_nonneg _) hz
  | zero => rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  | add u v _ _ hu hv => exact (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)
  | smul a u _ hu => exact (norm_smul_le_self a u).trans hu

theorem norm_le_one : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ UpperTheory.V.HV.Coef.O c → ‖x‖ ≤ (1 : ℝ) := by
  intro l _ c x hx
  have hfg : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.mp c.fin
  obtain ⟨C, hC⟩ := bounded _ hfg
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
  have := hC (x ^ n) (c.O.pow_mem hx n)
  rw [norm_pow] at this
  exact absurd hn (not_lt.mpr this)

end GlobalTheory.BoundedScalarNorm
end

section

noncomputable section

namespace GlobalTheory.PadicNormCastBounds

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_le_one_of_isIntegral {x : PadicAlgCl l} (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hz : ∀ a : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact a.2
  let v := NormedField.valuation (K := PadicAlgCl l)
  let φ : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer fun a => by
      rw [Valuation.mem_integer_iff]
      exact_mod_cast hz a
  have h1 : IsIntegral v.integer x := hx.map_of_comp_eq φ (RingHom.id _) (by ext a; rfl)
  have h2 := (Valuation.integer.integers v).mem_of_integral h1
  rw [Valuation.mem_integer_iff] at h2
  exact_mod_cast h2

theorem norm_natCast_of_coprime {a : ℕ} (ha : a.Coprime l) : ‖(a : PadicAlgCl l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ha.symm

theorem norm_inv_pow_val_le (r e : ℕ) (u : (ZMod (l ^ r))ˣ) :
    ‖((((u : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (u : ZMod (l ^ 0)).val = 0 := by
      have := ZMod.val_lt (u : ZMod (l ^ 0))
      simpa using this
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · simp [he.ne']
  · have hc : (u : ZMod (l ^ r)).val.Coprime l :=
      (ZMod.val_coe_unit_coprime u).coprime_dvd_right (dvd_pow_self l hr.ne')
    rw [norm_inv, norm_pow, norm_natCast_of_coprime hc]
    simp

theorem norm_inv_pow_sub_le {a b r : ℕ} (e : ℕ) (ha : a.Coprime l) (hb : b.Coprime l) (h : a ≡ b [MOD l ^ r]) :
    ‖((a : PadicAlgCl l) ^ e)⁻¹ - ((b : PadicAlgCl l) ^ e)⁻¹‖ ≤ ‖(l : PadicAlgCl l) ^ r‖ := by
  have na := norm_natCast_of_coprime ha
  have nb := norm_natCast_of_coprime hb
  have a0 : (a : PadicAlgCl l) ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [na]; exact one_ne_zero))
  have b0 : (b : PadicAlgCl l) ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [nb]; exact one_ne_zero))
  obtain ⟨k, hk⟩ := (h.pow e).dvd
  have hk' : (b : PadicAlgCl l) ^ e - (a : PadicAlgCl l) ^ e = (l : PadicAlgCl l) ^ r * (k : PadicAlgCl l) := by
    exact_mod_cast congrArg (Int.cast : ℤ → PadicAlgCl l) hk
  rw [inv_sub_inv a0 b0, hk', norm_div, norm_mul, norm_mul, norm_pow (a : PadicAlgCl l), norm_pow (b : PadicAlgCl l),
    na, nb, one_pow, one_mul, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ k)

theorem twist_compat (l : ℕ) [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e : ℕ)
    (χ : (r : ℕ) → (ZMod (l ^ r))ˣ → Formalism.ConjugateSelfDual.Qbar l)
    (hO : ∀ (r : ℕ) (x : (ZMod (l ^ r))ˣ), χ r x ∈ c.O)
    (hχ : ∀ (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r
      (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) : ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x)‖ ≤
        ‖(l : Formalism.ConjugateSelfDual.Qbar l) ^ r‖)
    (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ) :
    ‖(fun x : (ZMod (l ^ (r + 1)))ˣ => (((ZMod.val (x : ZMod (l ^ (r + 1))) : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ * χ (r + 1) x) x -
      (fun x : (ZMod (l ^ r))ˣ => (((ZMod.val (x : ZMod (l ^ r)) : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ * χ r x)
        (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) :
          ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x)‖ ≤ ‖(l : Formalism.ConjugateSelfDual.Qbar l) ^ r‖ := by
  have h1 := hχ r x
  generalize hy : Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) :
    ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x = y at h1 ⊢
  have hint : ‖χ r y‖ ≤ 1 :=
    norm_le_one_of_isIntegral
      ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨χ r y, hO r y⟩ : c.O)).map c.O.val)
  have hA := norm_inv_pow_val_le (r + 1) e x
  have hB := norm_inv_pow_val_le r e y
  have hAB : ‖((((x : ZMod (l ^ (r + 1))).val : ℕ) : PadicAlgCl l) ^ e)⁻¹ -
      ((((y : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹‖ ≤ ‖(l : PadicAlgCl l) ^ r‖ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [pow_zero (l : PadicAlgCl l), norm_one, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
      rwa [norm_neg]
    · refine norm_inv_pow_sub_le e
        ((ZMod.val_coe_unit_coprime x).coprime_dvd_right (dvd_pow_self l r.succ_ne_zero))
        ((ZMod.val_coe_unit_coprime y).coprime_dvd_right (dvd_pow_self l hr.ne')) ?_
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val, ← hy]
      rfl
  dsimp only
  set A := ((((x : ZMod (l ^ (r + 1))).val : ℕ) : PadicAlgCl l) ^ e)⁻¹
  set B := ((((y : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹
  have hsplit : A * χ (r + 1) x - B * χ r y = A * (χ (r + 1) x - χ r y) + (A - B) * χ r y := by ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hA).trans h1
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hint).trans hAB

end GlobalTheory.PadicNormCastBounds

end
end

section

namespace GlobalTheory.PadicInversePower

open Formalism.ConjugateSelfDual

theorem natCast_isUnit_padicInt (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem inv_pow_mem (l : ℕ) [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    (((x : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹ ∈ c.O := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (x : ZMod (l ^ 0)).val = 0 := by
      haveI : NeZero (l ^ 0) := ⟨by simp⟩
      exact Nat.lt_one_iff.mp (by simpa only [pow_zero] using ZMod.val_lt (x : ZMod (l ^ 0)))
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp only [pow_zero, inv_one]; exact c.O.one_mem
    · simp only [Nat.cast_zero, zero_pow he.ne', inv_zero]; exact c.O.zero_mem
  · let n := (x : ZMod (l ^ r)).val
    have hcop : l.Coprime n :=
      (ZMod.val_coe_unit_coprime x).symm.of_dvd_left (dvd_pow_self l hr.ne')
    have hnd : ¬ l ∣ n := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop
    obtain ⟨u, hu⟩ := (natCast_isUnit_padicInt l n hnd).pow e
    have key : ((n : Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ↑u⁻¹ := by
      rw [map_units_inv (algebraMap ℤ_[l] (Qbar l)) u, hu, map_pow, map_natCast]
    rw [key]
    exact c.O.algebraMap_mem _

end GlobalTheory.PadicInversePower
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.FockAdj

theorem fockQ_applyWord : Formalism.GradedWeylDivisibility.FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; rfl
  | cons x w ih =>
    intro F G
    have h1 : applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := rfl
    have h2 : applyWord ℚ (transposeWord (x :: w)) G =
        applyWord ℚ (transposeWord w) (rowDiv ℚ x.2.1 x.1 x.2.2 G) := by
      simp [applyWord, transposeWord, List.foldr_append]
    rw [h1, h2, fockQRowDivAdj, ih]

theorem map_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℚ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowAct ℚ g f) =
      rowAct ℂ (g.map (Rat.castHom ℂ)) (map (Rat.castHom ℂ) f) := by
  have : (map (Rat.castHom ℂ)).comp (rowAct ℚ (n := n) g).toRingHom =
      (rowAct ℂ (n := n) (g.map (Rat.castHom ℂ))).toRingHom.comp (map (Rat.castHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowAct]
    · intro v
      simp [rowAct]
  exact congrArg (fun φ => φ f) this

theorem fockQ_rowAct : Formalism.GradedWeylDivisibility.FockQRowAct := by
  intro r n g P Q
  have ht : (g.map (Rat.castHom ℂ)).conjTranspose = g.transpose.map (Rat.castHom ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h : ((fockQ (rowAct ℚ g P) Q : ℚ) : ℂ) = ((fockQ P (rowAct ℚ g.transpose Q) : ℚ) : ℂ) := by
    rw [lfockq_cast, lfockq_cast, map_rowAct, map_rowAct, fockRowAdj, ht]
  exact_mod_cast h

theorem fockQ_word_rowAct_adj : Formalism.GradedWeylDivisibility.FockQWordAdj ∧ Formalism.GradedWeylDivisibility.FockQRowAct :=
  ⟨fockQ_applyWord, fockQ_rowAct⟩

end GlobalTheory.FockAdj
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.FockHighestWeight

variable {r n : ℕ}

def diagExp (r : ℕ) (ν : Fin n → ℕ) : Fin r × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v.1.val = v.2.val then ν v.2 else 0

theorem diagExp_apply (ν : Fin n → ℕ) (a : Fin r) (s : Fin n) :
    diagExp r ν (a, s) = if a.val = s.val then ν s else 0 := rfl

theorem weight_rowW (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = ∑ s : Fin n, m (a, s) := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [rowW, Pi.single_apply]

theorem weight_rowW_diagExp (ν : Fin n → ℕ) :
    Finsupp.weight (rowW r n) (diagExp r ν) = rowNu (r := r) ν := by
  funext a
  rw [weight_rowW]
  simp only [diagExp_apply, rowNu]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Fin.ext e.symm)
    · simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg]
    have := s.2
    omega

theorem eq_diagExp_of_offDiag {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ}
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hoff : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0) : m = diagExp r ν := by
  ext ⟨a, s⟩
  rw [diagExp_apply]
  split_ifs with h
  · rw [← hcol s, Finset.sum_eq_single a]
    · intro b _ hb
      apply hoff
      intro e
      exact hb (Fin.ext (e.trans h.symm))
    · simp
  · exact hoff a s h

theorem lowerTri_of_interlaced {m : Fin r × Fin n →₀ ℕ} (hm : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 := by
    intro k
    induction k with
    | zero => intro s hs a ha; omega
    | succ k ih =>
      intro s hs a ha
      have hk : k < n := by have := s.2; omega
      have h := hm ⟨k, hk⟩ s hs a
      have h0 : ∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n)) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ?_
        have hb' : b.val < a.val := (Finset.mem_filter.mp hb).2
        exact ih ⟨k, hk⟩ rfl b (by simp only; omega)
      rw [h0] at h
      have h1 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
        Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _) (by simp)
      omega
  intro a s h
  exact key s.val s rfl a h

theorem eq_diagExp_of_lowerTri (hn : n ≤ r) {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ} (hm : LowerTri m)
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hrow : Finsupp.weight (rowW r n) m = rowNu (r := r) ν) : m = diagExp r ν := by
  refine eq_diagExp_of_offDiag hcol ?_
  have key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val ≠ s.val → m (a, s) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hs a ha
      let a0 : Fin r := ⟨s.val, by have := s.2; omega⟩
      have h1 : ∑ t : Fin n, m (a0, t) = ν s := by
        rw [← weight_rowW, hrow]
        simp [rowNu, a0]
      have h2 : m (a0, s) = ν s := by
        rw [← h1, Finset.sum_eq_single s]
        · intro t _ ht
          have ht' : t.val ≠ s.val := fun e => ht (Fin.ext e)
          rcases lt_or_gt_of_ne ht' with h | h
          · exact ih t.val (by omega) t rfl a0 (Ne.symm ht')
          · exact hm a0 t h
        · simp
      have hne : a ≠ a0 := fun e => ha (by rw [e])
      have h3 : ∑ b ∈ ({a, a0} : Finset (Fin r)), m (b, s) ≤ ∑ b : Fin r, m (b, s) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [Finset.sum_pair hne, hcol s] at h3
      omega
  intro a s h
  exact key s.val s rfl a h

theorem eval_idFrame_eq_coeff {R : Type*} [CommRing R] {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) R}
    (hcol : ∀ m ∈ F.support, ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) :
    eval (idFrame R r n) F = AddMonoidAlgebra.coeff F (diagExp r ν) := by
  rw [eval_eq', Finset.sum_eq_single (diagExp r ν)]
  · rw [Finset.prod_eq_one, mul_one]
    rintro ⟨a, s⟩ _
    rw [diagExp_apply, idFrame]
    split_ifs <;> simp
  · intro m hm hne
    have : ¬ ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0 :=
      fun h => hne (eq_diagExp_of_offDiag (hcol m hm) h)
    push Not at this
    obtain ⟨a, s, h1, h2⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ (a, s)), mul_zero]
    simp [idFrame, h1, h2]
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

theorem eval_idFrame_hw {R : Type*} [CommRing R] (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  rw [hw, map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, lpMinor, RingHom.map_det]
  have : ∀ (k : ℕ) (h1 : k ≤ r) (h2 : k ≤ n), (eval (idFrame R r n)).mapMatrix
      (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin r × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [idFrame, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one, one_pow]

theorem component_eq_smul_hw {R : Type} [CommRing R] [IsDomain R] (hn : n ≤ r) {ν : Fin n → ℕ} (hν : Antitone ν)
    {F : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) :
    weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F = eval (idFrame R r n) F • hw R hn ν := by
  classical
  rw [← sub_eq_zero]
  by_contra hG
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F - eval (idFrame R r n) F • hw R hn ν with hGdef
  have hH := hwMem R r n hn ν hν
  have hGm : G ∈ dualWeyl R r n ν :=
    Submodule.sub_mem _ (dualWeylRowGraded R r n ν _ F hF) (Submodule.smul_mem _ _ hH)
  have hGw : G ∈ weightedHomogeneousSubmodule R (rowW r n) (rowNu (r := r) ν) :=
    Submodule.sub_mem _ (weightedHomogeneousComponent_mem _ _ _)
      (Submodule.smul_mem _ _ (hwRowWeight R r n hn ν hν))
  have hd : (colLex r n).degree G ∈ G.support := (MonomialOrder.degree_mem_support_iff G).mpr hG
  have he := eq_diagExp_of_lowerTri hn (lowerTri_of_interlaced (leadInterlaced R r n ν G hGm hG))
    (colSums R r n ν G hGm _ hd) (hGw (mem_support_iff.mp hd))
  rw [he, mem_support_iff] at hd
  apply hd
  rw [hGdef, MvPolynomial.coeff_sub, coeff_weightedHomogeneousComponent, if_pos (weight_rowW_diagExp ν), MvPolynomial.coeff_smul,
    ← eval_idFrame_eq_coeff (colSums R r n ν F hF), ← eval_idFrame_eq_coeff (colSums R r n ν _ hH),
    eval_idFrame_hw]
  simp

theorem fockQ_hw : Formalism.GradedWeylDivisibility.FockQHW := by
  classical
  intro r n hn ν hν F hF
  have h := component_eq_smul_hw hn hν hF
  unfold fockQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' := hwRowWeight ℚ r n hn ν hν (mem_support_iff.mp hm)
  have h2 := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [coeff_weightedHomogeneousComponent, if_pos hw', MvPolynomial.coeff_smul, smul_eq_mul] at h2
  rw [h2]
  ring

end GlobalTheory.FockHighestWeight
end
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) (RatFunc k)),
  (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n → ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  first | exact @GlobalTheory.tsenLang_ratFunc | exact GlobalTheory.tsenLang_ratFunc | (intros; apply GlobalTheory.tsenLang_ratFunc <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.exists_unit_eq_div_of_locallyConstant_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : (Ω ≃ₐ[K] Ω) → Ωˣ),
  IsLocallyConstant w → (∀ g h, ((w (g * h) : Ωˣ) : Ω) = w g * g (w h)) → ∃ t : Ωˣ, ∀ g, ((w g : Ωˣ) : Ω) = g t / t := by
  first | exact @GlobalTheory.hilbert90_locallyConstant_cocycle | exact GlobalTheory.hilbert90_locallyConstant_cocycle | (intros; apply GlobalTheory.hilbert90_locallyConstant_cocycle <;> assumption)
end
