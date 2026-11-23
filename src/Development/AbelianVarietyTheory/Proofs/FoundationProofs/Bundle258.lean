module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpSeries

open PowerSeries

variable {K : Type} [Field K]

def euler (R : PowerSeries K) : PowerSeries K := X * derivativeFun R

theorem coeff_euler (R : PowerSeries K) (n : ℕ) : coeff n (euler R) = (n : K) * coeff n R := by
  cases n with
  | zero => simp [euler]
  | succ n =>
    rw [euler, coeff_succ_X_mul,
      show coeff n (derivativeFun R) = coeff (n + 1) R * ((n : K) + 1) from coeff_derivative R n]
    push_cast
    ring

theorem euler_one_add (R : PowerSeries K) : euler (1 + X * R) = X * (R + euler R) := by
  ext n
  cases n with
  | zero => simp [coeff_euler]
  | succ n =>
    simp only [coeff_euler, map_add (f := _), coeff_succ_X_mul, coeff_one]
    simp
    ring

def inv4 (R : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => coeff n R / (4 * ((n : K) + 2))

theorem inverseShiftedEulerOperatorFour_eq_iff [CharZero K] (R S : PowerSeries K) :
    inv4 S = R ↔ S = 4 * (2 * R + euler R) := by
  have h4 : (4 : PowerSeries K) = C 4 := (map_ofNat _ 4).symm
  have h2 : (2 : PowerSeries K) = C 2 := (map_ofNat _ 2).symm
  rw [PowerSeries.ext_iff, PowerSeries.ext_iff]
  refine forall_congr' fun n => ?_
  have hn : (4 * ((n : K) + 2)) ≠ 0 := by
    have : ((n : K) + 2) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    exact mul_ne_zero (by norm_num) this
  rw [inv4, coeff_mk, div_eq_iff hn, h4, h2, coeff_C_mul, map_add (f := _), coeff_C_mul, coeff_euler]
  constructor <;> intro h <;> rw [h] <;> ring

def rest (a b : K) (R : PowerSeries K) : PowerSeries K :=
  (euler R - R) ^ 2 - 12 * R ^ 2 - 4 * X * R ^ 3 + C a * X ^ 2 * (1 + X * R) + C b * X ^ 4

theorem contract (a b : K) (n : ℕ) (x y : PowerSeries K) (h : X ^ n ∣ x - y) :
    X ^ (n + 1) ∣ inv4 (X * rest a b x) - inv4 (X * rest a b y) := by
  have he : X ^ n ∣ euler x - euler y := by
    rw [X_pow_dvd_iff] at h ⊢
    intro m hm
    have := h m hm
    rw [map_sub, sub_eq_zero] at this
    rw [map_sub, coeff_euler, coeff_euler, this, sub_self]
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := he
  have hr : X ^ (n + 1) ∣ X * rest a b x - X * rest a b y := by
    refine ⟨(v - u) * (euler x - x + (euler y - y)) - 12 * u * (x + y)
      - 4 * X * u * (x ^ 2 + x * y + y ^ 2) + C a * X ^ 3 * u, ?_⟩
    unfold rest
    linear_combination X * (euler x - x + (euler y - y)) * hv +
      X * (-(euler x - x + (euler y - y)) - 12 * (x + y)
        - 4 * X * (x ^ 2 + x * y + y ^ 2) + C a * X ^ 3) * hu
  rw [X_pow_dvd_iff] at hr ⊢
  intro m hm
  have := hr m hm
  rw [map_sub, sub_eq_zero] at this
  rw [map_sub, inv4, inv4, coeff_mk, coeff_mk, this, sub_self]

theorem isWpSer_iff [CharZero K] (a b : K) (R : PowerSeries K) :
    IsWpSer a b (1 + X * R) ↔ inv4 (X * rest a b R) = R := by
  rw [inverseShiftedEulerOperatorFour_eq_iff]
  have he := euler_one_add R
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  unfold IsWpSer
  change _ ∧ (euler (1 + X * R) - _) ^ 2 = _ ↔ _
  rw [he]
  unfold rest
  constructor
  · rintro ⟨-, h⟩
    apply mul_left_cancel₀ hX
    linear_combination h
  · intro h
    refine ⟨by simp, ?_⟩
    linear_combination X * h

theorem eq_one_add {P : PowerSeries K} (h : constantCoeff P = 1) : ∃ R, P = 1 + X * R := by
  obtain ⟨R, hR⟩ : X ∣ P - 1 := by rw [X_dvd_iff]; simp [h]
  exact ⟨R, by linear_combination hR⟩

theorem existsUnique_isWpSer :
    ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  intro K _ _ a b
  obtain ⟨R, hR⟩ := GlobalTheory.GenusOneDatum.exists_fixed_of_contract
    (fun R : PowerSeries K => inv4 (X * rest a b R)) (contract a b)
  refine ⟨1 + X * R, (isWpSer_iff a b R).2 hR, fun P hP => ?_⟩
  obtain ⟨S, rfl⟩ := eq_one_add hP.1
  have hS := (isWpSer_iff a b S).1 hP
  have hd : ∀ n : ℕ, X ^ n ∣ S - R := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := contract a b n S R ih
      rwa [hS, show inv4 (X * rest a b R) = R from hR] at this
  have : S = R := by
    ext n
    have := X_pow_dvd_iff.1 (hd (n + 1)) n (by omega)
    rwa [map_sub, sub_eq_zero] at this
  rw [this]

end GlobalTheory.WpSeries
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SigmaDuplication

open Filter Topology

theorem sgStar_two_mul {Λ : AddSubgroup ℂ} (hΛ : GlobalTheory.EvenTheta.IsLat Λ) {P : ℂ} (hP : P ∉ Λ) :
    sgStar Λ (2 * P) = -(wpD Λ P) * sgStar Λ P ^ 4 := by
  obtain ⟨⟨hdiff, hd0, -, -⟩, hzero, -, hwp, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have h0 : sgStar Λ 0 = 0 := (hzero 0).2 (zero_mem Λ)
  have hPL : P ∉ L.lattice := fun hm => hP ((hL P).2 hm)
  have hwpfun : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hwpd : HasDerivAt (wpF Λ) (wpD Λ P) P := by
    rw [hwpfun, GlobalTheory.LatticeInvariants.wpD_eq hL P, ← congrFun L.deriv_weierstrassP P]
    exact ((L.differentiableOn_weierstrassP P hPL).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hPL)).hasDerivAt
  have hA : HasDerivAt (fun v => sgStar Λ (P + v)) (deriv (sgStar Λ) (P + P) * 1) P :=
    (hdiff (P + P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_add P)
  have hB : HasDerivAt (fun v => sgStar Λ (P - v)) (deriv (sgStar Λ) (P - P) * -1) P :=
    (hdiff (P - P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_sub P)
  have hS := (hdiff P).hasDerivAt.pow 2
  have hG := (hwpd.sub_const (wpF Λ P)).mul (hS.const_mul (sgStar Λ P ^ 2))
  have hev : (fun v => sgStar Λ (P + v) * sgStar Λ (P - v)) =ᶠ[𝓝 P]
      (fun v => (wpF Λ v - wpF Λ P) * (sgStar Λ P ^ 2 * sgStar Λ v ^ 2)) := by
    have hne : sgStar Λ P ≠ 0 := fun h => hP ((hzero P).1 h)
    filter_upwards [(hdiff.continuous.continuousAt (x := P)).eventually_ne hne] with v hv
    have hvΛ : v ∉ Λ := fun hm => hv ((hzero v).2 hm)
    linear_combination hwp P v hP hvΛ
  have huniq := (hA.mul hB).unique (hG.congr_of_eventuallyEq hev)
  simp only [sub_self, h0, hd0, Pi.pow_apply] at huniq
  rw [two_mul]
  linear_combination -huniq

theorem U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, P ∉ Λ →
    U1 Λ (2 * P) (sgStar Λ) 0 = -(wpD Λ P) * U1 Λ P (sgStar Λ) 0 ^ 4 := by
  intro Λ hΛ P hP
  show sgStar Λ (0 + 2 * P) * Complex.exp _ = -(wpD Λ P) * (sgStar Λ (0 + P) * Complex.exp _) ^ 4
  rw [zero_add, zero_add, sgStar_two_mul hΛ hP, mul_pow, ← Complex.exp_nat_mul, mul_assoc]
  congr 2
  simp only [map_mul, map_ofNat]
  push_cast
  ring_nf

end GlobalTheory.SigmaDuplication
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.ModelPoint

theorem wpD_sq {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    wpD Λ v ^ 2 = 4 * wpF Λ v ^ 3 - g2 Λ * wpF Λ v - g3 Λ := by
  obtain ⟨w₁, w₂, hi, hΛ⟩ := h
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  rw [GlobalTheory.LatticeInvariants.wpD_eq hL, GlobalTheory.LatticeInvariants.wpF_eq hL,
    GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
  exact L.derivWeierstrassP_sq v fun h => hv ((hL v).2 h)

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := dif_pos x.2

theorem lamC_neg_div_four (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) :
    lamC lam (-x / 4) = -lamC lam x / 4 := by
  lift x to Qbar using hx
  have e : (-(x : ℂ) / 4) = ((-x / 4 : Qbar) : ℂ) := by push_cast; rfl
  rw [e, lamC_coe, lamC_coe, map_div₀, map_neg, map_ofNat]

theorem lamC_eqn (lam : Qbar →+* ℂ_[p]) {x y a b : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar)
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (h : y ^ 2 = 4 * x ^ 3 - a * x - b) :
    lamC lam y ^ 2 = 4 * lamC lam x ^ 3 - lamC lam a * lamC lam x - lamC lam b := by
  lift x to Qbar using hx
  lift y to Qbar using hy
  lift a to Qbar using ha
  lift b to Qbar using hb
  have e : y ^ 2 = 4 * x ^ 3 - a * x - b := by
    apply Subtype.ext
    push_cast
    exact h
  have := congrArg lam e
  simpa only [lamC_coe, map_sub, map_mul, map_pow, map_ofNat] using this

theorem model_point : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → wpD g.abelian₂ v ∈ Qbar → g.W.toAffine.Equation (GlobalTheory.EvenTheta.xAt g v) (GlobalTheory.ThetaPar.yAt g v) ∧ 2 * GlobalTheory.ThetaPar.yAt g v + g.W.a₁ * GlobalTheory.EvenTheta.xAt g v + g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * lamC g.lam (wpD g.abelian₂ v) := by
  intro p _ g v hL h2 h3 hv hx hy
  have key := lamC_eqn g.lam hx hy h2 h3 (wpD_sq hL hv)
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt,
      lamC_neg_div_four g.lam h2, lamC_neg_div_four g.lam h3]
    linear_combination ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 / 4 * key
  · simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₃, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt]
    ring

end GlobalTheory.ThetaPar.ModelPoint
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.Chord

theorem chord_change {K : Type*} [Field K] [CharZero K] (e r s t a b c d : K) (he : e ≠ 0)
    (hac : a - c ≠ 0) :
    e ^ 2 * ((((b - d) / (a - c)) ^ 2 / 4 - a - c) - r) =
      ((e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
          (e ^ 2 * (a - r) - e ^ 2 * (c - r))) ^ 2 +
        (e * (2 * s)) * ((e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
          (e ^ 2 * (a - r) - e ^ 2 * (c - r))) - e ^ 2 * (3 * r - s ^ 2) -
        e ^ 2 * (a - r) - e ^ 2 * (c - r) := by
  have hm : (e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
      (e ^ 2 * (a - r) - e ^ 2 * (c - r)) = e * ((b - d) / (a - c) / 2 - s) := by
    rw [show e ^ 2 * (a - r) - e ^ 2 * (c - r) = e ^ 2 * (a - c) by ring]
    field_simp
    ring
  rw [hm]
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe' (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  unfold lamC
  rw [dite_eq_left x.2]

theorem W_a₁ (g : GL3Theta.G1 p) : g.W.a₁ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (2 * g.C.s) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₁]

theorem W_a₂ (g : GL3Theta.G1 p) :
    g.W.a₂ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (3 * g.C.r - g.C.s ^ 2) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₂]

theorem W_a₃ (g : GL3Theta.G1 p) :
    g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * (2 * g.C.t) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₃]

theorem xAt_add (g : GL3Theta.G1 p) (P Q : ℂ) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (hP : P ∉ g.abelian₂)
    (hQ : Q ∉ g.abelian₂) (h1 : P + Q ∉ g.abelian₂) (h2 : P - Q ∉ g.abelian₂) (a1 : wpF g.abelian₂ P ∈ Qbar)
    (a2 : wpD g.abelian₂ P ∈ Qbar) (a3 : wpF g.abelian₂ Q ∈ Qbar) (a4 : wpD g.abelian₂ Q ∈ Qbar) :
    GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) =
      ((yAt g P - yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 +
        g.W.a₁ * ((yAt g P - yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) -
        g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  have hne : wpF g.abelian₂ P ≠ wpF g.abelian₂ Q := fun e => by
    rcases (h.wp_eq_iff hP hQ).1 e.symm with h' | h'
    exacts [h1 h', h2 h']
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair g.abelian₂ h
  have hadd : wpF g.abelian₂ (P + Q) =
      ((wpD g.abelian₂ P - wpD g.abelian₂ Q) / (wpF g.abelian₂ P - wpF g.abelian₂ Q)) ^ 2 / 4 -
        wpF g.abelian₂ P - wpF g.abelian₂ Q := by
    simp only [GlobalTheory.LatticeInvariants.wpF_eq hL, GlobalTheory.LatticeInvariants.wpD_eq hL] at hne ⊢
    exact (GlobalTheory.weierstrassP_add L ((hL P).not.1 hP) ((hL Q).not.1 hQ) hne).1
  set A : Qbar := ⟨_, a1⟩
  set B : Qbar := ⟨_, a2⟩
  set C : Qbar := ⟨_, a3⟩
  set D : Qbar := ⟨_, a4⟩
  have eA : lamC g.lam (wpF g.abelian₂ P) = g.lam A := lamC_coe' g.lam A
  have eB : lamC g.lam (wpD g.abelian₂ P) = g.lam B := lamC_coe' g.lam B
  have eC : lamC g.lam (wpF g.abelian₂ Q) = g.lam C := lamC_coe' g.lam C
  have eD : lamC g.lam (wpD g.abelian₂ Q) = g.lam D := lamC_coe' g.lam D
  have eS : lamC g.lam (wpF g.abelian₂ (P + Q)) =
      ((g.lam B - g.lam D) / (g.lam A - g.lam C)) ^ 2 / 4 - g.lam A - g.lam C := by
    have : wpF g.abelian₂ (P + Q) = ((((B - D) / (A - C)) ^ 2 / 4 - A - C : Qbar) : ℂ) := by
      rw [hadd]; push_cast; rfl
    rw [this, lamC_coe']
    simp only [map_sub, map_div₀, map_pow, map_ofNat]
  have hAC : g.lam A - g.lam C ≠ 0 := fun e =>
    hne (congrArg Subtype.val (g.lam.injective (sub_eq_zero.1 e)))
  have he : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  rw [W_a₁, W_a₂]
  simp only [GlobalTheory.EvenTheta.xAt, yAt, eA, eB, eC, eD, eS]
  refine ⟨fun e => hAC ?_, chord_change _ _ _ _ _ _ _ _ he hAC⟩
  have := mul_left_cancel₀ (pow_ne_zero 2 he) e
  linear_combination this

theorem wpF_neg' {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) (z : ℂ) :
    wpF Λ (-z) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  simp only [GlobalTheory.LatticeInvariants.wpF_eq hL, PeriodPair.weierstrassP_neg]

theorem wpD_neg' {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) (z : ℂ) :
    wpD Λ (-z) = -wpD Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  simp only [GlobalTheory.LatticeInvariants.wpD_eq hL, PeriodPair.derivWeierstrassP_neg]

theorem xAt_neg (g : GL3Theta.G1 p) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (Q : ℂ) :
    GlobalTheory.EvenTheta.xAt g (-Q) = GlobalTheory.EvenTheta.xAt g Q := by
  simp only [GlobalTheory.EvenTheta.xAt, wpF_neg' h]

theorem yAt_neg (g : GL3Theta.G1 p) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (Q : ℂ)
    (a4 : wpD g.abelian₂ Q ∈ Qbar) :
    yAt g (-Q) = g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (yAt g Q) := by
  have e : lamC g.lam (-wpD g.abelian₂ Q) = -lamC g.lam (wpD g.abelian₂ Q) := by
    have e1 := lamC_coe' g.lam (-(⟨_, a4⟩ : Qbar))
    have e2 := lamC_coe' g.lam (⟨_, a4⟩ : Qbar)
    rw [map_neg, ← e2] at e1
    exact e1
  have e1 : g.W.toAffine.a₁ = _ := W_a₁ g
  have e3 : g.W.toAffine.a₃ = _ := W_a₃ g
  rw [WeierstrassCurve.Affine.negY, e1, e3]
  simp only [GlobalTheory.EvenTheta.xAt, yAt, wpF_neg' h, wpD_neg' h, e]
  ring

theorem model_chord : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P Q : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → Q ∉ g.abelian₂ → P + Q ∉ g.abelian₂ → P - Q ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → wpF g.abelian₂ Q ∈ Qbar → wpD g.abelian₂ Q ∈ Qbar → GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) = ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P - Q) = ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  intro p _ g P Q h _ _ hP hQ h1 h2 a1 a2 a3 a4
  obtain ⟨n, e⟩ := xAt_add g P Q h hP hQ h1 h2 a1 a2 a3 a4
  refine ⟨n, e, ?_⟩
  have := (xAt_add g P (-Q) h hP (by simpa using hQ) (by rwa [← sub_eq_add_neg])
    (by rwa [sub_neg_eq_add]) a1 a2 (by rwa [wpF_neg' h])
    (by rw [wpD_neg' h]; exact neg_mem a4)).2
  rwa [← sub_eq_add_neg, xAt_neg g h, yAt_neg g h Q a4] at this

end GlobalTheory.ThetaPar.Chord
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ModelDouble

open WeierstrassCurve

theorem weierstrassP_two_mul (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) (h2 : 2 * P ∉ L.lattice) :
    L.derivWeierstrassP P ≠ 0 ∧
      L.weierstrassP (2 * P) =
        ((3 * L.weierstrassP P ^ 2 - L.g₂ / 4) / L.derivWeierstrassP P) ^ 2 - 2 * L.weierstrassP P := by
  have hPP : P + P ∉ L.lattice := by rwa [← two_mul]
  have hd : L.derivWeierstrassP P ≠ 0 := (GlobalTheory.derivWeierstrassP_eq_zero_iff L hP).not.mpr hPP
  refine ⟨hd, ?_⟩
  have h := GlobalTheory.latticePoint_add L P P
  have hy : L.derivWeierstrassP P / 2 ≠
      (GlobalTheory.latticeCurve L).toAffine.negY (L.weierstrassP P) (L.derivWeierstrassP P / 2) := by
    simp only [WeierstrassCurve.Affine.negY, GlobalTheory.latticeCurve]
    intro e; apply hd; linear_combination e
  rw [GlobalTheory.latticePoint_of_notMem L hP, GlobalTheory.latticePoint_of_notMem L hPP,
    WeierstrassCurve.Affine.Point.add_of_Y_ne hy, WeierstrassCurve.Affine.Point.some.injEq] at h
  rw [two_mul, h.1, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, GlobalTheory.latticeCurve]
  rw [show L.derivWeierstrassP P / 2 - (-(L.derivWeierstrassP P / 2) - 0 * L.weierstrassP P - 0) = L.derivWeierstrassP P by ring]
  field_simp
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : Qbar} (hx : x ≠ 0) : lam x ≠ 0 :=
  (map_ne_zero lam).mpr hx

theorem tangent_law : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → 2 * P ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → 2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃ ≠ 0 ∧ GlobalTheory.EvenTheta.xAt g (2 * P) = ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) ^ 2 + g.W.a₁ * ((3 * GlobalTheory.EvenTheta.xAt g P ^ 2 + 2 * g.W.a₂ * GlobalTheory.EvenTheta.xAt g P + g.W.a₄ - g.W.a₁ * GlobalTheory.ThetaPar.yAt g P) / (2 * GlobalTheory.ThetaPar.yAt g P + g.W.a₁ * GlobalTheory.EvenTheta.xAt g P + g.W.a₃)) - g.W.a₂ - 2 * GlobalTheory.EvenTheta.xAt g P := by
  intro p _ g P hlat hg2 _ hP h2P hwF hwD
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair _ hlat
  obtain ⟨hd, hdup⟩ := weierstrassP_two_mul L ((hL P).not.mp hP) ((hL _).not.mp h2P)
  simp only [← GlobalTheory.LatticeInvariants.wpF_eq hL, ← GlobalTheory.LatticeInvariants.wpD_eq hL,
    ← GlobalTheory.LatticeInvariants.g2_eq hL] at hd hdup
  set a : Qbar := ⟨wpF g.abelian₂ P, hwF⟩ with ha
  set d : Qbar := ⟨wpD g.abelian₂ P, hwD⟩ with hd'
  set G : Qbar := ⟨g2 g.abelian₂, hg2⟩ with hG
  have hd0 : d ≠ 0 := fun h => hd (congrArg Subtype.val h)
  have he : wpF g.abelian₂ (2 * P) = (((((3 * a ^ 2 - G / 4) / d) ^ 2 - 2 * a : Qbar)) : ℂ) := by
    rw [hdup]; simp [a, d, G]; norm_cast
  have lX : lamC g.lam (wpF g.abelian₂ P) = g.lam a := lamC_coe _ a
  have lD : lamC g.lam (wpD g.abelian₂ P) = g.lam d := lamC_coe _ d
  have l2 : lamC g.lam (wpF g.abelian₂ (2 * P)) = ((3 * g.lam a ^ 2 - g.lam G / 4) / g.lam d) ^ 2 - 2 * g.lam a := by
    rw [he, lamC_coe]; simp [map_div₀, map_ofNat]
  have lA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam G) / 4 := by
    rw [show -(g2 g.abelian₂) / 4 = ((-G / 4 : Qbar) : ℂ) by simp [G]; norm_cast, lamC_coe]; simp [map_div₀, map_ofNat]
  have lD0 : g.lam d ≠ 0 := lamC_ne_zero _ hd0
  have ε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  simp only [GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt, GL3Theta.G1.W,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, wModel, lX, lD, l2, lA]
  set ε := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])
  set X := g.lam a
  set D := g.lam d
  have hden : 2 * (ε ^ 3 * (D / 2 - g.C.s * (X - g.C.r) - g.C.t)) + ε * (0 + 2 * g.C.s) * (ε ^ 2 * (X - g.C.r)) +
      ε ^ 3 * (0 + g.C.r * 0 + 2 * g.C.t) = ε ^ 3 * D := by ring
  rw [hden]
  refine ⟨mul_ne_zero (pow_ne_zero _ ε0) lD0, ?_⟩
  field_simp
  ring

end GlobalTheory.ModelDouble
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  first | exact @GlobalTheory.HalfPeriodTheta.theta_signed_translation | exact GlobalTheory.HalfPeriodTheta.theta_signed_translation | (intros; apply GlobalTheory.HalfPeriodTheta.theta_signed_translation <;> assumption)
end
