module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.RingTheory.PowerSeries.Derivative
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open Matrix MvPolynomial
namespace LateralTheory.DivDb.ChainPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N M : ℕ}

noncomputable def lin (φ : Mat C N →ₗ[C] Mat C M) (q : Fin M × Fin M) : MP C N :=
  ∑ r : Fin N × Fin N, MvPolynomial.C (φ (Matrix.single r.1 r.2 1) q.1 q.2) * X r

theorem sum_lin (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (q : Fin M × Fin M) :
    ∑ r : Fin N × Fin N, φ (Matrix.single r.1 r.2 1) q.1 q.2 * x r.1 r.2 = φ x q.1 q.2 := by
  have hx : x = ∑ r : Fin N × Fin N, x r.1 r.2 • Matrix.single r.1 r.2 (1 : C) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp [Matrix.smul_single]
  conv_rhs => rw [hx]

  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem ev_lin (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (q : Fin M × Fin M) :
    ev x (lin φ q) = φ x q.1 q.2 := by
  rw [← sum_lin φ x q]; simp [ev, lin]

theorem dAt_lin (φ : Mat C N →ₗ[C] Mat C M) (x Y : Mat C N) (q : Fin M × Fin M) :
    dAt (lin φ q) x Y = φ Y q.1 q.2 := by
  rw [← sum_lin φ Y q]

  simp only [dAt, lin, map_sum, Derivation.leibniz, pderiv_X, pderiv_C, smul_zero, add_zero, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [ev, Pi.single_apply, Finset.sum_ite_eq']

theorem ev_bind (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (f : MP C M) :
    ev x (bind₁ (lin φ) f) = ev (φ x) f := by
  show eval₂Hom (RingHom.id C) _ (bind₁ (lin φ) f) = eval₂Hom (RingHom.id C) _ f
  rw [eval₂Hom_bind₁]
  congr 2; funext q; exact ev_lin φ x q

theorem dAt_add (f g : MP C N) (x Y : Mat C N) : dAt (f + g) x Y = dAt f x Y + dAt g x Y := by
  simp [dAt, ev, add_mul, Finset.sum_add_distrib]

theorem dAt_mul (f g : MP C N) (x Y : Mat C N) :
    dAt (f * g) x Y = ev x f * dAt g x Y + ev x g * dAt f x Y := by
  simp only [dAt, Derivation.leibniz, smul_eq_mul, ev, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem dAt_C (a : C) (x Y : Mat C N) : dAt (MvPolynomial.C a : MP C N) x Y = 0 := by
  simp [dAt, ev]

theorem chain_of : Chain := by
  intro C _ N M φ f
  refine ⟨bind₁ (lin φ) f, fun x => ?_, ?_⟩
  · exact ev_bind φ x f
  · induction f using MvPolynomial.induction_on with
    | C a => intro x Y; simp [dAt_C]
    | add f g hf hg => intro x Y; rw [map_add (f := _), dAt_add, dAt_add, hf, hg]
    | mul_X f q hf =>
      intro x Y
      rw [map_mul, bind₁_X_right, dAt_mul, dAt_mul, hf, dAt_lin, ev_lin]
      rw [ev_bind]
      simp [dAt, ev, pderiv_X, Pi.single_apply]

end LateralTheory.DivDb.ChainPf

theorem LateralTheory.DivDb.Chain_of : LateralTheory.DivDb.Chain := LateralTheory.DivDb.ChainPf.chain_of
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TanLiePf
open LateralTheory.DivDb

theorem DX_X {C : Type} [Field C] {N : ℕ} (Y : Mat C N) (p : Fin N × Fin N) :
    DX Y (MvPolynomial.X p) = ∑ k, MvPolynomial.C (Y p.1 k) * MvPolynomial.X (k, p.2) := by
  simp [DX, MvPolynomial.mkDerivation_X]

theorem DX_comm {C : Type} [Field C] {N : ℕ} (Y Z : Mat C N) :
    ⁅DX Y, DX Z⁆ = DX (Z * Y - Y * Z) := by
  apply MvPolynomial.derivation_ext
  intro p
  rw [Derivation.commutator_apply, DX_X, DX_X, DX_X]

  simp only [map_sum, MvPolynomial.C_mul', map_smul, DX_X, Finset.smul_sum, smul_smul]
  simp only [Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  simp only [sub_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Derivation.map_smul, Derivation.map_smul, DX_X, DX_X]
  simp only [MvPolynomial.C_mul', Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]

end LateralTheory.DivDb.TanLiePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.TanLiePf

theorem TanLie_of (hF : TanField) : TanLie := by
  intro C _ N S Y hY Z hZ
  have hY' := (hF C N S Y).1 hY
  have hZ' := (hF C N S Z).1 hZ
  have h : Z * Y - Y * Z ∈ Tan (S : Set (Mat C N)) := by
    rw [hF C N S]
    intro f hf
    rw [← DX_comm, Derivation.commutator_apply]
    intro x hx
    have h1 := hY' _ (hZ' f hf) x hx
    have h2 := hZ' _ (hY' f hf) x hx
    simp only [ev, map_sub] at h1 h2 ⊢
    rw [h1, h2, sub_zero]
  have := (Tan (S : Set (Mat C N))).neg_mem h
  simpa using this

end LateralTheory.DivDb
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ExpVanPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C] {N : ℕ}

noncomputable def E (Y : Mat C N) : Fin N × Fin N → PowerSeries C :=
  fun p => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) p.1 p.2

noncomputable def F (Y : Mat C N) (f : MP C N) : PowerSeries C := MvPolynomial.aeval (E Y) f

theorem deriv_E (Y : Mat C N) (p : Fin N × Fin N) :
    PowerSeries.derivative (R := C) (E Y p) = MvPolynomial.aeval (E Y) (DX Y (MvPolynomial.X p)) := by
  rw [DX, MvPolynomial.mkDerivation_X]
  ext n

  rw [PowerSeries.coeff_derivative, map_sum, map_sum]
  simp only [E, PowerSeries.coeff_mk, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  have hn : ((n + 1).factorial : C)⁻¹ * (n + 1) = (n.factorial : C)⁻¹ := by
    have : ((n:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Nat.factorial_succ]; push_cast; field_simp
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Algebra.smul_def, map_smul, PowerSeries.coeff_mk, smul_eq_mul, ← hn]; ring

omit [CharZero C] in
theorem cc_F (Y : Mat C N) (f : MP C N) : PowerSeries.constantCoeff (F Y f) = ev 1 f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F, ev]
  | add p q hp hq => simp only [F, ev, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, ev, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X] at *
    rw [hp]; congr 1
    simp [E]

theorem deriv_F (Y : Mat C N) (f : MP C N) :
    PowerSeries.derivative (R := C) (F Y f) = F Y (DX Y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F]
  | add p q hp hq => simp only [F, map_add (f := _)] at * <;> rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, map_mul, Derivation.leibniz, MvPolynomial.aeval_X, smul_eq_mul, map_add (f := _)] at *
    rw [hp, ← deriv_E]

theorem coeff_F (hT : TanField) (S : Submonoid (Mat C N)) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) :
    ∀ k, ∀ f ∈ Van (S : Set (Mat C N)), PowerSeries.coeff k (F Y f) = 0 := by
  intro k
  induction k with
  | zero =>
    intro f hf
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_F]
    exact hf 1 S.one_mem
  | succ k ih =>
    intro f hf
    have h := ih _ ((hT C N S Y).1 hY f hf)
    rw [← deriv_F, PowerSeries.coeff_derivative] at h
    have : ((k:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp h).resolve_right this

end LateralTheory.DivDb.ExpVanPf

namespace LateralTheory.DivDb
theorem ExpVan_of (hT : TanField) : ExpVan := by
  intro C _ _ N S Y hY f hf
  ext k
  have h := ExpVanPf.coeff_F hT S Y hY k f hf
  rw [map_zero]; exact h
end LateralTheory.DivDb
end
