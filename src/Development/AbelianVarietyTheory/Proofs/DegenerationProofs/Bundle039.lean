module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem secOn_pull_surjective_of_surjective :
    ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ H : LB X, H.IsLB → ∀ D : X.Opens, IsAffineOpen D → Function.Surjective (SecOn.pull H β D) := by
  intro A A' _ _ g hg X X' f f' β hβ H hH D hD y
  letI := g.toAlgebra
  obtain ⟨z, hz⟩ := (SecOnR.baseChangeHom_bijective (R := A) (R' := A') hH hβ hD rfl).2 y
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective A (SecOnR f H D) A' hg z
  refine ⟨x, ?_⟩
  have h := (SecOnR.baseChangeHom_tmul (R := A) (R' := A') hβ.w le_rfl 1 x).symm.trans hz
  rw [one_smul] at h
  exact (SecOn.pullLE_self β x).symm.trans h

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pow_section' : ∀ (X X' : Scheme.{0}) (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β] [CompactSpace X] [QuasiSeparatedSpace X], (∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0) → ∀ H : LB X, H.IsLB → ∀ (s₀ : LB.Sec (H.pull β)) (D : X.Opens), β ⁻¹ᵁ D = nonzeroLocus s₀ → ∀ t : SecOn H D, SecOn.pull H β D t = GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D) → ∃ n : ℕ, 1 ≤ n ∧ ∃ σ : LB.Sec (pw H n), nonzeroLocus σ = D := by
  first | exact @GlobalTheory.SecPow.exists_pow_section | exact GlobalTheory.SecPow.exists_pow_section | (intros; apply GlobalTheory.SecPow.exists_pow_section <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.Ex
namespace NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem Form.div_add_left {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + y) z / j = β.be x z / j + β.be y z / j := by
  rw [β.symm, β.div_add hj, β.symm z, β.symm z]

theorem Form.div_add_nsmul {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + j • y) z / j = β.be x z / j + β.be y z := by
  rcases eq_or_ne j 0 with rfl | h
  · obtain rfl : k = 0 := Nat.eq_zero_of_zero_dvd hj
    have h0 : β.be y z = 0 := by simpa using β.dvd y z
    simp [h0]
  · rw [β.div_add_left hj, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 h)]

theorem Form.div_nsmul {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (m : ℕ) (x y : N.X) :
    β.be x (m • y) / j = β.be x y / j * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, β.div_add hj, ih]; push_cast; ring

theorem Form.exp_count {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m) (y χ : N.X) :
    β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) =
      β.be y y / 2 - β.be y y / (m ^ 2 : ℕ) * ((m ^ 2 - 1) / 2 : ℕ) + β.be χ χ / 2 + β.be y χ / (m ^ 2 : ℕ) * m := by
  have hd : ∀ x z, (2 * (m : ℤ) ^ 2) ∣ β.be x z := fun x z =>
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd x z)
  obtain ⟨a, ha⟩ := hd y y
  obtain ⟨b, hb⟩ := hd y χ
  obtain ⟨c, hc⟩ := hd χ χ
  obtain ⟨t, ht⟩ := ho.pow (n := 2)
  have hm0 : (m : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.2 ho.pos.ne')
  have h1 : (m ^ 2 - 1) / 2 = t := by omega
  have h2 : (m : ℤ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
  have e : β.be (y + m • χ) (y + m • χ) = 2 * m ^ 2 * (a + 2 * m * b + m ^ 2 * c) := by
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, β.symm χ y, ha, hb, hc]
    ring
  have d1 : ∀ x : ℤ, 2 * (m : ℤ) ^ 2 * x / 2 = m ^ 2 * x := fun x => by
    rw [mul_assoc, Int.mul_ediv_cancel_left _ two_ne_zero]
  have d2 : ∀ x : ℤ, 2 * (m : ℤ) ^ 2 * x / (m ^ 2 : ℕ) = 2 * x := fun x => by
    rw [Nat.cast_pow, mul_right_comm, Int.mul_ediv_cancel _ hm0]
  rw [e, h1, ha, hb, hc, d1, d1, d2, d2, Int.mul_ediv_cancel_left _ (mul_ne_zero two_ne_zero hm0)]
  linear_combination (-a) * h2

theorem twist_wQ {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (p : N.QT j) :
    (N.twist β u).wQ (N.twQ β u hj p) =
      u ^ (β.be p.1.1.toAdd p.1.1.toAdd / 2 - β.be p.1.1.toAdd p.1.1.toAdd / j * ((j - 1) / 2 : ℕ)) * N.wQ p := by
  show N.ψ p.1.1.toAdd * u ^ (β.be p.1.1.toAdd p.1.1.toAdd / 2) * mulq N.θ N.σ j p.1.2.b /
      (p.1.2.s p.1.1.toAdd * u ^ (β.be p.1.1.toAdd p.1.1.toAdd / j) * cubN N.θ j 1 p.1.2.b p.1.2.b /
        dbl N.θ N.σ p.1.2.b ^ j) ^ ((j - 1) / 2) = _ * (N.ψ p.1.1.toAdd * mulq N.θ N.σ j p.1.2.b /
      (p.1.2.s p.1.1.toAdd * cubN N.θ j 1 p.1.2.b p.1.2.b / dbl N.θ N.σ p.1.2.b ^ j) ^ ((j - 1) / 2))
  rw [zpow_sub, zpow_mul, zpow_natCast, mul_right_comm (p.1.2.s _), mul_div_right_comm _ (u ^ _), mul_pow]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel

theorem twist_vt {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (m : ℕ) (χ : N.X) :
    (N.twist β u).vt (N.twG β u g l hl ^ m) χ = (u ^ (β.be χ χ / 2 + l χ * m) : Oˣ) * N.vt (g ^ m) χ := by
  obtain ⟨h1, h2⟩ := N.twG_pow β u g l hl m
  show ((N.ψ χ * u ^ (β.be χ χ / 2) * (N.twG β u g l hl ^ m).s χ : Oˣ) : O) *
    N.th (N.c χ * (show N.A from (N.twG β u g l hl ^ m).b)) = _ * (((N.ψ χ * (g ^ m).s χ : Oˣ) : O) * N.th (N.c χ * (g ^ m).b))
  rw [h1, h2, ← mul_assoc (_ : O), ← Units.val_mul, zpow_add]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul]; abel

theorem twG_mul {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) :
    N.twG β u g l hl * N.twG β u g' l' hl' =
      N.twG β u (g * g') (fun z => l z + l' z) (fun a b => by rw [hl, hl']; ring) := by
  refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
  show g.s z * u ^ l z * (g'.s z * u ^ l' z) / N.θ (N.c z) g.b g'.b =
    g.s z * g'.s z / N.θ (N.c z) g.b g'.b * u ^ (l z + l' z)
  rw [zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twG_congr {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) (h : ∀ z, l z = l' z) : N.twG β u g l hl = N.twG β u g l' hl' := by
  obtain rfl : l = l' := funext h
  rfl

theorem twG_inj {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (h : N.twG β u g l hl = N.twG β u g' l hl) : g = g' :=
  NumD.Gt.ext (congrArg (fun x : (N.twist β u).Gt => x.b) h)
    (funext fun z => mul_right_cancel (congrArg (fun x : (N.twist β u).Gt => x.s z) h))

theorem twist_io {k : ℕ} (β : N.Form k) (u : Oˣ) (y : N.X) :
    (N.twist β u).io y = N.twG β u (N.io y) (fun z => β.be y z) (fun a b => map_add _ a b) :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => N.twist_τ β u y z)

theorem twist_txT {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    (N.twist β u).txT m (N.twQ β u hm p) χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ := by
  show (((N.twist β u).wQ (N.twQ β u hm p) / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) *
    (N.twist β u).vt (N.twG β u p.1.2 _ (β.div_add hm p.1.1.toAdd) ^ m) χ =
      _ * (((N.wQ p / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) * N.vt (p.1.2 ^ m) χ)
  rw [twist_wQ, twist_vt, β.exp_count hm ho, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twist_evT {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m) (p : N.QT (m ^ 2)) (χ : N.X)
    {j : ℕ} (hj : j ∣ k) (q : N.QT j) :
    (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ := by
  show ((q.1.2.s p.1.1.toAdd * u ^ (β.be q.1.1.toAdd p.1.1.toAdd / j) * cubN N.θ (m ^ 2) 1 p.1.2.b q.1.2.b *
    (N.twist β u).wQ (N.twQ β u hm p) / mulq N.θ N.σ m (q.1.2.b * p.1.2.b) : Oˣ) : O) *
    (N.twist β u).vt ((N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) *
      N.twG β u p.1.2 _ (β.div_add hm p.1.1.toAdd)) ^ m) χ =
      _ * (((q.1.2.s p.1.1.toAdd * cubN N.θ (m ^ 2) 1 p.1.2.b q.1.2.b *
        N.wQ p / mulq N.θ N.σ m (q.1.2.b * p.1.2.b) : Oˣ) : O) * N.vt ((q.1.2 * p.1.2) ^ m) χ)
  rw [twG_mul, twist_wQ, twist_vt, β.exp_count hm ho, β.div_add hj, β.div_nsmul hj, ← mul_assoc (_ : O), ← mul_assoc (_ : O),
    ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [add_mul, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twist_wp {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' := by
  show q.1.2.s q'.1.1.toAdd * u ^ (β.be q.1.1.toAdd q'.1.1.toAdd / j) * cubN N.θ j 1 q'.1.2.b q.1.2.b /
    (q'.1.2.s q.1.1.toAdd * u ^ (β.be q'.1.1.toAdd q.1.1.toAdd / j) * cubN N.θ j 1 q.1.2.b q'.1.2.b) =
    q.1.2.s q'.1.1.toAdd * cubN N.θ j 1 q'.1.2.b q.1.2.b / (q'.1.2.s q.1.1.toAdd * cubN N.θ j 1 q.1.2.b q'.1.2.b)
  rw [β.symm q'.1.1.toAdd]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twQ_mul {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show N.twG β u (q.1.2 * q'.1.2) _ (β.div_add hj (q.1.1.toAdd + q'.1.1.toAdd)) =
    N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) * N.twG β u q'.1.2 _ (β.div_add hj q'.1.1.toAdd)
  rw [twG_mul]
  exact N.twG_congr β u _ _ _ _ _ fun z => β.div_add_left hj _ _ z

theorem twist_qEq {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q') := by
  refine exists_congr fun (z : N.X) => and_congr_right fun (h : q'.1.1.toAdd = q.1.1.toAdd + j • z) => ?_
  show _ ↔ N.twG β u q'.1.2 _ (β.div_add hj q'.1.1.toAdd) =
    N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) * (N.twist β u).io z
  rw [twist_io, twG_mul, ← N.twG_congr β u (q.1.2 * N.io z) (fun x => β.be q'.1.1.toAdd x / j)
    (fun x => β.be q.1.1.toAdd x / j + β.be z x) (β.div_add hj q'.1.1.toAdd) _
    fun x => by rw [h, β.div_add_nsmul hj]]
  exact ⟨fun e => by rw [e], N.twG_inj β u _ _ _ _⟩

end NumD

theorem twist_terms : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p : N.QT (m ^ 2)) (χ : N.X), (N.twist β u).txT m (N.twQ β u hm p) χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ ∧ (∀ (j : ℕ) (hj : j ∣ k) (q : N.QT j), j ≠ 0 → (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) + β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q q' : N.QT j), (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' ∧ N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' ∧ (N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q')) :=
  fun _ _ N _ β u m hm ho p χ => ⟨N.twist_txT β u m hm ho p χ, fun _ hj q _ => N.twist_evT β u m hm ho p χ hj q,
    fun _ hj q q' => ⟨N.twist_wp β u hj q q', N.twQ_mul β u hj q q', N.twist_qEq β u hj q q'⟩⟩
end GlobalTheory.Ex
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

theorem NumD.exists_descent_subring : ∀ (O F : Type) [CommRing O] [CommRing F] (io : O →+* F), Function.Injective io → ∀ (N : NumD F) (A₀ : Subgroup N.A), (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, ∃ a : Oˣ, io a = N.θ x y u) → (∀ x ∈ A₀, ∃ a : Oˣ, io a = N.σ x) → (∀ x ∈ A₀, ∃ a : O, io a = N.th x) → (∀ χ, ∃ a : Oˣ, io a = N.ψ χ) → ∃ (N₀ : NumD O) (I : NumD.Hom io N₀ N), I.lam = 1 ∧ ∀ (k : ℕ) (p : N.QT k), p.1.2.b ∈ A₀ → (∀ χ, ∃ a : Oˣ, io a = p.1.2.s χ) → ∃ p₀ : N₀.QT k, p.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p.1.2 := by
  intro O F _ _ io hio N A₀ hc hθ hσ hth hψ
  have hθ' : ∀ x y u : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.θ x y u := fun x y u =>
    (hθ x x.2 y y.2 u u.2).imp fun a h => Units.ext h
  have hσ' : ∀ x : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.σ x := fun x =>
    (hσ x x.2).imp fun a h => Units.ext h
  have hth' : ∀ x : A₀, ∃ a : O, io a = N.th x := fun x => hth x x.2
  have hψ' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.ψ χ := fun χ =>
    (hψ χ).imp fun a h => Units.ext h
  choose θ eθ using hθ'
  choose σ eσ using hσ'
  choose th eth using hth'
  choose ψ eψ using hψ'
  have inj : Function.Injective (Units.map io.toMonoidHom) := Units.map_injective hio
  let B₀ : NumB O :=
    { A := A₀
      θ := θ
      cub :=
        { face := fun x y => inj (by rw [eθ, map_one]; exact N.cub.face _ _)
          s01 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s01 _ _ _)
          s12 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s12 _ _ _)
          coc := fun x x' x'' y => inj (by simp only [map_mul, eθ]; exact N.cub.coc _ _ _ _) }
      σ := σ
      σ_one := inj (by rw [eσ, map_one]; exact N.σ_one)
      σ_mul := fun x y => inj (by simp only [map_mul, eθ, eσ]; exact N.σ_mul _ _)
      th := th }
  let N₀ : NumD O :=
    { toNumB := B₀
      X := N.X
      c := fun χ => (⟨N.c χ, hc χ⟩ : A₀)
      c_add := fun a b => Subtype.ext (N.c_add a b)
      ψ := ψ
      even := fun χ => inj (by
        change Units.map io.toMonoidHom (ψ (-χ) * σ ⟨N.c χ, hc χ⟩) = _
        simp only [map_mul, eψ, eσ]; exact N.even χ)
      bimult := fun a a' b => inj (by
        change Units.map io.toMonoidHom (_ * θ ⟨N.c a, hc a⟩ ⟨N.c a', hc a'⟩ ⟨N.c b, hc b⟩) = _
        simp only [map_mul, map_div, eψ, eθ]; exact N.bimult a a' b) }
  let I : NumD.Hom io N₀ N :=
    { φ := A₀.subtype
      h := fun _ => 1
      h_one := rfl
      θ_eq := fun (x y u : A₀) => by
        simp only [mul_one]; exact (eθ x y u).symm
      σ_eq := fun (x : A₀) => by
        simp only [mul_one]; exact (eσ x).symm
      lam := 1
      th_eq := fun (x : A₀) => by
        simp only [mul_one, Units.val_one, one_mul]; exact (eth x).symm
      e := AddEquiv.refl N.X
      c_eq := fun _ => rfl
      ψ_eq := fun (χ : N.X) => by
        simp only [mul_one]; exact (eψ χ).symm }
  let Φ : N₀.Gt →* N.Gt := MonoidHom.mk'
    (fun g => ⟨((show A₀ from g.b) : N.A), fun (χ : N.X) => Units.map io.toMonoidHom (g.s χ), fun (χ χ' : N.X) => by
      have := congrArg (Units.map io.toMonoidHom) (g.mult χ χ')
      rw [map_mul, map_mul] at this
      rw [← this]
      exact congrArg _ (eθ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ g.b).symm⟩)
    (fun g g' => NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (g.s χ * g'.s χ / θ ⟨N.c χ, hc χ⟩ g.b g'.b) = _
      rw [map_div, map_mul, eθ]; rfl))
  have Φinj : Function.Injective Φ := fun g g' h =>
    NumD.Gt.ext (Subtype.ext (congrArg NumD.Gt.b h))
      (funext fun (χ : N.X) => inj (congrArg (fun z : N.Gt => z.s χ) h))
  have Φio : ∀ y : N.X, Φ (N₀.io y) = N.io y := fun y =>
    NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (ψ (y + χ) / ψ y / ψ χ) = _
      rw [map_div, map_div, eψ, eψ, eψ]; rfl)
  refine ⟨N₀, I, rfl, fun k p hb hs => ?_⟩
  have hs' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = p.1.2.s χ := fun χ =>
    (hs χ).imp fun a h => Units.ext h
  choose s es using hs'
  let g₀ : N₀.Gt := ⟨(⟨p.1.2.b, hb⟩ : A₀), s, fun (χ χ' : N.X) => inj (by
    change Units.map io.toMonoidHom (s (χ + χ') * θ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ ⟨p.1.2.b, hb⟩) = _
    simp only [map_mul, es, eθ]; exact p.1.2.mult χ χ')⟩
  have hg : Φ g₀ = p.1.2 := NumD.Gt.ext rfl (funext fun χ => es χ)
  refine ⟨⟨(p.1.1, g₀), Φinj ?_⟩, rfl, rfl, fun (χ : N.X) => ?_⟩
  · change Φ (g₀ ^ k) = Φ (N₀.io (show N.X from p.1.1.toAdd))
    rw [map_pow, hg, Φio]; exact p.2
  · change p.1.2.s χ * 1 = Units.map io.toMonoidHom (s χ) * 1 * 1
    rw [es, mul_one, mul_one]

end GlobalTheory.Ex
end

section

open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.HomCalc
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def comp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') : NumD.Hom (g.comp f) N N'' where
  φ := I'.φ.comp I.φ
  h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
  h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
  θ_eq x y u := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.θ_eq x y u)
    have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
    have c : Units.map (g.comp f).toMonoidHom (N.θ x y u) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.θ x y u)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
    linear_combination (norm := abel) a + b
  σ_eq x := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.σ_eq x)
    have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
    have c : Units.map (g.comp f).toMonoidHom (N.σ x) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.σ x)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply, map_inv I.φ] at a b ⊢
    linear_combination (norm := abel) a + b
  lam := I'.lam * Units.map g.toMonoidHom I.lam
  th_eq x := by
    rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq]
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.comp_apply]
    ring
  e := I.e.trans I'.e
  c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
  ψ_eq χ := by
    have c : Units.map (g.comp f).toMonoidHom (N.ψ χ) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.ψ χ)) := rfl
    rw [c, ← I.ψ_eq, map_mul, ← I'.ψ_eq, I.c_eq, AddEquiv.trans_apply, mul_assoc]

theorem comp_rel {I : NumD.Hom f N N'} {I' : NumD.Hom g N' N''} {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b)
    (h' : I'.Rel b c) : (comp I I').Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have u := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (h.2 χ)
  have v := congrArg Additive.ofMul (h'.2 (I.e χ))
  have w : Units.map (g.comp f).toMonoidHom (a.s χ) = Units.map g.toMonoidHom (Units.map f.toMonoidHom (a.s χ)) := rfl
  rw [I.c_eq, h.1] at v
  show c.s (I'.e (I.e χ)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) =
    _ * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _))
  apply Additive.ofMul.injective
  simp only [w, map_mul, ofMul_mul] at u v ⊢
  linear_combination (norm := abel) u + v

def inv {M M' : NumD O} (I : NumD.Iso M' M) : NumD.Hom (RingHom.id O) M M' where
  φ := I.φ.symm.toMonoidHom
  h x := (I.h (I.φ.symm x))⁻¹
  h_one := by rw [map_one, I.h_one, inv_one]
  θ_eq x y u := by
    have a := congrArg Additive.ofMul (I.θ_eq (I.φ.symm x) (I.φ.symm y) (I.φ.symm u))
    show M'.θ (I.φ.symm x) (I.φ.symm y) (I.φ.symm u) * _ * _ * _ = M.θ x y u * _ * _ * _ * _
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  σ_eq x := by
    have a := congrArg Additive.ofMul (I.σ_eq (I.φ.symm x))
    show M'.σ (I.φ.symm x) * _ = M.σ x * _
    apply Additive.ofMul.injective
    simp only [map_inv I.φ.symm, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  lam := I.lam⁻¹
  th_eq x := by
    have a := I.th_eq (I.φ.symm x)
    rw [MulEquiv.apply_symm_apply] at a
    show M'.th (I.φ.symm x) = _ * M.th x
    rw [a, ← mul_inv, Units.inv_mul_cancel_left]
  e := I.e.symm
  c_eq χ := by
    show _ = I.φ.symm _
    rw [MulEquiv.eq_symm_apply, ← I.c_eq, AddEquiv.apply_symm_apply]
  ψ_eq χ := by
    obtain ⟨χ, rfl⟩ := I.e.surjective χ
    show _ = M.ψ _
    rw [AddEquiv.symm_apply_apply, I.c_eq, MulEquiv.symm_apply_apply, ← I.ψ_eq, mul_inv_cancel_right]

theorem inv_rel {M M' : NumD O} {I : NumD.Iso M' M} {a : M'.Gt} {b : M.Gt} (h : I.Rel a b) : (inv I).Rel b a := by
  refine ⟨(I.φ.symm_apply_eq.2 h.1).symm, fun χ => ?_⟩
  obtain ⟨χ, rfl⟩ := I.e.surjective χ
  have u := congrArg Additive.ofMul (h.2 χ)
  show a.s (I.e.symm _) * (I.h (I.φ.symm _))⁻¹ = b.s _ * (I.h (I.φ.symm _))⁻¹ * (I.h (I.φ.symm _))⁻¹
  rw [AddEquiv.symm_apply_apply, I.c_eq, h.1, ← map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, MulEquiv.symm_apply_apply] at u ⊢
  linear_combination (norm := abel) -u

end GlobalTheory.HomCalc
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_productFormula_places_of_fg_field : ∀ (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k K], (⊤ : IntermediateField k K).FG → ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → x ∈ Set.range (algebraMap k K) := by
  first | exact @GlobalTheory.SS.exists_places_of_fg | exact GlobalTheory.SS.exists_places_of_fg | (intros; apply GlobalTheory.SS.exists_places_of_fg <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ModelData

def Labels {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La)
    (ζ : ℕ → Oˣ) (lab : ∀ k : ℕ, La → N.QT k) : Prop :=
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a * lab k b) (lab k (a + b))) ∧
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ ∃ e, a = b + k • e) ∧
  (∀ k, 0 < k → ∀ p, ∃ a, N.QEq (lab k a) p) ∧
  (∀ k m, 0 < k → 0 < m → ∀ a (p : N.QT k), p.1.1 = (lab (k * m) a).1.1 → p.1.2 = (lab (k * m) a).1.2 ^ m →
    N.QEq p (lab k a)) ∧
  ∀ k, 0 < k → ∀ a b, N.wp (lab k a) (lab k b) = ζ k ^ EF a b

def Strict {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) : Prop :=
  ∃ c : L.ι → L'.ι, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι), F (r z) ∈ L.U j →
    r z ∈ L'.U (c j) ∧ gw w r z j (c j) = 1

theorem exists_strict {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) :
    ∃ w : LB.Iso (L.pull F) (L.pull F), w.IsGen ∧ Strict w := by
  have hL' := pull_isLB hL F
  refine ⟨⟨fun j => (L.pull F).g j.1 j.2⟩, (isGen_iff _).2 fun Y f y j j' k k' hj hj' hk hk' => ?_,
    fun j _ => j, fun Z r z j hj => ⟨mem_pull.2 hj, gm_self hL' r z (mem_pull.2 hj)⟩⟩
  have a := gm_cocycle hL' f y (i := fun _ => j) (j := fun _ => j') (k := k') (mem_pull.2 hj) (mem_pull.2 hj') hk'
  have b := gm_cocycle hL' f y (i := fun _ => j) (j := k) (k := k') (mem_pull.2 hj) hk hk'
  have c := gm_pull_g L F f y (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [c, ← b] at a
  show gm f y _ ((L.pull F).g (fun _ => j) k) = _ * _ * gm f y _ ((L.pull F).g (fun _ => j') k')
  rw [mul_right_comm, a, mul_inv_cancel_right]

end GlobalTheory.ModelData
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.degenerationData_psi_quadratic_generators_linear : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X), N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧ ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧ (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n := by
  first | exact @GlobalTheory.PsiQuadratic.main | exact GlobalTheory.PsiQuadratic.main | (intros; apply GlobalTheory.PsiQuadratic.main <;> assumption)
end
