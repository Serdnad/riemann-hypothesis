module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle636
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinSchreierCocycleRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerSkewDimSemisimpleTwoRoots
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.iteratedPartialDeriv_const_mul_reindex : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (u : List I) (h : (J → ℂ) → ℂ) (A : ℂ) (z : I → ℂ), iterD u (fun z ↦ A * h (fun j ↦ z (e.symm j))) z = A * iterD (u.map e) h (fun j ↦ z (e.symm j)) := by
  first | exact @GlobalTheory.HilbFam.iterD_const_mul_reindex | exact GlobalTheory.HilbFam.iterD_const_mul_reindex | (intros; apply GlobalTheory.HilbFam.iterD_const_mul_reindex <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.iteratedPartialDeriv_prod_oneVar_at_zero : ∀ (I : Type) [Fintype I] [DecidableEq I] (u : List I) (r : ℝ) (ψ : I → ℂ → ℂ) (A : ℂ), 0 < r → (∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) → iterD u (fun z ↦ A * ∏ i, ψ i (z i)) 0 = A * ∏ i, iteratedDeriv (u.count i) (ψ i) 0 := by
  first | exact @GlobalTheory.IterDProd.iterD_prod | exact GlobalTheory.IterDProd.iterD_prod | (intros; apply GlobalTheory.IterDProd.iterD_prod <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ) (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M → (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) → (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) → (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) → HasSum (fun ξ ↦ iterD u (f ξ) 0) (iterD u g 0) := by
  first | exact @GlobalTheory.HilbFam.hasSum_iterD_termwise | exact GlobalTheory.HilbFam.hasSum_iterD_termwise | (intros; apply GlobalTheory.HilbFam.hasSum_iterD_termwise <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_term_smul_add (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt)
    (y : N.X) (hy : h ^ m = N.io y)
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
        (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S)
    (a b : N.X) : ∃ w : Oˣ, (w : O) ∈ S ∧
      N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  set H := Subgroup.closure (Set.range N.c ∪ {h.b}) with hH
  set T := S.toSubmonoid.units with hT
  set π : Oˣ →* Oˣ ⧸ T := QuotientGroup.mk' T with hπ
  have Hc : ∀ a, N.c a ∈ H := fun a => Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
  have Hb : h.b ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have θ1 : ∀ x ∈ H, ∀ x' ∈ H, ∀ x'' ∈ H, π (N.θ x x' x'') = 1 := fun x hx x' hx' x'' hx'' =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hθ x hx x' hx' x'' hx''))
  have σ1 : ∀ a, π (N.σ (N.c a)) = 1 := fun a =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hσ _ (Hc a)))
  have Bl : ∀ a a' b, π (N.τ (a + a') b) = π (N.τ a b) * π (N.τ a' b) := by
    intro a a' b
    have := congrArg π (N.τ_add_left a a' b)
    rwa [map_mul, map_mul, θ1 _ (Hc a) _ (Hc a') _ (Hc b), mul_one] at this
  have Br : ∀ a b b', π (N.τ a (b + b')) = π (N.τ a b) * π (N.τ a b') := by
    intro a b b'
    have := congrArg π (N.τ_add_right a b b')
    rwa [map_mul, map_mul, θ1 _ (Hc b) _ (Hc b') _ (Hc a), mul_one] at this
  have fadd : ∀ a b, π (N.ψ (a + b)) = π (N.τ a b) * π (N.ψ a) * π (N.ψ b) := by
    intro a b
    rw [N.ψ_add, map_mul, map_mul]
  have fneg : ∀ a, π (N.ψ (-a)) = π (N.ψ a) := by
    intro a
    have := congrArg π (N.even a)
    rwa [map_mul, σ1, mul_one] at this
  have Bnegr : ∀ a b, π (N.τ a (-b)) = (π (N.τ a b))⁻¹ := by
    intro a b
    have := Br a b (-b)
    rw [add_neg_cancel, N.τ_zero_right, map_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have Bself : ∀ a, π (N.τ a a) = π (N.ψ a) ^ 2 := by
    intro a
    have := fadd a (-a)
    rw [add_neg_cancel, N.ψ_zero, map_one, fneg, Bnegr, mul_assoc, eq_comm, inv_mul_eq_one] at this
    rw [sq]
    exact this
  have Bsmul : ∀ (k : ℕ) a b, π (N.τ (k • a) b) = π (N.τ a b) ^ k := by
    intro k a b
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Bl, ih, pow_succ]
  have Bsmulr : ∀ (k : ℕ) a b, π (N.τ a (k • b)) = π (N.τ a b) ^ k := by
    intro k a b
    rw [N.τ_symm, Bsmul, N.τ_symm]
  have fsmul : ∀ (k : ℕ) a, π (N.ψ (k • a)) = π (N.ψ a) ^ (k ^ 2) := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, fadd, ih, Bsmul, Bself, ← pow_mul, ← pow_add, ← pow_succ]
      congr 1
      ring
  have Sadd : ∀ χ χ', π (h.s (χ + χ')) = π (h.s χ) * π (h.s χ') := by
    intro χ χ'
    have := congrArg π (h.mult χ χ')
    rwa [map_mul, map_mul, θ1 _ (Hc χ) _ (Hc χ') _ Hb, mul_one] at this
  have Ssmul : ∀ (k : ℕ) a, π (h.s (k • a)) = π (h.s a) ^ k := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Sadd, ih, pow_succ]
  have Spow : π (h.s a) ^ m = π (N.τ a y) := by
    have := congrArg π (h.pow_s m a)
    rw [map_mul, map_pow, hy, GlobalTheory.Ex.NumD.io_s, N.τ_symm] at this
    have hc : π (cubN N.θ m 1 h.b (N.c a)) = 1 := by
      unfold cubN
      rw [map_prod]
      exact Finset.prod_eq_one fun i _ => θ1 _ (by rw [one_mul]; exact pow_mem Hb i) _ Hb _ (Hc a)
    rw [hc, mul_one] at this
    exact this.symm
  refine ⟨N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b)), ?_, ?_⟩
  · have e : π (N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b))) = 1 := by
      rw [map_div, div_eq_one, map_mul, map_mul, map_mul, map_mul, map_pow, fadd, Sadd, fsmul, Bsmul, Br, Bsmulr,
        Ssmul, Spow]
      ac_rfl
    exact ((Submonoid.mem_units_iff _ _).1 ((QuotientGroup.eq_one_iff _).1 e)).1
  · exact (fun (L X Y Z : Oˣ) => show L = L / (X * Y * Z) * X * Y * Z by
      rw [mul_assoc (L / (X * Y * Z)) X Y, mul_assoc (L / (X * Y * Z)) (X * Y) Z, div_mul_cancel]) _ _ _ _

end GlobalTheory
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.finsum_psiG_mul_star_eq_chG : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, psiG S n x * star (Y x) = ∑ᶠ x, chG S n x * star (Y x) := by
  first | (exact @GlobalTheory.psiG_pairing_eq_chG_pairing) | (exact GlobalTheory.psiG_pairing_eq_chG_pairing) | (intros; apply GlobalTheory.psiG_pairing_eq_chG_pairing <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.psi_sum_eq_char_sum_against_cusp_form : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (S : F[X] → ℂ) (n k : ℕ), S 1 = 0 → ∑ᶠ x, psiG S n x * star (cusp θ n k x) = ∑ᶠ x, chG S n x * star (cusp θ n k x) := by
  first | (exact @GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq) | (exact GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq) | (intros; apply GlobalTheory.Shin.sum_psiG_mul_star_cusp_eq  <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ConjExp


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.ConjExp.qConj_torsion : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wp N x) (_root_.GlobalTheory.WpFam.wp N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wpd N x) (_root_.GlobalTheory.WpFam.wpd N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ (x ≠ 0 → _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wB N x) (_root_.GlobalTheory.WpFam.wB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)))) := by
  intro N _ g a hg x
  have hc := _root_.GlobalTheory.WpFam.CoeffConj.main N g a hg x
  refine ⟨⟨_, _root_.GlobalTheory.WpFam.ExpP.main N x, ?_⟩,
    ⟨_, _root_.GlobalTheory.WpFam.DerivExpansion.main N x, ?_⟩, fun hx => ⟨_,
      _root_.GlobalTheory.WpFam.ExpansionB.main N x hx, ?_⟩⟩
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cP N x n)) = _root_.GlobalTheory.WpFam.cP N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.2.2]
    exact _root_.GlobalTheory.WpFam.ExpP.main N _
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cD N x n)) = _root_.GlobalTheory.WpFam.cD N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.1]
    exact _root_.GlobalTheory.WpFam.DerivExpansion.main N _
  · have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
    rw [show (fun n => g (_root_.GlobalTheory.WpFam.cB N x n)) = _root_.GlobalTheory.WpFam.cB N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).1]
    exact _root_.GlobalTheory.WpFam.ExpansionB.main N _ fun h => hx (hzero.1 h)

end GlobalTheory.WpFam.ConjExp
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F), cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  first | (exact @GlobalTheory.Shin.cusp_gal) | (exact GlobalTheory.Shin.cusp_gal) | (intros; apply GlobalTheory.Shin.cusp_gal <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wp N x) (cP N x) := by
  first | exact @GlobalTheory.WpFam.ExpP.main | exact GlobalTheory.WpFam.ExpP.main | (intros; apply GlobalTheory.WpFam.ExpP.main <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.PullAd

section
variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] {n : ℕ}

theorem val_eq_one_iff {K : Type} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ))) {z : K}
    (hz : z ≠ 0) : w z = 1 ↔ w z ≤ 1 ∧ w z⁻¹ ≤ 1 := by
  constructor
  · intro h; simp [map_inv₀, h]
  · rintro ⟨h1, h2⟩
    rw [map_inv₀] at h2
    have h0 : w z ≠ 0 := (Valuation.ne_zero_iff w).2 hz
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = w z * (w z)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ w z * 1 := mul_le_mul_right h2 _
      _ = w z := mul_one _

theorem res_eq_one {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E) {x : F} (hx : x ≠ 0) :
    p.1 (algebraMap F E x) = 1 ↔ (ρ p).1 x = 1 := by
  rw [val_eq_one_iff _ hx, val_eq_one_iff _ ((map_ne_zero _).2 hx), ← map_inv₀, hρ, hρ]

theorem res_mono {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E) {x y : F}
    (h : (ρ p).1 x ≤ (ρ p).1 y) : p.1 (algebraMap F E x) ≤ p.1 (algebraMap F E y) := by
  by_cases hy : y = 0
  · subst hy
    have h0 : (ρ p).1 x = 0 := le_antisymm (by simpa using h) zero_le'
    have hx : x = 0 := (Valuation.zero_iff _).1 h0
    simp [hx]
  · have h1 : (ρ p).1 (x * y⁻¹) ≤ 1 := by
      have h0 : (ρ p).1 y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
      rw [map_mul, map_inv₀]
      calc (ρ p).1 x * ((ρ p).1 y)⁻¹ ≤ (ρ p).1 y * ((ρ p).1 y)⁻¹ := mul_le_mul_left h _
        _ = 1 := mul_inv_cancel₀ h0
    have h2 := (hρ p (x * y⁻¹)).2 h1
    have e : algebraMap F E x = algebraMap F E (x * y⁻¹) * algebraMap F E y := by
      rw [← map_mul, inv_mul_cancel_right₀ hy]
    rw [e, map_mul]
    exact mul_le_of_le_one_left' h2

theorem det_map (M : Matrix (Fin n) (Fin n) F) :
    (M.map (algebraMap F E)).det = algebraMap F E M.det := by
  rw [RingHom.map_det]; rfl

theorem unimod_map {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E)
    (M : Matrix (Fin n) (Fin n) F) (hM : M.det ≠ 0) :
    Unimod p (M.map (algebraMap F E)) ↔ Unimod (ρ p) M := by
  unfold Unimod
  rw [det_map, res_eq_one hρ p hM]
  simp only [Matrix.map_apply]
  exact and_congr_left fun _ => forall_congr' fun i => forall_congr' fun j => hρ p _

theorem nrm_of_max (v : Place k F) (x : Fin n → F) (i : Fin n) (h : ∀ j, v.1 (x j) ≤ v.1 (x i)) :
    nrm v x = v.1 (x i) :=
  le_antisymm (Finset.sup_le fun j _ => h j) (Finset.le_sup (f := fun j => v.1 (x j)) (Finset.mem_univ i))

end

theorem adm_pullAd_and_deg_mul_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → admitted (pullAd ρ g) ∧ deg (pullAd ρ g) = Module.finrank F E * deg g ∧ (∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i)) = Module.finrank F E * degLine g w) ∧ ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ n g hg
  have hP := GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul k F E hFF ρ hρ
  have hdet : ∀ p, (pullAd ρ g p).det = algebraMap F E (g (ρ p)).det := fun p => det_map _
  have hadm : admitted (pullAd ρ g) := by
    refine ⟨fun p => by rw [hdet]; exact (map_ne_zero _).2 (hg.1 _), ?_⟩
    refine (hP.1 _ hg.2).subset fun p hp => ?_
    exact fun h => hp ((unimod_map hρ p (g (ρ p)) (hg.1 _)).2 h)
  have hdeg : deg (pullAd ρ g) = Module.finrank F E * deg g := by
    have hfin : {v | ord v (g v).det ≠ 0}.Finite := hg.2.subset fun v hv hu => hv (by simp [ord, hu.2])
    unfold deg
    rw [← hP.2 (fun v => (g v).det) hfin]
    exact finsum_congr fun p => by rw [hdet]
  have hline : ∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i))
      = Module.finrank F E * degLine g w := by
    intro w hw
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      obtain ⟨i, -⟩ := Function.ne_iff.1 hw; exact ⟨i, Finset.mem_univ _⟩
    have hmax : ∀ v : Place k F, ∃ i, ∀ j, v.1 ((g v).mulVec w j) ≤ v.1 ((g v).mulVec w i) := fun v => by
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => v.1 ((g v).mulVec w i)) hne
      exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
    choose idx hidx using hmax
    let φ : Place k F → F := fun v => (g v).mulVec w (idx v)
    have hvo : ∀ v, ordVec v ((g v).mulVec w) = ord v (φ v) := fun v => by
      simp only [ordVec, ord, φ, nrm_of_max v _ _ (hidx v)]
    have hpo : ∀ p, ordVec p ((pullAd ρ g p).mulVec (fun i => algebraMap F E (w i)))
        = ord p (algebraMap F E (φ (ρ p))) := fun p => by
      have e : (pullAd ρ g p).mulVec (fun i => algebraMap F E (w i))
          = fun i => algebraMap F E ((g (ρ p)).mulVec w i) := by
        funext i; exact (RingHom.map_mulVec _ _ _ _).symm
      rw [e]
      simp only [ordVec, ord, φ]
      rw [nrm_of_max p _ (idx (ρ p)) fun j => res_mono hρ p (hidx (ρ p) j)]
    have hfin : {v | ord v (φ v) ≠ 0}.Finite := by
      have hS : ({v | ¬ Unimod v (g v)} ∪ ⋃ i, {v : Place k F | w i ≠ 0 ∧ v.1 (w i) ≠ 1}).Finite := by
        refine hg.2.union (Set.finite_iUnion fun i => ?_)
        by_cases hi : w i = 0
        · simp [hi]
        · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF (w i) hi).1.subset fun v hv => hv.2
      refine hS.subset fun v hv => ?_
      by_contra hc
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_and,
        not_not] at hc
      obtain ⟨hu, hw1⟩ := hc
      apply hv
      rw [← hvo v]
      have h1 : nrm v w = 1 := by
        obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
        replace hi0 : w i0 ≠ 0 := hi0
        apply le_antisymm
        · refine Finset.sup_le fun j _ => ?_
          by_cases hj : w j = 0
          · simp [hj]
          · exact (hw1 j hj).le
        · rw [← hw1 i0 hi0]; exact Finset.le_sup (f := fun j => v.1 (w j)) (Finset.mem_univ i0)
      simp only [ordVec]
      rw [(GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.1 n (g v) w hu, h1]
      simp
    unfold degLine
    rw [finsum_congr hpo, hP.2 φ hfin, finsum_congr hvo]
  have hlines : ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
    intro b hb E' _ _ _ _ _ ρ' hρ' w hw
    letI : Algebra F E' := ((algebraMap E E').comp (algebraMap F E)).toAlgebra
    haveI : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower k F E' := IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k F E,
        ← IsScalarTower.algebraMap_apply k E E']
    haveI : FiniteDimensional F E' := Module.Finite.trans E E'
    have hres : IsRes (fun p => ρ (ρ' p)) := fun p x => (hρ' p (algebraMap F E x)).trans (hρ (ρ' p) x)
    have heq : pullAd ρ' (pullAd ρ g) = pullAd (fun p => ρ (ρ' p)) g := by
      funext p; ext i j; rfl
    have hb' := hb E' (fun p => ρ (ρ' p)) hres w hw
    rw [heq]
    calc (degLine (pullAd (fun p => ρ (ρ' p)) g) w : ℝ) ≤ b * Module.finrank F E' := hb'
      _ = b * Module.finrank F E * Module.finrank E E' := by
        rw [← Module.finrank_mul_finrank F E E']; push_cast; ring
  exact ⟨hadm, hdeg, hline, hlines⟩

end GlobalTheory.Nef.PullAd
end

section

open GlobalTheory.UPel.Sm

theorem _root_.GlobalTheory.T.kodairaSpencer_skew_dim_semisimple_two_roots : ∀ (k : Type) (H : Type 1) (O : Type) [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (ρ : O →+* Module.End k H) (st : O → O) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (w : O) (r r' : k) (d : ℕ), Function.Surjective st → (∀ b x y, φ (ρ b x) y = φ x (ρ (st b) y)) → (∀ x y, φ x y = -φ y x) → (∀ x, (∀ y, φ x y = 0) → x = 0) → (∀ x ∈ Fil, ∀ y ∈ Fil, φ x y = 0) → 2 * Module.finrank k Fil = Module.finrank k H → (∀ a, ∀ x ∈ Fil, ρ a x ∈ Fil) → (∀ a, ρ w * ρ a = ρ a * ρ w) → (ρ w - r • 1) * (ρ w - r' • 1) = 0 → r ≠ r' → (∀ x y, φ (ρ w x) y = φ x ((r + r') • y - ρ w y)) → Z ≤ LinearMap.range (ρ w - r' • 1) → KSDim ρ 0 (Fil ⊔ LinearMap.range (ρ w - r • 1)) Z d → KSDim ρ φ Fil Z d := by
  first | exact @GlobalTheory.UPel.Sm.KSCount.ksDim_of_eigen_reduce | exact GlobalTheory.UPel.Sm.KSCount.ksDim_of_eigen_reduce | (intros; apply GlobalTheory.UPel.Sm.KSCount.ksDim_of_eigen_reduce <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.TwistedGenericPoint

theorem loc_point {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ P V j := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨hsurj, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨k, v, hv⟩ := hsurj u
  exact ⟨𝒰.X k, 𝒰.f k, v, hprop k, hv, hP _ _ (h𝒰 _ (𝒰.f k) (Presieve.ofArrows.mk k))⟩

theorem isEmpty_of_subsingleton (X : Scheme.{0}) [Subsingleton Γ(X, ⊤)] : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  exact not_subsingleton Γ(X, ⊤) inferInstance

theorem smul_residue {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n : ℕ) (y : M) :
    n • y = (ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

end GlobalTheory.TwistedGenericPoint

namespace GlobalTheory


open GlobalTheory.TwistedGenericPoint in
theorem twGen_gen : ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)), Gen (tw q i) S (twGen i ζ) := by
  intro q i S ζ U s
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : Subsingleton Γ(S, ⊤) := by
      obtain ⟨hu, _⟩ := ζ.2
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hu))
    have hS := isEmpty_of_subsingleton S
    have hU : IsEmpty U := ⟨fun u => hS.elim (s u)⟩
    exact ⟨fun _ u => (hU.elim u), fun _ hne _ => (hU.elim hne.some)⟩
  · haveI : NeZero q := ⟨hq.ne'⟩
    obtain ⟨-, h2, h3, h4, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
    refine ⟨fun x u => ?_, fun c hne hc => ?_⟩
    · obtain ⟨V, j, v, hj, hjv, c, hc⟩ := loc_point (h2 U (ζ.map s.appTop.hom) x) u
      refine ⟨V, j, v, (c : ZMod q), hj, hjv, ?_⟩
      have e : Sec.pull (j ≫ s) (twGen i ζ) = twGen i ((ζ.map s.appTop.hom).map j.appTop.hom) :=
        h4 V S (j ≫ s) ζ
      rw [e]
      exact hc.trans (smul_residue c _)
    · haveI : Nonempty U := hne
      have e : Sec.pull s (twGen i ζ) = twGen i (ζ.map s.appTop.hom) := h4 U S s ζ
      rw [e] at hc
      have h0 : c.val • twGen i (ζ.map s.appTop.hom) = 0 := by
        rw [smul_residue (q := q), ZMod.natCast_zmod_val]
        exact hc
      have hd := h3 U _ c.val h0
      rw [← ZMod.natCast_zmod_val c]
      exact (ZMod.natCast_eq_zero_iff _ _).2 hd

end GlobalTheory
end
