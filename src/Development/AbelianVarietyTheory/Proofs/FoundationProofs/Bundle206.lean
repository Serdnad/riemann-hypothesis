module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle202
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumQExpansion
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle198
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open GlobalTheory.NeedB Polynomial

theorem GlobalTheory.cup_kummer_coboundary_of_norms : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨w, hwc, hw⟩ := GlobalTheory.T.kummer_carry_cocycle_coboundary_of_norms K Ω N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  obtain ⟨v, hvc, hv⟩ := GlobalTheory.T.kummer_carry_coboundary_twist_cochain K Ω N ζ hN hζ hfix a b α β ha hb hα hβ w hwc hw
  exact GlobalTheory.T.exists_locallyConstant_zmod_coboundary_of_mu_cocycle K Ω N ζ hN hζ hfix (fun g h => kum ζ α g * kum ζ β h) v hvc hv
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_saturation : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  first | exact @GlobalTheory.fn_sat | exact GlobalTheory.fn_sat | (intros; apply GlobalTheory.fn_sat <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_bounded_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  first | exact @GlobalTheory.FN.frac_bdd_den | exact GlobalTheory.FN.frac_bdd_den | (intros; apply GlobalTheory.FN.frac_bdd_den <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum : ∀ (k q : ℕ) (ε : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → 0 < q → ε 1 = 1 → PolyB a → PolyB (To k (ε q) q a) ∧ qs (To k (ε q) q a) = hsum k ε (repT q) (qs a) := by
  first | exact @GlobalTheory.EisM.qs_To_hsum | exact GlobalTheory.EisM.qs_To_hsum | (intros; apply GlobalTheory.EisM.qs_To_hsum <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_direction_indep : ∀ (j L : ℕ) (v w : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 1 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → Kills L w Φ → lat j 0 L v Φ τ = lat j 0 L w Φ τ := by
  first | exact @GlobalTheory.EisM.lat_indep | exact GlobalTheory.EisM.lat_indep | (intros; apply GlobalTheory.EisM.lat_indep <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.heckeCharacterSlashSum_invariant_of_stable : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι : Type) [Fintype ι] (β : ι → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → N ∣ L' → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → (∀ δ ∈ Δ, ∀ γ : SL(2, ℤ), (L' : ℤ) ∣ γ 1 0 → δ * (γ : M2) ∈ Δ) → LRep L Δ β → Inv k L (ch ε) f → Inv k L' (ch ε) (hsum k (ch ε) β f) := by
  first | exact @GlobalTheory.EisM.hsum_inv_of_stable | exact GlobalTheory.EisM.hsum_inv_of_stable | (intros; apply GlobalTheory.EisM.hsum_inv_of_stable <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low : ∀ (e : ℕ) (b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.integrableOn_sq_qs_low | exact GlobalTheory.EisM.integrableOn_sq_qs_low | (intros; apply GlobalTheory.EisM.integrableOn_sq_qs_low <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_qExpansion : ∀ (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ), 1 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → hat φ 0 = 0 → (∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) → ∃ c : ℂ, PolyB (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L (0, 1) (latF L b φ) τ = 2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  first | exact @GlobalTheory.LatQ.lat_qexp | exact GlobalTheory.LatQ.lat_qexp | (intros; apply GlobalTheory.LatQ.lat_qexp <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out : ∀ (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) = LSeries (fun n => φ n) (j + 2 * s) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  first | exact @GlobalTheory.EisM.lattice_sum_gcd_out | exact GlobalTheory.EisM.lattice_sum_gcd_out | (intros; apply GlobalTheory.EisM.lattice_sum_gcd_out <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_mul_int_left (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x ≤ 1) (hy : Triv χ y) :
    Triv χ (x * y) :=
  triv_mono χ y (x * y) (by rw [map_mul]; exact mul_le_of_le_one_left' hx) hy

theorem triv_mul_int_right (χ : kˣ →* ℂˣ) {x y : k} (hy : valuation k y ≤ 1) (hx : Triv χ x) :
    Triv χ (x * y) := by
  rw [mul_comm]; exact triv_mul_int_left χ hy hx

theorem grp_mul {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) {a b : GL (Fin n) k}
    (ha : a ∈ grp ψ) (hb : b ∈ grp ψ) : a * b ∈ grp ψ := by
  refine ⟨(KO k (Fin n)).mul_mem ha.1 hb.1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
    (triv_zero _) (fun l _ => ?_)
  rcases le_or_gt l i with hli | hil
  ·
    have h1 : Triv (ψ l / ψ j) (b.val l j) := hb.2 l j (lt_of_le_of_lt hli hij)
    have h2 : Triv (ψ i / ψ j) (b.val l j) := hψ l i j j hli hij.le le_rfl _ h1
    exact triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) h2
  · rcases lt_or_ge l j with hlj | hjl
    · have h1 : Triv (ψ i / ψ l) (a.val i l * b.val l j) :=
        triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) (ha.2 i l hil)
      have h2 : Triv (ψ l / ψ j) (a.val i l * b.val l j) :=
        triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) (hb.2 l j hlj)
      have h3 := triv_mul _ _ _ h1 h2
      rwa [div_mul_div_cancel] at h3
    · have h1 : Triv (ψ i / ψ l) (a.val i l) := ha.2 i l hil
      have h2 : Triv (ψ i / ψ j) (a.val i l) := hψ i i j l le_rfl hij.le hjl _ h1
      exact triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) h2

theorem grp_mul_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, a * b ∈ grp ψ :=
  fun _ _ _ _ _ _ ψ hψ _ ha _ hb => grp_mul ψ hψ ha hb

end GlobalTheory.PsType
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coeffHeckeUOperator_lowers_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k (L * l) χ a → MF k L χ (Uo l a) := by
  first | exact @GlobalTheory.Uo_lowers_level | exact GlobalTheory.Uo_lowers_level | (intros; apply GlobalTheory.Uo_lowers_level <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.rankin_mean_square_cuspForm : ∀ (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ), 1 ≤ k → CF k L χ h → h 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, ‖h n‖ ^ 2 ≤ C * (n : ℝ) ^ k) ∧ (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s)) ∧ ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ C := by
  first | exact @GlobalTheory.rankin_mean_square | exact GlobalTheory.rankin_mean_square | (intros; apply GlobalTheory.rankin_mean_square <;> assumption)
end
