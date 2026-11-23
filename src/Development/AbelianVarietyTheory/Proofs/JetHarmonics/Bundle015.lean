module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.mvPowerSeries_integral_bounded_closure : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type), (∀ S T : MvPowerSeries σ K, Intg S → Intg T → Intg (S + T) ∧ Intg (S - T) ∧ Intg (S * T)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → Bdd (S + T) ∧ Bdd (S - T) ∧ Bdd (S * T)) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), (Intg S → Intg (S ^ n)) ∧ (Bdd S → Bdd (S ^ n)) ∧ (Intg S → Bdd S)) ∧ (∀ a : K, Bdd (MvPowerSeries.C a : MvPowerSeries σ K) ∧ (‖a‖ ≤ 1 → Intg (MvPowerSeries.C a : MvPowerSeries σ K)) ∧ (‖a‖ < 1 → Small (MvPowerSeries.C a : MvPowerSeries σ K))) ∧ (∀ i : σ, Small (MvPowerSeries.X i : MvPowerSeries σ K)) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), ((∀ i ∈ t, Intg (f i)) → Intg (∏ i ∈ t, f i) ∧ Intg (∑ i ∈ t, f i)) ∧ ((∀ i ∈ t, Bdd (f i)) → Bdd (∏ i ∈ t, f i) ∧ Bdd (∑ i ∈ t, f i))) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (Intg S → Intg (MvPowerSeries.subst a S)) ∧ (Bdd S → Bdd (MvPowerSeries.subst a S))) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → (Intg f → Intg (f.subst a)) ∧ (Bdd f → Bdd (f.subst a))) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → Bdd (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A)) ∧ (∀ f : PowerSeries K, (Intg f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) ∧ (Bdd f ↔ ∃ C : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ C)) := by
  first | exact @GlobalTheory.BddAlg.bdd_alg | exact GlobalTheory.BddAlg.bdd_alg | (intros; apply GlobalTheory.BddAlg.bdd_alg <;> assumption)
end

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.Triang

variable {q : ℕ} [Fact q.Prime]

theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero =>
    intro m
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ]
    exact bd_one_mul ih hf

theorem norm_le_of_distinct {ι : Type*} (s : Finset ι) (e : ι → ℕ) (u : ι → ℂ_[q]⟦X⟧) (c : ι → ℂ_[q]) (B : ℝ)
    (he : Set.InjOn e s) (hu : ∀ j ∈ s, Bd 1 (u j)) (h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1)
    (hB : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j))) : ∀ j ∈ s, ‖c j‖ ≤ B := by
  classical
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hcoeff : ∀ N, coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) =
      ∑ j ∈ s, c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) := by
    intro N

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have key : ∀ N, ∀ j ∈ s, e j = N → ‖c j‖ ≤ B := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro j hj hjN
    have hsplit := (hcoeff N).trans (Finset.add_sum_erase s _ hj).symm
    beta_reduce at hsplit
    have hjterm : c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) = c j * constantCoeff (u j) := by
      rw [if_pos hjN.le, hjN, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hrest : ‖∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0)‖ ≤ B := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun i hi => ?_
      obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
      split_ifs with hle
      · have hlt : e i < N := lt_of_le_of_ne hle fun h => hij (he his hj (h.trans hjN.symm))
        rw [norm_mul]
        calc ‖c i‖ * ‖coeff (N - e i) (u i)‖ ≤ B * 1 :=
              mul_le_mul (ih _ hlt i his rfl) (hu i his _) (norm_nonneg _) hB0
          _ = B := mul_one B
      · simpa using hB0
    have hmain : c j * constantCoeff (u j) = coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) -
        ∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0) := by
      linear_combination -hsplit - hjterm
    have hnorm : ‖c j‖ = ‖c j * constantCoeff (u j)‖ := by rw [norm_mul, h0 j hj, mul_one]
    rw [hnorm, hmain, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hB N) ?_)
    rwa [norm_neg]
  exact fun j hj => key (e j) j hj rfl

theorem coeff_norm_le : ∀ (q : ℕ) [Fact q.Prime] (xs ys : ℂ_[q]⟦X⟧) (k : ℕ) (a b : ℕ → ℂ_[q]) (B : ℝ), Bd 1 xs → Bd 1 ys → ‖constantCoeff xs‖ = 1 → ‖constantCoeff ys‖ = 1 → Bd B (∑ i ∈ Finset.range (k + 1), (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys)) → ∀ i ≤ k, ‖a i‖ ≤ B ∧ ‖b i‖ ≤ B := by
  intro q _ xs ys k a b B hxs hys hx0 hy0 hB
  classical
  let s : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range (k + 1)
  let e : Bool × ℕ → ℕ := fun j => bif j.1 then 2 * (k - j.2) + 3 else 2 * (k - j.2)
  let u : Bool × ℕ → ℂ_[q]⟦X⟧ := fun j => bif j.1 then xs ^ j.2 else xs ^ j.2 * ys
  let c : Bool × ℕ → ℂ_[q] := fun j => bif j.1 then a j.2 else b j.2
  have hmem : ∀ {j : Bool × ℕ}, j ∈ s → j.2 < k + 1 := fun hj =>
    Finset.mem_range.mp (Finset.mem_product.mp hj).2
  have he : Set.InjOn e s := by
    rintro ⟨b₁, i₁⟩ h₁ ⟨b₂, i₂⟩ h₂ heq
    have hi₁ := hmem (Finset.mem_coe.mp h₁)
    have hi₂ := hmem (Finset.mem_coe.mp h₂)
    cases b₁ <;> cases b₂ <;> simp only [e, cond_true, cond_false] at heq hi₁ hi₂ <;>
      first | (exfalso; omega) | (congr 1; omega)
  have hu : ∀ j ∈ s, Bd 1 (u j) := by
    rintro ⟨_ | _, i⟩ _
    · exact bd_one_mul (bd_one_pow hxs i) hys
    · exact bd_one_pow hxs i
  have h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1 := by
    rintro ⟨_ | _, i⟩ _
    · show ‖constantCoeff (xs ^ i * ys)‖ = 1
      rw [map_mul, map_pow, norm_mul, norm_pow, hx0, hy0, one_pow, one_mul]
    · show ‖constantCoeff (xs ^ i)‖ = 1
      rw [map_pow, norm_pow, hx0, one_pow]
  have hsum : (∑ j ∈ s, C (c j) * (X ^ e j * u j)) = ∑ i ∈ Finset.range (k + 1),
      (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
    simp only [s]
    rw [Finset.sum_product, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [e, u, c, cond_true, cond_false]
    ring
  have hB' : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j)) := by
    rw [hsum]
    exact hB
  have key := norm_le_of_distinct s e u c B he hu h0 hB'
  intro i hi
  have hi' : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact ⟨key (true, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩),
    key (false, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩)⟩

end GlobalTheory.MomOne.Triang
end
end

section

open PowerSeries GlobalTheory.MomOne WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical

noncomputable section

namespace GlobalTheory.MomOne

def ringHomPointFun {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => 0
  | .some x y hP => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr hP)

def ringHomPoint {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (W.map f).toAffine.Point :=
  AddMonoidHom.mk' (ringHomPointFun f W) <| by
    refine GlobalTheory.map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, ringHomPointFun, Point.some.injEq, true_and, negY,
          map_a₁, map_a₃, map_sub, map_neg, map_mul]
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := GlobalTheory.exists_line_of_add_add_eq_zero h
      refine GlobalTheory.add_add_eq_zero_of_line _ _ _ (f l) (f n) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; simp
      · rw [e₂]; simp
      · rw [e₃]; simp
      · simpa using congrArg f s₁
      · simpa [map_ofNat] using congrArg f s₂

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_some {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W (.some x y h) =
      .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_surjective_of_ringEquiv {k k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') (W : WeierstrassCurve k) :
    Function.Surjective (_root_.GlobalTheory.MomOne.ringHomPoint (e : k →+* k') W) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, map_zero _⟩
  · have h' : W.toAffine.Nonsingular (e.symm x) (e.symm y) := by
      rw [← WeierstrassCurve.Affine.map_nonsingular W.toAffine (f := (e : k →+* k')) e.injective]
      simpa using h
    refine ⟨.some _ _ h', ?_⟩
    rw [ringHomPoint_some]
    simp

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_eq_zero_iff {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) (P : W.toAffine.Point) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [ringHomPoint_some]
    simp


open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
theorem _root_.GlobalTheory.MomOne.Mdl.exists_pointHom (q : ℕ) [Fact q.Prime]
    (M : _root_.GlobalTheory.MomOne.Mdl q) (hM : M.Ok) :
    ∃ φ : ℂ →+ M.W.toAffine.Point, Function.Surjective φ ∧
      (∀ z, φ z = 0 ↔ z ∈ M.L.lattice) ∧
      ∀ z ∉ M.L.lattice, ∃ h,
        φ z = WeierstrassCurve.Affine.Point.some (M.ι (M.x z))
          (M.ι (M.y z)) h := by
  obtain ⟨hc, -, -, -, -, -, -, h₄, h₆⟩ := hM
  have hιc : M.ι M.c ≠ 0 :=
    (map_ne_zero M.ι).mpr hc
  obtain ⟨C, hCu, hCr, hCs, hCt⟩ : ∃ C : VariableChange ℂ_[q],
      (C.u : ℂ_[q]) = (M.ι M.c)⁻¹ ∧
      C.r = -(M.W.b₂ / 12) ∧ C.s = -(M.W.a₁ / 2) ∧
      C.t = M.W.a₁ * M.W.b₂ / 24 -
        M.W.a₃ / 2 :=
    ⟨⟨Units.mk0 _ (inv_ne_zero hιc), _, _, _⟩, rfl, rfl, rfl, rfl⟩
  have hCu' : ((C.u⁻¹ : ℂ_[q]ˣ) : ℂ_[q]) = M.ι M.c := by
    rw [Units.val_inv_eq_inv_val, hCu, inv_inv]
  have hE : (_root_.GlobalTheory.latticeCurve M.L).a₁ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₂ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₃ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₄ = -M.L.g₂ / 4 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₆ = -M.L.g₃ / 4 := by
    simp [_root_.GlobalTheory.latticeCurve]
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hE₆⟩ := hE
  have hg₂ : M.ι M.L.g₂ =
      M.W.c₄ / 12 * M.ι M.c ^ 4 := by
    rw [h₄, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 4 hιc)]
  have hg₃ : M.ι M.L.g₃ =
      M.W.c₆ / 216 * M.ι M.c ^ 6 := by
    rw [h₆, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 6 hιc)]
  have hC : C • M.W =
      (_root_.GlobalTheory.latticeCurve M.L).map (M.ι : ℂ →+* ℂ_[q]) := by
    ext
    · rw [variableChange_a₁, hCu', hCs, map_a₁, hE₁]; simp only [map_zero]; ring
    · rw [variableChange_a₂, hCu', hCs, hCr, map_a₂, hE₂]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₃, hCu', hCt, hCr, map_a₃, hE₃]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₄, hCu', hCs, hCt, hCr, map_a₄, hE₄]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₂, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    · rw [variableChange_a₆, hCu', hCt, hCr, map_a₆, hE₆]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₃, WeierstrassCurve.c₆,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      ring
  let φ : ℂ →+ M.W.toAffine.Point :=
    (_root_.GlobalTheory.variableChangePoint C hC).comp
      ((_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)).comp
        (_root_.GlobalTheory.latticePointHom M.L))
  have hφ : ∀ z, φ z = _root_.GlobalTheory.variableChangePoint C hC
      (_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)
        (_root_.GlobalTheory.latticePoint M.L z)) := by
    intro z
    simp only [φ, AddMonoidHom.coe_comp, Function.comp_apply, _root_.GlobalTheory.latticePointHom_apply]
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro P
    obtain ⟨P₁, rfl⟩ := (_root_.GlobalTheory.variableChangePoint_bijective C hC).2 P
    obtain ⟨P₂, rfl⟩ := ringHomPoint_surjective_of_ringEquiv M.ι _ P₁
    obtain ⟨z, rfl⟩ := _root_.GlobalTheory.latticePoint_surjective M.L P₂
    exact ⟨z, hφ z⟩
  · intro z
    rw [hφ, map_eq_zero_iff _ (_root_.GlobalTheory.variableChangePoint_bijective C hC).1,
      ringHomPoint_eq_zero_iff, _root_.GlobalTheory.latticePoint_eq_zero_iff]
  · intro z hz
    have key : ∀ {a b a' b' : ℂ_[q]} (h : M.W.toAffine.Nonsingular a b),
        a = a' → b = b' → ∃ h', (Point.some a b h : M.W.toAffine.Point) =
          Point.some a' b' h' := by
      rintro a b a' b' h rfl rfl
      exact ⟨h, rfl⟩
    have hx : (C.u : ℂ_[q]) ^ 2 * M.ι (M.L.weierstrassP z) + C.r =
        M.ι (M.x z) := by
      show _ = M.ι (M.L.weierstrassP z / M.c ^ 2 -
        M.ι.symm (M.W.b₂ / 12))
      rw [map_sub, map_div₀, map_pow, RingEquiv.apply_symm_apply, hCu, hCr]
      field_simp
      ring
    have hy : (C.u : ℂ_[q]) ^ 3 * M.ι (M.L.derivWeierstrassP z / 2) +
        (C.u : ℂ_[q]) ^ 2 * C.s * M.ι (M.L.weierstrassP z) + C.t =
        M.ι (M.y z) := by
      show _ = M.ι ((M.L.derivWeierstrassP z /
        M.c ^ 3 - M.ι.symm M.W.a₁ *
        M.x z - M.ι.symm M.W.a₃) / 2)
      simp only [map_div₀, map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, map_ofNat]
      rw [← hx, hCu, hCr, hCs, hCt]
      field_simp
      ring
    rw [hφ, _root_.GlobalTheory.latticePoint_of_notMem M.L hz,
      ringHomPoint_some, _root_.GlobalTheory.variableChangePoint_some]
    exact key _ hx hy

end GlobalTheory.MomOne
end
end

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.MomOne.Frame

variable {g : ℕ}

theorem hf_sum_left {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm (∑ i, z i • x i) w = ∑ i, z i * hf Hm (x i) w := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem hf_sum_right {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * hf Hm w (x i) := by

  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem beta_sum_left {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm (∑ i, z i • x i) w = ∑ i, z i * beta d Hm (x i) w := by
  simp only [beta, hf_sum_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem beta_sum_right {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * beta d Hm w (x i) := by
  simp only [beta, hf_sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

section
variable {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → Fin g → ℂ} {a : Fin g → ℕ}

theorem beta_coord (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z : Fin g → ℂ) (j : Fin g) :
    beta d Hm (∑ i, z i • x i) (x j) = z j * a j := by
  simp [beta_sum_left, hx]

theorem beta_frame (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * (z i * conj (w i)) := by
  rw [beta_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [beta_coord hx]; ring

theorem hf_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    hf Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 d (z i) (w i) := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt d ≠ 0 := by positivity
    exact_mod_cast this
  have h := beta_frame hx z w
  have e : hf Hm (∑ i, z i • x i) (∑ i, w i • x i) =
      ((2 / Real.sqrt d : ℝ) : ℂ) * beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) := by
    rw [beta]; push_cast; field_simp
  rw [e, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

theorem expand (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, 0 < a i)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have ha' : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).ne'
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ x
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have hinj : Function.Injective L := by
    intro z w h
    funext j
    have h1 := beta_coord hx z j
    have h2 := beta_coord hx w j
    rw [← hL] at h1 h2
    rw [h, h2] at h1
    exact (mul_right_cancel₀ (ha' j) h1).symm
  obtain ⟨z, rfl⟩ := (LinearMap.injective_iff_surjective.1 hinj) v
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [beta_coord hx, mul_div_cancel_right₀ _ (ha' i)]

theorem opU_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opU Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 d (t i) (f j i) (z i) ^ a i := by
  have e : (∑ i, z i • x i) + ∑ i, t i • x i = ∑ i, (z + t) i • x i := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [opU, e, hG, hf_frame hd hx, hf_frame hd hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [U1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Pi.add_apply,
    Finset.mul_sum, ← Finset.sum_sub_distrib, mul_assoc]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

theorem opW_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opW d Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 d (t i) (f j i) (z i) ^ a i := by
  have e : (((beta d Hm (∑ i, t i • x i) (∑ i, t i • x i)).re : ℝ) : ℂ) =
      ∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ) := by
    rw [beta_frame hx]
    simp only [Complex.mul_conj]
    have : (∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ)) = ((∑ i, (a i : ℝ) * Complex.normSq (t i) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  rw [opW, opU_frame hd hx c f G hG, e, Finset.mul_sum _ (fun j => c j * _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [W1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Finset.mul_sum]
  rw [mul_left_comm]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

end

theorem jetV_frame (x : Fin g → Fin g → ℂ) (G : (Fin g → ℂ) → ℂ) (hG : ContDiff ℂ ⊤ G) (k : ℕ)
    (ys : Fin k → Fin g → ℂ) :
    jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys := by
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Fintype.linearCombination ℂ x)
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have e : (fun z : Fin g → ℂ => G (∑ i, z i • x i)) = G ∘ L := by
    funext z; simp [hL]
  rw [e, L.iteratedFDeriv_comp_right hG 0 le_top, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, jetV]
  simp only [hL]

theorem coord : ∀ (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), 0 < S.d → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i) → (∀ v : Fin g → ℂ, v = ∑ i, (beta S.d S.Hm v (x i) / (a i : ℂ)) • x i) ∧ (∀ z w : Fin g → ℂ, hf S.Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 S.d (z i) (w i)) ∧ (∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ), (∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) → ∀ t z : Fin g → ℂ, opU S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 S.d (t i) (f j i) (z i) ^ a i ∧ opW S.d S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 S.d (t i) (f j i) (z i) ^ a i) ∧ ∀ (G : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ G → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys :=
  fun _ _ x _ hd hx ha =>
    ⟨expand hx ha, hf_frame hd hx,
      fun _ c f G hG t z => ⟨opU_frame hd hx c f G hG t z, opW_frame hd hx c f G hG t z⟩,
      jetV_frame x⟩

end GlobalTheory.MomOne.Frame
end
