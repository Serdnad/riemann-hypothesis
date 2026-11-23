module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.InnerProductSpace.Trace
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.Qk

section Per
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}

theorem cv_add (M Nn : Fin g → ℤ) : cv (M + Nn) = cv M + cv Nn := by funext i; simp [cv]
theorem cv_sub (M Nn : Fin g → ℤ) : cv (M - Nn) = cv M - cv Nn := by funext i; simp [cv]
theorem cv_nsmul (k : ℕ) (M : Fin g → ℤ) : cv ((k : ℤ) • M) = k • cv M := by funext i; simp [cv]

theorem perV_add (M Nn M' Nn' : Fin g → ℤ) : perV τ (M + M') (Nn + Nn') = perV τ M Nn + perV τ M' Nn' := by
  simp only [perV, cv_add, mulVec_add]; abel

theorem perV_sub (M Nn M' Nn' : Fin g → ℤ) : perV τ (M - M') (Nn - Nn') = perV τ M Nn - perV τ M' Nn' := by
  simp only [perV, cv_sub, mulVec_sub]; abel

theorem perV_nsmul (k : ℕ) (M Nn : Fin g → ℤ) : perV τ ((k : ℤ) • M) ((k : ℤ) • Nn) = k • perV τ M Nn := by
  simp only [perV, cv_nsmul, mulVec_smul, smul_add]

theorem perV_eq_zero (hp : (τ.map Complex.im).PosDef) {M Nn : Fin g → ℤ} (h : perV τ M Nn = 0) : M = 0 ∧ Nn = 0 := by
  have hN : Nn = 0 := by
    by_contra hne
    have hx : (fun i => (Nn i : ℝ)) ≠ 0 := fun e => hne (funext fun i => by simpa using congrFun e i)
    have h1 := hp.dotProduct_mulVec_pos hx
    have h2 : (τ.map Complex.im) *ᵥ (fun i => (Nn i : ℝ)) = 0 := by
      funext i
      have := congrArg Complex.im (congrFun h i)
      simpa [perV, cv, mulVec, dotProduct, Complex.im_sum] using this
    rw [h2] at h1
    simp at h1
  subst hN
  refine ⟨funext fun i => ?_, rfl⟩
  have := congrFun h i
  simpa [perV, cv, mulVec, dotProduct] using this

end Per

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

theorem eq_zero_of_perV_full (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) {M Nn : Fin g → ℤ} (h0 : tP σ Nn = 0)
    (h : perV (d.full σ 0) M Nn = 0) : M = 0 ∧ Nn = 0 := by
  have h1 : perV d.τ (zP σ M) (zP σ Nn) = 0 := by
    have := congrArg (zP σ) h
    rw [Exp.leftComponent_periodVector, h0, Exp.cv_zero, mulVec_zero, add_zero] at this
    exact this
  obtain ⟨a, b⟩ := perV_eq_zero d.pos h1
  have h2 : tP σ M = 0 := by
    have := congrArg (tP σ) h
    rw [Exp.secondBlock_periodVector, h0, b, Exp.cv_zero, Exp.cv_zero, mulVec_zero, mulVec_zero, add_zero, add_zero] at this
    funext l
    have := congrFun this l
    simpa [cv, tP] using this
  exact ⟨Exp.ext_zP_tP σ a h2, Exp.ext_zP_tP σ b h0⟩

def yv (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin g' ⊕ Fin r) (Nn : Fin g → ℤ) : N.X := ∑ l, tP σ Nn l • bX l

theorem yv_add (σ : Fin g ≃ Fin g' ⊕ Fin r) (a b : Fin g → ℤ) : yv bX σ (a + b) = yv bX σ a + yv bX σ b := by
  simp [yv, tP, add_smul, Finset.sum_add_distrib]

theorem yv_sub (σ : Fin g ≃ Fin g' ⊕ Fin r) (a b : Fin g → ℤ) : yv bX σ (a - b) = yv bX σ a - yv bX σ b := by
  simp [yv, tP, sub_smul, Finset.sum_sub_distrib]

theorem yv_nsmul (σ : Fin g ≃ Fin g' ⊕ Fin r) (k : ℕ) (a : Fin g → ℤ) : yv bX σ ((k : ℤ) • a) = k • yv bX σ a := by
  simp [yv, tP, Finset.smul_sum, mul_smul]

theorem yv_of_tP (σ : Fin g ≃ Fin g' ⊕ Fin r) {a : Fin g → ℤ} (h : tP σ a = 0) : yv bX σ a = 0 := by
  simp [yv, h]

theorem tP_of_yv (σ : Fin g ≃ Fin g' ⊕ Fin r) {a : Fin g → ℤ} (h : yv bX σ a = 0) : tP σ a = 0 := by
  have := Exp.co_sum (bX := bX) (tP σ a)
  change co bX (yv bX σ a) = _ at this
  rw [h] at this
  funext l
  have := congrFun this l
  simpa [co, cv] using this.symm

theorem yv_surj (σ : Fin g ≃ Fin g' ⊕ Fin r) (z : N.X) : ∃ a, yv bX σ a = z :=
  ⟨Exp.asm σ 0 (bX.repr z), by rw [yv, Exp.secondBlock_assemble]; exact bX.sum_repr z⟩

end GlobalTheory.MBLow.Cl.Qk

namespace GlobalTheory.MBLow.Cl
open Qk

theorem torsion_eq_periods_mod : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → (∀ p, ∃ M Nn, d.Rep σ k M Nn p) ∧ (∀ M Nn, ∃! p, d.Rep σ k M Nn p) ∧ (∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → d.Rep σ k (M + M') (Nn + Nn') (p * p')) ∧ ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → (N.QEq p p' ↔ ∃ M₁ N₁, M' = M + (k : ℤ) • M₁ ∧ Nn' = Nn + (k : ℤ) • N₁) := by
  intro N g' r g bX d σ k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := exp_onto_torusExt N g' r g bX d σ
  choose E hE hU using h1
  have hiff : ∀ v h, d.IsPt σ v h ↔ h = E v := fun v h => ⟨hU v h, fun e => e ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ M Nn, E (perV (d.full σ 0) M Nn) = N.io (yv bX σ Nn) := fun M Nn => (hU _ _ (h5 M Nn)).symm
  have hker : ∀ v v', E v = E v' → ∃ M Nn, tP σ Nn = 0 ∧ v = v' + perV (d.full σ 0) M Nn := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨M, Nn, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨M, Nn, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : Fin g → ℂ, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : Fin g → ℂ, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ M Nn (p : N.QT k), d.Rep σ k M Nn p ↔
      p.1.1.toAdd = yv bX σ Nn ∧ p.1.2 = E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn) :=
    fun M Nn p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun M Nn => ?_, fun M Nn M' Nn' p p' h h' => ?_, fun M Nn M' Nn' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    obtain ⟨a, ha⟩ := yv_surj (bX := bX) σ p.1.1.toAdd
    have e : E (k • v) = E (perV (d.full σ 0) 0 a) := by
      rw [hpow, hper, ← hv', ha]
      exact N.mem_QT.1 p.2
    obtain ⟨M, Nn, hy, hl⟩ := hker _ _ e
    refine ⟨0 + M, a + Nn, (hrep _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [yv_add, yv_of_tP σ hy, add_zero, ha]
    · rw [perV_add, ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (yv bX σ Nn), E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)), ?_⟩,
      (hrep _ _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _ _).1 h'
    refine (hrep _ _ _).2 ⟨?_, ?_⟩
    · rw [yv_add, ← a, ← a']
      rfl
    · rw [perV_add, smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      obtain ⟨z₀, hz⟩ := yv_surj (bX := bX) σ z
      have e : E ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') =
          E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn + perV (d.full σ 0) 0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨M₀, N₀, hy, hl⟩ := hker _ _ e
      have key := eq_zero_of_perV_full d σ (M := M' - (M + (k : ℤ) • (0 + M₀)))
        (Nn := Nn' - (Nn + (k : ℤ) • (z₀ + N₀))) ?_ ?_
      · exact ⟨0 + M₀, z₀ + N₀, sub_eq_zero.1 key.1, sub_eq_zero.1 key.2⟩
      · apply tP_of_yv (bX := bX)
        rw [yv_sub, yv_add, yv_nsmul, yv_add, yv_of_tP σ hy, add_zero, hz, ← a, ← a', c, sub_self]
      · rw [perV_sub, perV_add, perV_nsmul, perV_add, ← hc2 (perV (d.full σ 0) M' Nn'), hl, add_assoc, smul_add, hc2,
          sub_self]
    · rintro ⟨M₁, N₁, rfl, rfl⟩
      refine ⟨yv bX σ N₁, ?_, ?_⟩
      · rw [a, a', yv_add, yv_nsmul]
      · rw [b, b', perV_add, perV_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.MBLow.Cl
end
end

section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem isBallFam_pow_le_encard :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ)
      (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) →
      ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  classical
  intro G _ Λ B hB r Q R v hR hv hvB
  obtain ⟨hmono, -, hadd⟩ := isBallFam_mono_neg_add G Λ B hB
  let f : (Fin r → Fin Q) → G := fun c => ∑ j, ((c j : ℕ) • v j)

  have hterm : ∀ (n : ℕ) (j : Fin r), n • v j ∈ B (n * R) := by
    intro n j
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using hB.zero_mem 0 le_rfl
    · exact (hB.nsmul_iff n R (v j) hn (hB.subset R (hvB j))).2 (hvB j)
  have hsum : ∀ (c : Fin r → Fin Q) (s : Finset (Fin r)),
      ∑ j ∈ s, ((c j : ℕ) • v j) ∈ B (∑ j ∈ s, ((c j : ℕ) : ℝ) * R) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hB.zero_mem 0 le_rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact hadd _ _ _ _ (hterm _ a) ih
  have hmem : ∀ c, f c ∈ B (r * Q * R) := by
    intro c
    refine hmono _ _ ?_ (hsum c Finset.univ)
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hR
    calc (∑ j, ((c j : ℕ) : ℝ)) ≤ ∑ _j : Fin r, (Q : ℝ) :=
          Finset.sum_le_sum fun j _ => by exact_mod_cast (c j).isLt.le
      _ = r * Q := by simp
  have hinj : Function.Injective f := by
    intro c c' h
    have h0 : ∑ j, (((c j : ℕ) : ℤ) - ((c' j : ℕ) : ℤ)) • v j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, natCast_zsmul]
      exact sub_eq_zero.mpr h
    have := Fintype.linearIndependent_iff.1 hv _ h0
    funext j
    have hj := this j
    exact Fin.ext (by omega)
  have hsub : ((Finset.univ.image f : Finset G) : Set G) ⊆ B (r * Q * R) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨c, rfl⟩ := hx
    exact hmem c
  calc ((Q ^ r : ℕ) : ℕ∞) = ((Finset.univ.image f).card : ℕ∞) := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ = ((Finset.univ.image f : Finset G) : Set G).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (B (r * Q * R)).encard := Set.encard_le_encard hsub

end GlobalTheory.VolBr
end

section

open Filter Topology GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.encard_seminormBall_pow_le_radius_change : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ), 1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite → (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  first | exact @GlobalTheory.VolBr.encard_ball_pow_le | exact GlobalTheory.VolBr.encard_ball_pow_le | (intros; apply GlobalTheory.VolBr.encard_ball_pow_le <;> assumption)
end

section

open Filter Topology GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.encard_seminormBall_mul_le_convexity : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ n : ℕ, 0 < n → (B n).Finite → (B n).encard * (B (n / 2)).encard ≤ (B 1).encard * (B (n ^ 2 + n / 2)).encard := by
  first | exact @GlobalTheory.VolBr.isBallFam_encard_mul_le | exact GlobalTheory.VolBr.isBallFam_encard_mul_le | (intros; apply GlobalTheory.VolBr.isBallFam_encard_mul_le <;> assumption)
end

section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.encard_seminormBall_le_pow_mul_smaller : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (R : ℝ) (q r : ℕ), 0 < q → (∀ (n : ℕ) (e : Fin n → G), LinearIndependent ℤ e → (∀ j, e j ∈ B R) → n ≤ r) → (B R).encard ≤ ((q ^ r : ℕ) : ℕ∞) * (B (2 * R / q)).encard := by
  first | exact @GlobalTheory.VolBr.encard_ball_le_pow_mul | exact GlobalTheory.VolBr.encard_ball_le_pow_mul | (intros; apply GlobalTheory.VolBr.encard_ball_le_pow_mul <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), CompleteSpace (M.H τ) ∧ IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ (HolShape M → OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) ∧ ∀ a c, x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹ = (M.fr τ)⁻¹ * Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1 * M.fr τ) := by
  first | exact @GlobalTheory.HolDict.ModelRep.model_rep | exact GlobalTheory.HolDict.ModelRep.model_rep | (intros; apply GlobalTheory.HolDict.ModelRep.model_rep <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flagDomain_frames_eq_gramFrames_unitary : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ k, ∃ e : D.what₂.Tau ≃ (X k).Ψ, (∀ ρ, (e ρ).1 = tauE D ρ) ∧ (∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r, x ∈ (X k).dom ↔ (fun ρ a b => x (e ρ) (Fin.cast hr a) (Fin.cast hr b)) ∈ frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ))) ∧ ∀ γ ∈ (X k).Γ, ∀ ρ, Matrix.reindex (finCongr hr.symm) (finCongr hr.symm) ((γ : Matrix (Fin r) (Fin r) D.host.E).map (tauE D ρ)) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  first | exact @GlobalTheory.HolDict.FdDom.dom_iff_frDoms | exact GlobalTheory.HolDict.FdDom.dom_iff_frDoms | (intros; apply GlobalTheory.HolDict.FdDom.dom_iff_frDoms <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_compactType_in_compactStable_submodule : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → S ≠ ⊥ → ∃ (μ : Fin n → ℝ) (S' : Submodule ℂ H), S' ≤ S ∧ IsKTypeOf ε σ μ S' := by
  first | exact @GlobalTheory.KTypeExists.exists_kType | exact GlobalTheory.KTypeExists.exists_kType | (intros; apply GlobalTheory.KTypeExists.exists_kType <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.negativeFrameDomainProduct_open_preconnected_stable : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → IsOpen (frDoms Hm q) ∧ IsPreconnected (frDoms Hm q) ∧ (∀ u ∈ UG Hm, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) → ∀ x ∈ frDoms Hm q, (fun τ => (u τ * Matrix.of (x τ) * b τ : Mt n)) ∈ frDoms Hm q) ∧ (fun τ => (x₀ τ : Mt n)) ∈ frDoms Hm q := by
  first | exact @GlobalTheory.HolDict.frDoms_open_preconnected_stable | exact GlobalTheory.HolDict.frDoms_open_preconnected_stable | (intros; apply GlobalTheory.HolDict.frDoms_open_preconnected_stable <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smooth_gram_schmidt_indefinite_hermitian_frames : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ → ∃ β : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ), ContDiffOn ℝ ∞ β {x | Matrix.of x ∈ frDom Hm q} ∧ ∀ x : Fin n → Fin n → ℂ, Matrix.of x ∈ frDom Hm q → UpT (Matrix.of (β x)) ∧ Matrix.of x * (Matrix.of (β x))⁻¹ * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  first | exact @GlobalTheory.HolDict.GS.smooth_gramSchmidt | exact GlobalTheory.HolDict.GS.smooth_gramSchmidt | (intros; apply GlobalTheory.HolDict.GS.smooth_gramSchmidt <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ v ∈ Submodule.span ℂ {w | SmoothVec (lieH Hm) σ w}, SmoothVec (lieH Hm) σ v) ∧ ∀ v, SmoothVec (lieH Hm) σ v → (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, SmoothVec (lieH Hm) σ (σ g v)) ∧ (∀ X ∈ lieH Hm, SmoothVec (lieH Hm) σ (dRep σ X v) ∧ HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0) ∧ (∀ Z, SmoothVec (lieH Hm) σ (dRepC Hm σ Z v)) ∧ ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieH Hm) σ ℓ → ∀ X ∈ lieH Hm, HasDerivAt (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) (ℓ (dRep σ X v)) 0 := by
  first | exact @GlobalTheory.UnitarySmVec.smoothVec_basic | exact GlobalTheory.UnitarySmVec.smoothVec_basic | (intros; apply GlobalTheory.UnitarySmVec.smoothVec_basic <;> assumption)
end

section

noncomputable section

open MeasureTheory
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]

theorem avg_inner_map {T : W →L[ℂ] W} (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : W) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(T : W →ₗ[ℂ] W), hT⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y

theorem avg_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (KG ε) := by
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact hemb.isInducing.secondCountableTopology

theorem avg_continuous_toMK (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

def avgF (T : Mat n → (W →L[ℂ] W)) (S : Mat n → (Z →L[ℂ] Z)) (e : W) (f : Z) (w : W) (k : KG ε) : Z :=
  ⟪T (toMK k) e, w⟫_ℂ • S (toMK k) f

theorem avgF_continuous {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : Continuous (avgF (ε := ε) T S e f w) := by
  have h1 : Continuous fun k : KG ε => T (toMK k) e :=
    (hT.2.2 e).comp_continuous (avg_continuous_toMK ε) fun k => k.2
  have h2 : Continuous fun k : KG ε => S (toMK k) f :=
    (hS.2.2 f).comp_continuous (avg_continuous_toMK ε) fun k => k.2
  exact (h1.inner continuous_const).smul h2

theorem avgF_integrable {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : Integrable (avgF (ε := ε) T S e f w) (muK ε) := by
  have := avg_secondCountable ε
  exact integrableOn_univ.1 ((avgF_continuous hT hS e f w).continuousOn.integrableOn_compact isCompact_univ)

def avgMapL {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z) :
    W →ₗ[ℂ] Z where
  toFun w := ∫ k, avgF T S e f w k ∂(muK ε)
  map_add' x y := by
    rw [← integral_add (avgF_integrable hT hS e f x) (avgF_integrable hT hS e f y)]
    congr 1; funext k; simp [avgF, inner_add_right, add_smul]
  map_smul' c x := by
    rw [RingHom.id_apply, ← integral_smul]
    congr 1; funext k; simp [avgF, inner_smul_right, smul_smul]

theorem avgMapL_apply {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : avgMapL hT hS e f w = ∫ k, avgF T S e f w k ∂(muK ε) := rfl

theorem avgMapL_intertwines {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (g : KG ε) (w : W) : avgMapL hT hS e f (T (toMK g) w) = S (toMK g) (avgMapL hT hS e f w) := by
  rw [avgMapL_apply, avgMapL_apply, ← (S (toMK g)).integral_comp_comm (avgF_integrable hT hS e f w),
    ← integral_mul_left_eq_self _ g]
  congr 1; funext k
  have hm : toMK (g * k) = toMK g * toMK k := rfl
  simp only [avgF, hm, hT.1.2 _ g.2 _ k.2, hS.1.2 _ g.2 _ k.2, ContinuousLinearMap.comp_apply, map_smul]
  rw [avg_inner_map (hT.2.1 _ g.2)]

end

theorem tracePairing_nonzero_intertwiner : AvgMap := by
  intro n ε W _ _ _ T Z _ _ _ S Γ hT hS hne
  classical
  set b := stdOrthonormalBasis ℂ W
  set c := stdOrthonormalBasis ℂ Z
  let φ : Fin (Module.finrank ℂ Z) → Z →L[ℂ] ℂ := fun j =>
    LinearMap.toContinuousLinearMap ((innerₛₗ ℂ (c j)).comp Γ)
  have hφ : ∀ j u, φ j u = ⟪c j, Γ u⟫_ℂ := fun j u => rfl
  have hpt : ∀ i j (k : KG ε), φ j (avgF T S (b i) (c j) (b i) k) =
      conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ := by
    intro i j k
    simp [avgF, hφ, map_smul, inner_conj_symm]
  have hint : ∀ i j, Integrable (fun k : KG ε =>
      conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ) (muK ε) := fun i j =>
    ((φ j).integrable_comp (avgF_integrable hT hS (b i) (c j) (b i))).congr
      (Filter.Eventually.of_forall fun k => hpt i j k)
  have key : ∀ i j, ⟪c j, Γ (avgMapL hT hS (b i) (c j) (b i))⟫_ℂ =
      ∫ k, conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ ∂(muK ε) := by
    intro i j
    rw [avgMapL_apply, ← hφ, ← (φ j).integral_comp_comm (avgF_integrable hT hS _ _ _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => hpt i j k)
  have hsum : ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) =
      ∑ i, ∑ j, ⟪c j, Γ (avgMapL hT hS (b i) (c j) (b i))⟫_ℂ := by
    simp only [key]
    have hpw : ∀ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) =
        ∑ i, ∑ j, conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ := by
      intro k

      simp only [trK, LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ c, map_sum,
      Finset.sum_mul, Finset.mul_sum, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      exact Finset.sum_comm
    simp_rw [hpw]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
  rw [hsum] at hne
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  refine ⟨avgMapL hT hS (b i) (c j), fun h0 => hj ?_, fun k hk v => ?_⟩
  · rw [h0, LinearMap.zero_apply, map_zero, inner_zero_right]
  · have hk' : k ∈ Set.range (fun g : KG ε => toMK g) := by rw [Formalism.REAL.range_toMK]; exact hk
    obtain ⟨g, rfl⟩ := hk'
    exact avgMapL_intertwines hT hS (b i) (c j) g v

end GlobalTheory.PsCo.PcEF
end
end
