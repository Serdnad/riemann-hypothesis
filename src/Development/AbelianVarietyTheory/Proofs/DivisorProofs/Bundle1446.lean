module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipMass.Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_invol (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem cA_inclR (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem bar_add (w w' : Fin n → AE F E) :
    (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
  funext i; simp

theorem bar_sub (w w' : Fin n → AE F E) :
    (fun i => cA σ ((w - w') i)) = (fun i => cA σ (w i)) - fun i => cA σ (w' i) := by
  funext i; simp

theorem bar_smul (a : AE F E) (w : Fin n → AE F E) :
    (fun i => cA σ ((a • w) i)) = cA σ a • fun i => cA σ (w i) := by
  funext i; simp

theorem hA_add_left (v v' w : Fin n → AE F E) : hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp [hA, add_dotProduct]

theorem hA_sub_left (v v' w : Fin n → AE F E) : hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp [hA, sub_dotProduct]

theorem hA_smul_left (a : AE F E) (v w : Fin n → AE F E) : hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

theorem hA_add_right (v w w' : Fin n → AE F E) : hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  simp only [hA, bar_add, Matrix.mulVec_add, dotProduct_add]

theorem hA_sub_right (v w w' : Fin n → AE F E) : hA σ J v (w - w') = hA σ J v w - hA σ J v w' := by
  simp only [hA, bar_sub, Matrix.mulVec_sub, dotProduct_sub]

theorem hA_smul_right (a : AE F E) (v w : Fin n → AE F E) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  simp only [hA, bar_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hA_swap (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) :
    hA σ J w v = -cA σ (hA σ J v w) := by

  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_invol σ hσ, incM, Matrix.map_apply, cA_inclR, hJ,
  map_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun x x_1 => (cA σ) (v x) * (-(inclR (F := F) (AF F)) (J x_1 x) * w x_1))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {σ J}

theorem hA_nmat (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (x u : Fin n → AE F E) (c : AE F E)
    (hxx : hA σ J x x = 0) (hux : hA σ J u x = 0) (hc : c - cA σ c = -hA σ J u u) (v w : Fin n → AE F E) :
    hA σ J (nmat σ J x u c *ᵥ v) (nmat σ J x u c *ᵥ w) = hA σ J v w := by
  have hxu : hA σ J x u = 0 := by rw [hA_swap σ J hσ hJ u x, hux, map_zero, neg_zero]
  have hxw : hA σ J x w = -cA σ (hA σ J w x) := hA_swap σ J hσ hJ w x
  have huw : hA σ J u w = -cA σ (hA σ J w u) := hA_swap σ J hσ hJ w u
  rw [nmat_mulVec, nmat_mulVec]
  simp only [hA_sub_left, hA_sub_right, hA_smul_left, hA_smul_right, hA_add_left, hA_add_right, hxx, hux, hxu,
    hxw, huw]
  linear_combination (hA σ J v x * cA σ (hA σ J w x)) * hc

theorem entry_eq (T : Matrix (Fin n) (Fin n) (AE F E)) (i j : Fin n) :
    (Tᵀ * incM F J * T.map (cA σ)) i j = hA σ J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  have hs : ∀ m : Fin n, T *ᵥ Pi.single m 1 = fun k => T k m := fun m => by
    funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hs, hs]
  simp only [hA, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem entry_J (hσ : ∀ a, σ (σ a) = a) (i j : Fin n) :
    incM F J i j = hA σ J (Pi.single i 1) (Pi.single j 1) := by
  have hb : (fun l => cA σ ((Pi.single j 1 : Fin n → AE F E) l)) = Pi.single j 1 := by
    funext l; by_cases h : l = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hA, hb, single_one_dotProduct, Matrix.mulVec_single_one]
  simp

end GlobalTheory.UnipMass.Unitary

namespace GlobalTheory.UnipMass

theorem nmat_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u : Fin n → AE F E) (c : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → c - cA σ c = -hA σ J u u → (nmat σ J x u c)ᵀ * incM F J * (nmat σ J x u c).map (cA σ) = incM F J := by
  intro F E _ _ _ _ _ σ hσ n J hJ x u c hxx hux hc
  ext i j
  rw [Unitary.entry_eq, Unitary.hA_nmat hσ hJ x u c hxx hux hc, ← Unitary.entry_J hσ]

end GlobalTheory.UnipMass
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section
namespace GlobalTheory.UnipMass
namespace ProdFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_cA_of_invol (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cA_incM_apply (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    cA σ (incM F J i j) = incM F (J.map σ) i j := by
  simp [cA, incM, inclR]

theorem hA_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J w v = - cA σ (hA σ J v w) := by

  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA_of_invol σ hσ, cA_incM_apply]
  simp only [incM, Matrix.map_apply, hJ, map_neg]
  simp only [Finset.mul_sum, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp only [hA, add_dotProduct]

theorem hA_sub_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    hA σ J (v - v') w = hA σ J v w - hA σ J v' w := by
  simp only [hA, sub_dotProduct]

theorem hA_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    hA σ J (a • v) w = a * hA σ J v w := by
  simp only [hA, smul_dotProduct, smul_eq_mul]

theorem hA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
    funext i; simp
  simp only [hA, this, Matrix.mulVec_add, dotProduct_add]

end ProdFormula


open ProdFormula in
theorem nmat_mul_nmat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) →
    ∀ (x u u' : Fin n → AE F E) (c c' : AE F E), hA σ J x x = 0 → hA σ J u x = 0 → hA σ J u' x = 0 →
    nmat σ J x u c * nmat σ J x u' c' = nmat σ J x (u + u') (c + c' - hA σ J u' u) := by
  intro F E _ _ _ _ _ σ hσ n J hJ x u u' c c' hxx hux hu'x
  have hxu : hA σ J x u = 0 := by rw [hA_swap σ hσ J hJ u x, hux, map_zero, neg_zero]
  have key : ∀ v, (nmat σ J x u c * nmat σ J x u' c') *ᵥ v =
      nmat σ J x (u + u') (c + c' - hA σ J u' u) *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, nmat_mulVec, nmat_mulVec, nmat_mulVec]
    simp only [hA_add_left, hA_sub_left, hA_smul_left, hA_add_right, hxx, hux, hu'x, hxu]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa only [Matrix.toLin'_apply] using key v)

end GlobalTheory.UnipMass
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def growth : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (g * infGL E a y)‖ ≤ C * height y ^ N}
  zero_mem' g := ⟨0, 0, fun y => by simp⟩
  add_mem' {f f'} h h' g := by
    obtain ⟨C, N, hC⟩ := h g
    obtain ⟨C', N', hC'⟩ := h' g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have h1 := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ h1 (by omega)
    have q1 : 0 ≤ height y ^ N := le_trans zero_le_one (one_le_pow₀ h1)
    have q2 : 0 ≤ height y ^ N' := le_trans zero_le_one (one_le_pow₀ h1)
    calc ‖(f + f') (g * infGL E a y)‖ ≤ ‖f (g * infGL E a y)‖ + ‖f' (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (hC y) (hC' y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) q1).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') q2).trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring
  smul_mem' c f h g := by
    obtain ⟨C, N, hC⟩ := h g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)


variable (E a) in
def tame : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ l : List (Lie E a), ((l.map (lie E a)).prod ψ).1 ∈ growth E a}
  zero_mem' l := by simp
  add_mem' {ψ ψ'} h h' l := by
    rw [map_add (f := _), Submodule.coe_add]
    exact add_mem (h l) (h' l)
  smul_mem' c ψ h l := by
    rw [map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ c (h l)

theorem growth_of_tame {ψ : Sm E a} (h : ψ ∈ tame E a) : ψ.1 ∈ growth E a := by
  simpa using h []

theorem lie_mem_tame (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ tame E a) : lie E a X ψ ∈ tame E a := by
  intro l
  have e : (l.map (lie E a)).prod (lie E a X ψ) = ((l ++ [X]).map (lie E a)).prod ψ := by
    simp [List.map_append, List.prod_append, Module.End.mul_apply]
  rw [e]
  exact h _

def dens (X : Lie E a) (α : Lie E a → ℂ) (x : Lie E a) : ℂ :=
  -(fderiv ℝ α x (lmul X x) + (LinearMap.trace ℝ (Lie E a) (lmul X).toLinearMap : ℂ) * α x)

def KInv (α : Lie E a → ℂ) : Prop :=
  ∀ (k : Kinf E a) (x : Lie E a),
    α (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = α x

def maps (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a))
    (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) : Submodule ℂ (W →ₗ[ℂ] Sm E a) where
  carrier := {T | (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
    ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧ ∀ k ∈ L, finRep E a k (T w) = T w}
  zero_mem' := ⟨fun k w => by simp, fun w => ⟨by simp, fun _ _ => rfl, fun k _ => by simp⟩⟩
  add_mem' {T T'} h h' := ⟨fun k w => by simp [h.1 k w, h'.1 k w], fun w =>
    ⟨by simpa using add_mem (h.2 w).1 (h'.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g, (h'.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk, (h'.2 w).2.2 k hk]⟩⟩
  smul_mem' c T h := ⟨fun k w => by simp [h.1 k w], fun w =>
    ⟨by simpa using Submodule.smul_mem _ c (h.2 w).1,
     fun γ g => by simp [(h.2 w).2.1 γ g],
     fun k hk => by simp [(h.2 w).2.2 k hk]⟩⟩

theorem isTest_dens (X : Lie E a) {α : Lie E a → ℂ} (h : GlobalTheory.CuspQuot.IsTest (invSet E a) α) :
    GlobalTheory.CuspQuot.IsTest (invSet E a) (dens X α) := by
  have hs : Function.support (dens X α) ⊆ tsupport α := by
    intro x hx
    by_contra hn
    apply hx
    have h1 : α x = 0 := image_eq_zero_of_notMem_tsupport hn
    have h2 : fderiv ℝ α x = 0 := fderiv_of_notMem_tsupport ℝ hn
    simp [dens, h1, h2]
  have ht : tsupport (dens X α) ⊆ tsupport α := closure_minimal hs (isClosed_tsupport α)
  refine ⟨?_, h.2.1.mono' hs, ht.trans h.2.2⟩
  refine (((h.1.fderiv_right (m := ∞) (by simp)).clm_apply (lmul X).contDiff).add
    (contDiff_const.mul h.1)).neg

end GlobalTheory.AutGrowth
end
end

section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

theorem blockUni_conj_mem (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ)
    (e : ι ≃ Fin a ⊕ Fin b) :
    ∀ p ∈ GlobalTheory.OrbDesc.blockPar (K := K) e, ∀ n ∈ GlobalTheory.OrbDesc.blockUni e,
      p * n * p⁻¹ ∈ GlobalTheory.OrbDesc.blockUni e := by
  intro p hp n hn
  obtain ⟨x, rfl⟩ := hn
  have hre : ∀ M N : Matrix ι ι K,
      Matrix.reindex e e (M * N) = Matrix.reindex e e M * Matrix.reindex e e N := by
    intro M N
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  have h21 : ∀ g ∈ blockPar (K := K) e, (Matrix.reindex e e (g : Matrix ι ι K)).toBlocks₂₁ = 0 := by
    intro g hg
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.zero_apply]
    apply hg
    simp [side]
  set P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K := Matrix.reindex e e (p : Matrix ι ι K) with hP
  set Q : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K :=
    Matrix.reindex e e ((p⁻¹ : GL ι K) : Matrix ι ι K) with hQ
  have hP21 : P.toBlocks₂₁ = 0 := h21 p hp
  have hQ21 : Q.toBlocks₂₁ = 0 := h21 _ (Subgroup.inv_mem _ hp)
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← hre, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp
  refine ⟨Multiplicative.ofAdd (fun i j => (P.toBlocks₁₁ * Matrix.of x.toAdd * Q.toBlocks₂₂) i j), ?_⟩
  apply Units.ext
  apply (Matrix.reindex e e).injective
  show Matrix.reindex e e (uMat e _) = Matrix.reindex e e ((p : Matrix ι ι K) * uMat e x.toAdd * ((p⁻¹ : GL ι K) : Matrix ι ι K))
  rw [hre, hre, ← hP, ← hQ]
  have hU : ∀ Y : Fin a → Fin b → K, Matrix.reindex e e (uMat e Y) = Matrix.fromBlocks 1 (Matrix.of Y) 0 1 := by
    intro Y
    simp [uMat]
  rw [hU, hU]
  rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q] at hPQ ⊢
  rw [hP21, hQ21] at hPQ ⊢
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hPQ
  obtain ⟨h11, h12, -, h22⟩ := hPQ
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add] at h11 h12 h22 ⊢
  rw [h11, h22]
  congr 1
  have key : P.toBlocks₁₁ * Q.toBlocks₁₂ + (P.toBlocks₁₁ * Matrix.of x.toAdd + P.toBlocks₁₂) * Q.toBlocks₂₂
      = P.toBlocks₁₁ * Matrix.of x.toAdd * Q.toBlocks₂₂ := by
    rw [Matrix.add_mul, ← add_assoc, add_comm (P.toBlocks₁₁ * Q.toBlocks₁₂), add_assoc, h12, add_zero]
  rw [key]
  ext i j
  simp

end GlobalTheory.OrbDesc
end

section

noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem locPart_mul {T L : Subgroup H} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : GlobalTheory.LKLoc.locPart T L (t * x * l) = GlobalTheory.LKLoc.locPart T L x := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l * k * l⁻¹, L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), ?_⟩
    calc x * (l * k * l⁻¹) * x⁻¹ = t⁻¹ * ((t * x * l * k * (t * x * l)⁻¹) * t) := by group
      _ = t⁻¹ * (t * (t * x * l * k * (t * x * l)⁻¹)) := by rw [hT _ hg t ht]
      _ = t * x * l * k * (t * x * l)⁻¹ := by group
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l⁻¹ * k * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl, ?_⟩
    have := hT _ hg t ht
    calc t * x * l * (l⁻¹ * k * l) * (t * x * l)⁻¹ = t * (x * k * x⁻¹) * t⁻¹ := by group
      _ = (x * k * x⁻¹) * t * t⁻¹ := by rw [← this]
      _ = x * k * x⁻¹ := by group

theorem wt_mul {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : wt T L U Ψ (t * x * l) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_mul hT ht hl, hΨr l hl, hΨl t ht]

theorem wt_out {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) (x : H) :
    wt T L U Ψ (Quotient.out (DoubleCoset.mk T L x)) = wt T L U Ψ x := by
  obtain ⟨t, ht, l, hl, h⟩ := (@DoubleCoset.eq _ _ T L _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk T L x))
  exact (wt_mul U hT hΨl hΨr ht hl).symm.trans (congrArg _ h.symm)

end GlobalTheory.OrbDesc
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.SchOp

theorem iteratedDeriv_cexp_real (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_ech : Function.HasTemperateGrowth ech := by
  set a : ℂ := -(2 * Real.pi * Complex.I) with ha
  have e : ech = fun y : ℝ => Complex.exp (a * y) := rfl
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (a * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨by rw [e]; exact hc, fun n => ⟨0, ‖a‖ ^ n, fun x => ?_⟩⟩
  rw [e, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (a * x)‖ = 1 := by
    have : a * (x : ℂ) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by rw [ha]; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_ech_affine {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Y →L[ℝ] ℝ) (c : ℝ) : Function.HasTemperateGrowth (fun x : Y => ech (L x + c)) :=
  hasTemperateGrowth_ech.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))

theorem sch_schwartz {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : SchwartzMap Y ℂ) : ∃ g : SchwartzMap Y ℂ, ⇑g = sch β a b ⇑f := by
  let L : Y →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (β.flip b)
  have hL : ∀ x, L x = β x b := fun x => rfl
  have hm : Function.HasTemperateGrowth (fun x : Y => ech (β x b + β a b / 2)) := by
    simpa only [hL] using hasTemperateGrowth_ech_affine L (β a b / 2)
  have ht : Function.HasTemperateGrowth (fun x : Y => x + a) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)
  have hu : ∃ (k : ℕ) (C : ℝ), ∀ x : Y, ‖x‖ ≤ C * (1 + ‖x + a‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, fun x => ?_⟩
    have h1 : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
      calc ‖x‖ = ‖(x + a) - a‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
    have h2 := norm_nonneg (x + a)
    have h3 := norm_nonneg a
    rw [pow_one]
    nlinarith
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x b + β a b / 2)) (SchwartzMap.compCLM ℂ ht hu f), ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, SchwartzMap.compCLM_apply]
  simp [sch, smul_eq_mul]

end GlobalTheory.SchOp
end
