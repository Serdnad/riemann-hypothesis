module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle099
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsGenericFibreOfClosedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle771
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Matrix Topology
open scoped ContDiff

namespace GlobalTheory.LeviSliceGA

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

def lowL (hr : r ≤ a) : Lie E (a - r) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr) (GlobalTheory.LeviGA.blkEquiv hr)
        (Matrix.fromBlocks 0 0 0 (Matrix.of y)))
      map_add' := fun y z => by
        funext i j
        obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
        obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
        rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply]
      map_smul' := fun c y => by
        funext i j
        obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
        obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
        rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply] }

theorem lowL_apply (hr : r ≤ a) (y : Lie E (a - r)) : lowL hr y = toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr)
    (GlobalTheory.LeviGA.blkEquiv hr) (Matrix.fromBlocks 0 0 0 (Matrix.of y))) := rfl

def affA (hr : r ≤ a) (y : Lie E (a - r)) : Lie E a :=
  lowL hr y + toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr) (GlobalTheory.LeviGA.blkEquiv hr) (Matrix.fromBlocks 1 0 0 0))

theorem affA_val (hr : r ≤ a) (u : GL (Fin (a - r)) (Cinf E)) :
    affA hr (toL u.val) = toL (GlobalTheory.LeviGA.blkGL hr (1, u)).val := by
  rw [affA, lowL_apply, GlobalTheory.LeviGA.blkGL_val]
  funext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply]

theorem infGL_apply {n : ℕ} (g : GL (Fin n) (Cinf E)) (i j : Fin n) :
    (infGL E n g : Matrix (Fin n) (Fin n) (Ad E)) i j = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j -
      sInf E ((1 : Matrix (Fin n) (Fin n) (Cinf E)) i j) + sInf E ((g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := rfl

theorem blkGL_infGL (hr : r ≤ a) (u : GL (Fin (a - r)) (Cinf E)) :
    GlobalTheory.LeviGA.blkGL hr ((1 : GA E r), infGL E (a - r) u) = infGL E a (GlobalTheory.LeviGA.blkGL hr (1, u)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rw [GlobalTheory.LeviGA.blkGL_apply, infGL_apply, GlobalTheory.LeviGA.blkGL_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, (GlobalTheory.LeviGA.blkEquiv hr).injective.eq_iff, infGL_apply]

theorem chart_slice (hr : r ≤ a) (m₁ : GA E r) (φ : GA E a → ℂ) (m₂ : GA E (a - r)) {y : Lie E (a - r)}
    (hy : y ∈ invSet E (a - r)) :
    chart (fun m : GA E (a - r) => φ (GlobalTheory.LeviGA.blkGL hr (m₁, m))) m₂ y =
      chart φ (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) (affA hr y) := by
  obtain ⟨u, hu⟩ := hy
  have e : y = toL u.val := hu.symm
  subst e
  rw [chart_val, affA_val, chart_val, ← blkGL_infGL, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem affA_one (hr : r ≤ a) : affA hr (oneL E (a - r)) = oneL E a := by
  have h := affA_val (E := E) hr 1
  rw [show ((1 : GL (Fin r) (Cinf E)), (1 : GL (Fin (a - r)) (Cinf E))) = 1 from rfl, map_one] at h
  exact h

theorem hasFDerivAt_affA (hr : r ≤ a) (y : Lie E (a - r)) : HasFDerivAt (affA hr) (lowL (E := E) hr) y :=
  (lowL hr).hasFDerivAt.add_const _

theorem lowL_single (hr : r ≤ a) (p p' : Fin (a - r)) (x : Cinf E) :
    lowL hr (toL (Matrix.single p p' x)) =
      toL (Matrix.single (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) x) := by
  rw [lowL_apply]
  funext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [toL, Matrix.reindex_apply, Matrix.single_apply, (GlobalTheory.LeviGA.blkEquiv hr).injective.eq_iff] <;>
    by_cases hi : i = p <;> by_cases hj : j = p' <;> simp [hi, hj, Pi.single_apply] <;> intros <;> simp_all

theorem slice_mem_Sm (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a) :
    (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) := fun m₂ =>
  ((f.2 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))).comp ((lowL (E := E) hr).contDiff.add contDiff_const).contDiffOn
    (fun y hy => by
      obtain ⟨u, hu⟩ := hy
      have e : y = toL u.val := hu.symm
      subst e
      show affA hr _ ∈ _
      rw [affA_val]
      exact val_mem_invSet _)).congr fun y hy => chart_slice hr m₁ f.1 m₂ hy

theorem lieS_slice (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a) (p p' : Fin (a - r)) (ψ : Sm E (a - r))
    (hψ : ψ.1 = fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) (x : Cinf E) (m₂ : GA E (a - r)) :
    (lieS E (a - r) p p' x ψ).1 m₂ =
      (lieS E a (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) x f).1
        (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  rw [GlobalTheory.CuspRep.lieS_apply, GlobalTheory.CuspRep.lieS_apply, GlobalTheory.CuspRep.lie_apply, GlobalTheory.CuspRep.lie_apply, lieD, lieD, hψ]
  have ev : chart (fun m : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m))) m₂ =ᶠ[𝓝 (oneL E (a - r))]
      chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) ∘ affA hr :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun y hy => chart_slice hr m₁ f.1 m₂ hy
  have hd : HasFDerivAt (chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)))
      (fderiv ℝ (chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) (oneL E a)) (affA hr (oneL E (a - r))) := by
    rw [affA_one]; exact (differentiableAt_chart f.2 _).hasFDerivAt
  rw [ev.fderiv_eq, (hd.comp (oneL E (a - r)) (hasFDerivAt_affA hr _)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, lowL_single]

theorem slice_smooth_Eop : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    (m₁ : GA E r) (f : Sm E a),
    (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) ∧
      ∀ (τ : E →+* ℂ) (p p' : Fin (a - r)) (ψ : Sm E (a - r)),
        ψ.1 = (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) →
        (Eop τ p p' ψ).1 = fun m₂ : GA E (a - r) =>
          (Eop τ (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) f).1
            (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  intro E _ _ _ a r hr m₁ f
  refine ⟨slice_mem_Sm hr m₁ f, fun τ p p' ψ hψ => funext fun m₂ => ?_⟩
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, lieS_slice hr m₁ f p p' ψ hψ]

end GlobalTheory.LeviSliceGA
end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviGA

open Matrix

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem mul_mul_upper {R : Type} [CommRing R] (A N B : Matrix (Fin a) (Fin a) R)
    (hA : ∀ k p : Fin a, ((k : ℕ) < r ↔ (p : ℕ) < r) ∨ A k p = 0)
    (hB : ∀ q l : Fin a, ((q : ℕ) < r ↔ (l : ℕ) < r) ∨ B q l = 0)
    (hN : ∀ p q : Fin a, ¬((p : ℕ) < r ∧ r ≤ (q : ℕ)) → N p q = 0)
    (k l : Fin a) (hkl : ¬((k : ℕ) < r ∧ r ≤ (l : ℕ))) : (A * N * B) k l = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hpq : (p : ℕ) < r ∧ r ≤ (q : ℕ)
  · rcases hA k p with h1 | h1
    · rcases hB q l with h2 | h2
      · exact absurd ⟨h1.2 hpq.1, by by_contra h; exact absurd (h2.2 (by omega)) (by omega)⟩ hkl
      · rw [h2, mul_zero]
    · rw [h1, zero_mul, zero_mul]
  · rw [hN p q hpq, mul_zero, zero_mul]

theorem lieD_single_blkGL (hr : r ≤ a) (f : Sm E a)
    (hf : ∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g)
    (i j : Fin a) (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) (p : GA E r × GA E (a - r)) (x : Cinf E) :
    lieD (toL (Matrix.single i j x)) f.1 (blkGL hr p) = 0 := by
  set m : GA E a := blkGL hr p with hm
  set S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.single i j x with hS
  have hij : j ≠ i := fun h => by rw [h] at hj; omega
  have hSS : S * S = 0 := by rw [hS]; simp [hij, hij.symm]
  let c : ℝ → GL (Fin a) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by simp [mul_sub, add_mul, smul_mul_smul_comm, hSS],
      by simp [sub_mul, mul_add, smul_mul_smul_comm, hSS]⟩
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hc : HasDerivAt (fun t => toL (c t).val) (toL S) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add (toL (1 : Matrix (Fin a) (Fin a) (Cinf E)))
    rw [one_smul] at this
    exact this
  have hd := hasDerivAt_curve f m c (toL S) h0 hc

  have hconst : ∀ t, f.1 (m * infGL E a (c t)) = f.1 m := by
    intro t
    set N : Matrix (Fin a) (Fin a) (Ad E) := matN a (sInf E) (t • S) with hN
    have hinf : (infGL E a (c t)).val = 1 + N := by
      change 1 - matN a (sInf E) 1 + matN a (sInf E) (1 + t • S) = 1 + N
      rw [map_add (f := _)]; abel
    have hNsupp : ∀ p q : Fin a, ¬((p : ℕ) < r ∧ r ≤ (q : ℕ)) → N p q = 0 := by
      intro p q hpq
      have : (t • S) p q = 0 := by
        rw [hS, Matrix.smul_apply]
        by_cases e : p = i ∧ q = j
        · exact absurd (by rw [e.1, e.2]; exact ⟨hi, hj⟩) hpq
        · rw [Matrix.single_apply_of_ne (h := by tauto), smul_zero]
      change sInf E ((t • S) p q) = 0
      rw [this, map_zero]
    have hinv : m⁻¹ = blkGL hr p⁻¹ := by rw [hm, map_inv]
    let y : BlockIx a r → Ad E := fun q => (m.val * N * (m⁻¹).val) q.1.1 q.1.2
    have hy : nilM y = m.val * N * (m⁻¹).val := by
      ext k l
      simp only [nilM, Matrix.of_apply, y]
      split_ifs with h
      · rfl
      · exact (mul_mul_upper _ _ _ (blkGL_block hr p) (by rw [hinv]; exact blkGL_block hr _) hNsupp k l h).symm
    have e : m * infGL E a (c t) = unip y * m := by
      apply Units.ext
      change m.val * (infGL E a (c t)).val = (1 + nilM y) * m.val
      rw [hinf, hy, add_mul, one_mul, mul_add, mul_one, mul_assoc _ _ m.val,
        Units.inv_mul, mul_one]
    rw [e, hf]
  have hfun : (fun t => f.1 (m * infGL E a (c t))) = fun _ => f.1 m := funext hconst
  rw [hfun] at hd
  exact hd.unique (hasDerivAt_const 0 _)

theorem Eop_upper_blkGL_eq_zero :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a),
        (i : ℕ) < r → r ≤ (j : ℕ) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)),
          (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  intro E _ _ _ a r hr f hf τ i j hi hj m₁ m₂
  have key : ∀ x : Cinf E, (lieS E a i j x f).1 (blkGL hr (m₁, m₂)) = 0 := fun x =>
    lieD_single_blkGL hr f hf i j hi hj (m₁, m₂) x
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, key, smul_zero, sub_zero]

end GlobalTheory.LeviGA
end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem block_mul {R : Type} [CommRing R] {M N : Matrix (Fin a) (Fin a) R}
    (hM : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ M i j = 0)
    (hN : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ N i j = 0) :
    ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (M * N) i j = 0 := by
  intro i j
  by_cases h : ((i : ℕ) < r ↔ (j : ℕ) < r)
  · exact Or.inl h
  · right
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases hM i k with h1 | h1
    · rcases hN k j with h2 | h2
      · exact absurd (h1.trans h2) h
      · rw [h2, mul_zero]
    · rw [h1, zero_mul]

theorem block_infGL (y : GL (Fin a) (Cinf E))
    (hy : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (y : Matrix (Fin a) (Fin a) (Cinf E)) i j = 0) :
    ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (infGL E a y : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := by
  intro i j
  by_cases h' : ((i : ℕ) < r ↔ (j : ℕ) < r)
  · exact Or.inl h'
  · right
    have h := (hy i j).resolve_left h'
    have hij : i ≠ j := fun e => h' (by rw [e])
    change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) = 0
    rw [h, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, sub_zero, zero_add]

theorem lieD_single_blkGL (hr : r ≤ a) (f : Sm E a)
    (hf : ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0)
    (i j : Fin a) (hij : (i : ℕ) < r ↔ (j : ℕ) < r) (x : Cinf E) (m₁ : GA E r) (m₂ : GA E (a - r)) :
    lieD (toL (Matrix.single i j x)) f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  set m := GlobalTheory.LeviGA.blkGL hr (m₁, m₂)
  set X : Lie E a := toL (Matrix.single i j x)
  have hz : ∀ t : ℝ, chart f.1 m (oneL E a + t • X) = 0 := by
    intro t
    unfold chart
    split_ifs with hu
    · have hyb : ∀ k l : Fin a, ((k : ℕ) < r ↔ (l : ℕ) < r) ∨
          ((hu.unit : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) k l = 0 := by
        intro k l
        rw [hu.unit_spec]
        by_cases hkl : ((k : ℕ) < r ↔ (l : ℕ) < r)
        · exact Or.inl hkl
        · right
          have hne : k ≠ l := fun e => hkl (by rw [e])
          have hs : Matrix.single i j x k l = 0 := by
            rw [Matrix.single_apply]
            rw [if_neg]
            rintro ⟨e1, e2⟩
            exact hkl (by rw [← e1, ← e2]; exact hij)
          change (1 : Matrix (Fin a) (Fin a) (Cinf E)) k l + t • Matrix.single i j x k l = 0
          rw [hs, Matrix.one_apply_ne hne, smul_zero, add_zero]
      obtain ⟨p, hp⟩ := GlobalTheory.LeviGA.exists_blkGL hr (m * infGL E a hu.unit)
        (by rw [Units.val_mul]; exact block_mul (GlobalTheory.LeviGA.blkGL_block hr _) (block_infGL _ hyb))
      rw [← hp]
      exact hf p.1 p.2
    · rfl
  have hline : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E a)
    rwa [one_smul] at this
  have hd : HasFDerivAt (chart f.1 m) (fderiv ℝ (chart f.1 m) (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (differentiableAt_chart f.2 m).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (chart f.1 m ∘ fun t : ℝ => oneL E a + t • X) 0 0 := by
    have e : (chart f.1 m ∘ fun t : ℝ => oneL E a + t • X) = fun _ => 0 := funext hz
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem Eop_blkGL_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    (f : Sm E a), (∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0) →
    ∀ (τ : E →+* ℂ) (i j : Fin a), ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)),
      (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  intro E _ _ _ a r hr f hf τ i j hij m₁ m₂
  have k := fun x => lieD_single_blkGL hr f hf i j hij x m₁ m₂
  change (1 / 2 : ℂ) * ((lieS E a i j (atEmb τ 1) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) -
    Complex.I * (lieS E a i j (atEmb τ Complex.I) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) = 0
  rw [lieS_apply, lieS_apply, lie_apply, lie_apply, k, k]
  simp

end GlobalTheory.LeviDeriv

end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.strict_henselisation_prime_eq : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j ∧
      ∃ (D₁ : Type) (_ : CommRing D₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁)
        (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ ∧
        ∀ σ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ →
          Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_torsor) | (exact GlobalTheory.KeyOriginCut.exists_stage_torsor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_torsor  <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem _root_.GlobalTheory.T.lineDegree_ge_of_twisted_section : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ (n : ℕ) (h : Place k F → Matrix (Fin n) (Fin n) F), admitted h → ∀ (v₀ : Place k F) (π : F), π ≠ 0 → ord v₀ π = 1 → ∀ (e : ℤ) (p : Fin n → F), p ≠ 0 → (∀ (v : Place k F) (i : Fin n), v.1 ((twistAt v₀ (π ^ (-e)) h v).mulVec p i) ≤ 1) → e ≤ degLine h p := by
  first | exact @GlobalTheory.Nef.degLine_ge_of_twist | exact GlobalTheory.Nef.degLine_ge_of_twist | (intros; apply GlobalTheory.Nef.degLine_ge_of_twist <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

open GlobalTheory.PDivGroup

theorem pow_sub_counit_mem_frobKerIdeal {p : ℕ} [Fact p.Prime] {R H : Type} [CommRing R]
    [CommRing H] [Bialgebra R H] (h : (p : R) = 0) (a : H) :
    a ^ p - algebraMap R H (counit (R := R) (a ^ p)) ∈ frobKerIdeal p R H := by
  have h0 := natCast_eq_zero_of_algebra h H
  have e : a ^ p - algebraMap R H (counit (R := R) (a ^ p)) =
      (a - algebraMap R H (counit (R := R) a)) ^ p := by
    rw [← frobRing_apply h0 (a - _), map_sub, frobRing_apply, frobRing_apply, counit_pow, map_pow]
  rw [e]
  exact pow_mem_frobKerIdeal (by simp [RingHom.mem_ker])

theorem kerIdeal_relFrob_le_frobKerIdeal (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) := by
  have key : ∀ x : (frobTwist h G).A n, (relFrob h G).app n x -
      algebraMap R (G.A n) (counit (R := R) ((relFrob h G).app n x)) ∈
        frobKerIdeal p R (G.A n) := by
    intro x
    induction x using frobTwist_induction h n with
    | h0 => simp
    | h1 r a =>
      rw [map_smul, relFrob_app_frobProj, map_smul, smul_eq_mul, map_mul, Algebra.smul_def,
        ← mul_sub]
      exact Ideal.mul_mem_left _ _ (pow_sub_counit_mem_frobKerIdeal h a)
    | h2 x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact add_mem hx hy
  refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
  have hx' : counit (R := R) x = 0 := hx
  have := key x
  rw [CoalgHomClass.counit_comp_apply, hx', map_zero, sub_zero] at this
  exact this

end GlobalTheory.PDiv
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstants_genericFibre_of_closedPoints : GlobalTheory.VertUnits.DivConstClosedPts → GlobalTheory.VertUnits.DivConstGeneric := by
  first | exact @GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | exact GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | (intros; apply GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt : ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S) (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  first | (exact @GlobalTheory.strictHenselisation_etale_over_polynomial) | (exact GlobalTheory.strictHenselisation_etale_over_polynomial) | (intros; apply GlobalTheory.strictHenselisation_etale_over_polynomial  <;> assumption)
end
