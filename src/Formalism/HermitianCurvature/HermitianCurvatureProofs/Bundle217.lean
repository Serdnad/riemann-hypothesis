module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle204
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle078
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle071
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle069
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle207
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem exponential_degree_holds : FExpDeg := by
  intro k r gens
  induction gens with
  | nil =>
    intro _ t ht
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | cons gn gs ih =>
    intro hdeg t ht
    have hgn : gn.1.natDegree ≤ 1 := hdeg gn (by simp)
    have ih' := ih (fun g hg => hdeg g (List.mem_cons_of_mem _ hg))
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨dX, hdX, t', ht', rfl⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_mul_le (p := gn.1) (q := t'.1)
        simp only [List.length_cons]
        omega
      · intro X hX
        obtain ⟨g, hg, d, hd⟩ := h2 X hX
        exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_C_mul_le dX.1 t'.1
        simp only [List.length_cons]
        omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨gn, by simp, dX.1, hdX⟩
        · obtain ⟨g, hg, d, hd⟩ := h2 X hX
          exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

namespace ExponentialSymbolLetters

variable {k r : ℕ} (τ : B.Mat k r → ℂ) (u s : ℂ)

def phi (t : Polynomial ℂ × List (B.Mat k r)) : ℂ := t.1.eval u * s ^ t.2.length * (t.2.map τ).prod

theorem head (p : Polynomial ℂ) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (p * t.1, t.2)).map (phi τ u s)).sum = p.eval u * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul]
  ring

theorem letter (d : ℂ) (X : B.Mat k r) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (Polynomial.C d * t.1, X :: t.2)).map (phi τ u s)).sum =
      (d * s * τ X) * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul, Polynomial.eval_C, List.length_cons, pow_succ,
    List.map_cons, List.prod_cons]
  ring

theorem letters (L : List (ℂ × B.Mat k r)) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((L.flatMap fun dX => l.map fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)).map (phi τ u s)).sum =
      s * (L.map fun dX => dX.1 * τ dX.2).sum * (l.map (phi τ u s)).sum := by
  induction L with
  | nil => simp
  | cons dX L ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, letter, ih, List.map_cons, List.sum_cons]
    ring

theorem all (gs : List (GenW k r)) : ((fexp gs).map (phi τ u s)).sum =
    (gs.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod := by
  induction gs with
  | nil => simp [fexp, phi]
  | cons gn gs ih =>
    rw [fexp, List.map_append, List.sum_append, head, letters, List.map_cons, List.prod_cons, ← ih]
    ring

end ExponentialSymbolLetters

theorem exponential_symbol_holds : FExpSymb := by
  intro k r gens τ u s
  exact ExponentialSymbolLetters.all τ u s gens

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cvag_posL_iff {k r : ℕ} (a b : Fin (Q.mdim k r 0)) : Q.posL k r 0 a = Q.posL k r 0 b ↔ a = b := by
  simp [Q.posL, Fin.ext_iff]

theorem cvag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : ℂ)
    (σ : Equiv.Perm (Fin (Q.mdim k r 0))) :
    (List.ofFn fun i : Fin (Q.mdim k r 0) =>
      Top (Q.EH (E := E) k r) (u - ((i : ℕ) : ℂ)) (Q.posL k r 0 (σ i)) (Q.posL k r 0 i)) =
      (capGens (zgCV k r) σ).map (fun gn => genOpR (E := E) gn u) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, Formalism.QuantumDeterminants.Top, genOpR, capGen, zgCV, Q.EH, EabH, cvag_posL_iff, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]
  split_ifs <;> simp

theorem capelli_vector_as_generators : CVAsGens := by
  intro k r E _ _ Y f g
  simp only [Q.CV, Q.capL, qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cvag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem clag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.LZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpL (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpL, capGen, zgB, Q.LZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem left_capelli_as_generators : CapLAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capLft, Q.qmFrev, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [List.map_reverse, List.foldr_reverse, clag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem crag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.RZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpR (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpR, capGen, zgB, Q.RZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem right_capelli_as_generators : CapRAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capR, Q.qmF, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [crag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem colsVm_castSucc {k r m : ℕ} (hm : m + 1 ≤ r) :
    colsVm k r (m + 1) ∘ Fin.castSucc = colsVm k r m := by
  funext j; ext; simp [colsVm]

theorem mirror_chain_expansion_holds : MirrorChainExpansion := by
  intro A _ _ M _ _ k r E La ρ hG m _hm u hR0 hR1 hL
  have hm : m + 2 ≤ r := _hm
  set a := colsVm k r (m + 2) with hadef
  have hav : ∀ l : Fin (m + 2), (a l).val = r + k + 1 + l.val := by
    intro l; have := l.isLt; simp [a, colsVm]; omega
  have hcs : a ∘ Fin.castSucc = colsVm k r (m + 1) := colsVm_castSucc hm
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u

  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have ha2 : a (Fin.last (m + 1)) = esI k r ⟨r - m - 2, by omega⟩ := by
    ext; rw [hav]; simp [esI]; omega

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.castSucc l)) = esI k r ⟨r - 1 - l.val, by omega⟩ := by
      ext; rw [hav]; simp [esI]; omega
    rw [ha1, ha2, hR0 _ ⟨r - 1 - l.val, by omega⟩ (by simp; omega), smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (colsVm k r (m + 1)) (colsVm k r (m + 1)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs, ha2]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (esI k r ⟨r - m - 2, by omega⟩) (colsVm k r m) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [esI]; omega
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [colsVm, hq']; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      ρ • La (qminor E (colsVm k r m) (colsVm k r m) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]

    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = colsVm k r m := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hx : colsVm k r (m + 1) (Fin.last m) = esI k r ⟨r - m - 1, by omega⟩ := by
        ext; simp [colsVm, esI]; omega
      have hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.last m) := by
        rw [hx]; intro h'; have := congrArg Fin.val h'; simp [esI] at this; omega
      rw [tm_offdiag _ _ hne, hx, hL _ ⟨r - m - 1, by omega⟩ (by simp; omega), if_pos rfl]
      rw [colsVm_castSucc (by omega), smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hq := q.isLt
      have hx : colsVm k r (m + 1) (Fin.castSucc q) = esI k r ⟨r - 1 - q.val, by omega⟩ := by
        ext; simp [colsVm, esI]
      have hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.castSucc q) := by
        rw [hx]; intro h'; have := congrArg Fin.val h'; simp [esI] at this; omega
      rw [tm_offdiag _ _ hne, hx, hL _ ⟨r - 1 - q.val, by omega⟩ (by simp; omega), if_neg (by simp; omega),
        zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.last m)) = esI k r ⟨r - m - 1, by omega⟩ := by ext; rw [hav]; simp [esI]; omega
    rw [ha1, ha2, hR1]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.CutMP.TVG
end

section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section WaveJc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r)

def IsWaveJc (Ψ : RadSp P.k P.r z z' π π') : Prop :=
  Ψ ∈ lcSub P.k P.r z z' π π' ∧ ∃ (s : ℂ) (ε : ℝ) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)), 0 < ε ∧ JC.NiceCoef D ε G ∧
    HasCompactSupport G ∧ ∀ y ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      fsv s (y.1 l) • resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2

def waveJc : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Ψ | IsWaveJc P z z' π π' D l Ψ}

end WaveJc

def JSliceGenC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → SliceGood X μ l c Ψ

def JSSob2 : Prop :=
  ∀ (t0 : ℂ) (δ : ℝ), 0 < δ → ∃ K : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f fx fy fxy : ℂ → E),
    (∀ t ∈ Metric.closedBall t0 (2 * δ),
      HasFDerivAt f (Complex.reCLM.smulRight (fx t) + Complex.imCLM.smulRight (fy t)) t) →
    (∀ t ∈ Metric.closedBall t0 (2 * δ), ∃ fyy : E,
      HasFDerivAt fy (Complex.reCLM.smulRight (fxy t) + Complex.imCLM.smulRight fyy) t) →
    ContinuousOn fx (Metric.closedBall t0 (2 * δ)) → ContinuousOn fxy (Metric.closedBall t0 (2 * δ)) →
    ∀ t ∈ Metric.ball t0 δ, ‖f t‖ ^ 2 ≤
      K * ∫ s in Metric.closedBall t0 (2 * δ), (‖f s‖ ^ 2 + ‖fx s‖ ^ 2 + ‖fy s‖ ^ 2 + ‖fxy s‖ ^ 2)

def JSMeas : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (l : Fin r) (c : Fin r → ℂ)
    (Φ Ψ : RadSp k r z z' π π'),
    Measurable (fun q : (ℂ × Cf r l.succ) × Mt k r =>
      B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)))

def SpectralL2Locality : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → ∀ (js : List (Fin 6)) (t0 : ℂ),
      t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε,
        LevelSquareIntegrable μ l.succ (wOp X l js Ψ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤ M

def JSWordNF : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (l : Fin r)
    (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π')), multiplicationOperator Wv (fun c _ => fsv s (c l)) →
    ∀ js : List (Fin 6), ∃ (K : ℕ) (m : Fin K → ℂ → ℂ) (ab : Fin K → List (Fin 6)),
      (∀ i, ContinuousOn (m i) {0}ᶜ) ∧ (∀ i, ∀ j ∈ ab i, j = 0 ∨ j = 3) ∧
      ∀ (Φ : RadSp k r z z' π π') (p : Fin r → ℂ), p ∈ OmX r → ∀ g : Mx k r,
        (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) p g =
          ∑ i, (m i (p l) * fsv s (p l)) • (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g

def JSRadLoc : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 → ∀ (ε : ℝ), 0 < ε → ∀ G : Mx P.k P.r → (Wq →L[ℂ] Wp), JC.NiceCoef D ε G →
    HasCompactSupport G → ∀ Φ : RadSp P.k P.r z z' π π', Φ ∈ lcSub P.k P.r z z' π π' →
    (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) →
    ∀ c ∈ OmX P.r, ∀ js : List (Fin 6), (∀ j ∈ js, j = 0 ∨ j = 3) → ∀ t0 : ℂ, t0 ≠ 0 →
      ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε',
        LevelSquareIntegrable μ l.succ (wOp X l js Φ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Φ) (wOp X l js Φ) c t‖ ≤ M

end Formalism.FourierDecayAlt.P.CutSE
end
end
