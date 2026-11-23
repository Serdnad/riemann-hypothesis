module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle181
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle201
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
public import GroundTheory.AutomorphicForms.GeometricLemmaModular
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
import GroundTheory.AutomorphicForms.Bundle002
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellSizes

theorem card_blk_fiber {α : Type} {N : ℕ} {m : α → Type} [DecidableEq α] [∀ i, Fintype (m i)]
    (e : (Σ i, m i) ≃ Fin N) (i : α) :
    (Finset.univ.filter fun x : Fin N => blk e x = i).card = Fintype.card (m i) := by
  have h : (Finset.univ.filter fun x : Fin N => blk e x = i) =
      (Finset.univ : Finset (m i)).map
        ⟨fun y => e ⟨i, y⟩, fun a b hab => by simpa using e.injective hab⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨(e.symm x).2, e.apply_symm_apply x⟩
    · rintro ⟨y, rfl⟩
      exact blk_apply e i y
  rw [h, Finset.card_map, Finset.card_univ]

theorem sizes_sum : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), (∀ i, ∑ j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m i)) ∧ ∀ j, ∑ i, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m' j) := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' w
  constructor
  · intro i
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e x = i)
      (t := (Finset.univ : Finset β')) (f := fun x => blk e' (w.symm x))
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    rw [← h]
    exact card_blk_fiber e i
  · intro j
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j)
      (t := (Finset.univ : Finset α)) (f := fun x => blk e x)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    have h2 : (Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e' y = j).card :=
      Finset.card_equiv w.symm (by simp)
    simp only [and_comm (a := blk e _ = _)]
    rw [← h, h2]
    exact card_blk_fiber e' j

end GlobalTheory.CompanionTheory.CellSizes
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.Cell

theorem exists_block_equiv_of_cells {X α β : Type} {m : α → Type} (e : (Σ i, m i) ≃ X) (b : X → β)
    (c : α → β → ℕ) (E : ∀ i j, {x : X // (e.symm x).1 = i ∧ b x = j} ≃ Fin (c i j)) :
    ∃ f : ∀ i, (Σ j, Fin (c i j)) ≃ m i,
      ∀ i j t, e ⟨i, f i ⟨j, t⟩⟩ = ((E i j).symm t).1 := by
  have hι : ∀ i, Function.Bijective
      (fun y : m i => (⟨e ⟨i, y⟩, by simp⟩ : {x : X // (e.symm x).1 = i})) := by
    intro i
    constructor
    · intro a a' h
      have h1 : e ⟨i, a⟩ = e ⟨i, a'⟩ := congrArg Subtype.val h
      exact sigma_mk_injective (e.injective h1)
    · rintro ⟨x, hx⟩
      obtain ⟨⟨k, y⟩, rfl⟩ := e.surjective x
      simp only [Equiv.symm_apply_apply] at hx
      subst hx
      exact ⟨y, rfl⟩
  have hF : ∀ i, Function.Bijective
      (fun p : Σ j, Fin (c i j) =>
        (⟨((E i p.1).symm p.2).1, ((E i p.1).symm p.2).2.1⟩ : {x : X // (e.symm x).1 = i})) := by
    intro i
    constructor
    · rintro ⟨j, t⟩ ⟨j', t'⟩ h
      have h1 : ((E i j).symm t).1 = ((E i j').symm t').1 := congrArg Subtype.val h
      have hj : j = j' := by
        calc j = b ((E i j).symm t).1 := ((E i j).symm t).2.2.symm
          _ = b ((E i j').symm t').1 := by rw [h1]
          _ = j' := ((E i j').symm t').2.2
      subst hj
      have ht : t = t' := (E i j).symm.injective (Subtype.ext h1)
      subst ht
      rfl
    · rintro ⟨x, hx⟩
      refine ⟨⟨b x, E i (b x) ⟨x, hx, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      simp
  refine ⟨fun i => (Equiv.ofBijective _ (hF i)).trans (Equiv.ofBijective _ (hι i)).symm, ?_⟩
  intro i j t
  have key := (Equiv.ofBijective _ (hι i)).apply_symm_apply (Equiv.ofBijective _ (hF i) ⟨j, t⟩)
  exact congrArg Subtype.val key

theorem cell_row_column_partitions :
    ∀ {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} {m' : β' → Type} (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), ∀ i j (t : Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩ := by
  intro α β' _ _ _ _ N m m' e e' w
  let E : ∀ i j, {x : Fin N // (e.symm x).1 = i ∧ blk e' (w.symm x) = j} ≃
      Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) :=
    fun i j => (Equiv.subtypeEquivRight (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩)).trans
      (Finset.equivFin _)
  let E' : ∀ j i, {x : Fin N // ((e'.trans w).symm x).1 = j ∧ blk e x = i} ≃
      Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) :=
    fun j i => (Equiv.subtypeEquivRight (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h.2, h.1⟩, fun h => ⟨h.2.2, h.2.1⟩⟩)).trans
      (Finset.equivFin _)
  obtain ⟨f, hf⟩ := exists_block_equiv_of_cells e (fun x => blk e' (w.symm x))
    (fun i j => (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) E
  obtain ⟨g, hg⟩ := exists_block_equiv_of_cells (e'.trans w) (fun x => blk e x)
    (fun j i => (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) E'
  refine ⟨f, g, ?_⟩
  intro i j t
  rw [hf i j t]
  exact hg j i t

end GlobalTheory.CompanionTheory.Cell
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.Twist

theorem exists_nat_labelling_blk : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  intro α _ _ N m _ _ e
  let o := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨fun x => (o (blk e x)).val, fun x y => ?_⟩
  exact Fin.lt_def.symm.trans (OrderIso.lt_iff_lt o)

end GlobalTheory.CompanionTheory.Twist
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviIso

theorem leviEquiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ
  have hz : ∀ x : GL (Fin N) k, x ∈ levi k N β → ∀ i j : Fin N, blk e i ≠ blk e j →
      (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro x hx i j hij
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper] at hx
    rcases lt_or_gt_of_ne hij with h | h
    · exact hx.2 (OrderDual.toDual_lt_toDual.mpr ((hβ i j).2 h))
    · exact hx.1 ((hβ j i).2 h)
  have hzE : ∀ (g : Levi k m) (i j : Fin N), blk e i ≠ blk e j →
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro g i j hij
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    have hab : a ≠ b := by simpa [blk] using hij
    exact leviEmb_apply_ne k e g hab i' j'
  have hent : ∀ (g : Levi k m) (a : α) (i j : m a),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
        ((g a : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    exact leviEmb_apply_same k e g a i j
  have hmem : ∀ g : Levi k m, leviEmb k e g ∈ levi k N β := by
    intro g
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    constructor
    · intro i j h
      exact hzE g i j ((hβ j i).1 h).ne'
    · intro i j h
      exact hzE g i j ((hβ i j).1 (OrderDual.toDual_lt_toDual.1 h)).ne
  have hkey : ∀ x : GL (Fin N) k, x ∈ levi k N β →
      Matrix.blockDiagonal' (Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e)) =
        (x : Matrix (Fin N) (Fin N) k).submatrix e e := by
    intro x hx
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases hab : a = b
    · subst hab
      rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab, Matrix.submatrix_apply,
        hz x hx _ _ (by simpa [blk] using hab)]
  have hmul : ∀ x y : GL (Fin N) k, x ∈ levi k N β → y ∈ levi k N β → ∀ a : α,
      Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e) a *
          Matrix.blockDiag' ((y : Matrix (Fin N) (Fin N) k).submatrix e e) a =
        Matrix.blockDiag' (((x * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a := by
    intro x y hx hy a
    rw [Units.val_mul, ← Matrix.submatrix_mul_equiv (x : Matrix (Fin N) (Fin N) k)
      (y : Matrix (Fin N) (Fin N) k) e e e, ← hkey x hx, ← hkey y hy]
    simp only [← Matrix.blockDiagonal'_mul, Matrix.blockDiag'_blockDiagonal']
  have hLE : Continuous (leviEmb k e) := continuous_leviEmb k e
  let ψ : levi k N β → Levi k m := fun x => (fun a =>
      ⟨Matrix.blockDiag' (((x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        Matrix.blockDiag' ((((x : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        by rw [hmul _ _ x.2 (inv_mem x.2), mul_inv_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl,
        by rw [hmul _ _ (inv_mem x.2) x.2, inv_mul_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl⟩ : ∀ a, GL (m a) k)
  refine ⟨{
      toFun := fun g => ⟨leviEmb k e g, hmem g⟩
      invFun := ψ
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }, fun g => rfl, ?_, ?_⟩
  · intro g
    refine funext fun a => ?_
    apply Units.ext
    ext i j
    simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    exact hent g a i j
  · intro x
    apply Subtype.ext
    apply Units.ext
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      dsimp only
      rw [hent]
      simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    · have h' : blk e (e ⟨a, i'⟩) ≠ blk e (e ⟨b, j'⟩) := by simpa [blk] using hab
      dsimp only
      rw [hzE _ _ _ h', hz _ x.2 _ _ h']
  · intro g h
    apply Subtype.ext
    exact map_mul (leviEmb k e) g h
  · exact hLE.subtype_mk hmem
  · change Continuous ψ
    refine continuous_pi fun a => ?_
    rw [Units.continuous_iff]
    constructor
    · refine continuous_matrix fun i j => ?_
      simp only [Function.comp_apply, ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · refine continuous_matrix fun i j => ?_
      simp only [ψ, Units.inv_mk, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _

end GlobalTheory.CompanionTheory.LeviIso
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviCont

theorem levi_iso_homeo (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (φ : Levi k m ≃* levi k N β) (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) : Continuous φ ∧ Continuous φ.symm := by
  have hcont : ∀ (Ψ : Levi k m → GL (Fin N) k) (ρ : ∀ a, GL (m a) k → Matrix (m a) (m a) k),
      (∀ a, Continuous (ρ a)) →
      (∀ g a (i j : m a), (Ψ g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) = ρ a (g a) i j) →
      (∀ g a b (i : m a) (j : m b), a ≠ b →
        (Ψ g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0) →
      Continuous fun g => (Ψ g : Matrix (Fin N) (Fin N) k) := by
    intro Ψ ρ hρ hs hn
    refine continuous_pi fun r => continuous_pi fun s => ?_
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective r
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective s
    by_cases hab : a = b
    · subst hab
      simp_rw [hs]
      exact (continuous_apply j).comp ((continuous_apply i).comp ((hρ a).comp (continuous_apply a)))
    · simp_rw [hn _ _ _ _ _ hab]
      exact continuous_const
  have hinv : ∀ g, ((φ g : levi k N β) : GL (Fin N) k)⁻¹ = leviEmb k e g⁻¹ := by
    intro g
    rw [← hφ, map_inv, Subgroup.coe_inv]
  have hs1 : ∀ g a (i j : m a), ((φ g : levi k N β) : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (g a : Matrix (m a) (m a) k) i j := by
    intro g a i j
    rw [hφ]
    exact leviEmb_apply_same k e g a i j
  have hs2 : ∀ g a (i j : m a),
      (((φ g : levi k N β) : GL (Fin N) k)⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (((g a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    rw [hinv]
    exact leviEmb_apply_same k e g⁻¹ a i j
  have hn1 : ∀ g a b (i : m a) (j : m b), a ≠ b →
      ((φ g : levi k N β) : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b i j hab
    rw [hφ]
    exact leviEmb_apply_ne k e g hab i j
  have hn2 : ∀ g a b (i : m a) (j : m b), a ≠ b →
      (((φ g : levi k N β) : GL (Fin N) k)⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b i j hab
    rw [hinv]
    exact leviEmb_apply_ne k e g⁻¹ hab i j
  refine ⟨?_, ?_⟩
  · refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact hcont (fun g => (φ g : GL (Fin N) k)) (fun a u => (u : Matrix (m a) (m a) k))
        (fun a => Units.continuous_val) hs1 hn1
    · exact hcont (fun g => ((φ g : GL (Fin N) k))⁻¹) (fun a u => ((u⁻¹ : GL (m a) k) : Matrix (m a) (m a) k))
        (fun a => Units.continuous_coe_inv) hs2 hn2
  · refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      have h : ∀ h : levi k N β, ((φ.symm h a : GL (m a) k) : Matrix (m a) (m a) k) i j =
          ((h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
        intro h
        rw [← hs1, MulEquiv.apply_symm_apply]
      simp_rw [Function.comp_apply, h]
      exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).comp continuous_subtype_val))
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      have h : ∀ h : levi k N β, (((φ.symm h a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k) i j =
          (((h : GL (Fin N) k))⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
        intro h
        rw [← hs2, MulEquiv.apply_symm_apply]
      simp_rw [h]
      exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_coe_inv (M := Matrix (Fin N) (Fin N) k)).comp continuous_subtype_val))

end GlobalTheory.CompanionTheory.LeviCont
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmGLBridge

theorem leviProj_found_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β), φ (leviProj k e ⟨p, h1⟩) = GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ p h1 h2
  have hblk : ∀ x y, β x = β y ↔ blk e x = blk e y := by
    intro x y
    constructor
    · intro h
      have h3 := (hβ x y).not.1 (by omega)
      have h4 := (hβ y x).not.1 (by omega)
      exact le_antisymm (not_lt.1 h4) (not_lt.1 h3)
    · intro h
      have h3 := (hβ x y).not.2 (by rw [h]; exact lt_irrefl _)
      have h4 := (hβ y x).not.2 (by rw [h]; exact lt_irrefl _)
      omega
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro x y
  rw [hφ]
  rw [show ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ : levi k N β) : GL (Fin N) k).val x y = _ from GroundTheory.Automorphic.Parabolic.leviProj_apply _ x y]
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases hab : a = b
  · subst hab
    rw [if_pos ((hblk _ _).2 (by simp))]
    have := leviEmb_apply_same k e (leviProj k e ⟨p, h1⟩) a i j
    rw [this, leviProj_apply]
  · rw [if_neg (fun h => hab (by simpa using (hblk _ _).1 h))]
    exact leviEmb_apply_ne k e _ hab i j

end GlobalTheory.CompanionTheory.SmGLBridge
end

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing


theorem _root_.GlobalTheory.T.omega_operator_commutes_infinite_gl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    ∀ y : GL (Fin a) (Cinf E),
      GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt | exact GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt | (intros; apply GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem Rd_ofReal_eq {n : ℕ} {Ψ : Mat n → ℝ} (hΨ : ContDiffOn ℝ ∞ Ψ (GLs n)) (X : Mat n)
    {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (Ψ z : ℂ)) y = ((Rr X Ψ y : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ Ψ y :=
    ((hΨ y hy).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
  have h : HasFDerivAt (fun z => (Ψ z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Ψ y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hd.hasFDerivAt
  simp only [Rd, Rr, h.fderiv]
  rfl

theorem integral_Rr_eq_zero : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  intro hR n _ _ μ _ Ψ hΨ hc X
  have hf : ContDiffOn ℝ ∞ (fun z => (Ψ z : ℂ)) (GLs n) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hΨ
  have hcf : Cpt (fun z => (Ψ z : ℂ)) := by
    obtain ⟨R, hR'⟩ := hc
    exact ⟨R, fun y hy h => by simp [hR' y hy h]⟩
  have h0 := (hR n).2.2 μ ℂ (fun z => (Ψ z : ℂ)) hf hcf X
  have h1 : (fun y : G n => Rd X (fun z => (Ψ z : ℂ)) y.val) =
      fun y : G n => ((Rr X Ψ y.val : ℝ) : ℂ) :=
    funext fun y => Rd_ofReal_eq hΨ X (val_mem_GLs y)
  rw [h1, integral_complex_ofReal] at h0
  exact Complex.ofReal_eq_zero.1 h0

end GlobalTheory.CompanionTheory.WaveSpd
end

end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.block_count_reindex_equivs : ∀ {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} {m' : β' → Type} (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), ∀ i j (t : Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Cell.cell_row_column_partitions | exact GlobalTheory.CompanionTheory.Cell.cell_row_column_partitions | (intros; apply GlobalTheory.CompanionTheory.Cell.cell_row_column_partitions <;> assumption)

end
end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.exists_strict_block_order : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  first | exact @GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk | exact GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk | (intros; apply GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk <;> assumption)

end
end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.permutation_block_counts : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), (∀ i, ∑ j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m i)) ∧ ∀ j, ∑ i, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m' j) := by
  first | exact @GlobalTheory.CompanionTheory.CellSizes.sizes_sum | exact GlobalTheory.CompanionTheory.CellSizes.sizes_sum | (intros; apply GlobalTheory.CompanionTheory.CellSizes.sizes_sum <;> assumption)

end
end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.levi_block_homeomorph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  first | exact @GlobalTheory.CompanionTheory.LeviIso.leviEquiv | exact GlobalTheory.CompanionTheory.LeviIso.leviEquiv | (intros; apply GlobalTheory.CompanionTheory.LeviIso.leviEquiv <;> assumption)

end
end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.levi_equiv_continuous : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → Continuous φ ∧ Continuous φ.symm := by
  first | exact @GlobalTheory.CompanionTheory.LeviCont.levi_iso_homeo | exact GlobalTheory.CompanionTheory.LeviCont.levi_iso_homeo | (intros; apply GlobalTheory.CompanionTheory.LeviCont.levi_iso_homeo <;> assumption)

end
end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.parabolic_levi_projection : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β), φ (leviProj k e ⟨p, h1⟩) = GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ := by
  first | exact @GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq | exact GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq | (intros; apply GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq <;> assumption)

end
end
