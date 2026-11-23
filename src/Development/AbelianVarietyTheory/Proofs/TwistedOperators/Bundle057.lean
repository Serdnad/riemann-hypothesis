module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.CutRow

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

end GlobalTheory.RootEx.CutRow


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.RootEx.opE_cut_om_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (χ : (n' → k) → ℂ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : GL n k), ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c p ⊓ _root_.GlobalTheory.RootEx.N k n c (p + 1), _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ y) = (((_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * (ψ (-_root_.GlobalTheory.RootEx.simpleSum u) : ℂ)) • _root_.GlobalTheory.SplitWeil.om μ 1 x (_root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * Φ y)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ ν _ μ χ Φ x u hu
  obtain ⟨huP, huP1⟩ := Subgroup.mem_inf.mp hu
  set cut : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ := fun y =>
    ∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0 with hcut
  have hlevi : ∀ (g : GL n k) (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      cut (((_root_.GlobalTheory.RootEx.embX c g : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * y) = cut y := by
    intro g y
    simp only [hcut, _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.OpELevi.left_inr]
  have hgen : _root_.GlobalTheory.RootEx.InN p u⁻¹ :=
    _root_.GlobalTheory.RootEx.Model.mem_N_iff.mp (inv_mem huP)
  have hunip : ∀ (x₀ : Matrix n n' k) (e : { rs // _root_.GlobalTheory.RootEx.Free (p + 1) rs } → k),
      cut (((u⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x₀ e) =
        cut (_root_.GlobalTheory.RootEx.affPt (p + 1) x₀ e) := by
    intro x₀ e
    simp only [hcut]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · congr 1
      funext s
      rw [_root_.GlobalTheory.RootEx.TargetUnip.mul_apply_of_inN hgen, Finset.sum_eq_zero, add_zero]
      intro r _
      split_ifs with hlt
      · cases r with
        | inl i =>
          simp [_root_.GlobalTheory.RootEx.lev] at hlt
          omega
        | inr i =>
          simp [_root_.GlobalTheory.RootEx.lev] at hlt
          rw [_root_.GlobalTheory.RootEx.TargetUnip.affPt_of_not_free]
          · simp [_root_.GlobalTheory.RootEx.basePt]
          · simp [_root_.GlobalTheory.RootEx.Free]
            omega
      · rfl
    · rfl
  have hmul : _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ =
      _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) (_root_.GlobalTheory.SplitWeil.om μ 1 u Φ) := by
    have h := _root_.GlobalTheory.SplitWeil.Model.om_mul μ 1 1 (_root_.GlobalTheory.RootEx.embX c x) u Φ
    rwa [one_mul] at h
  have hcomm : ∀ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ,
      (fun y => cut y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) Ψ y) =
        _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) (fun y => cut y * Ψ y) := by
    intro Ψ
    funext y
    simp only [_root_.GlobalTheory.SplitWeil.om, Units.val_one, Matrix.mul_one, ← map_inv, hlevi]
    ring
  have hcut_unip : _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => cut y * _root_.GlobalTheory.SplitWeil.om μ 1 u Φ y) =
      _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (_root_.GlobalTheory.SplitWeil.om μ 1 u (fun y => cut y * Φ y)) := by
    funext x₀
    unfold _root_.GlobalTheory.RootEx.opE
    congr 1
    funext e
    simp only [_root_.GlobalTheory.SplitWeil.om, Units.val_one, Matrix.mul_one, hunip]
    ring
  rw [hmul, hcomm, (_root_.GlobalTheory.RootEx.opE_om_embX k n n' c (p + 1) (by omega) (by omega) ψ ν μ _).1 x,
    hcut_unip, _root_.GlobalTheory.RootEx.opE_om_target_unipotent k n n' c (p + 1) (by omega) (by omega) ψ ν μ _ u huP1]
  funext y
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul]
  ring
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.rootExchangeUnipotent_haar_and_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure], IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) ∧ IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) ∧ (volN ν n c p).IsHaarMeasure ∧ (volN ν n c p).IsMulRightInvariant ∧ ∀ (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) = (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) • ∫ u : N k n c p, f u ∂(volN ν n c p) := by
  first | exact @GlobalTheory.RootEx.VolN.volN_haar_and_modulus | exact GlobalTheory.RootEx.VolN.volN_haar_and_modulus | (intros; apply GlobalTheory.RootEx.VolN.volN_haar_and_modulus <;> assumption)
end

section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology Matrix
open scoped ENNReal

namespace GlobalTheory.SmGL.UnipHaar

section Algebra

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)

theorem det_rmat_unip (u : unipRad R e) : (rmat e ((u : GL n R) : Matrix n n R)).det = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 u.2
  rw [← det_transpose, det_of_blocks (rmat e _)ᵀ (fun p => blk e p.1.2) ?_
    (fun a => {j : n // blk e j < a}) (fun _ => 1) (colEquiv e) ?_]
  · simp
  · intro p q h
    have h3 : ((u : GL n R) : Matrix n n R).BlockTriangular (blk e) := h1
    simp [rmat, h3 h]
  · intro a x y
    exact if_congr (eq_comm.trans Subtype.ext_iff.symm) (h2 a x.1 y.1) rfl

theorem unipEquiv_mul_right (u : unipRad R e) (x : Idx e → R) :
    unipEquiv e ((unipEquiv e).symm x * u) =
      unipEquiv e u + (rmat e ((u : GL n R) : Matrix n n R)).mulVec x := by
  rw [← ent_mat_mul]
  show ent e ((1 + mat e x) * ((u : GL n R) : Matrix n n R)) = _
  rw [add_mul, one_mul]
  rfl

end Algebra

section Measure

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem isMulRightInvariant_map :
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν)).IsMulRightInvariant := by
  haveI := secondCountable k
  haveI := t2Space k
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  refine ⟨fun u => ?_⟩
  have hm : Measurable (rmat e ((u : GL n k) : Matrix n n k)).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have h1 := WeilM.smul_map_mulVec_pi ν _ 1 (det_rmat_unip e u).symm
  rw [map_one, ENNReal.coe_one, one_smul] at h1
  have h2 : (· * u) ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ ((unipEquiv e u + ·) ∘
      (rmat e ((u : GL n k) : Matrix n n k)).mulVec) :=
    funext fun x => (unipEquiv e).eq_symm_apply.2 (unipEquiv_mul_right e u x)
  rw [Measure.map_map (measurable_mul_const u) hΦ, h2,
    ← Measure.map_map hΦ ((measurable_const_add _).comp hm),
    ← Measure.map_map (measurable_const_add _) hm, h1, map_add_left_eq_self]

end Measure

theorem haar_isMulRightInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] (μ : Measure (unipRad k e)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e _ _ μ _
  borelize k
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (unipRad k e) := (unipHomeo e).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k e) := (unipHomeo e).secondCountableTopology
  haveI := isHaarMeasure_map e (Measure.addHaar : Measure k)
  haveI := isMulRightInvariant_map e (Measure.addHaar : Measure k)
  rw [Measure.isMulLeftInvariant_eq_smul μ
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => (Measure.addHaar : Measure k)))]
  infer_instance

end GlobalTheory.SmGL.UnipHaar
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.MaschkeForms

open Representation

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_isAtom {π : Representation ℂ G V} {U : Subrepresentation π}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  have hne : U.toSubmodule ≠ ⊥ := fun h => hU.1 (Subrepresentation.toSubmodule_injective h)
  have hnt : Nontrivial (Subrepresentation U.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h' : (⊥ : Submodule ℂ U.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← U.toSubmodule.map_subtype_top, ← h', Submodule.map_bot]
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation π := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, S.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hT : T ≤ U := U.toSubmodule.map_subtype_le S.toSubmodule
  have hinj := Submodule.map_injective_of_injective U.toSubmodule.injective_subtype
  rcases hU.le_iff.mp hT with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans (Submodule.map_bot _).symm
  · right
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans U.toSubmodule.map_subtype_top.symm

end GlobalTheory.MaschkeForms
end
end
