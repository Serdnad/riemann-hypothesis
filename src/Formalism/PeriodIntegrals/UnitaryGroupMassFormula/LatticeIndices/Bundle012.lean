module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicReductionImage
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle007
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def StFrameA (p : TypX X) : Prop :=
  ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
    RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} ∧
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ∀ x : K, LocCong X p x ↔
        (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k

theorem reduction_image_of_frame (p : TypX X) (h : StFrameA X p) : LevelReductionImage X hb p := by
  obtain ⟨π, hπ, hker, K, hKc, ψ, hψ, hP, c, hc⟩ := h
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MulAut.conj (glRed π c)⁻¹).toMonoidHom.comp ((glRed π).comp ψ) with hρ₀
  have hval : ∀ x : K, ρ₀ x = (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c := by
    intro x; simp [hρ₀]
  have hk₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p := by
    intro x
    rw [hρ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MonoidHom.comp_apply, glRed_eq_one_iff, hker]
    exact hP x
  have hon : Function.Surjective ρ₀ := by
    have h := (MulEquiv.surjective (MulAut.conj (glRed π c)⁻¹)).comp
      ((glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ)
    exact h
  refine ⟨K, hKc, ρ₀, hon, hk₀, (nuG (ZMod (gOf p)) D.R.rS D.R.k).comap ρ₀, ?_, ?_, 1, ?_⟩
  · ext y
    rw [stImAloc_holds X hb p]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, (hc x).2 ((hval x) ▸ hx)⟩
      rw [← hKc]; exact x.2
    · rintro ⟨hy, hcy⟩
      have hyK : y ∈ K := by rw [← hKc] at hy; exact hy
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      show ρ₀ ⟨y, hyK⟩ ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k
      rw [hval]; exact (hc ⟨y, hyK⟩).1 hcy
  · intro x hx
    show ρ₀ x ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k
    rw [MonoidHom.mem_ker.mp hx]; exact one_mem _
  · rw [Subgroup.map_comap_eq_self_of_surjective hon]
    ext z; simp

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni isUpUni_inv isUpUni_det)

variable {K : Type} [Field K] {r k : ℕ}

def posW (i : Fin k) : Set (Idx r k) := Set.range Sum.inl ∪ wI '' {j | j < i}

def ColW (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ i : Fin k, m *ᵥ Pi.single (wI i) 1 - Pi.single (wI i) 1 ∈
    Submodule.span K ((fun j => Pi.single j (1 : K)) '' posW (r := r) i)

theorem colW_iff (m : Matrix (Idx r k) (Idx r k) K) :
    ColW m ↔ ∀ i : Fin k, ∀ j, j ∉ posW (r := r) i → m j (wI i) = if j = wI i then 1 else 0 := by
  unfold ColW
  refine forall_congr' fun i => ?_
  rw [mem_span_single]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  have e : (m *ᵥ Pi.single (wI i) (1 : K)) j = m j (wI i) := by rw [Matrix.mulVec_single_one]; rfl
  rw [Pi.sub_apply, sub_eq_zero, e, Pi.single_apply]

theorem par_uni_iff_flags (x y : Matrix (Idx r k) (Idx r k) K) (hxy : x * y = 1) (hyx : y * x = 1) :
    Par IsUpUni x ↔ ColC x ∧ ColW x ∧ RowC y := by
  constructor
  · intro hx
    have hu : Par (fun h => IsUnit h.det) x := by
      obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
      exact ⟨h11, h33, h21, h31, h32, h, uni_unit hh, h22⟩
    obtain ⟨hC, hR⟩ := (par_iff_flags x y hxy hyx).1 hu
    refine ⟨hC, ?_, hR⟩
    obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
    rw [colW_iff]
    intro i j hj
    rcases j with a | (j | u) | c
    · exact absurd (Or.inl ⟨a, rfl⟩) hj
    · have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      have hji : ¬ j < i := fun hlt => hj (Or.inr ⟨j, hlt, rfl⟩)
      show x (wI j) (wI i) = _
      rw [show x (wI j) (wI i) = h j i from e]
      by_cases hij : j = i
      · subst hij; simp [hh.2 j, wI]
      · have hlt : i < j := lt_of_le_of_ne (not_lt.1 hji) (Ne.symm hij)
        rw [hh.1 hlt]
        have : (wI j : Idx r k) ≠ wI i := by
          intro e'; apply hij; simpa [wI] using e'
        simp [wI, hij]
    · have e := congrFun (congrFun h22 (Sum.inr u)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at e
      have e' : x (Sum.inr (Sum.inl (Sum.inr u))) (wI i) = 0 := e
      rw [e']; simp [wI]
    · have e := congrFun (congrFun h32 c) (Sum.inl i)
      simp only [b32, Matrix.of_apply, Matrix.zero_apply] at e
      have e' : x (Sum.inr (Sum.inr c)) (wI i) = 0 := e
      rw [e']; simp [wI]
  · rintro ⟨hC, hW, hR⟩
    obtain ⟨h11, h33, h21, h31, h32, h, -, h22⟩ := (par_iff_flags x y hxy hyx).2 ⟨hC, hR⟩
    refine ⟨h11, h33, h21, h31, h32, h, ⟨fun j i hlt => ?_, fun i => ?_⟩, h22⟩
    ·
      have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      rw [← e]
      have hnot : (wI j : Idx r k) ∉ posW (r := r) i := by
        rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
        · simp [wI] at ha
        · have : j' = j := by simpa [wI] using he
          subst this
          exact absurd hlt (not_lt.2 (le_of_lt hj'))
      have := (colW_iff x).1 hW i (wI j) hnot
      rw [show x (wI j) (wI i) = x (Sum.inr (Sum.inl (Sum.inl j))) (Sum.inr (Sum.inl (Sum.inl i))) from rfl] at this
      rw [this]
      have hne : (wI j : Idx r k) ≠ wI i := by
        intro e'; have : j = i := by simpa [wI] using e'
        exact absurd hlt (by rw [this]; exact lt_irrefl _)
      simp [hne]
    · have e := congrFun (congrFun h22 (Sum.inl i)) (Sum.inl i)
      simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
      rw [← e]
      have hnot : (wI i : Idx r k) ∉ posW (r := r) i := by
        rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
        · simp [wI] at ha
        · have : j' = i := by simpa [wI] using he
          subst this
          exact lt_irrefl j' hj'
      have := (colW_iff x).1 hW i (wI i) hnot
      have h1 : x (wI i) (wI i) = 1 := by simpa using this
      exact h1

theorem mem_nuG_iff_flags (g : GL (Idx r k) K) :
    g ∈ nuG K r k ↔ ColFlag (g : Matrix (Idx r k) (Idx r k) K) ∧ ColW (g : Matrix (Idx r k) (Idx r k) K) ∧
      RowFlag ((g⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) := by
  rw [colFlag_iff, rowFlag_iff]
  exact par_uni_iff_flags _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

end MassDataIdxStIm
end
end
