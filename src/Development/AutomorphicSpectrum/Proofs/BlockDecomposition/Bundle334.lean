module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
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
import Mathlib.RingTheory.Henselian
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem locSec_parab_mir_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) :
    LocSec (parab k (two (stdSum h))) (Mir k (i + t)) 1 := by
  set e := GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) with he
  obtain ⟨b, hbc, hb1, hbw⟩ := GlobalTheory.CompanionTheory.BZRes.exists_rowSec (k := k) (Fin.last (i + t))
  obtain ⟨W, hW⟩ : ∃ W : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k,
      ∀ u, W u = (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) :=
    ⟨fun u : GL (Fin (i + t + 1)) k => (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)),
      fun _ => rfl⟩
  have hWc : Continuous W := by
    have hWeq : W = fun u : GL (Fin (i + t + 1)) k => (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) :=
      funext hW
    rw [hWeq]
    exact continuous_pi fun j =>
      (Units.continuous_coe_inv (M := Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)).matrix_elem
        (Fin.last (i + t)) j
  have hone : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
      GlobalTheory.BZMir.eLast k (i + t) := by
    funext j
    by_cases hj : j = Fin.last (i + t)
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · simp [GlobalTheory.BZMir.eLast, Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  have hrow : ∀ q p : GL (Fin (i + t + 1)) k, p ∈ GlobalTheory.BZMir.Mir k (i + t) →
      (↑(q * p)⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
        (↑q⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) := by
    intro q p hp
    have hp' := (GlobalTheory.BZMir.mem_Mir_iff k p⁻¹).1 (Subgroup.inv_mem _ hp)
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply_eq_vecMul, hp']
    simp only [GlobalTheory.BZMir.eLast, Matrix.single_one_vecMul]
    rfl
  have hW1 : W 1 = Pi.single (Fin.last (i + t)) 1 := by
    rw [hW, inv_one, Units.val_one, hone]
    rfl
  have hbW : ContinuousAt (fun u => b (W u)) 1 := by
    refine ContinuousAt.comp (f := W) (g := b) ?_ hWc.continuousAt
    rw [hW1]
    exact hbc
  have hbW1 : b (W 1) = 1 := by rw [hW1, hb1]
  unfold GlobalTheory.CompanionTheory.BZRes.LocSec
  intro OQ hOQ OP hOP
  have h1 : (fun u => (b (W u))⁻¹) ⁻¹' OQ ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    hbW.inv.preimage_mem_nhds (by
      show OQ ∈ 𝓝 (b (W 1))⁻¹
      rw [hbW1, inv_one]
      exact hOQ)
  have h2 : (fun u => b (W u) * u) ⁻¹' OP ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    (hbW.mul continuousAt_id).preimage_mem_nhds (by
      show OP ∈ 𝓝 (b (W 1) * 1)
      rw [hbW1, mul_one]
      exact hOP)
  have h3 : (fun u => W u (Fin.last (i + t))) ⁻¹' {x | x ≠ 0} ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    ((continuous_apply _).comp hWc).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds (by simp [hW1]))
  refine ⟨_, Filter.inter_mem h1 (Filter.inter_mem h2 h3), ?_⟩
  rintro u ⟨hu1, hu2, hu3⟩ hu
  unfold GlobalTheory.CompanionTheory.BZRes.dcos at hu
  obtain ⟨q, hq, p, hp, hqp⟩ := hu
  simp only [one_mul, mul_one] at hqp
  have hbw' := hbw (W u) hu3
  have hWu : W u = (↑q⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) := by
    rw [hW, hqp]
    exact hrow q p hp
  have hbQ : b (W u) ∈ GlobalTheory.SmGL.parab k e := by
    rw [GlobalTheory.SmGL.mem_parab_iff]
    rintro (_ | _) (_ | _) r c hlt
    all_goals first | exact absurd hlt (by decide) | skip
    rw [hbw']
    by_cases hr : e ⟨true, r⟩ = Fin.last (i + t)
    · rw [hr, Matrix.updateRow_self, hWu, ← hr]
      exact (GlobalTheory.SmGL.mem_parab_iff.1 (Subgroup.inv_mem _ hq)) true false r c hlt
    · rw [Matrix.updateRow_ne hr, Matrix.one_apply_ne]
      intro hrc
      exact absurd (e.injective hrc) (by simp)
  have hpP : b (W u) * u ∈ GlobalTheory.BZMir.Mir k (i + t) := by
    rw [GlobalTheory.BZMir.mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, hbw', Matrix.updateRow_self, hW,
      ← Matrix.mul_apply_eq_vecMul, Units.inv_mul, hone]
  refine ⟨(b (W u))⁻¹, Subgroup.inv_mem _ hbQ, hu1, b (W u) * u, hpP, hu2, ?_⟩
  simp

end GlobalTheory.CompanionTheory.BZRes

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wPerm_last {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e, ePG_false_last]

theorem vecMul_wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k))
      (wGL k h : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
  ext c
  rw [Matrix.single_one_vecMul]
  show (1 : Matrix _ _ k) (wPerm h (stdSum h (Sum.inl (Fin.last i)))) c = _
  rw [wPerm_last]
  simp [eLast, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem vecMul_wGL_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k) := by
  rw [← vecMul_wGL (k := k) h, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem mem_parab_of_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k)
    (y : Fin (i + t + 1) → k)
    (hg : (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix _ _ k).updateRow (stdSum h (Sum.inl (Fin.last i))) y) :
    g ∈ parab k (two (stdSum h)) := by
  rw [mem_parab_iff]
  intro a b x z hab
  have hab' : a = true ∧ b = false := by
    clear x z
    revert hab
    cases a <;> cases b <;> decide
  obtain ⟨rfl, rfl⟩ := hab'
  have hne : two (stdSum h) ⟨true, x⟩ ≠ stdSum h (Sum.inl (Fin.last i)) := by
    intro e
    have := (stdSum h).injective e
    simp at this
  have hne2 : two (stdSum h) ⟨true, x⟩ ≠ two (stdSum h) ⟨false, z⟩ := by
    intro e
    have := (two (stdSum h)).injective e
    simp at this
  rw [hg, Matrix.updateRow_ne hne, Matrix.one_apply_ne hne2]

theorem locSec_wGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1) : LocSec (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  intro OQ hOQ OP hOP
  set a₁ := stdSum h (Sum.inl (Fin.last i)) with ha₁
  set w := wGL k h with hw
  obtain ⟨b, hbc, hb1, hb⟩ := exists_rowSec (k := k) a₁
  let y : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k := fun u =>
    vecMul (eLast k (i + t)) (((w * u)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
  have hyc : Continuous y :=
    continuous_const.matrix_vecMul (Units.continuous_val.comp (continuous_const.mul continuous_id).inv)
  have hy1 : y 1 = Pi.single a₁ 1 := by
    simp only [y, mul_one]
    exact vecMul_wGL_inv h
  have hBc : ContinuousAt (fun u => b (y u)) 1 :=
    ContinuousAt.comp (f := y) (g := b) (by rw [hy1]; exact hbc) hyc.continuousAt
  have hB1 : b (y 1) = 1 := by rw [hy1, hb1]
  have hS : ContinuousAt (fun u => (b (y u))⁻¹) 1 := hBc.inv
  have hP : ContinuousAt (fun u => w⁻¹ * b (y u) * w * u) 1 :=
    ((continuousAt_const.mul hBc).mul continuousAt_const).mul continuousAt_id
  have hS' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), (b (y u))⁻¹ ∈ OQ :=
    hS.eventually_mem (by simpa [hB1] using hOQ)
  have hP' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), w⁻¹ * b (y u) * w * u ∈ OP :=
    hP.eventually_mem (by simpa [hB1] using hOP)
  have hne : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), y u a₁ ≠ 0 := by
    have : ContinuousAt (fun u => y u a₁) 1 := ((continuous_apply a₁).comp hyc).continuousAt
    exact this.eventually_ne (by rw [hy1]; simp)
  refine ⟨_, hS'.and (hP'.and hne), ?_⟩
  rintro u ⟨h1, h2, h3⟩ -
  have hBm := hb (y u) h3
  refine ⟨(b (y u))⁻¹, inv_mem (mem_parab_of_row h _ _ hBm), h1, w⁻¹ * b (y u) * w * u, ?_, h2, by group⟩
  show vecMul (eLast k (i + t)) _ = eLast k (i + t)
  have e1 : vecMul (vecMul (eLast k (i + t)) ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k))
      (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = y u := by
    rw [vecMul_wGL_inv h, hBm, Matrix.single_one_vecMul]
    exact Matrix.updateRow_self
  have e2 : vecMul (y u) ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
    simp only [y]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have e3 : ((w⁻¹ * b (y u) * w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
        (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
          ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [e3, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, e1, e2]

end GlobalTheory.CompanionTheory.BZRes

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

theorem eLast_vecMul {k : Type} [Field k] (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :
    vecMul (eLast k n) M = M (Fin.last n) := by
  ext j
  simp [eLast, vecMul, dotProduct, Pi.single_apply]

theorem mem_two_iff {k : Type} [Field k] {r t N : ℕ} (h : r + t = N) (g : GL (Fin N) k) :
    g ∈ parab k (two (stdSum h)) ↔
      ∀ a b : Fin N, r ≤ (a : ℕ) → (b : ℕ) < r → (g : Matrix (Fin N) (Fin N) k) a b = 0 := by
  constructor
  · intro hg a b ha hb
    have hlt : (a : ℕ) - r < t := by have := a.isLt; omega
    have ea : stdSum h (Sum.inr ⟨(a : ℕ) - r, hlt⟩) = a := Fin.ext (by rw [stdSum_inr]; simp only []; omega)
    have eb : stdSum h (Sum.inl ⟨(b : ℕ), hb⟩) = b := Fin.ext (by rw [stdSum_inl])
    have := mem_parab_iff.1 hg true false (⟨(a : ℕ) - r, hlt⟩ : Fin t) (⟨(b : ℕ), hb⟩ : Fin r) (by decide)
    rw [two_true, two_false, ea, eb] at this
    exact this
  · intro hg
    refine mem_parab_iff.2 ?_
    intro x y u v hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
    refine hg _ _ ?_ ?_
    · show r ≤ ((stdSum h (Sum.inr u) : Fin N) : ℕ)
      rw [stdSum_inr]; omega
    · show ((stdSum h (Sum.inl v) : Fin N) : ℕ) < r
      rw [stdSum_inl]; exact v.isLt

theorem mem_dcos_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 ↔
      ∀ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0 := by
  intro k _ _ _ _ i t h ht g
  have hlast : i + 1 ≤ ((Fin.last (i + t) : Fin (i + t + 1)) : ℕ) := by
    rw [Fin.val_last]; omega
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩ a
    have hpi : p⁻¹ ∈ Mir k (i + t) := inv_mem hp
    have hpi' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        eLast k (i + t) := hpi
    have e : (q * 1 * p)⁻¹ = p⁻¹ * q⁻¹ := by simp
    have h1 : vecMul (eLast k (i + t)) ((p⁻¹ * q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        vecMul (eLast k (i + t)) ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
      rw [Units.val_mul, ← vecMul_vecMul, hpi']
    have hrow := (eLast_vecMul (i + t) _).symm.trans (h1.trans (eLast_vecMul (i + t) _))
    rw [e]
    refine (congrFun hrow _).trans ((mem_two_iff h _).1 (inv_mem hq) _ _ hlast ?_)
    rw [stdSum_inl]; exact a.isLt
  · intro hy
    classical
    let y : Fin (i + t + 1) → k :=
      ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t))
    have hyg : vecMul y (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
      have : y = vecMul (eLast k (i + t))
          ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := (eLast_vecMul _ _).symm
      rw [this, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
    have hfirst : ∀ c : Fin (i + t + 1), (c : ℕ) < i + 1 → y c = 0 := by
      intro c hc
      have e : stdSum h (Sum.inl ⟨(c : ℕ), hc⟩) = c := Fin.ext (by rw [stdSum_inl])
      have := hy ⟨(c : ℕ), hc⟩
      rw [e] at this
      exact this
    obtain ⟨a₀, ha₀⟩ : ∃ c, y c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : y = 0 := funext hcon
      rw [h0, zero_vecMul] at hyg
      have := congrFun hyg (Fin.last (i + t))
      simp [eLast] at this
    have hblock : i + 1 ≤ (a₀ : ℕ) := by
      by_contra hlt
      exact ha₀ (hfirst a₀ (by omega))
    let σ : Equiv.Perm (Fin (i + t + 1)) := Equiv.swap a₀ (Fin.last (i + t))
    have hσ : ∀ r : Fin (i + t + 1), i + 1 ≤ (r : ℕ) → i + 1 ≤ (σ r : ℕ) := by
      intro r hr
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · exact hlast
      · exact hblock
      · exact hr
    let B : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
      ((1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).updateRow a₀ y).submatrix σ id
    have hdet : B.det ≠ 0 := by
      simp only [B]
      rw [Matrix.det_permute, det_updateRow_one]
      refine mul_ne_zero ?_ ha₀
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
    let b : GL (Fin (i + t + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet
    have hb : (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = B := rfl
    have hbQ : b ∈ parab k (two (stdSum h)) := by
      refine (mem_two_iff h b).2 fun r c hr hc => ?_
      rw [hb]
      simp only [B, submatrix_apply, id]
      by_cases e : σ r = a₀
      · rw [e, updateRow_self]
        exact hfirst c hc
      · rw [updateRow_ne e, one_apply_ne]
        intro e2
        have := hσ r hr
        rw [e2] at this
        omega
    refine ⟨b⁻¹, inv_mem hbQ, b * g, ?_, by simp⟩
    show vecMul (eLast k (i + t)) ((b * g : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)
    have hB : B (Fin.last (i + t)) = y := by
      funext c
      simp [B, σ]
    rw [Units.val_mul, ← vecMul_vecMul, eLast_vecMul, hb, hB]
    exact hyg

end GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem wGL_conj_apply (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * g * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e1 : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  have e2 : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  rw [Units.val_mul, Units.val_mul, e1, e2]
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (x : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) x) = ePG i t x := by
  simp [wPerm]

theorem mem_HPG_iff_conj_mem_parab (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (p : Mir k (i + t)) :
    p ∈ HPG k i t ↔ wGL k h * (p : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h)) := by
  show (p : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t) ↔ _
  rw [mem_parab_iff, mem_parab_iff]
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun x => forall_congr' fun y => ?_
  rw [wGL_conj_apply, wPerm_two, wPerm_two]

end GlobalTheory.CompanionTheory.BZRes
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibFin

theorem finite_image_of_rightInvariant {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) (hS : IsOpen (S : Set G)) {K : Set G} (hK : IsCompact K) (F : G → X)
    (hF : ∀ g, ∀ s ∈ S, F (g * s) = F g) : (F '' K).Finite := by
  have hcover : K ⊆ ⋃ g : K, (fun x => (g : G) * x) '' (S : Set G) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, 1, S.one_mem, mul_one x⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun g : K => (fun x => (g : G) * x) '' (S : Set G))
    (fun g => (Homeomorph.mulLeft (g : G)).isOpenMap _ hS) hcover
  apply (T.finite_toSet.image (fun g : K => F g)).subset
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (hT hx)
  obtain ⟨s, hs, rfl⟩ := hxg
  exact ⟨g, hg, (hF g s hs).symm⟩

theorem finite_fibV_image (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) :
    ((fun κ : GL (Fin (i + t)) k => fibV f κ) ''
      (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
  have hst : IsOpen {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} :=
    GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd (GlobalTheory.BZMir.Leib.HPG k i t)
      (GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ) f
  let H : Subgroup (GL (Fin (i + t)) k) :=
    { carrier := {g | ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * g) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ}
      mul_mem' := by
        intro a b ha hb κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        have hb' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * b) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := hb
        rw [← mul_assoc, hb', ha']
      one_mem' := by
        intro κ
        rw [mul_one]
      inv_mem' := by
        intro a ha κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        rw [← ha' (κ * a⁻¹), mul_assoc, inv_mul_cancel, mul_one] }
  have hcont := GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k (i + t)
  have hO := hcont.isOpen_preimage _ hst
  have hone : (1 : GL (Fin (i + t)) k) ∈ GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} := by
    show GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) 1) f = f
    rw [map_one, map_one]
    rfl
  have hsub : GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} ⊆ (H : Set _) := by
    intro g hg κ
    have hg' : GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) g) f = f := hg
    funext v
    have h1 := congrArg (fun φ => GlobalTheory.CompanionTheory.BZPsiPG.fibV φ κ v) hg'
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.fibV, map_mul, ← mul_assoc] at h1 ⊢
    exact h1
  have hHopen : IsOpen (H : Set (GL (Fin (i + t)) k)) :=
    Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds hone) hsub)
  have hF : ∀ g : GL (Fin (i + t)) k, ∀ s ∈ H,
      GlobalTheory.CompanionTheory.BZPsiPG.fibV f (g * s) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f g := fun g s hs => hs g
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_image_of_rightInvariant H hHopen GlobalTheory.SplitFlip.isCompact_KO _ hF

end GlobalTheory.CompanionTheory.BZPsiPG.FibFin
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mirabolic_extension_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A B C : MRep k n), MExt A B C → Ses A.ρ B.ρ C.ρ := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext | exact GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext <;> assumption)
end
