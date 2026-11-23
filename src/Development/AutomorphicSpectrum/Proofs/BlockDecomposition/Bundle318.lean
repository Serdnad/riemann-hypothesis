module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle300
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaProj

theorem blockIndex_succ_false (m j : ℕ) (a : Fin m) :
    eGP m (j + 1) ⟨false, a⟩ = (Fin.castSucc (eGP m j ⟨false, a⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]

theorem blockIndex_succ_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = (Fin.castSucc (eGP m j ⟨true, b⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]
    | (simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]; omega)

theorem blockIndex_succ_true_last (m j : ℕ) :
    eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = (Fin.last (m + j + 1) : Fin (m + j + 1 + 1)) := by
  exact GlobalTheory.BZMir.Leib.blockIndex_true_last m (j + 1)

theorem glEmbMat_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem gpProj_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : GlobalTheory.BZMir.Leib.MirabolicParabolic k m j)
    (hh : embedding₂ k (m + j) y ∈ GlobalTheory.BZMir.Leib.MirabolicParabolic k m (j + 1)),
    GlobalTheory.BZMir.Leib.gpProj k m (j + 1) ⟨_, hh⟩ =
      ((GlobalTheory.BZMir.Leib.gpProj k m j y).1,
        embedding₂ k j (GlobalTheory.BZMir.Leib.gpProj k m j y).2) := by
  intro k _ _ _ _ m j y hh
  refine Prod.ext ?_ ?_
  · refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) false a b).trans
      (Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
        (GlobalTheory.BZMir.Leib.hgpIncl k m j y) false a b).symm)
    rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j a, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j b]
    exact GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
      ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _
  · apply Subtype.ext
    refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) true a b).trans ?_
    have hR := fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j y) true a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k)).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) b).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) a).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _).trans
          ((hR a b).symm.trans
            (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (j + 1)
              ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
                Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b).symm)

end GlobalTheory.CompanionTheory.LeibPhi.IotaProj

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Emb

open GlobalTheory.CompanionTheory.BZPhiPhi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mirProj_iotaM (n : ℕ) (y : Mir k n) :
    mirabolicProjection k (n + 1) (embedding₂ k n y) = (y : GL (Fin (n + 1)) k) := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k (n + 1) (GlobalTheory.BZMir.glEmbMat k (n + 1) ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) i j = _
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem iotaM_mem_Q (n : ℕ) (y : Mir k n) : embedding₂ k n y ∈ Q k n := by
  show mirabolicProjection k (n + 1) (embedding₂ k n y) ∈ Mir k n
  rw [mirProj_iotaM]
  exact y.2

theorem mem_mirabolicParabolic_of_iotaM_mem (m j : ℕ) (p : Mir k (m + j))
    (h : embedding₂ k (m + j) p ∈ MirabolicParabolic k m (j + 1)) : p ∈ MirabolicParabolic k m j := by
  have h1 := (GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic k m (j + 1) (embedding₂ k (m + j) p)).1 h
  have e : mirabolicProjection k (m + (j + 1)) (embedding₂ k (m + j) p) = (p : GL (Fin (m + j + 1)) k) :=
    mirProj_iotaM (m + j) p
  rw [e] at h1
  exact h1

theorem mem_mirabolicParabolic_of_mirabolicProj_eq_one (m j : ℕ) (w : Mir k (m + j)) (h : mirabolicProjection k (m + j) w = 1) :
    w ∈ MirabolicParabolic k m j := by
  rw [GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic, h]
  exact one_mem _

theorem rowQ_eq_zero_of_mem_HGP (m j : ℕ) (h : Mir k (m + (j + 1))) (hh : h ∈ MirabolicParabolic k m (j + 1))
    (i : Fin (m + j + 1)) (hi : (i : ℕ) < m) : rowQ k (m + j) h i = 0 := by
  have h1 := (mem_mirabolicParabolic_iff k m (j + 1) h).1 hh ⟨j, by omega⟩ ⟨i, hi⟩
  have e1 : eGP m (j + 1) ⟨true, ⟨j, by omega⟩⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  have e2 : eGP m (j + 1) ⟨false, ⟨i, hi⟩⟩ = Fin.castSucc i :=
    Fin.ext (by rw [blockIndex_false_val]; simp)
  rw [e1, e2] at h1
  exact h1

theorem rowEl_mem_HGP (m j : ℕ) (r : Fin (m + j + 1) → k) (hr : (rowMat (m + j) r).det ≠ 0)
    (h0 : ∀ i : Fin (m + j + 1), (i : ℕ) < m → r i = 0) :
    (rowEl (m + j) r hr : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff]
  intro b a
  have hb := blockIndex_true_val m (j + 1) b
  have ha := blockIndex_false_val m (j + 1) a
  have hval : (((rowEl (m + j) r hr : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) :
      Matrix (Fin (m + j + 2)) (Fin (m + j + 2)) k) = rowMat (m + j) r := rfl
  generalize eGP m (j + 1) ⟨true, b⟩ = p at hb ⊢
  generalize eGP m (j + 1) ⟨false, a⟩ = q at ha ⊢
  show (((rowEl (m + j) r hr : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) :
      Matrix (Fin (m + j + 2)) (Fin (m + j + 2)) k) p q = 0
  rw [hval, rowMat]
  by_cases hp : p = Fin.castSucc (Fin.last (m + j))
  · subst hp
    rw [updateRow_self]
    have ham := a.2
    have hq : q = Fin.castSucc (⟨a, by omega⟩ : Fin (m + j + 1)) := Fin.ext (by simpa using ha)
    rw [hq, Fin.lastCases_castSucc]
    exact h0 _ a.2
  · rw [updateRow_ne hp, one_apply_ne]
    intro c
    have := congrArg Fin.val c
    have ham := a.2
    omega

theorem mul_inv_qProj_mem (m j : ℕ) (x : Mir k (m + j)) (h d κ : Mir k (m + (j + 1)))
    (hh : h ∈ MirabolicParabolic k m (j + 1)) (hd : d ∈ MirabolicParabolic k m (j + 1)) (hq : d * κ ∈ Q k (m + j))
    (e : embedding₂ k (m + j) x = h * κ) :
    x * (qProj k (m + j) ⟨d * κ, hq⟩)⁻¹ ∈ MirabolicParabolic k m j := by
  apply mem_mirabolicParabolic_of_iotaM_mem
  set y := qProj k (m + j) ⟨d * κ, hq⟩ with hy
  have e1 : embedding₂ k (m + j) (x * y⁻¹) = (h * d⁻¹) * ((d * κ) * (embedding₂ k (m + j) y)⁻¹) := by
    rw [map_mul, map_inv, e]
    group
  rw [e1]
  refine mul_mem (mul_mem hh (inv_mem hd)) (mem_mirabolicParabolic_of_mirabolicProj_eq_one m (j + 1) _ ?_)
  have e2 : mirabolicProjection k (m + (j + 1)) (embedding₂ k (m + j) y) = (y : GL (Fin (m + j + 1)) k) :=
    mirProj_iotaM (m + j) y
  have e3 : (y : GL (Fin (m + j + 1)) k) = mirabolicProjection k (m + (j + 1)) (d * κ) := rfl
  rw [map_mul, map_inv, e2, e3, mul_inv_cancel]

theorem iotaM_descent (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) :
    ∀ K' ∈ 𝓝 (1 : Mir k (m + j)), ∃ K ∈ 𝓝 (1 : Mir k (m + (j + 1))),
      ∀ x : Mir k (m + j), ∀ h ∈ MirabolicParabolic k m (j + 1), ∀ κ ∈ K, embedding₂ k (m + j) x = h * κ →
        ∃ h' ∈ MirabolicParabolic k m j, ∃ κ' ∈ K', x = h' * κ' := by
  have : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  intro K' hK'
  let r : Mir k (m + j + 1) → Fin (m + j + 1) → k := fun κ => rowQ k (m + j) κ⁻¹
  have hcr : Continuous r := (continuous_rowQ (m + j)).comp continuous_inv
  let O : Set (Mir k (m + j + 1)) := {κ | (rowMat (m + j) (r κ)).det ≠ 0}
  have hO : IsOpen O :=
    isOpen_compl_singleton.preimage ((continuous_rowMat (m + j)).comp hcr).matrix_det
  have hr1 : r 1 = Pi.single (Fin.last (m + j)) 1 := by
    show rowQ k (m + j) 1⁻¹ = _
    rw [inv_one, rowQ_one]
  have hm1 : rowMat (m + j) (r 1) = 1 := by rw [hr1, rowMat_single]
  have h1O : (1 : Mir k (m + j + 1)) ∈ O := by
    show (rowMat (m + j) (r 1)).det ≠ 0
    rw [hm1, det_one]
    exact one_ne_zero
  let d : O → Mir k (m + j + 1) := fun κ => rowEl (m + j) (r κ.1) κ.2
  have hdc : Continuous d :=
    (continuous_rowEl (k := k) (m + j)).comp
      (Continuous.subtype_mk (hcr.comp continuous_subtype_val) fun κ => κ.2)
  have hQ : ∀ κ : O, d κ * κ.1 ∈ Q k (m + j) := fun κ => by
    have := mul_inv_mem_Q_of_rowQ_eq (m + j) (d κ) (κ.1)⁻¹ (rowQ_rowEl (m + j) (r κ.1) κ.2)
    rwa [inv_inv] at this
  let φ : O → Q k (m + j) := fun κ => ⟨d κ * κ.1, hQ κ⟩
  have hφc : Continuous φ := Continuous.subtype_mk (hdc.mul continuous_subtype_val) _
  let ψ : O → Mir k (m + j) := fun κ => qProj k (m + j) (φ κ)
  have hψc : Continuous ψ := (GlobalTheory.CompanionTheory.BZMirOnto.continuous_qProj k (m + j)).comp hφc
  have hd1 : d ⟨1, h1O⟩ = 1 := Subtype.ext (Units.ext hm1)
  have hψ1 : ψ ⟨1, h1O⟩ = 1 := by
    have : φ ⟨1, h1O⟩ = 1 := Subtype.ext (by
      show d ⟨1, h1O⟩ * 1 = 1
      rw [hd1, one_mul])
    show qProj k (m + j) (φ ⟨1, h1O⟩) = 1
    rw [this, map_one]
  have hpre : ψ ⁻¹' K' ∈ 𝓝 (⟨1, h1O⟩ : O) :=
    hψc.continuousAt.preimage_mem_nhds (by rw [hψ1]; exact hK')
  refine ⟨Subtype.val '' (ψ ⁻¹' K'), hO.isOpenMap_subtype_val.image_mem_nhds hpre, ?_⟩
  rintro x h hh _ ⟨κ, hκ, rfl⟩ e
  have hκinv : (κ.1)⁻¹ = embedding₂ k (m + j) x⁻¹ * h := by
    rw [map_inv, e]
    group
  have hrow : r κ.1 = rowQ k (m + j) h := by
    show rowQ k (m + j) (κ.1)⁻¹ = _
    rw [hκinv]
    exact rowQ_mul_of_mem_Q k (m + j) _ h (iotaM_mem_Q (m + j) x⁻¹)
  have hdH : d κ ∈ MirabolicParabolic k m (j + 1) :=
    rowEl_mem_HGP m j (r κ.1) κ.2 fun i hi => by
      rw [hrow]
      exact rowQ_eq_zero_of_mem_HGP m j h hh i hi
  exact ⟨x * (ψ κ)⁻¹, mul_inv_qProj_mem m j x h (d κ) κ.1 hh hdH (hQ κ) e, ψ κ, hκ, by group⟩

end GlobalTheory.CompanionTheory.LeibPhi.Emb

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwAvgInd

open GlobalTheory.CompanionTheory.TwistedAverage

theorem exists_finite_average {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {L : Subgroup G} (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L))
    (x : V) :
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → L) (c : ℂ),
      x - c • ∑ i, twOrbit ρ L θ x (r i) ∈ twKer ρ L θ ∧
      ∀ l : L, ρ (l : G) (c • ∑ i, twOrbit ρ L θ x (r i)) =
        (θ l : ℂ) • (c • ∑ i, twOrbit ρ L θ x (r i)) := by
  classical
  haveI := finiteIndex_stabKer hρ hL θ hθ x
  haveI : Finite (L ⧸ stabKer ρ L θ x) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (L ⧸ stabKer ρ L θ x)
  have hn : ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ stabKer ρ L θ x) = QuotientGroup.mk b →
      twOrbit ρ L θ x a = twOrbit ρ L θ x b := by
    intro a b h
    have hm : a⁻¹ * b ∈ stabKer ρ L θ x := QuotientGroup.eq.1 h
    have := twOrbit_mul_right ρ L θ x a _ hm
    rw [mul_inv_cancel_left] at this
    exact this.symm
  refine ⟨L ⧸ stabKer ρ L θ x, inferInstance, Quotient.out,
    ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹, ?_, ?_⟩
  · have e : x - ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ •
          ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) =
        ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ •
          ∑ q : L ⧸ stabKer ρ L θ x, (x - twOrbit ρ L θ x (Quotient.out q)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    have e2 : x - twOrbit ρ L θ x (Quotient.out q) =
        (-(((θ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
          (ρ ((Quotient.out q : L) : G) x - (θ (Quotient.out q) : ℂ) • x) := by
      rw [twOrbit, smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        neg_smul, neg_smul, one_smul]
      abel
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
  · intro l
    have h1 : ∀ t : L, ρ (l : G) (twOrbit ρ L θ x t) = (θ l : ℂ) • twOrbit ρ L θ x (l * t) := by
      intro t
      have h0 : θ l * (θ (l * t))⁻¹ = (θ t)⁻¹ := by
        rw [map_mul, mul_inv, mul_inv_cancel_left]
      simp only [twOrbit, map_smul, smul_smul]
      rw [← Units.val_mul, h0, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    have h2 : ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) =
        ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) := by
      let e : Equiv.Perm (L ⧸ stabKer ρ L θ x) := MulAction.toPerm l
      have h3 : ∀ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) =
          twOrbit ρ L θ x (Quotient.out (e q)) := by
        intro q
        refine hF _ _ ?_
        rw [QuotientGroup.out_eq']
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [Finset.sum_congr rfl fun q _ => h3 q]
      exact Equiv.sum_comp e (fun q => twOrbit ρ L θ x (Quotient.out q))

    rw [map_smul, map_sum, Finset.sum_congr rfl fun q _ => h1 _, ← Finset.smul_sum, h2,
    smul_comm]

def evalAt {G W : Type} [AddCommGroup W] [Module ℂ W] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W)
    (g : G) : smoothPart (ind P τ) →ₗ[ℂ] W :=
  (LinearMap.proj g) ∘ₗ (indSpace P τ).subtype ∘ₗ (smoothPart (ind P τ)).subtype

theorem exists_twisted_average_smInd {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W)
    (L : Subgroup G) (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L))
    (f : smoothPart (ind P τ)) :
    ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧
      (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧
      ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  obtain ⟨ι, _, r, c, h1, h2⟩ :=
    exists_finite_average (smInd P τ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_smInd P τ) hL θ hθ f
  refine ⟨_, h1, ?_, ?_⟩
  · intro g hg
    by_contra hcon
    push_neg at hcon
    apply hg
    have hz : ∀ i, evalAt P τ g (twOrbit (smInd P τ) L θ f (r i)) = 0 := by
      intro i
      have : evalAt P τ g (smInd P τ ((r i : L) : G) f) = 0 := hcon _ (r i).2
      simp only [twOrbit, map_smul, this, smul_zero]
    have : evalAt P τ g (c • ∑ i, twOrbit (smInd P τ) L θ f (r i)) = 0 := by

      rw [map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]
    exact this
  · intro l g
    have h3 := congrArg (evalAt P τ g) (h2 l)
    rw [map_smul] at h3
    exact h3

end GlobalTheory.CompanionTheory.TwAvgInd
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartBc

theorem chart_bc_of_ne : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) (hp : p ≠ 0) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) {V : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d),
    letI := σ.toAlgebra
    letI := c.D.i.toAlgebra
    ∃ (c' : Chart γ' p q κ' V d) (e : c.D ⟶ (m.mor p).functor.obj c'.D), (∀ i, e.φ (c.t i) = c'.t i) ∧
      (FlatT c.D → FlatT c'.D) ∧
      ∃ f : R' ⊗[R] c.D.B ≃+* c'.D.B, (∀ r, f (r ⊗ₜ 1) = c'.D.i r) ∧ ∀ x, f (1 ⊗ₜ x) = e.φ x := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m hp hu hg V d c
  exact chart_bc m hu hg (fun h => absurd h hp) c

end GlobalTheory.CompanionTheory.ChartBc
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cohomology_restriction_between_stable_families : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 : Set X.Opens) (Q' : ObjectProperty (Thick (nlFun γ p X q κ))) (h : St Q₀ 𝒱 ≤ Q') (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := by
  first | exact @GlobalTheory.CompanionTheory.ZarCosieve.main | exact GlobalTheory.CompanionTheory.ZarCosieve.main | (intros; apply GlobalTheory.CompanionTheory.ZarCosieve.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

theorem _root_.GlobalTheory.T.truncated_envelope_filtration_quotient : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → ∀ (b : ℕ →₀ B) (r : ℕ), r ≤ s → ∀ c : B, (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ⊔ Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) := by
  first | exact @GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit | exact GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit | (intros; apply GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit <;> assumption)
end
