module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulVecOfMemTD
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle176
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle319
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.QLevi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  apply Fin.ext
  simp [ePG]

theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  apply Fin.ext
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem two_true_eq (i t : ℕ) (b : Fin t) :
    two (stdSum (rfl : i + t = i + t)) ⟨true, b⟩ = Fin.natAdd i b := by
  apply Fin.ext
  simp

theorem two_false_eq (i t : ℕ) (a : Fin i) :
    two (stdSum (rfl : i + t = i + t)) ⟨false, a⟩ = Fin.castAdd t a := by
  apply Fin.ext
  simp

theorem levi_entry (n : ℕ) (g : GL (Fin n) k) (a b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (g : Matrix (Fin n) (Fin n) k) a b := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_col (n : ℕ) (g : GL (Fin n) k) (a : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_row (n : ℕ) (g : GL (Fin n) k) (b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc b) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last (n : ℕ) (g : GL (Fin n) k) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_mem_HPG (i t : ℕ) (q : Qp k i t) : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t := by
  show ((levi k (i + t) (q : GL (Fin (i + t)) k) : Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t)
  refine mem_parab_iff.2 ?_
  intro a c x y hac
  obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
    revert hac; cases a <;> cases c <;> decide
  have hx : ePG i t ⟨true, x⟩ = Fin.castSucc (Fin.natAdd i (x : Fin t)) := ePG_true_eq i t x
  rw [hx]
  induction (y : Fin (i + 1)) using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact levi_entry_last_col _ _ _
  | cast y =>
    rw [ePG_false_eq, levi_entry]
    have := mem_parab_iff.1 q.2 true false (x : Fin t) (y : Fin i) (by decide)
    rwa [two_true_eq, two_false_eq] at this

theorem pgProj_levi (i t : ℕ) (q : Qp k i t) (h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t) :
    pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) false : GL (Fin (i + 1)) k).val a b =
      ((levi k i (qBlocks k i t q).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b
    rw [leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨false, a⟩) (ePG i t ⟨false, b⟩) = _
    induction a using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last, levi_entry_last]
      | cast b => rw [ePG_false_eq, levi_entry_last_row, levi_entry_last_row]
    | cast a =>
      rw [ePG_false_eq]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last_col, levi_entry_last_col]
      | cast b =>
        rw [ePG_false_eq, levi_entry, levi_entry]
        show _ = (leviProj k (two (stdSum (rfl : i + t = i + t))) q false : GL (Fin i) k).val a b
        rw [leviProj_apply, two_false_eq, two_false_eq]
  · apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) true : GL (Fin t) k).val a b =
      (leviProj k (two (stdSum (rfl : i + t = i + t))) q true : GL (Fin t) k).val a b
    rw [leviProj_apply, leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨true, a⟩) (ePG i t ⟨true, b⟩) = _
    rw [ePG_true_eq, ePG_true_eq, levi_entry, two_true_eq, two_true_eq]

end GlobalTheory.CompanionTheory.BZPsiPG.QLevi

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem levi_Qp_mem_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (q : Qp k i t) :
    ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t,
      pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) :=
  ⟨QLevi.levi_mem_HPG i t q, QLevi.pgProj_levi i t q _⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Cont

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_entry (n : ℕ) (a b : Fin (n + 1)) :
    Continuous fun y : Fin n → k => colMat k n y a b := by
  unfold colMat
  split_ifs
  · induction a using Fin.lastCases with
    | last => simp only [Fin.lastCases_last]; exact continuous_const
    | cast i => simp only [Fin.lastCases_castSucc]; exact continuous_apply i
  · exact continuous_const

theorem continuous_uM_val (n : ℕ) : Continuous fun y : Fin n → k =>
    (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  have h : (fun y : Fin n → k =>
      (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) =
      fun y => 1 + colMat k n y := by
    funext y
    rfl
  rw [h]
  refine continuous_const.add (continuous_matrix fun a b => ?_)
  exact continuous_colMat_entry k n a b

theorem uM_inv (n : ℕ) (y : Fin n → k) : (uM k n y)⁻¹ = uM k n (-y) := by
  have h : uM k n (-y) * uM k n y = 1 := by
    rw [← uM_add, neg_add_cancel, uM_zero]
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem continuous_uM (n : ℕ) : Continuous (uM k n) := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨continuous_uM_val k n, ?_⟩
  have h : ∀ y : Fin n → k, ((uM k n y : GL (Fin (n + 1)) k))⁻¹ =
      (uM k n (-y) : GL (Fin (n + 1)) k) := by
    intro y
    rw [← uM_inv k n y, Subgroup.coe_inv]
  simp only [Function.comp_apply, h]
  exact (continuous_uM_val k n).comp continuous_neg

end GlobalTheory.CompanionTheory.BZPsiPG.Cont

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem continuous_levi_uM_mirProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
  intro k _ _ _ _ n
  exact ⟨GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n, Cont.continuous_uM k n,
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n⟩

end GlobalTheory.CompanionTheory.BZPsiPG
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Off

variable {k : Type} [Field k]

theorem sEmb_row (n : ℕ) (m : Mir k n) (j : Fin (n + 1 + 1)) :
    (((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
      (Fin.castSucc (Fin.last n)) j = (1 : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hs : ((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmb k (n + 1) (m : GL (Fin (n + 1)) k) := rfl
  have hm : Matrix.vecMul (GlobalTheory.BZMir.eLast k n) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.eLast k n := m.2
  rw [GlobalTheory.BZMir.vecMul_eLast] at hm
  rw [hs]
  show GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (Fin.castSucc (Fin.last n)) j = _
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne]
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
    rw [hm]
    by_cases hj : j' = Fin.last n
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · rw [Matrix.one_apply_ne (fun e => hj (Fin.castSucc_injective _ e).symm)]
      simp [GlobalTheory.BZMir.eLast, Pi.single_apply, hj]

theorem dEmb_mul_sEmb_mem_Cl (i t : ℕ) (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) :
    dEmb k i t d * sEmb k _ m ∈ Cl k i t := by
  simp only [Cl, Set.mem_ofPred_eq]
  intro c
  rw [_root_.mul_inv_rev, ← map_inv, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  simp_rw [sEmb_row]
  rw [← Matrix.mul_apply, Matrix.one_mul]
  show ((1 : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) -
      GlobalTheory.BZMir.colMat k (i + 1 + (t + 1)) (Fin.append 0 d)) _ _ = 0
  rw [Matrix.sub_apply]
  have hRC : (Fin.last (i + 1 + t)).castSucc ≠ (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  have hCL : (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) ≠ Fin.last (i + 1 + (t + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  rw [Matrix.one_apply_ne hRC]
  simp [GlobalTheory.BZMir.colMat, hCL]

end GlobalTheory.CompanionTheory.BZPhiPG.Off


open GlobalTheory.CompanionTheory.BZPhiPG.Off in
theorem GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
    eC ψ f = 0 := by
  intro k _ _ _ _ i t ψ τ σ hτ hσ f hf
  funext m
  have hz : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * sEmb k (i + 1 + t) m) = 0 :=
    fun d => hf _ (dEmb_mul_sEmb_mem_Cl i t d m)
  have hint : intC ψ f (sEmb k (i + 1 + t) m) = 0 := by
    unfold intC
    simp only [hz, smul_zero]
    unfold GlobalTheory.CompanionTheory.Rodier.smInt
    apply finsum_eq_zero_of_forall_eq_zero
    intro w
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have hpre : ((fun _ => (0 : TensorProduct ℂ τ.V σ.V)) : (Fin (t + 1) → k) → TensorProduct ℂ τ.V σ.V) ⁻¹' {w} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h0 => hw h0.symm
      rw [hpre, MeasureTheory.measure_empty]
      simp
  simp only [eC, hint, map_zero, smul_zero, Pi.zero_apply]

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

private theorem continuous_leviProj_hpgIncl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (b : Bool) :
    Continuous (fun h : HPG k i t => (leviProj k (ePG i t) (hpgIncl k i t h)) b) := by
  have h0 : Continuous (fun h : HPG k i t =>
      (((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hv : Continuous (fun h : HPG k i t =>
      ((leviProj k (ePG i t) (hpgIncl k i t h)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k)) :=
    (h0.matrix_submatrix (fun j => (ePG i t) ⟨b, j⟩) (fun j => (ePG i t) ⟨b, j⟩)).congr (fun _ => rfl)
  rw [Units.continuous_iff]
  refine ⟨hv, ?_⟩
  have hinv : Continuous (fun h : HPG k i t =>
      ((leviProj k (ePG i t) (hpgIncl k i t h⁻¹)) b : Matrix (Two (Fin (i + 1)) (Fin t) b) (Two (Fin (i + 1)) (Fin t) b) k)) :=
    hv.comp continuous_inv
  refine hinv.congr (fun h => ?_)
  simp only [map_inv, Pi.inv_apply]

theorem continuous_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) : Continuous (pgProj k i t) := by
  have h1 : Continuous (fun h : HPG k i t => (pgProj k i t h).1) :=
    continuous_induced_rng.2 ((continuous_leviProj_hpgIncl k i t false).congr (fun _ => rfl))
  have h2 : Continuous (fun h : HPG k i t => (pgProj k i t h).2) :=
    (continuous_leviProj_hpgIncl k i t true).congr (fun _ => rfl)
  exact (h1.prodMk h2).congr (fun _ => rfl)

theorem isSmooth_sigX {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) : IsSmooth (sigX τ σ) := by
  have hd : ∀ (n : ℕ) (s : ℂ), IsSmoothChar (detChar (Fin n) (absPow k s)) :=
    fun n s => IsSmoothChar.detChar (isSmoothChar_of_isUnram (isUnram_absPow k s))
  have h1 : IsSmooth (mtw τ (↑(t + 1) / 2)).ρ := by
    refine isSmooth_twist hτ ?_
    unfold dpowM dpow
    unfold IsSmoothChar
    rw [← MonoidHom.comap_ker]
    exact IsOpen.preimage continuous_subtype_val (hd _ _)
  have h2 : IsSmooth (σ.tw (-↑(i + 1 + 1) / 2)).ρ := by
    unfold GRep.tw
    exact isSmooth_twist hσ (by unfold dpow; exact hd _ _)
  intro v
  exact (isSmooth_extTensor h1 h2 v).preimage (continuous_pgProj k (i + 1) (t + 1))

theorem sigX_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (w : τ.V ⊗[ℂ] σ.V),
  ∃ O ∈ nhds (1 : Mir k ((i + 1) + t + 1)), ∀ h : HPG k (i + 1) (t + 1), ((h : Mir k ((i + 1) + (t + 1))) ∈ O) → sigX τ σ h w = w := by
  intro k _ _ _ _ i t τ σ hτ hσ w
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 (isSmooth_sigX τ σ hτ hσ w)
  have h1 : (1 : HPG k (i + 1) (t + 1)) ∈ Subtype.val ⁻¹' O := by
    rw [hOeq]
    simp
  refine ⟨O, hO.mem_nhds h1, fun h hh => ?_⟩
  have hh' : h ∈ Subtype.val ⁻¹' O := hh
  rw [hOeq] at hh'
  exact hh'

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BZPhiPG.Scale

theorem sr1_field (k : Type) [Field k] : GlobalTheory.HaarLin.HasStableRangeOne k := by
  intro a b h
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      exact not_isCoprime_zero_zero h
    exact ⟨b⁻¹, by simp [hb]⟩
  · exact ⟨0, by simp [ha]⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAddHaar_muD (t : ℕ) : @Measure.IsAddHaarMeasure _ _ _ (_root_.borel _) (muD k t) := by
  letI : MeasurableSpace (Fin t → k) := _root_.borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem map_muD (t : ℕ) (A : GL (Fin t) k) :
    @Measure.map _ _ (_root_.borel _) (_root_.borel _) (fun d : Fin t → k => (A⁻¹ : GL (Fin t) k).val *ᵥ d) (muD k t) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det A)) • muD k t := by
  haveI : SecondCountableTopology k := GlobalTheory.HaarScaleMatrix.secondCountable_of_localField k
  have h := GlobalTheory.HaarLin.map_mulVec_of_mem_TD k (Fin t) (A⁻¹ : GL (Fin t) k).val
    (GlobalTheory.HaarLin.Gauss.mem_TD_of_isUnit_det k (sr1_field k) (Fin t) _
      (Matrix.GeneralLinearGroup.det (A⁻¹ : GL (Fin t) k)).isUnit)
    (Matrix.GeneralLinearGroup.det (A⁻¹ : GL (Fin t) k)) rfl (muD k t) (isAddHaar_muD t)
  rw [h, map_inv, map_inv, inv_inv]

theorem val_dpow_one (t : ℕ) (A : GL (Fin t) k) :
    ((dpow t 1 A : ℂˣ) : ℂ) = ((distribHaarChar k (Matrix.GeneralLinearGroup.det A) : ℝ) : ℂ) := by
  show ((absPow k (((1 : ℝ)) : ℂ) (Matrix.GeneralLinearGroup.det A) : ℂˣ) : ℂ) = _
  rw [val_absPow, Complex.ofReal_one, Complex.cpow_one]
  rfl

theorem smInt_mulVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W)
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) =
      ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) φ := by
  classical
  letI : MeasurableSpace (Fin t → k) := _root_.borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  haveI : (muD k t).IsAddHaarMeasure := isAddHaar_muD t
  set f : (Fin t → k) → (Fin t → k) := fun d => (A⁻¹ : GL (Fin t) k).val *ᵥ d with hf
  have fc : Continuous f := Continuous.matrix_mulVec continuous_const continuous_id
  have fm : Measurable f := fc.measurable
  set a : NNReal := distribHaarChar k (Matrix.GeneralLinearGroup.det A) with ha
  have hmeas : ∀ y : W, muD k t ((φ ∘ f) ⁻¹' {y}) = a • muD k t (φ ⁻¹' {y}) := by
    intro y
    have hS : MeasurableSet (φ ⁻¹' {y}) := (l.isOpen_fiber y).measurableSet
    rw [Set.preimage_comp, ← Measure.map_apply fm hS, map_muD t A]
    rfl
  let S : Finset W := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.finite_range l c).toFinset
  have hS : ∀ x, φ x ∈ S := fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩
  have e₀ : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (id ∘ (φ ∘ f)) =
      ∑ y ∈ S, ((((muD k t) ((φ ∘ f) ⁻¹' {y})).toReal : ℝ) : ℂ) • id y :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp (muD k t) (φ ∘ f) id S (fun x => hS _)
      (fun y _ => ((l.comp_continuous fc).isOpen_fiber y).measurableSet)
      (fun y _ hy => by
        rw [hmeas y]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top (GlobalTheory.CompanionTheory.Rodier.SmIntEl.measure_level_ne_top _ c hy))
  have e₁ : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (id ∘ φ) =
      ∑ y ∈ S, ((((muD k t) (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • id y :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp (muD k t) φ id S hS
      (fun y _ => (l.isOpen_fiber y).measurableSet)
      (fun y _ hy => GlobalTheory.CompanionTheory.Rodier.SmIntEl.measure_level_ne_top _ c hy)
  have e₀' : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (fun d => φ (f d)) = _ := e₀
  have e₁' : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) φ = _ := e₁
  rw [val_dpow_one]
  refine e₀'.trans ?_
  rw [e₁', Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hmeas y, ENNReal.toReal_smul, smul_smul]
  congr 1
  simp [NNReal.smul_def, ← ha]

end GlobalTheory.CompanionTheory.BZPhiPG.Scale

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.quotient_filtration_bijective_of_cover : KH.KIso → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (U : Cov q) (s u : ℕ), (∀ α, U.d α < u) → u ≤ s → ∀ (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ (j : ℕ),
    Function.Bijective (quoK q (KS q s 𝒱) (u : ℤ) j) := by
  first | exact @GlobalTheory.CompanionTheory.QuoK.quoK_bijective | exact GlobalTheory.CompanionTheory.QuoK.quoK_bijective | (intros; apply GlobalTheory.CompanionTheory.QuoK.quoK_bijective <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.continuous_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi <;> assumption)
end
