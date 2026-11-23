module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle334
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle337
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle336
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle098

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open ValuativeRel Topology GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem uM_levi_mul_uM_levi (n : ℕ) (y y' : Fin n → k) (b b' : GL (Fin n) k) :
    uM k n y * levi k n b * (uM k n y' * levi k n b') =
      uM k n (y + (b : Matrix (Fin n) (Fin n) k).mulVec y') * levi k n (b * b') := by
  rw [mul_assoc, ← mul_assoc (GlobalTheory.BZMir.levi k n b), GlobalTheory.CompanionTheory.BZPsiPG.levi_mul_uM,
    GlobalTheory.CompanionTheory.BZPsiPG.uM_add, map_mul]
  simp only [mul_assoc]

theorem mirProj_levi_eq (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi n g

theorem mirProj_uM (n : ℕ) (y : Fin n → k) : mirabolicProjection k n (uM k n y) = 1 :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_uv n y

theorem uM_injective (n : ℕ) : Function.Injective (uM k n) := by
  intro y y' h
  funext a
  have entry : ∀ z : Fin n → k, ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n z : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = z a := by
    intro z
    change (1 + GlobalTheory.BZMir.colMat k n z) (Fin.castSucc a) (Fin.last n) = z a
    simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  rw [← entry y, ← entry y', h]

theorem uM_levi_inj (n : ℕ) {y y' : Fin n → k} {g g' : GL (Fin n) k}
    (h : uM k n y * levi k n g = uM k n y' * levi k n g') : y = y' ∧ g = g' := by
  have hg : g = g' := by
    have hp := congrArg (GlobalTheory.BZMir.mirabolicProjection k n) h
    simpa only [map_mul, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_levi_eq, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_uM, one_mul] using hp
  subst hg
  exact ⟨GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_injective n (mul_right_cancel h), rfl⟩

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def latt (n : ℕ) (c : kˣ) : AddSubgroup (Fin n → k) where
  carrier := {y | ∀ j, y j ∈ cball c}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' j := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_latt {n : ℕ} {c : kˣ} {y : Fin n → k} : y ∈ latt n c ↔ ∀ j, y j ∈ cball c :=
  Iff.rfl

theorem latt_eq_pi (n : ℕ) (c : kˣ) : (latt n c : Set (Fin n → k)) = Set.univ.pi fun _ => cball c := by
  ext y
  simp only [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt, Set.mem_univ_pi]

theorem isOpen_latt (n : ℕ) (c : kˣ) : IsOpen (latt n c : Set (Fin n → k)) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_cball c

theorem isCompact_latt (n : ℕ) (c : kˣ) : IsCompact (latt n c : Set (Fin n → k)) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt_eq_pi]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball c

theorem isClosed_latt (n : ℕ) (c : kˣ) : IsClosed (latt n c : Set (Fin n → k)) :=
  AddSubgroup.isClosed_of_isOpen _ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c)

theorem exists_latt_subset {n : ℕ} {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ c : kˣ, (latt n c : Set (Fin n → k)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hmem : (⋂ j, t j) ∈ 𝓝 (0 : k) := Filter.iInter_mem.2 fun j => by simpa using ht j
  obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_cball_subset hmem
  refine ⟨c, fun y hy => hsub (Set.mem_pi.2 fun j _ => ?_)⟩
  exact Set.mem_iInter.1 (hc (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt.1 hy j)) j

theorem mulVec_mem_latt {n : ℕ} {c : kˣ} {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) {y : Fin n → k}
    (hy : y ∈ latt n c) : (κ : Matrix (Fin n) (Fin n) k).mulVec y ∈ latt n c := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt] at hy ⊢
  have hint := ((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1
  intro j
  change valuation k ((κ : Matrix (Fin n) (Fin n) k).mulVec y j) ≤ valuation k (c : k)
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro i _
  rw [map_mul]
  calc valuation k ((κ : Matrix (Fin n) (Fin n) k) j i) * valuation k (y i)
      ≤ 1 * valuation k (c : k) :=
        mul_le_mul' ((Valuation.mem_integer_iff _ _).1 (hint j i)) (hy i)
    _ = valuation k (c : k) := one_mul _

def Bgrp (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) : Subgroup (Mir k n) where
  carrier := {p | ∃ y ∈ latt n c, ∃ b ∈ K₁, p = uM k n y * levi k n b}
  mul_mem' := by
    rintro _ _ ⟨y, hy, b, hb, rfl⟩ ⟨y', hy', b', hb', rfl⟩
    exact ⟨_, add_mem hy (mulVec_mem_latt (h hb) hy'), _, mul_mem hb hb', uM_levi_mul_uM_levi n y y' b b'⟩
  one_mem' := ⟨0, zero_mem _, 1, one_mem _, by rw [uM_zero, map_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨y, hy, b, hb, rfl⟩
    refine ⟨_, mulVec_mem_latt (h (inv_mem hb)) (neg_mem hy), b⁻¹, inv_mem hb, ?_⟩
    rw [_root_.mul_inv_rev, ← map_inv, GlobalTheory.CompanionTheory.BZPsiPG.Cont.uM_inv, levi_mul_uM]

theorem mem_Bgrp {n : ℕ} {c : kˣ} {K₁ : Subgroup (GL (Fin n) k)} {h : K₁ ≤ KO k (Fin n)} {p : Mir k n} :
    p ∈ Bgrp n c K₁ h ↔ ∃ y ∈ latt n c, ∃ b ∈ K₁, p = uM k n y * levi k n b :=
  Iff.rfl

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (g : GL (Fin (i + t)) k), ∃ q : Qp k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), g = (q : GL (Fin (i + t)) k) * κ := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO | exact GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.finite_fibre_functions_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (f : cIndSpace (HPG k i t) (hRep τ σ)), ((fun κ : GL (Fin (i + t)) k => fibV f κ) '' (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_fibV_image | exact GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_fibV_image | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_fibV_image <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mulVec_mid_block_decomp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t) (v : Fin t → k), ∃ x : Fin i → k, ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) = topV k i t x + midV k i t ((((qBlocks k i t q).2 : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top | exact GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unipotent_top_mem_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (x : Fin i → k), ∃ h : uM k (i + t) (topV k i t x) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (uM k i x, 1) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main | exact GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.continuous_levi_unipotent_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj | exact GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levi_block_mem_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t), ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj | exact GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.DConj

open GlobalTheory.CompanionTheory.BZPhiPG.Cells GlobalTheory.CompanionTheory.LeibPhi GlobalTheory.CompanionTheory.BZPhiPhi
open GlobalTheory.CompanionTheory.BZMir.GpExists (unip_apply_of_ne_last unip_apply_last_last)

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blockIndex_false_eq_castAdd₂ (i t : ℕ) (a : Fin (i + 1)) :
    eGP (i + 1) t ⟨false, a⟩ = (Fin.castAdd (t + 1) a : Fin ((i + 1) + (t + 1))) :=
  Fin.ext (by rw [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_false_val]; simp)

theorem blockIndex_true_eq_natAdd₂ (i t : ℕ) (b : Fin (t + 1)) :
    eGP (i + 1) t ⟨true, b⟩ = (Fin.natAdd (i + 1) b : Fin ((i + 1) + (t + 1))) :=
  Fin.ext (by rw [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val]; simp)

theorem gpProj_snd_apply (m j : ℕ) (g : MirabolicParabolic k m j) (a b : Fin (j + 1)) :
    (((gpProj k m j g).2 : Mir k j) : GL (Fin (j + 1)) k).val a b =
      ((g : Mir k (m + j)) : GL (Fin (m + j + 1)) k).val (eGP m j ⟨true, a⟩) (eGP m j ⟨true, b⟩) := by
  show (leviProj k (eGP m j) (hgpIncl k m j g) true).val a b = _
  rw [leviProj_apply]
  rfl

theorem inv_mulVec_natAdd (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k) (x : Fin (t + 1)) :
    ((((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ
        (Fin.append (0 : Fin (i + 1) → k) d : Fin ((i + 1) + (t + 1)) → k)) (Fin.natAdd (i + 1) x) =
      (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) x := by
  have hinv : ((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k) =
      (((gpProj k (i + 1) t h⁻¹).2 : Mir k t) : GL (Fin (t + 1)) k) := by
    rw [map_inv]
    rfl
  have hcoe : (((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) =
      (((h⁻¹ : MirabolicParabolic k (i + 1) t) : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) := rfl
  rw [hinv, hcoe]
  have hz : ∀ a : Fin (i + 1), ((((h⁻¹ : MirabolicParabolic k (i + 1) t) : Mir k ((i + 1) + t)) :
      GL (Fin ((i + 1) + t + 1)) k)).val (Fin.natAdd (i + 1) x) (Fin.castAdd (t + 1) a) = 0 := by
    intro a
    have := (mem_mirabolicParabolic_iff k _ _ _).1 (h⁻¹ : MirabolicParabolic k (i + 1) t).2 x a
    rwa [blockIndex_true_eq_natAdd₂, blockIndex_false_eq_castAdd₂] at this
  show ∑ y : Fin ((i + 1) + (t + 1)), _ = ∑ y : Fin (t + 1), _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [gpProj_snd_apply, blockIndex_true_eq_natAdd₂, blockIndex_true_eq_natAdd₂]

theorem pgProj_fst_apply (I T : ℕ) (g : HPG k I T) (a b : Fin (I + 1)) :
    (((pgProj k I T g).1 : Mir k I) : GL (Fin (I + 1)) k).val a b =
      ((g : Mir k (I + T)) : GL (Fin (I + T + 1)) k).val (ePG I T ⟨false, a⟩) (ePG I T ⟨false, b⟩) := by
  show (leviProj k (ePG I T) (hpgIncl k I T g) false).val a b = _
  rw [leviProj_apply]
  rfl

theorem pgProj_snd_apply (I T : ℕ) (g : HPG k I T) (a b : Fin T) :
    ((pgProj k I T g).2 : GL (Fin T) k).val a b =
      ((g : Mir k (I + T)) : GL (Fin (I + T + 1)) k).val (ePG I T ⟨true, a⟩) (ePG I T ⟨true, b⟩) := by
  show (leviProj k (ePG I T) (hpgIncl k I T g) true).val a b = _
  rw [leviProj_apply]
  rfl

theorem one_ePG (I T : ℕ) (x : Bool) (a b : Two (Fin (I + 1)) (Fin T) x) :
    (1 : Matrix (Fin (I + T + 1)) (Fin (I + T + 1)) k) (ePG I T ⟨x, a⟩) (ePG I T ⟨x, b⟩) =
      (1 : Matrix (Two (Fin (I + 1)) (Fin T) x) (Two (Fin (I + 1)) (Fin T) x) k) a b := by
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
    intro e
    exact hab (by simpa using (ePG I T).injective e)


variable (k) in
def uEl (i t : ℕ) (c : Fin (i + 1) → k) : Mir k ((i + 1) + t + 1) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k))), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem uEl_mem (i t : ℕ) (c : Fin (i + 1) → k) : uEl k i t c ∈ HPG k (i + 1) (t + 1) := by
  refine mem_HPG_of (I := i + 1) (T := t + 1) (uEl k i t c) ?_ ?_
  · intro x y
    refine unip_castSucc_castSucc _ _ _ _ ?_
    intro e
    have := congrArg Fin.val e
    simp only at this
    omega
  · intro x
    refine (unip_apply_castSucc_last k _ _ _).trans ?_
    show (Fin.append c (0 : Fin (t + 1) → k)) (Fin.natAdd (i + 1) x) = 0
    simp

theorem uEl_fst (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).1 ∈ MirUin k (i + 1) := by
  refine ⟨Multiplicative.ofAdd c, ?_⟩
  apply Units.ext
  ext a b
  show (unip k (i + 1) (Multiplicative.ofAdd c)).val a b =
    (((pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).1 : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k).val a b
  rw [pgProj_fst_apply]
  show _ = (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k)))).val _ _
  induction b using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    induction a using Fin.lastCases with
    | last => rw [ePG_false_last, unip_apply_last_last, unip_apply_last_last]
    | cast a =>
      have e : ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a) :=
        Fin.ext (by rw [ePG_false_val]; simp)
      rw [e, unip_apply_castSucc_last, unip_apply_castSucc_last]
      simp
  | cast b =>
    have hq : ePG (i + 1) (t + 1) ⟨false, Fin.castSucc b⟩ ≠ Fin.last ((i + 1) + (t + 1)) := fun h =>
      Fin.castSucc_ne_last b ((ePG_false_eq_last_iff _ _ _).1 h)
    rw [unip_apply_of_ne_last _ _ _ _ hq, unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last b), one_ePG]

theorem uEl_snd (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uEl k i t c, uEl_mem i t c⟩).2 = 1 := by
  apply Units.ext
  ext a b
  rw [pgProj_snd_apply]
  show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c (0 : Fin (t + 1) → k)))).val _ _ = _
  have hq : ePG (i + 1) (t + 1) ⟨true, b⟩ ≠ Fin.last ((i + 1) + (t + 1)) := by
    intro h
    have := congrArg Fin.val h
    rw [ePG_true_val] at this
    have hb := b.2
    simp at this
    omega
  rw [unip_apply_of_ne_last _ _ _ _ hq, one_ePG]
  rfl

end

theorem dEmb_mul_sEmb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k), ∃ u : HPG k (i + 1) (t + 1), (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1) ∧ (pgProj k (i + 1) (t + 1) u).2 = 1 ∧ dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * (u : Mir k ((i + 1) + t + 1)) * dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) := by
  intro k _ _ _ _ i t h d
  let A : GL (Fin ((i + 1) + t + 1)) k := ((h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k)
  let v : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) d
  let w : Fin ((i + 1) + (t + 1)) → k := (A⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ v
  let c : Fin (i + 1) → k := fun x => w (Fin.castAdd (t + 1) x)
  let e : Fin (t + 1) → k :=
    ((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d
  let a : Fin ((i + 1) + (t + 1)) → k := Fin.append c (0 : Fin (t + 1) → k)
  let b : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) e
  have hsum : a + b = w := by
    funext x
    induction x using Fin.addCases with
    | left x => simp [a, b, c]
    | right x =>
      simp only [a, b, Pi.add_apply, Fin.append_right, Pi.zero_apply, zero_add]
      exact (inv_mulVec_natAdd i t h d x).symm
  refine ⟨⟨uEl k i t c, uEl_mem i t c⟩, uEl_fst i t c, uEl_snd i t c, ?_⟩
  apply Subtype.ext
  have e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd w) := by
    rw [← map_mul, ← ofAdd_add, hsum]
  have e3 : A.val *ᵥ w = v := by
    show A.val *ᵥ ((A⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
    simp
  have e2 : glEmb k _ A * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd w) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ A := by
    have := glEmb_mul_unip' k _ A (Multiplicative.ofAdd w)
    rw [toAdd_ofAdd, e3] at this
    exact this
  show unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ A =
    glEmb k _ A * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b)
  rw [mul_assoc, e1, e2]

end GlobalTheory.CompanionTheory.BZPhiPG.DConj

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.support_compact_mod_parabolic_off_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ C : Set (Mir k ((i + 1) + t + 1)), IsCompact C ∧ (∀ c ∈ C, c ∉ Cl k i t) ∧
    ∀ g, evX f g ≠ 0 → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ c ∈ C, g = h * c := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl | exact GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.closed_evaluation_vanishing_on_open : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  eC ψ f = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish | exact GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integral_linear_change_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W) (l : IsLocallyConstant φ) (c : HasCompactSupport φ), @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) = ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) φ := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec | exact GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec <;> assumption)
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Scale

theorem smInt_subst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (w : GL (Fin n) k) (F : (Fin n → k) → W),
    IsLocallyConstant F → HasCompactSupport F →
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun d => F ((w⁻¹ : GL (Fin n) k).1.mulVec d)) =
      ((dpow n 1 w : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F := by
  intro k _ _ _ _ n W _ _ w F l c
  exact smInt_mulVec k n W w F l c

end GlobalTheory.CompanionTheory.BZPhiPG.Scale

end
end
