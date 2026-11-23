module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Formalism.CharacterColumnKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFinite
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthAddMonoidHomFiniteGroupFractionQuotientLe
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle075
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem full_blocks {r : ℕ} {k : Type} [CommRing k] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    full (blocks A) = A := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [full, blocks, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castSucc,
      finSumFinEquiv_symm_last]

def nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k :=
  Matrix.of fun i j => if i = Fin.last r then c j else if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

theorem nfMat_mulVec_castSucc {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k)
    (i : Fin r) : (nfMat c *ᵥ v) (Fin.castSucc i) = v i.succ := by
  simp only [Matrix.mulVec, dotProduct, nfMat, Matrix.of_apply, Fin.castSucc_ne_last, if_false]
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [if_neg]; · simp
    intro h; apply hj; ext; simp [h]
  · simp

theorem nfMat_mulVec_last {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k) :
    (nfMat c *ᵥ v) (Fin.last r) = c ⬝ᵥ v := by
  simp [Matrix.mulVec, dotProduct, nfMat]

theorem nfMat_injective {r : ℕ} {k : Type} [Field k] (c : Fin (r + 1) → k) (h0 : c 0 ≠ 0) :
    Function.Injective (nfMat c).mulVec := by
  intro x y hxy
  set v := x - y with hv
  have key : nfMat c *ᵥ v = 0 := by rw [hv, Matrix.mulVec_sub, hxy, sub_self]
  have hs : ∀ i : Fin r, v i.succ = 0 := fun i => by
    rw [← nfMat_mulVec_castSucc c v i, key]; rfl
  have hl : c ⬝ᵥ v = 0 := by rw [← nfMat_mulVec_last c v, key]; rfl
  have h0v : v 0 = 0 := by
    rw [dotProduct, Fin.sum_univ_succ] at hl
    simp only [hs, mul_zero, Finset.sum_const_zero, add_zero] at hl
    exact (mul_eq_zero.mp hl).resolve_left h0
  have : v = 0 := by
    funext j
    induction j using Fin.cases with
    | zero => exact h0v
    | succ i => exact hs i
  exact sub_eq_zero.mp this

theorem eL_vecMul_nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    eL r k ᵥ* nfMat c = c := by
  funext j
  simp [eL, Matrix.vecMul, dotProduct, nfMat, Pi.single_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem shiftCompanionLastRowMatrix_mulVec_firstBasis {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    nfMat c *ᵥ (fun i : Fin (r + 1) => if (i : ℕ) = 0 then (1 : k) else 0) = c 0 • eL r k := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [nfMat, Matrix.mulVec, dotProduct, eL]
  | cast i =>
    rw [nfMat_mulVec_castSucc]
    simp [eL, Pi.single_apply, Fin.castSucc_ne_last]

theorem glNormal_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 →
    ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  intro k _ r a h0
  have hu : IsUnit (GlobalTheory.JR.Step.nfMat a.2.1) :=
    Matrix.mulVec_injective_iff_isUnit.mp (GlobalTheory.JR.Step.nfMat_injective a.2.1 h0)
  refine ⟨hu.unit, GlobalTheory.JR.Step.blocks ((hu.unit : Matrix _ _ k) * companion a.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix _ _ k)), ?_⟩
  have hg : ((hu.unit : GL (Fin (r + 1)) k) : Matrix _ _ k) = GlobalTheory.JR.Step.nfMat a.2.1 := rfl
  have hinv : GlobalTheory.JR.Step.eL r k ᵥ* (GlobalTheory.JR.Step.nfMat a.2.1) = a.2.1 := GlobalTheory.JR.Step.eL_vecMul_nfMat a.2.1
  unfold act sec GlobalTheory.JR.Step.lift
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact (GlobalTheory.JR.Step.full_blocks _).symm
  · simp only [hg]; exact GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis a.2.1
  · show a.2.1 ᵥ* _ = _
    have hgi : GlobalTheory.JR.Step.nfMat a.2.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = 1 := by
      exact hu.unit.mul_inv
    have e : (GlobalTheory.JR.Step.eL r k ᵥ* GlobalTheory.JR.Step.nfMat a.2.1) ᵥ*
        ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = GlobalTheory.JR.Step.eL r k := by
      rw [Matrix.vecMul_vecMul, hgi, Matrix.vecMul_one]
    rw [hinv] at e
    exact e

end GlobalTheory.JR.Step
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step.ActEmbLift

theorem embHom_mul_full_mul (k : Type) [CommRing k] (r : ℕ) (g h : Matrix (Fin r) (Fin r) k) (Z : Gl r k) :
    embHom r k g * full Z * embHom r k h = full (g * Z.1 * h, g *ᵥ Z.2.1, Z.2.2.1 ᵥ* h, Z.2.2.2) := by
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, full, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

theorem embHom_mulVec_eL (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    embHom r k g *ᵥ eL r k = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.mulVec_single_one]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

theorem eL_vecMul_embHom (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    eL r k ᵥ* embHom r k g = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.single_one_vecMul]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

theorem act_emb_lift (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k) :
    act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  have hinv : ((emb r k g)⁻¹ : GL (Fin (r + 1)) k) = emb r k g⁻¹ := (map_inv _ _).symm
  simp only [act, lift, hinv, emb, Units.coe_map, MonoidHom.coe_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact embHom_mul_full_mul k r _ _ Z
  · simp only [Matrix.mulVec_smul, embHom_mulVec_eL]
  · exact eL_vecMul_embHom k r _

end GlobalTheory.JR.Step.ActEmbLift
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitGLift

variable {k : Type} [CommRing k] {r : ℕ}

theorem full_apply_cc (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_cl (Y : Gl r k) (a : Fin r) : full Y (Fin.castSucc a) (Fin.last r) = Y.2.1 a := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_lc (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_ll (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

end GlobalTheory.JR.UnitGLift

namespace GlobalTheory.JR.UnitGLift

theorem norm_full_le_one_iff {F : Type} [NormedField F] {r : ℕ} (Z : Gl r F) :
    (∀ i j, ‖full Z i j‖ ≤ 1) ↔
      ((∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1) := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full_apply_cc] using h (Fin.castSucc i) (Fin.castSucc j)
    · simpa [full_apply_cl] using h (Fin.castSucc i) (Fin.last r)
    · simpa [full_apply_lc] using h (Fin.last r) (Fin.castSucc j)
    · simpa [full_apply_ll] using h (Fin.last r) (Fin.last r)
  · rintro ⟨h1, h2, h3, h4⟩ i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_ll] using h4
      | cast j => simpa [full_apply_lc] using h3 j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_cl] using h2 i
      | cast j => simpa [full_apply_cc] using h1 i j

theorem norm_eL_le_one {F : Type} [NormedField F] {r : ℕ} (i : Fin (r + 1)) :
    ‖GlobalTheory.JR.Step.eL r F i‖ ≤ 1 := by
  unfold GlobalTheory.JR.Step.eL
  by_cases h : i = Fin.last r
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem unitG_lift : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 →
    unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  intro F _ r Z μ l hμ
  have hb : ∀ i, ‖(μ • GlobalTheory.JR.Step.eL r F) i‖ ≤ 1 := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ hμ (norm_nonneg _) (norm_eL_le_one i)
  have hmem : GlobalTheory.JR.Step.lift Z μ l ∈
      {Y : Gl (r + 1) F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} ↔
      (Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
        ∧ ‖l‖ ≤ 1) := by
    simp only [Set.mem_setOf_eq, GlobalTheory.JR.Step.lift]
    rw [norm_full_le_one_iff]
    exact ⟨fun ⟨h1, _, _, h4⟩ => ⟨h1, h4⟩, fun ⟨h1, h4⟩ => ⟨h1, hb, norm_eL_le_one, h4⟩⟩
  unfold unitG
  by_cases hZ : Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
  · by_cases hl : ‖l‖ ≤ 1
    · rw [Set.indicator_of_mem (hmem.2 ⟨hZ, hl⟩), Set.indicator_of_mem hZ, if_pos hl]
      simp
    · rw [Set.indicator_of_notMem (fun h => hl (hmem.1 h).2), if_neg hl, zero_mul]
  · rw [Set.indicator_of_notMem (fun h => hZ (hmem.1 h).1), Set.indicator_of_notMem hZ, mul_zero]

end GlobalTheory.JR.UnitGLift
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem forall_full_entries_iff {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) (P : k → Prop) :
    (∀ i j, P (full Y i j)) ↔
      (∀ i j, P (Y.1 i j)) ∧ (∀ i, P (Y.2.1 i)) ∧ (∀ j, P (Y.2.2.1 j)) ∧ P Y.2.2.2 := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full] using h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
    · simpa [full] using h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr (0 : Fin 1)))
    · simpa [full] using h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inl j))
    · simpa [full] using h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inr (0 : Fin 1)))
  · rintro ⟨h1, h2, h3, h4⟩ i j
    simp only [full, Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b
    · simpa using h1 a b
    · simpa using h2 a
    · simpa using h3 b
    · simpa using h4

theorem unitU_liftH_of_norm_le_one {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ ≤ 1) :
    unitU (r + 1) F E (liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by
  classical
  have hA : (∀ i j, ‖full X.toGl i j‖ ≤ 1) ↔
      (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 := by
    rw [forall_full_entries_iff X.toGl (fun x => ‖x‖ ≤ 1)]
    simp only [Hn.toGl, Pi.star_apply, Unram.norm_star (F := F), norm_algebraMap']
    tauto
  have hb : ∀ i, ‖(ν • eL r E) i‖ ≤ 1 := by
    intro i
    by_cases hi : i = Fin.last r
    · subst hi; simpa [eL] using hν
    · simp [eL, Pi.single_eq_of_ne hi]
  unfold unitU
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  have e : ((∀ i j, ‖(liftH X ν l).1.1 i j‖ ≤ 1) ∧ (∀ i, ‖(liftH X ν l).2.1 i‖ ≤ 1) ∧ ‖(liftH X ν l).2.2‖ ≤ 1) ↔
      (‖l‖ ≤ 1 ∧ (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1) := by
    change ((∀ i j, ‖full X.toGl i j‖ ≤ 1) ∧ (∀ i, ‖(ν • eL r E) i‖ ≤ 1) ∧ ‖l‖ ≤ 1) ↔ _
    rw [hA]
    exact ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hb, h.1⟩⟩
  simp only [e]
  by_cases h1 : ‖l‖ ≤ 1 <;>
    by_cases h2 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 <;>
    simp only [h1, h2, if_true, if_false, true_and, false_and, and_self, mul_one, mul_zero, zero_mul, implies_true]

end GlobalTheory.JR.Step
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.GLift

theorem embHom_apply_cc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.castSucc j) = a i j := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc]

theorem embHom_apply_cl {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.last r) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embHom_apply_lc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.castSucc j) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embHom_apply_ll {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.last r) = 1 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_last]

theorem coe_emb {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    ((GlobalTheory.JR.Step.emb r F g : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F (g : Matrix (Fin r) (Fin r) F) := rfl

theorem coe_emb_inv {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    (((GlobalTheory.JR.Step.emb r F g)⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
  rw [← map_inv]; rfl

theorem emb_preimage_glO : ∀ (F : Type) [NormedField F] (r : ℕ),
    ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  intro F _ r
  ext g
  simp only [Set.mem_preimage, glO, Set.mem_setOf_eq, coe_emb, coe_emb_inv]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    rwa [embHom_apply_cc, embHom_apply_cc] at this
  · intro h i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [embHom_apply_ll]
    · simp [embHom_apply_lc]
    · simp [embHom_apply_cl]
    · rw [embHom_apply_cc, embHom_apply_cc]; exact h i j

end GlobalTheory.JR.GLift
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Step.EmbClosed

theorem embHom_castSucc {r : ℕ} {k : Type} [CommRing k] (g : Matrix (Fin r) (Fin r) k) (i j : Fin r) :
    embHom r k g (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embHom, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]

theorem continuous_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    Continuous (embHom r F) := by
  show Continuous fun g : Matrix (Fin r) (Fin r) F =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
    continuous_const).matrix_reindex _ _

theorem isClosedEmbedding_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    IsClosedEmbedding (embHom r F) :=
  Function.LeftInverse.isClosedEmbedding
    (f := fun x : Matrix (Fin (r + 1)) (Fin (r + 1)) F => x.submatrix Fin.castSucc Fin.castSucc)
    (fun g => by ext i j; exact embHom_castSucc g i j)
    (Continuous.matrix_submatrix continuous_id _ _) (continuous_embHom r F)

theorem isClosedEmbedding_emb (F : Type) [NontriviallyNormedField F] (r : ℕ) :
    IsClosedEmbedding (emb r F) := by
  have hE := isClosedEmbedding_embHom r F
  let Φ : Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ →
      Matrix (Fin (r + 1)) (Fin (r + 1)) F × (Matrix (Fin (r + 1)) (Fin (r + 1)) F)ᵐᵒᵖ :=
    Prod.map (embHom r F) (MulOpposite.op ∘ embHom r F ∘ MulOpposite.unop)
  have hΦ : IsClosedEmbedding Φ := by
    refine hE.prodMap ?_
    exact MulOpposite.opHomeomorph.isClosedEmbedding.comp
      (hE.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hcomm : Units.embedProduct _ ∘ emb r F = Φ ∘ Units.embedProduct _ := by
    funext g
    rfl
  rw [← (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin (r + 1)) (Fin (r + 1)) F)).of_comp_iff, hcomm]
  exact hΦ.comp Units.isClosedEmbedding_embedProduct

end GlobalTheory.JR.Step.EmbClosed
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem isClosedEmbedding_embHom (r : ℕ) (E : Type) [CommRing E] [TopologicalSpace E] [T2Space E] :
    Topology.IsClosedEmbedding (embHom r E) := by
  have hc : Continuous (embHom r E) := by
    change Continuous fun g : Matrix (Fin r) (Fin r) E =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
    exact (continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _
  have hl : Function.LeftInverse
      (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) E => M.submatrix (Fin.castAdd 1) (Fin.castAdd 1))
      (embHom r E) := by
    intro g
    ext i j
    change (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
      (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = g i j
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  exact hl.isClosedEmbedding (continuous_id.matrix_submatrix _ _) hc

theorem isClosed_unitaryGroup (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) := by
  have : (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) = {M | M * Mᴴ = 1} := by
    ext M
    exact Matrix.mem_unitaryGroup_iff
  rw [this]
  exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const

theorem isClosedEmbedding_uEmb (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := by
  have h1 : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin (r + 1)) E → Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
    (isClosed_unitaryGroup (r + 1) E).isClosedEmbedding_subtypeVal
  have h0 : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) :=
    (isClosed_unitaryGroup r E).isClosedEmbedding_subtypeVal
  rw [← h1.of_comp_iff]
  exact (isClosedEmbedding_embHom r E).comp h0

end GlobalTheory.JR.Step
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧ Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  first | exact @GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | exact GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | (intros; apply GlobalTheory.CofinGen.exists_equiv_pi_prod_finite <;> assumption)
end

section

open Formalism.NG

theorem _root_.GlobalTheory.T.length_addMonoidHom_finite_group_fractionQuotient_le : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] KO O)
    (A : Type) [AddCommGroup A] [Finite A],
    Module.length O (A →+ M) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (Nat.card A) : ℕ∞) := by
  first | exact @GlobalTheory.HomLen.length_addMonoidHom_le | exact GlobalTheory.HomLen.length_addMonoidHom_le | (intros; apply GlobalTheory.HomLen.length_addMonoidHom_le <;> assumption)
end

section


theorem _root_.GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ) (x : GL (Fin r) K), (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) = Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  first | exact @GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint | exact GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint | (intros; apply GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint <;> assumption)
end
