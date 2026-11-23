module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle076
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.NilpotentSubgroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
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
import Mathlib.Tactic.Lemma
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

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh

open GlobalTheory.LeadingMinorInv

namespace OmgRight

end OmgRight

open OmgRight

open Matrix in
variable {k r : ℕ} in
private lemma inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH {x : _root_.Formalism.FourierDecayAlt.Q.Mx k r} (hx : x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    x⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk k r * xᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_eq_UH hx

open Matrix in
variable {k r : ℕ} in
private lemma hpk_mul_hpk_mul_eq_self (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) :
    _root_.Formalism.QuantumDeterminants.Hpk k r * (_root_.Formalism.QuantumDeterminants.Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
private lemma hpk_conjTranspose_eq_self' : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose

open Matrix in
variable {k r : ℕ} in
private lemma adjugate_upUni_last_apply {m : ℕ} {U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) (a : Fin (m + 1)) :
    U.adjugate (Fin.last m) a = if a = Fin.last m then 1 else 0 := by
  rw [adjugate_apply, det_of_upperTriangular]
  · simp [updateRow_apply, Pi.single_apply, hU.2]
  · intro i j hij
    simp only [updateRow_apply]
    split_ifs with h
    · subst h
      rw [Pi.single_apply, if_neg]
      exact (hij.trans_le (Fin.le_last _)).ne
    · exact hU.1 i j hij

open Matrix in
variable {k r : ℕ} in
private lemma flagMat_mulVec_eq_sum_smul_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]

open Matrix in
variable {k r : ℕ} in
private lemma rW_mulVec_adjugate_zhat_single_last_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_smul_fvec]
  simp [mulVec_single_one, conjTranspose_apply]

open Matrix in
variable {k r : ℕ} in
private lemma gram_eq_conjTranspose_hpk_mul_flagMat_mul (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
private lemma prW_mulVec_eq_of_mem_nset_of_tail_eq_zero {z' : Fin (2 * r + k + 1) → ℂ} {m : _root_.Formalism.FourierDecayAlt.Q.Mx k r}
    (hm : m ∈ _root_.Formalism.QuantumDeterminants.Nset k r) {p : Fin (2 * r + k + 1) → ℂ}
    (hp : ∀ j : Fin (2 * r + k + 1), r + k < ↑j → p j = 0) :
    _root_.Formalism.FourierDecayAlt.D.prW k r z' (m *ᵥ p) = _root_.Formalism.FourierDecayAlt.D.prW k r z' p := by
  have hNC := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).2
  have hb : (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then (m *ᵥ p) i else 0) =
      (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then p i else 0) := by
    ext i
    split_ifs with hi
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · rw [hNC i i hi.2 (min_le_left _ _)]
        simp
      · intro j _ hji
        by_cases hj : (j : ℕ) ≤ r + k
        · rw [hNC i j hj (le_trans (min_le_right _ _) hi.1), if_neg (Ne.symm hji)]
          simp
        · rw [hp j (by omega)]
          simp
      · simp
    · rfl
  simp only [_root_.Formalism.FourierDecayAlt.D.prW]
  rw [hb]

open Matrix in
variable {k r : ℕ} in
private lemma mulVec_adjugate_single_last_apply_eq_zero_of_lt (z' : Fin (2 * r + k + 1) → ℂ)
    (Q : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) (j : Fin (2 * r + k + 1))
    (hj : r + k < ↑j) :
    (Q *ᵥ ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ *ᵥ
      Pi.single (Fin.last r) 1)) j = 0 := by
  have hJP : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) i c,
      (_root_.Formalism.QuantumDeterminants.Hpk k r * X) i c = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i * X (_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i) c := by
    intro X i c
    have hJa : ∀ i l, _root_.Formalism.QuantumDeterminants.Hpk k r i l =
        if l = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i then _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i else 0 :=
      fun i l => _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply i l
    rw [Matrix.mul_apply]
    simp only [hJa, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hj2 := j.isLt
  obtain ⟨b, hb⟩ : ∃ b : Fin r, (b : ℕ) = 2 * r + k - j := ⟨⟨2 * r + k - j, by omega⟩, rfl⟩
  have hpi : _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r (_root_.Formalism.QuantumDeterminants.eI k r b) = j := by
    have hb2 := b.isLt
    apply Fin.ext
    rw [_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI_val, if_neg] <;> simp only [_root_.Formalism.QuantumDeterminants.eI] <;> omega
  have key : (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ *
      (Q * (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ) =
      ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugate *
        (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')))ᴴ := by
    rw [conjTranspose_mul (adjugate _), conjTranspose_mul Qᴴ, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h1 := congrFun (congrFun key (Fin.castSucc b)) (Fin.last r)
  rw [adjugate_mul] at h1
  simp only [conjTranspose_apply, Matrix.smul_apply, one_apply,
    if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1
  rw [conjTranspose_mul, hpk_conjTranspose_eq_self', Matrix.mul_assoc, Matrix.mul_apply,
    Finset.sum_eq_single (_root_.Formalism.QuantumDeterminants.eI k r b)] at h1
  · rw [hJP, hpi] at h1
    have heps := _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self (k := k) (r := r) (_root_.Formalism.QuantumDeterminants.eI k r b)
    have hF : (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ (Fin.castSucc b) (_root_.Formalism.QuantumDeterminants.eI k r b) = 1 := by
      simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec]
    rw [hF, one_mul] at h1
    simp only [Matrix.one_apply, if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1
    rw [mulVec_mulVec]
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rcases mul_eq_zero.1 h1 with h | h
    · rw [h, zero_mul] at heps
      exact absurd heps zero_ne_one
    · exact h
  · intro l _ hl
    simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec, Pi.single_apply, hl]
  · simp


open Matrix in
theorem _root_.GlobalTheory.WigSh.omg_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (g m : _root_.Formalism.FourierDecayAlt.Q.Mx k r), _root_.Formalism.QuantumDeterminants.inWb k r z → _root_.Formalism.QuantumDeterminants.inWb k r z' →
    g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) → m ∈ _root_.Formalism.QuantumDeterminants.Nset k r →
    _root_.GlobalTheory.WigSh.omg k r z z' (g * m) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  intro k r z z' g m _ hz' _ hm
  obtain ⟨U, hU, hmF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z' hz' m hm
  have hmUH : m ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).1
  have hQm : _root_.Formalism.QuantumDeterminants.Hpk k r * (g * m)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) := by
    rw [inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self]
  have hC : (m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z))ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') =
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
        (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')) * U := by
    rw [conjTranspose_mul m⁻¹, inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
      Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self, hmF]
  have he : U.adjugateᴴ *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1 := by
    ext a
    simp [mulVec_single_one, conjTranspose_apply, adjugate_upUni_last_apply hU, Pi.single_apply]
  rw [rW_mulVec_adjugate_zhat_single_last_eq, rW_mulVec_adjugate_zhat_single_last_eq, gram_eq_conjTranspose_hpk_mul_flagMat_mul, gram_eq_conjTranspose_hpk_mul_flagMat_mul, hQm, hC, adjugate_mul_distrib, conjTranspose_mul,
    ← mulVec_mulVec _ (adjugate _)ᴴ, he, ← mulVec_mulVec _ m⁻¹]
  exact prW_mulVec_eq_of_mem_nset_of_tail_eq_zero ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.nilpotent_subgroup k r).2.2 m hm)
    (mulVec_adjugate_single_last_apply_eq_zero_of_lt _ _)

end GlobalTheory.WigSh
end
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV
open scoped BigOperators

namespace GlobalTheory.GoodDepth.Zero

theorem cut (K s B : ℕ) (e : ℕ → ℕ) : ∃ pc : Fin s → ℕ → ℕ,
    (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧
    (∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → (∀ k, e k ≠ 0 → 1 ≤ k ∧ k ≤ K) → ∀ k, ∑ u, pc u k = e k) := by
  by_cases h : ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B
  · obtain ⟨pc, h1, h2, h3⟩ := GlobalTheory.exists_cut_columns_bounded_width K s B e h
    refine ⟨pc, h2, fun _ hsupp k => ?_⟩
    by_cases hk : k ∈ Finset.Icc 1 K
    · exact h1 k hk
    · have hek : e k = 0 := by
        by_contra hne
        exact hk (Finset.mem_Icc.mpr (hsupp k hne))
      rw [hek]
      exact Finset.sum_eq_zero fun u _ => h3 u k hk
  · exact ⟨fun _ _ => 0, fun _ => by simp, fun h' => absurd h' h⟩

theorem monAl_le_first (K rk : ℕ) (e : ℕ → ℕ) (ρ : ℕ) :
    monAl K rk e ρ ≤ ∑ k ∈ Finset.Icc 1 K, e k := by
  unfold monAl
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_Icc] at hk ⊢
  exact ⟨by omega, hk.2.trans (min_le_left _ _)⟩

theorem zero_of_pkg (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (Pk : RF.PkgZero P l) : Pk.ν ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hz : ∀ z ∈ Pk.Z, ∀ g a k, Pk.ga z g a k = 0 := by
      intro z hz g a k
      by_contra hne
      have hs := Pk.supp z hz g a k hne
      have h0 : Pk.s * (l - 1) = 0 := by simp [hl]
      have hf := (Pk.first z hz g a).trans h0.le
      exact hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k
        (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))
    have h := Pk.val (fun _ => []) (by simp) (by simp)
      (by intro o ho g a k; simp [hz o ho g a k])
    simpa using h
  · have hcut : ∀ z g a, ∃ pc : Fin Pk.s → ℕ → ℕ,
        (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧
        (z ∈ Pk.Z → ∀ k, ∑ u, pc u k = Pk.ga z g a k) := by
      intro z g a
      obtain ⟨pc, h1, h2⟩ := cut Pk.K Pk.s (l - 1) (Pk.ga z g a)
      exact ⟨pc, h1, fun hz => h2 (Pk.first z hz g a)
        fun k hk => ⟨(Pk.supp z hz g a k hk).1, (Pk.supp z hz g a k hk).2.2⟩⟩
    choose pc hpc1 hpc2 using hcut
    let blk : P.Pl → Fin 2 × Fin Pk.s → RF.GlobalTheory P.d × ℝ :=
      fun z q => (RF.GlobalTheory.mon q.1 (fun a => pc z q.1 a q.2) Pk.K, 0)
    let L : P.Pl → List (RF.GlobalTheory P.d × ℝ) :=
      fun z => (Finset.univ : Finset (Fin 2 × Fin Pk.s)).toList.map (blk z)
    have hsum0 : ∑ o ∈ Pk.Z, ((L o).map Prod.snd).sum = 0 := by
      simp [L, blk]
    refine (Pk.val L ?_ ?_ ?_).trans hsum0.le
    · intro o _ p hp
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      refine (hM Pk.R.C Pk.R.V P.d (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) q.1
        (fun a => pc o q.1 a q.2) Pk.K).2 ?_
      intro a ρ
      rw [Pk.R.hVl]
      have h1 := (monAl_le_first Pk.K ((Pk.R.X o).rkF q.1 a) (pc o q.1 a q.2) ρ).trans (hpc1 o q.1 a q.2)
      omega
    · have hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K := by
        intro o
        simp only [L, List.map_map]
        rw [Finset.sum_map_toList]
        simp [blk, RF.GlobalTheory.what₂]
      rw [Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul]
      calc Pk.Z.card * (2 * Pk.s * Pk.K) = 2 * Pk.K * Pk.s * Pk.Z.card := by ring
        _ ≤ Pk.nW := Pk.what₂
    · intro o ho g a k
      have hw : ∀ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k =
          if q.1 = g then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0)
          else 0 := by
        rintro ⟨g', u⟩
        by_cases hg : g' = g
        · subst hg
          simp [blk, RF.GlobalTheory.wt]
        · simp [blk, RF.GlobalTheory.wt, hg, Ne.symm hg]
      calc ((L o).map fun p => p.1.wt (Pk.R.X o) g a k).sum
          = ∑ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k := by
            simp only [L, List.map_map]
            rw [Finset.sum_map_toList]
            rfl
        _ = ∑ q : Fin 2 × Fin Pk.s, if q.1 = g then
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0) else 0 :=
            Finset.sum_congr rfl fun q _ => hw q
        _ = ∑ u : Fin Pk.s,
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a u k else 0) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
        _ = Pk.ga o g a k := by
            by_cases hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a)
            · simp only [if_pos hk]
              exact hpc2 o g a ho k
            · simp only [if_neg hk, Finset.sum_const_zero]
              symm
              by_contra hne
              have hs := Pk.supp o ho g a k hne
              exact hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩

theorem zero_of_pkgC (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (Pk : RF.PkgZeroC P l) : Pk.ν ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hz : ∀ z σ k, Pk.gaC z σ k = 0 := by
      intro z σ k
      by_contra hne
      have hs := Pk.supp z σ k hne
      have h0 : Pk.s * (l - 1) = 0 := by simp [hl]
      have hf := (Pk.first z σ).trans h0.le
      exact hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k
        (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))
    have h := Pk.val (fun _ => []) (by simp) (by simp) (by simp)
      (by intro o σ k; simp [hz o σ k])
    simpa using h
  · have hcut : ∀ z σ, ∃ pc : Fin Pk.s → ℕ → ℕ,
        (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧ (∀ k, ∑ u, pc u k = Pk.gaC z σ k) := by
      intro z σ
      obtain ⟨pc, h1, h2⟩ := cut Pk.K Pk.s (l - 1) (Pk.gaC z σ)
      exact ⟨pc, h1, h2 (Pk.first z σ)
        fun k hk => ⟨(Pk.supp z σ k hk).1, (Pk.supp z σ k hk).2.2⟩⟩
    choose pc hpc1 hpc2 using hcut
    let ee : P.Pl → ZMod 2 × Fin Pk.s → ZMod 2 → ℕ → ℕ :=
      fun z q a k => if a = q.1 then pc z q.1 q.2 k else 0
    let blk : P.Pl → ZMod 2 × Fin Pk.s → RF.GlobalTheory 2 × ℝ :=
      fun z q => (RF.GlobalTheory.mon 0 (ee z q) Pk.K, 0)
    let L : P.Pl → List (RF.GlobalTheory 2 × ℝ) :=
      fun z => (Finset.univ : Finset (ZMod 2 × Fin Pk.s)).toList.map (blk z)
    have hsum0 : ∑ o, ((L o).map Prod.snd).sum = 0 := by
      simp [L, blk]
    refine (Pk.val L ?_ ?_ ?_ ?_).trans hsum0.le
    · intro o p hp
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      refine (hM Pk.R.C Pk.R.V 2 (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) 0 (ee o q) Pk.K).2 ?_
      intro a ρ
      rw [Pk.R.hVl]
      have h1 : ∑ k ∈ Finset.Icc 1 Pk.K, ee o q a k ≤ l - 1 := by
        by_cases ha : a = q.1
        · simpa [ee, ha] using hpc1 o q.1 q.2
        · simp [ee, ha]
      have h2 := (monAl_le_first Pk.K ((Pk.R.X o).rkF 0 a) (ee o q a) ρ).trans h1
      omega
    · intro o p hp g e N hpe
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hpe
      exact ⟨q.1, fun a k ha => by simp [ee, ha]⟩
    · have hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K := by
        intro o
        simp only [L, List.map_map]
        rw [Finset.sum_map_toList]
        simp [blk, RF.GlobalTheory.what₂]
      rw [Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul, Finset.card_univ]
      calc 2 * (Fintype.card P.Pl * (2 * Pk.s * Pk.K)) = 4 * Pk.K * Pk.s * Fintype.card P.Pl := by ring
        _ ≤ Pk.nW := Pk.what₂
    · intro o σ k
      have hw : ∀ q : ZMod 2 × Fin Pk.s,
          (blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k =
          if q.1 = σ then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0)
          else 0 := by
        rintro ⟨a, u⟩
        by_cases ha : a = σ
        · subst ha
          simp [blk, ee, RF.GlobalTheory.wt]
        · simp [blk, ee, RF.GlobalTheory.wt, ha, Ne.symm ha]
      calc ((L o).map fun p => p.1.wt (Pk.R.X o) 0 σ k + p.1.wt (Pk.R.X o) 1 (σ + 1) k).sum
          = ∑ q : ZMod 2 × Fin Pk.s,
              ((blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k) := by
            simp only [L, List.map_map]
            rw [Finset.sum_map_toList]
            rfl
        _ = ∑ q : ZMod 2 × Fin Pk.s, if q.1 = σ then
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0) else 0 :=
            Finset.sum_congr rfl fun q _ => hw q
        _ = ∑ u : Fin Pk.s,
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ u k else 0) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single σ]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
        _ = Pk.gaC o σ k := by
            by_cases hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ)
            · simp only [if_pos hk]
              exact hpc2 o σ k
            · simp only [if_neg hk, Finset.sum_const_zero]
              symm
              by_contra hne
              have hs := Pk.supp o σ k hne
              exact hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩

end GlobalTheory.GoodDepth.Zero

theorem GlobalTheory.GoodDepth.zeroBd : GlobalTheory.GoodDepth.ZeroBd :=
  ⟨fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkg GlobalTheory.T.monomialBlock_supply_both_typings.2 P l Pk,
    fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkgC GlobalTheory.T.monomialBlock_supply_both_typings.2 P l Pk⟩
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupTau

theorem hsq_nonneg (r : ℕ) (T b : ℝ) : 0 ≤ Hsq r T b := by
  unfold Hsq
  apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
  rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
  positivity

theorem arith (a a' d e A A' : ℝ) (n : ℕ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : 0 < d) (he : 0 < e) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (h : a ^ 2 * d / e ≤ A ^ n) (h' : a' ^ 2 * d / e ≤ A' ^ n) :
    a' * a * d / e ≤ Real.sqrt (A * A') ^ n := by
  have h2 : (Real.sqrt (A * A') ^ n) ^ 2 = A ^ n * A' ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hA hA'), mul_pow]
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1
  rw [h2]
  calc (a' * a * d / e) ^ 2 = (a ^ 2 * d / e) * (a' ^ 2 * d / e) := by ring
    _ ≤ A ^ n * A' ^ n := mul_le_mul h h' (by positivity) (by positivity)

end GlobalTheory.SupTau
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SuppliedPieri

theorem n1_add_eZ_le {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : I.card = ∑ i : Fin n, (if i ∈ I then 1 else 0) := by
    rw [Finset.sum_boole]; simp
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, eZ]
  split_ifs <;> omega

theorem JF_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (g : B.Mat k r) :
    B.JF D 0 g = 0 := by
  simp [B.JF, Formalism.QuantumDeterminants.besselJ]

end GlobalTheory.SuppliedPieri
end
