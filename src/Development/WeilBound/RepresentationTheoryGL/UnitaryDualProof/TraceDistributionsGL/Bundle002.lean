module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.LeviTransposeDistributions.BoundOneTwo
import GroundTheory.AutomorphicForms.GLnLocal
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_updateRow_one_last {n : ℕ} (v : Fin (n + 1) → k) :
    (updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) v).det = v (Fin.last n) := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [Matrix.updateRow_apply, Fin.castSucc_ne_last]
  · intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    rw [Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]

theorem exists_last_row {n : ℕ} (w : Fin (n + 1) → k) (hw : w ≠ 0) :
    ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := by
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hw
  have hm' : w m ≠ 0 := by simpa using hm
  have hM : ((updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)
      (fun j => w (Equiv.swap m (Fin.last n) j))).submatrix id (Equiv.swap m (Fin.last n))).det ≠ 0 := by
    rw [Matrix.det_permute', det_updateRow_one_last, Equiv.swap_apply_right]
    refine mul_ne_zero ?_ hm'
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap m (Fin.last n))) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, fun j => ?_⟩
  show ((updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)
      (fun j => w (Equiv.swap m (Fin.last n) j))).submatrix id (Equiv.swap m (Fin.last n))) (Fin.last n) j = w j
  simp [Matrix.submatrix_apply, Matrix.updateRow_self, Equiv.swap_apply_self]

theorem secSpec : SecSpec k := by
  intro n w hw j
  have h := exists_last_row w hw
  unfold sec
  rw [dite_eq_left h]
  exact h.choose_spec j

theorem cj_mul {n : ℕ} (a b : GL (Fin (n + 1)) k) (x : Mx k n) : cj (a * b) x = cj a (cj b x) := by
  simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem cj_one {n : ℕ} (x : Mx k n) : cj (1 : GL (Fin (n + 1)) k) x = x := by
  simp [cj]

def cjHomeo {n : ℕ} (g : GL (Fin (n + 1)) k) : Mx k n ≃ₜ Mx k n where
  toFun := cj g
  invFun := cj g⁻¹
  left_inv x := by rw [← cj_mul, inv_mul_cancel, cj_one]
  right_inv x := by rw [← cj_mul, mul_inv_cancel, cj_one]
  continuous_toFun := by unfold cj; fun_prop
  continuous_invFun := by unfold cj; fun_prop

theorem slice_cj_mem {n : ℕ} {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) (g : GL (Fin (n + 1)) k)
    (w : Vc k n) : (fun x => F (cj g x, w)) ∈ SB (Mx k n) := by
  change IsLocallyConstant F ∧ HasCompactSupport F at hF
  have hι : Topology.IsClosedEmbedding (fun y : Mx k n => (y, w)) := by
    refine ⟨isEmbedding_prodMkLeft w, ?_⟩
    have hr : Set.range (fun y : Mx k n => (y, w)) = Set.univ ×ˢ {w} := by
      ext ⟨a, b⟩
      simp [eq_comm]
    rw [hr]
    exact isClosed_univ.prod isClosed_singleton
  have hemb := hι.comp (cjHomeo g).isClosedEmbedding
  exact ⟨hF.1.comp_continuous hemb.continuous, hF.2.comp_isClosedEmbedding hemb⟩

theorem phiIndep : PhiIndep k := by
  intro n Λ hΛ F hF w hw s hs
  unfold phi
  rw [if_neg hw]
  have hrow : ∀ (g : GL (Fin (n + 1)) k) (j : Fin (n + 1)),
      (eLast k n ᵥ* (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) j = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j := by
    intro g j
    simp [eLast, Matrix.vecMul, dotProduct, Pi.single_apply]
  have ht : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j :=
    secSpec n w hw
  have e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      = eLast k n ᵥ* (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    funext j
    rw [hrow, hrow, ht, hs]
  have hp : sec w * s⁻¹ ∈ Mir k n := by
    change eLast k n ᵥ* ((sec w * s⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = eLast k n
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  have hf : (fun x => F (cj (sec w)⁻¹ x, w)) ∈ SB (Mx k n) := slice_cj_mem hF (sec w)⁻¹ w
  rw [← hΛ _ hp _ hf]
  congr 1
  funext x
  dsimp only [Function.comp_apply]
  rw [← cj_mul, inv_mul_cancel_left]

theorem phiLin : PhiLin k := by
  intro n Λ F _ G _ a b
  funext w
  unfold phi
  simp only [Pi.add_apply, Pi.smul_apply]
  split_ifs
  · simp
  · rw [← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1

theorem phiEquiv : PhiEquiv k := by
  intro n Λ hΛ F hF h w
  by_cases hw : w = 0
  · subst hw
    simp [phi, Matrix.mulVec_zero]
  · have hw' : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w ≠ 0 := by
      intro h0
      apply hw
      have e : ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ
          ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    rw [phiIndep n Λ hΛ F hF _ hw' (sec w * h) ?_]
    · unfold phi
      rw [if_neg hw]
      congr 1
      funext x
      dsimp only
      rw [← cj_mul, _root_.mul_inv_rev]
    · intro j
      rw [Units.val_mul, Matrix.mul_apply]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun x _ => by rw [secSpec n w hw x, mul_comm]

theorem ltEquiv (hE : PhiEquiv k) : LtEquiv k := by
  intro _ _ ν _ n Λ hΛ F hF h
  unfold lt
  have e : ∀ w, phi Λ (fun q : Mx k n × Vc k n => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) w
      = phi Λ F ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w) := fun w => hE n Λ hΛ F hF h w
  simp only [e]
  have hd : ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
  have key := integral_comp_mulVec_eq_smul ν (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) (fun v => phi Λ F v)
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd)
      = Matrix.GeneralLinearGroup.det h := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact Matrix.det_transpose _
  rw [hdet] at key
  exact key.trans (by simp [Complex.real_smul])

end PositivityTheory.RgUd.AB.Pf
end
end

section

noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def cutL {n : ℕ} (U : Set k) : (Mx k n → ℂ) →ₗ[ℂ] (GL (Fin (n + 1)) k → ℂ) where
  toFun ψ x := by
    classical
    exact if (x.val).det ∈ U then ψ x.val else 0
  map_add' ψ₁ ψ₂ := funext fun x => by
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
open Classical in
theorem cutL_apply {n : ℕ} (U : Set k) (ψ : Mx k n → ℂ) (x : GL (Fin (n + 1)) k) :
    cutL U ψ x = if (x.val).det ∈ U then ψ x.val else 0 := by
  classical
  rfl

theorem mem_SB_iff_supportedIn {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ f ∈ supportedIn (Set.univ : Set X) := by
  constructor
  · intro h
    exact ⟨h, Set.subset_univ _⟩
  · intro h
    exact h.1

theorem cutL_mem {n : ℕ} (U : Set k) (hU : IsClopen U) (h0 : (0 : k) ∉ U) {ψ : Mx k n → ℂ}
    (hψ : ψ ∈ SB (Mx k n)) : cutL U ψ ∈ SB (GL (Fin (n + 1)) k) := open Topology Filter in by
  have hE : IsEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
    refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
    · intro A hA
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_matrix_inv
      have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hd
    · intro u
      exact (Matrix.coe_units_inv u).symm
  have hdet : Continuous fun x : GL (Fin (n + 1)) k => (x.val).det :=
    Units.continuous_val.matrix_det
  constructor
  · have h1 : IsLocallyConstant (fun x : GL (Fin (n + 1)) k => ψ x.val) :=
      hψ.1.comp_continuous Units.continuous_val
    rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
    intro x
    by_cases hx : (x.val).det ∈ U
    · have h2 : ∀ᶠ x' in nhds x, (x'.val).det ∈ U :=
        hdet.continuousAt.preimage_mem_nhds (hU.isOpen.mem_nhds hx)
      filter_upwards [h2, h1 x] with x' hx' h'
      simp only [cutL_apply, if_pos hx, if_pos hx', h']
    · have h2 : ∀ᶠ x' in nhds x, (x'.val).det ∈ Uᶜ :=
        hdet.continuousAt.preimage_mem_nhds (hU.isClosed.isOpen_compl.mem_nhds hx)
      filter_upwards [h2] with x' hx'
      have hx'' : (x'.val).det ∉ U := hx'
      simp only [cutL_apply, if_neg hx, if_neg hx'']
  · have hK : IsCompact (tsupport ψ ∩ (fun A : Mx k n => A.det) ⁻¹' U) :=
      hψ.2.isCompact.inter_right (hU.isClosed.preimage continuous_id.matrix_det)
    have hKr : tsupport ψ ∩ (fun A : Mx k n => A.det) ⁻¹' U ⊆
        Set.range (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
      intro A hA
      have hd : A.det ≠ 0 := by
        intro h
        exact h0 (h ▸ hA.2)
      exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hd)).unit,
        IsUnit.unit_spec _⟩
    have hK' := hE.isInducing.isCompact_preimage' hK hKr
    refine HasCompactSupport.intro' hK' (hK.isClosed.preimage Units.continuous_val) ?_
    intro x hx
    rw [cutL_apply]
    split_ifs with h
    · exact image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨hm, h⟩)
    · rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_cj {n : ℕ} (p x : GL (Fin (n + 1)) k) :
    ((p * x * p⁻¹ : GL (Fin (n + 1)) k).val).det = (x.val).det := by
  simp only [Units.val_mul, Matrix.det_mul]
  rw [mul_right_comm, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.det_one, one_mul]

theorem cutL_cj {n : ℕ} (U : Set k) (p : GL (Fin (n + 1)) k) (ψ : Mx k n → ℂ) :
    cutL U (ψ ∘ cj p) = fun x => cutL U ψ (p * x * p⁻¹) := by
  funext x
  rw [cutL_apply, cutL_apply, det_cj]
  rfl

end PositivityTheory.RgUd.AB.Pf

namespace PositivityTheory.RgUd.AB.Pf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmA_of_core : CoreX k → ThmT k → ThmA k := open Topology Filter in by
  intro hC hT n Λ hP p f hf
  classical
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf.1
  let φ : SB (GL (Fin (n + 1)) k) := ⟨f, hf'⟩
  have hE : IsOpenEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
    have hEmb : IsEmbedding (Units.val : GL (Fin (n + 1)) k → Mx k n) := by
      refine Units.isEmbedding_val_mk' (f := Inv.inv) ?_ ?_
      · intro A hA
        apply ContinuousAt.continuousWithinAt
        apply continuousAt_matrix_inv
        have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ hd
      · intro u
        exact (Matrix.coe_units_inv u).symm
    refine ⟨hEmb, ?_⟩
    have hr : Set.range (Units.val : GL (Fin (n + 1)) k → Mx k n) =
        {A | A.det ≠ 0} := by
      ext A
      constructor
      · rintro ⟨u, rfl⟩
        exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
      · intro h
        exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)).unit,
          IsUnit.unit_spec _⟩
    rw [hr]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  let ext : Mx k n → ℂ := fun y => if h : IsUnit y then φ.1 h.unit else 0
  have ext_val (u : GL (Fin (n + 1)) k) : ext u.val = φ.1 u := by
    dsimp [ext]
    rw [dif_pos u.isUnit, IsUnit.unit_of_val_units]
  have ext_mem : ext ∈ SB (Mx k n) := by
    have hK : IsCompact (Units.val '' tsupport φ.1) := φ.2.2.isCompact.image hE.continuous
    have hKc : IsClosed (Units.val '' tsupport φ.1) := hK.isClosed
    have hzero : ∀ y, y ∉ Units.val '' tsupport φ.1 → ext y = 0 := by
      intro y hy
      dsimp [ext]
      split_ifs with h
      · exact image_eq_zero_of_notMem_tsupport (fun hm => hy ⟨h.unit, hm, h.unit_spec⟩)
      · rfl
    refine ⟨?_, HasCompactSupport.intro' hK hKc hzero⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    by_cases hy : IsUnit y
    · obtain ⟨u, rfl⟩ := hy
      have hφ := (IsLocallyConstant.iff_eventually_eq _).1 φ.2.1 u
      rw [← hE.map_nhds_eq, Filter.eventually_map]
      filter_upwards [hφ] with u' hu'
      rw [ext_val, ext_val, hu']
    · have hy' : y ∉ Units.val '' tsupport φ.1 := by
        rintro ⟨u, -, rfl⟩
        exact hy u.isUnit
      filter_upwards [hKc.isOpen_compl.mem_nhds hy'] with y' hy''
      rw [hzero y' hy'', hzero y hy']
  let ψ : SB (Mx k n) := ⟨ext, ext_mem⟩
  have hdet : Continuous fun x : GL (Fin (n + 1)) k => (x.val).det :=
    (continuous_id.matrix_det).comp Units.continuous_val
  obtain ⟨U, hU, hCU, h0⟩ := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.exists_clopen_local
    ((fun x : GL (Fin (n + 1)) k => (x.val).det) '' tsupport f)
    (hf'.2.isCompact.image hdet)
    (by
      rintro ⟨x, -, hx⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero hx)
  have hfeq : cutL U ψ.1 = f := by
    funext x
    rw [cutL_apply]
    split_ifs with h
    · exact ext_val x
    · symm
      by_contra hne
      exact h (hCU ⟨x, subset_tsupport _ hne, rfl⟩)
  let Λ' : (Mx k n → ℂ) →ₗ[ℂ] ℂ := Λ ∘ₗ cutL U
  have hPX : PInvX Λ' := by
    intro q hq g hg
    show Λ (cutL U (g ∘ cj q)) = Λ (cutL U g)
    rw [cutL_cj]
    exact hP q hq _ ((mem_SB_iff_supportedIn _).mp (cutL_mem U hU h0 hg))
  have hGX := hC hT n Λ' hPX p ψ.1 ψ.2
  have e1 : (fun g => f (p * g * p⁻¹)) = cutL U (ψ.1 ∘ cj p) := by
    rw [cutL_cj, hfeq]
  have e2 : Λ (cutL U (ψ.1 ∘ cj p)) = Λ (cutL U ψ.1) := hGX
  rw [e1, e2, hfeq]

end PositivityTheory.RgUd.AB.Pf
end
end
