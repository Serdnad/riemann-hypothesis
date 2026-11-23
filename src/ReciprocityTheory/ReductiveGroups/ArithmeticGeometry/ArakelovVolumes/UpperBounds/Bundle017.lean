module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

open Filter Topology Set Matrix NumberField ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def eΨ : Fin X.Ψ.card ≃ X.Ψ := X.Ψ.equivFin.symm

def Zmap (z : V (nd X)) : V (nD X.Ψ.card X.p0 (r - X.p0)) :=
  WithLp.toLp 2 fun j => ExF.Zt X z (eΨ X (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1 (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2

theorem Zof_Zmap (z : V (nd X)) (k : Fin X.Ψ.card) : Zof (Zmap X z) k = ExF.Zt X z (eΨ X k) := by
  ext a b
  change ExF.Zt X z (eΨ X (finProdFinEquiv.symm (finProdFinEquiv (k, finProdFinEquiv (a, b)))).1) _ _ = _
  simp only [Equiv.symm_apply_apply]

private theorem contDiff_nM_apply (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => ExF.nM X z τ a b := by
  unfold ExF.nM
  simp only [mat, Matrix.of_apply, nmat]
  split_ifs
  · first
    | exact ((contDiff_piLp _).mp contDiff_id) _
    | fun_prop
  · exact contDiff_const
  · exact contDiff_const

private theorem det_n1_eq_one (z : V (nd X)) (τ : X.Ψ) : (ExF.n1 X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    change nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1
    simp [nmat]
  · intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    rw [Fin.lt_def] at hlt
    change nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0
    have h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i) := by
      rw [Fin.lt_def]; simp only [Fin.coe_castLE]; omega
    have h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.coe_castLE] at h; omega
    simp only [nmat, dif_neg h1, if_neg h2]

private theorem inv_n1_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (ExF.n1 X z τ)⁻¹ = (ExF.n1 X z τ).adjugate := by
  rw [Matrix.inv_def, det_n1_eq_one, Ring.inverse_one, one_smul]

private theorem contDiff_det_of_contDiff_entries {n : ℕ} (M : V (nd X) → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ContDiff ℂ ∞ fun z => M z i j) : ContDiff ℂ ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  first
  | exact contDiff_prod fun i _ => hM _ _
  | fun_prop

private theorem contDiff_adjugate_apply_of_contDiff_entries {n : ℕ} (M : V (nd X) → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ContDiff ℂ ∞ fun z => M z i j) (a b : Fin n) :
    ContDiff ℂ ∞ fun z => (M z).adjugate a b := by
  simp only [Matrix.adjugate_apply]
  apply contDiff_det_of_contDiff_entries
  intro i j
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hM i j

theorem Zmap_contDiff : ContDiff ℂ ∞ (Zmap X) := by
  have hn1 : ∀ τ : X.Ψ, ∀ i j, ContDiff ℂ ∞ fun z : V (nd X) => ExF.n1 X z τ i j :=
    fun τ i j => contDiff_nM_apply X τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
  have hW : ∀ τ : X.Ψ, ∀ b c, ContDiff ℂ ∞ fun z : V (nd X) => ExF.Wm X z τ b c :=
    fun τ b c => contDiff_nM_apply X τ (ExF.qI X b) (Fin.castLE X.p0_le c)
  refine (contDiff_piLp _).mpr fun j => ?_
  change ContDiff ℂ ∞ fun z : V (nd X) => ExF.Zt X z _ _ _
  simp only [ExF.Zt, Matrix.transpose_apply, inv_n1_eq_adjugate, Matrix.mul_apply]
  exact ContDiff.sum fun c _ => (hW _ _ _).mul (contDiff_adjugate_apply_of_contDiff_entries X (fun z => ExF.n1 X z _) (hn1 _) _ _)

theorem rh_Zmap (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    rh (Zmap X z) = rhF X x0 z := by
  rw [ExF.rhF_eq_sum X x0 ho, rh]
  congr 1
  rw [← (eΨ X).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Zof_Zmap]
  have hpd := (ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)
  rw [show (1 - ExF.Zt X z (eΨ X k) * (ExF.Zt X z (eΨ X k))ᴴ) = ExF.Am X z (eΨ X k) from rfl,
    ExF.norm_of_pos hpd.det_pos]

theorem Zmap_mem (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Zmap X z ∈ Dset X.Ψ.card X.p0 (r - X.p0) := by
  intro k
  rw [Zof_Zmap]
  exact (ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)

theorem rh_contDiffAt {f p q : ℕ} {v : V (nD f p q)} (hv : v ∈ Dset f p q) :
    ContDiffAt ℝ 2 (fun w : V (nD f p q) => ((rh w : ℝ) : ℂ)) v := by
  have hZ : ∀ k a b, ContDiff ℝ 2 fun w : V (nD f p q) => Zof w k a b := by
    intro k a b
    simp only [Zof, Matrix.of_apply]
    first
    | exact ((contDiff_piLp _).mp contDiff_id) _
    | fun_prop
  have hM : ∀ k i j, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ : Matrix (Fin p) (Fin p) ℂ) i j := by
    intro k i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine contDiff_const.sub (ContDiff.sum fun l _ => (hZ k i l).mul ?_)
    have h := hZ k j l
    first
    | exact h.star
    | exact Complex.conjCLE.contDiff.comp h
    | fun_prop
  have hdet : ∀ k, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ).det := by
    intro k
    simp only [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    first
    | exact contDiff_prod fun i _ => hM k _ _
    | fun_prop
  have hpos : ∀ k, 0 < ((1 - Zof v k * (Zof v k)ᴴ).det).re := by
    intro k
    have h := (hv k).det_pos
    first
    | exact (Complex.pos_iff.mp h).1
    | simpa using (Complex.lt_def.mp h).1
  have hlog : ∀ k, ContDiffAt ℝ 2
      (fun w : V (nD f p q) => Real.log ((1 - Zof w k * (Zof w k)ᴴ).det.re)) v := by
    intro k
    have hre : ContDiff ℝ 2 fun w : V (nD f p q) => ((1 - Zof w k * (Zof w k)ᴴ).det).re :=
      Complex.reCLM.contDiff.comp (hdet k)
    exact (Real.contDiffAt_log.mpr (hpos k).ne').comp v hre.contDiffAt
  have hsum : ContDiffAt ℝ 2 (fun w : V (nD f p q) => rh w) v := by
    unfold rh
    exact (ContDiffAt.sum fun k _ => hlog k).neg
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp v hsum

end

theorem rhGradF_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : RhGradFStatement (E := E) := by
  intro r X x0 ho z hz ξ
  have hU := ExF.isOpen_OmF X x0
  have hZ : ContDiff ℂ ∞ (Zmap X) := Zmap_contDiff X
  have hZd : HasFDerivAt (Zmap X) (fderiv ℂ (Zmap X) z) z :=
    (hZ.differentiable (by simp) z).hasFDerivAt
  have hmem := Zmap_mem X x0 ho hz
  have hg := rh_contDiffAt hmem
  have hev : (fun w : V (nd X) => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z]
      (fun w : V (nD X.Ψ.card X.p0 (r - X.p0)) => ((rh w : ℝ) : ℂ)) ∘ Zmap X := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simp only [Function.comp_apply, rh_Zmap X x0 ho hw]
  have h1 : ∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j =
      ∑ a, wd _ a (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) *
        fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) a := by
    rw [← gc_sum_wd_comp _ _ _ _ _ z (hg.differentiableAt (by norm_num)) hZd ξ]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [_root_.ReciprocityTheory.L2DbarEstimates.wd, hev.fderiv_eq]
  have h2 : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ =
      leviV _ (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) (fun b => fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) b) := by
    rw [Y.fc_leviV_congr (nd X) _ _ z hev]
    exact gc_leviV_comp _ _ _ _ Set.univ isOpen_univ z trivial (hZ.contDiffOn.of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)) hg ξ
  rw [h1, h2]
  exact RhGradStatement_holds _ _ _ _ hmem _

end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem RhGradFStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    RhGradFStatement (E := E) := RGF.rhGradF_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

local instance instMSMat {m n : Type*} : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance instBorelMat {m n : Type*} [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

theorem meas_inv {n : Type*} [Fintype n] [DecidableEq n] : Measurable fun A : Matrix n n ℂ => A⁻¹ := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact (continuous_id.matrix_det.measurable.inv).mul
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable

theorem meas_Yb {p q : ℕ} : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => Yb M := by
  have hB : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => M.toBlocks₂₂ :=
    (show Continuous fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ =>
        (M.toBlocks₂₂ : Matrix (Fin q) (Fin q) ℂ) from
      continuous_pi fun i => continuous_pi fun j =>
        continuous_id.matrix_elem (Sum.inr i) (Sum.inr j)).measurable
  have hBi := (meas_inv (n := Fin q)).comp hB
  unfold Yb
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (continuous_id.matrix_elem (Sum.inl i) (Sum.inr k)).measurable.mul
    ((continuous_id.matrix_elem k j).measurable.comp hBi)

theorem meas_dpow {p q : ℕ} (s : ℝ) : Measurable fun Z : Matrix (Fin p) (Fin q) ℂ => dpow Z s := by
  unfold dpow
  exact (Complex.continuous_re.comp ((continuous_const.sub
    (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)).matrix_det)).measurable.pow_const s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cont_mat (X : Data E r) (τ : X.Ψ) : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ

theorem cont_Mx (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) : Continuous fun x => Mx X x0 x τ := by
  unfold Mx tl
  exact (continuous_const.matrix_mul (cont_mat X τ)).matrix_submatrix _ _

theorem meas_kap (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kap X x0 bb) := by
  unfold kap
  exact Finset.measurable_prod _ fun τ _ =>
    (meas_dpow bb).comp (meas_Yb.comp (cont_Mx X x0 τ).measurable)

theorem cont_lact (X : Data E r) (γ : GL (Fin r) E) : Continuous (lact (Ψ := X.Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : Frame X.Ψ r =>
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  exact continuous_const.matrix_mul (cont_mat X τ)

theorem meas_Bor (X : Data E r) : MeasurableSet (Bor X.Ψ r) := by
  have h : Bor X.Ψ r = ⋂ τ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a, ⋂ c, {b : Frame X.Ψ r | c < a → b τ a c = 0}) := by
    ext b
    simp [Bor]
  rw [h]
  refine MeasurableSet.iInter fun τ => ?_
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => ?_)
  · exact (isOpen_ne_fun (cont_mat X τ).matrix_det continuous_const).measurableSet
  · by_cases hca : c < a
    · simp only [hca, true_implies]
      exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
    · simp [hca]

def Sset (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  (fun pr : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 pr.1) pr.2) '' (FF ×ˢ Bor X.Ψ r)

theorem meas_S (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : MeasurableSet FF) : MeasurableSet (Sset X x0 FF) := by
  have : PolishSpace (V (nd X) × Frame X.Ψ r) := {}
  refine MeasurableSet.image_of_continuousOn_injOn (hFF.prod (meas_Bor X)) ?_ ?_
  · refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    exact ((cont_mat X τ).comp ((cont_cpt X x0).comp continuous_fst)).matrix_mul
      ((cont_mat X τ).comp continuous_snd)
  · rintro ⟨z, b⟩ ⟨_, hb⟩ ⟨z', b'⟩ ⟨_, hb'⟩ h
    obtain ⟨e1, e2⟩ := cpt_inj X ho hb hb' h
    exact Prod.ext e1 e2

private lemma rmul_rmul_eq_rmul_rmul (X : Data E r) (x b c : Frame X.Ψ r) :
    rmul (rmul x b) c = rmul x (rmul b c) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)

private lemma bor_rmul_mem (X : Data E r) {b c : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hc : c ∈ Bor X.Ψ r) : rmul b c ∈ Bor X.Ψ r := by
  intro τ
  have hm : mat (rmul b c) τ = mat b τ * mat c τ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero (hb τ).1 (hc τ).1
  · have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
    have h2 : (mat c τ).BlockTriangular id := fun i j h => (hc τ).2 i j h
    exact (h1.mul h2) hda

private lemma inv_mat_mem_bor (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
  intro τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  have hm : mat (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) τ = (mat b τ)⁻¹ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  letI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
  have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular h1) hda

private lemma rmul_rmul_inv_mat (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (y : Frame X.Ψ r) :
    rmul (rmul y b) (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = y := by
  funext τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat y τ * mat b τ * (mat b τ)⁻¹ = y τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rfl

theorem rmul_mem_S (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ Sset X x0 FF ↔ y ∈ Sset X x0 FF := by
  constructor
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)⟩, ⟨hz, bor_rmul_mem X hc (inv_mat_mem_bor X hb)⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans
      ((congrArg (fun w => rmul w _) h).trans (rmul_rmul_inv_mat X hb y))
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c b⟩, ⟨hz, bor_rmul_mem X hc hb⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans (congrArg (fun w => rmul w b) h)

theorem cpt_mem_S (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))} (z : V (nd X)) :
    cpt X x0 z ∈ Sset X x0 FF ↔ z ∈ FF := by
  constructor
  · rintro ⟨⟨z', b'⟩, ⟨hz', hb'⟩, h⟩
    simp only at h
    rw [← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    rwa [← (cpt_inj X ho hb' (ExtFPf.oneF_mem X) h).1]
  · intro hz
    exact ⟨⟨z, ExtFPf.oneF X⟩, ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩

theorem lact_rmul' (X : Data E r) (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (rmul x b) τ = mat (lact γ x) τ * mat b τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
end
