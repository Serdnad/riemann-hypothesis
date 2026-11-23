module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cd_nM (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ a b := by
  show ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b
  unfold nmat
  by_cases h : b < a
  · simp only [dif_pos h]
    first
      | exact (EuclideanSpace.proj (𝕜 := ℂ) _).contDiff
      | fun_prop
      | exact ((EuclideanSpace.proj (𝕜 := ℂ) _).contDiff).congr fun z => rfl
  · simp only [dif_neg h]
    exact contDiff_const

theorem unipotentFrame_inv_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ)⁻¹ = (n1 X z τ).adjugate := by
  have hdet : (n1 X z τ).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [n1, nM_diag]
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      exact nM_upper X z τ (show Fin.castLE X.p0_le i < Fin.castLE X.p0_le j from hij')
  rw [Matrix.inv_def, hdet]
  simp

private lemma cd_det_lemma {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) : ContDiff 𝕜 ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

private lemma cd_adj_lemma_2 {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) (i j : Fin k) :
    ContDiff 𝕜 ∞ fun z => (M z).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine cd_det_lemma fun a b => ?_
  by_cases hab : a = j
  · simp only [Matrix.updateRow_apply, hab, if_true]
    exact contDiff_const
  · simp only [Matrix.updateRow_apply, hab, if_false]
    exact h a b

theorem cd_Zt (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    ContDiff ℂ ∞ fun z : V (nd X) => Zt X z τ a m := by
  have hfun : (fun z : V (nd X) => Zt X z τ a m) =
      fun z => ∑ k, Wm X z τ m k * (n1 X z τ).adjugate k a := by
    funext z
    simp only [Zt, Matrix.transpose_apply, Matrix.mul_apply, unipotentFrame_inv_eq_adjugate]
  rw [hfun]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ ?_
  · show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (qI X m) (Fin.castLE X.p0_le k)
    exact cd_nM X τ _ _
  · refine cd_adj_lemma_2 (M := fun z : V (nd X) => n1 X z τ) (fun i j => ?_) k a
    show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
    exact cd_nM X τ _ _

theorem cd_Am_entry (τ : X.Ψ) (a c : Fin X.p0) :
    ContDiff ℝ ∞ fun z : V (nd X) => Am X z τ a c := by
  have hZ : ∀ a m, ContDiff ℝ ∞ fun z : V (nd X) => Zt X z τ a m :=
    fun a m => (cd_Zt X τ a m).restrict_scalars ℝ
  have hfun : (fun z : V (nd X) => Am X z τ a c) = fun z =>
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a c - ∑ m, Zt X z τ a m * star (Zt X z τ c m) := by
    funext z
    simp only [Am, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hfun]
  refine contDiff_const.sub (ContDiff.sum fun m _ => (hZ a m).mul ?_)
  first
    | exact (hZ c m).star
    | exact Complex.conjCLE.contDiff.comp (hZ c m)

theorem cd_detAm (τ : X.Ψ) : ContDiff ℝ ∞ fun z : V (nd X) => (Am X z τ).det := by
  exact cd_det_lemma (M := fun z : V (nd X) => Am X z τ) fun a c => cd_Am_entry X τ a c

theorem rhF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  have hfun : rhF X x0 = fun w => -∑ τ, Real.log ‖(Am X w τ).det‖ := funext (rhF_eq_sum X x0 ho)
  have hpd := (mem_OmF_iff X x0 ho z).1 hz
  rw [hfun]
  refine (ContDiffAt.sum fun τ _ => ?_).neg
  have hne : (Am X z τ).det ≠ 0 := (hpd τ).det_pos.ne'
  have h1 : ContDiffAt ℝ ∞ (fun w : V (nd X) => (Am X w τ).det) z := (cd_detAm X τ).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun w : V (nd X) => ‖(Am X w τ).det‖) z :=
    (contDiffAt_norm ℂ hne).comp z h1
  exact h2.log (norm_ne_zero_iff.2 hne)

theorem T_cd {n : ℕ} : ContDiff ℝ ∞ fun z : V n => Real.log (1 + ‖z‖ ^ 2) := by
  exact (contDiff_const.add (contDiff_norm_sq ℂ)).log fun z => by positivity

theorem eF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (eF X x0) z := by
  exact (rhF_contDiffAt X x0 ho hz).add (T_cd (n := nd X)).contDiffAt

theorem isOpen_OmF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hfun : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ k, x0 τ a k * nM X z τ k b := by
      funext z
      have h := congrFun (congrFun (mat_cpt X x0 z τ) a) b
      simpa [mat, Matrix.mul_apply] using h
    rw [hfun]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (cd_nM X τ k b).continuous
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
    fun τ => (hmat τ).matrix_det
  have hdmin : ∀ τ i, Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.submatrix_apply, FD.gram, Matrix.of_apply, FD.hermC, FD.col, mat]
    fun_prop
  have hset : OmF X x0 = ⋂ τ : X.Ψ, ({z | (mat (cpt X x0 z) τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {z | 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re}) := by
    ext z
    simp only [OmF, Set.mem_setOf_eq, X.mem_dom_iff, Set.mem_iInter, Set.mem_inter_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun ((hdet τ).comp hc) continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp ((hdmin τ i).comp hc)))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OFC

open NumberField Complex Matrix Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def isW (i : Fin (nd X)) : Prop :=
  X.p0 ≤ (((Fintype.equivFin (Ent X)).symm i).2.1.1 : ℕ) ∧ (((Fintype.equivFin (Ent X)).symm i).2.1.2 : ℕ) < X.p0

instance (i : Fin (nd X)) : Decidable (isW X i) := by unfold isW; infer_instance

def S1 (t : ℝ) (z : V (nd X)) : V (nd X) := WithLp.toLp 2 fun i => if isW X i then (t : ℂ) * z i else z i

def S2 (t : ℝ) (z : V (nd X)) : V (nd X) := WithLp.toLp 2 fun i => if isW X i then 0 else (t : ℂ) * z i

theorem scaledWm_linear (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Wm X (S1 X t z) τ = (t : ℂ) • ExF.Wm X z τ := by
  ext m c
  have hc := c.isLt
  have hlt : Fin.castLE X.p0_le c < ExF.qI X m := by
    rw [Fin.lt_def]
    simp only [Fin.coe_castLE, ExF.qI]
    omega
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S1, dif_pos hlt]
  rw [if_pos]
  simp only [isW, Equiv.symm_apply_apply, ExF.qI, Fin.coe_castLE]
  omega

theorem unipotentFrame_scaling_invariant (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.n1 X (S1 X t z) τ = ExF.n1 X z τ := by
  ext a b
  have ha := a.isLt
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S1]
  split_ifs with h1 h2 <;>
    first
    | rfl
    | (exfalso
       simp only [isW, Equiv.symm_apply_apply, Fin.coe_castLE] at *
       omega)

theorem retractedWm_eq_zero (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Wm X (S2 X t z) τ = 0 := by
  ext m c
  have hc := c.isLt
  have hlt : Fin.castLE X.p0_le c < ExF.qI X m := by
    rw [Fin.lt_def]
    simp only [Fin.coe_castLE, ExF.qI]
    omega
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S2, dif_pos hlt, Matrix.zero_apply]
  rw [if_pos]
  simp only [isW, Equiv.symm_apply_apply, ExF.qI, Fin.coe_castLE]
  omega

theorem scaledZt_linear (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Zt X (S1 X t z) τ = (t : ℂ) • ExF.Zt X z τ := by
  simp only [ExF.Zt, scaledWm_linear, unipotentFrame_scaling_invariant, Matrix.smul_mul, Matrix.transpose_smul]

theorem retractedZt_eq_zero (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Zt X (S2 X t z) τ = 0 := by
  simp only [ExF.Zt, retractedWm_eq_zero, Matrix.zero_mul, Matrix.transpose_zero]

theorem S1_mem_OmF (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : S1 X t z ∈ OmF X x0 := by
  rw [ExF.mem_OmF_iff X x0 ho] at hz ⊢
  intro τ
  have hA := hz τ
  have heq : ExF.Am X (S1 X t z) τ =
      ((1 - t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) + ((t ^ 2 : ℝ) : ℂ) • ExF.Am X z τ := by
    simp only [ExF.Am, scaledZt_linear, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.star_def, Complex.conj_ofReal]
    have e1 : ((1 - t ^ 2 : ℝ) : ℂ) = 1 - (t : ℂ) * t := by
      push_cast
      ring
    have e2 : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) * t := by
      push_cast
      ring
    rw [e1, e2, sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  rcases ht0.lt_or_eq with htpos | rfl
  · have h2 : (0 : ℂ) < ((t ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast pow_pos htpos 2
    have h1 : (0 : ℂ) ≤ ((1 - t ^ 2 : ℝ) : ℂ) := by
      have : t ^ 2 ≤ 1 := by nlinarith
      exact_mod_cast sub_nonneg.2 this
    exact (hA.smul h2).posSemidef_add ((Matrix.PosSemidef.one).smul h1)
  · simpa using Matrix.PosDef.one

theorem radialRetraction_mem_chart (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (t : ℝ) : S2 X t z ∈ OmF X x0 := by
  rw [ExF.mem_OmF_iff X x0 ho]
  intro τ
  simp only [ExF.Am, retractedZt_eq_zero, Matrix.zero_mul, sub_zero]
  exact Matrix.PosDef.one

theorem continuous_linearScaling (z : V (nd X)) : Continuous fun t : ℝ => S1 X t z := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : isW X i
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    fun_prop

theorem continuous_radialRetraction (z : V (nd X)) : Continuous fun t : ℝ => S2 X t z := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : isW X i
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    fun_prop

theorem linearScaling_zero_eq_retraction (z : V (nd X)) : S1 X 0 z = S2 X 1 z := by
  ext i
  simp only [S1, S2, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

theorem radialRetraction_at_zero (z : V (nd X)) : S2 X 0 z = 0 := by
  ext i
  simp only [S2, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

theorem linearScaling_at_one (z : V (nd X)) : S1 X 1 z = z := by
  ext i
  simp only [S1, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

end

theorem omFConn_of_cm {E : Type} [Field E] [NumberField E] [IsCMField E] : OmFConnStatement (E := E) := by
  intro r X x0 ho
  refine isPreconnected_of_forall 0 fun y hy => ?_
  refine ⟨(fun t => S2 X t y) '' Set.Icc 0 1 ∪ (fun t => S1 X t y) '' Set.Icc 0 1, ?_, ?_, ?_, ?_⟩
  · rintro w (⟨t, -, rfl⟩ | ⟨t, ⟨ht0, ht1⟩, rfl⟩)
    · exact radialRetraction_mem_chart X x0 ho y t
    · exact S1_mem_OmF X x0 ho hy ht0 ht1
  · exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, radialRetraction_at_zero X y⟩
  · exact Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, linearScaling_at_one X y⟩
  · refine IsPreconnected.union (S2 X 1 y) ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
      ⟨0, ⟨le_rfl, zero_le_one⟩, linearScaling_zero_eq_retraction X y⟩ ?_ ?_
    · exact isPreconnected_Icc.image _ (continuous_radialRetraction X y).continuousOn
    · exact isPreconnected_Icc.image _ (continuous_linearScaling X y).continuousOn

end ReciprocityTheory.ChartRestriction.G.AR.Up.OFC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem OmFConnStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    OmFConnStatement (E := E) :=
  OFC.omFConn_of_cm

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
