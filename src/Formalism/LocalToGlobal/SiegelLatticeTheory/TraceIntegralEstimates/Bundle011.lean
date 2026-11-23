module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerS2
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle021
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle009
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SecondDualReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameOp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.HeisOpHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle003

@[expose] public section

section

noncomputable section

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerJ

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.FolnerS Formalism.L2.S.Pv.FolnerG
  Formalism.L2.S.Pv.FolnerT PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG

open Formalism.MainNotions.S (uMat)

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem uMat_ext {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b :=
  Subtype.ext (Units.ext h)

theorem continuous_uMat : Continuous (uMat : Formalism.REAL.UJ ε → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

def ofM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    GH k r :=
  mk (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r) g hg

theorem toM_ofM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    (ofM g hg).toM = g := toM_mk g hg

def psiF (hF : IsFrameJ ε e f wf z0) : GH k r ≃* Formalism.REAL.UJ ε where
  toFun g := toUJ (Qm e f wf z0 * g.toM * Qi ε e f wf z0) (conjQ_UJ hF g.toM_mem)
  invFun s := ofM (Qi ε e f wf z0 * uMat s * Qm e f wf z0) (conj_mem_UH hF (uMat_mem s))
  left_inv g := by
    apply toM_injective
    rw [toM_ofM, uMat_toUJ]
    exact Qi_Qm_conj hF _
  right_inv s := by
    apply uMat_ext
    rw [uMat_toUJ, toM_ofM]
    simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
    rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
  map_mul' g h := by
    apply uMat_ext
    rw [uMat_mul, uMat_toUJ, uMat_toUJ, uMat_toUJ, toM_mul]
    calc Qm e f wf z0 * (g.toM * h.toM) * Qi ε e f wf z0
        = Qm e f wf z0 * g.toM * (Qi ε e f wf z0 * Qm e f wf z0) * h.toM * Qi ε e f wf z0 := by
          rw [Qi_mul_Qm hF, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem continuous_psiF (hF : IsFrameJ ε e f wf z0) : Continuous (psiF hF) := by
  rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).1.isEmbedding.continuous_iff]
  show Continuous (fun g : GH k r => Qm e f wf z0 * g.toM * Qi ε e f wf z0)
  exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const

theorem continuous_psiF_symm (hF : IsFrameJ ε e f wf z0) : Continuous (psiF hF).symm := by
  rw [continuous_iff_toM]
  have e1 : (fun s : Formalism.REAL.UJ ε => ((psiF hF).symm s).toM) = fun s => Qi ε e f wf z0 * uMat s * Qm e f wf z0 := by
    funext s; exact toM_ofM _ (conj_mem_UH hF (uMat_mem s))
  rw [e1]
  exact (continuous_const.matrix_mul continuous_uMat).matrix_mul continuous_const

theorem inS_psiF_iff {T : ℝ} {z : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf (z0v T z)) (hT : 0 < T) (g : GH k r) :
    InS e z (uMat (psiF hF g)) ↔ g.toM ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) := by
  have hz := Qm_zB (e := e) (f := f) (wf := wf) hT z
  have key : psiF hF g ∈ HNset ε e f wf (z0v T z) (zBv k r T) ↔ g.toM ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) := by
    show Qi ε e f wf (z0v T z) * uMat (psiF hF g) * Qm e f wf (z0v T z) ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) ↔ _
    show Qi ε e f wf (z0v T z) * (Qm e f wf (z0v T z) * g.toM * Qi ε e f wf (z0v T z)) * Qm e f wf (z0v T z) ∈ _ ↔ _
    rw [Qi_Qm_conj hF]
  rw [← key]
  constructor
  · intro hs
    exact HNset_of_inS (fun k r T hT s hs h1 h2 => bessel_levi_formula k r T hT s hs h1 h2) hF hT hz hs
  · intro hs
    exact inS_of_HNset hF hz (inWb_zB T) ⟨_, rfl⟩ hs

theorem isFolner_Sinf {ι : Type} [Fintype ι] {εv : ι → Fin (2 * r + k + 1) → Bool}
    (ev fv : ι → Fin r → Fin (2 * r + k + 1) → ℂ) (wv : ι → Fin k → Fin (2 * r + k + 1) → ℂ)
    (zv : ι → Fin (2 * r + k + 1) → ℂ) (T : ι → ℝ) (hT : ∀ v, 0 < T v)
    (hF : ∀ v, IsFrameJ (εv v) (ev v) (fv v) (wv v) (z0v (T v) (zv v)))
    (μS : Measure (∀ v, Formalism.REAL.UJ (εv v)))
    (hμ : IsHaarSub {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS) :
    IsFolner {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS := by
  let Φ : (ι → GH k r) ≃* (∀ v, Formalism.REAL.UJ (εv v)) := MulEquiv.piCongrRight fun v => psiF (hF v)
  have hΦ : Continuous Φ := continuous_pi fun v => (continuous_psiF (hF v)).comp (continuous_apply v)
  have hΦ' : Continuous Φ.symm := continuous_pi fun v => (continuous_psiF_symm (hF v)).comp (continuous_apply v)
  have hset : Φ ⁻¹' {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} =
      SP (fun v => zBv k r (T v)) := by
    ext x
    show (∀ v, InS (ev v) (zv v) (uMat (psiF (hF v) (x v)))) ↔ ∀ v, (x v).toM ∈ PI.QuotSetU.Sset k r (zBv k r (T v))
    exact forall_congr' fun v => inS_psiF_iff (hF v) (hT v) (x v)
  refine isFolner_of_equiv Φ hΦ hΦ' hμ ?_
  have hμ' := isHaarSub_comap Φ hΦ hΦ' hμ
  rw [hset] at hμ' ⊢
  exact isFolner_pi (z := fun v => zBv k r (T v)) (fun v => inWb_zB (T v))
    (fun v => by show 0 < Formalism.QuantumDeterminants.Tz k r (zBv k r (T v)); rw [Tz_zB (hT v).le]; exact hT v) _ hμ'

end Formalism.L2.S.Pv.FolnerJ
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.S.Pv.ClassCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW
  PI.TermsAtPtFiniteW.HeisW PI.TermsAtPtFiniteW.LeviW PI.TermsAtPtFiniteW.FrameW Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frameOpFull (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ)
    (B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (hBlo : ∀ i j, j < i → B i j = 0) (hBd : ∀ i, B i i = 1) :
    ∃ n ∈ NLam Λ (lf D F0), ∀ j,
      n (frame (lf D F0) j) = ∑ c, ((B c j : 𝓞 D.host.E) : D.host.E) • frame (lf D F0) c := by
  obtain ⟨θ, hθ⟩ := PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D
  obtain ⟨f, L, hff, hef, hL, hzL, hΛeq⟩ := split_row_iso D u F0 Λ hΛ
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y :=
    fun x hx y hy => PI.SRW.pair_int _ hU hy hx
  have he : ∀ a, F0.e a ∈ Λ := fun a => by
    rw [hΛeq]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.subset_span ⟨a, 1, one_mem_aaS D a, (one_smul _ _).symm⟩))
  have hLΛ : L ≤ Λ := by
    rw [hΛeq]
    exact le_sup_right.trans le_sup_left
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hzz : (VS D).hT F0.z F0.z = -((Tu D u : ℕ) : D.host.E) := F0.z_norm

  have horth : ∀ c : D.host.E, c • F0.z ∈ orth (VS D) (Xsp (lf D F0)) := fun c =>
    PI.DCRelEquiv.UnitaryGroupMassFormula.mem_orth_iff.mpr fun x hx =>
      orth_span F0.e (fun a => by rw [map_smul, F0.z_orth, smul_zero]) x hx
  obtain ⟨σ, hσL, hσz⟩ := exists_partner L F0.z hzL (by rw [hzz]; exact neg_ne_zero.mpr hT0)
    (fun x hx y hy => hint x (hLΛ hx) y (hLΛ hy))
    (fun c hc => mem_L_of_dual Λ (aaS D) F0.e f L hU hΛeq F0.e_iso hff hef hL
      (fun a => by rw [map_smul, F0.z_orth, smul_zero])
      (fun a => by rw [map_smul, (hL _ hzL a).2, smul_zero]) hc)
    (fun c hc => hΛ.2.1.2.2.2.2 c ⟨Submodule.mem_sup_left ⟨hLΛ hc, horth c⟩, horth c⟩)
  have hσΛ : σ ∈ Λ := hLΛ hσL

  set β : Fin D.R.rS → D.host.E := fun c => -star ((B (Fin.castSucc c) (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E)
    with hβ
  have hβO : ∀ c, ∃ o : 𝓞 D.host.E, (o : D.host.E) = β c := fun c => by
    obtain ⟨o, ho⟩ := PI.SRW.star_int (B (Fin.castSucc c) (Fin.last D.R.rS))
    exact ⟨-o, by simp only [hβ, ← ho]; push_cast; ring⟩
  set a : Fin D.R.rS → (VS D).V := fun c => β c • σ with ha
  have haΛ : ∀ c, a c ∈ Λ := fun c => smul_memO Λ (hβO c) hσΛ
  have hea : ∀ c d, (VS D).hT ((lf D F0).fl.e c) (a d) = 0 := fun c d => by
    show (VS D).hT (F0.e c) (β d • σ) = 0
    rw [map_smul, (hL σ hσL c).1, smul_zero]
  set s : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c d => -(θ : D.host.E) * (VS D).hT (a c) (a d) with hs
  have hsO : ∀ c d, ∃ o : 𝓞 D.host.E, (o : D.host.E) = s c d := fun c d => by
    obtain ⟨o, ho⟩ := hint _ (haΛ c) _ (haΛ d)
    exact ⟨-θ * o, by simp only [hs, ← ho]; push_cast; ring⟩
  have hss : ∀ c d, s c d + star (s d c) = -(VS D).hT (a c) (a d) := fun c d => by
    simp only [hs, star_mul', star_neg, hsym]
    linear_combination (-(VS D).hT (a c) (a d)) * hθ
  obtain ⟨nH, hnH, hnHapp⟩ := heisOp_holds D.host.E (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E) Λ (lf D F0) a s hint he haΛ hea hsO hss
  have hnHe : ∀ j, nH (F0.e j) = F0.e j := fun j => by
    rw [show F0.e j = (lf D F0).fl.e j from rfl, hnHapp]
    have h1 : ∀ c, (VS D).hT ((lf D F0).fl.e c) ((lf D F0).fl.e j) = 0 := fun c => F0.e_iso c j
    have h2 : ∀ c, (VS D).hT (a c) ((lf D F0).fl.e j) = 0 := fun c => by
      rw [← hsym, hea j c, star_zero]
    simp [PI.TermsAtPtFiniteW.heisFun, h1, h2]
  have hnHz : nH F0.z = F0.z + ∑ c, ((B (Fin.castSucc c) (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) • F0.e c := by
    rw [show F0.z = (lf D F0).fl.z from rfl, hnHapp]
    have h1 : ∀ c, (VS D).hT ((lf D F0).fl.e c) ((lf D F0).fl.z) = 0 := fun c => F0.z_orth c
    have h2 : ∀ c, (VS D).hT (a c) ((lf D F0).fl.z) =
        -((B (Fin.castSucc c) (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) := fun c => by
      show (VS D).hT (β c • σ) F0.z = _
      rw [LinearMap.map_smulₛₗ₂, hσz, smul_eq_mul, mul_one, starRingEnd_apply, hβ]
      simp
    simp only [PI.TermsAtPtFiniteW.heisFun, h1, h2, zero_smul, Finset.sum_const_zero, add_zero, mul_zero, neg_smul,
      Finset.sum_neg_distrib, sub_neg_eq_add]

  set U : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E) := fun c j => B (Fin.castSucc c) (Fin.castSucc j)
    with hUdef
  have hUlo : ∀ i j, j < i → U i j = 0 := fun i j h =>
    hBlo (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.mpr h)
  have hUd1 : ∀ i, U i i = 1 := fun i => hBd _
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hUlo i j h)]
    exact Finset.prod_eq_one fun i _ => hUd1 i
  haveI : Invertible U.det := by rw [hdet]; exact invertibleOne
  haveI : Invertible U := Matrix.invertibleOfDetInvertible U
  have hUbt : U.BlockTriangular id := fun i j h => hUlo i j h
  have hUibt : (U⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hUbt
  have hUiU : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U (by rw [hdet]; exact isUnit_one)
  set UE : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c j => ((U c j : 𝓞 D.host.E) : D.host.E) with hUE
  set U'E : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c b => star ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E)
    with hU'E
  have hentry : ∀ b a, ∑ c, ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E) * ((U c a : 𝓞 D.host.E) : D.host.E) =
      if b = a then 1 else 0 := by
    intro b a
    have h := congrArg (fun M : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E) =>
      algebraMap (𝓞 D.host.E) D.host.E (M b a)) hUiU

    simp only [Matrix.mul_apply, Matrix.one_apply, map_sum, map_mul] at h
    exact h.trans (by split_ifs <;> simp)
  have hUU : ∀ a b, ∑ c, star (UE c a) * U'E c b = if a = b then 1 else 0 := by
    intro a b
    calc ∑ c, star (UE c a) * U'E c b =
          star (∑ c, ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E) * ((U c a : 𝓞 D.host.E) : D.host.E)) := by
          rw [star_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [hUE, hU'E, star_mul']
          ring
      _ = if a = b then 1 else 0 := by
          rw [hentry]
          rcases eq_or_ne a b with h | h
          · subst h; simp
          · simp [h, Ne.symm h]
  have hisoL := isom_psiF F0.e f F0.e_iso hff hef UE U'E hUU
  let nL : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofInjectiveEndo (psiF F0.e f UE U'E) (inj_of_isom _ hisoL)
  have hnL : ∀ v, nL v = psiF F0.e f UE U'E v := fun v =>
    congrFun (LinearEquiv.coe_ofInjectiveEndo _ _) v
  have hLm : ∀ v ∈ Λ, psiF F0.e f UE U'E v ∈ Λ := fun v hv =>
    levi_mem Λ (aaS D) F0.e f L hΛeq F0.e_iso hff hef hL (aaS_mono D) (aaS_ne D) UE U'E
      (fun c a' => ⟨fun h => by simp [hUE, hUlo c a' h], ⟨U c a', rfl⟩⟩)
      (fun c a' => ⟨fun h => by simp [hU'E, hUibt h], PI.SRW.star_int _⟩) hv
  have hnLmem : nL ∈ NLam Λ (lf D F0) := by
    refine ⟨⟨fun x y => by rw [hnL, hnL]; exact hisoL x y, ?_⟩, ?_, ?_⟩
    · exact gmap_of_isom Λ hU nL (fun x y => by rw [hnL, hnL]; exact hisoL x y)
        (fun v hv => by rw [hnL]; exact hLm v hv)
    · intro j x hx
      have hsub : F0.Xa (j + 1) ≤ (F0.Xa j).comap (psiF F0.e f UE U'E - LinearMap.id) := by
        unfold Formalism.MainNotions.S.FlagG.Xa
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
        rw [psiF_e F0.e f hef UE U'E F0.e_iso i, sum_sub_delta]
        refine Submodule.sum_mem _ fun c _ => ?_
        rcases lt_trichotomy c i with h | h | h
        · exact Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨c, show c.1 < j from lt_of_lt_of_le (Fin.lt_def.mp h) (Nat.lt_succ_iff.mp hi), rfl⟩)
        · subst h
          simp [hUE, hUd1]
        · simp [hUE, hUlo c i h, if_neg h.ne']
      have := hsub hx
      rw [hnL]
      exact this
    · intro x hx
      have hφ : ∀ c, (VS D).hT (F0.e c) x = 0 := fun c =>
        (PI.DCRelEquiv.UnitaryGroupMassFormula.mem_orth_iff.mp hx) _ (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) c)
      rw [hnL, psiF_apply]
      simp only [hφ, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
      refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) c))
        (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) a))
  refine ⟨nH * nL, PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul hnH hnLmem, frame_fin D F0 1 B
    (fun i j => ⟨hBlo i j, fun h => h ▸ hBd i, fun _ => one_dvd _⟩) nH nL hnHe hnHz
    (fun i => by rw [hnL]; exact psiF_e F0.e f hef UE U'E F0.e_iso i)
    (by rw [hnL]; exact psiF_fix F0.e f UE U'E F0.z (fun a => (hL _ hzL a).2) (fun a => F0.z_orth a))⟩

end Formalism.L2.S.Pv.ClassCounting

end
end
