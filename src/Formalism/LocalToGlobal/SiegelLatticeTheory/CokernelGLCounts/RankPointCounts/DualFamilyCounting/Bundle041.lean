module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle040
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle013
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatA

open Alg

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

def SS (I : FI) : Prop := ∀ x ∈ I, star x ∈ I

theorem SS_one : SS (1 : FI) := by
  intro x hx
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  obtain ⟨o', ho'⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_int o
  exact (FractionalIdeal.mem_one_iff _).2 ⟨o', ho'⟩

theorem SS_dIpow (n : ℕ) : SS (((Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ n : Ideal (𝓞 D.host.E)) : FI)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  obtain ⟨y', hy', ey⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_pow n y hy
  exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y', hy', ey⟩

theorem SS_inv {I : FI} (hI : SS I) : SS I⁻¹ := by
  by_cases h0 : I = 0
  · subst h0
    intro x hx
    rw [_root_.inv_zero] at hx ⊢
    rw [(FractionalIdeal.mem_zero_iff _).1 hx, star_zero]
    exact (FractionalIdeal.mem_zero_iff _).2 rfl
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  have h := SS_one _ (hx _ (hI y hy))
  rwa [star_mul, star_star, mul_comm] at h

theorem SS_mul {I J : FI} (hI : SS I) (hJ : SS J) : SS (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [star_mul']
    exact FractionalIdeal.mul_mem_mul (hI a ha) (hJ b hb)
  · intro a b ha hb
    rw [star_add]
    exact Submodule.add_mem _ ha hb

theorem SS_aaD (a : Fin D.R.rS) : SS (aaD D a) := by
  rw [Formalism.L2.SG.SplitPrimeNormLemmas.IntG.aaD_eq]
  have : ddS D ^ (D.R.rS - (a : ℕ)) = (((Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (a : ℕ)) : Ideal (𝓞 D.host.E)) : FI)) := by
    rw [FractionalIdeal.coeIdeal_pow]; rfl
  rw [this]
  exact SS_inv (SS_dIpow _)

theorem aa_ne (a : Fin D.R.rS) : aaD D a ≠ 0 := by
  rw [Formalism.L2.SG.SplitPrimeNormLemmas.IntG.aaD_eq]; exact inv_ne_zero (pow_ne_zero _ Formalism.L2.SG.SplitPrimeNormLemmas.IntG.ddS_ne_zero)

variable (X : HidaSetting D)

theorem smul_aaLb {d : Fin D.R.rS} {c : D.host.E} (hc : c ∈ (aaD D d)⁻¹) {y : (VS D).V} (hy : y ∈ aaLb X d) :
    c • y ∈ X.Lb := by
  have hy' : y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D d : Set D.host.E), ∃ l ∈ X.Lb, y = c • l} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c', hc', l, hl, rfl⟩ := hz
    have hm : c * c' ∈ (1 : FI) := by
      rw [← inv_mul_cancel₀ (aa_ne d)]; exact FractionalIdeal.mul_mem_mul hc hc'
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    rw [smul_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o hl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ o hx

theorem Lb_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]; exact le_sup_of_le_left le_sup_right

theorem hT_aaLb_mem {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) {w : (VS D).V} (hw : w ∈ X.Lb) :
    (VS D).hT y w ∈ aaD D b := by
  have hy' : y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, l, hl, rfl⟩ := hz
    obtain ⟨o, ho⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int (VS D).baseLattice_isUnimodular (Lb_le X hl) (Lb_le X hw)
    rw [hT_smulL, ← ho, mul_comm]
    exact fi_smul_mem (SS_aaD b c hc) o
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [← algebraMap_smul D.host.E o x, hT_smulL]
    obtain ⟨o', ho'⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_int o
    rw [show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl, ← ho']
    exact fi_smul_mem hx o'

theorem aa_cancel (a b c : Fin D.R.rS) : aaD D b * (aaD D a)⁻¹ * (aaD D a * (aaD D c)⁻¹) = aaD D b * (aaD D c)⁻¹ := by
  rw [mul_assoc, ← mul_assoc (aaD D a)⁻¹, inv_mul_cancel₀ (aa_ne a), one_mul]

theorem aa_cancel2 (a b c : Fin D.R.rS) : aaD D b * (aaD D a)⁻¹ * (aaD D a * aaD D c) = aaD D b * aaD D c := by
  rw [mul_assoc, ← mul_assoc (aaD D a)⁻¹, inv_mul_cancel₀ (aa_ne a), one_mul]

theorem one_mem_aa (a : Fin D.R.rS) : (1 : D.host.E) ∈ aaD D a * (aaD D a)⁻¹ := by
  rw [mul_inv_cancel₀ (aa_ne a)]; exact FractionalIdeal.one_mem_one _

theorem shape_inv (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a, a < b → X0 b a = 0)
    (hd : ∀ a, X0 a a = 1) (hs : ∀ b a, b < a → X0 b a ∈ aaD D b * (aaD D a)⁻¹) :
    ∀ b a, b < a → X0⁻¹ b a ∈ aaD D b * (aaD D a)⁻¹ := by
  have hdet : X0.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hup i j hij)]
    simp [hd]
  have hU : IsUnit X0.det := by rw [hdet]; exact isUnit_one
  have hXY : X0 * X0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hYup : ∀ b a, a < b → X0⁻¹ b a = 0 := by
    have hbt : X0.BlockTriangular id := fun i j hij => hup i j hij
    haveI : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU
    exact fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h
  have hYd : ∀ a, X0⁻¹ a a = 1 := by
    intro a
    have h := congrFun (congrFun hXY a) a
    rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul] at h
    have hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1
      · rw [hup a e h1, zero_mul]
      · rw [hYup e a h1, mul_zero]
    rw [hz, add_zero] at h
    exact h
  have key : ∀ k, ∀ b a : Fin D.R.rS, a.val - b.val = k → b < a → X0⁻¹ b a ∈ aaD D b * (aaD D a)⁻¹ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro b a hk hba
      have h0 : ∑ e, X0 b e * X0⁻¹ e a = 0 := by
        have := congrFun (congrFun hXY b) a
        rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hba)] at this
        exact this
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hd, one_mul] at h0
      rw [eq_neg_of_add_eq_zero_left h0]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun e he => ?_)
      have heb : e ≠ b := Finset.ne_of_mem_erase he
      rcases lt_or_gt_of_ne heb with h1 | h1
      · rw [hup b e h1, zero_mul]; exact Submodule.zero_mem _
      · rcases lt_trichotomy e a with h2 | h2 | h2
        · have hY := ih (a.val - e.val) (by have := Fin.lt_iff_val_lt_val.1 h1; omega) e a rfl h2
          rw [← aa_cancel e b a]
          exact FractionalIdeal.mul_mem_mul (hs b e h1) hY
        · subst h2
          rw [hYd, mul_one]; exact hs b e h1
        · rw [hYup e a h2, mul_zero]; exact Submodule.zero_mem _
  exact fun b a h => key _ b a rfl h

theorem shape_mul (X0 M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a, a < b → X0 b a = 0)
    (hd : ∀ a, X0 a a = 1) (hs : ∀ b a, b < a → X0 b a ∈ aaD D b * (aaD D a)⁻¹)
    (hM : ∀ b a, M b a ∈ aaD D b * aaD D a) : ∀ b a, (X0 * M) b a ∈ aaD D b * aaD D a := by
  intro b a
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rcases lt_trichotomy e b with h | h | h
  · rw [hup b e h, zero_mul]; exact Submodule.zero_mem _
  · subst h; rw [hd, one_mul]; exact hM e a
  · rw [← aa_cancel2 e b a]
    exact FractionalIdeal.mul_mem_mul (hs b e h) (hM e a)

end LatA

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section

namespace Formalism.L2.SG.Pf.NcVal

theorem volOrdV_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : VolOrdV X u u' ψ :=
  volOrdV_of X u u' ψ Formalism.L2.SG.Pf.conductor_inverse_different

end Formalism.L2.SG.Pf.NcVal
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatF

open Alg

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

theorem mem_mul_inv_of {I J : FI} (hI : I ≠ 0) {x : D.host.E} (h : ∀ c ∈ I, c * x ∈ J) : x ∈ J * I⁻¹ := by
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I ≤ J := by
    rw [FractionalIdeal.mul_le]
    intro s hs c hc
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hs
    rw [Algebra.smul_def, mul_assoc, mul_comm x c]
    exact LatA.fi_smul_mem (h c hc) z
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x ≤ J * I⁻¹ := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ J * I⁻¹ := FractionalIdeal.mul_le.mpr fun i hi j hj => FractionalIdeal.mul_mem_mul (h1 hi) hj
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ x)

theorem mul_mem_cancel {I J K : FI} (hK : K ≠ 0) {x y : D.host.E} (hx : x ∈ I * K⁻¹) (hy : y ∈ K * J) :
    x * y ∈ I * J := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  have e : I * K⁻¹ * (K * J) = I * J := by
    calc I * K⁻¹ * (K * J) = I * J * (K⁻¹ * K) := by ring
      _ = I * J := by rw [inv_mul_cancel₀ hK, mul_one]
  rwa [e] at h

variable (X : HidaSetting D)

theorem aa_ne (Y : HidaSetting D) (a : Fin D.R.rS) : aaD D a ≠ 0 := Formalism.L2.SG.Pf.NcReal.JX.CovB.aaD_ne_zero Y a

theorem e_mem {a : Fin D.R.rS} {c : D.host.E} (hc : c ∈ aaD D a) : c • X.eX a ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, c, hc, rfl⟩))

theorem f_mem {a : Fin D.R.rS} {c : D.host.E} (hc : c ∈ (aaD D a)⁻¹) : c • X.fY a ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, c, hc, rfl⟩)

variable {X}

theorem lattice_map_preserves_base {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    {y : (VS D).V} (hy : y ∈ (VS D).L0) : m y ∈ (VS D).L0 := by
  rw [← hL]; exact ⟨y, hy, rfl⟩

theorem gmap_symm {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0) :
    Formalism.HermitianLatticesTheory.gmap m.symm (VS D).L0 = (VS D).L0 := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hL] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    show m.symm (m w) ∈ (VS D).L0
    simpa using hw
  · intro hy
    exact ⟨m y, lattice_map_preserves_base hL hy, by simp⟩

theorem ex_shape {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    (b d : Fin D.R.rS) : (VS D).hT (X.fY b) (m (X.eX d)) ∈ aaD D b * (aaD D d)⁻¹ := by
  refine mem_mul_inv_of (aa_ne X d) fun c hc => ?_
  have h := Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (e_mem X hc))
  rw [map_smul, map_smul, smul_eq_mul] at h
  exact h

theorem fa_shape {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    (b a : Fin D.R.rS) : (VS D).hT (X.fY b) (m (X.fY a)) ∈ aaD D b * aaD D a := by
  have hne : (aaD D a)⁻¹ ≠ 0 := inv_ne_zero (aa_ne X a)
  have := mem_mul_inv_of hne (J := aaD D b) (x := (VS D).hT (X.fY b) (m (X.fY a))) fun c hc => by
    have h := Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (f_mem X hc))
    rw [map_smul, map_smul, smul_eq_mul] at h
    exact h
  rwa [inv_inv] at this

variable {u : D.what₂.Word} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}

theorem Xinv (hn : NFl X u n) : Xq X n.symm * Xq X n = 1 := by
  refine Matrix.ext fun b a => ?_
  simp only [Matrix.mul_apply, Xq]
  rw [Finset.sum_congr rfl fun d _ => mul_comm _ _, ← hT_sumR]
  have e : ∑ d, (VS D).hT (X.fY d) (n (X.eX a)) • n.symm (X.eX d) = n.symm (n (X.eX a)) := by
    conv_rhs => rw [Xq_expand hn a]

    rw [map_sum]
    simp only [map_smul, Xq]
  rw [e, LinearEquiv.symm_apply_apply, hfe, Matrix.one_apply]

theorem rows_mem (hL : Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) (b : Fin D.R.rS) : xq X n b ∈ aaLb X b := by
  have hβ : ∀ β ∈ (aaD D b)⁻¹, β • xq X n b ∈ X.Lb := by
    intro β hβ
    have h := lattice_map_preserves_base (gmap_symm hL) (f_mem X hβ)
    rw [map_smul] at h
    have := ((LatA.mem_hermitianStandardLattice_iff_pairing_integral X _).1 h).2.2
    rwa [pW_smul] at this
  have h1 : (1 : D.host.E) ∈ aaD D b * (aaD D b)⁻¹ := by
    rw [mul_inv_cancel₀ (aa_ne X b)]; exact FractionalIdeal.one_mem_one _
  have key : ∀ t ∈ ((aaD D b * (aaD D b)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E),
      t • xq X n b ∈ aaLb X b := by
    intro t ht
    rw [FractionalIdeal.coeToSubmodule_mul] at ht
    refine Submodule.mul_induction_on ht (fun α hα β hβ' => ?_) (fun s t hs ht => ?_)
    · rw [mul_smul]
      exact Submodule.subset_span ⟨α, hα, β • xq X n b, hβ β hβ', rfl⟩
    · rw [add_smul]; exact add_mem hs ht
  simpa using key 1 h1

end LatF


open Alg LatF in
theorem dictLatF_holds : DictLatF := by
  intro D X u n hn hL
  refine ⟨fun b a _ => ex_shape hL b a, fun b => rows_mem hL b, fun b a => ?_⟩
  have hinv : (Xq X n)⁻¹ = Xq X n.symm := Matrix.inv_eq_left_inv (Xinv hn)
  show ((Xq X n)⁻¹ * Aq X n) b a ∈ _
  rw [hinv, Matrix.mul_apply]
  refine Submodule.sum_mem _ fun d _ => ?_
  exact mul_mem_cancel (aa_ne X d) (ex_shape (gmap_symm hL) b d) (fa_shape hL d a)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section

namespace Formalism.L2.SG.Pf.Cnt

theorem lattice_exists_holds : RowLatExists := by
  intro D T u
  obtain ⟨Λ, hΛ⟩ := Formalism.L2.SG.Pf.latSub T.X u 1
  exact ⟨Λ, Formalism.L2.SG.Pf.latRowLat T.X u 1 Λ hΛ⟩

end Formalism.L2.SG.Pf.Cnt
end

section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def CntIsoInv : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D),
    cntE T' (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) Z = cntE T' F0 Λ Z

theorem orbitFiniteR_of (hI : CntIsoInv) : OrbitFiniteR := by
  intro D δ M hA L u u' hT F0 what₂ hR Z Λ hΛ
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  obtain ⟨β, hβ, he, hz⟩ := Formalism.L2.SG.Pf.WittFlags.flag_witt hT0 rfl F0 (Formalism.MainNotions.S.Inh.tie_flag0 D u)
  have hR' := Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR
  have hF1e : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).e = D.sp.hypE := by
    funext a
    show β (F0.e a) = _
    rw [he a]
    rfl
  have hF1z : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).z = D.zmOf u := by
    show β F0.z = _
    rw [hz]
    rfl
  have hRO : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β)) :=
    ⟨hF1e, hF1z, hR', ⟨_, Finset.mem_image_of_mem _ hΛ⟩⟩
  have h := PI.UnitaryGroupMassFormula.CntFormula.orbitFinite_of PI.UnitaryGroupMassFormula.CntFormula.unipotent_integral_isGroup PI.UnitaryGroupMassFormula.CntFormula.orbit_representatives
    D δ M hA L u u' hT _ _ hRO Z (Formalism.HermitianLatticesTheory.gmap β Λ) (Finset.mem_image_of_mem _ hΛ)
  rwa [hI D β hβ (Tn u') F0 Λ Z] at h

end Formalism.L2.SG.Pf.Cnt
end
end
