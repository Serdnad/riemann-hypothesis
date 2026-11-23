module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle020
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle011
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SecondFlagXsLeBigBlock
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CoeffOfSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemInvCoeIdeal
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle012
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PairSpanDimension

variable {D : Formalism.BasicNotions.D7}

theorem totPos_ne_zero {x : D.host.E} (hx : TotPos x) : x ≠ 0 := by
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; have := D.R.two_le_m; have := D.R.m_le_f
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; omega)
  obtain ⟨τ⟩ := this
  intro h
  have := hx τ
  rw [h, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

def fam {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim F0.fvec F'.fl.fvec

variable {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')

theorem upair_eq : UPair D F0 F' = Submodule.span D.host.E (Set.range (fam F0 F')) := by
  unfold UPair fam
  rw [Set.Sum.elim_range]

theorem hT_fam (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    (VS D).hT (fam F0 F' a) (fam F0 F' b) = Ga T T' (ZhatL (lf D F0) F') a b := by
  have hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := by
    intro x y
    rw [← starRingEnd_apply]
    first
      | exact (VS D).herm.eq x y
      | exact (VS D).herm x y
  have hze : ∀ j, (VS D).hT F0.z (F0.e j) = 0 := fun j => by rw [← hs, F0.z_orth, star_zero]
  have hze' : ∀ j, (VS D).hT F'.fl.z (F'.fl.e j) = 0 := fun j => by rw [← hs, F'.fl.z_orth, star_zero]
  rcases a with a | a <;> rcases b with b | b
  · simp only [fam, Sum.elim_inl, Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [FlagG.fvec, F0.e_iso, F0.z_orth, F0.z_norm, hze]
  · simp only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    show _ = star ((VS D).hT (F0.fvec b) (F'.fl.fvec a))
    rw [hs]
  · simp only [fam, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [FlagG.fvec, F'.fl.e_iso, F'.fl.z_orth, F'.fl.z_norm, hze']

theorem eq_zero_of_orth (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0)
    (c : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → D.host.E)
    (h : ∀ a, (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i) = 0) : c = 0 := by
  have hdet : (Ga T T' (ZhatL (lf D F0) F')).det ≠ 0 := by
    rw [PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_Ga]
    refine mul_ne_zero ?_ hG
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h1 | h1 <;>
      rw [h1] <;> simp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  funext a
  have ha := h a

  simp only [map_sum, map_smul, smul_eq_mul, hT_fam] at ha
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← ha]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem fam_li (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) : LinearIndependent D.host.E (fam F0 F') := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := eq_zero_of_orth F0 F' hG c (fun a => by rw [hc, map_zero])
  intro i
  exact congrFun h0 i

theorem mem_orthK {U : Submodule D.host.E (VS D).V} {x : (VS D).V} :
    x ∈ orthK (VS D).hT U ↔ ∀ u ∈ U, (VS D).hT u x = 0 := by
  simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem inf_orth (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F') = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxU, hxO⟩ := hx
  rw [upair_eq, Submodule.mem_span_range_iff_exists_fun] at hxU
  obtain ⟨c, rfl⟩ := hxU
  have hc := eq_zero_of_orth F0 F' hG c (fun a => (mem_orthK.mp hxO) _
    (by rw [upair_eq]; exact Submodule.subset_span ⟨a, rfl⟩))
  rw [Submodule.mem_bot, hc]
  simp

theorem isCompl (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    IsCompl (UPair D F0 F') (orthK (VS D).hT (UPair D F0 F')) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    exact inf_orth F0 F' hG
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let Φ : ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) →ₗ[D.host.E]
        ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) :=
      { toFun := fun c a => (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i)
        map_add' := by
          intro c d
          ext a
          simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro s c
          ext a
          simp [mul_smul, ← Finset.smul_sum, mul_add] }
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      exact eq_zero_of_orth F0 F' hG c (fun a => congrFun hc a)
    obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun a => (VS D).hT (fam F0 F' a) v)
    have hu : ∑ i, c i • fam F0 F' i ∈ UPair D F0 F' := by
      rw [upair_eq]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hw : v - ∑ i, c i • fam F0 F' i ∈ orthK (VS D).hT (UPair D F0 F') := by
      rw [mem_orthK]
      intro u hu'
      rw [upair_eq] at hu'
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        have h1 := congrFun hc a
        simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1
        rw [map_sub, h1, sub_self]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | smul s x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
    have hv : v = ∑ i, c i • fam F0 F' i + (v - ∑ i, c i • fam F0 F' i) := by abel
    rw [hv]
    exact Submodule.add_mem_sup hu hw

theorem finrank_upair (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    finrank D.host.E (UPair D F0 F') = D.R.m := by
  rw [upair_eq, finrank_span_eq_card (fam_li F0 F' hG)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  have := D.R.rS_two
  omega

theorem finrank_V : finrank D.host.E (VS D).V = D.R.r := by
  rw [(VS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Formalism.BasicNotions.Ranks.rankY]

theorem X_le_upair : F0.X ≤ UPair D F0 F' := by
  unfold FlagG.X UPair
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  left
  exact ⟨i.castSucc, by simp [FlagG.fvec]⟩

theorem z_mem_upair : F0.z ∈ UPair D F0 F' := by
  unfold UPair
  exact Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)

theorem Xplus_le_upair : F0.Xplus ≤ UPair D F0 F' := by
  unfold FlagG.Xplus
  exact sup_le (X_le_upair F0 F') ((Submodule.span_singleton_le_iff_mem _ _).mpr (z_mem_upair F0 F'))

end PairSpanDimension


open PairSpanDimension in
theorem perpendicular_definition_holds : PerpDef := by
  intro D u u' _ F0 what₂ _ Z F' _ hZ hP
  have hG : GZ (Tn u) (Tn u') (ZhatL (lf D F0) F') ≠ 0 := by rw [hZ]; exact totPos_ne_zero hP
  have hC := PairSpanDimension.isCompl F0 F' hG
  have hU := PairSpanDimension.finrank_upair F0 F' hG
  have hW : finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) = D.R.k - 1 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := D.R.r_eq
    rw [PairSpanDimension.finrank_V, hU] at h1
    omega
  refine ⟨hC, ?_, hU, hW⟩
  intro x hx hx0 φ
  have hpos := Formalism.MainNotions.LatticeGluingRadicals.p_posX D (D.mem u).A.T (D.mem u).A.T_prime.pos (lf D F0)
  have hxO : x ∈ orth (VS D) (Xplus (lf D F0)) := by
    rw [Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth]
    intro w hw
    exact (PairSpanDimension.mem_orthK.1 hx) w (PairSpanDimension.Xplus_le_upair F0 F' hw)
  have hxX : x ∉ Xsp (lf D F0) := by
    intro hxX
    have : x ∈ UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F') := ⟨PairSpanDimension.X_le_upair F0 F' hxX, hx⟩
    rw [PairSpanDimension.inf_orth F0 F' hG] at this
    exact hx0 ((Submodule.mem_bot _).1 this)
  exact hpos φ x hxO hxX

end Formalism.L2.SG.Pf.Cnt
end
end

section

noncomputable section

open NumberField Module IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem frameAct_one (f : Fin (r + 1) → S.V) (b : Fin (r + 1)) : frameAct f 1 b = f b := by
  unfold frameAct
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Matrix.one_apply_ne hab]
  · simp

end General

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'}
  {Λ : Submodule (𝓞 D.host.E) (VS D).V}

theorem f_mem_UUS (i : Fin (D.R.rS + 1)) : F0.fvec i ∈ UUS D F0 F' := by
  unfold UUS
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have e : F0.fvec (Fin.last _) = F0.z := by simp [FlagG.fvec]
    rw [e]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  · have e : F0.fvec (Fin.castSucc a) = F0.e a := by simp [FlagG.fvec]
    rw [e]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
    exact Submodule.subset_span ⟨a, 1, one_mem_ddS D a, (one_smul _ _).symm⟩

theorem f'_mem_UUS (i : Fin (D.R.rS + 1)) : F'.fl.fvec i ∈ UUS D F0 F' := by
  unfold UUS
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have e : F'.fl.fvec (Fin.last _) = F'.fl.z := by simp [FlagG.fvec]
    rw [e]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · have e : F'.fl.fvec (Fin.castSucc a) = F'.fl.e a := by simp [FlagG.fvec]
    rw [e]
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact Submodule.subset_span ⟨a, 1, one_mem_ddS D a, (one_smul _ _).symm⟩

theorem spanE_UUS : spanE (VS D) (UUS D F0 F') = UPair D F0 F' := by
  apply le_antisymm
  · unfold spanE
    rw [Submodule.span_le]
    intro y hy
    have hle : UUS D F0 F' ≤ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
      unfold UUS
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · unfold XS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact (UPair D F0 F').smul_mem x (Submodule.subset_span (Or.inl ⟨Fin.castSucc a, by simp [FlagG.fvec]⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)
      · unfold XS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact (UPair D F0 F').smul_mem x (Submodule.subset_span (Or.inr ⟨Fin.castSucc a, by simp [FlagG.fvec]⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Or.inr ⟨Fin.last _, by simp [FlagG.fvec]⟩)
    exact hle hy
  · unfold UPair
    rw [Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Submodule.subset_span (f_mem_UUS i)
    · exact Submodule.subset_span (f'_mem_UUS i)

theorem UU_eq (hX0 : XLam Λ (lf D F0) = XS D F0) (hX1 : XLam Λ F' = XS D F'.fl) (hz : F'.zt = F'.fl.z) :
    UU Λ (lf D F0) F' = UUS D F0 F' := by
  unfold UU
  rw [hX0, hX1, hz]
  rfl

theorem blat_eq (hX0 : XLam Λ (lf D F0) = XS D F0) (hX1 : XLam Λ F' = XS D F'.fl) (hz : F'.zt = F'.fl.z) :
    BLat Λ (lf D F0) F' = Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
  unfold BLat UUE
  rw [UU_eq hX0 hX1 hz, spanE_UUS]

theorem mplus1_loc (hX0 : XLam Λ (lf D F0) = XS D F0) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (Mplus Λ (gS D) (lf D F0) F' 1) = Formalism.HermitianLatticesTheory.localization₂ P (BB D F0 F') := by
  rw [loc_BB_g D F0 F' P hg]
  refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (Submodule.span_le.2 ?_))
    (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))
  · rintro v ((hv | hv) | ⟨b, rfl⟩)
    · have hv' : v ∈ XS D F0 := by rw [← hX0]; exact hv
      refine ((XS_le_locP_e D F0 P hg).trans (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))) hv'
      rintro _ ⟨a, rfl⟩; exact e_mem_MMg D F0 F' a
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact Formalism.L2.SG.Pf.le_locP' _ _ (z_mem_MMg D F0 F')
    · refine Formalism.L2.SG.Pf.le_locP' _ _ ?_
      simp only [frame, frameAct_one]
      exact m_mem_MMg D F0 F' b
  · rintro v (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · induction i using Fin.lastCases with
      | last => rw [fvec_last]; exact Submodule.subset_span (Or.inl (Or.inr rfl))
      | cast a =>
        rw [fvec_cast]
        refine Submodule.subset_span (Or.inl (Or.inl ?_))
        rw [hX0]; exact e_mem_XS D F0 a
    · refine Submodule.subset_span (Or.inr ⟨b, ?_⟩)
      simp only [frame, frameAct_one]

theorem isAdmissibleIntegralBasisChange_one (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F') :
    AdmWit Λ (gS D) (lf D F0) F' 1 := by
  refine ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a, fun b P _ => ?_⟩
  have := P.isPrime
  have hm : (((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b) ∈ Λ := by
    have := MMg_le_BB D F0 F' (m_mem_MMg D F0 F' b)
    rw [← hB] at this
    exact this.1
  refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
  rw [one_smul]
  have e : frame F' b - frameAct (frame (lf D F0)) 1 b =
      ((gS D : ℕ) : 𝓞 D.host.E) • ((((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) := by
    rw [frameAct_one, smulO, map_natCast, smul_smul, mul_inv_cancel₀ (g_ne D), one_smul]
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm

theorem forward {Z : MatZ D} (hz : F'.zt = F'.fl.z) (hR : IsRowLat D F0 Λ) (hE : F' ∈ EZ T' F0 Λ Z) :
    Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F' := by
  obtain ⟨-, ⟨-, -, hL, hF⟩, hX0⟩ := hR
  obtain ⟨⟨hL', -, -⟩, h1, ⟨ξ, hξ, hgen⟩, ⟨hF', hX1⟩, -⟩ := hE
  rw [← blat_eq hX0 hX1 hz]
  apply Formalism.L2.SG.Pf.eq_of_locP
  intro P
  have := P.isPrime
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · rw [(hgen P).1 hg, Formalism.L2.SG.Pf.Mplus_eq_MplusInt hL hF hL' hF' P hg ξ hξ,
      ← Formalism.L2.SG.Pf.Mplus_eq_MplusInt hL hF hL' hF' P hg 1 h1, mplus1_loc hX0 P.asIdeal hg]
  · rw [(hgen P).2 hg, UU_eq hX0 hX1 hz, ← loc_BB_ng D F0 F' P.asIdeal hg]

theorem backward (hU : Formalism.MainNotions.BridgeRowsGenus.LocUnimod) {Z : MatZ D} (hz : F'.zt = F'.fl.z)
    (hZ : ZhatL (lf D F0) F' = Z) (hG : GZ T T' (Zhat F0 F'.fl) ≠ 0)
    (hlat : Submodule.IsLattice D.host.E Λ) (huni : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F') :
    IsRowLat D F0 Λ ∧ F' ∈ EZ T' F0 Λ Z := by
  have hw := indep D F0 F'.fl hG
  have hX0 := xlam0 hw hB
  have hX1 := xlam1 hw hB
  have hzΛ : F0.z ∈ Λ := BB_le_Lam hw hB (MMg_le_BB D F0 F' (z_mem_MMg D F0 F'))
  have hz'Λ : F'.fl.z ∈ Λ := BB_le_Lam hw hB (MMg_le_BB D F0 F' (z'_mem_MMg D F0 F'))
  have hFC0 : IsFixedConv Λ (gS D) (lf D F0) := by
    refine ⟨fun P => ?_, prim0 hw hB⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := xs_locGen D F0 P
    exact ⟨c, hc0, hc1, by rw [hX0]; exact hc2⟩
  have hFC1 : IsFixedConv Λ (gS D) F' := by
    refine ⟨fun P => ?_, prim1 hw hB⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := xs_locGen D F'.fl P
    exact ⟨c, hc0, hc1, by rw [hX1]; exact hc2⟩
  have h1 := isAdmissibleIntegralBasisChange_one hB
  refine ⟨⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus hU D.sp.cm (VS D) Λ hlat huni,
    ⟨hlat, huni, ⟨hzΛ, rfl⟩, hFC0⟩, hX0⟩, ⟨⟨hz'Λ, hz⟩, ⟨1, h1⟩, hG⟩, h1, ⟨1, h1, fun P => ?_⟩,
    ⟨hFC1, hX1⟩, hZ⟩
  have := P.isPrime
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [blat_eq hX0 hX1 hz, hB, mplus1_loc hX0 P.asIdeal hg]
  · rw [blat_eq hX0 hX1 hz, hB, UU_eq hX0 hX1 hz, loc_BB_ng D F0 F' P.asIdeal hg]

end Formalism.L2.SG.Pf.Cnt.R3

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmChar_of (hU : Formalism.MainNotions.BridgeRowsGenus.LocUnimod) : MMChar := by
  intro D u u' _ F0 what₂ _ Z F' hz hZ hP
  have hG : GZ (Tn u) (Tn u') (Zhat F0 F'.fl) ≠ 0 := by
    subst hZ
    exact totPos_ne D hP
  rw [MMof_eq]
  refine ⟨BB_latIn D F0 F', fun Λ => ⟨fun ⟨hR, hE⟩ => ?_, fun ⟨hlat, huni, hB⟩ => ?_⟩⟩
  · exact ⟨hR.2.1.1, hR.2.1.2.1, forward hz hR hE⟩
  · exact backward hU hz hZ hG hlat huni hB

end Formalism.L2.SG.Pf.Cnt
end
end
