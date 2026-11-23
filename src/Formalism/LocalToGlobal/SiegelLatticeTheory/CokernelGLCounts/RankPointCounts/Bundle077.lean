module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle039
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle071
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensCongPf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ddS_ne : ddS D ≠ 0 := by
  intro h
  apply shapeNZ.1 1
  unfold ddPow; rw [h]; simp

theorem ddPow_mul (i j : ℕ) : ddPow D i * ddPow D j = ddPow D (i + j) := by
  unfold ddPow
  rw [← zpow_add₀ ddS_ne]
  congr 1; push_cast; ring

theorem mem_ddPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ ddPow D (i + j) := by
  rw [← ddPow_mul]; exact FractionalIdeal.mul_mem_mul hx hy

theorem mem_qdPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ qdPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ qdPow D (i + j) := by
  have := FractionalIdeal.mul_mem_mul hx hy
  unfold qdPow at this ⊢
  rwa [mul_assoc, ddPow_mul] at this

theorem mem_ddPow_mul_qd {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ qdPow D j) :
    x * y ∈ qdPow D (i + j) := by
  rw [mul_comm, add_comm]; exact mem_qdPow_mul hy hx

theorem one_mem_ddPow0 : (1 : D.host.E) ∈ ddPow D 0 := by
  unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
  exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩

theorem qd_le_dd (h : ℕ) {x : D.host.E} (hx : x ∈ qdPow D h) : x ∈ ddPow D h := by
  rw [qdPow_mem_iff] at hx
  have h2 : ((gS D : ℕ) : D.host.E) ∈ ddPow D 0 := by
    unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨(gS D : ℕ), map_natCast _ _⟩
  have := mem_ddPow_mul h2 hx
  rwa [zero_add, mul_div_cancel₀ _ gS_ne] at this

def GrD (M : MatR D) : Prop := ∀ a c : Fin (D.R.rS + 1), a ≤ c → M a c ∈ ddPow D (c.val - a.val)

theorem grD_inv {X : MatR D} (hX : UpU X) (hG : GrD X) : GrD X⁻¹ := by
  have hXi := upU_inv hX
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have key : ∀ n : ℕ, ∀ a c : Fin (D.R.rS + 1), a ≤ c → c.val - a.val = n → X⁻¹ a c ∈ ddPow D n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a c hac hn
      rcases eq_or_lt_of_le hac with h | h
      · subst h; rw [(hXi a a).2 rfl]; simp only [Nat.sub_self] at hn; subst hn; exact one_mem_ddPow0
      ·
        have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv X hd) a) c
        rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt h), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
          (hX a a).2 rfl, one_mul] at h1
        have h2 : X⁻¹ a c = -∑ i ∈ Finset.univ.erase a, X a i * X⁻¹ i c := by
          rw [eq_neg_iff_add_eq_zero]; exact h1
        rw [h2]
        refine (ddPow D n : Submodule (𝓞 D.host.E) D.host.E).neg_mem (Submodule.sum_mem _ fun i hi => ?_)
        have hia : i ≠ a := Finset.ne_of_mem_erase hi
        by_cases hai : a < i
        · by_cases hic : i ≤ c
          · have hlt : c.val - i.val < n := by have : a.val < i.val := hai; omega
            have e : n = (i.val - a.val) + (c.val - i.val) := by have : a.val < i.val := hai; omega
            rw [e]
            exact mem_ddPow_mul (hG a i (le_of_lt hai)) (ih _ hlt i c hic rfl)
          · rw [(hXi i c).1 (lt_of_not_ge hic), mul_zero]; exact FractionalIdeal.zero_mem _
        · rw [(hX a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]; exact FractionalIdeal.zero_mem _
  intro a c hac
  exact key _ a c hac rfl

theorem inv_diff {X X' : MatR D} (hX : UpU X) (hX' : UpU X') {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hag : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val → X i j = X' i j) :
    X⁻¹ a c - X'⁻¹ a c = X' a c - X a c := by
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have hd' : IsUnit X'.det := by rw [upU_det hX']; exact isUnit_one
  have hXi := upU_inv hX
  have hXi' := upU_inv hX'
  have hm : X⁻¹ - X'⁻¹ = X⁻¹ * (X' - X) * X'⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd', Matrix.mul_one]
  have e := congrFun (congrFun hm a) c
  rw [Matrix.sub_apply] at e
  rw [e, Matrix.mul_apply, Finset.sum_eq_single c]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hXi a a).2 rfl, (hXi' c c).2 rfl, one_mul, mul_one, Matrix.sub_apply]
    · intro i _ hia
      by_cases hai : a < i
      · rw [Matrix.sub_apply]
        by_cases hic : i < c
        · rw [hag i c hic (by have : a.val < i.val := hai; have : i.val < c.val := hic; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hic) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i c).1 h, (hX i c).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]
    · simp
  · intro j _ hjc
    by_cases hjc' : j < c
    · rw [Matrix.mul_apply]
      refine mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _
      by_cases hai : a ≤ i
      · rw [Matrix.sub_apply]
        by_cases hij : i < j
        · rw [hag i j hij (by have : a.val ≤ i.val := hai; have : j.val < c.val := hjc'; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hij) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i j).1 h, (hX i j).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_not_ge hai), zero_mul]
    · rw [(hXi' j c).1 (lt_of_le_of_ne (not_lt.1 hjc') (Ne.symm hjc)), mul_zero]
  · simp

variable (w : Point D.host.E (D.R.rS + 1))

theorem Xmat_upU (y : FreeE w → D.host.E) : UpU (Xmat w y) := by
  intro a c
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [Xmat, ne_of_gt h, if_false]
    rw [dite_eq_right (fun h' => absurd h'.1 (not_lt.2 (le_of_lt h)))]
  · simp [Xmat, h]

theorem Xmat_blk (y : FreeE w → D.host.E) : IsBlockDiagonalMatrix w (Xmat w y) := by
  intro a c hne
  have hac : a ≠ c := fun e => hne (by rw [e])
  simp only [Xmat, hac, if_false]
  rw [dite_eq_right (fun h' => hne h'.2)]

theorem Xmat_q (y : FreeE w → D.host.E) (q : FreeE w) : Xmat w y q.1.1 q.1.2 = y q := by
  have hne : q.1.1 ≠ q.1.2 := ne_of_lt q.2.1
  simp only [Xmat, hne, if_false]
  rw [dite_eq_left q.2]
  rfl

theorem Xmat_grD (y : FreeE w → D.host.E) (hy : ∀ q, y q ∈ ddPow D (hgt w q)) : GrD (Xmat w y) := by
  intro a c hac
  rcases eq_or_lt_of_le hac with h | h
  · subst h; simp only [Xmat, if_true, Nat.sub_self]; exact one_mem_ddPow0
  · by_cases hb : blkOf w.1 a.val = blkOf w.1 c.val
    · have := Xmat_q w y ⟨(a, c), h, hb⟩
      simp only at this; rw [this]; exact hy ⟨(a, c), h, hb⟩
    · rw [Xmat_blk w y a c hb]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut

def TermHyp (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  IsTerm Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ AdmWit Λ₂ (gS D) (lf D F0) (liftF F'₂) 1 ∧
    IsGeneric Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ FrameOK D Λ₂ (liftF F'₂)

end BwdBetaCut

open BwdBetaCut

variable (u u' F0 what₂)

def BwdBeta' : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        TermHyp (F0 := F0) Λ₂ F'₂ →
        ∃ x : Carrier (PD D γ.lam (lf D F0) u'), TermDef.mk _ _ _ x = γ.cls ∧ Gval (lf D F0) x.1 ≠ 0 ∧
          ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V,
            IsPair γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β (gS D) ∧
            Lat.s0 γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β D.R.k = 1 ∧
            IsScalar γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β

def RepG : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ x : Carrier (PD D γ.lam (lf D F0) u'), x.1 = repF γ ∧ TermDef.mk _ _ _ x = γ.cls ∧ Gval (lf D F0) x.1 ≠ 0

def BetaCore : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        TermHyp (F0 := F0) Λ₂ F'₂ → PD D γ.lam (lf D F0) u' (repF γ) → Gval (lf D F0) (repF γ) ≠ 0 →
        ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V,
          IsPair γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β (gS D) ∧
          Hp γ.lam (lf D F0) (repF γ) ≤ Th γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β ∧
          IsScalar γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β

variable {u u' F0 what₂}

theorem bwdBeta'_of_core (hR : RepG u u' F0 what₂) (hB : BetaCore Zd u u' F0 what₂) : BwdBeta' Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT
  obtain ⟨x, hx, hmk, hG⟩ := hR hC γ Z hZ
  have hPD : PD D γ.lam (lf D F0) u' (repF γ) := hx ▸ x.2
  have hG' : Gval (lf D F0) (repF γ) ≠ 0 := hx ▸ hG
  obtain ⟨β, hP, hle, hsc⟩ := hB hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT hPD hG'
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hfix := hrow.2.1
  refine ⟨x, hmk, hG, β, hx ▸ hP, ?_, hx ▸ hsc⟩
  rw [hx]
  refine (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k (Corank.finrank_VS D) γ.lam hrow.1.1 (lf D F0) (repF γ) _ β
    hfix.2.2.1 hPD.1 hG').2 ?_
  exact le_antisymm (PI.PairCorankPos.W.Th_le_Hp _ _ _ _ _) hle

theorem bwdPair_of'' (h2 : BwdTerm' Zd u u' F0 what₂) (h4 : BwdBeta' Zd u u' F0 what₂) : BwdPair Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg
  have hT := h2 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩
  obtain ⟨hT1, hA, hG, hO⟩ := hT
  have hE := mem_EZ_of hn γ.lam Λ₂ (gmap_eq_of_image himg) (liftF F'₂) Z hT1 hA hG hO hS.1
  obtain ⟨x, hx, hGx, β, hP, hs0, hsc⟩ := h4 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg ⟨hT1, hA, hG, hO⟩
  have hPD : PD D γ.lam (lf D F0) u' (mapL n (isom_of_N0F hn) (liftF F'₂)) := ⟨hE.1.1, hE.1.2.1, hE.2.2.2.1⟩
  let pr : Corank.Pair D u u' F0 what₂ :=
    ⟨γ.lam, γ.mem, x, ⟨_, hPD⟩, hGx, hE.1.2.2, β, hP⟩
  refine ⟨⟨γ.lam, γ.mem, TermDef.mk _ _ _ ⟨_, hPD⟩⟩, ⟨pr, ?_, rfl, hs0, hsc⟩, hPD, rfl⟩
  exact congrArg (fun c => (⟨γ.lam, γ.mem, c⟩ : TermDef.Term D u u' F0 what₂)) hx

theorem bwdC_of''' (hC : CtxP u u' F0 what₂) (h1 : BwdN Zd u u' F0 what₂) (h2 : BwdTerm' Zd u u' F0 what₂)
    (h4 : BwdBeta' Zd u u' F0 what₂) : BwdC Zd u u' F0 what₂ := by
  intro γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨n, hn, himg⟩ := h1 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨hT, hA, hG, hO⟩ := h2 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩
  refine ⟨mapL n (isom_of_N0F hn) (liftF F'₂),
    ⟨?_, bwdPair_of'' Zd h2 h4 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg⟩, n, hn, ⟨fun a => rfl, rfl⟩, himg⟩
  exact mem_EZ_of hn γ.lam Λ₂ (gmap_eq_of_image himg) (liftF F'₂) Z hT hA hG hO hS.1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem split_finite : {p : PlF D | (Zd.M p).split.isSome}.Finite := by
  have hfinite (ℓ : ℕ) : {p : PlF D | Loc.resChar p = ℓ}.Finite := by
    have hsub : {p : PlF D | Loc.resChar p = ℓ} ⊆
        {v | v.asIdeal ∣ Ideal.span {(ℓ : 𝓞 D.host.F)}} := by
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      rw [Ideal.dvd_span_singleton, ← hp, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact ringChar.Nat.cast_ringChar
    by_cases hℓ : ℓ = 0
    · subst hℓ
      convert Set.finite_empty
      rename_i p
      change Loc.resChar p = 0 ↔ False
      simp only [iff_false]
      intro hp
      have h1 : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.absNorm_mem p.asIdeal
      have hc : CharP (𝓞 D.host.F ⧸ p.asIdeal) 0 := by
        have h2 := ringChar.charP (𝓞 D.host.F ⧸ p.asIdeal)
        unfold Loc.resChar at hp
        rwa [hp] at h2
      rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at h1
      exact p.ne_bot h1
    · refine (Ideal.finite_factors ?_).subset hsub
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hℓ
  refine ((hfinite (D.host.g 0)).union (hfinite (D.host.g 1))).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have hs : (D.s.atP p).split.isSome := by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hp
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hg] at hA
    cases h2 : (D.s.atP p).split with
    | none =>
      rw [h2] at hA
      exact (hA : False).elim
    | some sg => rfl
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (D.s_split p).1 hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hin
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  exact hin

theorem cohIota_holds : CohIota Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' _
  refine (split_finite Zd).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq]
  by_contra hn
  apply hp
  intro g hg
  rw [hg] at hn
  exact (hn rfl).elim

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf

theorem density_congruence_holds : Coef.DensCong := by
  intro F E _ _ _ _ _ _ _ M V _ _ H ϖ abelian₂ ι _ _ G A hA hdet
  obtain ⟨y, hy, hyd⟩ := hdet
  have hyd' : y * A.det = 1 := by rw [mul_comm]; exact hyd
  set B : Matrix ι ι E := y • A.adjugate with hBdef
  have hB : ∀ i j, B i j ∈ M.L.O := fun i j => by
    simp only [hBdef, Matrix.smul_apply, smul_eq_mul]
    exact M.L.O.mul_mem hy (DensCongPf.adj_mem A hA i j)
  have hAB : A * B = 1 := by
    rw [hBdef, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hyd', one_smul]
  have hBA : B * A = 1 := by
    rw [hBdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hyd', one_smul]
  have hm : ∀ X Y : Matrix ι ι E, (X * Y).map M.L.cj = X.map M.L.cj * Y.map M.L.cj := by
    intro X Y
    ext i j

    simp [Matrix.mul_apply, map_sum, map_mul]
  have hone : (1 : Matrix ι ι E).map M.L.cj = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hG : (B.map M.L.cj).transpose * ((A.map M.L.cj).transpose * G * A) * B = G := by
    calc _ = ((A * B).map M.L.cj).transpose * G * (A * B) := by
          rw [hm, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hAB, hone, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  unfold MainNotions.S.Loc.HermSp.dens
  congr 2
  have fwd : ∀ (K P Q : Matrix ι ι E) (hP : ∀ i j, P i j ∈ M.L.O), (∀ i j, Q i j ∈ M.L.O) →
      P * Q = 1 → Q * P = 1 → ∀ x, x ∈ Set.range (fun (v : {v : ι → V // H.Prim abelian₂ v ∧
        ∀ a b, H.h (v b) (v a) - K a b ∈ (M.L.O ∙ (algebraMap F E) ↑ϖ)}) (a : ι) =>
          (Submodule.Quotient.mk (p := H.smulLat ((algebraMap F E) ↑ϖ) abelian₂) (v.1 a))) →
      DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) P hP x ∈ Set.range (fun (v : {v : ι → V //
        H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - ((P.map M.L.cj).transpose * K * P) a b ∈
          (M.L.O ∙ (algebraMap F E) ↑ϖ)}) (a : ι) =>
          (Submodule.Quotient.mk (p := H.smulLat ((algebraMap F E) ↑ϖ) abelian₂) (v.1 a))) := by
    rintro K P Q hP hQ hPQ hQP x ⟨⟨v, hv1, hv2⟩, rfl⟩
    exact ⟨⟨DensCongPf.act P v, DensCongPf.prim_act H abelian₂ P Q hP hQ hPQ hQP v hv1,
      DensCongPf.cong_act H _ P K hP v hv2⟩, (DensCongPf.psi_mk H abelian₂ _ P hP v).symm⟩
  refine Nat.card_congr
    { toFun := fun x => ⟨DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) B hB x.1, by
        have h := fwd _ B A hB hA hBA hAB x.1 x.2
        rw [hG] at h
        exact h⟩
      invFun := fun x => ⟨DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) A hA x.1,
        fwd G A B hA hB hAB hBA x.1 x.2⟩
      left_inv := fun x => Subtype.ext (DensCongPf.psi_psi H abelian₂ _ B A hB hA hBA x.1)
      right_inv := fun x => Subtype.ext (DensCongPf.psi_psi H abelian₂ _ A B hA hB hAB x.1) }

end Formalism.L2.SG.Pf
end
end
