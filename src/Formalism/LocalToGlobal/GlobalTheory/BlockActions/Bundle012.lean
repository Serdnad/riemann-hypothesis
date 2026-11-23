module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle005
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle007
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle010
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.IsUnitBZMap
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle011
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle009
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormalFormAgree
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabiliserBijectiveOfFinite
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField
open scoped ComplexOrder



theorem normClsAt_of_tors (hT : ChiTors) : NormClsAt := by
  intro D u Ch chOf Tf hL hBe h s x Pc hPc Qc hQc o ho o' ho' c
  classical
  have hbase := base_eq Tf hL h x Pc hPc Qc hQc c
  obtain ⟨k, hk, hχ⟩ := hT D u Ch chOf Tf c
  obtain ⟨a, ha, has⟩ := desc_scalar D.what₂.embLL (Qc c) (brTenL D u (PL Tf c (Pc ((D.fm u).til c)))) _ k hk hχ hbase
  have hAsu : ∀ τ, IsUnit ((AL Tf c τ).map s).det := fun τ => isUnit_AL_map Tf c s τ
  have hR : MvPolynomial.map s (Pc ((D.fm u).til c)) ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) :=
    map_mem_CSpan_of_rat _ _ (pc_rat Tf x Pc hPc _) s
  have hY := blkRow_mem_CSpan _ (fun τ => (AL Tf c τ).map s) hAsu _ hR
  have hQs : MvPolynomial.map s (Qc c) = (s a * ∏ τ, ((AL Tf c τ).map s).det ^ shiftOf (lamT u D.R.m) τ) •
      Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s) (MvPolynomial.map s (Pc ((D.fm u).til c)))) := by
    rw [ha, MvPolynomial.smul_eq_C_mul, map_mul, map_C, map_brTenL, map_PL, map_smul, ← MvPolynomial.smul_eq_C_mul,
      smul_smul]
  have hoN : ∀ τ, (o.1 τ)ᴴ * gramC (gramN D D.R.m le_rfl) (embS D s) τ * o.1 τ = 1 := fun τ =>
    Formalism.L2.Col.frame_pos o ho τ (gramN_posDef_at Tf (embS D s τ)).posSemidef
  have hoP : ∀ τ, (o'.1 τ)ᴴ * gramC (gramP D) (embS D s) τ * o'.1 τ = 1 := fun τ =>
    Formalism.L2.Col.frame_pos o' ho' τ (gramP_posDef_at Tf (embS D s τ)).posSemidef
  have hon : ∀ τ, ((AL Tf c τ).map s * dOT u (o'.1 τ))ᴴ * gramC (gramN D D.R.m le_rfl) (embS D s) τ *
      ((AL Tf c τ).map s * dOT u (o'.1 τ)) = 1 := by
    intro τ
    rw [AL_map, Matrix.map_mul]
    exact frame_on_at Tf c (embS D s τ) (o'.1 τ) (hoP τ)
  have hind := term_frame_indep ((D.fm u).lam D.R.m) (gramC (gramN D D.R.m le_rfl) (embS D s)) (shiftOf (lamT u D.R.m)) o.1
    (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) hoN hon (MvPolynomial.map s (Pc ((D.fm u).til c)))
  have hchain := chain_at Tf hBe o'.1 o'.2 _ hY
  have hcomp : blkRow (fun τ => dOT u (o'.1 τ)) (blkRow (fun τ => (AL Tf c τ).map s) (MvPolynomial.map s (Pc ((D.fm u).til c)))) =
      subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))) := blkRow_comp _ _ _
  rw [hcomp] at hchain
  rw [hQs, map_smul, nfAll_smul_reB, normal_form_agree, hind]
  have hdet : ∏ τ, ‖((AL Tf c τ).map s * dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) =
      (∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        ∏ τ, ‖(dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_mul, norm_mul, mul_zpow]
  have hκ : ‖s a * ∏ τ, ((AL Tf c τ).map s).det ^ shiftOf (lamT u D.R.m) τ‖ ^ 2 =
      ‖s a‖ ^ 2 * ∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_zpow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm (shiftOf (lamT u D.R.m) τ)]
    norm_num
  rw [hdet, hκ]
  have hsa : ‖s a‖ ^ 2 ≤ 1 := by
    have h1 := has s
    have h0 := norm_nonneg (s a)
    nlinarith
  set nW := (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s)
    (MvPolynomial.map s (Pc ((D.fm u).til c)))))) (subP o'.1 (Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s)
    (MvPolynomial.map s (Pc ((D.fm u).til c))))))).re with hnW
  set K2 := ∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)
  set KA := ∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)
  have hKA : 0 ≤ KA := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  have hK2 : 0 ≤ K2 := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  have hnW : 0 ≤ nW := Formalism.L2.Ker.ta_nfAll_nonneg _ _
  calc K2 * (‖s a‖ ^ 2 * KA * nW) = ‖s a‖ ^ 2 * (KA * (K2 * nW)) := by ring
    _ ≤ 1 * (KA * (ptB D u * ((∏ τ, ‖(dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
          (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))))
            (subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))))).re))) :=
        mul_le_mul hsa (mul_le_mul_of_nonneg_left hchain hKA) (mul_nonneg hKA (mul_nonneg hK2 hnW)) zero_le_one
    _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

theorem mulLat_one {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  unfold mulLat
  convert Submodule.map_id L
  ext x i
  simp

theorem dualL_stable {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (γ γi : Matrix (Fin n) (Fin n) E) (hγi : γi * γ = 1) (hγ' : γ * γi = 1)
    (hU : cT σ γ * J * γ = J) (hL : mulLat γ L = L) :
    ∀ y ∈ dualL σ J L, γ *ᵥ y ∈ dualL σ J L := by
  have hLi : mulLat γi L = L := by
    conv_lhs => rw [← hL]
    rw [mulLat_mulLat, hγi, mulLat_one]
  have hset : ∀ y ∈ dualSet σ J L, γ *ᵥ y ∈ dualSet σ J L := by
    intro y hy x hx
    have hxi : γi *ᵥ x ∈ L := by
      rw [← hLi]; exact Submodule.mem_map_of_mem hx
    have e : x = γ *ᵥ (γi *ᵥ x) := by rw [mulVec_mulVec, hγ', one_mulVec]
    rw [e, hform_UJ σ J γ hU]
    exact hy _ hxi
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span (hset z hz)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have e : γ *ᵥ (r • a) = r • (γ *ᵥ a) := by
      rw [← algebraMap_smul E r a, mulVec_smul, algebraMap_smul]
    rw [e]; exact Submodule.smul_mem _ r ha

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem stabLF_of (Tf : FormsTiedSym D u Ch chOf)
    (h : ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
      γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
      mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) = clsCrd D u D.R.m le_rfl ((D.fm u).til c) ∧
      ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
        (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
          (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)) :
    StabLF Tf := by
  intro c γ hγ
  obtain ⟨hL, hf⟩ := h c γ hγ
  refine ⟨hL, ?_, hf⟩
  have h1 : (γ.1⁻¹ : GL _ _).1 * γ.1.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : γ.1.1 * (γ.1⁻¹ : GL _ _).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact dualL_stable _ _ _ γ.1.1 _ h1 h2 γ.2 hL

end Formalism.L2.GlobalTheoryTheory.Br
end
end
