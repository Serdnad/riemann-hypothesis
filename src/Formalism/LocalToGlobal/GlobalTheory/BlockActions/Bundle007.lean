module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.TiedBrProof
import Formalism.LocalToGlobal.HermitianForms.Bundle004
import Formalism.LocalToGlobal.HermitianForms.TiedBrCl
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LowerTieChain
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField

theorem exists_map_of_ratSpan (D : D7) {n : ℕ} {lam : D.what₂.Tau → DomWeight n}
    {p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hp : p ∈ RatSpan D lam) :
    ∃ F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL, MvPolynomial.map D.what₂.embLL F = p := by
  have hle : RatSpan D lam ≤ (MvPolynomial.map (σ := D.what₂.Tau × Fin n × Fin n) D.what₂.embLL).range.toAddSubgroup := by
    unfold RatSpan
    refine (AddSubgroup.closure_le _).2 ?_
    rintro q ⟨r, f, -, rfl⟩
    refine RingHom.mem_range.2
      ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hi : D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    congr 1
    unfold Formalism.L2.Forms.ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map, hi]
  obtain ⟨F, hF⟩ := RingHom.mem_range.1 (hle hp)
  exact ⟨F, hF⟩

def FramesAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf)
    (s : D.what₂.LL →+* ℂ),
    (∃ o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s)), o.IsON) ∧ ∃ o : Frames (gramC (gramP D) (embS D s)), o.IsON

def NormClsAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u →
    ∀ (h : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ) (x : Vl D u D.R.m)
      (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL),
      (∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) →
    ∀ (Qc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
      (∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
        fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c))) →
    ∀ (o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s))), o.IsON →
    ∀ (o' : Frames (gramC (gramP D) (embS D s))), o'.IsON →
    ∀ c, (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
        (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re ≤
      ptB D u * ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))
          (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))).re)

theorem ptB_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ ptB D u :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)

theorem wt_re_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (c : (D.mem u).C.cls i) :
    ((D.mem u).C.wt i c).re = ((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ := by
  unfold ColumnChain.wt
  rw [show (((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℂ))⁻¹ = ((((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

theorem sum_le_of_inj {α β : Type} [Fintype α] [Fintype β] (f : α → β) (hf : Function.Injective f) (a : α → ℝ) (b : β → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, 0 ≤ b y) (hab : ∀ x, a x ≤ B * b (f x)) : ∑ x, a x ≤ B * ∑ y, b y := by
  classical
  calc ∑ x, a x ≤ ∑ x, B * b (f x) := Finset.sum_le_sum fun x _ => hab x
    _ = B * ∑ y ∈ Finset.univ.image f, b y := by
        rw [Finset.sum_image (fun x _ y _ h => hf h), Finset.mul_sum]
    _ ≤ B * ∑ y, b y := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => hb y) hB

theorem norm_bound_of_classes_frames (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hF : FramesAt) (hC : NormClsAt) : NormBoundAtInfinity := by
  intro D u Ch chOf Tf hL hB h v x
  obtain ⟨s, rfl⟩ : ∃ s, InfinitePlace.mk s = v := ⟨v.embedding, v.mk_embedding⟩

  have hx := ((Tf.val D.R.m le_rfl (Or.inr rfl)).rat ((D.fm u).emb D.R.m x)).1 ⟨x, rfl⟩
  choose P hP hPz using hx.2
  choose Pc hPc using fun c => exists_map_of_ratSpan D (hP c)
  have hrep : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z) := fun c z => by rw [hPc c]; exact hPz c z

  have hy := (Tf.valP.rat ((D.fm u).ptEmb ((D.fm u).PtL h x))).1 ⟨_, rfl⟩
  choose Q hQ hQz using hy.2
  choose Qc hQc using fun c => exists_map_of_ratSpan D (hQ c)
  have hrepP : ∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c)) := fun c => by rw [hQc c]; exact hQz c
  obtain ⟨⟨o, ho⟩, ⟨o', ho'⟩⟩ := hF D u Ch chOf Tf s
  rw [Tf.normP s _ Qc hrepP o' ho', Tf.norm D.R.m le_rfl (Or.inr rfl) s x Pc hrep o ho]
  refine sum_le_of_inj _ (h1 D u Ch chOf Tf) _ _ _ (ptB_nonneg D u) (fun c => ?_) (fun c => ?_)
  · refine mul_nonneg (mul_nonneg ?_ (Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _))
      (Formalism.L2.Ker.ta_nfAll_nonneg ((D.fm u).lam D.R.m) _)
    rw [wt_re_eq]; positivity
  · have hcard : Nat.card ((D.fm u).stabilizer₂ c) = Nat.card ((D.mem u).C.stab D.R.m ((D.fm u).til c)) :=
      Nat.card_congr (Equiv.ofBijective _ (h2 D u Ch chOf Tf c))
    have hk := hC D u Ch chOf Tf hL hB h s x Pc hrep Qc hrepP o ho o' ho' c
    rw [wt_re_eq, ← hcard]
    have hw : 0 ≤ ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ := by positivity
    calc ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re
        = ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * ((∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hw
      _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms

theorem bij_of_inj_back {A B : Type} [Finite A] (f : A → B) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    Function.Bijective f := by
  haveI : Finite B := Finite.of_injective g hg
  exact hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective g hg)

theorem stabiliser_bijective_of_injection
    (h : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      ∀ c, ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g) :
    StabiliserMapBijective := by
  intro D u Ch chOf Tf c
  obtain ⟨g, hg⟩ := h D u Ch chOf Tf c
  exact bij_of_inj_back _ ((D.fm u).stabMap_inj c) g hg

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brTen_blkRowS (Tf : FormsTiedSym D u Ch chOf) (G : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brTen D u (blkRow (fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
              Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose) P) =
      blkRow (fun τ => (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose) (Formalism.L2.Ker.brTen D u P) := by
  have hS : ∀ τ, Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    fun τ => Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  rw [blkRow_eq_blk, blkRow_eq_blk]
  unfold Formalism.L2.Ker.brTen
  rw [Formalism.L2.Ker.ta_blk_comp, Formalism.L2.Ker.ta_blk_comp]
  have e : (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ∘ₗ
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m) ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
        Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose).toLinearMap)) =
      fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m - 1) (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose).toLinearMap ∘ₗ
        Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) := by
    funext τ f
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    exact brOne_rowAct (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (hS τ) (G τ) f
  rw [e]

theorem shift_lamT_sgTS (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) :
    shiftOf (lamT u D.R.m) τ = shiftOf (sgT u) τ := by
  have hS : Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have h1 : 0 < D.R.N D.R.m := by omega
  have h2 : 0 < D.R.N D.R.m - 1 := by omega
  have hS' : (sgTr D u τ).detShift = (lamTr D u τ).detShift := hS
  unfold lamTr sgTr at hS'
  rw [detShift_wSh _ _ h1, detShift_wSh _ _ h2] at hS'
  simp only [shiftOf, lamT, sgT]
  rw [detShift_shW _ _ h1, detShift_shW _ _ h2]
  unfold cTw at hS'
  omega

theorem exP_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) :
    ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c))) := by
  intro w φ hφ c
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  refine ⟨P, hP, hv, fun z hz => ?_⟩
  have hBc := hB w c
  have hU1 := atInf_inv_isUnit _ hBc
  have hbZ := bZ_isUnitS Tf
  have hbZg := bZg_isUnitS Tf (B w c) hBc
  have hU2 := atInf_inv_isUnit _ hbZg

  have hL : coPTS Tf B w z c = (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (_root_.Formalism.L2.Forms.embT D) (B w c)⁻¹ τ)⁻¹).det ^ shiftOf (sgT u) τ) •
      blkRow (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
        (atInf (_root_.Formalism.L2.Forms.embT D) (B w c)⁻¹ τ)⁻¹) (Formalism.L2.Ker.brTen D u P) := by
    have e1 : coPTS Tf B w z c = fnInv (gramC (gramP D) (_root_.Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) (atInf (_root_.Formalism.L2.Forms.embT D) (B w c)⁻¹) (Tf.valP.eW z c) := rfl
    rw [e1, hz, fnOf_change _ _ (atInf (_root_.Formalism.L2.Forms.embT D) (B w c)⁻¹) 1 hU1, fnInv_fnOf _ _ _ hU1]

  have hM : trEvS Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  have hR : coMTS Tf B w c (φ ((D.fm u).til c)) = (∏ τ, (atInf (_root_.Formalism.L2.Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ *
      (atInf (_root_.Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹).det ^ shiftOf (lamT u D.R.m) τ) •
      blkRow (fun τ => atInf (_root_.Formalism.L2.Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (_root_.Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) P := by
    change fnInv (gramC (gramN D D.R.m le_rfl) (_root_.Formalism.L2.Forms.embT D))
      (shiftOf (lamT u D.R.m)) (atInf (_root_.Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹)
      (trEvS Tf c (φ ((D.fm u).til c))) = _
    rw [hM, mZ, fnOf_change _ _ (atInf (_root_.Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (atInf (_root_.Formalism.L2.Forms.embT D) (bZ u Tf.til.z0)⁻¹) hU2,
      fnInv_fnOf _ _ _ hU2]
  have hKm : (fun τ => atInf (_root_.Formalism.L2.Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (_root_.Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) =
      fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (glT (B w c) hBc τ) : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [embGL_glT, atInf_inv_inv _ hbZg, bZg_eq_mul]
    show (bZ u Tf.til.z0)⁻¹.map (_root_.Formalism.L2.Forms.embT D τ) * (bZ u Tf.til.z0 * dgE (B w c)).map (_root_.Formalism.L2.Forms.embT D τ) = _
    rw [← Matrix.map_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbZ, Matrix.one_mul]
  have hKp : (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (_root_.Formalism.L2.Forms.embT D) (B w c)⁻¹ τ)⁻¹) = fun τ => ((glT (B w c) hBc τ : GL (Fin (D.R.N D.R.m - 1)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [glT_val, Matrix.transpose_transpose, Pi.one_apply, Matrix.one_mul, atInf_inv_inv _ hBc]
    rfl
  rw [hL, hR, hKm, hKp, map_smul, brTen_blkRowS Tf]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrFun hKm τ
  have h2 := congrFun hKp τ
  rw [h1, h2, shift_lamT_sgTS Tf τ, embGL_glT, glT_val, Matrix.det_transpose]
  unfold dgE
  rw [Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.det_submatrix_equiv_self, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_transpose]

structure RestrictionSymmetric (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMTS Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))).re

theorem pendRest_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionSymmetric Tf B gP) :
    PendRestS Tf B gP :=
  ⟨exP_ofS Tf B hB, h.lat_co, h.pt_co, h.ipV_co, h.re_petersson_self_eq_sum_coord⟩

theorem brExists_of_rest4S (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionSymmetric Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_restS Tf B hB hL gP (pendRest_ofS Tf B hB gP h)

theorem weightedInner_self_eq_sum_coords_of_orthonormal' (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) (o : FrP D) (ho : o.IsON) :
    ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c))
        (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c))).re := by
  classical
  intro w z hz
  have hQ : ∀ c, blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c) ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
    intro c
    have h0 := coP_mem_of_isUnit_det' Tf B hB w z hz c
    rw [← cspan_sgTr] at h0
    have h1 := Formalism.L2.Ker.lc_blk_sqAct_mem _ (gPof B hB o w c) _ h0
    rw [cspan_sgTr] at h1
    exact h1
  have hE : ∀ c, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹)
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c)) := by
    intro c
    obtain ⟨Q, _, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
    have hc : coPTS Tf B w z c = Q := by
      change fnInv (gramC (gramP D) (_root_.Formalism.L2.Forms.embT D)) (shiftOf (sgT u))
        (atInf (embT D) (B w c)⁻¹) (Tf.valP.eW z c) = Q
      rw [hq]
      exact fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c)) Q
    have hs : shiftOf (sgT u) = fun τ => (sgTr D u τ).detShift := funext fun τ => (shift_sgTr τ).symm
    rw [hc, hq, hs, fnOf_sqAct _ (sgTr D u) (atInf (_root_.Formalism.L2.Forms.embT D) (B w c)⁻¹) o.1 o.2 _ (fun τ => rfl)]
    rfl
  rw [Tf.valP.ipP o ho z z _ _ hQ hQ hE hE, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ)⁻¹ = (((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

variable {D : D7}

section IsExtAlg

variable {z0 : Fin (D.R.N D.R.m) → D.host.E} {R : Type} [CommRing R] {φ : D.host.E →+* R}

theorem isExt_mul {a b : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R} {A B : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R}
    (ha : IsExt D z0 φ a A) (hb : IsExt D z0 φ b B) : IsExt D z0 φ (a * b) (A * B) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_assoc, hb1, ← Matrix.mul_assoc, ha1, Matrix.mul_assoc]
  · rw [← mulVec_mulVec, hb2, ha2]

theorem isExt_inv {a a' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R} {A A' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R}
    (ha : IsExt D z0 φ a A) (hA : A' * A = 1) (ha' : a * a' = 1) : IsExt D z0 φ a' A' := by
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨?_, ?_⟩
  · calc A' * (iXm D).map φ = A' * ((iXm D).map φ * (a * a')) := by rw [ha', Matrix.mul_one]
      _ = (A' * A) * (iXm D).map φ * a' := by rw [← Matrix.mul_assoc ((iXm D).map φ), ← ha1]; simp only [Matrix.mul_assoc]
      _ = (iXm D).map φ * a' := by rw [hA, Matrix.one_mul]
  · conv_lhs => rw [← ha2]
    rw [mulVec_mulVec, hA, one_mulVec]

theorem isExt_map {a : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E} {A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E}
    (ha : IsExt D z0 (RingHom.id D.host.E) a A) : IsExt D z0 φ (a.map φ) (A.map φ) := by
  obtain ⟨ha1, ha2⟩ := ha
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  rw [hm] at ha1
  refine ⟨?_, ?_⟩
  · rw [← Matrix.map_mul, ha1, Matrix.map_mul]
  · have hz : (fun i => (RingHom.id D.host.E) (z0 i)) = z0 := rfl
    rw [hz] at ha2
    funext i
    have := congrArg (fun w => φ (w i)) ha2
    rw [← this, RingHom.map_mulVec]; rfl

end IsExtAlg

variable {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}



theorem til_eq_level (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ∃ (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
      (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      (∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y) ∧
      IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1 ∧
      G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U ∧
      (Tf.clsP.y c').1.1 * k = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 := by
  set incl : D.host.E →+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F :=
    inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hincl
  obtain ⟨δ, hδE, hδi⟩ := til_eq_ext Tf hC hSD hdeg v c c' h
  have hdet : ∀ d : (D.fm u).clsP, IsUnit ((Tf.clsP.y d).1.1).det := fun d =>
    (Matrix.isUnit_iff_isUnit_det _).mp (Tf.clsP.y d).1.isUnit
  have ext_of : ∀ d : (D.fm u).clsP, ∃ Gd : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsExt D Tf.til.z0 incl (Tf.clsP.y d).1.1 Gd.1 := by
    intro d
    obtain ⟨g, hg, hu⟩ := til_ext Tf incl (Tf.clsP.y d).1.1
    exact ⟨((Matrix.isUnit_iff_isUnit_det g).mpr (hu (hdet d))).unit, hg⟩
  obtain ⟨Gc, hGc⟩ := ext_of c
  obtain ⟨Gc', hGc'⟩ := ext_of c'
  have e1 := Tf.tilAd.til_ad c Gc hGc
  have e2 := Tf.tilAd.til_ad c' Gc' hGc'
  rw [← h] at e2
  have hGc1 : Gc = bc incl (Tf.til.ga c).1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c).1)⁻¹ := eq_mul_inv_of_mul_eq e1.symm
  have hGc2 : Gc' = bc incl (Tf.til.ga c').1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c').1)⁻¹ := eq_mul_inv_of_mul_eq e2.symm
  set Γ := bc incl (Tf.til.ga c').1 * (bc incl (Tf.til.ga c).1)⁻¹ with hΓ
  refine ⟨δ, ((Tf.clsP.y c').1.1)⁻¹ * δ.map incl * (Tf.clsP.y c).1.1, Gc'⁻¹ * Γ * Gc, hδE, hδi, ?_, ?_, ?_⟩
  · have hinv : IsExt D Tf.til.z0 incl ((Tf.clsP.y c').1.1)⁻¹ (Gc'⁻¹).1 :=
      isExt_inv hGc' (Units.inv_mul Gc') (Matrix.mul_nonsing_inv _ (hdet c'))
    have hΓ1 : (Γ.1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
        ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1).map incl := by
      rw [hΓ, Units.val_mul, Matrix.map_mul]
      congr 1
    have hG : IsExt D Tf.til.z0 incl (δ.map incl) Γ.1 := by rw [hΓ1]; exact isExt_map hδE
    rw [Units.val_mul, Units.val_mul]
    exact isExt_mul (isExt_mul hinv hG) hGc
  · have : Gc'⁻¹ * Γ * Gc = (Tf.tilAd.ka c').1 * ((Tf.tilAd.ka c).1)⁻¹ := by
      rw [hGc1, hGc2, hΓ]; group
    rw [this]
    exact Subgroup.mul_mem _ (Tf.tilAd.ka c').2 (Subgroup.inv_mem _ (Tf.tilAd.ka c).2)
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet c'), Matrix.one_mul]

end Formalism.L2.GlobalTheoryTheory.Br
end
end
