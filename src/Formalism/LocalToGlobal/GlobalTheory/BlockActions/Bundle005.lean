module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormOneOfPow
public import Formalism.LocalToGlobal.HermitianForms.Bundle006
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle004
import Formalism.LocalToGlobal.HermitianForms.Bundle004
public import Formalism.LocalToGlobal.HermitianForms.TiedBrCl
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

structure PendClausesS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  coM_mem : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m)
  coM_inj : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0
  coP_mem : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg
  coP_inj : ∀ w, ∀ z ∈ (D.fm u).ptC, coPTS Tf B w z = 0 → z = 0
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c)))
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

def pendOfS (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClausesS Tf B gP) : Pend D u where
  br τ := Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)
  coM := coMTS Tf B
  coP := coPTS Tf B
  coM_mem := h.coM_mem
  coM_inj := h.coM_inj
  coP_mem := h.coP_mem
  coP_inj := h.coP_inj
  Pt_eq := by
    intro w φ hφ c
    obtain ⟨P, hP, hv, hz⟩ := h.exP w φ hφ c
    exact hz _ (hL.map.pt_eq (bZ_isUnitS Tf) φ c P hP hv)
  lat_co := h.lat_co
  pt_co := h.pt_co
  gP := gP
  ipV_co := h.ipV_co
  re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord
  beOn_eq := hL.beOn
  interlace := sg_interlace Tf.valP

theorem brExists_of_tiedS (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClausesS Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  ⟨pendOfS Tf hL B gP h, archimedeanSignatureMatching_of_trivial_branching_symm Tf _ fun _ => rfl⟩

section Cl

theorem bZg_isUnitS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) :
    IsUnit (bZg u Tf.til.z0 B').det := by
  have hBi : Function.Injective B'.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hB')
  refine isUnit_det_cols (Nm_succ D.R) (iXm D * B') (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) ?_ ?_
  · intro x y h
    simp only [← Matrix.mulVec_mulVec] at h
    exact hBi (iXm_mulVec_injective D h)
  · intro x h
    apply quotient_not_in_range_symmetric Tf (B' *ᵥ x)
    rw [Matrix.mulVec_mulVec]; exact h

theorem trEv_repS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m), trEvS Tf c (φ ((D.fm u).til c)) =
      fnOf _ (shiftOf (lamT u D.R.m)) (atInf (embT D) (bZg u Tf.til.z0 B')⁻¹) Q := by
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  have hM : trEvS Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  have hU := atInf_inv_isUnit _ (bZg_isUnitS Tf B' hB')
  rw [hM]
  exact exists_change _ _ _ _ _ hU P hP

theorem eW_repS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan (D.fm u).sg, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (atInf (embT D) B'⁻¹) Q := by
  have hF := (Tf.valP.ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (Tf.clsP.y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
    have := CSpan_shW (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgT at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hU := atInf_inv_isUnit _ hB'
  rw [he]
  exact exists_change _ _ _ _ _ hU Q0 hQ0'

variable (Tf : FormsTiedSym D u Ch chOf)
  (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  (hB : ∀ w c, IsUnit (B w c).det)

include hB

theorem coM_mem_ofS : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    coMTS Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m) := by
  intro w c φ hφ
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    change fnInv (gramC (gramN D D.R.m le_rfl) (Formalism.L2.Forms.embT D)) (shiftOf (lamT u D.R.m))
      (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (trEvS Tf c (φ ((D.fm u).til c))) = Q
    rw [hq]
    exact fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c))) Q
  rw [this]; exact hQ

theorem coP_mem_of_isUnit_det' : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg := by
  intro w z hz c
  obtain ⟨Q, hQ, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
  have : coPTS Tf B w z c = Q := by
    change fnInv (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u))
      (atInf (embT D) (B w c)⁻¹) (Tf.valP.eW z c) = Q
    rw [hq]
    exact fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c)) Q
  rw [this]; exact hQ

theorem coP_inj_of_isUnit_det' : ∀ w, ∀ z ∈ (D.fm u).ptC, coPTS Tf B w z = 0 → z = 0 := by
  intro w z hz h0
  apply Tf.valP.eW.injective
  rw [map_zero]
  funext c
  obtain ⟨Q, hQ, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
  have : coPTS Tf B w z c = Q := by
    change fnInv (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u))
      (atInf (embT D) (B w c)⁻¹) (Tf.valP.eW z c) = Q
    rw [hq]
    exact fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c)) Q
  have hQ0 : Q = 0 := by rw [← this, h0]; rfl
  rw [hq, hQ0, map_zero]; rfl

theorem coM_inj_ofS : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0 := by
  intro w c φ hφ h0
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have hc : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    change fnInv (gramC (gramN D D.R.m le_rfl) (Formalism.L2.Forms.embT D)) (shiftOf (lamT u D.R.m))
      (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (trEvS Tf c (φ ((D.fm u).til c))) = Q
    rw [hq]
    exact fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c))) Q
  have ht : trEvS Tf c (φ ((D.fm u).til c)) = 0 := by rw [hq, ← hc, h0, map_zero]
  funext s'
  let ga : GL (Fin (D.R.N D.R.m)) D.host.E := (Tf.til.ga c).1
  have hy := congrFun ht (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').tr (atInf (embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga))
  simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hy
  have hback : (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').tr (atInf (embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga)).tr
      (atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga⁻¹) =
      (Tf.val D.R.m le_rfl (Or.inr rfl)).eY s' := by
    apply Subtype.ext
    funext τ
    show atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
      (atInf (embT D) (ga : Matrix _ _ D.host.E) τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').1 τ) = ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').1 τ
    have h1 := atInf_mul_inv (embT D) ga⁻¹ τ
    rw [inv_inv] at h1
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hback, Equiv.symm_apply_apply] at hy
  exact (mul_eq_zero.mp hy).resolve_left (Units.ne_zero _)


omit hB in
structure PendRestS (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c)))
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

theorem brExists_of_restS (hL : LowerSymmetricCompatible Tf)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendRestS Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_tiedS Tf hL B gP
    { coM_mem := coM_mem_ofS Tf B hB, coM_inj := coM_inj_ofS Tf B hB, coP_mem := coP_mem_of_isUnit_det' Tf B hB,
      coP_inj := coP_inj_of_isUnit_det' Tf B hB, exP := h.exP, lat_co := h.lat_co, pt_co := h.pt_co, ipV_co := h.ipV_co,
      re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord }

end Cl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ClassMapInjective : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf),
    Function.Injective (D.fm u).til

def StabiliserMapBijective : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf),
    ∀ c, Function.Bijective ((D.fm u).stabMap c)

def FormsCarriedToComplement : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC

def NormBoundAtInfinity : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u →
    ∀ (h : (D.fm u).PRat) (v : NumberField.InfinitePlace D.what₂.LL) (x : Vl D u D.R.m),
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X v ((D.fm u).PtL h x) ((D.fm u).PtL h x)).re ≤
        ptB D u * (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X v x x).re

def ClassMapPropertiesOfSymmetricForms : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → ClassMapInjectiveBijectiveNorms D u

theorem symmetric_clauses_of_four (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (h3 : FormsCarriedToComplement) (h4 : NormBoundAtInfinity) : ClassMapPropertiesOfSymmetricForms :=
  fun D u Ch chOf Tf hL hB =>
    ⟨h1 D u Ch chOf Tf, h2 D u Ch chOf Tf, h3 D u Ch chOf Tf hL, h4 D u Ch chOf Tf hL hB⟩

theorem lowerMapTieSym_of (Tf : FormsTiedSym D u Ch chOf) (h : Formalism.L2.Rows.LowerMapTieS Tf) : LowerMapTieSym Tf := h

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField

def ChiTors : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf)
    (c : (D.fm u).clsP), ∃ k : ℕ, 0 < k ∧
      ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ)) ^ k = 1

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def tauLE (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

def AL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.what₂.LL :=
  (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) * bZ u Tf.til.z0).map (tauLE D τ)

def PL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP)
    (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL :=
  C (∏ τ, (AL Tf c τ).det ^ shiftOf (lamT u D.R.m) τ) * rowSubK (AL Tf c) F

theorem AL_map (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    (AL Tf c τ).map j = (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) *
      bZ u Tf.til.z0).map (embS D j τ) := by
  unfold AL
  rw [Matrix.map_map]
  rfl

theorem map_PL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ)
    (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    map j (PL Tf c F) = (∏ τ, ((AL Tf c τ).map j).det ^ shiftOf (lamT u D.R.m) τ) •
      blkRow (fun τ => (AL Tf c τ).map j) (map j F) := by
  unfold PL
  rw [map_mul, map_C, map_rowSubK, rowSubK_eq_subP, subP_eq_blkRow, MvPolynomial.smul_eq_C_mul, map_prod]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, RingHom.map_det]
  rfl

theorem isUnit_AL_map (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    IsUnit ((AL Tf c τ).map j).det := by
  rw [AL_map, Matrix.map_mul, Matrix.det_mul]
  refine IsUnit.mul ?_ ?_
  · exact isUnit_det_atInf (embS D j) (((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) τ
  · have := (bZ_isUnitS Tf).map (embS D j τ)
    rw [RingHom.map_det] at this
    exact this

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

def BlockFockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ))
    (F : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ) (c : ι → ℝ),
    (∀ τ, ∀ f ∈ V τ, (Formalism.REAL.fockF (F τ f) (F τ f)).re ≤ c τ ^ 2 * (Formalism.REAL.fockF f f).re) →
    ∀ P ∈ Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ V τ) ∧ p = Formalism.MainNotions.product_first_zeroth_parts.ten f},
      (Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P)).re ≤
        (∏ τ, c τ ^ 2) * (Formalism.REAL.fockF P P).re

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def eX {k : ℕ} (l : DomWeight k) : ℝ := (Formalism.REAL.fockF (extremal ℂ k l) (extremal ℂ k l)).re

theorem eX_pos {k : ℕ} (l : DomWeight k) : 0 < eX l := by
  have h := (Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.L2.Ker.lm_extremal_ne (K := ℂ) l)).1
  rw [Formalism.L2.Ker.nm_fockF_self (extremal ℂ k l), Complex.ofReal_re] at h
  exact h

theorem normFock_re {k : ℕ} (l : DomWeight k) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    (normFock l f f).re = (Formalism.REAL.fockF f f).re / eX l := by
  unfold normFock eX
  rw [Formalism.L2.Ker.nm_fockF_self (extremal ℂ k l), Complex.div_ofReal_re, Complex.ofReal_re]

def cF (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (D.fm u).beOn τ * Real.sqrt (eX ((D.fm u).sg τ) / eX ((D.fm u).lam D.R.m τ))

theorem cF_sq (τ : D.what₂.Tau) :
    cF D u τ ^ 2 = (D.fm u).beOn τ ^ 2 * (eX ((D.fm u).sg τ) / eX ((D.fm u).lam D.R.m τ)) := by
  unfold cF
  rw [mul_pow, Real.sq_sqrt (div_nonneg (eX_pos _).le (eX_pos _).le)]

theorem factor_le (Tf : FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u) (τ : D.what₂.Tau)
    (f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hf : f ∈ delSq ℂ _ ((D.fm u).lam D.R.m τ)) :
    (Formalism.REAL.fockF (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)
      (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)).re ≤ cF D u τ ^ 2 * (Formalism.REAL.fockF f f).re := by
  have hI := interlaceTr D u (sg_interlace Tf.valP) τ
  have hI' := (Formalism.L2.Ker.interlace_iff _ _ (Nm_succ D.R)).1 hI
  have hS := Formalism.L2.Ker.sameShiftTr D u τ hI
  have hf' : f ∈ nablaSq ℂ _ (lamTr D u τ) := by
    rw [Formalism.L2.Col.nablaSq_eq_delSq]; unfold lamTr; rw [delSq_wSh]; exact hf
  have h := Formalism.L2.Ker.nm_le _ _ _ hI' hS f hf'
  have hb : (D.fm u).beOn τ ^ 2 = ((Formalism.L2.Col.Br.cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ) ^ 2 *
      Formalism.L2.Col.Br.kapBr ℝ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) := by
    rw [beOn_closedS Tf hB τ]
    unfold Formalism.L2.Ker.beOnVal
    rw [mul_pow, sq_abs, Real.sq_sqrt (Formalism.L2.Ker.nm_kapR_pos _ _ _ hI' hS).le]
  have eS : eX (sgTr D u τ) = eX ((D.fm u).sg τ) := by unfold eX sgTr; rw [extremal_wSh]
  have eL : eX (lamTr D u τ) = eX ((D.fm u).lam D.R.m τ) := by unfold eX lamTr; rw [extremal_wSh]
  rw [normFock_re, normFock_re, eS, eL, ← hb] at h
  have hs := eX_pos ((D.fm u).sg τ)
  have hl := eX_pos ((D.fm u).lam D.R.m τ)
  rw [div_le_iff₀ hs] at h
  rw [cF_sq]
  calc _ ≤ (D.fm u).beOn τ ^ 2 * ((Formalism.REAL.fockF f f).re / eX ((D.fm u).lam D.R.m τ)) * eX ((D.fm u).sg τ) := h
    _ = _ := by field_simp

theorem nfAll_brTen_le (hT : BlockFockBound) (Tf : FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re ≤
      (∏ τ, (D.fm u).beOn τ ^ 2) * (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) P P).re := by
  have key := hT D.what₂.Tau (D.R.N D.R.m) (D.R.N D.R.m - 1) (fun τ => delSq ℂ _ ((D.fm u).lam D.R.m τ))
    (fun τ => Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) (cF D u)
    (fun τ f hf => factor_le Tf hB τ f hf) P hP
  have eprod : ∀ {k : ℕ} (l : D.what₂.Tau → DomWeight k),
      ∏ τ, Formalism.REAL.fockF (extremal ℂ k (l τ)) (extremal ℂ k (l τ)) = ((∏ τ, eX (l τ) : ℝ) : ℂ) := by
    intro k l
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.Ker.nm_fockF_self _
  unfold Formalism.L2.Forms.nfAll
  rw [eprod, eprod, Complex.div_ofReal_re, Complex.div_ofReal_re]
  have hs : 0 < ∏ τ, eX ((D.fm u).sg τ) := Finset.prod_pos fun τ _ => eX_pos _
  have hl : 0 < ∏ τ, eX ((D.fm u).lam D.R.m τ) := Finset.prod_pos fun τ _ => eX_pos _
  have hc : ∏ τ, cF D u τ ^ 2 =
      (∏ τ, (D.fm u).beOn τ ^ 2) * ((∏ τ, eX ((D.fm u).sg τ)) / ∏ τ, eX ((D.fm u).lam D.R.m τ)) := by
    rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => cF_sq τ
  rw [hc] at key
  rw [div_le_iff₀ hs]
  calc (Formalism.REAL.fockF (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re
      ≤ (∏ τ, (D.fm u).beOn τ ^ 2) * ((∏ τ, eX ((D.fm u).sg τ)) / ∏ τ, eX ((D.fm u).lam D.R.m τ)) *
          (Formalism.REAL.fockF P P).re := key
    _ = _ := by field_simp

end Formalism.L2.GlobalTheoryTheory.Br
end
end
