module

public import Formalism.LocalToGlobal.HermitianForms.TiedBrRep
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle006
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle008
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FormsOfLatticeExtension
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.HformSmulRightB
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle009
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle007
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LowerTieChain
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section GenE

theorem ext_mem_gen {A S : Type} [CommRing A] [Ring S] {n N : ℕ} [Module S (Fin N → A)] [Module S (Fin n → A)]
    (Λm Λd : Submodule S (Fin N → A)) (Λp : Submodule S (Fin n → A)) (hmd : Λm ≤ Λd)
    (I : Matrix (Fin N) (Fin n) A) (P : Matrix (Fin n) (Fin N) A) (k : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin N) (Fin N) A) (hPI : P * I = 1) (hG : G = I * k * P + (1 - I * P))
    (hk : ∀ x, x ∈ Λp ↔ k *ᵥ x ∈ Λp) (hI : ∀ x ∈ Λp, I *ᵥ x ∈ Λm) (hO : ∀ x ∈ Λd, P *ᵥ x ∈ Λp)
    (x : Fin N → A) : (x ∈ Λd ↔ G *ᵥ x ∈ Λd) ∧ (x ∈ Λd → G *ᵥ x - x ∈ Λm) := by
  have hGx : G *ᵥ x - x = I *ᵥ (k *ᵥ (P *ᵥ x)) - I *ᵥ (P *ᵥ x) := by
    simp only [hG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have hPIv : ∀ y, P *ᵥ (I *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hPI, Matrix.one_mulVec]
  have e : G *ᵥ x = x + (I *ᵥ (k *ᵥ (P *ᵥ x)) - I *ᵥ (P *ᵥ x)) := by rw [← hGx]; abel
  have hPG : P *ᵥ (G *ᵥ x) = k *ᵥ (P *ᵥ x) := by
    rw [e, Matrix.mulVec_add, Matrix.mulVec_sub, hPIv, hPIv]; abel
  have hdiff : P *ᵥ x ∈ Λp → G *ᵥ x - x ∈ Λm := fun h => by
    rw [hGx]; exact sub_mem (hI _ ((hk _).1 h)) (hI _ h)
  refine ⟨⟨fun hx => ?_, fun hx => ?_⟩, fun hx => hdiff (hO x hx)⟩
  · have e2 : G *ᵥ x = x + (G *ᵥ x - x) := by abel
    rw [e2]; exact add_mem hx (hmd (hdiff (hO x hx)))
  · have h1 : P *ᵥ x ∈ Λp := (hk _).2 (by rw [← hPG]; exact hO _ hx)
    have e2 : x = G *ᵥ x - (G *ᵥ x - x) := by abel
    rw [e2]; exact sub_mem hx (hmd (hdiff h1))

theorem stabFun_gen {A R M : Type} [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module R M] {N : ℕ}
    (Λ Λm : Submodule R (Fin N → A)) (f : Λ →ₗ[R] M) (g : GL (Fin N) A)
    (hst : ∀ x, x ∈ Λ ↔ (g : Matrix (Fin N) (Fin N) A) *ᵥ x ∈ Λ)
    (hd : ∀ x ∈ Λ, (g : Matrix (Fin N) (Fin N) A) *ᵥ x - x ∈ Λm) (hm : Λm ≤ Λ)
    (hf : ∀ y : Λ, y.1 ∈ Λm → f y = 0) : g ∈ stabFun Λ f := by
  refine ⟨hst, fun x => ?_⟩
  have e : (⟨(g : Matrix (Fin N) (Fin N) A) *ᵥ (x : Fin N → A), (hst x).1 x.2⟩ : Λ) = x + ⟨_, hm (hd x.1 x.2)⟩ :=
    Subtype.ext (by simp)
  rw [e, map_add (f := _), hf ⟨_, hm (hd x.1 x.2)⟩ (hd x.1 x.2), add_zero]

end GenE

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem proj_dual (Tf : FormsTiedSym D u Ch chOf) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0) :
    ∀ y ∈ Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
      (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb), P *ᵥ y ∈ Tf.clsP.lev.Lb := by
  have hiX : ∀ x, iXm D *ᵥ x = iXc D x := fun x => by simp only [iXm, LinearMap.toMatrix'_mulVec]
  obtain ⟨a0, ha0⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have ha : a0 ≠ 0 := by
    rintro rfl
    have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha0, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  have hPzc : P *ᵥ zc D = 0 := by
    rw [ha0, Matrix.mulVec_smul] at hPz
    exact (smul_eq_zero.mp hPz).resolve_left ha
  have hin := (lat_in_out Tf P hP1 hPz).1
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, s, rfl⟩ := span_iXc_zc D y
    have e : P *ᵥ (iXc D x + s • zc D) = x := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hPzc, smul_zero, add_zero, ← hiX, Matrix.mulVec_mulVec, hP1,
        Matrix.one_mulVec]
    rw [e]
    have hd : x ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) Tf.clsP.lev.Lb := by
      intro x' hx'
      have h := hy (iXc D x') (by rw [← hiX]; exact hin x' hx')
      rwa [hform_add_right, hform_smul_rightB, hform_iXc, hform_iXc_zc, mul_zero, add_zero] at h
    have := Tf.clsP.lev.Lb_dual x hd
    simpa using this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul D.host.E a x, Matrix.mulVec_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx




theorem extV_lat (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0)
    (Λd : Submodule (intV D.host.E v) (Fin (D.R.N D.R.m) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))
    (hmd : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb ≤ Λd)
    (hO : ∀ x ∈ Λd, (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ x ∈
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) Tf.clsP.lev.Lb)
    (x : Fin (D.R.N D.R.m) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    (x ∈ Λd ↔ G.1.map (prV (E := D.host.E) v) *ᵥ x ∈ Λd) ∧
      (x ∈ Λd → G.1.map (prV (E := D.host.E) v) *ᵥ x - x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) := by
  have hκv : bc (prV (E := D.host.E) v) κ.1 ∈ Tf.clsP.lev.Uloc v := ((Tf.clsP.lev.U_eq κ.1).1 κ.2).2 v
  have hκst := (Subgroup.mem_inf.mp (Tf.clsP.lev.Uloc_lev v hκv)).2
  have hin := (lat_in_out Tf P hP1 hPz).1
  have hI := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (iXm D) _ _ hin
  have hform := ext_form Tf (inclE (F := D.host.F) (v.adicCompletion D.host.F)) P hP1 hPz _ _ (isExt_prV v hE)
  rw [Matrix.map_mul] at hform
  have hPI : (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *
      ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) = 1 := by
    rw [← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ext_mem_gen _ Λd _ hmd _ _ (κ.1.1.map (prV (E := D.host.E) v)) _ hPI hform (fun y => hκst y) hI hO x




theorem extV_unit (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ UJ (sigR (sigD D) (v.adicCompletion D.host.F))
      ((gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) := by
  have hκv : bc (prV (E := D.host.E) v) κ.1 ∈ Tf.clsP.lev.Uloc v := ((Tf.clsP.lev.U_eq κ.1).1 κ.2).2 v
  have hκU0 := Tf.clsP.lev.Uloc_le v hκv
  have hκU : cT (sigR (sigD D) (v.adicCompletion D.host.F)) (κ.1.1.map (prV (E := D.host.E) v)) *
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * κ.1.1.map (prV (E := D.host.E) v) =
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) := hκU0
  show cT (sigR (sigD D) (v.adicCompletion D.host.F)) (G.1.map (prV (E := D.host.E) v)) *
      (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * G.1.map (prV (E := D.host.E) v) =
      (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))
  exact extUR Tf _ hκU _ (isExt_prV v hE)




theorem extV_stabL (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ stabGL (latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
      (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) := by
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  have hout := (lat_in_out Tf P hP1 hPz).2
  have hO := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) P _ _ hout
  intro x
  exact (extV_lat Tf κ G hE v P hP1 hPz _ le_rfl hO x).1




theorem extV_level (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ levelVL (sigD D) (gramN D D.R.m le_rfl) v (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb :=
  Subgroup.mem_inf.mpr ⟨extV_unit Tf κ G hE v, extV_stabL Tf κ G hE v⟩




theorem extV_fT (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hT : ((D.mem u).A.T : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) G ∈ stabFun _ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.fT v hT) := by
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  have hOd := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) P _ _ (proj_dual Tf P hP1 hPz)
  have hmd : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb ≤
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
          (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb)) :=
    Submodule.span_mono (Set.image_mono fun y hy =>
      Submodule.subset_span ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb_int y hy))
  exact stabFun_gen _ _ _ (bc (prV (E := D.host.E) v) G)
    (fun x => (extV_lat Tf κ G hE v P hP1 hPz _ hmd hOd x).1)
    (fun x hx => (extV_lat Tf κ G hE v P hP1 hPz _ hmd hOd x).2 hx) hmd
    (fun y hy => (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.fT_L v hT y hy)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brTen_blk_gFull (Tf : FormsTiedSym D u Ch chOf) (g : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brTen D u (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) Q) =
      (∏ τ, (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ)) •
        blk (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) (Formalism.L2.Ker.brTen D u Q) := by
  have e1 : (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) =
      fun τ => ⇑(Formalism.L2.Ker.ta_sqActL (lamTr D u τ) (gFull D u (g τ))) :=
    funext fun τ => (Formalism.L2.Ker.ta_sqActL_coe _ _).symm
  have e2 : (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) = fun τ => ⇑(Formalism.L2.Ker.ta_sqActL (sgTr D u τ) (g τ)) :=
    funext fun τ => (Formalism.L2.Ker.ta_sqActL_coe _ _).symm
  unfold Formalism.L2.Ker.brTen
  rw [e1, e2, Formalism.L2.Ker.ta_blk_comp, Formalism.L2.Ker.ta_blk_comp]
  have e3 : (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ∘ₗ
      Formalism.L2.Ker.ta_sqActL (lamTr D u τ) (gFull D u (g τ)))) =
      fun τ => ⇑((((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ) • (Formalism.L2.Ker.ta_sqActL (sgTr D u τ) (g τ) ∘ₗ
        Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))) := by
    funext τ f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Formalism.L2.Ker.ta_sqActL_coe]
    exact brOne_gFull Tf τ (g τ) f
  rw [e3, Formalism.L2.Ker.blk_smul]
  rfl

theorem blkRow_mem_CSpan {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} (m : ι → DomWeight k)
    (M : ι → Matrix (Fin k) (Fin k) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (p : MvPolynomial (ι × Fin k × Fin k) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m) : blkRow M p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m := by
  have hT : ∀ τ, IsUnit ((M τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact hM τ
  let g : ι → GL (Fin k) ℂ := fun τ => ⟨(M τ)ᵀ, ((M τ)ᵀ)⁻¹, Matrix.mul_nonsing_inv _ (hT τ), Matrix.nonsing_inv_mul _ (hT τ)⟩
  have h := Formalism.L2.Ker.lc_blk_sqAct_mem m g p hp
  rw [blk_sqAct_eq] at h
  have hgT : (fun τ => ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)ᵀ) = M := funext fun τ => Matrix.transpose_transpose _
  rw [hgT] at h
  have hc : (∏ τ, detPow ℂ k (g τ) (m τ).detShift) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _
  have h2 := Submodule.smul_mem _ (∏ τ, detPow ℂ k (g τ) (m τ).detShift)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

theorem map_mem_CSpan_of_rat {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) (hF : map D.what₂.embLL F ∈ RatSpan D lam)
    (s : D.what₂.LL →+* ℂ) : map s F ∈ Formalism.L2.Forms.CSpan lam := by
  have hinj : Function.Injective (map (σ := D.what₂.Tau × Fin n × Fin n) D.what₂.embLL) :=
    MvPolynomial.map_injective _ D.what₂.embLL.injective
  have hten : ∀ (j : D.what₂.LL →+* ℂ) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
      map j (Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom D.what₂.LL) (f τ))) =
        Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom ℂ) (f τ)) := by
    intro j f
    have hi : j.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    unfold Formalism.L2.Forms.ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map, hi]
  have key : ∀ p ∈ RatSpan D lam, ∀ F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      map D.what₂.embLL F = p → map s F ∈ Formalism.L2.Forms.CSpan lam := by
    intro p hp
    induction hp using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨r, f, hf, rfl⟩ := hx
      intro F hF
      have hFe : F = r • Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom D.what₂.LL) (f τ)) := by
        apply hinj
        rw [hF, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hten]
      rw [hFe, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hten, ← MvPolynomial.smul_eq_C_mul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ), fun τ => ?_, rfl⟩)
      exact Formalism.L2.G.Model.sw_weyl_map (Int.castRingHom ℂ) le_rfl _ (f τ) (hf τ)
    | zero =>
      intro F hF
      have : F = 0 := hinj (by rw [hF, map_zero])
      rw [this, map_zero]; exact Submodule.zero_mem _
    | add x y hx' hy' hx hy =>
      intro F hF
      obtain ⟨Fx, hFx⟩ := exists_map_of_ratSpan D hx'
      obtain ⟨Fy, hFy⟩ := exists_map_of_ratSpan D hy'
      have : F = Fx + Fy := hinj (by rw [map_add (f := _), hFx, hFy, hF])
      rw [this, map_add (f := _)]
      exact Submodule.add_mem _ (hx Fx hFx) (hy Fy hFy)
    | neg x hx' hx =>
      intro F hF
      obtain ⟨Fx, hFx⟩ := exists_map_of_ratSpan D hx'
      have : F = -Fx := hinj (by rw [map_neg, hFx, hF])
      rw [this, map_neg]
      exact Submodule.neg_mem _ (hx Fx hFx)
  exact key _ hF F rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end
