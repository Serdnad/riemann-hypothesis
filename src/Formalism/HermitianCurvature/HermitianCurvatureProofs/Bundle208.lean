module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle194
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle123
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle141
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section mul

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def nfMulOp (c : B.Mat k r → ℂ) : B.DiffOp k r Wp Wq :=
  [{ coef := fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
     coefAdj := fun g => star (c g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
     word := []
     word_lie := by simp
     adj_id := by
       intro x A B'
       unfold B.hsInner
       simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.id_apply]
       rw [TBBx2.Tri.hsVec_smul, TBBx2.Tri.hsVec_smul, inner_smul_right, inner_smul_left]
       simp }]

theorem nfMulOp_apply (c : B.Mat k r → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (nfMulOp (Wp := Wp) (Wq := Wq) c) F g = c g • F g := by
  unfold B.opApply nfMulOp B.Rw
  simp

theorem nfMulOp_poly {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) :
    CutMP.PolyOp 0 κ (nfMulOp (Wp := Wp) (Wq := Wq) c) := by
  unfold CutMP.PolyOp
  intro Tm hTm
  simp only [nfMulOp, List.mem_singleton] at hTm
  subst hTm
  exact ⟨le_refl _, c, hc, fun g => rfl, fun g => rfl⟩

end mul

theorem nf_isPolyDeg_one {N : ℕ} : U.IsPolyDeg (N := N) 0 (fun _ => (1 : ℂ)) := by
  unfold U.IsPolyDeg
  exact ⟨1, by simp, fun g => by simp⟩

theorem nf_isPolyDeg_pow {N κ : ℕ} {c : Matrix (Fin N) (Fin N) ℂ → ℂ} (hc : U.IsPolyDeg κ c) (e : ℕ) :
    U.IsPolyDeg (κ * e) (fun g => c g ^ e) := by
  unfold U.IsPolyDeg at hc ⊢
  obtain ⟨q, hq, hcq⟩ := hc
  refine ⟨q ^ e, ?_, fun g => ?_⟩
  · calc (q ^ e).totalDegree ≤ e * q.totalDegree := MvPolynomial.totalDegree_pow q e
      _ ≤ e * κ := Nat.mul_le_mul_left e hq
      _ = κ * e := Nat.mul_comm e κ
  · simp only [hcq g, map_pow]

theorem empty_operator_list_holds : NFEmptyOps := by
  refine ⟨2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p N
  have hn : (1 : ℝ) ≤ CutMP.nDim P.k P.r := by unfold CutMP.nDim; push_cast; linarith
  have ok : ∀ (κ : ℕ) (c : B.Mat P.k P.r → ℂ), U.IsPolyDeg κ c → (κ : ℝ) ≤ 2 * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) →
      (∀ pp : B.SS P.k P.r, p.T.base.inSS pp → ∀ g, c (B.sgs pp g) = c g) → NFOpOK 2 p N (nfMulOp c) := by
    intro κ c hc hκ hinv
    obtain ⟨hs, hg, ho⟩ := CutMP.polynomial_decay_admissible P.k P.r Wp Wq 0 κ (nfMulOp c) (nfMulOp_poly hc)
    refine ⟨hs _, ?_, hg _ hκ, ?_⟩
    · intro pp hpp f _ g _
      have hfun : B.opApply (nfMulOp (Wp := Wp) (Wq := Wq) c) f = fun g => c g • f g := funext (nfMulOp_apply c f)
      rw [nfMulOp_apply, hfun]
      unfold B.rho
      show _ = (p.T.base.π (Matrix.of pp.1.1)).comp ((c (B.sgs pp g) • f (B.sgs pp g)).comp (p.T.base.π' (Matrix.of pp.2.1)⁻¹))
      rw [hinv pp hpp g, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    · have : (B.opOrder (nfMulOp (Wp := Wp) (Wq := Wq) c) : ℝ) ≤ 0 := by exact_mod_cast ho
      have : (0 : ℝ) ≤ 2 * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
      linarith
  refine ⟨nfMulOp (fun _ => (1 : ℂ)), nfMulOp (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ)),
    ok 0 _ nf_isPolyDeg_one (by push_cast; positivity) (fun _ _ _ => rfl), ok ((2 * P.r + 2) * N) _ ?_ ?_ ?_, fun F g => ?_⟩
  · have h := nf_isPolyDeg_pow (Formalism.FourierDecayAlt.P.gram_function_polynomial P.k P.r p.T.base.z p.T.base.z') N
    refine ⟨h.choose, h.choose_spec.1, fun g => ?_⟩
    rw [← h.choose_spec.2 g]; push_cast; rfl
  · push_cast
    have h1 : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul h1 hn (by norm_num) (by positivity)]
  · intro pp hpp g
    rw [TBBx2.Gf_sgs p.T.base pp hpp g]
  · rw [nfMulOp_apply, nfMulOp_apply, one_smul]
    exact ⟨rfl, rfl⟩

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RightTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_right (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg (Qx8.uw_one z) (Qx8.nlev_one _) hh (Qx8.nlev_one _)
  simpa using this

theorem J_right (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) h hh
  rw [Matrix.one_mul, Matrix.mul_one, hπ'.1] at e1
  rw [Matrix.one_mul] at e2
  have e3 : (J g).comp (1 : Wq →L[ℂ] Wq) = J g := ContinuousLinearMap.comp_id _
  rw [e3] at e1
  rw [e2, ← ContinuousLinearMap.comp_assoc, ← e1]

theorem rd_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : QrD.InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : RdV X F g = (J g).comp ((QrD.dOp π' X).comp B) := by
  have h := QrD.dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (J g)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π' (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_right hD hg (QrD.exp_uw hX t)), J_right hπ' hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold RdV
  rw [h3]
  exact h2.deriv

theorem rz_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : QrD.InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((QrD.ecOp π' Z).comp B) := by
  unfold RZ QrD.ecOp
  rw [rd_right hD hπ' hc hJ hF h1 hg, rd_right hD hπ' hc hJ hF h2 hg]
  ext v
  simp

theorem fold_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z' (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z' (hpart2 (Hpk k r) p.2)) :
    ∃ B : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r i ∩ D,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
          (J g).comp B) ∧
      ∀ v, B v = (L.map fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v := by
  induction L with
  | nil => exact ⟨1, fun g _ => (ContinuousLinearMap.comp_id _).symm, fun v => rfl⟩
  | cons p L ih =>
    obtain ⟨B, hB1, hB2⟩ := ih fun q hq => hL q (by simp [hq])
    have hp := hL p (by simp)
    refine ⟨p.1 • B + (QrD.ecOp π' p.2).comp B, fun g hg => ?_, fun v => ?_⟩
    · simp only [List.map_cons, List.foldr_cons, Pi.add_apply, Pi.smul_apply]
      rw [rz_right hD hπ' hc hJ hB1 hp.1 hp.2 hg, hB1 g hg]
      ext v
      simp
    · simp only [List.map_cons, List.foldr_cons]
      rw [← hB2 v, QrD.ecRep_eq hπ' hc hp.1 hp.2]
      rfl

end RightTypeActionHermitianCurvature

theorem right_type_action_holds : RightTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ' hc J hJ g hg Bs hB w v
  unfold capR capRep qmF

  simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply,
  map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  obtain ⟨B, hB1, hB2⟩ := RightTypeActionHermitianCurvature.fold_right hD hπ' hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j)
  have e1 := hB1 g hg
  have e2 := hB2 v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1 e2
  simp only [id]
  rw [e1, ← e2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

section

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section ShiftJ

variable {r : ℕ}

def shIdxJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) :
    {m : Fin (r - i) // jl.val ≤ m.val} ≃ {p : Fin r // j.val ≤ p.val} where
  toFun m := ⟨⟨m.1.val + i.val, by have := m.1.isLt; have := i.isLt; omega⟩, by
    have := m.2; show j.val ≤ m.1.val + i.val; omega⟩
  invFun p := ⟨⟨p.1.val - i.val, by have := p.1.isLt; have := p.2; omega⟩, by
    have := p.2; show jl.val ≤ p.1.val - i.val; omega⟩
  left_inv m := by
    apply Subtype.ext; apply Fin.ext
    show m.1.val + i.val - i.val = m.1.val
    omega
  right_inv p := by
    apply Subtype.ext; apply Fin.ext
    show p.1.val - i.val + i.val = p.1.val
    have := p.2; omega

def shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) : Cf (r - i) (jl) ≃ᵐ Cf r j :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdxJ i j jl hjl)

theorem shEqJ_mp (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) : MeasurePreserving (shEqJ i j jl hjl) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdxJ i j jl hjl)

theorem shEqJ_apply (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c' : Cf (r - i) (jl))
    (p : {p : Fin r // j.val ≤ p.val}) : shEqJ i j jl hjl c' p = c' ((shIdxJ i j jl hjl).symm p) := by
  unfold shEqJ
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

def shiftV (i : Fin (r + 1)) (c' : Fin r → ℂ) : Fin (r - i) → ℂ :=
  fun m => c' ⟨m.val + i.val, by have := m.isLt; have := i.isLt; omega⟩

theorem glue_shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) (c'' : Cf (r - i) (jl)) :
    glue j c' (shEqJ i j jl hjl c'') =
      glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue (jl) (shiftV i c') c'')) := by
  funext p
  by_cases h1 : j.val ≤ p.val
  · have h2 : i.val ≤ p.val := by omega
    have h3 : (jl).val ≤ p.val - i.val := by omega
    simp only [glue, dif_pos h1, dif_pos h2, Formalism.FourierDecayAlt.P.PTie.shiftCf, dif_pos h3, shEqJ_apply]
    rfl
  · by_cases h2 : i.val ≤ p.val
    · have h3 : ¬ (jl).val ≤ p.val - i.val := by omega
      simp only [glue, dif_neg h1, dif_pos h2, Formalism.FourierDecayAlt.P.PTie.shiftCf, dif_neg h3, shiftV]
      congr 1
      apply Fin.ext
      show p.val = p.val - i.val + i.val
      omega
    · simp only [glue, dif_neg h1, dif_neg h2]
      exact hc p (by omega)

theorem wtI_shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c'' : Cf (r - i) (jl)) :
    wtI j (shEqJ i j jl hjl c'') = wtI (jl) c'' := by
  unfold wtI
  congr 1
  simp_rw [shEqJ_apply]
  exact Fintype.prod_equiv (shIdxJ i j jl hjl).symm _ _ fun l => rfl

end ShiftJ

section Tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem integrand_tr (μ : Measure (Mt k r)) (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ}
    {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - i)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (u v : Ix S → RadSp k r z z' π π') (c'' : Cf (r - i) (jl)) :
    wtI j (shEqJ i j jl hjl c'') * ∑ a, pairAt μ (u a) (v a) (glue j c' (shEqJ i j jl hjl c'')) =
      (κ : ℂ)⁻¹ * (wtI (jl) c'' *
        ∑ a, pairAt μi (T (u a)) (T (v a)) (glue (jl) (shiftV i c') c'')) := by
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  rw [wtI_shEqJ, glue_shEqJ i j jl hjl c c' hc]
  simp_rw [hT]
  rw [← Finset.mul_sum]
  field_simp

theorem form_tr (μ : Measure (Mt k r)) (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ}
    {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - i)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (u v : Ix S → RadSp k r z z' π π') :
    form μ j u v c' = (κ : ℂ)⁻¹ * form μi (jl) (fun a => T (u a)) (fun a => T (v a)) (shiftV i c') := by
  unfold form
  rw [← (shEqJ_mp i j jl hjl).integral_comp', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c'' => ?_)
  exact integrand_tr μ i j jl hjl c c' hc μi T κ hκ hT u v c''

end Tr

theorem arel_star {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {S : Type}
    [Fintype S] [DecidableEq S] {T : V →ₗ[ℂ] V'} {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')}
    (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M') : Formalism.FourierDecayAlt.P.PBH.ARel T (star M) (star M') := fun a b => by
  rw [Matrix.star_apply, Matrix.star_apply]
  exact Formalism.FourierDecayAlt.P.PBH.rel_star (h b a)

end Formalism.FourierDecayAlt.P5.HerD
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Shift

def shIdx {r : ℕ} (i : Fin (r + 1)) : {l : Fin (r - i) // (0 : Fin (r - i + 1)).val ≤ l.val} ≃ {l : Fin r // i.val ≤ l.val} where
  toFun l := ⟨⟨l.1.val + i.val, by have := l.1.isLt; have := i.isLt; omega⟩, Nat.le_add_left _ _⟩
  invFun l := ⟨⟨l.1.val - i.val, by have := l.1.isLt; have := l.2; omega⟩, Nat.zero_le _⟩
  left_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val + i.val - i.val = l.1.val
    omega
  right_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val - i.val + i.val = l.1.val
    have := l.2; omega

def shEq {r : ℕ} (i : Fin (r + 1)) : Cf (r - i) 0 ≃ᵐ Cf r i :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_mp {r : ℕ} (i : Fin (r + 1)) : MeasurePreserving (shEq i) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_apply {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) (l : {l : Fin r // i.val ≤ l.val}) :
    shEq i c' l = c' ((shIdx i).symm l) := by
  unfold shEq
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem shiftCf_glue {r : ℕ} (i : Fin (r + 1)) (c'' : Fin (r - i) → ℂ) (c' : Cf (r - i) 0) :
    Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue 0 c'' c') = shEq i c' := by
  funext l
  rw [shEq_apply]
  simp [Formalism.FourierDecayAlt.P.PTie.shiftCf, shIdx]
  rfl

theorem wtI_shEq {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) : wtI i (shEq i c') = wtI 0 c' := by
  unfold wtI
  congr 1
  simp_rw [shEq_apply]
  exact Fintype.prod_equiv (shIdx i).symm _ _ fun l => rfl

end Shift

section Transfer

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem level_square_integrable_of_transport {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (i : Fin (r + 1)) (c : Fin r → ℂ)
    {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ} {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)}
    (μi : Measure (Mt k (r - i))) (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (v : RadSp k r z z' π π') (c'' : Fin (r - i) → ℂ) (h : LevelSquareIntegrable μi 0 (T v) c'') : LevelSquareIntegrable μ i v c := by
  unfold LevelSquareIntegrable at h ⊢
  have e : (fun c' : Cf r i => wtI i c' * pairAt μ v v (glue i c c')) ∘ (shEq i) =
      fun c' => (κ : ℂ)⁻¹ * (wtI 0 c' * pairAt μi (T v) (T v) (glue 0 c'' c')) := by
    funext c'
    simp only [Function.comp_apply]
    rw [hT, shiftCf_glue, wtI_shEq]
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    field_simp
  have h2 := h.const_mul ((κ : ℂ)⁻¹)
  rw [← e] at h2
  exact ((shEq_mp i).integrable_comp_emb (shEq i).measurableEmbedding).mp h2

end Transfer

section Lev

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem act_tr {k r k' r' : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {zi zi' : Fin (2 * r' + k' + 1) → ℂ} {πi : Mx k' r' → (Wp →L[ℂ] Wp)}
    {πi' : Mx k' r' → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k' r' zi zi' πi πi') {M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))}
    {M' : SlopeTestRemainingChoices S (Pr (RadSp k' r' zi zi' πi πi'))} (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M')
    (x : Ix S → RadSp k r z z' π π') (a : Ix S) : T (act M x a) = act M' (fun b => T (x b)) a := by
  unfold act

  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := congrArg (fun f => f (x b)) (h a b).1
  simpa using this.symm

end Lev

end Formalism.FourierDecayAlt.P5.HerD
end
end

section

namespace Formalism.FourierDecayAlt.P

theorem pb_degTop_of (hRA : PBN.RadAATop) (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop :=
  degree_top_of_parts word_recursion hRA hPT density_constant

end Formalism.FourierDecayAlt.P
end
