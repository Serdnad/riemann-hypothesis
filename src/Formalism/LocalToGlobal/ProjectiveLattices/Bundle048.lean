module

import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableIndicatorOfContOn
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle046
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle045
public import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

section FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dmin_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
  have hconj : ∀ z : E, τ.1 (cc z) = starRingEnd ℂ (τ.1 z) := fun z =>
    NumberField.IsCMField.complexEmbedding_complexConj E τ.1 z
  have hcc : ∀ (b q : Fin r), cc ((Pi.single b (1 : E) : Fin r → E) q) =
      (Pi.single b (1 : E) : Fin r → E) q := by
    intro b q
    by_cases h : q = b
    · subst h
      simp [cc]
    · simp [cc, Pi.single_eq_of_ne h]
  have hU : ∀ a b : Fin r, ∑ p, ∑ q, (γ : Matrix (Fin r) (Fin r) E) p a * X.Gm p q *
      cc ((γ : Matrix (Fin r) (Fin r) E) q b) = X.Gm a b := by
    intro a b
    have h := (X.Γ_stab γ hγ).1 (Pi.single a 1) (Pi.single b 1)
    simp only [herm, hcc] at h
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hUm : Matrix.transpose (γ : Matrix (Fin r) (Fin r) E) * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
    ext a b
    rw [← hU a b]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hg : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      gram τ.1 X.Gm M = Matrix.transpose M * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    intro M
    ext a b
    simp only [gram, Matrix.of_apply, hermC, col, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hmat : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    ext a b
    simp only [Matrix.map_apply, hconj]
  have e : X.Gm.map τ.1 = (Matrix.transpose (γ : Matrix (Fin r) (Fin r) E)).map τ.1 * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    conv_lhs => rw [← hUm]
    rw [Matrix.map_mul, Matrix.map_mul]
  have key : gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    rw [hg, hg, hmat, Matrix.transpose_mul, Matrix.map_mul, hc, ← Matrix.transpose_map]
    conv_rhs => rw [e]
    simp only [Matrix.mul_assoc]
  unfold dmin
  rw [key]

theorem dmin_ne_of_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h0
  have h1 : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
    first
      | exact (hx τ).2 i
      | (simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
         exact (hx τ).2 i)
  rw [h0] at h1
  simp at h1

theorem continuousOn_pnorm (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : ContinuousOn P X.dom) :
    ContinuousOn (X.pnorm la P) X.dom := by
  apply GlobalTheory.KronOff.pnorm_contOn <;> assumption

end FD

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end Gen

section Core

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps CompSplitPfB

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)


variable {j} in
def CompOf (cm : ∀ σ : Tc.Q.c.F →+* ℂ, (Tc.U j σ).Comp → Comp (Tc.Q.Xo j) Tc.Q.c) : Prop :=
  ∀ (σ : Tc.Q.c.F →+* ℂ) (k : (Tc.U j σ).Comp) (x : ((Tc.U j σ).X k).dom) (q : PrimeSpectrum (CAt σ)),
    cspB_lift ((Tc.U j σ).un k x).x ((Tc.U j σ).un k x).x_over q ∈
      ((cm σ k : Comp (Tc.Q.Xo j) Tc.Q.c) : Set ((Tc.Q.Xo j).XF Tc.Q.c))

def ptAt (hj : InR D j) (hA : AllTest (Tc.Q.Xo j) Tc.Q.c) (hB : ∀ σ, GoodEmb Tc.Q.c σ → BCEx (Tc.Q.Xo j) Tc.Q.c σ)
    (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c) (hb : CBaseEx (Tc.Q.Xo j) Tc.Q.c h) (Z : Comp (Tc.Q.Xo j) Tc.Q.c)
    (P : Om Z →+* ℂ) (sg : Tc.Q.c.F →+* ℂ) (hP : sgOf P = sg) : SupPtAt j (goodOf Tc.Q.c sg) :=
  hP ▸ nrmTieDefPt hL j hj hA hB h hb Z P

end Core

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)



abbrev phiI (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (Z : Comp (T.Q.Xo j) T.Q.c) :=
  phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w

def CurveHyp (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  SpanW (recPlus h j hj) G.w S ∧ BigAt h j hj hG G ∧ ThAt h j hj hG G g0 ∧ (recPlus h j hj).NonZeroComp wF g0


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem curveInst_of [Fintype (Comp (T.Q.Xo j) T.Q.c)]
    (hinj : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ f : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Z, phiI h j hj hG hT la G Z f = 0) → f = 0)
    (hone : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
        ∀ Z Z', RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z') ≤ Q → Z = Z')
    (hloc : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a)
    (hS1 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)))
    (hH2 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ (e : ℕ) (w' : WeightFamilies.Wt D j) (θ : (recB h.toLawsCore).Cusp j w') (hw : wadd wF w' = wsmul e wL),
        (∀ Z, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0) →
        IsUnit (toOsK (recPlus h j hj) la G.w (u0 (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0 θ hw)))
    (hH3 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ b : ↥(Frac0 (recPlus h j hj) la G.w),
        (b : Lw (recPlus h j hj) la G.w) *
          algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
            (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0)) = 0 → b = 0) :
    CurveInstSt h j hj := by
  intro _ ka wL wF G la S g0 hSp hBig hTh hNZ
  have hH : CurveHyp h j hj hG ka wL wF G S g0 := ⟨hSp, hBig, hTh, hNZ⟩
  have h1 := LocalUnitReduction.finRed (Kp (recPlus h j hj) la G.N) ↥(Frac0 (recPlus h j hj) la G.w) (Jid (recPlus h j hj) la G.w)
    (Comp (T.Q.Xo j) T.Q.c) (fun Z => RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
    (fun Z => phiI h j hj hG hT la G Z) (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
    (hloc _ _ _ G S g0 la hH) (hS1 _ _ _ G S g0 la hH)
  obtain ⟨e, w', θ, hw, hθ⟩ := hTh
  exact curveModel_of_fr (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0 h1.1 h1.2 θ hw
    (hH2 _ _ _ G S g0 la hH e w' θ hw hθ) (hH3 _ _ _ G S g0 la hH)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def wRat (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : Fin G.N) :
    ↥(Frac0 (xplus X E hM) la G.w) :=
  ⟨frac (xplus X E hM) la G.w 1 (emb (xplus X E hM) la G.N (X.inc wL (G.w k))),
    Algebra.subset_adjoin (frac_mem_Hfr (xplus X E hM) la G.w (by
      rw [add_zero_weight_one_eq]; exact emb_mem_Vw (xplus X E hM) la G.N wL (G.w k)))⟩

def GenericSectionMinimumIntegral (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) →
    IsReduced (OsK (xplus X E hM) la G.w) → ∀ ζ : PtsG G la, (∀ k, 0 ≤ ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k))) ∧
    ∃ k, ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k)) = 0

lemma nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ 0 ≤ nval T.V 1 z := by
  by_cases hz : z = 0
  · simp [hz, nval_zero]
  · rw [nval_of_ne hz, nval_of_ne hz, EReal.coe_nonneg, EReal.coe_nonneg]
    have : (0 : ℝ) < e := by exact_mod_cast he
    constructor
    · intro h; simpa using (div_nonneg_iff.1 h).elim (fun h' => h'.1) (fun h' => absurd h'.2 (not_le.2 this))
    · intro h; exact div_nonneg (by simpa using h) this.le

lemma nval_eq_zero_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : nval T.V e z = 0 ↔ nval T.V 1 z = 0 := by
  by_cases hz : z = 0
  · simp [hz, nval_zero]
  · rw [nval_of_ne hz, nval_of_ne hz]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    simp [div_eq_zero_iff, this]

theorem depthAtSec_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (S : Scal B)
    (hspan : SpanW (xplus X E hM) G.w S) (h0 : GenericSectionMinimumIntegral G la)
    (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w)) (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ))
    (ζ : PtsG G la) :
    (xplus X E hM).depth S.sW wL la (.inr (y ζ)) =
      nval (hs ζ).T.V (ep (unifO (xplus X E hM) la G.N) ζ) ((hs ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) := by
  set h := hs ζ with hh
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have he := h.ep_pos

  have hwk : ∀ k, E.vAt' la (y ζ) (X.inc wL (G.w k)) =
      nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) +
        nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k : Lw (xplus X E hM) la G.w)) := by
    intro k
    rw [h.hv, ← nval_mul]
    congr 1
    show _ = _ * h.lift (frac (xplus X E hM) la G.w 1 _)
    rw [h.lift_frac, pow_one, mul_comm, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hord : ∀ k, nval h.T.V 1 (h.lift (wRat G la k : Lw (xplus X E hM) la G.w)) =
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k))) :=
    fun k => (h.ord (wRat G la k)).symm
  obtain ⟨hint, k0, hk0⟩ := h0 hfd hred ζ
  have hnn : ∀ k, 0 ≤ nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k : Lw _ la G.w)) := by
    intro k
    rw [nval_nonneg_iff he, hord]
    have := hint k
    generalize ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k)) = o at this ⊢
    cases o with
    | top => simp [toE]
    | coe n => simp only [toE]; exact_mod_cast (WithTop.coe_nonneg.1 this)
  have hz0 : nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k0 : Lw _ la G.w)) = 0 := by
    rw [nval_eq_zero_iff he, hord, hk0]
    show toE ((0 : ℤ) : WithTop ℤ) = 0
    simp [toE]
  apply le_antisymm
  · refine (iInf₂_le (G.w k0) (by rw [← hspan]; exact Submodule.subset_span ⟨k0, rfl⟩)).trans_eq ?_
    show E.vAt' la (y ζ) (X.inc wL (G.w k0)) = _
    rw [hwk, hz0, add_zero]
  · refine le_iInf₂ fun F hF => ?_
    rw [← hspan] at hF
    show _ ≤ E.vAt' la (y ζ) (X.inc wL F)
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hwk]
      exact le_add_of_nonneg_right (hnn k)
    | zero => rw [map_zero, E.vAt'_zero]; exact le_top
    | add x z _ _ hx hz =>
      rw [map_add (f := _)]
      exact (le_min hx hz).trans (E.vAt'_add la _ _ _)
    | smul a x _ hx =>
      by_cases ha : ((a : 𝓞 B.KO) : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        rw [this, zero_smul, map_zero, E.vAt'_zero]; exact le_top
      · rw [← algebraMap_smul B.KO a x, map_smul, E.vAt'_smul la _ _ _ ha]
        exact le_add_of_nonneg_of_le (by exact_mod_cast vAdd_int_nonneg la ha) hx

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {N : ℕ}


variable (K) in
def HomQ (x : Fin N → L) (f : L) : Prop :=
  ∃ (e : ℕ) (A B : MvPolynomial (Fin N) K), A.IsHomogeneous e ∧ B.IsHomogeneous e ∧
    MvPolynomial.aeval x B ≠ 0 ∧ f = MvPolynomial.aeval x A / MvPolynomial.aeval x B

theorem homQ_mul {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f * g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * A', B * B', hA.mul hA', hB.mul hB', by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem homQ_add {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f + g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * B' + B * A', B * B', (hA.mul hB').add (hB.mul hA'), hB.mul hB',
    by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_add (f := _), map_mul, map_mul, map_mul, div_add_div _ _ hBx hBx']⟩

theorem homQ_inv {x : Fin N → L} {f : L} (hf : HomQ K x f) : HomQ K x f⁻¹ := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  by_cases hAx : MvPolynomial.aeval x A = 0
  · rw [hAx, zero_div, inv_zero]
    exact ⟨0, 0, 1, MvPolynomial.isHomogeneous_zero _ _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩
  · exact ⟨e, B, A, hB, hA, hAx, by rw [inv_div]⟩

theorem homQ_algebraMap (x : Fin N → L) (c : K) : HomQ K x (algebraMap K L c) :=
  ⟨0, MvPolynomial.C c, 1, MvPolynomial.isHomogeneous_C _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩

theorem homQ_ratio (x : Fin N → L) (m k₀ : Fin N) (hx : x k₀ ≠ 0) : HomQ K x (x m / x k₀) :=
  ⟨1, MvPolynomial.X m, MvPolynomial.X k₀, MvPolynomial.isHomogeneous_X _ _, MvPolynomial.isHomogeneous_X _ _,
    by simpa using hx, by simp⟩


variable (K) in
def homQField (x : Fin N → L) : IntermediateField K L where
  carrier := {f | HomQ K x f}
  mul_mem' := fun ha hb => homQ_mul ha hb
  add_mem' := fun ha hb => homQ_add ha hb
  algebraMap_mem' := homQ_algebraMap x
  inv_mem' := fun _ hf => homQ_inv hf

theorem homQ_of_mem_adjoin (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0) {f : L}
    (hf : f ∈ IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) : HomQ K x f := by
  have hle : IntermediateField.adjoin K (Set.range fun m => x m / x k₀) ≤ homQField K x := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨m, rfl⟩
    exact homQ_ratio x m k₀ hx
  exact hle hf

theorem isAlgebraic_of_trdeg_eq (F : IntermediateField K L) (d : ℕ) (hF : Algebra.trdeg K F = d)
    (hL : Algebra.trdeg K L = d) : Algebra.IsAlgebraic F L := by
  have hs := trdeg_add_eq K F (A := L)
  rw [hF, hL] at hs
  have h0 : Algebra.trdeg F L = 0 := by
    rcases Cardinal.add_eq_left_iff.1 hs with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.2 ((Cardinal.natCast_lt_aleph0 (n := d))))
    · exact h
  exact trdeg_eq_zero_iff.1 h0

theorem exists_homInt (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) L) (a : L) :
    ∃ (k n : ℕ) (P : MvPolynomial (Fin N) K) (cf : ℕ → MvPolynomial (Fin N) K), 0 < k ∧ P.IsHomogeneous k ∧
      MvPolynomial.aeval x P ≠ 0 ∧ (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) ∧
      (MvPolynomial.aeval x P * a) ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval x (cf i) * (MvPolynomial.aeval x P * a) ^ i = 0 := by
  set F := IntermediateField.adjoin K (Set.range fun m => x m / x k₀) with hFdef
  obtain ⟨p, hpm, hp⟩ := ((halg.isAlgebraic a).isIntegral : IsIntegral F a)
  have hq : ∀ i, HomQ K x ((p.coeff i : F) : L) := fun i => homQ_of_mem_adjoin x k₀ hx (p.coeff i).2
  choose e A B hA hB hBx hf using hq
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
  set P : MvPolynomial (Fin N) K := MvPolynomial.X k₀ * ∏ i ∈ Finset.range n, B i with hPdef
  have hPh : P.IsHomogeneous (1 + ∑ i ∈ Finset.range n, e i) :=
    (MvPolynomial.isHomogeneous_X K k₀).mul (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => hB i)
  have hPx : MvPolynomial.aeval x P = x k₀ * ∏ i ∈ Finset.range n, MvPolynomial.aeval x (B i) := by
    rw [hPdef, map_mul, MvPolynomial.aeval_X, map_prod]
  have hPx0 : MvPolynomial.aeval x P ≠ 0 := by
    rw [hPx]; exact mul_ne_zero hx (Finset.prod_ne_zero_iff.2 fun i _ => hBx i)
  refine ⟨1 + ∑ i ∈ Finset.range n, e i, n, P,
    fun i => P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i,
    by omega, hPh, hPx0, ?_, ?_⟩
  · intro i hi
    have hS : ∑ j ∈ Finset.range n, e j = e i + ∑ j ∈ (Finset.range n).erase i, e j :=
      (Finset.add_sum_erase _ _ (Finset.mem_range.2 hi)).symm
    have h1 := ((hPh.pow (n - i - 1)).mul ((MvPolynomial.isHomogeneous_X K k₀).mul
      (MvPolynomial.IsHomogeneous.prod ((Finset.range n).erase i) B e fun j _ => hB j))).mul (hA i)
    convert h1 using 1
    obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, hS]
    ring
  · beta_reduce
    have hp' : Polynomial.aeval a p = 0 := by rw [Polynomial.aeval_def]; exact hp
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul, hn] at hp'
    have key : ∀ i ∈ Finset.range n,
        MvPolynomial.aeval x (P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i) *
          (MvPolynomial.aeval x P * a) ^ i = MvPolynomial.aeval x P ^ n * (p.coeff i • a ^ i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hPi : MvPolynomial.aeval x P = x k₀ * (MvPolynomial.aeval x (B i) *
          ∏ j ∈ (Finset.range n).erase i, MvPolynomial.aeval x (B j)) := by
        rw [hPx, ← Finset.mul_prod_erase _ _ hi]
      have hsm : p.coeff i • a ^ i = MvPolynomial.aeval x (A i) / MvPolynomial.aeval x (B i) * a ^ i := by
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, hf i]
      obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
      have hpow : MvPolynomial.aeval x P ^ n =
          MvPolynomial.aeval x P ^ t * MvPolynomial.aeval x P * MvPolynomial.aeval x P ^ i := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hsm, hpow]
      simp only [map_mul, map_pow, MvPolynomial.aeval_X, map_prod]
      rw [ht, Nat.add_sub_cancel, hPi]
      field_simp [hBx i]
      ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, mul_pow, ← mul_add, add_comm, hp', mul_zero]

end Alg

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def IntFormSt {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → (recB h.toLawsCore).Cusp j wL) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (k n : ℕ) (cf : ℕ → MvPolynomial (Fin N) T.Q.c.F) (b : Om Z), 0 < k →
    (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) →
    b ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval (fun m => evC hG Z ((w m : (recB h.toLawsCore).Cusp j wL) : T.R j)) (cf i) * b ^ i = 0 →
    ∃ g : (recB h.toLawsCore).Cusp j (wsmul k wL),
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j) = b

theorem birSt_of (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (hB2 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
      Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
        evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
          evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)
    (hint : IntFormSt h j hG G.w) : BIRSt h j hj hG G := by
  intro Z a
  obtain ⟨k₀, hx0, htrF⟩ := hB2 Z
  have halg := isAlgebraic_of_trdeg_eq _ _ htrF (htr Z)
  obtain ⟨k, n, P, cf, hk, hP, hP0, hcf, heq⟩ := exists_homInt (K := T.Q.c.F) _ k₀ hx0 halg a
  obtain ⟨g, hg⟩ := hint Z k n cf _ hk hcf heq
  exact ⟨k, g, P, hP, hP0, by rw [hg, mul_comm]⟩

theorem birSt_of_big (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hBig : BigAt h j hj hG G) (hint : IntFormSt h j hG G.w) :
    BIRSt h j hj hG G :=
  birSt_of h j hj hG htr G hBig.2 hint

end Formalism.L2.Pj
end
end
