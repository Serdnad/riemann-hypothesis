module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle009
public import Formalism.HermitianCurvature.Bundle005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothDecayOfWeighted
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle001
public import Formalism.HermitianCurvature.StatementNF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff

noncomputable section



namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smooth_zero (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH]
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => map_zero (σ g)⟩

theorem smooth_add {σ : Mx k r → (H →L[ℂ] H)} {v w : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ)
    (hw : w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) : v + w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv hw ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hGe⟩ := hw g₀ hg₀
  refine ⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  simp only [map_add (f := _), hFe g hg.1 hgH, hGe g hg.2 hgH]

theorem smooth_smul {σ : Mx k r → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) :
    a • v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, fun g hg hgH => ?_⟩
  simp only [map_smul, hFe g hg hgH]

theorem DD_smooth (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hw : PI.UpqRep.IsLowUnitH k r ε lam σ w0) :
    ∀ x ∈ DDsp σ w0, x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hrep := hDS.2.2.1.1.2
  have hconj := Formalism.QuantumDeterminants.unitary_conjugation_holds _ ε (PI.UpqRep.Hpk k r) P hdet hPJ
  have hback : ∀ g, P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      hPP, Matrix.one_mul, Matrix.mul_one]
  have hmul : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      σ (a * b) = (σ a).comp (σ b) := by
    intro a b ha hb
    have ha' := (hconj a).mp ha
    have hb' := (hconj b).mp hb
    have h := hrep _ ha' _ hb'
    simp only [hback] at h
    rw [← h]
    congr 1
    rw [show P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPP, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
  have hinUH : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      PI.UpqRep.inUH (PI.UpqRep.Hpk k r) (a * b) := by
    intro a b ha hb
    unfold PI.UpqRep.inUH at *
    rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * PI.UpqRep.Hpk k r * (a * b) =
      bᴴ * (aᴴ * PI.UpqRep.Hpk k r * a) * b by simp only [Matrix.mul_assoc], ha, hb]
  have hw0 : PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g => σ g w0) :=
    low_smooth_of_k_finite hK k r ε lam H σ w0 hl ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ hw
  have htr : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro g hg
    have hgH : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g := hg
    have hcd : ContDiff ℝ ∞ (fun x : Mx k r => x * g) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)).contDiff
    show PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g' => σ g' (σ g w0))
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFeq⟩ := hw0 (g₀ * g) (hinUH _ _ hg₀ hgH)
    refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g), hU.preimage hcd.continuous, hgU,
      hF.comp hcd.contDiffOn (fun x hx => hx), ?_⟩
    intro x hx hxH
    have hx' := hFeq (x * g) hx (hinUH _ _ hxH hgH)
    simp only at hx'
    show σ x (σ g w0) = F (x * g)
    rw [← hx', hmul x g hxH hgH]
    rfl
  intro x hx
  unfold DDsp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    exact htr g hg
  | zero => exact smooth_zero σ
  | add y z _ _ hy hz => exact smooth_add hy hz
  | smul a y _ hy => exact smooth_smul a hy

end Smooth

end Formalism.FourierDecayAlt.P.DDSmoothness
end
end

section

open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

namespace WordTransvectionCongruences

section Frames

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem ofWord_x_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).x = (Fr.ofWord L st w).x := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hx]

theorem ofWord_q_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hq : st'.q = st.q) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).q = (Fr.ofWord L st w).q := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hq]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hq]

theorem ofWord_xi_congr (L : R.LevelData A r) (st st' : Fr.Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : st'.xi Y = st.xi Y) : (Fr.ofWord L st' w).xi Y = (Fr.ofWord L st w).xi Y := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hY]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hY]

theorem ofWord_N (L : R.LevelData A r) (st : Fr.Start A) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st w).N = w.length := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih]

theorem ofWord_c_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (hq : st'.q = st.q)
    (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1)) :
    (Fr.ofWord L st' w).c = (Fr.ofWord L st w).c := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx, hq]
  | cons l w ih =>
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have hl := hw l List.mem_cons_self
    have hxw := ofWord_x_congr L st st' hx w
    have hqw := ofWord_q_congr L st st' hq w
    have hxi1 := ofWord_xi_congr L st st' w (l.pt + 1) hl.1
    have hxi2 := ofWord_xi_congr L st st' w (l.pt - 1) hl.2
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih', hxw, hqw, hxi1, hxi2]

end Frames

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_diagonal (D : Ix S → Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (Matrix.diagonal D) x a = (D a).1 (x a) := by
  unfold act
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.diagonal_apply_eq]
  · intro b _ hb
    simp only [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    first
      | rfl
      | simp [Pr]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem pow_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (n : ℕ) (Φ : RadSp k r z z' π π') (p : (Fin r → ℂ) × Mx k r)
    (hp : p ∈ DomR k r z z') :
    ((((L.ζ * L.ζb * L.GGi) ^ n).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 =
      (fnVal k r z z' 0 p.2 * fnVal k r z z' 2 p.2 * fnVal k r z z' 5 p.2) ^ n •
        (Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 := by
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, hgi, -⟩ := hAL
  induction n generalizing Φ with
  | zero => simp only [pow_zero, one_smul]; rfl
  | succ n ih =>
    rw [pow_succ, pr_fst_mul, Module.End.mul_apply, ih, pr_fst_mul, pr_fst_mul, Module.End.mul_apply,
      Module.End.mul_apply, hz, hzb, hgi]
    simp only [mkP]
    rw [X.fn_apply 0 _ p hp, X.fn_apply 2 _ p hp, X.fn_apply 5 _ p hp, smul_smul, smul_smul, smul_smul, pow_succ]
    ring_nf

end Act

theorem hsInner_zero_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (V : Wq →L[ℂ] Wp) : B.hsInner 0 V = 0 := by
  unfold B.hsInner
  have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
    unfold B.hsVec
    ext i
    simp
  rw [h0, inner_zero_right]

end WordTransvectionCongruences

open WordTransvectionCongruences in
theorem topDensNonnegOfKappa : TopDensNonnegOfKappa := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 K hD hl1 hlk hK
  obtain ⟨κ, hκx, hκxi, hκpos⟩ := hK
  obtain ⟨hPl, -, hAL, -, hq, -, -, -⟩ := hD
  intro w hw x _ c _ g

  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hCD := (Formalism.FourierDecayAlt.P.c_diagonal (Pr (RadSp P.k P.r z z' π π')) S P.r L st' (M.Ty P) κ
    (fun ρ Y => M.x0 P l0 ρ Y) hκx (fun Y => rfl) w).2.2
  have hc : (Fr.ofWord L st w).c = Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [← ofWord_c_congr L st st' rfl rfl w, hCD]
    · rw [← hq]
    · intro l hl
      have h := hw.1.2.2.1 l hl
      exact ⟨(hκxi _ h.2.1).symm, (hκxi _ h.2.2.1).symm⟩

  have hpos : ∀ (e : Ix S) (ρ : M.Ty P), 0 < Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    intro e ρ
    have h := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
      Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true S P.k P.u P.u' (M.rho P ρ) l0 P.T P.T' w hl1 hlk
      (Formalism.FourierDecayAlt.P.types_interlace P hPl.1 ρ) hPl.1.T_pos hPl.1.T'_pos hw.2.1 hw.2.2 e
    rw [Complex.lt_def]
    exact ⟨h.1, h.2.symm⟩
  unfold topDens
  refine Finset.sum_nonneg fun e _ => ?_
  have hd : (Fr.ofWord L st w).d L = io ((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N) *
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [Fr.FrameData.d, hc, Fr.wt, io, io, map_pow]
  rw [act_mul, hd, act_mul, act_io, act_diagonal]
  set Φ := act (Fr.ofWord L st w).F x e
  by_cases hp : (c, g) ∈ DomR P.k P.r z z'
  · have := pow_apply X L hAL (Fr.ofWord L st w).N ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ) (c, g) hp
    simp only at this
    rw [this, hsInner_smul_left]
    refine mul_nonneg ?_ (hκpos _ (hpos e) Φ c g)
    obtain ⟨-, -, hGG⟩ := hp
    have hre : fnVal P.k P.r z z' 0 g * fnVal P.k P.r z z' 2 g * fnVal P.k P.r z z' 5 g =
        ((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) := by
      simp only [fnVal, Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
      rfl
    rw [hre, ← Complex.ofReal_pow]
    exact Complex.zero_le_real.mpr (pow_nonneg (mul_nonneg (Complex.normSq_nonneg _) (inv_nonneg.mpr hGG.le)) _)
  · have h0 := ((((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N).1
      ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ)).2).1 (c, g) hp
    simp only at h0
    rw [h0, hsInner_zero_left]

end Formalism.FourierDecayAlt.P5
end
end

section

open MeasureTheory Real Complex Module

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

theorem unif_bound {X : Type*} (f : ℕ → X → ℝ) (m : ℕ) (h : ∀ j ≤ m, ∃ B, ∀ t, f j t ≤ B) :
    ∃ B, ∀ j ≤ m, ∀ t, f j t ≤ B := by
  choose! B hB using h
  refine ⟨∑ j ∈ Finset.range (m + 1), |B j|, fun j hj t => ?_⟩
  calc f j t ≤ B j := hB j hj t
    _ ≤ |B j| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (m + 1), |B j| :=
        Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))

theorem smooth_extension_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hE : Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t))
    (hc : ∀ t, t ≠ 0 → ContinuousAt D t)
    (hdD : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3)))
    (hdE : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ t, t ≠ 0 → D' t = D t) ∧ (∫ t, D' t = ∫ t, D t) ∧
      (∃ C', ∀ j ≤ m, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ C' * (1 + ‖t‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D') ∧ ∫ t, iteratedFDeriv ℝ j D' t = 0 := by
  set E : ℂ → ℂ := fun t => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t with hEdef
  obtain ⟨D', hD'c, -, hD'eq⟩ := smooth_bounded_of_fourier_decay D m C hD hdD
  obtain ⟨E', hE'c, hE'b, hE'eq⟩ := smooth_bounded_of_fourier_decay E m C hE hdE
  have hEc : ∀ t, t ≠ 0 → ContinuousAt E t := fun t ht => by
    show ContinuousAt (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) t
    exact (((continuous_const.add (continuous_norm.pow 2)).pow 2).continuousAt).smul (hc t ht)
  have hw : ∀ x, E' x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x := by
    have hcont1 : Continuous E' := hE'c.continuous
    have hcont2 : Continuous (fun x : ℂ => ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x) :=
      ((continuous_const.add (continuous_norm.pow 2)).pow 2).smul hD'c.continuous
    have h := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hcont1 hcont2 (fun x hx => by
      have hx0 : x ≠ 0 := hx
      show E' x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x
      rw [hE'eq x (hEc x hx0), hD'eq x (hc x hx0)])
    exact fun x => congrFun h x
  obtain ⟨B, hB⟩ := unif_bound (fun j t => ‖iteratedFDeriv ℝ j E' t‖) m hE'b
  obtain ⟨-, hdec, hint⟩ := smooth_decay_of_weighted (V := ℂ) (by rw [Complex.finrank_real_complex]; norm_num) hE'c B hB hw
  have hae : D' =ᵐ[volume] D := by
    have : ∀ᵐ t ∂(volume : Measure ℂ), t ≠ 0 := by
      rw [ae_iff]; simpa using (measure_singleton (0 : ℂ))
    filter_upwards [this] with t ht
    exact hD'eq t (hc t ht)
  exact ⟨D', hD'c, fun t ht => hD'eq t (hc t ht), integral_congr_ae hae, hdec, hint⟩

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem tendsto_int_uv_ae (I J : α → ℂ) (hI : Integrable I μ) (hJ : Integrable J μ) (u v : ℕ → α → ℂ) (M : ℝ)
    (hum : ∀ n, AEStronglyMeasurable (u n) μ) (hvm : ∀ n, AEStronglyMeasurable (v n) μ)
    (hu : ∀ n x, ‖u n x‖ ≤ 1) (hv : ∀ n x, ‖v n x‖ ≤ M) (hl : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, u n x = 1 ∧ v n x = 0) :
    Tendsto (fun n => ∫ x, (u n x * I x + v n x * J x) ∂μ) atTop (𝓝 (∫ x, I x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖I x‖ + M * ‖J x‖)
    (fun n => ((hum n).mul hI.1).add ((hvm n).mul hJ.1)) (hI.norm.add (hJ.norm.const_mul M))
    (fun n => Filter.Eventually.of_forall fun x => ?_) ?_
  · calc ‖u n x * I x + v n x * J x‖ ≤ ‖u n x * I x‖ + ‖v n x * J x‖ := norm_add_le _ _
      _ ≤ 1 * ‖I x‖ + M * ‖J x‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hu n x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hv n x) (norm_nonneg _))
      _ = ‖I x‖ + M * ‖J x‖ := by ring
  · filter_upwards [hl] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx] with n hn
    rw [hn.1, hn.2]
    ring

end Lim

section Main

def psiC (n : ℕ) (c : ℂ) : ℂ := ((psiL n c : ℝ) : ℂ)

theorem psiC_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiC n) := Complex.ofRealCLM.contDiff.comp (psiL_contDiff n)

theorem fderiv_psiC (n : ℕ) (c : ℂ) : fderiv ℝ (psiC n) c = Complex.ofRealCLM.comp (fderiv ℝ (psiL n) c) := by
  have hd : DifferentiableAt ℝ (psiL n) c := (psiL_contDiffAt n c).differentiableAt (by simp)
  exact (Complex.ofRealCLM.hasFDerivAt.comp c hd.hasFDerivAt).fderiv

theorem norm_c_dZ_psiC_le {C : ℝ} (hC : ∀ t, ‖deriv bumpR t‖ ≤ C) (n : ℕ) (c : ℂ) :
    ‖c * NF.dZ (psiC n) c‖ ≤ C := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, norm_zero]
    exact (norm_nonneg _).trans (hC 0)
  · rw [dZ_eq, fderiv_psiC, norm_mul]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    have hD := norm_mul_fderiv_psiL_le hC n c hc
    have ha : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm 1
    have hb : ‖((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm Complex.I
    have hz : ‖(1 / 2 : ℂ) * (((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ))‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [norm_mul]
      have h3 : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) - Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤
          2 * ‖fderiv ℝ (psiL n) c‖ := by
        calc _ ≤ ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ + ‖Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ ‖fderiv ℝ (psiL n) c‖ + ‖fderiv ℝ (psiL n) c‖ := by
              rw [norm_mul, Complex.norm_I, one_mul]
              exact add_le_add ha hb
          _ = 2 * ‖fderiv ℝ (psiL n) c‖ := by ring
      have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [h2]
      linarith
    calc ‖c‖ * _ ≤ ‖c‖ * ‖fderiv ℝ (psiL n) c‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg c)
      _ ≤ C := hD

theorem psiC_eventually (c : ℂ) (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, psiC n c = 1 ∧ c * NF.dZ (psiC n) c = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |Real.log ‖c‖|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hlt : |Real.log ‖c‖| < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hev := psiL_one_near n c hc hlt
  refine ⟨?_, ?_⟩
  · simp [psiC, hev.eq_of_nhds]
  · rw [dZ_eq, fderiv_psiC, hev.fderiv_eq]
    simp

end Main

end Formalism.FourierDecayAlt.P5.HerB
end
end
