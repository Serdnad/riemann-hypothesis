module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem torus_parameter : GTCTT := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH
  have hOK : P.OK := hH.1.1
  show 0 ≤ P.T * P.T'
  exact (mul_pos hOK.T_pos hOK.T'_pos).le

section frame

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  first
  | rfl
  | (simp [B.hsVec]; done)
  | (unfold B.hsVec; rw [← WithLp.toLp_smul]; rfl)

theorem star_mul_self_of_norm {z : ℂ} (h : ‖z‖ = 1) : star z * z = 1 := by
  calc star z * z = (starRingEnd ℂ) z * z := rfl
    _ = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
    _ = 1 := by rw [h]; norm_num

theorem isFrameB_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ) (he : IsFrameB P Bs e)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) :
    IsFrameB P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  obtain ⟨hs, hf⟩ := he
  refine ⟨fun ρ => (hu ρ).1.smul (hs ρ), fun ζ hζ => ?_⟩
  obtain ⟨hF, hO, hX⟩ := hf ζ hζ
  have hn : ∀ ρ, star (u ρ ζ) * u ρ ζ = 1 := fun ρ => star_mul_self_of_norm ((hu ρ).2 ζ hζ)
  refine ⟨fun ρ => ?_, fun ρ ρ' => ?_, fun X hXF => ?_⟩
  · have h1 := hF ρ
    beta_reduce
    simp only [NF.Fib, Set.mem_setOf_eq] at h1 ⊢
    intro p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h1 p hp]
  · beta_reduce
    rw [hsVec_smul, hsVec_smul, inner_smul_left, inner_smul_right, hO ρ ρ']
    split_ifs with h
    · subst h
      rw [mul_one]
      exact hn ρ
    · rw [mul_zero, mul_zero]
  · conv_lhs => rw [hX X hXF]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    beta_reduce
    rw [hsVec_smul, inner_smul_left, smul_smul]
    congr 1
    rw [show (starRingEnd ℂ) (u ρ ζ) = star (u ρ ζ) from rfl]
    linear_combination (-(inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X))) * hn ρ

end frame

section trans

theorem comp_snd_mem_smSub (P : M.Par) {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) :
    (fun q : MA.Qp P.r P.TT => v q.1.2) ∈ MA.smSub P.r P.TT := by
  show ContDiffOn ℝ MA.sm (MA.ext (fun q : MA.Qp P.r P.TT => v q.1.2)) (MA.Qset P.r P.TT)
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MA.E P.r => v x.2) (MA.Qset P.r P.TT) :=
    hv.comp contDiff_snd.contDiffOn (fun x hx => show P.TT < Complex.normSq x.2 from hx.2)
  exact h1.congr (fun x hx => by simp [MA.ext, hx])

theorem fnZ_eq_mk (P : M.Par) {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) :
    fnZ P v = ⟨fun q => v q.1.2, comp_snd_mem_smSub P hv⟩ := by
  unfold fnZ MA.toSm
  exact dif_pos (comp_snd_mem_smSub P hv)

theorem toSm_mulZ (P : M.Par) {v w : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P))
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ann P)) (hvw : ∀ ζ ∈ Ann P, w ζ * v ζ = 1)
    (g : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (fun q => v q.1.2 * g q) = fnZ P v * MA.toSm P g := by
  by_cases hg : g ∈ MA.smSub P.r P.TT
  · have hvg : (fun q : MA.Qp P.r P.TT => v q.1.2 * g q) ∈ MA.smSub P.r P.TT :=
      (MA.smSub P.r P.TT).mul_mem (comp_snd_mem_smSub P hv) hg
    rw [fnZ_eq_mk P hv]
    unfold MA.toSm
    rw [dif_pos hvg, dif_pos hg]
    rfl
  · have hvg : (fun q : MA.Qp P.r P.TT => v q.1.2 * g q) ∉ MA.smSub P.r P.TT := by
      intro h
      apply hg
      have h2 := (MA.smSub P.r P.TT).mul_mem (comp_snd_mem_smSub P hw) h
      convert h2 using 1
      funext q
      have h3 : w q.1.2 * v q.1.2 = 1 := hvw q.1.2 q.2.2
      simp only [Pi.mul_apply]
      rw [← mul_assoc, h3, one_mul]
    unfold MA.toSm
    rw [dite_eq_right hvg, dite_eq_right hg, mul_zero]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rawR_phase (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (u : M.Ty P → ℂ → ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawR P μsec (fun ρ ζ => u ρ ζ • e ρ ζ) Φ ρ = fun q => star (u ρ q.1.2) * rawR P μsec e Φ ρ q := by
  funext q
  simp only [rawR, hsVec_smul, inner_smul_left]
  rw [show star (u ρ q.1.2) = (starRingEnd ℂ) (u ρ q.1.2) from rfl]
  ring

theorem conj_smooth {v : ℂ → ℂ} {s : Set ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => star (v ζ)) s := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  exact hs.comp_contDiffOn hv

theorem trR_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    trR P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) Φ ρ = fnZ P (fun ζ => star (u ρ ζ)) * trR P Bs e Φ ρ := by
  simp only [trR]
  rw [rawR_phase]
  exact toSm_mulZ P (conj_smooth (hu ρ).1) (hu ρ).1
    (fun ζ hζ => by
      show u ρ ζ * star (u ρ ζ) = 1
      rw [mul_comm]
      exact star_mul_self_of_norm ((hu ρ).2 ζ hζ)) _

end trans

section act

def mulQ (P : M.Par) (x : (MA.DQ P).Pr) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := x.1 f

theorem actA_diag (P : M.Par) (x : M.Ty P → (MA.DQ P).Pr) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (Matrix.diagonal x : MA.A P (MA.DQ P)) g ρ = (x ρ).1 (g ρ) := by
  unfold MA.actA
  refine (Fintype.sum_eq_single ρ (fun b hb => ?_)).trans ?_
  · have h0 := congrArg (fun m : (MA.DQ P).Pr => m.1 (g b)) (Matrix.diagonal_apply_ne x (Ne.symm hb))
    exact h0.trans (by first | rfl | simp)
  · exact congrArg (fun m : (MA.DQ P).Pr => m.1 (g ρ)) (Matrix.diagonal_apply_eq x ρ)

theorem algebraMap_fst_apply (P : M.Par) (c : ℂ) (f : MA.SmQ P.r P.TT) :
    (algebraMap ℂ (MA.DQ P).Pr c).1 f = c • f := rfl

theorem actA_kap (P : M.Par) (f : M.Ty P → ℂ) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.kap P (MA.DQ P) f) g ρ = f ρ • g ρ := by
  have hk : (MA.kap P (MA.DQ P) f : MA.A P (MA.DQ P)) =
      Matrix.diagonal (fun π => algebraMap ℂ (MA.DQ P).Pr (f π)) := by
    first
    | rfl
    | (ext i j; simp [MA.kap, Matrix.diagonal_apply])
  rw [hk, actA_diag, algebraMap_fst_apply]

theorem actA_nabA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.nabA P (MA.DQ P)) g ρ =
      dzQ P (g ρ) + (M.aC P ρ : ℂ) • mulQ P (MA.DQ P).zbP (mulQ P ((MA.DQ P).ggiP P.TT) (g ρ)) := by
  unfold MA.nabA
  rw [actA_diag]
  rfl

theorem actA_nabsA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.nabsA P (MA.DQ P)) g ρ =
      -dzbQ P (g ρ) + (M.aC P ρ : ℂ) • mulQ P (MA.DQ P).zP (mulQ P ((MA.DQ P).ggiP P.TT) (g ρ)) := by
  unfold MA.nabsA
  rw [actA_diag]
  rfl

end act

section kap

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem kapF_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1)
    (hk : KapF P Bs d e) : KapF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  unfold KapF at hk ⊢
  intro f Φ
  funext ρ
  rw [actA_kap, trR_phase P Bs e u hu, trR_phase P Bs e u hu, hk f Φ, actA_kap, mul_smul_comm]

end kap

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def FundG : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A A' : B.Mat k r → (Wq →L[ℂ] Wp)), ContinuousOn A (B.GV k r) → ContinuousOn A' (B.GV k r) →
    (∀ φ : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) φ → HasCompactSupport φ → B.SuppIn (B.GPos D) φ →
      ∫ x : Mt k r, B.hsInner (A (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG =
        ∫ x : Mt k r, B.hsInner (A' (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG) →
    ∀ g ∈ B.GPos D, A g = A' g

def AdjCont : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ContinuousOn (B.opAdj Θ (B.rho D p f)) (B.GV k r) ∧
        ContinuousOn (B.rho D p (B.opAdj Θ f)) (B.GV k r)

def AdjInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ∀ φ : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) φ → HasCompactSupport φ →
        B.SuppIn (B.GPos D) φ →
        ∫ x : Mt k r, B.hsInner (B.opAdj Θ (B.rho D p f) (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG =
          ∫ x : Mt k r, B.hsInner (B.rho D p (B.opAdj Θ f) (Matrix.of x)) (φ (Matrix.of x)) ∂D.μG

theorem adjComm_of_parts (hF : FundG) (hC : AdjCont) (hI : AdjInt) : AdjComm := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp g hg
  obtain ⟨c1, c2⟩ := hC k r Wp Wq D Θ hs f hf hfc hfs p hp
  exact hF k r Wp Wq D _ _ c1 c2 (fun φ h1 h2 h3 => hI k r Wp Wq D Θ hs hc f hf hfc hfs p hp φ h1 h2 h3) g hg

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

abbrev GFn (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type := B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))

def smoothFormsPositiveCone (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) : Set (GFn S v) :=
  Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

def GfP (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (g : B.Mat S.G.k S.G.r) : ℝ :=
  Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g

def mulG (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (ψ : ℝ → ℝ) (J : GFn S v) : GFn S v :=
  fun g => ((ψ (GfP S T v g) : ℝ) : ℂ) • J g

def CCg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (A Bg : ℝ) (F : GFn S v) : Prop :=
  ∀ m : ℕ, B.InCC (A - Bg * m) m F

def CutCoef (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ) : Prop :=
  ∀ Tm ∈ Θ, ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r),
    (∀ X ∈ u, B.unitLie S.G.k S.G.r X) → (∀ X ∈ w, B.unitLie S.G.k S.G.r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV S.G.k S.G.r, ε ≤ GfP S T v g →
      ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ (d + Bg * m) ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ (d + Bg * m)

def IsAAOp (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) : Prop :=
  B.SmoothCoef (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θ

def LocCC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (A Bg : ℝ) (J : GFn S v) : Prop :=
  J ∈ smoothFormsPositiveCone S T v ∧ ∀ δ : ℝ, 0 < δ → ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ CCg S v A Bg F ∧
    ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, δ ≤ GfP S T v (B.gq (T v).base x) →
      J (B.gq (T v).base x) = B.JF (T v).base F (B.gq (T v).base x)

def applyL (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (J : GFn S v) : GFn S v :=
  Θs.foldr (fun Θ J' => B.opApply Θ J') J

def adjL (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (J : GFn S v) : GFn S v :=
  Θs.foldl (fun J' Θ => B.opAdj Θ J') J

end defs

def JABddStar : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), star b ∈ Submonoid.closure (MA.bddSet P L) ∧
      ∀ (ε : ℝ) (U V : M.Ty P → MA.SmQ P.r P.TT), 0 < ε →
        (∀ π q, MA.Gq P q < ε → MA.evQ P (U π) q = 0) →
        (∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ P (U π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) →
        (∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ P (V π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) →
        MA.ipA P U (MA.actA P b V) = MA.ipA P (MA.actA P (star b) U) V

def JAIsAdj : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ a ∈ Submonoid.closure (MA.hatSet P L ∪ MA.bddSet P L), MA.IsAdjA P a

def JAPhiOp : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → ∀ φ : ℝ → ℝ, LE.SmoothLog φ →
      ∀ J ∈ smoothFormsPositiveCone S T v, mulG S T v φ J ∈ smoothFormsPositiveCone S T v ∧
        trJ S T v e (mulG S T v φ J) =
          fun π => MA.toSm (D.parOf S v) (fun q => (φ (MA.Gq (D.parOf S v) q) : ℂ)) * trJ S T v e J π

def JAStarOp : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ a ∈ Submonoid.closure (MA.hatSet (D.parOf S v) L ∪ MA.bddSet (D.parOf S v) L), ∀ ts : List (ℂ × List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))), (∀ t ∈ ts, ∀ Θ ∈ t.2, IsAAOp S T v Θ) →
        (∀ J ∈ smoothFormsPositiveCone S T v, (∀ t ∈ ts, applyL S v t.2 J ∈ smoothFormsPositiveCone S T v ∧ adjL S v t.2 J ∈ smoothFormsPositiveCone S T v) ∧
          MA.actA (D.parOf S v) a (trJ S T v e J) = (ts.map fun t => t.1 • trJ S T v e (applyL S v t.2 J)).sum) →
        ∀ J ∈ smoothFormsPositiveCone S T v,
          MA.actA (D.parOf S v) (star a) (trJ S T v e J) = (ts.map fun t => (starRingEnd ℂ t.1) • trJ S T v e (adjL S v t.2 J)).sum

def JAGroupAdj : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ → CutCoef S T v Θ d Bg →
      ∀ ε : ℝ, 0 < ε → ∀ J₁ J₂ : GFn S v,
        LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₁ →
        LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₂ →
        (∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, GfP S T v (B.gq (T v).base x) < ε → J₁ (B.gq (T v).base x) = 0) →
        B.opApply Θ J₁ ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J₂ ∈ smoothFormsPositiveCone S T v →
        MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ J₁)) (trJ S T v e J₂) =
          MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.opAdj Θ J₂))

def JALocCC : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v,
      (∀ (F : GFn S v) (A Bg : ℝ), B.CkOn ⊤ (B.GV S.G.k S.G.r) F → (∀ m : ℕ, B.InCC A m F) →
        B.JF (T v).base F ∈ smoothFormsPositiveCone S T v → 0 ≤ Bg → LocCC S T v A Bg (B.JF (T v).base F)) ∧
      (∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)) ∧
      (∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)) ∧
      (∀ (φ : ℝ → ℝ) (Bg A : ℝ) (J : GFn S v), LE.SmoothLog φ → (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
        Cg * ((S.G.r : ℝ) + 1) ≤ Bg → LocCC S T v A Bg J → mulG S T v φ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v A Bg (mulG S T v φ J)) ∧
      (∀ (Bg A : ℝ) (J J' : GFn S v), 0 ≤ Bg → Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 ≤ A →
        LocCC S T v A Bg J → LocCC S T v A Bg J' → LocCC S T v A Bg (J + J')) ∧
      (∀ (Bg A : ℝ) (c : ℂ) (J : GFn S v), LocCC S T v A Bg J → LocCC S T v A Bg (c • J)) ∧
      (∀ (Bg A A' : ℝ) (J : GFn S v), A' ≤ A → LocCC S T v A Bg J → LocCC S T v A' Bg J) ∧
      (∀ (Bg A ε : ℝ) (J : GFn S v) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → 0 ≤ Bg → 0 < ε →
        Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * Bg ≤ A → LocCC S T v A Bg J →
        ∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT))

def JAFFStable : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))), IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end
