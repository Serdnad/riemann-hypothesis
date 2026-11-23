module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle139
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_section_holds : SARadSec := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl e he U
  classical
  let g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := fun x =>
    (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2
  let φ := (NF.QR P.k P.r Bs.z Bs.z').indicator g
  have hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT := Set.ext (qr_iff P Bs hpl)
  have hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT) := by
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ))
        (MA.Qset P.r P.TT) := by
      refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
      refine ContDiffOn.inv ?_ fun x hx => (Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx)).ne'
      exact (Formalism.FourierDecayAlt.P.CutMP.En.wq_contDiff P.k P.r P.TT).contDiffOn.sqrt fun x hx =>
        (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx).ne'
    refine hw.smul (ContDiffOn.sum fun ρ _ => ?_)
    have hF : ContDiffOn ℝ ∞ (MA.ext (U ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := (U ρ).2
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    exact hF.smul he'
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hQR]
      exact hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]
    · simp only [φ, Set.indicator_of_mem hx, g]
      have hx' : P.TT < Complex.normSq x.2 := ((qr_iff P Bs hpl x).1 hx).2
      have h1 := fib_sum_smul P Bs x.2 (fun ρ => MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x) (fun ρ => e ρ x.2) fun ρ => (he.2 x.2 hx').1 ρ
      by_cases hne : Nonempty (M.Ty P)
      · obtain ⟨ρ0⟩ := hne
        intro p hp
        have h3 := fib_sum_smul P Bs x.2 (fun ρ => if ρ = ρ0 then (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) else 0)
          (fun _ => ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2) (fun _ => h1) p hp
        simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
        exact h3
      · have : ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2 = 0 := by
          rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hne)]; simp
        rw [this, smul_zero]
        intro p hp
        ext v
        simp
    · simp [φ, Set.indicator_of_notMem hx]
  obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'
    (radBase P Bs hpl) φ hφ
  refine ⟨Φ, hΦ, fun q => ?_⟩
  have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (qr_iff P Bs hpl q.1).2 q.2
  have h := congrFun hrad q.1
  simp only [NF.radR, Set.indicator_of_mem hq, φ] at h
  rw [h]
  simp only [g]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  simp [MA.ext, q.2]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem mem_level_zero_of_mem_group {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

def LocSm (g₀ : B.Mat k r) (h : B.Mat k r → E') : Prop :=
  ∃ (U : Set (B.Mat k r)) (F : B.Mat k r → E'), IsOpen U ∧ g₀ ∈ U ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ x ∈ U, x ∈ B.GV k r → h x = F x

theorem locSm_of_ckOn {UU : Set (B.Mat k r)} {h : B.Mat k r → E'} (hh : B.CkOn ⊤ UU h) {g₀ : B.Mat k r}
    (hg : g₀ ∈ UU) : LocSm g₀ h := hh g₀ hg

theorem locSm_zero (g₀ : B.Mat k r) : LocSm g₀ (fun _ => (0 : E')) :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem locSm_add {g₀ : B.Mat k r} {h₁ h₂ : B.Mat k r → E'} (h1 : LocSm g₀ h₁) (h2 : LocSm g₀ h₂) :
    LocSm g₀ (fun x => h₁ x + h₂ x) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := h1
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := h2
  exact ⟨U₁ ∩ U₂, fun x => F₁ x + F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
    (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right),
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩

theorem locSm_smul {g₀ : B.Mat k r} {h : B.Mat k r → E'} (c : ℂ) (h1 : LocSm g₀ h) :
    LocSm g₀ (fun x => c • h x) := by
  obtain ⟨U, F, o, m, cd, e⟩ := h1
  exact ⟨U, fun x => c • F x, o, m, cd.const_smul c, fun x hx hxG => by simp only [e x hx hxG]⟩

theorem locSm_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] {g₀ : B.Mat k r}
    {a : B.Mat k r → (E' →L[ℂ] E₂)} {φ : B.Mat k r → E'} (ha : LocSm g₀ a) (hφ : LocSm g₀ φ) :
    LocSm g₀ (fun x => a x (φ x)) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := ha
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := hφ
  refine ⟨U₁ ∩ U₂, fun x => F₁ x (F₂ x), o₁.inter o₂, ⟨m₁, m₂⟩, ?_,
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩
  have c₁' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (F₁ x).restrictScalars ℝ) (U₁ ∩ U₂) :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E' E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (c₁.mono Set.inter_subset_left))
  exact c₁'.clm_apply (c₂.mono Set.inter_subset_right)

theorem locSm_listSum {ι : Type*} {g₀ : B.Mat k r} (l : List ι) (φ : ι → B.Mat k r → E')
    (h : ∀ i ∈ l, LocSm g₀ (φ i)) : LocSm g₀ (fun x => (l.map fun i => φ i x).sum) := by
  induction l with
  | nil => simpa using locSm_zero (E' := E') g₀
  | cons a l ih =>
    simpa using locSm_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem ckOn_Rw_top {f : B.Mat k r → E'} (hf : B.CkOn ⊤ (B.GV k r) f) (w : List (B.Mat k r))
    (hw : ∀ X ∈ w, B.inLie k r X) : B.CkOn ⊤ (B.GV k r) (B.Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    have ih' := ih (fun Y hY => hw Y (by simp [hY]))
    show B.CkOn ⊤ (B.GV k r) (RdV X (B.Rw w f))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) (hw X (by simp)) (by rw [top_add]; exact ih')

theorem locSm_smoothLev {O : Set (B.Mat k r)} {h : B.Mat k r → E'}
    (hh : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → LocSm g₀ h) : Q.SmoothLev k r 0 O h := by
  intro g₀ hg₀
  obtain ⟨U, F, o, m, c, e⟩ := hh g₀ hg₀.1.1 hg₀.2
  exact ⟨U, F, o, m, c, fun x hx hxG => e x hx hxG.1⟩

end loc

theorem extension_locality_holds : ExtLoc := by
  intro k r E' _ _ O J hO hJ g₀ hg₀ hg₀O
  obtain ⟨U₀, F, hU₀, hgU₀, hF, hFJ⟩ := hJ g₀ ⟨mem_level_zero_of_mem_group hg₀, hg₀O⟩
  have hV : U₀ ∩ O ∈ nhds g₀ := (hU₀.inter hO).mem_nhds ⟨hgU₀, hg₀O⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  let b : ContDiffBump g₀ := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  have hts : tsupport (fun x => b x • F x) ⊆ Metric.closedBall g₀ (2 * ε / 3) :=
    (tsupport_smul_subset_left _ _).trans b.tsupport_eq.subset
  have hcb : Metric.closedBall g₀ (2 * ε / 3) ⊆ U₀ ∩ O := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  refine ⟨fun x => b x • F x, Metric.ball g₀ (ε / 3), ?_, ?_, fun x hx => (hcb (hts hx)).2,
    Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_⟩
  · intro g _
    refine ⟨Set.univ, fun x => b x • F x, isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    apply ContDiff.contDiffOn
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U₀
    · exact ((b.contDiff.contDiffOn).smul hF).contDiffAt (hU₀.mem_nhds hx)
    · have hx' : x ∉ tsupport (fun x => b x • F x) := fun h => hx (hcb (hts h)).1
      exact (contDiffAt_const (c := (0 : E'))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hx')
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall g₀ (2 * ε / 3)) (isClosed_tsupport _) hts
  · intro x hx hxG
    have hb : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U₀ := (hball (Metric.ball_subset_ball (by linarith) hx)).1
    simp only [hb, one_smul]
    exact (hFJ x hxU (mem_level_zero_of_mem_group hxG)).symm

theorem smooth_operators_holds : SmoothOps := by
  intro k r Wp Wq _ _ _ _ _ D Θ O hO hOP hΘ f hf hs
  have hsupp : closure {g | g ∈ B.GV k r ∧ f g ≠ 0} ⊆ B.GPos D := by
    intro x hx
    have hxG : x ∈ B.GV k r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f := closure_mono (by exact fun y hy => hy.2) hx
    exact hOP x (hs hxT) hxG
  constructor
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    exact locSm_clm (locSm_of_ckOn (hΘ T hT).1 (hOP g₀ hg₀O hg₀))
      (locSm_of_ckOn (ckOn_Rw_top hf T.word T.word_lie) hg₀)
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    apply locSm_smul
    have hc : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (f x)) :=
      Formalism.FourierDecayAlt.P.B5.ckOn_coef (hΘ T hT).2 hf hsupp
    exact locSm_of_ckOn (ckOn_Rw_top hc T.word.reverse
      (fun X hX => T.word_lie X (List.mem_reverse.1 hX))) hg₀

theorem omP_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    OmP S T v = Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this]
      rw [show Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨0, by omega⟩ = 1 by
        unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (S.G.r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by have := a.isLt; simp only [Fin.val_mk]; omega)⟩

theorem positive_domain_condition_holds : OmPDom := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v
  refine ⟨?_, fun g hg hgG => ⟨hgG, hg.1⟩⟩
  rw [omP_eq]
  exact Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (T v).base.z_mem (T v).base.z'_mem

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem foldCV_nil (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (H : B.Mat k r → E) :
    foldCV k r s [] H = H := rfl

theorem foldCV_cons (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (x : C.Letter)
    (a : List C.Letter) (H : B.Mat k r → E) :
    foldCV k r s (x :: a) H = s • Q.CV k r (x.2 : ℂ) (foldCV k r s a H) := rfl

theorem foldCV_mem {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_mem hcl hJ s a) x.2 s

theorem om_sub {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  obtain ⟨hU, hD, hG⟩ := hg
  refine ⟨⟨hU, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ ?_⟩
  show (a : ℕ) + 1 ≤ r
  omega

theorem energyTr_of_parts (hR : FoldRev) (hL : AdmLen) (hBF : BesselFoldBuilt) (hL2 : L2BoundAtTowerPlace) (hBe : BetaFrame) :
    EnergyTr := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hcl ε hε hJF a hadm
  have hB' := hB
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := hB'
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, _, _⟩ := hv v
  have hlen : a.length ≤ S.Ntop := hL E Wp Wq S v a hadm
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set J₁ := foldCV S.G.k S.G.r s a.reverse (B.JF Db F) with hJ₁
  have hJ₁m : J₁ ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_mem hcl hJF s _
  have hOpen : IsOpen (OmP S T v) := (isDom_omP Db.z_mem Db.z'_mem).1

  have hae : ∀ᵐ p ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)),
      bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p = 0 ∨
        B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p) = J₁ (B.gq Db p) := by
    have h0 := ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict Db)
    filter_upwards [h0] with p hp
    by_cases hq : p ∈ B.Qset Db
    · right
      have hg := Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db p (hp hq)
      rw [hBF E Wp Wq S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF a hlen _ hg]
      exact (hR _ _ _ _ _ _ _ _ _ hOpen hcl _ hJF s a _ (om_sub hg)).symm
    · left
      exact le_antisymm (not_lt.1 hq) (Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ p)
  have hN1 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (J₁ (B.gq Db q))) ≠ ⊤ := by
    have h := hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε a hlen
    unfold B.normSq at h
    unfold jNormSq at h ⊢
    rwa [lintegral_congr_ae (hae.mono fun p hp => ?_)] at h
    rcases hp with hp | hp
    · rw [show bcWeight S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') p = 0 from hp]
      simp
    · show ENNReal.ofReal (_ * ‖B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))‖ ^ 2) = _
      rw [hp]
  have hN2 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (B.JF Db F (B.gq Db q))) ≠ ⊤ :=
    hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε [] (Nat.zero_le _)
  have hBeq := hBe E Wp Wq S T v hplace e hFr J₁ hJ₁m (B.JF Db F) hJF hN1 hN2
  unfold C7.principalHermitianLattice B.beta
  show _ = MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.JF Db F))
  rw [← hBeq]
  unfold betaBig
  refine integral_congr_ae (hae.mono fun p hp => ?_)
  rcases hp with hp | hp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _ =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _
    rw [hp]; simp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))) =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (J₁ (B.gq Db p)))
    rw [hp]

end Formalism.FourierDecayAlt.P.CutMP.En
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem connection_uniqueness_holds : GTCConnUniq := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he A B A' B' hAB hAB' hC hC' ρ ζ hζ
  obtain ⟨Φ, hΦ, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have h1 := (hC Φ ρ).1
  have h2 := (hC' Φ ρ).1
  rw [hΦ] at h1 h2
  simp only [mul_one] at h1 h2
  have h3 : fnZ P (A ρ) = fnZ P (A' ρ) := by
    have := h1.symm.trans h2
    exact add_left_cancel this
  rw [fnZ_eq_mk P (hAB ρ).1, fnZ_eq_mk P (hAB' ρ).1] at h3
  have hq : ((fun _ => (1 : ℂ), ζ) : (Fin P.r → ℂ) × ℂ) ∈ MA.Qset P.r P.TT :=
    ⟨fun _ => one_ne_zero, hζ⟩
  have := congrFun (congrArg Subtype.val h3) ⟨_, hq⟩
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd
open scoped ComplexConjugate

noncomputable section

section cs

variable {n : ℕ}

theorem xs_upL (x0 : ℂ → ℂ) : ∀ (L : List (Letter ℂ (Fin n))) (E : Ix (Fin (n + 1))) (Y : ℂ),
    Fr.xs x0 (L.map PBF.upL) E Y = Fr.xs x0 L (fun a => E a.succ) Y
  | [], _, _ => rfl
  | l :: L, E, Y => by
    simp only [List.map_cons, Fr.xs]
    rw [xs_upL x0 L E Y]
    rfl

theorem cs_upL (x0 q0 : ℂ → ℂ) : ∀ (L : List (Letter ℂ (Fin n))) (E : Ix (Fin (n + 1))),
    Fr.cs x0 q0 (L.map PBF.upL) E = Fr.cs x0 q0 L (fun a => E a.succ)
  | [], _ => rfl
  | l :: L, E => by
    simp only [List.map_cons, Fr.cs]
    simp only [cs_upL, xs_upL,
      show qw q0 (L.map PBF.upL) = qw q0 L from funext fun Y => PBF.qw_map_reindex q0 Fin.succ L Y]
    rfl

theorem cW_cons_plus (P : M.Par) (l0 : ℕ) (y : ℝ) (w : List C.Letter) (E : Ix (Fin (w.length + 1))) (ρ : M.Ty P) :
    Top.cW P l0 ((true, y) :: w) E ρ = Top.cW P l0 w (fun a => E a.succ) ρ *
      (if E 0 = 0 then qw (M.qC P) (D.positionted w) (y : ℂ) /
          Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) (fun a => E a.succ) ((y : ℂ) + 1)
        else Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) (fun a => E a.succ) (y : ℂ)) := by
  unfold Top.cW
  rw [PBF.positioned_cons]
  simp only [Fr.cs, if_true]
  simp only [cs_upL, xs_upL, show qw (M.qC P) ((D.positionted w).map PBF.upL) = qw (M.qC P) (D.positionted w) from
    funext fun Y => PBF.qw_map_reindex _ Fin.succ _ Y]

def topRprod {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Ix (Fin a.length)) (ρ : M.Ty P) : List ℝ → ℂ
  | [] => 1
  | y :: ys => topRprod l0 a e ρ ys * topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y

theorem cW_plusW (P : M.Par) (l0 : ℕ) (a : List C.Letter) (e : Ix (Fin a.length)) (ρ : M.Ty P) :
    ∀ ys : List ℝ, Top.cW P l0 (KB.plusW ys a) (KB.firstSt ys e) ρ = Top.cW P l0 a e ρ * topRprod l0 a e ρ ys
  | [] => by simp [topRprod, KB.plusW, KB.firstSt]
  | y :: ys => by
    have h := cW_cons_plus P l0 y (KB.plusW ys a) (Fin.cons (0 : Fin 2) (KB.firstSt ys e)) ρ
    simp only [Fin.cons_zero, Fin.cons_succ, if_true] at h
    show Top.cW P l0 ((true, y) :: KB.plusW ys a) (Fin.cons (0 : Fin 2) (KB.firstSt ys e)) ρ = _
    rw [h, cW_plusW P l0 a e ρ ys]
    simp only [topRprod, topR]
    ring

end cs

end

end Formalism.FourierDecayAlt.P.PBL
end
