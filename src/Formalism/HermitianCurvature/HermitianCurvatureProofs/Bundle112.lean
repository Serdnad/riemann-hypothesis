module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle105
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle109
public import Formalism.HermitianCurvature.StatementB
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_space_smoothness : RadSpSmooth := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ e he Φ ρ
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  have hz : inWb P.k P.r Bs.z := hpl.2.1
  have hz' : inWb P.k P.r Bs.z' := hpl.2.2.1
  set Qs := MA.Qset P.r P.TT with hQs
  have hζ : ∀ x ∈ Qs, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq x.2 := by
    intro x hx
    rw [hT, hT']
    exact hx.2
  have hmZ : ContDiffOn ℝ ∞ (fun x : MA.E P.r => NF.muZ P.k P.r Bs.μsec x.2) Qs :=
    (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).comp contDiff_snd.contDiffOn fun x hx => hζ x hx
  have hm : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) Qs :=
    contDiffOn_fst.prodMk hmZ
  have hGl : ∀ x ∈ Qs, NF.muZ P.k P.r Bs.μsec x.2 ∈ Q.Glev P.k P.r (Fin.last P.r) := fun x hx =>
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec (hζ x hx))
  have hD : ∀ x ∈ Qs, (x.1, NF.muZ P.k P.r Bs.μsec x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' := fun x hx =>
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := x) ⟨hx.1, hζ x hx⟩
  have hΦq : ContDiffOn ℝ ∞ (fun x : MA.E P.r =>
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (NF.muZ P.k P.r Bs.μsec x.2)) Qs := by
    refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := Φ.2.2.1 _ (hD x₀ hx₀)
    refine ⟨Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U,
      hm.continuousOn.isOpen_inter_preimage (MA.Qset_open P.r P.TT) hU, ⟨hx₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun x : MA.E P.r => F (x.1, NF.muZ P.k P.r Bs.μsec x.2))
        (Qs ∩ (Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U)) :=
      hF.comp (hm.mono fun x hx => hx.1) fun x hx => hx.2.2
    exact hc.congr fun x hx => hΦF _ hx.2.2 (hGl x hx.1)
  have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) Qs :=
    (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
  have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => ((wR P.k P.TT x.2 : ℝ) : ℂ)) Qs := by
    refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
    unfold wR
    refine (((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt
      fun x hx => ?_
    have h2 : P.TT < Complex.normSq x.2 := hx.2
    exact (pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'
  have hin : ContDiffOn ℝ ∞ (fun x : MA.E P.r =>
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (NF.muZ P.k P.r Bs.μsec x.2)))) Qs :=
    (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn hΦq)
  have hall := hw.mul hin
  show ContDiffOn ℝ MA.sm (MA.ext _) Qs
  refine hall.congr fun x hx => ?_
  exact dif_pos hx

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

def sig (TT : ℝ) (ζ : ℂ) : ℂ := ((Real.sqrt (Complex.normSq ζ - TT) : ℝ) : ℂ)

def gg (TT : ℝ) (ζ : ℂ) : ℂ := ((Complex.normSq ζ - TT : ℝ) : ℂ)

def PS (TT : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ (m : ℕ) (p : MvPolynomial (Fin 3) ℂ), ∀ ζ : ℂ, TT < Complex.normSq ζ →
    gg TT ζ ^ m * f ζ = MvPolynomial.eval ![ζ, conj ζ, sig TT ζ] p

def PSV (TT : ℝ) {V : Type*} [AddCommGroup V] [Module ℂ V] (f : ℂ → V) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℂ → ℂ) (v : Fin n → V), (∀ i, PS TT (a i)) ∧
    ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = ∑ i, a i ζ • v i

def rot (θ : ℝ) (ζ : ℂ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I) * ζ

def PolynomialRadialAtSection : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def Transfer : Prop := SSn.Rep.ThtFacts → PolynomialRadialAtSection → PolyRadialS

def DatumConst : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ ζ ζ₁ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → Tz k r z * Tz k r z' < Complex.normSq ζ₁ →
      SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ = SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ₁ ∧
      SSn.nu0' k r z z' (TheSec.theSection k r z z') ζ = SSn.nu0' k r z z' (TheSec.theSection k r z z') ζ₁ ∧
      SSn.io0 k r z z' (TheSec.theSection k r z z') ζ = SSn.io0 k r z z' (TheSec.theSection k r z z') ζ₁

def KapLine : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∃ Qr : M.Ty P → (Wq →L[ℂ] Wq), Gauge.GC.KapPt P Bs d Qr ∧
      ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ ρ : M.Ty P,
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf.comp (Qr ρ)

def FibStable : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ ρ : M.Ty P,
      (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ ∧
      (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ

def AlgSS : Prop :=
  ∀ (P : M.Par) (𝒜 : Type) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜), d.Rel →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ Y : ℂ,
      d.κ (Pi.single ρ 1) * d.QQ Y 1 0 * d.κ (Pi.single π 1) = M.xEx P {l} π Y • (d.SS l * d.κ (Pi.single π 1))

def CorePoly : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (X₀ : Wq →L[ℂ] Wp),
      (∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = X₀) →
      ∀ c ∈ OmX P.r, ∀ Y : ℂ, PSV P.TT (fun ζ =>
        Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0 ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))

def PhaseInv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ θ : ℝ, ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))).comp (S (rot θ ζ) Xf) = c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) ∧
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ)) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ)) Xf) =
          c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def PhaseExtract : Prop :=
  ∀ (TT : ℝ) (f : ℂ → ℂ), 0 < TT → PS TT f → (∀ θ : ℝ, ∀ ζ : ℂ, TT < Complex.normSq ζ → f (rot θ ζ) = f ζ) →
    ∃ (m : ℕ) (q : Polynomial ℂ), ∀ ζ : ℂ, TT < Complex.normSq ζ → gg TT ζ ^ m * f ζ = q.eval (sig TT ζ)

def TWNe : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ ζ ∈ Gauge.GC.Ann P,
    ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf → Xf ≠ 0 →
      (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) ≠ 0

def PolynomialRadialAtSectionOfPhaseInvariance : Prop :=
  DatumConst → KapLine → FibStable → AlgSS → CorePoly → PhaseInv → PhaseExtract → TWNe → PolynomialRadialAtSection

def PolyRadialSOfCut : Prop :=
  SSn.Rep.ThtFacts → Transfer → DatumConst → KapLine → FibStable → AlgSS → CorePoly → PhaseInv → PhaseExtract → TWNe →
    PolyRadialS

theorem polynomialRadial_of_base (h0 : PolynomialRadialAtSectionOfPhaseInvariance) : PolyRadialSOfCut :=
  fun hT hTr hD hK hF hA hC hP hE hW => hTr hT (h0 hD hK hF hA hC hP hE hW)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem boundary_torus_adjoin : CutSH.BTlAdjoin := by
  intro Wp Wq _ _ _ _ _ _ k r z z' π π' X L hX S _ _ l w a b
  set Qa : Subalgebra ℂ (Module.End ℂ (RadSp k r z z' π π')) := Algebra.adjoin ℂ (Set.range (X.op l)) with hQa
  let good : Pr (RadSp k r z z' π π') → Prop := fun x => x.1 ∈ Qa ∧ x.2.unop ∈ Qa
  have hop : ∀ i, X.op l i ∈ Qa := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  have gmul : ∀ x y, good x → good y → good (x * y) := fun x y hx hy =>
    ⟨Subalgebra.mul_mem _ hx.1 hy.1, Subalgebra.mul_mem _ hy.2 hx.2⟩
  have gadd : ∀ x y, good x → good y → good (x + y) := fun x y hx hy =>
    ⟨Subalgebra.add_mem _ hx.1 hy.1, Subalgebra.add_mem _ hx.2 hy.2⟩
  have gneg : ∀ x, good x → good (-x) := fun x hx => ⟨Subalgebra.neg_mem _ hx.1, Subalgebra.neg_mem _ hx.2⟩
  have gzero : good 0 := ⟨Subalgebra.zero_mem _, Subalgebra.zero_mem _⟩
  have gone : good 1 := ⟨Subalgebra.one_mem _, Subalgebra.one_mem _⟩
  have gstar : ∀ x, good x → good (star x) := fun x hx => ⟨hx.2, hx.1⟩
  have galg : ∀ c : ℂ, good (algebraMap ℂ (Pr (RadSp k r z z' π π')) c) := fun c =>
    ⟨Subalgebra.algebraMap_mem _ c, Subalgebra.algebraMap_mem _ (starRingEnd ℂ c)⟩
  have gp : good (L.p l) := by
    rw [hX.1 l]
    exact ⟨hop 0, Subalgebra.neg_mem _ (hop 3)⟩
  have gc : good (L.c l) := by
    rw [hX.2.2.1 l]
    exact ⟨hop 1, hop 4⟩
  have gci : good (L.ci l) := by
    rw [hX.2.2.2.1 l]
    exact ⟨hop 2, hop 5⟩
  have hTs : ∀ (Y : ℂ) (i j : Fin 2), good ((Wd.Ts (site L l) Y) i j) := by
    intro Y i j
    fin_cases i <;> fin_cases j <;>
      simp only [Wd.Ts, site, Formalism.YangianSpanCharacter.T.Tm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
        Fin.zero_eta, Fin.mk_one]
    · exact gadd _ _ (galg Y) gp
    · exact gneg _ gc
    · exact gci
    · exact gzero
  have hmulA : ∀ M N : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')), (∀ a b, good (M a b)) → (∀ a b, good (N a b)) →
      ∀ a b, good ((M * N) a b) := by
    intro M N hM hN a b
    rw [Matrix.mul_apply]
    refine Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun c _ => ?_)
    exact gmul _ _ (hM a c) (hN c b)
  have hsumA : ∀ (ι : Type) (t : Finset ι) (f : ι → Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))),
      (∀ i, ∀ a b, good (f i a b)) → ∀ a b, good ((∑ i ∈ t, f i) a b) := by
    intro ι t f hf a b
    rw [Matrix.sum_apply]
    exact Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun i _ => hf i a b)
  have heU : ∀ (x : S) (i j : Fin 2), ∀ a b, good ((Wd.eU (A := Pr (RadSp k r z z' π π')) x i j : Wd.SlopeTestRemainingChoices S _) a b) := by
    intro x i j a b
    unfold Wd.eU
    simp only [Matrix.of_apply]
    split_ifs
    · exact gone
    · exact gzero
  have hio : ∀ y, good y → ∀ a b, good ((Wd.io (S := S) y) a b) := by
    intro y hy a b
    unfold Wd.io
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hy
    · exact gzero
  have hvlet : ∀ lt : Wd.Letter ℂ S, ∀ a b, good ((Wd.vlet (site L l) lt) a b) := by
    intro lt
    unfold Wd.vlet Wd.ins
    refine hsumA _ _ _ (fun i => ?_)
    refine hsumA _ _ _ (fun j => ?_)
    refine hmulA _ _ (heU _ i j) ?_
    intro a b
    unfold Wd.lift0
    rw [Matrix.map_apply]
    refine hio _ ?_ a b
    split_ifs
    · exact hTs _ i j
    · rw [Matrix.map_apply]
      exact gstar _ (hTs _ i j)
  have hbT : ∀ w' : List (Wd.Letter ℂ S), ∀ a b, good ((Wd.bT (site L l) w') a b) := by
    intro w'
    induction w' with
    | nil =>
      intro a b
      simp only [Wd.bT]
      rw [Matrix.one_apply]
      split_ifs
      · exact gone
      · exact gzero
    | cons lt w' ih =>
      intro a b
      simp only [Wd.bT]
      exact hmulA _ _ (hvlet lt) ih a b
  exact (hbT w a b).1

end Formalism.FourierDecayAlt.P
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

def DTExists : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ ∧
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ ∧
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂

def DTStab : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ →
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ →
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂ →
      ∀ p ∈ NF.Stab k r z z' μsec ζ₂, (h⁻¹ * p.1 * h, h'⁻¹ * p.2 * h') ∈ NF.Stab k r z z' μsec ζ₁

theorem datumTransit_of_cut (hE : DTExists) (hS : DTStab) : DatumTransit := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  obtain ⟨h, hh, h', hh', e1, e2, e3⟩ := hE k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  exact ⟨h, hh, h', hh', e1, e2, e3, hS k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂ h hh h' hh' e1 e2 e3⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def RightRuleE : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z' → IsOpen D → Q.SmoothLev k r 0 D f →
    Q.RightEq k r z' 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ a b : Fin r, a.val < b.val →
      Q.EH k r (eI k r a) (eI k r b) f g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • f g

def LeftRuleCell : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z → IsOpen D →
    (∀ g ∈ Q.Glev k r 0 ∩ D, ∀ n ∈ Q.Nlev k r 0, n * g ∈ D) → Q.SmoothLev k r 0 D f → Q.LeftEq k r z 0 D f →
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D → ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (eI k r a) (eI k r b) f (Q.wCell k r (Fin.last r) c * g) =
        (if a.val = b.val + 1 then c a / c b else 0) • f (Q.wCell k r (Fin.last r) c * g)

def TorusCell : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r 0 D f → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
    Q.wCell k r (Fin.last r) c * g ∈ D → ∀ l : Fin r,
      Q.EH k r (eI k r l) (eI k r l) f (Q.wCell k r (Fin.last r) c * g) =
        pOp l (fun c' => f (Q.wCell k r (Fin.last r) c' * g)) c

def GaugeP : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) (n : Fin r → ℕ) (H : (Fin r → ℂ) → E)
    (c : Fin r → ℂ), c ∈ OmX r → DifferentiableAt ℝ H c → ∀ l : Fin r,
      pOp l (fun c' => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') c =
        ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) • (pOp l H c + ((n l : ℂ) / 2) • H c)

def MinorCellOfParts : Prop := RightRuleE → LeftRuleCell → TorusCell → GaugeP → MinorCell

end Formalism.FourierDecayAlt.P.PBN
end
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

theorem haar_open_pos {k r : ℕ} {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) {O : Set (Mt k r)}
    (hO : IsOpen O) {g₀ : Mt k r} (hg₀ : Matrix.of g₀ ∈ B.GV k r) (hg₀O : g₀ ∈ O) : μ O ≠ 0 := by
  intro h0
  have hnull : ∀ b ∈ B.GV k r, μ (lmulM (k := k) (r := r) b ⁻¹' O) = 0 := by
    intro b hb
    have hm : Measurable (lmulM (k := k) (r := r) b) := (BesselUnitaryEquiv.continuous_lmulM b).measurable
    rw [← Measure.map_apply hm hO.measurableSet, hμ.left b hb, h0]
  let U : {b : B.Mat k r // b ∈ B.GV k r} → Set (Mt k r) := fun b => lmulM (k := k) (r := r) b.1 ⁻¹' O
  have hUo : ∀ i, IsOpen (U i) := fun i => hO.preimage (BesselUnitaryEquiv.continuous_lmulM i.1)
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have hcov : {x : Mt k r | Matrix.of x ∈ B.GV k r} ⊆ ⋃ i, U i := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨Matrix.of g₀ * (Matrix.of x)⁻¹,
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hg₀ (Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem hx)⟩, ?_⟩
    have hx' : Matrix.of x ∈ B.GV k r := hx
    have e : lmulM (k := k) (r := r) (Matrix.of g₀ * (Matrix.of x)⁻¹) x = g₀ := by
      unfold lmulM
      rw [mul_assoc, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hx').2, mul_one]
      rfl
    show lmulM (k := k) (r := r) (Matrix.of g₀ * (Matrix.of x)⁻¹) x ∈ O
    rw [e]
    exact hg₀O
  have hGV0 : μ {x : Mt k r | Matrix.of x ∈ B.GV k r} = 0 := by
    refine measure_mono_null (hcov.trans hT.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun i _ => hnull i.1 i.2
  have hsub : (Set.univ : Set (Mt k r)) ⊆ {x : Mt k r | Matrix.of x ∈ B.GV k r} ∪ (B.GV k r)ᶜ := by
    intro x _
    by_cases hx : Matrix.of x ∈ B.GV k r
    · exact Or.inl hx
    · exact Or.inr hx
  have huniv : μ Set.univ = 0 := measure_mono_null hsub (measure_union_null hGV0 hμ.conc)
  exact hμ.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

end Formalism.FourierDecayAlt.P.CutMP.ER
end
