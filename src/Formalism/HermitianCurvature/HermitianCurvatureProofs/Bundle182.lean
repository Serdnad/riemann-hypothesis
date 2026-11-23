module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelPointEntryContDiffOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle155
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnlyOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle158
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle151
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle067
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle133
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle171
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.HermitianCurvature.Bundle005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

namespace SSPw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def conjL (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun X := A.comp (X.comp B)
  map_add' X Y := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c X := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

def sumL {ι : Type} [Fintype ι] (f : ι → (Wq →L[ℂ] Wp)) (V : ι → (Wq →L[ℂ] Wp)) :
    (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ ρ, (((innerₛₗ ℂ (B.hsVec (f ρ))).comp Formalism.FourierDecayAlt.P.JFxI.hsVecL).smulRight (V ρ))

theorem sumL_apply {ι : Type} [Fintype ι] (f : ι → (Wq →L[ℂ] Wp)) (V : ι → (Wq →L[ℂ] Wp)) (Y : Wq →L[ℂ] Wp) :
    sumL f V Y = ∑ ρ, inner ℂ (B.hsVec (f ρ)) (B.hsVec Y) • V ρ := by
  unfold sumL
  rw [LinearMap.sum_apply]
  rfl

end SSPw

open SSPw in
theorem second_shift_pointwise_holds : SSn.Rep.Core.SSPointwise := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := hA
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl

  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set μ0 := TheSec.theSection P.k P.r Bs.z Bs.z' with hμ0
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hcs0.1 }
  have hyp0 : Gauge.GC.GTHyp P Bs0 X d := ⟨hpl, hk, hcs0, hL, hS, hRel, hQQ⟩
  obtain ⟨e0, he0, -⟩ := Gauge.GC.gauge_kappa_holds Wp Wq P Bs0 X d hyp0

  have hRT := Gauge.GC.radial_torus_local_holds Wp Wq P Bs0 hpl hk hcs0 X
  have hSl : ∀ (Y : ℂ) (a b : Fin 2), Gauge.GC.SliceLoc P Bs0 (X.t Y a b) := fun Y a b =>
    Gauge.GC.second_shift_slice_derivative Wp Wq P Bs0 hpl _ (hRT Y a b)
  have hSL := (Gauge.GC.second_shift_slice_operator Wp Wq P Bs0 X d hyp0 hSl l hl).1

  have hC : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute (d.SS l).1 W := by
    intro f hf W hW
    obtain ⟨W₁, hW₁⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZ f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZ_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    obtain ⟨W₂, hW₂⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZb f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZb_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    exact ((Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X d hL hS hRel hQQ f hf W W₁ W₂
      hW hW₁ hW₂).2.1 l hl).1

  have hRB0 : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := Gauge.GC.radBase_of P Bs0 hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he0.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB0 _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs0.μsec ζ) = e0 ρ ζ := by
    intro ρ c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have h := congrFun (hΨr ρ) (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h

  have hdec : ∀ ζ : ℂ, ∃ hh : Q.Mx P.k P.r × Q.Mx P.k P.r, ζ ∈ Gauge.GC.Ann P →
      hh.1 ∈ UWset P.k P.r Bs.z ∧ hh.2 ∈ UWset P.k P.r Bs.z' ∧
        NF.muZ P.k P.r Bs.μsec ζ = hh.1 * NF.muZ P.k P.r μ0 ζ * hh.2 := by
    intro ζ
    by_cases hζ : ζ ∈ Gauge.GC.Ann P
    · have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
      have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
      obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hcs0.1
        hdom.2.1 hdom.2.2
      rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hq.2] at he
      exact ⟨(h, h'), fun _ => ⟨hh, hh', he⟩⟩
    · exact ⟨(1, 1), fun h => absurd h hζ⟩
  choose H hH using hdec
  let V : M.Ty P → ℂ → (Wq →L[ℂ] Wp) := fun ρ ζ =>
    ((d.SS l).1 (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r μ0 ζ)
  refine ⟨fun ζ => LinearMap.toContinuousLinearMap
    ((conjL (Bs.π (H ζ).1) (Bs.π' (H ζ).2)) ∘ₗ sumL (fun ρ => e0 ρ ζ) (fun ρ => V ρ ζ) ∘ₗ
      conjL (Bs.π (H ζ).1⁻¹) (Bs.π' (H ζ).2⁻¹)), ?_⟩
  intro Φ c hc ζ hζ
  obtain ⟨hh, hh', hd⟩ := hH ζ hζ
  set h := (H ζ).1
  set h' := (H ζ).2
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hdom0 := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs0.1 hq
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'

  have hback : NF.muZ P.k P.r μ0 ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
    rw [hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
      Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
  have hΦ0 : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r μ0 ζ) =
      (Bs.π h⁻¹).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)) := by
    rw [hback]
    exact Φ.2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) hdom h⁻¹ hhi h'⁻¹ hhi'

  have hfwd : (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r Bs.μsec ζ) =
      (Bs.π h).comp (((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r μ0 ζ)).comp (Bs.π' h')) := by
    rw [hd]
    exact ((d.SS l).1 Φ).2.2.2 (c, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh'
  have hkey := Gauge.GC.key_slice P Bs0 hpl hk e0 he0 Ψ hΨ (d.SS l).1 hSL hC Φ hc hc0 hζ
  rw [hfwd]
  change _ = (Bs.π h).comp ((sumL (fun ρ => e0 ρ ζ) (fun ρ => V ρ ζ)
    ((Bs.π h⁻¹).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)))).comp
      (Bs.π' h'))
  rw [← hΦ0, sumL_apply]
  congr 2

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

namespace Formalism.FourierDecayAlt.P

theorem z_only_of_levi_curve (hC : WirtingerOperators.CurveLevi) (hH : WirtingerOperators.HpartLevi) : LevelPointCoordinates.ZOnly :=
  WirtingerOperators.zOnly_of_parts hC hH xi_coefficient xi_coefficient_vector xiMem_statement xi_smooth
    right_derivative_operator_class wirtinger_slice_smooth

end Formalism.FourierDecayAlt.P
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def capA (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X := C3.AAop k r r le_rfl (Q.uC k r 0 y) F

def capAv (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  C3.AAvop k r r le_rfl (y - ((2 * r + k : ℕ) : ℂ) / 2) F

def capBeta (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a))))

def capAlphaV (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l))

end defs

def JDACapRep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (y : ℂ),
    ∃ Θ Θv : B.DiffOp k r Wp Wq,
      PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θ ∧ PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θv ∧
      B.opOrder Θ = r ∧ B.opOrder Θv = r ∧
      (∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θ : ℕ∞) {g} F →
        B.opApply Θ F g = capA k r y F g) ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θv : ℕ∞) {g} F →
        B.opApply Θv F g = capAv k r y F g

def JDACapInv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ (y : ℂ) (Θ : B.DiffOp P.k P.r Wp Wq), P.r ≤ B.opOrder Θ →
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capA P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) ∧
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capAv P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ)

def JDACapToda : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capA P.k P.r y J) c g =
          dMul (drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

def JDACapTodaV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
          dMul (drbF P.r) (Q.crd (Q.cmp (vABm P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem capa_J_ck (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r)
    {g : Q.Mx P.k P.r} (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) (m : ℕ∞) :
    Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r ∧ B.CkOn m {Q.wCell P.k P.r (Fin.last P.r) c * g} J := by
  have hGV : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hg
  refine ⟨hGV, fun g₀ hg₀ => ?_⟩
  rw [Set.mem_singleton_iff] at hg₀
  subst hg₀
  have hG0 : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
    ⟨hGV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  obtain ⟨U, F, hU, hmem, hF, hJF⟩ := hJ.1 _ ⟨hG0, hcg⟩
  refine ⟨U, F, hU, hmem, hF.of_le ?_, fun x hx hxG => hJF x hx ⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩
  exact_mod_cast le_top

end assembly

theorem jDAGrp_of_parts (hR : JDACapRep) (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDAGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨Θ, Θv, hP, hPv, hO, hOv, hA, hAv⟩ := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) y
  refine ⟨Θ, Θv, hP, hPv, (hI _ _ (D.parOf S v) (T v).base hpl hk y Θ hO.ge).1 hA,
    (hI _ _ (D.parOf S v) (T v).base hpl hk y Θv hOv.ge).2 hAv, fun J hJ c hc g hg hcg => ⟨?_, ?_⟩⟩
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θ)
    rw [← hT _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hA J _ hGV hCk]
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θv)
    rw [← hTv _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hAv J _ hGV hCk]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

theorem averaging_invariance_holds : ACInv := by
  intro k r Wp Wq _ _ _ _ D φ₀ _hφ p₀ hp₀ g
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨h1, h2, h3, h4⟩ := hp₀
  let F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun x => ((φ₀ x : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)
  let π1 : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun _ => 1
  have hpsi : ∀ (w : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r), psi k r w 0 y = 1 := by
    intro w y; simp [psi]
  have hJ : ∀ x : B.Mat k r, besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F x =
      ((∫ p, φ₀ (B.sgs p x) ∂D.μSS : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
    intro x
    unfold besselJ
    simp only [hpsi, star_one, mul_one, one_smul, π1, F]
    rw [← integral_complex_ofReal, ← integral_smul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ext
    simp [B.sgs]
  have hrep : ∀ U : Set (B.Mat k r), IsCRepOn U π1 := fun U => ⟨rfl, fun _ _ _ _ => by ext; simp [π1]⟩
  have hN := bessel_unipotent_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    (fun n₀ h => D.haarN.left n₀ h)
  have hU := bessel_unitary_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) (hrep _) (hrep _)
  have hs : B.sgs p₀ g = (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ *
      ((Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r)) * (Matrix.of p₀.2.1 : B.Mat k r) := by
    show (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ * (Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r) *
      (Matrix.of p₀.2.1 : B.Mat k r) = _
    simp only [Matrix.mul_assoc]
  have key : besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F (B.sgs p₀ g) =
      besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F g := by
    rw [hs, hU _ _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3, hN _ _ (WeylGroupFacts.mem_n_inv h2) _ h4]
    ext
    simp [π1, hpsi]
  rw [hJ, hJ] at key
  have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) key
  simp at this
  exact_mod_cast this

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

variable {k r : ℕ}

theorem haar_pos_nhds_one {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ)
    (hinv : ∀ u ∈ U, u⁻¹ ∈ U) (hunit : ∀ u ∈ U, IsUnit u.det) {V : Set (Mt k r)} (hV : IsOpen V)
    (h1 : ((1 : B.Mat k r) : Mt k r) ∈ V) : 0 < μ V := by
  rw [pos_iff_ne_zero]
  intro h0
  let W : B.Mat k r → Set (Mt k r) := fun u => lmulM u⁻¹ ⁻¹' V
  have hWo : ∀ u ∈ U, IsOpen (W u) := fun u _ => hV.preimage (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont _)
  have hW0 : ∀ u ∈ U, μ (W u) = 0 := by
    intro u hu
    have e := h.left u⁻¹ (hinv u hu)
    have := Measure.map_apply (μ := μ) (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) u⁻¹).measurable hV.measurableSet
    rw [e] at this
    show μ (lmulM u⁻¹ ⁻¹' V) = 0
    rw [← this]; exact h0
  have hcov : (U : Set (Mt k r)) ⊆ ⋃ u ∈ U, W u := by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
    have e : (lmulM x⁻¹ x : Mt k r) = ((1 : B.Mat k r) : Mt k r) := by
      show x⁻¹ * x = 1
      exact Matrix.nonsing_inv_mul x (hunit x hx)
    show lmulM x⁻¹ x ∈ V
    rw [e]; exact h1
  obtain ⟨T, hTU, hTc, hTeq⟩ := TopologicalSpace.isOpen_biUnion_countable U W hWo
  have hU0 : μ (U : Set (Mt k r)) = 0 := by
    refine measure_mono_null (hcov.trans hTeq.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun u hu => hW0 u (hTU hu)
  have huniv : μ Set.univ = 0 := by
    refine measure_mono_null ?_ (measure_union_null hU0 h.conc)
    intro x _
    by_cases hx : x ∈ (U : Set (Mt k r))
    · exact Or.inl hx
    · exact Or.inr hx
  exact h.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

theorem averaging_haar_positivity : ACHaarPos := by
  intro k r Wp Wq _ _ _ _ D O hO h1
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨A, B', hA, hB, hoA, hoB, hAB⟩ := isOpen_prod_iff.1 hO oneP.1 oneP.2 h1
  obtain ⟨V1, V2, hV1, hV2, ho1, ho2, h12⟩ := isOpen_prod_iff.1 hA oneP.1.1 oneP.1.2 hoA
  obtain ⟨V3, V4, hV3, hV4, ho3, ho4, h34⟩ := isOpen_prod_iff.1 hB oneP.2.1 oneP.2.2 hoB
  have hsub : (V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4) ⊆ O :=
    (Set.prod_mono h12 h34).trans hAB
  have uwI : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, u⁻¹ ∈ UWset k r w :=
    fun w u hu => Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hu
  have uwU : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, IsUnit u.det :=
    fun w u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have nI : ∀ u ∈ Nset k r, u⁻¹ ∈ Nset k r := fun u hu => WeylGroupFacts.mem_n_inv hu
  have nU : ∀ u ∈ Nset k r, IsUnit u.det := fun u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have p1 := haar_pos_nhds_one D.haarW (uwI _) (uwU _) hV1 ho1
  have p2 := haar_pos_nhds_one D.haarN nI nU hV2 ho2
  have p3 := haar_pos_nhds_one D.haarW' (uwI _) (uwU _) hV3 ho3
  have p4 := haar_pos_nhds_one D.haarN nI nU hV4 ho4
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  show 0 < ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) ((V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4))
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  rw [pos_iff_ne_zero] at p1 p2 p3 p4 ⊢
  exact mul_ne_zero (mul_ne_zero p1 p2) (mul_ne_zero p3 p4)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDecayTrQQ_of_open (h2 : JDHatOpQQ) : JDecayTrQQ := jDecayTrQQd_of_open h2

end Formalism.FourierDecayAlt.P.CutMP
end
