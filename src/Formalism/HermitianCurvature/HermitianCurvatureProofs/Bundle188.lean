module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle183
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle166
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle186
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVstep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle150
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle180
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle181
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamJFDeriv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle174
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEig
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem En.bessel_folding_at_built_place : En.BesselFoldBuilt := En.besselFoldBuilt_of En.coefficient_vector_in_L2_class

theorem energyTr_of_betaFrame (h : En.BetaFrame) : EnergyTr :=
  En.energyTr_of_parts En.folding_reversal_holds En.admissible_length_holds En.bessel_folding_at_built_place En.L2_bound_at_built_place_holds h

theorem energy_trace_identity_holds : EnergyTr := energyTr_of_betaFrame En.beta_frame_identity_holds

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem vIsoCpt_main : Formalism.FourierDecayAlt.KB.VIsoCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' hx hx'

  obtain ⟨ε, hε, hεall⟩ := Formalism.FourierDecayAlt.P.JCx2.exists_common_eps
    (fun (i : Bool × Wd.Ix (Fin w.length)) ε => JC.NiceCoef (p.T.bs j) ε (if i.1 then x i.2 else x' i.2))
    (fun i ε ε' _ h hF => nice_mono h hF)
    (fun i => by
      rcases i with ⟨b, e⟩
      cases b
      · exact Formalism.FourierDecayAlt.P.TLB.nice_of_cpt (hx' e)
      · exact Formalism.FourierDecayAlt.P.TLB.nice_of_cpt (hx e))
  have hxN : ∀ e, JC.NiceCoef (p.T.bs j) ε (x e) := fun e => by simpa using hεall (true, e)
  have hx'N : ∀ e, JC.NiceCoef (p.T.bs j) ε (x' e) := fun e => by simpa using hεall (false, e)
  obtain ⟨R, hR⟩ := common_R (fun i : Bool × Wd.Ix (Fin w.length) => if i.1 then x i.2 else x' i.2)
    (fun i => by
      rcases i with ⟨b, e⟩
      cases b
      · exact (hx' e).2.1
      · exact (hx e).2.1)
  have hxR : ∀ e, ∀ g ∈ B.GV P.k (P.r - j), x e g ≠ 0 → B.gN g ≤ R := fun e => by simpa using hR (true, e)
  have hx'R : ∀ e, ∀ g ∈ B.GV P.k (P.r - j), x' e g ≠ 0 → B.gN g ≤ R := fun e => by simpa using hR (false, e)
  have hwN := waveG_nice (p.T.bs j) ε s w x hxN
  refine ⟨fun e => ⟨(hwN e).1, ⟨R, waveG_bs (p.T.bs j) s w x R hxR e⟩, ε, hε, (hwN e).2.2⟩, ?_⟩
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  obtain ⟨K, hThm, -, -, hJc⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hJ : ∀ (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), JC.NiceCoef (p.T.bs jF) ε F →
      (∃ R : ℝ, ∀ g ∈ B.GV P.k (P.r - j), F g ≠ 0 → B.gN g ≤ R) →
      ∃ Φ ∈ K 0, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Φ : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) F) y.1 y.2 := by
    rintro F hF ⟨R', hR'⟩
    exact Formalism.FourierDecayAlt.P.PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJc hε hF hR'
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2
  choose Φ hΦK hΦ using fun a => hJ (x a) (hxN a) ⟨R, hxR a⟩
  choose Φ' hΦ'K hΦ' using fun a => hJ (x' a) (hx'N a) ⟨R, hx'R a⟩
  have hnx := waveG_nice (p.T.bs j) ε s w x hxN
  have hnx' := waveG_nice (p.T.bs j) ε s w x' hx'N
  show D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') =
    D.formLev p.T (M.sgn P p.l0) jF w x x'
  have hmem : ∀ (Wv Wv' : Module.End ℂ (RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z'
      (p.T.bs jF).π (p.T.bs jF).π')) (Ψ' : Ix (Fin w.length) → RadSp (JC.parLev P jF).k (JC.parLev P jF).r
      (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'),
      (∀ e, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Ψ' e : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) (KB.waveG (p.T.bs j) s w x' e))
            y.1 y.2) → InK (K 0) Ψ' := by
    intro _ _ Ψ' hΨ' e
    obtain ⟨Ψ0, hΨ0K, hΨ0⟩ := hJ (KB.waveG (p.T.bs j) s w x' e) (hnx' e) ⟨R, waveG_bs (p.T.bs j) s w x' R hx'R e⟩
    have : Ψ' e = Ψ0 := radSp_ext (fun y hy => (hΨ' e y hy).trans (hΨ0 y hy).symm)
    rw [this]
    exact hΨ0K
  by_cases hr : 0 < P.r - j
  · obtain ⟨Wv, hW⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ s
    obtain ⟨Wv', hW'⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hxN Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx'N Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hxN hx'N hΦ hΦ']
    congr 1
    have key := rr_wave_A (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))
  · have hr0 : P.r - j = 0 := by omega
    obtain ⟨Wv, hW⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s
    obtain ⟨Wv', hW'⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (_ : Fin (P.r - j) → ℂ) (g : Mx P.k (P.r - j)) => fsv s (P5.zeta P.k (P.r - j) (p.T.bs jF).z
          (p.T.bs jF).z' g)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_top_eq_zeta hr0]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hxN Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx'N Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hxN hx'N hΦ hΦ']
    congr 1
    have key := rr_wave_B (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr0 s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))

end Formalism.FourierDecayAlt.P.PBFV

namespace Formalism.FourierDecayAlt.P

theorem vector_isomorphism_compact_support : Formalism.FourierDecayAlt.KB.VIsoCpt := Formalism.FourierDecayAlt.P.PBFV.vIsoCpt_main

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section kb

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def OmKB (p : KB.Pl P Wp Wq) : Set (B.Mat P.k P.r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g ∧
    ∀ a : Fin P.r, Formalism.QuantumDeterminants.Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def FFKB (p : KB.Pl P Wp Wq) : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :=
  Q.FFl P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' 0 (OmKB p)

def IsGaugeQQKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
    CutMP.Gauge.FamR P p.T.base Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (CutMP.Gauge.rawR P p.T.base.μsec e
          (Q.QL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b)
          (fun ρ' => MA.toSm P (CutMP.Gauge.rawR P p.T.base.μsec e Φ ρ')) ρ

end kb

def NFHatProdKBS : Prop :=
  ∃ C₁ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
    IsFrameKB p e → IsGaugeQQKB p e → MA.IsModelLevel P (MA.DQ P) L → ∀ (N : ℕ) (u : List (MA.A P (MA.DQ P))),
      u.length ≤ N → (∀ a ∈ u, a ∈ MA.hatSet P L) →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (Th : Fin m → B.DiffOp P.k P.r Wp Wq),
        (∀ k, b k ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ k, NFOpOK C₁ p N (Th k)) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          B.JF p.T.base F ∈ FFKB p →
          MA.actA P u.prod (trJKB p e (B.JF p.T.base F)) =
            ∑ k, MA.actA P (b k) (trJKB p e (B.JF p.T.base (B.opApply (Th k) F)))

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open scoped ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section opc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem opc_cc_zero (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc (P := P) j hj t c ⟨0, by omega⟩ = t := by
  unfold cc consC
  simp

theorem opc_cc_line (j : ℕ) (hj : j + 1 ≤ P.r) (t v : ℂ) (s : ℝ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc (P := P) j hj (t + (s : ℂ) * v) c =
      cc (P := P) j hj t c + s • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ) := by
  funext l
  unfold cc consC
  by_cases hl : (l : ℕ) = 0
  · have e : l = ⟨0, by omega⟩ := Fin.ext hl
    simp [hl, Pi.single_apply, e, Complex.real_smul]
  · have hne : l ≠ ⟨0, by omega⟩ := fun h => hl (by rw [h])
    simp [hl, Pi.single_apply, hne]

theorem opc_mul (h2 : FamAlg) (h4 : RepLin) {T : D.LevTower P.k P.r Wp Wq}
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) {j : ℕ} {hj : j + 1 ≤ P.r}
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)} (hG : GoodFam T j G) (hR : Rep T j hj Ψ G)
    (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {t | t ≠ 0})
    (hv : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (Ψ' : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
        m t • (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2)) :
    InC T j hj Ψ' := by
  refine ⟨fun t γ => m t • G t γ, (h2 Wp Wq P T j G G hG hG m hm).2, fun t ht x hx => ?_⟩
  rw [hv t ht x hx, hR t ht x hx]
  exact (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht (m t) x hx).2.symm

theorem opc_two (h2 : FamAlg) (h3 : FamDeriv) (h4 : RepLin) {T : D.LevTower P.k P.r Wp Wq}
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) {j : ℕ} {hj : j + 1 ≤ P.r}
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)} (hG : GoodFam T j G)
    (m1 m2 : ℂ → ℂ) (hm1 : ContDiffOn ℝ ∞ m1 {t | t ≠ 0}) (hm2 : ContDiffOn ℝ ∞ m2 {t | t ≠ 0}) (v1 v2 : ℂ)
    (hv : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (Ψ' : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
        m1 t • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v1 t)) x.1 x.2 +
        m2 t • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v2 t)) x.1 x.2) :
    InC T j hj Ψ' := by
  have hd1 := h3 Wp Wq P T j G hG v1
  have hd2 := h3 Wp Wq P T j G hG v2
  have hA : GoodFam T j (fun t γ => m1 t • famP j G v1 t γ) := (h2 Wp Wq P T j _ _ hd1 hd1 m1 hm1).2
  have hB : GoodFam T j (fun t γ => m2 t • famP j G v2 t γ) := (h2 Wp Wq P T j _ _ hd2 hd2 m2 hm2).2
  refine ⟨fun t γ => m1 t • famP j G v1 t γ + m2 t • famP j G v2 t γ,
    (h2 Wp Wq P T j _ _ hA hB (fun _ => 1) contDiffOn_const).1, fun t ht x hx => ?_⟩
  have e0 := (h4 Wp Wq P T hP hT j hj hPs _ _ hA hB t ht 0 x hx).1
  have e1 := (h4 Wp Wq P T hP hT j hj hPs _ _ hd1 hd1 t ht (m1 t) x hx).2
  have e2 := (h4 Wp Wq P T hP hT j hj hPs _ _ hd2 hd2 t ht (m2 t) x hx).2
  rw [hv t ht x hx, ← e1, ← e2]
  exact e0.symm

theorem opc_fderiv (h5 : FamJFDeriv) (h6 : CellTie) (T : D.LevTower P.k P.r Wp Wq)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) (j : ℕ) (hj : j + 1 ≤ P.r)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (hG : GoodFam T j G) (hR : Rep T j hj Ψ G)
    (t : ℂ) (ht : t ≠ 0) (x : (Fin (P.r - (j + 1)) → ℂ) × Mx P.k (P.r - (j + 1)))
    (hx : x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z') (v : ℂ) :
    fderiv ℝ (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) (cc j hj t x.1)
        (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2 := by
  have hy := (h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx).1
  obtain ⟨-, hs, -⟩ := Ψ.2
  obtain ⟨U, F, hU, hyU, hF, hΨF⟩ := hs _ hy
  have hg : gi j hj x.2 ∈ Glev P.k (P.r - j) (Fin.last _) := hy.2.1
  have hemb : Continuous fun c' : Fin (P.r - j) → ℂ => (c', gi j hj x.2) :=
    continuous_id.prodMk continuous_const
  have hev : (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) =ᶠ[𝓝 (cc j hj t x.1)]
      fun c' => F (c', gi j hj x.2) := by
    have hU' : ∀ᶠ c' in 𝓝 (cc j hj t x.1), (c', gi j hj x.2) ∈ U :=
      hemb.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
    filter_upwards [hU'] with c' hc'
    exact hΨF (c', gi j hj x.2) hc' hg
  have hFd : DifferentiableAt ℝ (fun c' => F (c', gi j hj x.2)) (cc j hj t x.1) :=
    ((hF.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).comp (cc j hj t x.1)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  have hφ := (hFd.congr_of_eventuallyEq hev).hasFDerivAt
  have hφ' : HasFDerivAt (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (fderiv ℝ (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) (cc j hj t x.1))
      (cc j hj t x.1 + (0 : ℝ) • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ)) := by
    rw [zero_smul, add_zero]; exact hφ
  have hline := ((hasDerivAt_id (0 : ℝ)).smul_const
    (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ)).const_add (cc j hj t x.1)
  rw [one_smul] at hline
  have hcomp := hφ'.comp_hasDerivAt (0 : ℝ) hline
  have hJ := h5 Wp Wq P T hP hT j hj hPs G hG t ht x hx v
  have hc : Continuous fun s : ℝ => t + (s : ℂ) * v :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hne : ∀ᶠ s : ℝ in 𝓝 0, t + (s : ℂ) * v ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using ht)
  have heq : ((fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) ∘
      fun s : ℝ => cc j hj t x.1 + id s • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ))
      =ᶠ[𝓝 0] fun s : ℝ =>
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2 := by
    filter_upwards [hne] with s hs
    simp only [Function.comp, id]
    rw [← opc_cc_line]
    exact hR _ hs x hx
  exact hcomp.unique (hJ.congr_of_eventuallyEq heq)

end opc

theorem cutSH_opClosed_of (h2 : FamAlg) (h3 : FamDeriv) (h4 : RepLin) (h5 : FamJFDeriv) (h6 : CellTie) :
    OpClosed := by
  intro Wp Wq _ _ _ _ _ _ P T hP hT j hj hPj hPs X i Ψ hΨ
  obtain ⟨G, hG, hR⟩ := hΨ
  have hom : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      cc j hj t x.1 ∈ OmX (P.r - j) := fun t ht x hx => (h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx).1.1
  have hD := fun v t ht x hx => opc_fderiv h5 h6 T hP hT j hj hPj hPs Ψ G hG hR t ht x hx v
  have hid : ContDiff ℝ ∞ (fun t : ℂ => t) := contDiff_id
  have hst : ContDiff ℝ ∞ (fun t : ℂ => star t) := Complex.conjCLE.contDiff
  fin_cases i
  · refine opc_two h2 h3 h4 hP hT hPs hG (fun t => t / 2) (fun t => -(t * Complex.I / 2))
      (hid.div_const 2).contDiffOn ((hid.mul contDiff_const).div_const 2).neg.contDiffOn 1 Complex.I
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change pOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold pOp
    rw [if_pos (hom t ht x hx), opc_cc_zero]
    unfold wirt
    rw [hD 1 t ht x hx, hD Complex.I t ht x hx]
    module
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => t) hid.contDiffOn (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cOp
    rw [opc_cc_zero]
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => t⁻¹) (hid.contDiffOn.inv fun t ht => ht)
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change ciOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold ciOp
    rw [opc_cc_zero]
  · refine opc_two h2 h3 h4 hP hT hPs hG (fun t => star t / 2) (fun t => star t * Complex.I / 2)
      (hst.div_const 2).contDiffOn ((hst.mul contDiff_const).div_const 2).contDiffOn 1 Complex.I
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change pbOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold pbOp
    rw [if_pos (hom t ht x hx), opc_cc_zero]
    unfold wirtBar
    rw [hD 1 t ht x hx, hD Complex.I t ht x hx]
    module
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => star t) hst.contDiffOn (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cbOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cbOp
    rw [opc_cc_zero]
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => (star t)⁻¹)
      (hst.contDiffOn.inv fun t ht => star_ne_zero.mpr ht) (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cbiOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cbiOp
    rw [opc_cc_zero]

end Formalism.FourierDecayAlt.P.CutSH

theorem Formalism.FourierDecayAlt.P.cutSH_opClosed_of (h2 : Formalism.FourierDecayAlt.P.CutSH.FamAlg) (h3 : Formalism.FourierDecayAlt.P.CutSH.FamDeriv)
    (h4 : Formalism.FourierDecayAlt.P.CutSH.RepLin) (h5 : Formalism.FourierDecayAlt.P.CutSH.FamJFDeriv) (h6 : Formalism.FourierDecayAlt.P.CutSH.CellTie) :
    Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.CutSH.cutSH_opClosed_of h2 h3 h4 h5 h6

theorem Formalism.FourierDecayAlt.P.cutSH_opClosed_of_famJFDeriv (h5 : Formalism.FourierDecayAlt.P.CutSH.FamJFDeriv) : Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.CutSH.cutSH_opClosed_of Formalism.FourierDecayAlt.P.CutSH.family_algebraic Formalism.FourierDecayAlt.P.family_derivative
    Formalism.FourierDecayAlt.P.CutSH.representation_linear h5 Formalism.FourierDecayAlt.P.CutSH.cell_compatibility

theorem Formalism.FourierDecayAlt.P.operator_class_closed : Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.cutSH_opClosed_of_famJFDeriv Formalism.FourierDecayAlt.P.family_orbital_derivative_identity
end
end

section

namespace Formalism.FourierDecayAlt.P

theorem z_only : LevelPointCoordinates.ZOnly :=
  z_only_of_levi_curve levi_curve hermitian_part_levi

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem elliptic_regularity_weighted : EllRegW := elliptic_regularity_transfer_holds ZetaZeros.D.EllReg.elliptic_regularity_of_parts

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem inverse_alpha_positive_holds : RInvAlphaP := by
  intro k r z' w m hz' hw hm M _ _ X
  exact InvEig.usage₅ hz' ((m * w)⁻¹) (InvEigA.inverse_product_block_zero hw hm) (InvEigA.det_inverse_product_block hw hm)
    (InvEigA.zeta_fix hz' hw hm) M X

end Formalism.FourierDecayAlt.P.CutMP
end
