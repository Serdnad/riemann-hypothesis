module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsConjSplitPointLatticeLinearMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle115
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverComparisonScalarEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.CrysConn

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

def PDPoly.derVal (Q : PDPoly B) : ℕ → Q.P
  | 0 => 0
  | n + 1 => Q.e n

def PDPoly.derLin (Q : PDPoly B) : Q.P →ₗ[B] Q.P := Q.e.constr B Q.derVal

theorem PDPoly.derLin_e (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e n) = Q.derVal n := by
  simp [PDPoly.derLin, Module.Basis.constr_basis]

theorem PDPoly.derLin_e_succ (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e (n + 1)) = Q.e n := Q.derLin_e (n + 1)

theorem PDPoly.derLin_e_zero (Q : PDPoly B) : Q.derLin (Q.e 0) = 0 := Q.derLin_e 0

theorem PDPoly.derLin_e_mul_e (Q : PDPoly B) (m n : ℕ) :
    Q.derLin (Q.e m * Q.e n) = Q.e m * Q.derLin (Q.e n) + Q.e n * Q.derLin (Q.e m) := by
  rcases m with _ | a
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rcases n with _ | b
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rw [Q.derLin_e_succ, Q.derLin_e_succ, Q.e_mul, Q.e_mul, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
    show a + 1 + (b + 1) = (a + b + 1) + 1 by omega, Q.derLin_e_succ, show a + 1 + b = a + b + 1 by omega,
    show b + 1 + a = a + b + 1 by omega, Nat.choose_succ_succ' (a + b + 1) a,
    Nat.choose_symm_of_eq_add (show a + b + 1 = (b + 1) + a by omega)]
  push_cast
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem PDPoly.derLin_mul (Q : PDPoly B) (x y : Q.P) :
    Q.derLin (x * y) = x * Q.derLin y + y * Q.derLin x := by
  have h2 : ∀ x n, Q.derLin (x * Q.e n) = x * Q.derLin (Q.e n) + Q.e n * Q.derLin x := fun x n ↦ by
    have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulRight B (Q.e n))
      (f₂ := LinearMap.mulRight B (Q.derLin (Q.e n)) + LinearMap.mulLeft B (Q.e n) ∘ₗ Q.derLin)
      (fun m ↦ by simpa using Q.derLin_e_mul_e m n)
    simpa using LinearMap.congr_fun this x
  have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulLeft B x)
    (f₂ := LinearMap.mulLeft B x ∘ₗ Q.derLin + LinearMap.mulRight B (Q.derLin x))
    (fun n ↦ by simpa using h2 x n)
  simpa using LinearMap.congr_fun this y

def PDPoly.der (Q : PDPoly B) : Derivation B Q.P Q.P :=
  Derivation.mk' Q.derLin fun x y ↦ by simpa [smul_eq_mul] using Q.derLin_mul x y

theorem PDPoly.der_apply (Q : PDPoly B) (x : Q.P) : Q.der x = Q.derLin x := rfl

end GlobalTheory.PDA

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

theorem PDPoly.der_dpow_succ {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (n : ℕ) {a : Q.P} (ha : a ∈ Q.ext J) :
    Q.der (η.dpow (n + 1) a) = η.dpow n a * Q.der a := by
  set D := Q.der
  let P : Q.P → Prop := fun a ↦ ∀ n, D (η.dpow n a) = dpPred η n a • D a
  have hzero : P 0 := fun n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Q.ext J).zero_mem]
    | succ n => simp [dpow_eval_zero _ n.succ_ne_zero]
  have hadd : ∀ a ∈ Q.ext J, ∀ b ∈ Q.ext J, P a → P b → P (a + b) := fun a ha b hb iha ihb n ↦ by
    have iha : ∀ n, D (η.dpow n a) = dpPred η n a • D a := iha
    have ihb : ∀ n, D (η.dpow n b) = dpPred η n b • D b := ihb

    simp only [η.dpow_add ha hb, map_sum, D.leibniz, iha, ihb, smul_smul, Finset.sum_add_distrib,
    ← Finset.sum_smul, sum_dpow_mul_dpPred η ha hb, sum_dpow_mul_dpPred' η ha hb, map_add, smul_add]
    exact add_comm _ _
  have hmul : ∀ r, ∀ a ∈ Q.ext J, P a → P (r * a) := fun r a ha hP n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Ideal.mul_mem_left _ r ha), dpPred]
    | succ m =>
      have hm := hP (m + 1)
      have hs := dpPred_mul_self η ha (m + 1)
      simp only [dpPred, smul_eq_mul] at hm hs ⊢
      rw [η.dpow_mul ha, η.dpow_mul ha, D.leibniz, D.leibniz, D.leibniz_pow, hm]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      push_cast at hs ⊢
      linear_combination (-(r ^ m * D r)) * hs
  have hspan : ∀ s : Set Q.P, s ⊆ Q.ext J → (∀ x ∈ s, P x) → ∀ a ∈ Ideal.span s, P a := by
    intro s hs hP a ha
    have hle : Ideal.span s ≤ Q.ext J := Ideal.span_le.2 hs
    induction ha using Submodule.span_induction with
    | mem x hx => exact hP x hx
    | zero => exact hzero
    | add x y hx hy ihx ihy => exact hadd x (hle hx) y (hle hy) ihx ihy
    | smul r x hx ih => exact hmul r x (hle hx) ih
  have hJ : ∀ x ∈ J.map (algebraMap B Q.P), P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩; exact Q.algebraMap_mem_ext hj
    · rintro _ ⟨j, hj, rfl⟩ n
      rw [h.dp.2 j hj, Derivation.map_algebraMap, Derivation.map_algebraMap, smul_zero]
  have he1 := Q.e_one_mem_ext J
  have hA : ∀ x ∈ Q.aug, P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨k, rfl⟩; exact Ideal.mem_sup_right (Q.e_succ_mem_aug k)
    · rintro _ ⟨k, rfl⟩ n
      cases n with
      | zero => simp [η.dpow_zero (Ideal.mem_sup_right (Q.e_succ_mem_aug k)), dpPred]
      | succ m =>
        have c1 : η.dpow (m + 1) (Q.e (k + 1)) =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e ((m * (k + 1) + k) + 1) := by
          rw [← h.var (k + 1), η.dpow_comp (by omega) he1, h.var, show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring]
        have c2 : dpPred η (m + 1) (Q.e (k + 1)) * Q.e k =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e (m * (k + 1) + k) := by
          have := dpPred_dpow η he1 (m + 1) (n := k + 1) (by omega)
          rw [h.var, show dpPred η (k + 1) (Q.e 1) = Q.e k from h.var k,
            show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring,
            show dpPred η (m * (k + 1) + k + 1) (Q.e 1) = Q.e (m * (k + 1) + k) from h.var _] at this
          exact this
        rw [c1, D.leibniz, D.map_natCast, smul_zero, add_zero, smul_eq_mul, smul_eq_mul, Q.der_apply,
          Q.der_apply, Q.derLin_e_succ, Q.derLin_e_succ, c2]
  have hall : ∀ x ∈ Q.ext J, P x := fun x hx ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact hadd y (Ideal.mem_sup_left hy) z (Ideal.mem_sup_right hz) (hJ y hy) (hA z hz)
  simpa [dpPred, smul_eq_mul] using hall a ha (n + 1)

theorem PDPoly.exists_der (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) :
    Q.IsStd δ η → ∃ D : Derivation R Q.P Q.P, (∀ b, D (algebraMap B Q.P b) = 0) ∧
      (∀ n, D (Q.e (n + 1)) = Q.e n) ∧ ∀ n, ∀ a ∈ Q.ext J, D (η.dpow (n + 1) a) = η.dpow n a * D a := by
  intro h
  refine ⟨Q.der.restrictScalars R, fun b ↦ ?_, fun n ↦ ?_, fun n a ha ↦ ?_⟩
  · rw [Derivation.restrictScalars_apply, Derivation.map_algebraMap]
  · rw [Derivation.restrictScalars_apply, Q.der_apply, Q.derLin_e_succ]
  · simp only [Derivation.restrictScalars_apply]
    exact Q.der_dpow_succ δ η h n ha

end GlobalTheory.PDA
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section
namespace GlobalTheory.LevGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem adelicProb_mul_volFund : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ 0 ∧ (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ ⊤ ∧ ∀ Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (Φ k)) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x) → (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x) → (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) * ∑ k, muF ((U σ).X k) (x0 k) (FF k) = ∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) := by
  intro D j H Dw l Xo c U dict hL σ hσ x0 FF hFF
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  have hvp := Formalism.L2.Pj.volPair_isVolPair (D.sp.W j) hP
  haveI : (Formalism.L2.Pj.volPair (D.sp.W j)).1.IsHaarMeasure := hvp.1.1
  have h0 : (Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2 ≠ 0 :=
    Formalism.L2.Pj.muQ_univ (D.sp.W j) ▸ hV.1
  have h1 : (Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2 ≠ ⊤ :=
    Formalism.L2.Pj.muQ_univ (D.sp.W j) ▸ hV.2
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  have hU := hL.unf σ hσ
  have hΨ : ∀ k k', ((U σ).X k).Ψ = ((U σ).X k').Ψ ∧ ((U σ).X k).p0 = ((U σ).X k').p0 := fun k k' =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm, (hU.2.1 k).1.trans (hU.2.1 k').1.symm⟩
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨κ, hκ0, hκ1, hI⟩ := GlobalTheory.PeterssonCompare.lintegral_adelic (D.sp.W j) (U σ).X (dict σ) hM hth hd hK hu hΨ
    _ hvp.2 h0 h1
  set k0 := (dict σ 1).1
  obtain ⟨κ2, h20, h21, hH⟩ := GlobalTheory.T.flagQuotientIntegral_eq_universal_const_mul D.R.r Dw.q ((U σ).X k0).Ψ.card
  have hQ : ∀ k (F : Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞), Measurable F →
      (∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F (lact γ x) = F x) →
      (∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F (rmul x b) = F x) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) F = κ2 * ∫⁻ z in FF k, F (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k)) :=
    fun k F hF hΓ hB => hH D.host.E ((U σ).X k) (hU.2.1 k).1 (by rw [(hΨ k k0).1]) (x0 k) (FF k) F (hFF k).1 (hFF k).2
      hF hΓ hB
  have key : ∀ F : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F k (rmul x b) = F k x) →
      ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j)) =
        ((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ *
          (κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k)) := by
    intro F hF hΓ hB
    obtain ⟨h2, h3⟩ := hI F hF hΓ hB
    have hout : ∀ g, F (dict σ (Formalism.L2.Pj.autMk (D.sp.W j) g).out).1 (dict σ (Formalism.L2.Pj.autMk (D.sp.W j) g).out).2 =
        F (dict σ g).1 (dict σ g).2 := by
      intro g
      have h4 : g * (Formalism.L2.Pj.autMk (D.sp.W j) g).out⁻¹ ∈ GQ (D.sp.W j) :=
        QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
      obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 (Formalism.L2.Pj.autMk (D.sp.W j) g).out
      rw [inv_mul_cancel_right] at e
      rw [e]
      exact (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
    have hq : Measurable fun q : Formalism.L2.Pj.AutQ (D.sp.W j) => F (dict σ q.out).1 (dict σ q.out).2 := by
      rw [measurable_from_quotient]
      have : ((fun q : Formalism.L2.Pj.AutQ (D.sp.W j) => F (dict σ q.out).1 (dict σ q.out).2) ∘ Quotient.mk'') =
          fun g => F (dict σ g).1 (dict σ g).2 := funext hout
      rw [this]
      exact h2
    have h5 : ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(Formalism.L2.Pj.muQ (D.sp.W j)) =
        κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k) := by
      rw [Formalism.L2.Pj.muQ, lintegral_map hq (Formalism.L2.Pj.autMk_measurable (D.sp.W j))]
      simp only [hout]
      exact h3
    rw [Formalism.L2.Pj.muQ1, if_pos (show Formalism.L2.Pj.muQ (D.sp.W j) Set.univ ≠ 0 ∧ Formalism.L2.Pj.muQ (D.sp.W j) Set.univ ≠ ⊤
      from hV), lintegral_smul_measure, h5, Formalism.L2.Pj.muQ_univ, smul_eq_mul]
  have e1 := key (fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_congr rfl fun k _ => hQ k (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl),
    ← Finset.mul_sum] at e1
  simp only [setLIntegral_one, lintegral_const, measure_univ, mul_one, one_mul, Measure.restrict_apply_univ] at e1
  have hv0 : ((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 h1
  refine ⟨fun hS => ?_, fun hS => ?_, fun Φ hΦ hΓ hB => ?_⟩
  · rw [hS, mul_zero, mul_zero, mul_zero] at e1
    exact one_ne_zero e1
  · rw [hS, ENNReal.mul_top h20, ENNReal.mul_top hκ0, ENNReal.mul_top hv0] at e1
    exact ENNReal.one_ne_top e1
  · rw [key Φ hΦ hΓ hB, Finset.sum_congr rfl fun k _ => hQ k (Φ k) (hΦ k) (hΓ k) (hB k), ← Finset.mul_sum]
    calc _ = (∑ k, ∫⁻ z in FF k, Φ k (cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k))) *
          (((Formalism.L2.Pj.volPair (D.sp.W j)).1 (Formalism.L2.Pj.volPair (D.sp.W j)).2)⁻¹ *
            (κ * (κ2 * ∑ k, muF ((U σ).X k) (x0 k) (FF k)))) := by ring
      _ = _ := by rw [← e1, mul_one]

end GlobalTheory.LevGeo
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjSplitIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nsmul_cancel {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) {N : ℕ} (hN : 0 < N) {u u' : D.La} (h : N • u = N • u') : u = u' := by
  apply hP.2.1
  have h' := congrArg P h
  rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h'
  exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') h'

theorem form_nsmul_nsmul (D : Datum H) (N : ℕ) (x y : D.La) : D.EF (N • x) (N • y) = (N * N : ℤ) * D.EF x y := by
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  ring

end GlobalTheory.ConjSplitIndex

namespace GlobalTheory.CompRat


open ConjIsometry in
theorem exists_isometry_of_conj_split_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P') (N : ℕ), 0 < N → (∀ v : (F.Di i).La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → C.ActsBy τ io N (1, 0) → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) ∧ (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) ∧ ∀ n : ℕ, 0 < n → C.ActsBy τ io (N * n) (1, 0) → ∀ v, spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P v)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ v))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' N hN hNv hu hAN
  obtain ⟨f, hadd, hw, -, hact, hf⟩ := GlobalTheory.ConjSplit.exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := GlobalTheory.ConjSplitAnyLevel.exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε
    refine ⟨Φ, hΦ, fun n s hA a => ?_⟩
    rw [smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex,
      GlobalTheory.ConjSplit.ex_congr_type F hP ε a.2 (hact n s hA), one_div]
  obtain ⟨Φp, hp, tp⟩ := key 1 H.rt0 (by simp)
  obtain ⟨Φm, hm, tm⟩ := key (-1) (-H.rt0) (by simp)
  have hd := Submodule.disjoint_def.1 (disjoint_lat hP (GlobalTheory.ConjSplit.rt0_ne_neg (H := H)))

  have hsum : ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      U ≫ F.ex i P ((n : ℂ)⁻¹ • P (a.1 + b.1)) =
        F.ex i' P' ((n : ℂ)⁻¹ • P' (Φp (wE H s • a) + Φm (H.bar (wE H s) • b))) := by
    intro n s hA a b
    rw [map_smul, map_smul, map_add P', GlobalTheory.ConjSplit.period_wE hP' (hp a),
      GlobalTheory.ConjSplit.period_bar_wE hP' (hm b), smul_add, F.ex_add i' P' hP', ← tp n s hA, ← tm n s hA,
      ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]
  have hsum1 : ∀ n : ℕ, C.ActsBy τ io n (1, 0) → ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      U ≫ F.ex i P ((n : ℂ)⁻¹ • P (a.1 + b.1)) = F.ex i' P' ((n : ℂ)⁻¹ • P' (Φp a + Φm b)) := by
    intro n hA a b
    rw [hsum n (1, 0) hA a b]
    simp [wE]

  have hiso₀ : ∀ (a a' : lat hP H.rt0) (b b' : lat hP (-H.rt0)),
      (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') = (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1) := by
    intro a a' b b'
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') - (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1) := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.CompRat.Acts.main E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (congrArg (fun m => m.left) (hsum n s hs a b))
        (congrArg (fun m => m.left) (hsum n s hs a' b'))
      have hM := GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = M at hM hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = M := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP' H.rt0, ∀ v ∈ lat hP' (-H.rt0),
          (F.Di i').EF u v = 0 ∧ (F.Di i').EF v u = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' hu hv
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φp (wE H s • a) + Φm (H.bar (wE H s) • b)) (Φp (wE H s • a') + Φm (H.bar (wE H s) • b')) =
          M * (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') := by
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [(o _ (hp _) _ (hm _)).1, (o _ (hp _) _ (hm _)).2, (o _ (hp a) _ (hm b')).1, (o _ (hp a') _ (hm b)).2,
          map_smul Φp, map_smul Φp, map_smul Φm, map_smul Φm, form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hM] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') - (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1)).natAbs + 1)
      (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this
      (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hdec : ∀ v, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v := fun v => by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hNv v)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
  have huniq : ∀ (a a' : lat hP H.rt0) (b b' : lat hP (-H.rt0)), a.1 + b.1 = a'.1 + b'.1 → a = a' ∧ b = b' := by
    intro a a' b b' h
    have e : a.1 - a'.1 = b'.1 - b.1 := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have z : a.1 - a'.1 = 0 := hd _ (sub_mem a.2 a'.2) (e ▸ sub_mem b'.2 b.2)
    exact ⟨Subtype.ext (sub_eq_zero.1 z), Subtype.ext (sub_eq_zero.1 (e ▸ z)).symm⟩
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hdiv : ∀ v, ∃ u : (F.Di i').La, ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v →
      Φp a + Φm b = N • u := by
    intro v
    obtain ⟨a, b, hab⟩ := hdec v
    have e := hsum1 N hAN a b
    rw [hab, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hNc, (F.ex_ker i P hP _).2 ⟨v, rfl⟩,
      MonObj.comp_one] at e
    obtain ⟨u, hu'⟩ := (F.ex_ker i' P' hP' _).1 e.symm
    refine ⟨u, fun a' b' h => ?_⟩
    obtain ⟨rfl, rfl⟩ := huniq a a' b b' (hab.trans h.symm)
    apply hP'.2.1
    rw [map_nsmul, hu', ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hNc]
  choose Ψ hΨ using hdiv
  let Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La :=
    { toFun := Ψ
      map_add' := fun v w => by
        obtain ⟨a, b, hab⟩ := hdec v
        obtain ⟨a', b', hab'⟩ := hdec w
        refine GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN ?_
        rw [smul_add, ← hΨ v a b hab, ← hΨ w a' b' hab', ← hΨ (v + w) (a + a') (b + b')
          (by rw [smul_add, ← hab, ← hab', Submodule.coe_add, Submodule.coe_add]; abel), map_add (f := _), map_add (f := _)]
        abel
      map_smul' := fun c v => by
        obtain ⟨a, b, hab⟩ := hdec v
        refine GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN ?_
        rw [RingHom.id_apply, smul_comm N c, ← hΨ v a b hab, ← hΨ (c • v) (c • a) (c • b)
          (by rw [smul_comm N c, ← hab, Submodule.coe_smul, Submodule.coe_smul, smul_add]), map_smul, map_smul,
          smul_add] }
  have hΦ : ∀ v (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v → Φp a + Φm b = N • Φ v := hΨ
  have hiso : ∀ v w, (F.Di i').EF (Φ v) (Φ w) = (F.Di i).EF v w := by
    intro v w
    obtain ⟨a, b, hab⟩ := hdec v
    obtain ⟨a', b', hab'⟩ := hdec w
    have e := hiso₀ a a' b b'
    rw [hΦ v a b hab, hΦ w a' b' hab', hab, hab', GlobalTheory.ConjSplitIndex.form_nsmul_nsmul,
      GlobalTheory.ConjSplitIndex.form_nsmul_nsmul] at e
    have hz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact mul_left_cancel₀ (mul_ne_zero hz hz) e
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero _).2 fun v hv =>
    (F.Di i).unimod.1 (by
      ext z
      rw [← hiso, hv]; simp)
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, fun a ha => ?_, fun b hb => ?_, fun n hn hA v => ?_⟩
  · have e := hΦ a (N • ⟨a, ha⟩) 0 (by simp)
    rw [map_zero, add_zero, map_nsmul] at e
    show Φ a ∈ _
    rw [← GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN e]
    exact hp _
  · have e := hΦ b 0 (N • ⟨b, hb⟩) (by simp)
    rw [map_zero, zero_add, map_nsmul] at e
    show Φ b ∈ _
    rw [← GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN e]
    exact hm _
  · obtain ⟨a, b, hab⟩ := hdec v
    have e := hsum1 (N * n) hA a b
    have hc : ∀ x : Fin g → ℂ, ((N * n : ℕ) : ℂ)⁻¹ • N • x = (n : ℂ)⁻¹ • x := fun x => by
      rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_mul, mul_inv_rev, mul_smul, inv_smul_smul₀ hNc]
    rw [hΦ v a b hab, hab, map_nsmul, map_nsmul, hc, hc] at e
    exact congrArg (fun m => m.left) e

end GlobalTheory.CompRat
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.coverComparison_scalar_eq_one : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∀ ζ : D.host.E, ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * Matrix.scalar (Fin D.R.r) ζ → Matrix.scalar (Fin D.R.r) ζ = 1 := by
  first | exact @GlobalTheory.LevScalar.scalar_eq_one_of_conj | exact GlobalTheory.LevScalar.scalar_eq_one_of_conj | (intros; apply GlobalTheory.LevScalar.scalar_eq_one_of_conj <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.partial_fourier_preserves_schwartz_L2 : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.DblEval.lintegral_partL_eq | exact GlobalTheory.DblEval.lintegral_partL_eq | (intros; apply GlobalTheory.DblEval.lintegral_partL_eq <;> assumption)
end
