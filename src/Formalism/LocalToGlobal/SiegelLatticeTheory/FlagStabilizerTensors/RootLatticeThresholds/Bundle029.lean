module

public import Formalism.HermitianCurvature.StatementD
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMass
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightActionThreeFamilies
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PerpIffOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle011
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPin

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem choose_congr {α : Sort*} {p q : α → Prop} (e : p = q) (h : ∃ x, p x) (h' : ∃ x, q x) :
    h.choose = h'.choose := by
  subst e; rfl

theorem orbIntegrand_smul (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ) (p : Formalism.FourierDecayAlt.B.SS k r) :
    Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p = c • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p := by
  unfold Formalism.FourierDecayAlt.D.orbIntegrand Formalism.FourierDecayAlt.B.rho
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem orbJ_smulF (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) {c : ℂ} (hc : c ≠ 0) :
    Formalism.FourierDecayAlt.D.orbJ D γ μ (fun g => c • F g) = c • Formalism.FourierDecayAlt.D.orbJ D γ μ F := by
  have hP : (fun θ => Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
      (fun θ => Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS) := by
    funext θ
    have e : (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) =
        c • (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) := by
      funext p; rw [orbIntegrand_smul, smul_comm]; rfl
    rw [e, integrable_smul_iff hc]
  have e2 : ∀ θ : Formalism.FourierDecayAlt.B.SS k r → ℝ, (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) =
      fun p => c • (θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) := fun θ => by
    funext p; rw [orbIntegrand_smul, smul_comm]
  unfold Formalism.FourierDecayAlt.D.orbJ
  by_cases h2 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS
  · have h1 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS := by
      rw [show (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
        ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS from congrArg Exists hP]
      exact h2
    rw [dite_eq_left h1, dite_eq_left h2, choose_congr hP h1 h2, e2, integral_smul]
  · have h1 : ¬ ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS := by
      rw [show (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
        ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS from congrArg Exists hP]
      exact h2
    rw [dite_eq_right h1, dite_eq_right h2, smul_zero]

end Lin

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

end Formalism.L2.SG.Pf.Carrier.CarPin
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem autLz_finite (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) {Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ' : Λ' ∈ Y.what₂ u') : Finite (autLz D (X.Fu u') Λ') := by
  let q : {Λ // Λ ∈ Y.what₂ u'} := ⟨Λ', hΛ'⟩
  have e1 := Equiv.ofBijective _ (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN q)
  have e2 := Equiv.ofBijective _ (Formalism.L2.SG.Pf.Act.gamL_levi_bij (Y.cs u') Y.TR Y.hK hN q)
  exact Finite.of_equiv _ (e2.symm.trans e1)

theorem fib_bij (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (s₀ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') :
    ∃ f : {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} → autLz D (X.Fu u') s₀.lam', Function.Bijective f := by
  haveI := autLz_finite hN s₀.mem'
  have hex : ∀ s : {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm}, ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V,
      c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam' ∧
      (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
      ∃ n ∈ NLam s₀.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s₀.lam' (lf D (X.Fu u')),
        (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u').lin = n * s₀.lin * ν * c :=
    fun s => fib_c s.2.symm
  let cf : {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} → (VS D).V ≃ₗ[D.host.E] (VS D).V := fun s => (hex s).choose
  have hcf : ∀ s, _ := fun s => (hex s).choose_spec
  let f : {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} → autLz D (X.Fu u') s₀.lam' := fun s =>
    ⟨indQ (X.Fu u') (cf s) (hcf s).1 (hcf s).2.2.1, indQ_mem (X.Fu u') _ _ _ (hcf s).2.1⟩
  refine ⟨f, fun s s' hss => ?_, fun φ => ?_⟩
  · have hq := sub_mem_of_indQ (X.Fu u') (hcf s).1 (hcf s).2.2.1 (hcf s').1 (hcf s').2.2.1
      (congrArg Subtype.val hss)
    obtain ⟨n, hn, ν, hν, he⟩ := (hcf s).2.2.2
    obtain ⟨n', hn', ν', hν', he'⟩ := (hcf s').2.2.2
    exact Subtype.ext (eq_of_dec s.2.symm s'.2.symm hn hn' hν hν' (hcf s).1 (hcf s').1 (hcf s).2.1 (hcf s').2.1
      (hcf s).2.2.1 (hcf s').2.2.1 he he' hq)
  · obtain ⟨φ, hφ⟩ := φ
    obtain ⟨g, hg⟩ := (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s₀.lam', s₀.mem'⟩).2 ⟨φ, hφ⟩
    have hc₁s : Formalism.L2.SG.Pf.Act.isoG g.1 ∈ stabF D (X.Fu u') := Formalism.L2.SG.Pf.Act.isoG_stab g.1
    have hc₁ : Formalism.L2.SG.Pf.Act.isoG g.1 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hc₁s.1
    have hc₁fix : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
      intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · have hz : (X.Fu u').z = X.zu u' := X.flagZVector u'
        simp only [FlagG.fvec, Fin.snoc_last]
        rw [hz]
        exact Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)
      · have he : (X.Fu u').e i = X.eX i := congrFun (X.Fu_e u') i
        simp only [FlagG.fvec, Fin.snoc_castSucc]
        rw [he]
        exact Formalism.L2.SG.Pf.Act.isoG_e g.1 i
    have hc₁g : Formalism.HermitianLatticesTheory.gmap (Formalism.L2.SG.Pf.Act.isoG g.1) s₀.lam' = s₀.lam' :=
      Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s₀.lam', s₀.mem'⟩ g
    have hφ' : ⇑(Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) hc₁s) = φ := congrArg Subtype.val hg
    set c₁ := Formalism.L2.SG.Pf.Act.isoG g.1 with hc₁def
    have hA₁ : IsAutLam (VS D) s₀.lam' c₁ := ⟨hc₁, hc₁g⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X c₁⁻¹ (Subgroup.inv_mem _ hc₁)
    have hβ : c₁⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s₀.lam' (lf D (X.Fu u')) := by
      refine ⟨Formalism.L2.SG.Pf.isAutLam_inv hA₁, fun a => inv_fix (X.Fu u') hc₁fix a, ?_⟩
      have := inv_fix (X.Fu u') hc₁fix (Fin.last _)
      simpa [FlagG.fvec] using this
    set s₁ := Formalism.L2.SG.Pf.SatGramActR.tmap x c₁⁻¹ Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds hx s₀ with hs₁
    have ht : s₁.toTerm = s₀.toTerm := Formalism.L2.SG.Pf.SatGramActR.toTerm_tmap _ _ _ hx s₀
    have hcls := Formalism.L2.SG.Pf.SatGramActR.tmap_cls x c₁⁻¹ Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds hx s₀ hβ
    obtain ⟨n₁, hn₁, n₁', hn₁', hlin⟩ := lin_of_cls s₁ _ hcls
    have hν₁ : c₁ * n₁' * c₁⁻¹ ∈ NLam s₀.lam' (lf D (X.Fu u')) :=
      Formalism.L2.SG.Pf.nlam_conj hA₁ (fun a => (hc₁fix a).symm) hn₁'
    have hlin' : s₁.lin = n₁ * s₀.lin * (c₁ * n₁' * c₁⁻¹) * c₁ := by
      rw [hlin]
      show n₁ * (s₀.lin * c₁⁻¹⁻¹) * n₁' = _
      group
    refine ⟨⟨s₁, ht⟩, Subtype.ext ?_⟩
    obtain ⟨n, hn, ν, hν, he⟩ := (hcf ⟨s₁, ht⟩).2.2.2
    have hwd := wd (F := X.Fu u) hn hn₁ hν hν₁ (hcf ⟨s₁, ht⟩).1 hc₁ (hcf ⟨s₁, ht⟩).2.1 hc₁g
      (hcf ⟨s₁, ht⟩).2.2.1 hc₁fix (he.symm.trans hlin')
    show indQ (X.Fu u') (cf ⟨s₁, ht⟩) (hcf ⟨s₁, ht⟩).1 (hcf ⟨s₁, ht⟩).2.2.1 = φ
    rw [← hφ']
    funext w
    induction w using Submodule.Quotient.induction_on with
    | H y =>
      rw [indQ_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq]
      exact hwd y y.2

theorem liftMassC_of (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) : Formalism.L2.SG.Pf.RowForm.LiftMassC X Y u u' := by
  intro t _
  obtain ⟨s₀, hs₀⟩ := Formalism.L2.SG.Pf.Act.liftOnto (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D)
    (fun n hn => Formalism.L2.SG.Pf.ratPt_holds D X n hn) Y u u'
    (Formalism.L2.SG.Pf.toTermRel_holds X u u' (X.Fu u) (X.Fu u')) t
  subst hs₀
  haveI := autLz_finite hN s₀.mem'
  obtain ⟨f, hf⟩ := fib_bij hN s₀
  let e := Equiv.ofBijective f hf
  haveI : Finite {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} := Finite.of_equiv _ e.symm
  haveI : Fintype {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} := Fintype.ofFinite _
  have hw : ∀ s : {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm},
      Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = Formalism.MainNotions.S.wRow D (X.Fu u') s₀.lam' := fun s => by
    rw [lam'_eq s.2.symm]
  have hpos : 0 < Nat.card (autLz D (X.Fu u') s₀.lam') := by
    haveI : Nonempty (autLz D (X.Fu u') s₀.lam') := ⟨f ⟨s₀, rfl⟩⟩
    exact Nat.card_pos
  show ∑' s : {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm}, Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = 1
  rw [tsum_fintype, Finset.sum_congr rfl (fun s _ => hw s), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold Formalism.MainNotions.S.wRow
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
  exact mul_inv_cancel₀ (by exact_mod_cast hpos.ne')

end Count

end Formalism.L2.SG.Pf.FibreCounting
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.BDat Formalism.L2.SG.ThmBUseR
open scoped ENNReal

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.BDatR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section J2

variable {D : D7}

def JointAmplitudeFactorizationRotated {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl Nu) (large₂ : SizeData₂ D) (C1 : ℝ)
    (W : D.what₂.Tau → LocW D.R.k D.R.rS) (A : ∀ τ, LocS (W τ)) (T T' : ℕ) (Cfac : ℝ) : Prop :=
  ∀ γ (w : Point D.host.E (D.R.rS + 1)), Formalism.FourierDecayAlt.PN.IsPt X N γ → Formalism.L2.SG.RowsConc.toPts w = γ →
    Formalism.L2.SG.ThmBUse.IsRowPt D T T' w → 0 < N.jacobianSquareBound γ →
    ∃ (g : D.what₂.Tau → MatKR D.R.k D.R.rS) (θ' : D.what₂.Tau → ℝ)
      (νR : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
      (∀ τ, RelPt D (W τ).z (W τ).z' (g τ) (ptLoc D τ w) ∧ normWin D large₂ C1 (θ' τ) ∧
        RMeas D (W τ) (g τ) (θ' τ) (νR τ)) ∧
      ENNReal.ofReal (N.jacobianSquareBound γ) ≤ ENNReal.ofReal Cfac * ∏ τ, ENNReal.ofReal (hsNormSq ((A τ).J (νR τ) (g τ)))

private lemma prod_ofReal_le_lemma {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ∏ i ∈ s, ENNReal.ofReal (x i) ≤ ENNReal.ofReal (∏ i ∈ s, x i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha]
  rcases le_or_gt 0 (x a) with h | h
  · rw [ENNReal.ofReal_mul h]; gcongr
  · rw [ENNReal.ofReal_of_nonpos h.le, zero_mul]; simp

theorem jointAmplitude_bound_rotated {τ₀ Rw I₀ H H₁ : Type} [Fintype I₀] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ₀ Rw I₀ H H₁)
    {Cl Nu : Type} (N : Formalism.FourierDecayAlt.PN.NGData τ₀ D.host.E D.R.rS Cl Nu) {large₂ : SizeData₂ D} {C1 Ca Ch Cg b : ℝ}
    {u u' : D.what₂.Word} {θ : ℝ} {hT : 0 < Tr D u} {hT' : 0 < Tr D u'} (I : AmpIn large₂ C1 Ca u u' θ hT hT')
    (hok : ∀ τ, LocOk D Ch Cg (I.L τ) (lamSH D.R (D.hc τ)) (kaRe D) b (kaRe D))
    (hka : 0 < Formalism.MainNotions.S.Bridge.kaS D) {Cfac : ℝ} (hCfac : 0 ≤ Cfac)
    (hF : JointAmplitudeFactorizationRotated X N large₂ C1 I.W I.A (D.mem u).A.T (D.mem u').A.T Cfac) :
    JointNormBoundRotated X N (bdOf I.toInputs hok) (Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) := by
  intro γ w hpt hw hrow
  by_cases hpos : 0 < N.jacobianSquareBound γ
  · obtain ⟨g, θ', νR, hτ, hle⟩ := hF γ w hpt hw hrow hpos
    have h1 : ∏ τ, ENNReal.ofReal (hsNormSq ((I.A τ).J (νR τ) (g τ))) ≤
        ∏ τ, (ENNReal.ofReal (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
          orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by
      apply Finset.prod_le_prod'
      intro τ _
      exact le_trans (I.hJ τ (g τ) (ptLoc D τ w) (hτ τ).1 (θ' τ) (hτ τ).2.1 (νR τ) (hτ τ).2.2)
        (by gcongr; exact orbSqO_le_bdOf I.toInputs hok hka τ _)
    rw [Finset.prod_mul_distrib] at h1
    have h2 := prod_ofReal_le_lemma Finset.univ (fun τ => I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))
    calc ENNReal.ofReal (N.jacobianSquareBound γ)
        ≤ ENNReal.ofReal Cfac * ∏ τ, ENNReal.ofReal (hsNormSq ((I.A τ).J (νR τ) (g τ))) := hle
      _ ≤ ENNReal.ofReal Cfac * ((∏ τ, ENNReal.ofReal (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          ∏ τ, orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by gcongr
      _ ≤ ENNReal.ofReal Cfac * (ENNReal.ofReal (∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          ∏ τ, orbSq ((bdOf I.toInputs hok).L τ) ((bdOf I.toInputs hok).f τ)
            (Formalism.MainNotions.S.Pv.Frames.turnPt (ptLoc D τ w))) := by gcongr
      _ = ENNReal.ofReal (Cfac * ∏ τ, (I.K τ * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2))) *
          JSqR D (bdOf I.toInputs hok) w := by
        rw [ENNReal.ofReal_mul hCfac, mul_assoc]; rfl
  · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hpos)]; simp

end J2

section Cut

open Formalism.L2.SG.Pf.JointAmplitudePoints

variable {D : D7} {X : HidaSetting D}

def RelPtExPR (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → ∀ τ,
      RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w τ) (ptLoc D τ w)

private lemma toPts_inj_lemma {K : Type} [Zero K] {i : ℕ} (p q : Formalism.MainNotions.S.Point K (i + 1))
    (h : Formalism.L2.SG.RowsConc.toPts p = Formalism.L2.SG.RowsConc.toPts q) : p = q := by
  have h1 : p.1.map Prod.snd = q.1.map Prod.snd := congrArg (fun s => s.1.blocks) h
  have key : ∀ r : Formalism.MainNotions.S.Point K (i + 1), List.ofFn (Formalism.L2.SG.RowsConc.toPts r).2 = r.1.map Prod.fst := by
    intro r
    apply List.ext_get
    · simp [Formalism.L2.SG.RowsConc.toPts, Composition.length]
    · intro n h1 h2
      simp [Formalism.L2.SG.RowsConc.toPts]
  have h2 : p.1.map Prod.fst = q.1.map Prod.fst := by
    rw [← key p, ← key q]
    exact congrArg (fun s : (Σ c : Composition (i + 1), (Fin c.length → K)) => List.ofFn s.2) h
  apply Subtype.ext
  rw [← List.zip_unzip p.1, ← List.zip_unzip q.1, List.unzip_fst, List.unzip_snd, List.unzip_fst,
    List.unzip_snd, h1, h2]

private lemma quot_scale_lemma_2 {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : Formalism.MainNotions.S.IsQuotMeas μG μS ν) {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    Formalism.MainNotions.S.IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  intro f hf
  rw [h f hf]
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hct, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem jointAmplitudeFactorizationRotated_of (Y : Full X) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hR : RelPtExPR u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1) :
    JointAmplitudeFactorizationRotated (Y.tO u u') (NOf2 Y u u' νL ν ng) large₂ C1 (WX C u u') (AX hB u u') (D.mem u).A.T (D.mem u').A.T 1 := by
  intro γ w hpt hw hrow hpos
  have hJB : (NOf2 Y u u' νL ν ng).jacobianSquareBound γ = J2of Y u u' ν γ := rfl
  rw [hJB] at hpos ⊢
  subst hw
  obtain ⟨w', hw', hrep⟩ := isPtRep_of_J2of hpos
  have hww : w' = w := toPts_inj_lemma w' w hw'
  subst hww
  have hP1 : 0 < localAmplitudeProduct u u' hB w' := hP w' hrow hpos
  haveI := Formalism.L2.SG.Pf.LTL.tau_nonempty D
  have hn : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos
  have hθ0 : thetaP u u' hB (J2of Y u u' ν (toPts w')) w' =
      (localAmplitudeProduct u u' hB w' / J2of Y u u' ν (toPts w')) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    simp only [thetaP, if_pos (And.intro hpos hP1)]
  have hθpos : 0 < thetaP u u' hB (J2of Y u u' ν (toPts w')) w' := by
    rw [hθ0]; apply Real.rpow_pos_of_pos; exact div_pos hP1 hpos
  have hν1 : ∀ τ, RMeas D (locW C u u' τ) (gamP C u u' w' τ) 1 (nu1P C u u' w' τ) := fun τ => by
    have h := hM w' hrow hrep τ
    simp only [nu1P, dif_pos h]
    exact h.choose_spec
  have hsc : ∀ τ, RMeas D (locW C u u' τ) (gamP C u u' w' τ) (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')
      (ENNReal.ofReal (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')⁻¹ • nu1P C u u' w' τ) := fun τ => by
    obtain ⟨p, μR, hroot, hq⟩ := hν1 τ
    refine ⟨p, μR, hroot, ?_⟩
    rw [ENNReal.ofReal_one, one_smul] at hq
    rw [ENNReal.ofReal_inv_of_pos hθpos]
    exact quot_scale_lemma_2 hq (ENNReal.ofReal_pos.mpr hθpos).ne' ENNReal.ofReal_ne_top
  refine ⟨fun τ => gamP C u u' w' τ, fun _ => thetaP u u' hB (J2of Y u u' ν (toPts w')) w',
    fun τ => ENNReal.ofReal (thetaP u u' hB (J2of Y u u' ν (toPts w')) w')⁻¹ • nu1P C u u' w' τ,
    fun τ => ⟨hR w' hrow hrep τ, hT w' hrow hpos, hsc τ⟩, ?_⟩
  set θ0 := thetaP u u' hB (J2of Y u u' ν (toPts w')) w' with hθdef
  set J2 := J2of Y u u' ν (toPts w') with hJ2def
  have hfac : ∀ τ, hsNormSq ((AX hB u u' τ).J (ENNReal.ofReal θ0⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ)) =
      θ0⁻¹ * θ0⁻¹ * hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ)) := fun τ => by
    show hsNormSq ((locS hB u u' τ).J (ENNReal.ofReal θ0⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ)) = _
    rw [Formalism.L2.SG.Pf.LTL.locJ_smul, Formalism.L2.SG.Pf.LTL.hsNormSq_smul, Complex.normSq_ofReal,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hθpos.le)]
  have hpow : θ0 ^ (2 * Fintype.card D.what₂.Tau) = localAmplitudeProduct u u' hB w' / J2 := by
    rw [hθ0, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hP1 hpos).le]
    have : (1 : ℝ) / (2 * Fintype.card D.what₂.Tau) * ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  have hprod : ∏ τ, (θ0⁻¹ * θ0⁻¹ * hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ))) = J2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    change (θ0⁻¹ * θ0⁻¹) ^ Fintype.card D.what₂.Tau * localAmplitudeProduct u u' hB w' = J2
    have e : (θ0⁻¹ * θ0⁻¹) ^ Fintype.card D.what₂.Tau = (θ0 ^ (2 * Fintype.card D.what₂.Tau))⁻¹ := by
      rw [← mul_inv, ← pow_two, inv_pow, ← pow_mul]
    rw [e, hpow, inv_div, div_mul_cancel₀ _ hP1.ne']
  rw [ENNReal.ofReal_one, one_mul]
  simp only [hfac]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun τ _ => by
    have := Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ))
    positivity), hprod]

end Cut

section Steps

open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants NumberField
  Formalism.L2.SG.Pf.MainEqCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Steps

end Formalism.L2.SG.Pf.BDatR
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopsFinal

namespace Formalism.L2.SG.Pf.LoopBFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))

theorem rowLat_fl' {u u' : D.what₂.Word} (t : D.s.Term u u') :
    IsRowLat D (fl'Of W hI t).fl (lamOf W hI t) := by
  have hR := rowLat_map (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) (W.δ u) (W.isom u) (X.Fu u) _ (rowLat_tc hI t)
  have hFx := fixedC W hI (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) t
  obtain ⟨hLift, -, hOK⟩ := pdC W hI t
  exact ⟨hR.1, ⟨hFx.1, hFx.2.1, ⟨hLift.1, rfl⟩, hOK.1⟩, hOK.2⟩

theorem frameChangeAt_holds : FrameChangeAt W hI := by
  intro u u' t ξ hl hd
  obtain ⟨n, hn, hnf⟩ := Formalism.L2.S.Pv.ClassCounting.frameOpFull D u' (fl'Of W hI t).fl (lamOf W hI t) (rowLat_fl' W hI t) ξ hl hd
  exact ⟨n, hn, fun b => hnf b⟩

theorem frameChangeC_holds : FrameChangeC := fun _ _ _ _ hI W => frameChangeAt_holds W hI

end Formalism.L2.SG.Pf.LoopBFrame
end
end
