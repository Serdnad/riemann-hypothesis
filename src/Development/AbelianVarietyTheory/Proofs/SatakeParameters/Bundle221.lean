module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle206
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle204
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle152
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle001
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
public import Formalism.LocalToGlobal.InertKernelTheory.KernelDifferenceOfFrame
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelMoveDegree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

noncomputable section

namespace GlobalTheory.FrobOpsIdx
open Polynomial

theorem frobOpsIdx : SphOps → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (Kw : Levels E a) (W0 : Set (HeightOneSpectrum (𝓞 E))), (∀ w ∈ W0, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ Kw w = GlobalTheory.LFun.KGL w (n := a)) → ∃ (J : Type) (T : LocOps l ι Kw J) (x fr : J → _root_.Formalism.ConjugateSelfDual.G E Ω) (n : J → ℕ), (∀ j, x j = (fr j)⁻¹ ^ n j) ∧ (∀ j, T.pl j ∈ W0 ∧ ∃ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A (T.pl j) ∧ IsFrob A (normV (T.pl j)) (fr j)) ∧ (∀ w ∈ W0, ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ s : _root_.Formalism.ConjugateSelfDual.G E Ω, IsFrob A (normV w) s → ∃ j, T.pl j = w ∧ fr j = s ∧ n j = 1) ∧ (∀ j g, ∃ q : ℚ, T.f j g = q) ∧ (∀ (j : J) (σ : SmIrr (GL (Fin a) ((T.pl j).adicCompletion E))), GlobalTheory.PRep.fixed σ.ρ (Kw (T.pl j)) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL (T.pl j) σ.ρ B → ∀ ρ : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), ((ρ (fr j)⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV (T.pl j)) B).map fun b => Polynomial.X - Polynomial.C b).prod → ι.symm (T.z j σ) = trc ρ (x j)) ∧ ∀ w ∈ W0, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), (∀ j (h : T.pl j = w), trc r (x j) = ι.symm (T.z j (h ▸ σ))) → ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ s : _root_.Formalism.ConjugateSelfDual.G E Ω, IsFrob A (normV w) s → ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro hS E Ω _ _ _ _ _ _ l _ ι a Kw W0 hW
  classical
  have hl : l.Prime := Fact.out
  let J : Type := {p : HeightOneSpectrum (𝓞 E) × ValuationSubring Ω × _root_.Formalism.ConjugateSelfDual.G E Ω × ℕ //
    p.1 ∈ W0 ∧ _root_.Formalism.ConjugateSelfDual.IsPlaceOver p.2.1 p.1 ∧ IsFrob p.2.1 (normV p.1) p.2.2.1 ∧ 1 ≤ p.2.2.2}
  have hf : ∀ j : J, ∃ f : GL (Fin a) (j.1.1.adicCompletion E) →₀ ℂ,
      (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV j.1.1 : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 (n := a)),
          opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ ((j.1.2.2.2 : ℕ) : ℤ))).sum • v :=
    fun j => (hS E j.1.1 a).2 (j.1.2.2.2 : ℤ)
  let zz : ∀ j : J, SmIrr (GL (Fin a) (j.1.1.adicCompletion E)) → ℂ := fun j σ =>
    if h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B then
      ((UpperTheory.V.Af.algSat a (normV j.1.1) h.choose).map (· ^ j.1.2.2.2)).sum else 0
  have hz : ∀ (j : J) (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ),
      GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B → zz j σ = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ j.1.2.2.2)).sum := by
    intro j σ B hB
    have h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B := ⟨B, hB⟩
    simp only [zz, dif_pos h]
    rw [show h.choose = B from h.choose_spec.unique hB]
  let T : LocOps l ι Kw J :=
    { pl := fun j => j.1.1
      split := fun j => (hW _ j.2.1).1
      away := fun j => (hW _ j.2.1).2.1
      f := fun j => (hf j).choose
      int := fun j g => by
        obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
        rw [he]
        exact GlobalTheory.FrobOps.norm_le_one ι m _ e (GlobalTheory.FrobOps.not_dvd_normV hl _ (hW _ j.2.1).2.1)
      z := zz
      act := fun j σ v hv => by
        rw [(hW _ j.2.1).2.2] at hv
        by_cases h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B
        · obtain ⟨B, hB⟩ := h
          rw [hz j σ B hB, (hf j).choose_spec.2 σ B hB v hv]
          simp only [zpow_natCast]
        · have h0 : PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 (n := a)) = ⊥ := by
            by_contra hne
            exact h ((hS E j.1.1 a).1 σ hne)
          rw [h0, Submodule.mem_bot] at hv
          subst hv
          simp [opOf] }
  let fr : J → _root_.Formalism.ConjugateSelfDual.G E Ω := fun j => j.1.2.2.1
  let nn : J → ℕ := fun j => j.1.2.2.2
  let x : J → _root_.Formalism.ConjugateSelfDual.G E Ω := fun j => (fr j)⁻¹ ^ nn j
  refine ⟨J, T, x, fr, nn, fun j => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨j.2.1, j.1.2.1, j.2.2.1, j.2.2.2.1⟩
  · intro w hw A hA s hsF
    exact ⟨⟨(w, A, s, 1), hw, hA, hsF, le_rfl⟩, rfl, rfl, rfl⟩
  · intro j g
    obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
    refine ⟨(m : ℚ) / ((normV j.1.1 : ℕ) : ℚ) ^ e, ?_⟩
    show (hf j).choose g = _
    rw [he]
    push_cast
    rfl
  · intro j σ _ B hB ρ hFE
    show ι.symm (zz j σ) = trc ρ (x j)
    rw [hz j σ B hB]
    apply ι.injective
    rw [RingEquiv.apply_symm_apply, GlobalTheory.FrobOps.iota_trc]
    exact (GlobalTheory.FrobOps.trace_pow_of_charpoly _ _ (by rw [Matrix.charpoly_map]; exact hFE) _).symm
  · intro w hw σ _ B hBσ r hr A hA s hsF
    rw [← Matrix.charpoly_map]
    refine GlobalTheory.CharpolyNewton.charpoly_eq_prod_of_trace_pow ℂ a _ _ ?_ ?_
    · simp [UpperTheory.V.Af.algSat, hBσ.card]
    · intro n hn
      let j : J := ⟨(w, A, s, n), hw, hA, hsF, hn⟩
      have h2 : trc r (x j) = ι.symm (zz j σ) := hr j rfl
      rw [hz j σ B hBσ] at h2
      rw [← GlobalTheory.FrobOps.iota_trc]
      change ι (trc r (x j)) = _
      rw [h2, RingEquiv.apply_symm_apply]

end GlobalTheory.FrobOpsIdx
end
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SegSumOne

theorem segSum_of_mono0 : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))), (segSum rc l).mono0 →
      (∀ Δ ∈ l, Δ.len = 1) ∧ segSum rc l = sumList (l.map fun Δ => rc Δ.first) := by
  intro E Ω _ _ _ _ _ A w h rc hrc l hm
  obtain ⟨a, ha, H⟩ := hrc
  have hlen : ∀ Δ ∈ l, Δ.len = 1 := by
    intro Δ hΔ
    have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
      rw [← H.nu]; exact (H.cusp _ (Δ.isCusp_first.nu _))
    have hmi : (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).mono0 :=
      GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm _ (List.mem_map.2 ⟨Δ, hΔ, rfl⟩)
    have hpos := Δ.len_pos
    by_contra hne
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by omega) hmi
  refine ⟨hlen, ?_⟩
  unfold segSum
  congr 1
  refine List.map_congr_left fun Δ hΔ => ?_
  rw [hlen Δ hΔ, GlobalTheory.SegLen.lpChar_lpSp_one']
  simp [WD.lpTw_zero]

end GlobalTheory.SegSumOne
end

section

noncomputable section

namespace GlobalTheory.ShortModelTie

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.KerInert.BeCob
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.DworkPowerSeriesWeights (Integral)
open GlobalTheory.CurveDictionary (lgF_eq_logF cc_lgF')

theorem X_mul_lU {K : Type} [Field K] [CharZero K] (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.X * Formalism.L2.Th1.B.lU f = f := by
  ext n
  cases n with
  | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]

theorem integral_ps {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, _root_.GlobalTheory.CurveDictionary.cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [_root_.GlobalTheory.CurveDictionary.lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem phTie : Formalism.L2.KerInert.BeCob.PhTie := by
  intro l _ g hLT hOk s2 hph
  have hp : l.Prime := Fact.out
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := _root_.GlobalTheory.CurveDictionary.cc_lgF' _ _
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  set v := vLT hLT with hvdef
  have hvcc : PowerSeries.constantCoeff v = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  set lW := Formalism.L2.Th1.A.logSer g.W with hlWdef
  have hgl : g.l = lW := Formalism.L2.KerInert.Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff lW = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hlW1 : PowerSeries.coeff 1 lW = 1 := (Formalism.L2.Th1.A.logSpec ℂ_[l] g.W).2.1
  have hvl : PowerSeries.subst v lW = PowerSeries.C e⁻¹ * Lc := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  set P := Formalism.L2.Th1.A.wpReg g.W with hPdef
  have hP : Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)) = P := by
    rw [GlobalTheory.CurveDictionary.wpReg_eq, hPdef, GlobalTheory.CurveDictionary.wpReg_eq g.W, (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.1,
      (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.2.1]
  have hneg : ∀ f : PowerSeries ℂ_[l], PowerSeries.subst v (-f) = -PowerSeries.subst v f := fun f => by
    rw [← PowerSeries.coe_substAlgHom hvS, map_neg]
  have hlU1 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW) = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hlW1]
  set U := PowerSeries.subst v (Formalism.L2.Th1.B.lU lW) with hU
  have hψ : psiLT hLT = -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog U := by
    unfold psiLT
    rw [hph]
    unfold Formalism.L2.Th1.B.phW Formalism.L2.Th1.B.phO
    rw [PowerSeries.subst_sub hvS, PowerSeries.subst_add hvS, hneg, PowerSeries.subst_mul hvS,
      PowerSeries.subst_pow hvS, PowerSeries.subst_C, hvl,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
    have hfl : PowerSeries.subst v (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU lW)) = Formalism.L2.Th1.B.fLog U := by
      rw [hU, PowerSeries.subst_def, PowerSeries.subst_def]
      exact Formalism.L2.Th1.B.subst_fLog (fun _ => hvcc) hlU1
    rw [← hfl]
    rfl
  have hFF : phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU Lc) := by
    unfold phFF
    rw [hP]

  have hvU : v * U = PowerSeries.C e⁻¹ * Lc := by
    have h1 : PowerSeries.subst v (PowerSeries.X * Formalism.L2.Th1.B.lU lW) = v * U := by
      rw [PowerSeries.subst_mul hvS, PowerSeries.subst_X hvS]
    rw [← h1, X_mul_lU lW hlW0, hvl]
  have hprod : Formalism.L2.Th1.B.lU Lc = (PowerSeries.C e * Formalism.L2.Th1.B.lU v) * U := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ_[l]))
    rw [X_mul_lU Lc hL0]
    calc Lc = PowerSeries.C e * (PowerSeries.C e⁻¹ * Lc) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hene, map_one, one_mul]
      _ = PowerSeries.C e * (v * U) := by rw [hvU]
      _ = PowerSeries.X * (PowerSeries.C e * Formalism.L2.Th1.B.lU v * U) := by
          rw [show PowerSeries.C e * (v * U) = PowerSeries.C e * ((PowerSeries.X * Formalism.L2.Th1.B.lU v) * U) by
            rw [X_mul_lU v hvcc]]
          ring

  have hex1 : PowerSeries.coeff 1 g.ex = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hinv
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hex, Formalism.L2.G.Pend.coeff_one_l g hOk.2.1, one_mul,
      PowerSeries.coeff_one_X] at h
    exact h
  have hv1 : PowerSeries.coeff 1 v = e⁻¹ := by
    rw [hvdef]
    unfold vLT
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hv0, hex1, one_mul, PowerSeries.coeff_C_mul,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hp.two_le, mul_one]
  have hA : MvPowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hv1, mul_inv_cancel₀ hene]
  have hLU : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU Lc) = 1 := Formalism.L2.Th1.E.Joints.cc_lU hp.two_le
  have hUc : MvPowerSeries.constantCoeff (U : MvPowerSeries Unit ℂ_[l]) = 1 := by
    have h := congrArg PowerSeries.constantCoeff hprod
    rw [hLU, map_mul] at h
    have hA' : PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1 := hA
    rw [hA', one_mul] at h
    exact h.symm
  have hdiff : (psiLT hLT : MvPowerSeries Unit ℂ_[l]) -
      phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      Formalism.L2.Th1.B.fLog (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) := by
    rw [hψ, hFF, hprod, Formalism.L2.Th1.B.ParO.fLog_mul hA hUc]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdiff]; exact Formalism.L2.Th1.B.constantCoeff_fLog hA
  · rw [hdiff]
    show Integral (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog _))
    rw [Formalism.L2.Th1.B.fExp_fLog hA]
    apply integral_ps
    intro k
    rw [PowerSeries.coeff_C_mul, norm_mul, he1, one_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]
    exact v_integral hOk hLT (k + 1)

end GlobalTheory.ShortModelTie
end
end

section

noncomputable section

namespace GlobalTheory.CobExactProof

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.KerInert.BeCob (eLT vLT psiLT)
open GlobalTheory.CurveDictionary (map_cob lgF_eq_logF cc_lgF')

theorem cobExact : Formalism.L2.KerInert.BeCob.CobExact := by
  apply _root_.Formalism.L2.KerInert.BeCob.coboundary_exact <;> assumption

end GlobalTheory.CobExactProof
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem polD_eq_map_polDY (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    GL3Theta.polD D s Q y' =
      MvPolynomial.map (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q) := by
  set v : GL3Theta.FrV D N' → ℂ := fun k => y' k.1 k.2.1 k.2.2
  have hmap : ∀ P : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ),
      MvPolynomial.map (MvPolynomial.eval v) P = MvPolynomial.mapAlgHom (MvPolynomial.aeval v) P := fun P => rfl
  rw [hmap]
  unfold GL3Theta.polD polDY
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun k => ?_

  rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.mapAlgHom_apply]
  split_ifs with h
  · simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.C_mul]
    simp [v]
  · simp

theorem applyFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame := by
  intro D N N' s Q G y'
  rw [polD_eq_map_polDY]
  unfold GL3Theta.applyAt0 framePol GL3Theta.evFr

  rw [map_sum]
  symm
  rw [← Finset.sum_subset (MvPolynomial.support_map_subset
    (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q))]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.eval_C, mul_assoc]
  · intro α _ hα
    rw [MvPolynomial.notMem_support_iff] at hα
    rw [MvPolynomial.coeff_map] at hα
    rw [map_mul, hα, zero_mul]

theorem entQFrame : Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ i c Q c' y'
  unfold Formalism.L2.KerInert.SecondKernelDifference.entQ
  rw [applyFrame]
  rfl

theorem applyFrame_and_entQFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame :=
  ⟨applyFrame, entQFrame⟩

end GlobalTheory.TwV.DelA
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem polDY_exp_deg : ∀ (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → ∀ α ∈ (polDY D s Q (N' := N')).support, ∀ τ, ∑ b, ∑ a, α (τ, b, a) = ∑ r, ν τ r := by
  intro D N N' s ν Q hQ α hα τ
  exact Formalism.L2.KerInert.SecondKernelMoveDegree.difference_polynomial_degree D N N' s ν Q hQ α hα τ

end GlobalTheory.TwV.DelA
end
