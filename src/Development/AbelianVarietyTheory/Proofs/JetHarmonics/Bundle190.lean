module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle167
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle185
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMul
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle188
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle160
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralC
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfFormalBiextension
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle065
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubstOneVariableUncurryEqSubst
public import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
import Formalism.LocalToGlobal.CharacterGerms.Bundle007
public import Formalism.LocalToGlobal.CharacterGerms.Bundle026
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle108
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle182
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle135
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle180
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle189
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem supply_pairs : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → (∀ o, (Even d ∧ ∀ s : ZMod d, (lab.big o 0 s ↔ Even s.val)) ∨ ∀ s, lab.big o 0 s) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → Supply V d Orb Finset.univ lab.n (lab.j + lab.j') lab.big (fun o g s => Dw.mult (lab.tau o g s)) (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) nW ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb _ d _ lab ha hsurj hr hj hdich a hdom nW ν hν
  have hg : LabGeo C3 ι Y lab :=
    GlobalTheory.LabelledDirections.labGeoSt E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha
  have hnd : NDG Y := GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY
  have Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V := fun o =>
    FBChart.hyps GlobalTheory.cartHyp_of_formalBiextension axesFB GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.2 Y (pairOfLab ha hg o)
      (rankHyp_ofLab ha hg hr o)
      (GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal.2 C V (𝓞 E) _ Y d _ (pairOfLab ha hg o) hnd (rankHyp_ofLab ha hg hr o) _)
      (GlobalTheory.T.characterBound_pairs_of_places_integralChart hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl Orb d lab ha hg hr o _)
  have hfl := fun o => GlobalTheory.flag_of_numbering C V d (fun _ => ZMod d) (fun g s => Dw.mult (lab.tau o g s))
    (fun _ => Equiv.refl _) (JJ (lab.II Dw o)) (RF.rd Y (pairOfLab ha hg) Hy o) (fun _ _ => rfl)
  have hrk : ∀ o g s, (RF.rd Y (pairOfLab ha hg) Hy o).rkF g s = Dw.mult (lab.tau o g s) := fun o => (hfl o).1
  choose F hF using fun o => (hfl o).2
  refine ⟨fun o => lab.II Dw o, fun o => JJ (lab.II Dw o), inferInstance, inferInstance,
    fun o => RF.rd Y (pairOfLab ha hg) Hy o, F, fun o => ⟨rfl, rfl⟩, fun o _ g s => ⟨Iff.rfl, hrk o g s⟩, ?_⟩
  refine RF.valBlocks_of_nuPlE Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) nW F Finset.univ _ ν
    (hν.trans (GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw lv Xo c T io y C3 C V ι hι k Y hY a nW))
    (pairsSep_ofLab ha hg) (GlobalTheory.RowVal.value_eq_prod C V (𝓞 E) _ Y d Orb _ (pairOfLab ha hg) Hy _ nW) GlobalTheory.JetProd.jetProd
    (GlobalTheory.T.blockProd_mem_chartFamily_at_place_pairs E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hsurj hr hj Hy F
      (fun o g s q => (hF o g s q).2) a hdom nW) ?_
  refine RF.blkAdm _ F Finset.univ _ (fun o _ => hdich o) (fun _ _ => hj) fun o _ g s q hq => ?_
  rw [hrk]
  by_contra hc
  exact hq (by unfold gap; rw [if_neg fun h => hc h.2])

end GlobalTheory.RowAt
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthPrimeToLevel

theorem isUnit_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h1 := RPfVal.vLa_int_not_mem la hN
  have h2 : (((N : ℕ) : 𝓞 K) : K) = (N : K) := map_natCast (algebraMap (𝓞 K) K) N
  rw [h2] at h1
  have h3 := ho.2 (N : K)
  rw [h1, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
  have hx : algebraMap S.V S.Fr (N : S.V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact_mod_cast hN0
  have hne := valV_ne_zero (V := S.V) hx
  have h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1 := by
    unfold vV at h3
    rw [← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]
  unfold valV at h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h4
  by_contra hu
  exact h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)

theorem rootDiscriminantDegreeRatio_pos (D : D7) : 0 < rr0 D := by
  unfold rr0
  have h1 : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have h2 : (0 : ℝ) < Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
  positivity

theorem err_le (R N n Dg Φ φ c e g₀ g₁ : ℝ) (hR : 0 < R) (hN : 0 < N) (hn : 0 ≤ n) (he : 0 < e) (hg₀ : 0 < g₀)
    (hg₁ : 1 ≤ g₁) (hΦ0 : 0 ≤ Φ) (hΦ : Φ ≤ e * (R * N ^ 3 * φ))
    (hc : R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g₀ ≤ c) : Dg ^ 2 * Φ / (g₀ * g₁) / e ≤ c * φ := by
  have hφ : 0 ≤ φ := by
    have h1 : 0 ≤ (e * (R * N ^ 3)) * φ := by nlinarith
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hc hφ)
  calc Dg ^ 2 * Φ / (g₀ * g₁) / e ≤ Dg ^ 2 * (e * (R * N ^ 3 * φ)) / (g₀ * 1) / e := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ := by field_simp
    _ ≤ _ := by
      have h1 : 0 ≤ N ^ 4 * n := by positivity
      have h2 : 0 ≤ N ^ 3 := by positivity
      gcongr
      linarith

theorem depth_le : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro D T h j hj hinj EX w c _ hrun la hg y
  letI := T.Q.H.starRing
  obtain ⟨hlp, hn, h4, hc0, hc⟩ := hrun
  obtain ⟨S, io, e, ho, z, hz, hl, C, Pu, hC, hPu, hval⟩ := GlobalTheory.T.exists_uniformisedModel_integralChart_at_point D T h j hj la y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io z C Pu ϖ hϖ
  obtain ⟨r, Φ, M0, ⟨hΦ0, b, hb1, hb2⟩, -, hM0, hjm, hΦ⟩ :=
    GlobalTheory.T.exists_short_basis_uniformization_lattice D T h j hj la S io e ho z hz (imgV y) hl C Pu ϖ hϖ Q hQ
  have hΦ' : Φ ≤ e * (rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * (recPJ h j hj).phiC la y) := hΦ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T.toCore h.toLawsCore.toLawsM EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := level_M T.toCore h.toLawsCore.toLawsM
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨st, hn⟩ := h.nabPin j hj
    have := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
    subst this
    exact hn
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S.V) := by
    refine isUnit_natCast la S _ e ho _ ?_
    rw [hM, Nat.cast_mul]
    intro hm
    rcases la.isPrime.mem_or_mem hm with h1 | h1
    · exact hg 0 h1
    · exact hg 1 h1
  have hf1 : 1 ≤ D.R.f := by
    have h1 := GlobalTheory.DepthLink.finrank_host D
    have h2 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hm2 := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ w.n := le_trans (Nat.mul_pos (by omega) hr1) hn
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ D.host.g 0 * D.host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by rw [hM]; exact_mod_cast hle
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hDM : (WeightAlgebra.DF w : ℝ) * M0 < (T.Q.l.M : ℕ) := by
    rcases lt_or_ge j D.R.m with hjm' | hjm'
    · exact ((mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg _)).trans_lt (hc hjm' 0).1).trans_le hle'
    · rw [(hjm hjm').1, mul_zero]; linarith
  have hnum : (WeightAlgebra.DF w : ℝ) ^ 2 * Φ / (T.Q.l.M : ℕ) / e ≤ c * (recPJ h j hj).phiC la y := by
    rcases lt_or_ge j D.R.m with hjm' | hjm'
    · rw [hM, Nat.cast_mul]
      have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
      have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
      exact err_le (rr0 D) _ w.n _ Φ _ c e _ _ (rootDiscriminantDegreeRatio_pos D) (by positivity) (Nat.cast_nonneg _) he' (by linarith)
        (by linarith) hΦ0 hΦ' (hc hjm' 0).2
    · unfold WeightAlgebra.PJ.phiC
      rw [(hjm hjm').2, if_neg (not_lt.2 hjm')]
      simp
  have hA := GlobalTheory.T.iInf_theta_generators_le_local_depth_prime_to_level _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (h.thTot j hj) S io z C hC
    Pu hPu hz ϖ hϖ Q hQ Φ M0 r b hΦ0 hb1 hb2 α hα1 hα2 hMu (wtA w) w.n (WeightAlgebra.DF w) e hn1 ho.1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.DF_wtA_le _ _) (by rw [hM]; exact (h4 0).trans hle) hDM
  have hB := (GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts D T h j hj w hn la).2.2.2.2 S io e ho z hz C
  have hsW := RPfVal.vAdd_sW (recB h.toLawsCore) hinj EX w la hg
  have hs0 : sWt (recB h.toLawsCore) hinj EX w ≠ 0 := by
    refine mul_ne_zero (fun h0 => RPfVal.nnW_not_mem (recB h.toLawsCore) hinj EX w la hg ?_) ?_
    · rw [h0]; exact la.asIdeal.zero_mem
    · have hq : D.host.q.Prime := D.host.hyp.1
      have hd : D.host.d.Prime := D.host.hyp.2.1
      exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
        (pow_ne_zero _ hd.ne_zero))
  have hdep : (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤
      (⨅ f ∈ T.th j w, nval S.V e (evI z f)) + (((ramOverZ la : ℝ) * clOf w la : ℝ) : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← hval w f hf, add_comm]
    refine (GlobalTheory.T.thetaDepth_le_scaled_rule_value D T h j hj w hlp _ hs0 la y f hf).trans (le_of_eq ?_)
    exact congrArg (fun x : ℝ => (x : EReal) + vAtV y f) hsW
  have hnu : nusOf (recB h.toLawsCore) w (nuWt T w) la =
      (ramOverZ la : ℝ) * nuWt T w la + (ramOverZ la : ℝ) * clOf w la := by
    unfold nusOf
    rw [dite_eq_right (fun ⟨i, hi⟩ => hg i hi), ← mul_add, ← H1algLink.eWL_eq la]
    rfl
  refine hdep.trans ?_
  rw [hnu, add_right_comm, EReal.coe_add, EReal.coe_add]
  exact add_le_add (hA.trans (add_le_add hB (EReal.coe_le_coe_iff.2 hnum))) le_rfl

end GlobalTheory.DepthPrimeToLevel
end
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelAction_shortThetaSeries_rootOfUnity_mul : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ) (hj : InR D j), (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) → ∀ (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → ∀ (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.toTop.sh j w, ∃ (u : 𝓞 T.Q.c.F) (f' : T.R j), f' ∈ T.toTop.sh j w ∧ actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f = (u : T.Q.c.F) • f' := by
  first | exact @GlobalTheory.ShortMove.actLev_short | exact GlobalTheory.ShortMove.actLev_short | (intros; apply GlobalTheory.ShortMove.actLev_short <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integralChartDepth_le_residueChar_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ¬ IsUnit ((p : ℕ) : T.V) → UpperTheory.Depth.SplitAt H.d p → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuLocC Ch e k a n ≤ (((vV T.V ((p : ℕ) : T.Fr) : ℝ) / (e : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_over_two | exact GlobalTheory.CharDepth.nuLocC_le_over_two | (intros; apply GlobalTheory.CharDepth.nuLocC_le_over_two <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZero_cutoff_eq_bigCell_integral : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re = ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) := by
  first | exact @GlobalTheory.TopVec.levelZero_cut_eq_integral_Ew | exact GlobalTheory.TopVec.levelZero_cut_eq_integral_Ew | (intros; apply GlobalTheory.TopVec.levelZero_cut_eq_integral_Ew <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.bigCell_integral_topDensity_eq_levelZero : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c) → ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) = (p.RR f 0 w [] []).re := by
  first | exact @GlobalTheory.TopVec.integral_topDensity_eq_levelZero | exact GlobalTheory.TopVec.integral_topDensity_eq_levelZero | (intros; apply GlobalTheory.TopVec.integral_topDensity_eq_levelZero <;> assumption)
end
