module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle253
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1828
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle558
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVacFix

open GlobalTheory.Hk3 GlobalTheory.WeilParts GlobalTheory.IdemSupport

variable {D : D7}

theorem infPart_eq_one {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) {x : AE D}
    (hx : f * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := of_isPrimeIdem hΦ h
  have h1 := congrArg (infPart D) hx
  rw [RingHom.map_mul, (place_comp hΦ hε).1, zero_mul, RingHom.map_sub, RingHom.map_one, eq_comm, sub_eq_zero] at h1
  exact h1

theorem exists_nonSplit {P : Pl D.host.E} (hP : Formalism.DivisionValues.conjPl P = P) :
    ∃ v ε, NonSplitAt D v ε ∧ ∀ e f, IsPrimeIdem P e f →
      e = algebraMap (AF D.host.F) (AE D) ε ∧ f = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hc : P = cP P := by
    refine (isConjPl_iff P P).1 fun c hc => ⟨cO D c, ?_, rfl⟩
    have h1 : cO D c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have hd : IsDelta Φ P (algebraMap (AF D.host.F) (AE D) ε) :=
    ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩
  refine ⟨_, ε, ⟨hε, ?_⟩, fun e f h => ?_⟩
  · rintro ⟨e, ⟨e1, e2, -⟩, e3⟩
    have key : ∀ a : AE D, a * a = a → algebraMap (AF D.host.F) (AE D) ε * a = a → Φ a P ≠ 0 → IsDelta Φ P a :=
      fun a a1 a2 a3 => ⟨by rw [← a2, RingHom.map_mul, h0, zero_mul],
        mul_left_cancel₀ a3 (by rw [← ev_mul, a1, mul_one]),
        fun Q hQ => by rw [← a2, ev_mul, hd.2.2 Q hQ, zero_mul]⟩
    have e1' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, e1]
    have hz : Φ e P * Φ (cA D e) P = 0 := by rw [← ev_mul, e2, ev_zero]
    have hs : Φ e P + Φ (cA D e) P = 1 := by rw [← ev_add, e3, hd.2.1]
    by_cases h : Φ e P = 0
    · have a := key (cA D e) e1' (by rw [← e3]; linear_combination e1' + e2)
        (by rw [h, zero_add] at hs; rw [hs]; exact one_ne_zero)
      have b := delta_conj hΦ a
      rw [cA_cA, ← hc] at b
      exact zero_ne_one (h.symm.trans b.2.1)
    · have a := key e e1 (by rw [← e3]; linear_combination e1 + e2) h
      have b := delta_conj hΦ a
      rw [← hc] at b
      rw [a.2.1, b.2.1, one_mul] at hz
      exact one_ne_zero hz
  · obtain ⟨k1, ε', k2, k3⟩ := of_isPrimeIdem hΦ h
    exact ⟨delta_unique hΦ k1 hd, by rw [k3, placeIdem_unique k2 hε]⟩

theorem isHalf_of_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun w => w = v) : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  intro i j
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := FiniteAdeleRing.ext _ fun w => by
      change evalV D.host.F w (β * α) = evalV D.host.F w α
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => exact mul_zero _
  | add x x' _ _ h h' => rw [Matrix.add_apply, mul_add, h, h']
  | neg x _ h => rw [Matrix.neg_apply, mul_neg, h]

theorem vacFix_of_unrPl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E) (hW : IsWeilDatumO ψ S T χS χT om)
    (uS : UnrPl P χS) (uT : UnrPl P χT) : VacFix ψ om P := by
  by_cases hP : Formalism.DivisionValues.conjPl P = P
  swap
  · exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace ψ S T χS χT om P hW hP uS uT).1
  obtain ⟨v, ε, hv, hu⟩ := exists_nonSplit hP
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨e, e', he⟩ := exists_isPrimeIdem hΦ P
  obtain ⟨rfl, rfl⟩ := hu e e' he
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  rintro f hf k ⟨hk, a, a', ha, sk⟩ k' ⟨hk', b, b', hb, sk'⟩
  rw [(hu a a' ha).2] at sk
  rw [(hu b b' hb).2] at sk'
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
    χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv (uS _ _ he) (uT _ _ he) k k' sk sk'
    (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
      (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) v ε hv.1 k k'
      (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hk.2.1) (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hk'.2.1))
    f hf.1 fun u hu => hf.2 _ _ he u
      (by
        rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hu
        exact GlobalTheory.PlaceModel.latO_le_top _ hu)
      (Or.inl (isHalf_of_mem hv.1 hu))

theorem unr_and_vacFix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → ∀ f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.UnrPl P μ' ∧ GlobalTheory.Hk3.UnrPl P (μ' * η'⁻¹) ∧ GlobalTheory.Hk3.VacFix R.ψ ω P := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hc i σ μ' η' H ω hW f₀ f B _ P hP
  have h0 := (GlobalTheory.T.splittingCharacters_unramified_offLevels R F hc.lev A.μ0 P hP).2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have h1 : UnrPl P μ' := fun e f h x a b c => by
    refine (H.mu_cond x ⟨infPart_eq_one h a, b, c⟩).2 ?_
    have h2 : R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = 1 := h0 e f h x a b c
    rwa [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hc.lev.xi_base ▸ hc.lev.xi A.μ0) x, mul_one] at h2
  have h2 : UnrPl P (μ' * η'⁻¹) := fun e f h x a b c => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1 e f h x a b c, H.eta_unr x (infPart_eq_one h a) b c, inv_one, mul_one]
  exact ⟨h1, h2, vacFix_of_unrPl _ _ _ _ _ ω P hW h1 h2⟩

end GlobalTheory.ConjVacFix

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

open GlobalTheory.ThetaTransform

noncomputable section

namespace GlobalTheory.LineDerivTransfer

theorem hasDerivAt_heisV_of {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) (hΦ'm : Φ' ∈ GlobalTheory.WeilM.schA F (Fin N)) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (hΦ'd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0) (w : VA F N) :
    HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := GlobalTheory.ThetaDeriv.decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ :=
    GlobalTheory.ThetaDeriv.decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (GlobalTheory.SWQ.rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (GlobalTheory.SWQ.rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (GlobalTheory.SWQ.rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (GlobalTheory.ThetaDeriv.hasDerivAt_schr hF ψ hM hΦ'd (GlobalTheory.SWQ.rat ξ + w.1) t).const_mul (ph ξ))
    (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this

theorem thV_smul {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (c : ℂ) (Φ : (Fin N → AF F) → ℂ) : thV ψ (c • Φ) = c • thV ψ Φ := by
  funext w
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

end GlobalTheory.LineDerivTransfer


open GlobalTheory.LineDerivTransfer in
theorem GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  intro D ψ hψ S T JB ξ hB κ _ co hrat Φ hΦ L L' hL hL0 hL' hL0' c hrel x
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  let e := numCoord co σ
  have he : ∀ w w', symplO S T w w' = symV (e w) (e w') := fun w w' => by
    rw [symplO_eq_symp rfl hB, co.form]
    simp only [e, symV, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
  obtain ⟨-, -, hfin, -⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank _ e
  have hc : Continuous e := (GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank _ e).1
  have hΦσ := comp_mem_schA σ hΦ
  have key : ∀ L : ℝ →+ WO S T, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∃ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin (Fintype.card κ)),
        (∀ x, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) (Φ' (x ∘ σ.symm)) 0) ∧
        (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
          thV ψ Φ' ∘ e := by
    intro L hL hL0
    have hM : IsRealLine (e.toLinearMap.toAddMonoidHom.comp L) := ⟨hc.comp hL, fun t => (hfin _).1 (hL0 t)⟩
    obtain ⟨Φ', hm, hd⟩ := GlobalTheory.ThetaDeriv.exists_deriv_schr hR ψ hψ.1 hM hΦσ
    refine ⟨Φ', hm, fun x => ?_, funext fun w => ?_⟩
    · have h : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) =
          fun t => GlobalTheory.WeilM.schr ψ (e.toLinearMap.toAddMonoidHom.comp L t) (fun y => Φ (y ∘ σ)) (x ∘ σ.symm) := by
        funext t
        simp only [GlobalTheory.WeilM.schr, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          LinearEquiv.coe_coe, e, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
        congr 2
        funext i
        simp
      rw [h]
      exact hd _
    · rw [thetaTr_eq co σ]
      have h : (fun t : ℝ => heisO ψ S T (L t) (thV ψ (fun y => Φ (y ∘ σ)) ∘ e) w) =
          fun t => heisV ψ (e.toLinearMap.toAddMonoidHom.comp L t) (thV ψ (fun y => Φ (y ∘ σ))) (e w) :=
        funext fun t => congrFun (heisO_comp he (L t) _) w
      rw [show numCoord co σ = e from rfl, h]
      exact (hasDerivAt_heisV_of ψ hR hψ.1 hΦσ hm hM hd (e w)).deriv
  obtain ⟨Φ₁, hm₁, hd₁, hh₁⟩ := key L hL hL0
  obtain ⟨Φ₂, hm₂, hd₂, hh₂⟩ := key L' hL' hL0'
  rw [hh₁, hh₂] at hrel
  have h2 : thV ψ Φ₂ = thV ψ (c • Φ₁) := by
    rw [thV_smul]
    funext v
    obtain ⟨w, rfl⟩ := e.surjective v
    exact congrFun hrel w
  have h3 := thV_injOn hR hψ.1 hm₂ (Submodule.smul_mem _ c hm₁) h2
  rw [(hd₂ x).deriv, (hd₁ x).deriv, h3]
  rfl
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.AdjCoord

variable {D : D7} {v : FinPl D}

def conjProj (φ : SplitProj D v) : SplitProj D v :=
  φ.comp (Algebra.TensorProduct.map (AlgHom.id (Fv D.host.F v) (Fv D.host.F v)) D.sp.cm.sig)

theorem rdA_conjProj (φ : SplitProj D v) (a : AE D) : rdA (conjProj φ) a = rdA φ (cA D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul x y =>
    simp only [rdA, conjProj, RingHom.comp_apply, cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, GlobalTheory.AdelicU.compFin,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy => simp only [_root_.map_add (f := _), hx, hy]

theorem isIdemOf_conjProj {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : IsIdemOf (conjProj φ) (cA D e) := by
  have hcc : ∀ x : AE D, cA D (cA D x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul a y =>
      simp only [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      congr 1
      exact star_star y
    | add x y hx hy => simp only [_root_.map_add (f := _), hx, hy]
  refine ⟨GlobalTheory.SplitScalar.isSplitIdem_conj he.1, ?_, ?_⟩
  · rw [hcc, add_comm]; exact he.2.1
  · rw [rdA_conjProj, hcc]; exact he.2.2

def trHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ}
    (A A' : Matrix (Fin n) (Fin n) K) (B B' : Matrix (Fin m) (Fin m) K) (hA : A' * A = 1) (hB : B * B' = 1) :
    Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin n) (Fin m) K where
  toFun y := A * yᵀ * B
  invFun z := (A' * z * B')ᵀ
  left_inv y := by
    have : A' * (A * yᵀ * B) * B' = (A' * A) * yᵀ * (B * B') := by simp only [Matrix.mul_assoc]
    simp only [this, hA, hB, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_transpose]
  right_inv z := by
    have : A * (A' * z * B') * B = (A * A') * z * (B' * B) := by simp only [Matrix.mul_assoc]
    simp only [Matrix.transpose_transpose, this, mul_eq_one_comm.1 hA, mul_eq_one_comm.1 hB, Matrix.one_mul,
      Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const
  continuous_invFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_transpose

theorem isCoord_comp {S T : HSp D} {m n : ℕ} {a : AE D} {Λ : AddSubgroup (WO S T)}
    {κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)} (h : IsCoord a Λ κ)
    (A A' : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (B B' : Matrix (Fin m) (Fin m) (Fv D.host.F v))
    (hA : A' * A = 1) (hB : B * B' = 1) : IsCoord a Λ (fun t => A * (κ t)ᵀ * B) := by
  have e : (fun t => A * (κ t)ᵀ * B) = ⇑(trHomeo A A' B B' hA hB) ∘ κ := rfl
  refine ⟨fun x y => ?_, ?_, ?_, ?_⟩
  · simp only [h.1 x y, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  · rw [e]; exact (Set.bijOn_univ.2 (trHomeo A A' B B' hA hB).bijective).comp h.2.1
  · rw [e, Set.image_comp]; exact (trHomeo A A' B B' hA hB).isOpenMap _ h.2.2.1
  · rw [e, Set.image_comp]; exact h.2.2.2.image (trHomeo A A' B B' hA hB).continuous

theorem gram_inv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  exact Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)

theorem adj_mul {A : Type} [CommRing A] (σ : A →+* A) {a b : ℕ} (G G' k k' : Matrix (Fin a) (Fin a) A)
    (H m m' : Matrix (Fin b) (Fin b) A) (x : Matrix (Fin b) (Fin a) A) (h1 : G' * G = 1)
    (hk : Formalism.UG.cT σ k * G * k = G) (hm : Formalism.UG.cT σ m * H * m = H) (hk' : k * k' = 1) (hm' : m * m' = 1) :
    G' * Formalism.UG.cT σ (m * x * k) * H = k' * (G' * Formalism.UG.cT σ x * H) * m' := by
  have hG : G * G' = 1 := mul_eq_one_comm.1 h1
  have s1 : Formalism.UG.cT σ k * G = G * k' := calc
    Formalism.UG.cT σ k * G = Formalism.UG.cT σ k * G * (k * k') := by rw [hk', Matrix.mul_one]
    _ = (Formalism.UG.cT σ k * G * k) * k' := by simp only [Matrix.mul_assoc]
    _ = G * k' := by rw [hk]
  have e1 : G' * Formalism.UG.cT σ k = k' * G' := calc
    G' * Formalism.UG.cT σ k = G' * (Formalism.UG.cT σ k * (G * G')) := by rw [hG, Matrix.mul_one]
    _ = G' * ((Formalism.UG.cT σ k * G) * G') := by simp only [Matrix.mul_assoc]
    _ = (G' * G) * k' * G' := by rw [s1]; simp only [Matrix.mul_assoc]
    _ = k' * G' := by rw [h1, Matrix.one_mul]
  have e2 : Formalism.UG.cT σ m * H = H * m' := calc
    Formalism.UG.cT σ m * H = Formalism.UG.cT σ m * H * (m * m') := by rw [hm', Matrix.mul_one]
    _ = (Formalism.UG.cT σ m * H * m) * m' := by simp only [Matrix.mul_assoc]
    _ = H * m' := by rw [hm]
  unfold Formalism.UG.cT at *
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc G' * ((k.map σ)ᵀ * ((x.map σ)ᵀ * (m.map σ)ᵀ)) * H
      = (G' * (k.map σ)ᵀ) * (x.map σ)ᵀ * ((m.map σ)ᵀ * H) := by simp only [Matrix.mul_assoc]
    _ = k' * (G' * (x.map σ)ᵀ * H) * m' := by rw [e1, e2]; simp only [Matrix.mul_assoc]

theorem map_mul_conj {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {a b : ℕ} (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (k : Matrix (Fin a) (Fin a) A) (m : Matrix (Fin b) (Fin b) A) (X Y : Matrix (Fin a) (Fin b) A) (h : Y = k * X * m) :
    (P⁻¹).val * Y.map π * Q.val =
      ((P⁻¹).val * k.map π * P.val) * ((P⁻¹).val * X.map π * Q.val) * ((Q⁻¹).val * m.map π * Q.val) := by
  subst h
  simp only [Matrix.map_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  first
  | rw [Units.mul_inv_cancel_left]
  | rw [← Matrix.mul_assoc (P : Matrix (Fin a) (Fin a) K), Units.mul_inv, Matrix.one_mul]

theorem mt_mul_mt_inv (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← _root_.map_mul, _root_.mul_inv_cancel, _root_.map_one, Units.val_one]

theorem grpCo_val (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g).val = (B⁻¹).val * (Formalism.L2.Theta.mt V g).map (rdA φ) * B.val := rfl

theorem grpCo_inv (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g)⁻¹ = grpCo φ V B g⁻¹ := by
  simp only [grpCo, _root_.mul_inv_rev, _root_.inv_inv, _root_.map_inv, _root_.mul_assoc]

theorem adjCo_actO (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (g : GA D S) (h : GA D T) (t : WO S T) :
    adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  have hm' : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simpa only [_root_.inv_inv] using mt_mul_mt_inv T h⁻¹
  have key := adj_mul (cA D) (S.gram.map (incA D)) ((S.gram⁻¹).map (incA D)) (Formalism.L2.Theta.mt S g)
    (Formalism.L2.Theta.mt S g⁻¹) (T.gram.map (incA D)) (Formalism.L2.Theta.mt T h⁻¹) (Formalism.L2.Theta.mt T h)
    (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (gram_inv_mul S) (by exact g.2) (by exact h⁻¹.2)
    (mt_mul_mt_inv S g) hm'
  unfold Formalism.UG.cT at key
  have hact : (actO S T g⁻¹ h⁻¹ t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      Formalism.L2.Theta.mt T h⁻¹ * t * Formalism.L2.Theta.mt S g := by
    first
    | rfl
    | (simp only [actO, _root_.inv_inv]; done)
    | simp [actO]
  unfold adjCo
  rw [hact, key, map_mul_conj (rdA φ) BS BT (Formalism.L2.Theta.mt S g⁻¹) (Formalism.L2.Theta.mt T h) _ _ rfl, grpCo_inv,
    grpCo_val, grpCo_val]

end GlobalTheory.PlaceTensor.AdjCoord

namespace GlobalTheory.PlaceTensor

open AdjCoord

theorem adjCo_isCoord : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord (cA D e) (latO S T ΛS ΛT fun _ => True) (adjCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  refine ⟨?_, fun g h t => adjCo_actO φ S T BS BT g h t⟩
  have hc := (GlobalTheory.T.splitPlace_matrix_coordinate_on_half D S T ΛS ΛT hS hT v (conjProj φ) (cA D e) (isIdemOf_conjProj he) 1 1).1
  have h1 : ((S.gram⁻¹).map (incA D)).map (rdA φ) * (S.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have h2 : ((T.gram⁻¹).map (incA D)).map (rdA φ) * (T.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have hA : ((S.gram.map (incA D)).map (rdA φ) * BS.val) * ((BS⁻¹).val * ((S.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BS.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h1
  have hB : ((T.gram.map (incA D)).map (rdA φ) * BT.val) * ((BT⁻¹).val * ((T.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h2
  convert isCoord_comp hc _ _ _ _ hA hB using 1
  funext t
  have ht : (((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ).map (rdA φ) =
      ((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (rdA (conjProj φ)))ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, rdA_conjProj]
  simp only [adjCo, mapCo, Matrix.map_mul, ht, _root_.inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc]

end GlobalTheory.PlaceTensor

end
end
