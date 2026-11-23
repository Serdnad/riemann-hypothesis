module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle090
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle107
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle071
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle111
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShape
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle110
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle108
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004

@[expose] public section

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotDiscrete


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  have h1 : μ.inv = Measure.haarScalarFactor μ.inv μ • μ :=
    Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c := Measure.haarScalarFactor μ.inv μ with hc
  have h2 : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [← h1]
      _ = c • μ.inv := by
          ext s _
          simp [Measure.inv_apply]
      _ = (c * c) • μ := by rw [h1, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K < ∞ := hK.measure_lt_top
  have h3 : ((c * c : NNReal) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [h2]
    rfl
  have h4 : ((c * c : NNReal) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h3
  have h5 : ((c : ℝ) * c) = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  exact ⟨by rw [h1, h6, one_smul]⟩


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.QuotDiscrete.existsUnique_subgroupOf {G : Type} [Group G] {Γ H : Subgroup G} (hΓ : Γ ≤ H) {F : Set G}
    (hF : ∀ x : G, ∃! γ : Γ, γ • x ∈ F) (g : G) (h : H) :
    ∃! γ : Γ.subgroupOf H, γ • h ∈ {h : H | (h : G) * g ∈ F} := by
  obtain ⟨γ, hγ, huniq⟩ := hF (h * g)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at hγ ⊢
    simpa [mul_assoc] using hγ
  · intro δ hδ
    have hδ' : (⟨((δ : H) : G), Subgroup.mem_subgroupOf.1 δ.2⟩ : Γ) • ((h : G) * g) ∈ F := by
      simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at hδ ⊢
      simpa [mul_assoc] using hδ
    have := huniq _ hδ'
    have h2 : ((δ : H) : G) = (γ : G) := congrArg Subtype.val this
    exact Subtype.ext (Subtype.ext h2)


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.QuotDiscrete.discreteClause : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.DiscreteClause := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.DiscreteClause
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ hH hG hHu dg _ ν _ μ hμ hQ Γ hΓ hd
  haveI : Countable Γ := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  haveI : Countable (Γ.subgroupOf H) :=
    Countable.of_equiv _ (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv.symm
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ν.IsMulRightInvariant := hHu ν inferInstance
  haveI : ν.IsInvInvariant := _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant ν
  haveI : dg.IsMulRightInvariant := hG dg inferInstance
  haveI : dg.IsInvInvariant := _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant dg
  obtain ⟨F, hFm, hF⟩ := _root_.GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hFg : ∀ g : G, MeasurableSet {h : H | (h : G) * g ∈ F} := fun g =>
    hFm.preimage (measurable_subtype_coe.mul_const g)
  have hFD : IsFundamentalDomain Γ F dg := IsFundamentalDomain.mk' hFm.nullMeasurableSet hF
  have hFD' : ∀ g : G, IsFundamentalDomain (Γ.subgroupOf H) {h : H | (h : G) * g ∈ F} ν :=
    fun g => IsFundamentalDomain.mk' (hFg g).nullMeasurableSet
      (_root_.GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓ hF g)
  refine ⟨⟨F, hFm, hFD⟩, ⟨_, hFg 1, hFD' 1⟩, ?_⟩
  intro D D' hD hD' f hf hinv
  have hFi : Measurable (F.indicator f) := hf.indicator hFm
  have hK : Measurable (fun x : G => F.indicator f x⁻¹) := hFi.comp measurable_inv
  obtain ⟨hcm, hcint⟩ := hQ _ hK
  have he : Continuous (QuotientGroup.quotientRightRelEquivQuotientLeftRel H) := by
    refine (Topology.IsQuotientMap.continuous_iff isQuotientMap_quotient_mk').2 ?_
    have hc : Continuous fun g : G => ((g⁻¹ : G) : G ⧸ H) :=
      continuous_quotient_mk'.comp continuous_inv
    exact hc
  refine ⟨fun q => _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H q), hcm.comp he.measurable, ?_, ?_⟩
  · intro g
    show _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹) ((g⁻¹ : G) : G ⧸ H) = _
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk]
    calc ∫⁻ h : H, F.indicator f (g⁻¹ * (h : G))⁻¹ ∂ν = ∫⁻ h : H, F.indicator f ((h : G) * g) ∂ν := by
          rw [← lintegral_inv_eq_self (μ := ν) (fun h : H => F.indicator f ((h : G) * g))]
          congr 1
          funext h
          simp [mul_inv_rev]
      _ = ∫⁻ h in {h : H | (h : G) * g ∈ F}, f ((h : G) * g) ∂ν := by
          rw [← lintegral_indicator (hFg g)]
          congr 1
      _ = ∫⁻ h in D', f ((h : G) * g) ∂ν := by
          refine (hFD' g).setLIntegral_eq hD' (fun h : H => f ((h : G) * g)) (fun γ h => ?_)
          simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
          exact hinv _ (Subgroup.mem_subgroupOf.1 γ.2) _
  · unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.rightMeasure
    calc ∫⁻ x in D, f x ∂dg = ∫⁻ x in F, f x ∂dg :=
          hD.setLIntegral_eq hFD f (fun γ x => hinv _ γ.2 x)
      _ = ∫⁻ x, F.indicator f x ∂dg := (lintegral_indicator hFm f).symm
      _ = ∫⁻ x, F.indicator f x⁻¹ ∂dg := (lintegral_inv_eq_self (μ := dg) (F.indicator f)).symm
      _ = ∫⁻ q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹) q ∂μ := hcint
      _ = ∫⁻ q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹)
            (QuotientGroup.quotientRightRelEquivQuotientLeftRel H (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H q)) ∂μ := by
          congr 1
          funext q
          rw [show _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H q =
            (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm q from rfl,
            Equiv.apply_symm_apply]
      _ = _ := (lintegral_map (hcm.comp he.measurable)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.continuous_invCoset H).measurable).symm

end GlobalTheory.QuotDiscrete
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalUnitaryDomains

theorem isDiscreteWithDomains_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [hc : Countable Γ] [hd : DiscreteTopology Γ] : IsDiscreteWithDomains Γ := by
  refine ⟨hc, hd, fun μ _ => ?_⟩
  obtain ⟨𝓕, hF, h⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  exact ⟨𝓕, hF, IsFundamentalDomain.mk' hF.nullMeasurableSet h⟩

theorem isDiscreteWithDomains_ratPts' (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have : Countable (ratPts (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have : DiscreteTopology (ratPts (AF F) σ J) := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  exact isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) :=
  fun F E _ _ _ _ _ σ _ M J _ => isDiscreteWithDomains_ratPts' F E σ M J

end GlobalTheory.RationalUnitaryDomains
end

section


theorem _root_.GlobalTheory.T.stabSelfDualLattice_transitive_on_length : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  first | exact @GlobalTheory.StabOrbit.stabTransitive | exact GlobalTheory.StabOrbit.stabTransitive | (intros; apply GlobalTheory.StabOrbit.stabTransitive <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.primesInProgressions_relativeError : GlobalTheory.Lin.PrimesRel := by
  first | exact @GlobalTheory.Lin.primesRel_holds | exact GlobalTheory.Lin.primesRel_holds | (intros; apply GlobalTheory.Lin.primesRel_holds <;> assumption)
end

section

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  first | exact @GlobalTheory.MomTrans.latInt_translate | exact GlobalTheory.MomTrans.latInt_translate | (intros; apply GlobalTheory.MomTrans.latInt_translate <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_numAt :
    SzRow (fun C D L => HostArith D.host → Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  refine szRow_and_imp.2 _ _ (szRow_and_imp.1 _ _ (szRow_and_imp.1 _ _ explicitConstants_parameterConditions_large szRow_blockLengthParams)
    (szRow_and_imp.1 _ _ szRow_sizesAt szRow_band_lambda_primes)) ?_
  rintro C cD ch D L hC hV ⟨⟨h5, hT⟩, hS, hrho, hLa, hg, hp, hp', hTT, hCode⟩ hA
  obtain ⟨P, hPK, hPW⟩ := h5 hA
  obtain ⟨T, hTK, hTe⟩ := hT P hPW
  have hCt : C.Ct = 401 := hC.1.2.2.2.2.2.2.2.2.2
  obtain ⟨hn, hm, hk, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, -, hLw, hcc, -⟩ := hV.host
  refine ⟨⟨{ params := P
             params_K := hPK
             CnW_eq := hPW
             parT := T
             parT_K := hTK
             eP_eq := hTe
             sizes := hS
             rho_le := hrho
             CGam_eq := hV.CGam_eq
             Cc_eq := hV.Cc_eq
             Ct_eq := hV.Ct_eq
             secondConstant_eq := hV.secondConstant_eq
             LaG_ge := hLa
             bT_le := hV.bT_le
             ccK_top := hcc
             g_le := hg
             pde_lt := ⟨hp, hp'⟩
             logFiveDepth_eq := hV.logFiveDepth_eq
             Lw_eq := ?_
             cloud1 := fun τ τ' => ?_
             win := ⟨hn, hm, hk⟩ }⟩, hTT, hCode⟩
  · rw [hLw, hCt]; unfold Lwv; norm_num
  · funext i
    rw [hV.hc.1 τ i, hV.hc.1 τ' i]

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.KerT

theorem ratStep_of_chTh_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i < R.m → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i (i + 1) := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A _ _ _ _ _ _ hL _ hT hi
  have hq := Formalism.L2.Ker.muqTie_of_ok Ch sel mu cst L hL
  have hm := hL.hm
  have key : ∀ j, (j = i + 1 ∧ i ≤ m2) ∨ (j = R.m ∧ i = m2 + 1) → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i j := by
    intro j hj
    unfold RatStep
    rw [← Formalism.L2.Ker.stepC_eq_stepT W Ch sel mu cst hq A u i hi]
    rcases hj with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
    · intro γ γ' N fr N' fr' c x h'
      exact (hT.th i h).equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
    · intro γ γ' N fr N' fr' c x h'
      exact hT.top.equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
  exact key _ (by omega)

end GlobalTheory.KerT
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.moments_translate_rationalPoint_unitDenominator : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]), X.Ok → A.LaHyp a b ∅ → A.AA ≠ ⊥ → A.ESmooth a b → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → IsSdLat N → IsSdLat N' → PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E)) → ∀ (t : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * (ϖ : X.E)) • t ∈ per A N N' → (∀ m, jetC A.cD (Wx A t (A.e a b N N')) m ∈ TaylorLogMetric.Qbar) ∧ InIntClosure (per A N N' : Set (HomE X.E a b)) (ptTab ι un) Set.univ fun m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A t (A.e a b N N')) m) := by
  first | exact @GlobalTheory.MomT.UnitTr.moments_unit_translate | exact GlobalTheory.MomT.UnitTr.moments_unit_translate | (intros; apply GlobalTheory.MomT.UnitTr.moments_unit_translate <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.exists_lift_halfLattice_rational : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), A.AA.FG → A.AA ≠ ⊥ → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∃ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') := by
  first | exact @GlobalTheory.MomT.exists_lift_halfAO | exact GlobalTheory.MomT.exists_lift_halfAO | (intros; apply GlobalTheory.MomT.exists_lift_halfAO <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.theta_movedCosetIndicator_vacuum_shape : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), X.Ok → A.LaHyp a b S → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∃ n : ℕ, n ≠ 0 ∧ n ∣ (halfBO S (per A N N') c).toAddSubgroup.relIndex (per A N N').toAddSubgroup ∧ ∀ x ∈ divLat cA (homAt S N N'), ∀ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') → ∀ R : Finset (HomE X.E a b), IsReps (per A N N').toAddSubgroup (halfBO S (per A N N') c).toAddSubgroup R → A.thInd S N N' c x = fun z => (n : ℂ)⁻¹ * Wx A (-t) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) z := by
  first | exact @GlobalTheory.MomT.ThShape.thInd_shape | exact GlobalTheory.MomT.ThShape.thInd_shape | (intros; apply GlobalTheory.MomT.ThShape.thInd_shape <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem natW_alcove_bound (p : ℕ) (N : ℕ) (lam : DomWeight N)
    (hl : ∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) :
    ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 ∧ lam.natW ⟨0, h⟩ + (N - 1) ≤ p := by
  intro h
  obtain ⟨_, h2, h3⟩ := factNatW N lam
  refine ⟨h3 h, ?_⟩
  have e0 := h2 ⟨0, h⟩
  have e1 := h2 ⟨N - 1, by omega⟩
  rw [h3 h] at e1
  by_cases hN1 : N = 1
  · subst hN1
    have : (⟨0, h⟩ : Fin 1) = ⟨1 - 1, by omega⟩ := rfl
    rw [this, h3 h]
    omega
  · have hlt : (⟨0, h⟩ : Fin N) < ⟨N - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    have := hl _ _ hlt
    simp only at this
    have hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    push_cast at this
    omega

theorem inducedSimpleLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  intro p hp k _ _ N lam hl
  have hN := factNatW N lam
  have hne : nablaSq k N lam ≠ ⊥ := by
    intro h
    have hm : hw k le_rfl lam.natW ∈ nablaSq k N lam := hwMem k N N le_rfl _ hN.1
    rw [h, Submodule.mem_bot] at hm
    exact hwNe k N N le_rfl _ hm
  refine ⟨hne, fun M hM hG => ?_⟩
  by_contra hc
  push_neg at hc
  have key := GlobalTheory.T.highestWeightVector_mem_of_lt_stable_dualWeyl p hp k N lam.natW hN.1 (natW_alcove_bound p N lam hl)
  have good := GlobalTheory.T.isRowOperatorStable_dualWeyl_and_GLSubmodules k N lam
  have h1 := (key ⊥ M (good_top_bot k N N).2 (good.2 M hG) (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) (good.2 M hG) good.1 (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.Alc
end
