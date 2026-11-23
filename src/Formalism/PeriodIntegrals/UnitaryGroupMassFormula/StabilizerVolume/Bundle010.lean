module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldAbsAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Unimod
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gram_orbit_equiv {a : ℕ} (X0 : Fin a → Fin M → E)
    (hW : ∀ X : Fin a → Fin M → E, gramE σ J X = gramE σ J X0 →
      ∃ g ∈ Formalism.UG.UJ (σ : E →+* E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i) = X i) :
    ∃ e : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} ≃
        orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
      ∀ X, (e X : Fin a → Fin M → AF F ⊗[F] E) = ratTup (F := F) (AF F) (X : Fin a → Fin M → E) := by
  let f : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} →
      orbS (GamA σ J) (ratTup (F := F) (AF F) X0) := fun X =>
    ⟨ratTup (F := F) (AF F) (X : Fin a → Fin M → E), by
      obtain ⟨g, hg, hgX⟩ := hW X X.2
      refine ⟨ratElA σ J g hg, ratElA_mem σ J g hg, ?_⟩
      rw [ratElA_smul]
      congr 1
      funext i
      exact hgX i⟩
  have hinj : Function.Injective f := fun X X' h =>
    Subtype.ext (ratTup_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, ⟨γ, hγ, rfl⟩⟩
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1
      (Subgroup.mem_subgroupOf.1 (show (show HR (AF F) σ J from γ) ∈ HFinIn (AF F) σ J from hγ))
    have hγe : γ = ratElA σ J g hg := Subtype.ext hgγ.symm
    have hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E) = J := hg
    refine ⟨⟨fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i), ?_⟩, ?_⟩
    · show gramE σ J _ = gramE σ J X0
      ext i j
      show Formalism.UG.hform (σ : E →+* E) J _ _ = Formalism.UG.hform (σ : E →+* E) J _ _
      rw [Formalism.UG.P.hform_mulVec, hg']
    · apply Subtype.ext
      show ratTup (F := F) (AF F) _ = γ • ratTup (F := F) (AF F) X0
      rw [hγe, ratElA_smul]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun X => rfl⟩

end Main

section Of

theorem unfold_of (hW : Witt) (hFT : FinTheta) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp) :
    Unfold := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C
    𝓕' h𝓕' φ hφ0 hadm hθ
  haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ'.IsHaarMeasure := hμ'H
  haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ
  haveI : μ'.IsInvInvariant :=
    (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2 ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J
  obtain ⟨e, he⟩ := gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)
  have hsub : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) ⊆
      Set.range (fun γ : (GamA σ J) =>
        (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) X0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  haveI hcO : Countable (orbS (GamA σ J)
      (ratTup (F := F) (AF F) X0)) := ((Set.countable_range _).mono hsub).to_subtype
  have hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F := F) (AF F) X0) := by
    have := hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm
    have h2 := Complex.measurable_re.comp this
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have hint : Integrable (fun X => (φ X : ℂ)) νX := by
    obtain ⟨d, b, Φinf, Φf, Φv, h1, h2, h3, h4⟩ := id hadm
    obtain ⟨⟨μinf, hμinf⟩, k1⟩ := hν.2
    obtain ⟨⟨νinf, hνinf⟩, k2⟩ := k1 μinf hμinf
    obtain ⟨⟨μv, hμv⟩, k3⟩ := k2 νinf hνinf
    obtain ⟨⟨νv, hνv⟩, k4⟩ := k3 μv hμv
    obtain ⟨⟨fI, hfI⟩, k5⟩ := k4 νv hνv
    obtain ⟨⟨fV, hfV⟩, k6⟩ := k5 fI hfI
    exact (k6 fV hfV d b _ Φinf Φf Φv h1 h2 h3 h4).1
  have hφae : AEMeasurable φ νX := by
    have h2 := Complex.measurable_re.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have key : ∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ =
      μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX :=
    unfold_abs (Γ := GamA σ J) (H := stabT (AF F) σ J X0) μ μ' (ratTup (F := F) (AF F) X0) (fun k => MulAction.mem_stabilizer_iff) νX
      (fun X => ENNReal.ofReal (φ X)) hφae.ennreal_ofReal hmφ.ennreal_ofReal hμ'C.1 hμ'C.2 𝓕 h𝓕 𝓕' h𝓕'
  have hθS : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) =
      ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by
    intro h
    rw [← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    exact tsum_congr fun X => by rw [he X]
  have hfin : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ≠ ⊤ := by
    intro h
    have hF := hFT F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet (fun X => (φ X : ℂ)) hadm h
    rw [hθS h]
    refine ENNReal.tsum_coe_ne_top_iff_summable.2 (summable_of_hasFiniteSupport ?_)
    refine (hF.preimage Subtype.val_injective.injOn).subset ?_
    intro X hX
    simp only [Function.mem_support] at hX
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Ne, Complex.ofReal_eq_zero]
    intro hz
    apply hX
    change φ (h⁻¹ • ratTup (AF F) (X : Fin a → Fin M → E)) = 0 at hz
    simp [hz]
  have hθm : Measurable fun h : HA (AF F) σ J => ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) := by
    refine Measurable.tsum fun x => ?_
    have hx : (fun h : HA (AF F) σ J => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))) =
        fun h => ENNReal.ofReal (φ ((h⁻¹ * repO _ _ x) • ratTup (F := F) (AF F) X0)) := by
      funext h
      rw [mul_smul, repO_smul]
    rw [hx]
    exact (hmφ.comp (measurable_inv.mul_const _)).ennreal_ofReal
  have hθeq : ∀ h, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h =
      (((∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
        ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))).toReal : ℝ) : ℂ) := by
    intro h
    unfold thetaS
    rw [← Complex.ofReal_tsum, hθS h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1
    exact tsum_congr fun X => (ENNReal.toReal_ofReal (hφ0 _)).symm
  have hI1 : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ =
      (((∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ).toReal
          : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hθeq), integral_complex_ofReal,
      integral_toReal hθm.aemeasurable (Filter.Eventually.of_forall fun h => (hfin h).lt_top)]
  have hI2 : ∫ X, (φ X : ℂ) ∂νX = (((∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      hφae.aestronglyMeasurable]
  rw [hI1] at hθ ⊢
  rw [hI2, key]
  rw [key] at hθ
  have hL0 : (μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal ≠ 0 := fun h0 => hθ (by rw [h0]; simp)
  have hR0 : ∫⁻ X, ENNReal.ofReal (φ X) ∂νX ≠ 0 := fun h => hL0 (by simp [h])
  have hμ'top : μ' 𝓕' ≠ ⊤ := fun h => hL0 (by rw [h, ENNReal.top_mul hR0]; simp)
  refine ⟨hμ'top, ?_⟩
  rw [ENNReal.toReal_mul, Complex.ofReal_mul, Complex.real_smul]

end Of

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

section Abstract

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

theorem orb_cont (x0 : X) (hc : Continuous fun g : G => g • x0) :
    Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
  rw [(QuotientGroup.isQuotientMap_mk (MulAction.stabilizer G x0)).continuous_iff]
  have : ((fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ∘ QuotientGroup.mk) =
      fun g => g • x0 := funext (orb_mk x0)
  rw [this]
  exact hc

theorem orb_inj (x0 : X) :
    Function.Injective (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
  intro q q' h
  simp only at h
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    MulAction.mem_stabilizer_iff, mul_smul, ← h, inv_smul_smul]

end Abstract

def LCSCPolish : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] [SecondCountableTopology Y],
    PolishSpace Y

def SecCtblW : Prop := InCtx fun F E _ _ _ _ _ _σ _M _J _a _X0 _hT =>
  SecondCountableTopology (AF F ⊗[F] E)

theorem stabClosed_holds : StabClosed := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hmat : Continuous (fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0) := by
    show Continuous (fun g : HA (AF F) σ J => actTup (AF F) (HA.mat (AF F) σ J g) (ratTup (F := F) (AF F) X0))
    unfold actTup
    exact continuous_pi fun i => hmat.matrix_mulVec continuous_const
  exact isClosed_eq hcont continuous_const

theorem smul_ratTup_cont (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) {a : ℕ}
    (X0 : Fin a → Fin M → E) :
    Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0) := by
  have hmat : Continuous (fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  show Continuous (fun g : HA (AF F) σ J => actTup (AF F) (HA.mat (AF F) σ J g) (ratTup (F := F) (AF F) X0))
  unfold actTup
  exact continuous_pi fun i => hmat.matrix_mulVec continuous_const

theorem secCtblG_of (hW : SecCtblW) : SecCtblG := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (GL (Fin M) (AF F ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have h2 : SecondCountableTopology (HR (AF F) σ J) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact h2

theorem orbEmb_of (hW : SecCtblW) (hP : LCSCPolish) : OrbEmb := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have := secCtblG_of hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))
  have : IsClosed ((MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0) : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) :=
    stabClosed_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : PolishSpace (HA (AF F) σ J) := hP _
  have : PolishSpace (HA (AF F) σ J ⧸ MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0)) := hP _
  have : BorelSpace (HA (AF F) σ J ⧸ MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0)) := CosetSpace.borelSpace
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hcont := orb_cont (G := HA (AF F) σ J) (ratTup (F := F) (AF F) X0)
    (smul_ratTup_cont F E σ M J X0)
  exact ⟨hcont.measurableEmbedding (orb_inj _), hcont⟩

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem us_exists_open (μ : Measure G) [IsHaarMeasure μ] :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ U⁻¹ = U ∧ 0 < μ U ∧ μ U < ⊤ := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set U := interior V ∩ (interior V)⁻¹ with hUdef
  have h1 : (1 : G) ∈ U := ⟨mem_interior_iff_mem_nhds.2 hV1,
    by rw [Set.mem_inv, inv_one]; exact mem_interior_iff_mem_nhds.2 hV1⟩
  have hUo : IsOpen U := isOpen_interior.inter isOpen_interior.inv
  refine ⟨U, hUo, h1, ?_, hUo.measure_pos μ ⟨1, h1⟩, ?_⟩
  · rw [hUdef, Set.inter_inv, inv_inv, inter_comm]
  · exact lt_of_le_of_lt (measure_mono (inter_subset_left.trans interior_subset))
      hVc.measure_lt_top

theorem us_invInv [SigmaCompactSpace G] (μ : Measure G) [IsHaarMeasure μ]
    [IsMulRightInvariant μ] : IsInvInvariant μ := by
  have hc : μ.inv = haarScalarFactor μ.inv μ • μ := um_eq_smul_of_sigmaCompact _ _
  obtain ⟨U, hUo, -, hUi, hpos, hfin⟩ := us_exists_open μ
  have h : μ.inv U = μ U := by rw [Measure.inv_apply, hUi]
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hc1 : haarScalarFactor μ.inv μ = 1 := by
    have : ((haarScalarFactor μ.inv μ : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h
    exact_mod_cast this
  exact ⟨by rw [hc, hc1, one_smul]⟩

theorem us_rightInv_of_compat (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ]
    {S : Type*} [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
    [T2Space S] [MeasurableSpace S] [BorelSpace S] [SigmaCompactSpace S] (ι : S →* G)
    (μ' : Measure S) [IsHaarMeasure μ'] {Y : Type*} [MeasurableSpace Y] (νX : Measure Y)
    (s : Y → G)
    (hcompat : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * ι h') ∂μ' ∂νX) :
    IsMulRightInvariant μ' := by
  obtain ⟨U, hUo, -, -, hpos, hfin⟩ := us_exists_open μ
  set f : G → ℝ≥0∞ := U.indicator 1 with hfdef
  have hfm : Measurable f := measurable_one.indicator hUo.measurableSet
  have hI : ∫⁻ g, f g ∂μ = μ U := lintegral_indicator_one hUo.measurableSet
  refine ⟨fun k => ?_⟩
  set c := haarScalarFactor (map (· * k) μ') μ' with hcdef
  have hc : map (· * k) μ' = c • μ' := um_eq_smul_of_sigmaCompact _ _
  have h1 := hcompat (fun g => f (g * ι k)) (hfm.comp (measurable_mul_const _))
  rw [lintegral_mul_right_eq_self f (ι k)] at h1
  have hin : ∀ y, ∫⁻ h', f (s y * ι h' * ι k) ∂μ' = c * ∫⁻ h', f (s y * ι h') ∂μ' := by
    intro y
    have e1 : (fun h' => f (s y * ι h' * ι k)) = fun h' => f (s y * ι (h' * k)) := by
      funext h'
      rw [map_mul, mul_assoc]
    rw [e1]
    have e2 := lintegral_map_equiv (μ := μ') (fun h' => f (s y * ι h')) (MeasurableEquiv.mulRight k)
    have e3 : (⇑(MeasurableEquiv.mulRight k) : S → S) = (· * k) := rfl
    rw [e3, hc, lintegral_smul_measure] at e2
    rw [← e2]
    rfl
  simp_rw [hin] at h1
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← hcompat f hfm, hI] at h1
  have hc1 : c = 1 := by
    have : (c : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h1.symm
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end Gen

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem us_isClosed_stab (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (X0 : Fin a → Fin M → E) :
    IsClosed ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) := by
  have hcont : Continuous fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0 := by
    show Continuous fun g : HA (AF F) σ J =>
      actTup (AF F) (HA.mat (AF F) σ J g) (ratTup (F := F) (AF F) X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR (AF F) σ J => (g : GL (Fin M) (AF F ⊗[F] E)))
  have : ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) =
      {g | g • ratTup (F := F) (AF F) X0 = ratTup (F := F) (AF F) X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

def InvG : Prop := InCtx fun F E _ _ _ _ _ σ M J _a _X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → μ.IsInvInvariant

def InvS : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
      μ'.IsInvInvariant

theorem unimodStab_holds : UnimodStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ _ μ hμ νX _ μ' hμ' hC
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y) →
      s y • ratTup (F := F) (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  exact us_rightInv_of_compat μ (stabT (AF F) σ J X0).subtype μ' νX s
    (fun f hf => hC.2 f hf s hs)

theorem invG_holds : InvG := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 _a ha1 ha2 X0 hT hdet μ hμ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 _a ha1 ha2 X0 hT hdet μ hμ
  exact us_invInv μ

theorem invS_holds : InvS := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ' hC
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  have : IsMulRightInvariant μ' :=
    unimodStab_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ' hC
  exact us_invInv μ'

theorem invInv_holds : InvInv := fun F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet =>
  ⟨invG_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet,
    invS_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet⟩

end Spec

end PI.VolStabS
end
end
