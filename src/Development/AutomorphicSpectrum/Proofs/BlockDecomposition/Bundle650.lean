module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle692
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle635
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle328
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle327
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle368
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilConv

theorem absThetaInt_le_of_meets_orbits (D : D7) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {n : ℕ}
    (φ : Mx D V.rank n → ℂ) (hφ : Continuous φ) (S : Set (GA D V)) (hS : MeasurableSet S)
    (hcov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) : absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  have hinv := leftInv_absTheta V φ
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) ν := isFundamentalDomain_stdDom _ ν
  have e : absThetaInt V ν φ = ∫⁻ g in stdDom (GQ V), absTheta V φ g ∂ν := by
    unfold absThetaInt
    show ∫⁻ q, descend (GQ V) (absTheta V φ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
    rw [GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure hfd]
    exact lintegral_congr fun g => congrFun hinv.lift_descend g
  rw [e]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν hfd hS hcov (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) hinv

end GlobalTheory.CompanionTheory.WeilConv

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ


theorem _root_.GlobalTheory.T.archimedean_siegel_weil_integral_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
  ∀ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch P →
    Integrable (starLoc (Ainf F) σ J (psiInf F ψ) μ P) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_starLoc_inf | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_starLoc_inf | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_starLoc_inf <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.rational_character_kernel_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∀ N : ℕ, 0 < N → ∀ D : ℕ, 0 < D → (∀ f : F,
      (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f) →
    ∃ t : F, t ≠ 0 ∧ ∀ w : E, (∀ x : Af F ⊗[F] E, InNOh b N x →
        psiFin F ψ (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F) w)) = 1) →
      ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = t • w := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test <;> assumption)
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

theorem lintegral_sq_le_of_average {G Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (F : Set G) (hF : IsFundamentalDomain Γ F μ)
    (ν : Measure Y) (b : Y → ℝ≥0∞) (hb : Measurable b) (hmass : ∫⁻ y, b y ∂ν = 1)
    (k : Y → G) (hk : Continuous k) (f : G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (s : G → ℂ)
    (hs : ∀ x, ‖s x‖ₑ ≤ ∫⁻ y, b y * ‖f (x * k y)‖ₑ ∂ν) :
    ∫⁻ x in F, ‖s x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  set p := ν.withDensity b with hp
  haveI : IsProbabilityMeasure p := ⟨by rw [hp, withDensity_apply _ MeasurableSet.univ]; simpa using hmass⟩
  have hm : ∀ x, Continuous fun y => f (x * k y) := fun x => hf.comp (continuous_const.mul hk)
  have hsq : ∀ {X : Type _} [MeasurableSpace X] (m : Measure X) (g : X → ℂ) (hg : AEStronglyMeasurable g m),
      eLpNorm g 2 m ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂m := by
    intro X _ m g hg
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hg,
      ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_two]
  have hpt : ∀ x, ‖s x‖ₑ ^ 2 ≤ ∫⁻ y, ‖f (x * k y)‖ₑ ^ 2 ∂p := by
    intro x
    have h1 : ∫⁻ y, b y * ‖f (x * k y)‖ₑ ∂ν = ∫⁻ y, ‖f (x * k y)‖ₑ ∂p := by
      rw [hp, lintegral_withDensity_eq_lintegral_mul ν hb (hm x).measurable.enorm]
      rfl
    have h2 : eLpNorm (fun y => f (x * k y)) 1 p ≤ eLpNorm (fun y => f (x * k y)) 2 p :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    rw [eLpNorm_one_eq_lintegral_eNorm (hm x).measurable.aestronglyMeasurable] at h2
    rw [← hsq p _ (hm x).measurable.aestronglyMeasurable]
    exact pow_le_pow_left' ((hs x).trans (h1.le.trans h2)) 2
  have hΓ : ∀ (γ : Γ) (x : G), ‖f (γ • x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := fun γ x => by
    rw [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
  have htr : ∀ h : G, ∫⁻ x in F, ‖f (x * h)‖ₑ ^ 2 ∂μ = ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
    intro h
    have hF' : IsFundamentalDomain Γ (MulOpposite.op h • F) μ := hF.smul_of_comm _
    have e1 := (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulRight h).measurableEmbedding (fun z => ‖f z‖ₑ ^ 2) (MulOpposite.op h • F)
    have e2 : (fun x => x * h) ⁻¹' (MulOpposite.op h • F) = F := by
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    rw [e2] at e1
    rw [e1]
    exact hF'.setLIntegral_eq hF _ hΓ
  have hjoint : Measurable (Function.uncurry fun (x : G) (y : Y) => ‖f (x * k y)‖ₑ ^ 2) :=
    ((hf.comp (continuous_fst.mul (hk.comp continuous_snd))).measurable.enorm).pow_const 2
  calc ∫⁻ x in F, ‖s x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ∫⁻ y, ‖f (x * k y)‖ₑ ^ 2 ∂p ∂μ := lintegral_mono hpt
    _ = ∫⁻ y, ∫⁻ x in F, ‖f (x * k y)‖ₑ ^ 2 ∂μ ∂p := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ _y, ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ ∂p := lintegral_congr fun y => htr (k y)
    _ = ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by simp

theorem sm_sq_mass_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) →
  ∫⁻ x in F, ‖sm ν β f x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  intro E _ _ _ N _ _ μ _ _ _ ν _ F β hF hβ f hf hinv
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  haveI : SecondCountableTopology (GA E N) := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E N
  haveI : LocallyCompactSpace (GA E N) := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E N
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.haar_right_invariant_totally_complex E N μ
  haveI : SFinite μ := @MeasureTheory.instSFiniteOfSigmaFinite _ _ μ (Measure.IsHaarMeasure.sigmaFinite μ)
  refine lintegral_sq_le_of_average μ (latticeGL E N) F hF ν (fun y => ENNReal.ofReal (β y))
    hβ.cont.measurable.ennreal_ofReal ?_ (infEmb E N) continuous_infEmb f hf hinv (sm ν β f) ?_
  · rw [← ofReal_integral_eq_lintegral_ofReal
      (hβ.cont.integrable_of_hasCompactSupport hβ.cpt) (Eventually.of_forall hβ.nonneg), hβ.mass]
    simp
  · intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hβ.nonneg y)]

end GlobalTheory.CompanionTheory.Conc

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_bump_section_on_compact_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ v : W, ∃ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd ∧ IsCompact (L₀ : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) ∧ (∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1) ∧ ∃ f ∈ openFns d hd ρ, (∀ u ∈ L₀, f.1.1 (pm k (wOpen d hd) * u) = v) ∧ ∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1 (pm k (wOpen d hd) * u) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_openFns_bump | exact GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_openFns_bump | (intros; apply GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_openFns_bump <;> assumption)
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibTrivBlock

theorem nonempty_equiv_cInd {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W)
    {π : Representation ℂ G V} (hπ : IsSmooth π) (hH : ∀ g, g ∈ H) (L : V ≃ₗ[ℂ] W)
    (law : ∀ (h : H) v, σ h (L v) = L (π h v)) : Nonempty (π.Equiv (cInd H σ)) := by
  let f : V →ₗ[ℂ] cIndSpace H σ :=
    { toFun := fun v => ⟨⟨⟨fun x => L (π x v), fun p x => by
          refine Eq.trans ?_ (law p _).symm
          simp⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          simp [hg'])⟩,
        ⟨{1}, isCompact_singleton, fun g _ => ⟨g, hH g, 1, rfl, by simp⟩⟩⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => by simp)))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => by simp))) }
  have hb : Function.Bijective f := by
    refine ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1.1 1), Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => ?_)))⟩⟩
    · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1.1 1) h
      simpa using h1
    · have h1 := φ.1.1.2 ⟨x, hH x⟩ 1
      rw [mul_one] at h1
      refine (law ⟨x, hH x⟩ _).symm.trans ?_
      rw [L.apply_symm_apply]
      exact h1.symm
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective f hb) fun g => LinearMap.ext fun v =>
    Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => by
      show L (π x (π g v)) = L (π (x * g) v)
      simp)))⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

instance subsingleton_GL0 : Subsingleton (GL (Fin 0) k) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩

theorem absPow_zero_apply (s : ℂ) (hs : s = 0) (x : kˣ) : absPow k s x = 1 := by
  subst hs
  apply Units.ext
  simp [absPow]

theorem dpow_eq_one (n : ℕ) (s : ℝ) (hs : s = 0) (g : GL (Fin n) k) : dpow n s g = 1 := by
  simp only [dpow, detChar, MonoidHom.comp_apply]
  exact absPow_zero_apply _ (by simp [hs]) _

theorem mem_parab_zero {r : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ x, Two (Fin r) (Fin 0) x) ≃ n)
    (g : GL n k) : g ∈ parab k e := by
  have hb : ∀ x, blk e x = false := by
    intro x
    unfold blk
    rcases e.symm x with ⟨_ | _, c⟩
    · rfl
    · exact c.elim0
  intro a b hlt
  have h1 := hb a
  have h2 := hb b
  simp [h1, h2] at hlt

theorem deltaHalf_zero {r : ℕ} (z : Levi k (Two (Fin r) (Fin 0))) : deltaHalf k (Two (Fin r) (Fin 0)) z = 1 := by
  have h := deltaHalf_two (k := k) (a := Fin r) (b := Fin 0) ((leviTwo k (Fin r) (Fin 0)).symm z)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, absPow_zero_apply _ (by simp), Subsingleton.elim ((leviTwo k (Fin r) (Fin 0)).symm z).2 1]
  simp

theorem ePG_zero_val (i : ℕ) (b : Fin (i + 1)) : (ePG i 0 ⟨false, b⟩ : Fin (i + 0 + 1)).val = b.val := by
  induction b using Fin.lastCases with
  | last => rw [ePG_false_last]; simp
  | cast c =>
    simp [ePG, finSumFinEquiv_symm_apply_castSucc]
    rw [finSumFinEquiv_apply_left]
    rfl

theorem leviProj_std_false {i : ℕ} (p : parab k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0)))) :
    (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p false : GL (Fin (i + 1)) k) = (p : GL (Fin (i + 1 + 0)) k) := by
  apply Units.ext
  ext a b
  rw [leviProj_apply]
  have : ∀ c : Fin (i + 1), two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0)) ⟨false, c⟩ = c := fun c => by
    apply Fin.ext
    simp [two, stdSum]
  rw [this, this]

theorem pgProj_fst {i : ℕ} (h : HPG k i 0) :
    (((pgProj k i 0 h).1 : Mir k i) : GL (Fin (i + 1)) k) = ((h : Mir k (i + 0)) : GL (Fin (i + 0 + 1)) k) := by
  apply Units.ext
  ext a b
  show (leviProj k (ePG i 0) (hpgIncl k i 0 h) false : GL (Fin (i + 1)) k).val a b = _
  rw [leviProj_apply]
  have : ∀ c : Fin (i + 1), ePG i 0 ⟨false, c⟩ = c := fun c => Fin.ext (ePG_zero_val i c)
  rw [this, this]
  rfl

def actFst {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin n) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W) :
    Representation ℂ (GL (Fin n) k) (V ⊗[ℂ] W) :=
  (extTensor π₁ π₂).comp (MonoidHom.inl _ _)

theorem actFst_tmul {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin n) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W) (g : GL (Fin n) k) (v : V) (w : W) :
    actFst π₁ π₂ g (v ⊗ₜ w) = π₁ g v ⊗ₜ w := by
  simp [actFst, extTensor_tmul]

theorem isSmooth_actFst {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π₁ : Representation ℂ (GL (Fin n) k) V} {π₂ : Representation ℂ (GL (Fin 0) k) W}
    (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (actFst π₁ π₂) :=
  isSmooth_comp (isSmooth_extTensor h₁ h₂) _ (by
    show Continuous fun g : GL (Fin n) k => (g, (1 : GL (Fin 0) k))
    exact continuous_id.prodMk continuous_const)

theorem tE_piTensor {i : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W)
    (p : parab k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0)))) (y : ⨂[ℂ] x, TwoT V W x) :
    BZRes.tE V W (piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p) y) =
      actFst π₁ π₂ (p : GL (Fin (i + 1 + 0)) k) (BZRes.tE V W y) := by
  have key : ((BZRes.tE V W).toLinearMap ∘ₗ piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p)) =
      (actFst π₁ π₂ (p : GL (Fin (i + 1 + 0)) k)) ∘ₗ (BZRes.tE V W).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show BZRes.tE V W (piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p)
        (PiTensorProduct.tprod ℂ x)) = actFst π₁ π₂ (p : GL (Fin (i + 1 + 0)) k) (BZRes.tE V W (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod]
    refine (Exponents.boolTensorEquiv_tprod _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Exponents.boolTensorEquiv_tprod x).symm)
    rw [actFst_tmul, ← leviProj_std_false p]
    show π₁ _ (x false) ⊗ₜ[ℂ] π₂ _ (x true) = _
    rw [Subsingleton.elim (leviProj k (two (stdSum (rfl : (i + 1) + 0 = (i + 1) + 0))) p true : GL (Fin 0) k) 1, map_one]
    rfl
  exact LinearMap.congr_fun key y

theorem nonempty_actFst_equiv_prod2 {i : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W)
    (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) :
    Nonempty ((show Representation ℂ (GL (Fin (i + 1 + 0)) k) (V ⊗[ℂ] W) from actFst π₁ π₂).Equiv
      (prod2 (rfl : (i + 1) + 0 = (i + 1) + 0) π₁ π₂)) := by
  refine WordProd.OneBlockProd.nonempty_equiv_parInd _ (isSmooth_actFst h₁ h₂) (mem_parab_zero _) deltaHalf_zero
    (BZRes.tE V W).symm fun p v => ?_
  apply (BZRes.tE V W).injective
  rw [tE_piTensor, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hpg_act {i : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W)
    (χ₁ : Mir k i →* ℂˣ) (χ₂ : GL (Fin 0) k →* ℂˣ) (hχ : ∀ g, χ₁ g = 1) (h : HPG k i 0) (x : V ⊗[ℂ] W) :
    ((extTensor (_root_.GlobalTheory.SmGL.twist (π₁.comp (Mir k i).subtype) χ₁) (_root_.GlobalTheory.SmGL.twist π₂ χ₂)).comp (pgProj k i 0)) h x =
      actFst π₁ π₂ (((h : Mir k (i + 0)) : GL (Fin (i + 0 + 1)) k)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v w =>
    rw [actFst_tmul, MonoidHom.comp_apply, extTensor_tmul, ← pgProj_fst h, Subsingleton.elim (pgProj k i 0 h).2 1]
    simp [twist_apply, hχ]

theorem miso_gres_prod_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i n : ℕ) (π₁ : GRep k (i + 1)) (π₂ : GRep k 0) (h : (i + 1) + 0 = n + 1) (h' : i + 0 = n),
    IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodPGn (gres π₁) π₂)) := by
  intro k _ _ _ _ i n π₁ π₂ h h' h₁ h₂
  subst h'
  obtain ⟨E₁⟩ := nonempty_actFst_equiv_prod2 π₁.ρ π₂.ρ h₁ h₂
  have hs : IsSmooth ((actFst π₁.ρ π₂.ρ : Representation ℂ (GL (Fin (i + 0 + 1)) k) (π₁.V ⊗[ℂ] π₂.V)).comp
      (Mir k (i + 0)).subtype) :=
    isSmooth_comp (isSmooth_actFst h₁ h₂) _ continuous_subtype_val
  obtain ⟨E₂⟩ := nonempty_equiv_cInd (HPG k i 0)
    ((extTensor (mtw (gres π₁) (((0 : ℕ) : ℝ) / 2)).ρ (π₂.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i 0)) hs
    (fun g => mem_parab_zero _ _) (LinearEquiv.refl ℂ _) (fun g x => hpg_act π₁.ρ π₂.ρ _ _ (fun a => dpow_eq_one _ _ (by simp) _) g x)
  refine ⟨Representation.Equiv.trans (Representation.Equiv.mk E₁.symm.toLinearEquiv fun g => ?_) E₂⟩
  ext v
  exact eint E₁.symm _ v

end GlobalTheory.CompanionTheory.LeibTrivBlock

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair

theorem whit2_isSubquotient_whitImg_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Type} [AddCommGroup X]
    [Module ℂ X] (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    IsSubquotient (whit2 ψ d J) (whitImg ψ d J ⊤).toRepresentation := by
  let f : (whitImg ψ d J ⊤).toRepresentation.IntertwiningMap (whit2 ψ d J) :=
    ⟨(whitImg ψ d J ⊤).toSubmodule.subtype, fun _ => rfl⟩
  refine .of_surjective f fun w => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨⟨Submodule.Quotient.mk x, x, trivial, rfl⟩, rfl⟩

theorem not_isSubquotient_whitImg_bot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X W : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup W] [Module ℂ W] (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {σ : Representation ℂ (GL (Fin (d 0)) k) W} (hσ : σ.IsIrreducible) :
    ¬ IsSubquotient σ (whitImg ψ d J ⊥).toRepresentation := by
  rintro ⟨R, f, hf⟩
  have := nontrivial_of_irreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  have hv : v = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨t, ht, h⟩ := v.1.2
    have ht0 : t = 0 := ht
    rw [← h, ht0]
    simp
  exact hw (by rw [hv, map_zero])

theorem exists_constituent_of_whit2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl S hS
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  obtain ⟨T, hT, hmin⟩ := WellFounded.has_min hlt
    {T : Subrepresentation J | IsSubquotient S.ρ (whitImg ψ d J T).toRepresentation}
    ⟨⊤, hS.trans (whit2_isSubquotient_whitImg_top ψ d J)⟩
  have hne : T ≠ ⊥ := by
    rintro rfl
    exact not_isSubquotient_whitImg_bot ψ d J S.irr hT
  obtain ⟨T', hT'lt, hmax⟩ := WellFounded.has_min hgt {U : Subrepresentation J | U < T}
    ⟨⊥, bot_lt_iff_ne_bot.2 hne⟩
  have hcov : T' ⋖ T := ⟨hT'lt, fun c h1 h2 => hmax c h2 h1⟩
  have hq : IsSubquotient (subQuot T T') J :=
    ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', hq.isSmooth hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k (Fin 2)
    (fun a => Fin (d a)) τ
  have hspan := GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'lt.le Φ
  refine ⟨s, (IsSubquotient.of_surjective Φ.toIntertwiningMap Φ.surjective).trans hq, ?_⟩
  rcases GlobalTheory.T.irreducible_subquotient_of_extension _ _ _ (whit2 ψ d J) S.ρ _ _ (whitImg_mono ψ d J hT'lt.le) S.irr hT with h | h
  · exact absurd hT'lt (hmin T' h)
  · obtain ⟨e⟩ := GlobalTheory.T.subquotient_equiv_of_irreducible_image _ _ _ _ (s 0).ρ _ S.ρ (s 0).irr S.irr hspan h
    exact ⟨e.symm⟩

end GlobalTheory.CompanionTheory.BZNuPair

end
end
