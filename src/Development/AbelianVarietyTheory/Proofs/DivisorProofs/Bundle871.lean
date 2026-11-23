module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle840
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle349
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle841
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle625
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle832
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle839
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle526
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnalyticOnNhdOrbitOfDerivSeqNormEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachExp

theorem exists_locExp_expAt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  intro l _ LL _ hex
  obtain ⟨ζL, hζL⟩ := hex
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin := LL.2
  have hint : IsIntegral ℤ_[l] ζL := IsIntegral.of_pow hl (by rw [hζL.pow_eq_one]; exact isIntegral_one)
  let ζ : ↥(OL LL) := ⟨ζL, hint⟩
  have hζ : IsPrimitiveRoot ζ l :=
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζL Subtype.val_injective

  have hu : IsUnit (1 + (l : ℤ_[l]) * 1) := by
    have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
    rcases h with h | h
    · exact absurd ((IsUnit.neg_iff _).1 h) PadicInt.prime_p.not_isUnit
    · simpa [sub_eq_add_neg] using h
  let u : ℤ_[l]ˣ := hu.unit
  have hu1 : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * 1 := hu.unit_spec

  have hmax : ζ - 1 ∈ maximalIdeal ↥(OL LL) := by
    refine (GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm (p := l) LL.1 _).2 ?_
    refine lt_of_eq_of_lt (b := ‖((((ζL - 1 : ↥LL.1)) : PadicAlgCl l) : ℂ_[l])‖) rfl ?_
    rw [PadicComplex.norm_extends]
    exact norm_root_sub_one_lt LL hζL.pow_eq_one
  have hpow : ∀ b : ℕ, (ζL ^ b) ^ l = 1 := fun b => by
    rw [← pow_mul, mul_comm, pow_mul, hζL.pow_eq_one, one_pow]
  choose ev hC hev using fun b : ℕ => exists_ev LL (ζL ^ b) (hpow b)
  refine ⟨u, 1, ζ, ev, hu1, isUnit_one, hζ, hmax, fun b _ => ⟨⟨fun a => hC b a, ?_, fun f => ?_⟩, ⟨fun a => hC b a, hev b⟩⟩⟩
  · obtain ⟨g, hg⟩ : X ∣ exp ↥LL.1 - 1 := X_dvd_iff.2 (by simp)
    have hg0 : constantCoeff g = 1 := by
      have h := congrArg (coeff 1) hg
      rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h
      rw [← h]; simp [coeff_exp]
    have hzb : ζL ^ b ≠ 0 := pow_ne_zero _ (hζL.ne_zero (by omega))
    have hunit : IsUnit (C (ζL ^ b) * g) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hg0, hzb]
    have hcalc : ev b (X - C (ζ ^ b - 1)) = X * (C (ζL ^ b) * g) := by
      rw [map_sub, hev, hC]
      have hco : ((ζ ^ b - 1 : ↥(OL LL)) : ↥LL.1) = ζL ^ b - 1 := rfl
      rw [hco, map_sub (C : ↥LL.1 →+* _), map_one]
      linear_combination (C (ζL ^ b)) * hg
    rw [hcalc]
    exact associated_mul_unit_left X _ hunit
  · set r : ↥LL.1 := algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) with hr_def
    have hact : Formalism.CohomologicalDescent.HeightDescentMinors.act l ↥(OL LL) (u : ℤ_[l]) f = GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) f := by
      simp only [Formalism.CohomologicalDescent.HeightDescentMinors.act, Formalism.CohomologicalDescent.HeightDescentMinors.br, GlobalTheory.Fon.gam]
      exact (congrFun (coe_substAlgHom _) f).symm
    have hxz := ringHom_gam_X (O := ↥(OL LL)) (L := ↥LL.1) (ev b) (hC b) (ζL ^ b) (hev b) (hpow b)
      (u : ℤ_[l]) ⟨1, by rw [hu1]; ring⟩
    have huniq := ev_unique LL (C (ζL ^ b) * rescale r (exp ↥LL.1) - 1)
      (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL (hpow b))
      ((ev b).comp (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) : PowerSeries ↥(OL LL) →+* PowerSeries ↥(OL LL)))
      ((rescale r).comp (ev b))
      (fun a => by
        change ev b (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) (C a)) = _
        rw [GlobalTheory.Fon.gam_C, hC])
      (fun a => by
        change rescale r (ev b (C a)) = _
        rw [hC, rescale_C'])
      hxz
      (by
        change rescale r (ev b X) = _
        rw [hev, map_sub, map_mul, map_one, rescale_C'])
    rw [hact]
    exact RingHom.congr_fun huniq f

end GlobalTheory.WachExp
end

section


theorem _root_.GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  first | exact @GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | exact GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | (intros; apply GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.real_unitary_covolume_sum : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → IsSReps X.Gm (Λ : Set (Fin r → E)) 1 s → ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) ≤ ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  first | exact @GlobalTheory.SUVolBound.sum_covolume_le | exact GlobalTheory.SUVolBound.sum_covolume_le | (intros; apply GlobalTheory.SUVolBound.sum_covolume_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.polarisation_dlog_cocycle_coboundary_closed_fibre_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  first | exact @GlobalTheory.ChartCob.chart_isCob | exact GlobalTheory.ChartCob.chart_isCob | (intros; apply GlobalTheory.ChartCob.chart_isCob <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_vectorField_lifts_affine_cover_smooth_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := by
  first | exact @GlobalTheory.KSLift.exists_lifts | exact GlobalTheory.KSLift.exists_lifts | (intros; apply GlobalTheory.KSLift.exists_lifts <;> assumption)
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.conj_skew_mem_productSpecialUnitaryLieAlgebra : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (Y : X.Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ a b, Y τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (Y τ a b) = 0) → (∀ τ a, Y τ a a = 0) → (fun τ => ((mat x τ * Y τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ)) ∈ realLie X.Ψ X.Gm := by
  first | exact @GlobalTheory.SUChartSection.conj_mem_realLie | exact GlobalTheory.SUChartSection.conj_mem_realLie | (intros; apply GlobalTheory.SUChartSection.conj_mem_realLie <;> assumption)
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem metaplecticRepresentation_holds : GlobalTheory.Published.MetaplecticRepresentation := by
  intro ι _ _
  obtain ⟨G, iG, tG, tgG, pr, om, omS, φ, hcov, hsurj, ⟨ε, hε1, hker, hεf⟩, hcont, hint, hcompat, hφ, hjc,
    hgauss⟩ := GlobalTheory.T.metaplectic_cover_weil_representation ι
  obtain ⟨e, u, he, hu⟩ := GlobalTheory.T.schwartz_L2_euclidean_identification ι
  have hes : ∀ (ψ : Sch ι) (x : ι → ℝ), e.symm ψ x = ψ (WithLp.toLp 2 x) := by
    intro ψ x
    simpa using (he (e.symm ψ) (WithLp.toLp 2 x)).symm
  have inj : ∀ ψ₁ ψ₂ : Sch ι, ψ₁.toLp 2 = ψ₂.toLp 2 → ψ₁ = ψ₂ := fun ψ₁ ψ₂ h =>
    SchwartzMap.injective_toLp (E := EuclideanSpace ℝ ι) (F := ℂ) 2 volume h
  let Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))) :=
    { toFun := fun g => ((u.symm.toContinuousLinearEquiv : L2 ι →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))).comp
          ((om g).toContinuousLinearEquiv : L2 ι →L[ℂ] L2 ι)).comp
          (u.toContinuousLinearEquiv : Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] L2 ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hΩ : ∀ g f, Ω g f = u.symm (om g (u f)) := fun g f => rfl
  let ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ)) :=
    { toFun := fun g => ((e.symm : Sch ι →L[ℂ] 𝓢(ι → ℝ, ℂ)).comp (omS g)).comp (e : 𝓢(ι → ℝ, ℂ) →L[ℂ] Sch ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hω : ∀ g f, ω g f = e.symm (omS g (e f)) := fun g f => rfl
  have heω : ∀ g f, e (ω g f) = omS g (e f) := fun g f => by rw [hω, e.apply_symm_apply]
  have hφ₀ : ∀ x : ι → ℝ, e.symm φ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
    intro x
    rw [hes, hφ]
  refine ⟨G, iG, tG, tgG, pr, Ω, ω, e.symm φ, hsurj, hcov, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hφ₀, ?_, ?_⟩
  · have hk : (pr.ker : Set G) = {1, ε} := by
      ext g
      simp [MonoidHom.mem_ker, hker]
    rw [← SetLike.coe_sort_coe, hk, Nat.card_coe_set_eq, Set.ncard_pair hε1.symm]
  · intro g f
    rw [hΩ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  · intro f
    exact u.symm.continuous.comp (hcont (u f))
  · intro g ψ
    rw [hΩ, LinearIsometryEquiv.symm_apply_eq, hu, hu, heω, hcompat]
  · have : (fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) =
        (fun y : Sch ι => e.symm y) ∘ (fun y : G × Sch ι => omS y.1 y.2) ∘ (fun x : G × 𝓢(ι → ℝ, ℂ) => (x.1, e x.2)) := by
      funext x; rfl
    rw [this]
    exact e.symm.continuous.comp (hjc.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
  · intro g w ψ
    apply e.injective
    apply inj
    rw [heω, ← hcompat]
    rw [GlobalTheory.T.schrodinger_product_euclidean_models_agree ι w ψ (e ψ) (e (GlobalTheory.Published.Metaplectic.rho w ψ)) (he ψ) (he _)]
    rw [hint, hcompat]
    rw [GlobalTheory.T.schrodinger_product_euclidean_models_agree ι (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ) (e (ω g ψ))
      (e (GlobalTheory.Published.Metaplectic.rho (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ))) (he _) (he _)]
    rw [heω]
    congr 2
    simp [GlobalTheory.Published.Metaplectic.act, Sum.elim_comp_inl_inr]
  · intro g hg1 hg ψ
    have hgε : g = ε := ((hker g).1 hg1).resolve_left hg
    subst hgε
    have h1 : omS g (e ψ) = -(e ψ) := by
      apply inj
      have hn := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))).map_neg (e ψ)
      simp only [SchwartzMap.toLpCLM_apply] at hn
      rw [← hcompat, hεf, hn]
    rw [hω, h1, map_neg, e.symm_apply_apply]
  · intro g
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨-, hsymm⟩ := GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2
    have hsieg := GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 hdet hsymm
    have hωx : ∀ x : ι → ℝ, ω g (e.symm φ) x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ
        (-((Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) *
          (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))⁻¹)) *ᵥ
          fun i => (x i : ℂ))) := by
      intro x
      rw [hω, e.apply_symm_apply, hes, hcx]
    simp only [hωx, hφ₀]
    exact GlobalTheory.T.vacuum_matrix_coefficient_sq ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) hdet hsieg c hc
  · intro g horth
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨hP, hq⟩ := GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 horth hdet
    refine ⟨c, by rw [hP]; exact hc, ?_⟩
    ext x
    rw [hω, e.apply_symm_apply, hes, hcx, SchwartzMap.smul_apply, smul_eq_mul, hφ₀]
    simp only [PiLp.toLp_apply]
    rw [hq x]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_complexLinear_of_pure_types_finite_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La) (N : ℕ), 0 < N → (∀ v : D.La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) → (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  first | exact @GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index | exact GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index | (intros; apply GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index <;> assumption)
end

section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

theorem _root_.GlobalTheory.T.exists_conj_integral_galoisRep : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)), Continuous r → (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) → ∃ A : GL (Fin n) (PadicAlgCl l), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ i j, ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ g i j, ‖((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1 := by
  first | exact @GlobalTheory.GalIntegral.exists_conj_integral | exact GlobalTheory.GalIntegral.exists_conj_integral | (intros; apply GlobalTheory.GalIntegral.exists_conj_integral <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.OrbitAnalytic in
theorem analyticOnNhd_orbit_pol : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ (P : Pol p q r s), AnalyticOnNhd ℝ (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) Set.univ ∧ ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) 0 = F.ι ((omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) ^ k) P) := by
  intro p q r s T0 T1 T2 F Z hZ P
  set Y := Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z with hY
  let f : ℕ → ℝ → F.H := fun k t => F.Om (T0.expt (t • Z)) (F.ι ((omAct p q r s Y ^ k) P))
  have hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t := fun k t =>
    hasDerivAt_orbit (fun t => F.Om (T0.expt (t • Z)))
      (fun s t => by simp only [T0.expt_add Z hZ, map_mul]) _ _
      (by simpa only [pow_succ', Module.End.mul_apply] using F.der Z hZ ((omAct p q r s Y ^ k) P)) t
  have h0 : (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) = f 0 := by
    funext t; simp [f]
  rw [h0]
  refine ⟨fun a _ => ?_, fun k => ?_⟩
  · set S : ℝ := 4 * ∑ l, ∑ l', ‖Y l l'‖ with hS
    have hS0 : 0 ≤ S := by positivity
    refine analyticAt_of_bound f hf ((2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖) (S + 1)⁻¹
      (by positivity) (fun k t => ?_) a
    have hb := (GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (isFockIsometry_of_fockData F) Y P.totalDegree k P le_rfl).2
    simp only [f]
    rw [F.isom]
    refine hb.trans ?_
    rw [← hS, inv_pow, div_inv_eq_mul]
    calc _ ≤ (S + 1) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖ := by
          gcongr; linarith
      _ = _ := by ring
  · have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [iteratedDeriv_succ, ih]; funext t; exact (hf k t).deriv
    rw [hit]
    simp [f, T0.expt_zero]

end GlobalTheory.FockAlg
end

section

open Formalism.BasicNotions.TH
open scoped Kronecker

namespace GlobalTheory.FockPair

theorem fockAct1_eq_kron (p q r s : ℕ) (Y : Mat p q) :
    fockAct1 p q r s Y = omAct p q r s (Y ⊗ₖ (1 : Mat r s)) := rfl

theorem fockAct2_eq_kron (p q r s : ℕ) (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s ((1 : Mat p q) ⊗ₖ Z) := rfl

theorem pair_lie_commute : ∀ (p q r s : ℕ), IsLieAct (fockAct1 p q r s) ∧
    IsLieAct (fockAct2 p q r s) ∧ ∀ (Y : Mat p q) (Z : Mat r s),
      fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  intro p q r s
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun Y Z => ?_⟩
  · rw [map_sub]
    simp only [fockAct1_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [map_sub]
    simp only [fockAct2_eq_kron]
    rw [← GlobalTheory.T.fockQuadraticAction_map_lie_bracket, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [← sub_eq_zero, fockAct1_eq_kron, fockAct2_eq_kron, ← GlobalTheory.T.fockQuadraticAction_map_lie_bracket,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

end GlobalTheory.FockPair
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector : ∀ (p q r s : ℕ), (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧ (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := by
  first | exact @GlobalTheory.FockAlg.degW_le_of_homog_wtSub | exact GlobalTheory.FockAlg.degW_le_of_homog_wtSub | (intros; apply GlobalTheory.FockAlg.degW_le_of_homog_wtSub <;> assumption)
end
