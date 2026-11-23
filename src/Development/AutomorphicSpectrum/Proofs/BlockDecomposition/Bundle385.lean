module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExistsNatCastConjMem
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExistsNormConjArchLe
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import GroundTheory.GlobalFields.Adele.Topology
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc.SmKill

theorem ctn_sm {K : Type} [Field K] [NumberField K] {n : ℕ} [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {β : archGroup K n → ℝ}
    (hβ : Continuous β) (hβc : HasCompactSupport β) {f : AdelicGLn.AdelicGL K n → ℂ} (hf : Continuous f)
    (r : ℕ) (g : AdelicGLn.AdelicGL K n) :
    Integrable (fun y => (β y : ℂ) * An.ctn r f (g * infEmb K n y)) ν ∧
      An.ctn r (sm ν β f) g = ∫ y, (β y : ℂ) * An.ctn r f (g * infEmb K n y) ∂ν := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ (φ : AdelicGLn.AdelicGL K n → ℂ) (h : AdelicGLn.AdelicGL K n),
      An.ctn r φ h = c * constantTerm r φ h := ⟨_, fun _ _ => rfl⟩
  set F : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ :=
    fun p => c * ((β p.2 : ℂ) * f (unipGL p.1 * g * infEmb K n p.2)) with hF
  have hFc : Continuous F :=
    continuous_const.mul ((Complex.continuous_ofReal.comp (hβ.comp continuous_snd)).mul
      (hf.comp ((continuous_unipGL.comp continuous_fst).mul continuous_const |>.mul
        (continuous_infEmb.comp continuous_snd))))
  have hint : Integrable F ((unipMeasure K n r).restrict (unipFundamentalDomain K n r) |>.prod ν) := by
    have e : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod ν =
        ((unipMeasure K n r).prod ν).restrict (unipFundamentalDomain K n r ×ˢ Set.univ) := by
      rw [← Measure.restrict_univ (μ := ν), Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    refine IntegrableOn.of_forall_sdiff_eq_zero
      (hFc.continuousOn.integrableOn_compact (hC.prod hβc.isCompact))
      (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) fun p hp => ?_
    have hy : p.2 ∉ tsupport β := fun hy => hp.2 ⟨hDC hp.1.1, hy⟩
    simp [hF, image_eq_zero_of_notMem_tsupport hy]
  have hval : ∀ y, ∫ X in unipFundamentalDomain K n r, F (X, y) ∂unipMeasure K n r =
      (β y : ℂ) * An.ctn r f (g * infEmb K n y) := fun y => by
    simp only [hF, hc, constantTerm, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    ring
  constructor
  · have := hint.swap.integral_prod_left
    refine this.congr (Eventually.of_forall fun y => ?_)
    exact hval y
  · have h := integral_integral_swap (f := fun X y => F (X, y)) hint
    simp only [hval] at h
    rw [← h]
    simp only [hc, constantTerm, sm, hF]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [integral_const_mul]

end GlobalTheory.CompanionTheory.Conc.SmKill


open GlobalTheory.CompanionTheory.Conc.SmKill in
theorem GlobalTheory.CompanionTheory.Conc.kill_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ) (r : ℕ) (p : ℂ[X]), Ker ν β → 0 < r → r < n → Continuous f →
    An.Kill r f p → An.Kill r (sm ν β f) p := by
  intro K _ _ n _ _ ν _ β f r p hk _ _ hf hkill g
  have h1 : ∀ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * An.ctn r (sm ν β f) (An.aR K n r j * g) =
        ∫ y, p.coeff j * ((β y : ℂ) * An.ctn r f (An.aR K n r j * g * infEmb K n y)) ∂ν := fun j _ => by
    rw [(ctn_sm ν hk.cont hk.cpt hf r _).2, integral_const_mul]
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum _ fun j _ =>
    ((ctn_sm ν hk.cont hk.cpt hf r _).1).const_mul _]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  have h2 := hkill (g * infEmb K n y)
  have h3 : ∑ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * ((β y : ℂ) * An.ctn r f (An.aR K n r j * g * infEmb K n y)) =
      (β y : ℂ) * ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * An.ctn r f (An.aR K n r j * (g * infEmb K n y)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (An.aR K n r j)]
    ring
  simp only [Pi.zero_apply]
  rw [h3, h2, mul_zero]

end
end

section

noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

theorem continuous_sm_uFam {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hβ : Ker ν β) {f : AdelicGLn.AdelicGL K n → ℂ}
    (hf : Continuous f) : Continuous (sm ν β f) := by
  have hF : Continuous (Function.uncurry fun (x : AdelicGLn.AdelicGL K n) (y : archGroup K n) =>
      (β y : ℂ) * f (x * infEmb K n y)) := by
    refine (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul (hf.comp ?_)
    exact continuous_fst.mul (continuous_infEmb.comp continuous_snd)
  set_option synthInstance.maxHeartbeats 1000000 in
  have h := continuous_parametric_integral_of_continuous (μ := ν) hF hβ.cpt.isCompact
  refine h.congr fun x => ?_
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have : β y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [this]

theorem uFam_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ)
    (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ), Ker ν β → UFam f → UFam (fun i => sm ν β (f i)) := by
  intro K _ _ n _ _ ν _ β ι f hβ hf
  refine ⟨fun i => continuous_sm_uFam ν hβ (hf.cont i), fun i γ x => ?_, ?_⟩
  · simp only [sm, mul_assoc]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hf.left i γ (x * infEmb K n y)]
  · obtain ⟨U, hU, hlev⟩ := hf.level
    refine ⟨U, hU, fun i g u => ?_⟩
    simp only [sm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [mul_assoc g, ← infEmb_mul_finEmb_comm, ← mul_assoc, hlev i (g * infEmb K n y) u]

end GlobalTheory.CompanionTheory.Conc

end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

open scoped Pointwise

theorem sm_lip_of_sq_zero : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ), Ker ν β → ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
  ∀ (f : AdelicGLn.AdelicGL K n → ℂ), Continuous f → ∀ g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖f (g * q)‖ ≤ M) →
    ‖sm ν β f (g * CuspidalSpectrum.archExp Y) - sm ν β f g‖ ≤ C * ‖Y‖ * M := by
  intro K _ _ n _ _ ν _ β hβ R
  obtain ⟨L, hL0, hL⟩ := hβ.lip
  set e : ArchMatrix K n → archGroup K n :=
    fun Y => (isExpLieAlgebra K n).expG ⟨Y, Submodule.mem_top⟩ with he
  have hec : Continuous e :=
    (isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _)
  have hT₀ : IsCompact (tsupport β) := hβ.cpt
  haveI : ProperSpace (ArchMatrix K n) := FiniteDimensional.proper ℝ _
  have hB : IsCompact (e '' Metric.closedBall 0 R) := (isCompact_closedBall 0 R).image hec
  set T : Set (archGroup K n) := tsupport β ∪ (e '' Metric.closedBall 0 R) * tsupport β with hTdef
  have hT : IsCompact T := hT₀.union (hB.mul hT₀)
  obtain ⟨S, hS0, hS⟩ := (hT.image continuous_mat).isBounded.exists_pos_norm_le
  have hne : (tsupport β).Nonempty := by
    rcases Set.eq_empty_or_nonempty (tsupport β) with h0 | h0
    · exfalso
      have hz : ∀ y, β y = 0 := fun y => image_eq_zero_of_notMem_tsupport (by simp [h0])
      have := hβ.mass
      simp [hz] at this
    · exact h0
  refine ⟨infEmb K n '' T, L * S * ν.real T, hT.image continuous_infEmb, by positivity, ?_⟩
  intro f hf g Y M hYY hYR hM
  obtain ⟨t₀, ht₀⟩ := hne
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨t₀, Or.inl ht₀, rfl⟩)
  set h : archGroup K n → ℂ := fun y => f (g * infEmb K n y) with hh
  have hhc : Continuous h := hf.comp (continuous_const.mul continuous_infEmb)

  have hexp : mat (e Y) = 1 + Y :=
    (CuspidalSpectrum.coe_expG_top Y).trans (CuspidalSpectrum.exp_eq_one_add_of_mul_self_eq_zero hYY)
  have hmul : ∀ a b : archGroup K n, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have hinv : mat (e Y)⁻¹ = 1 - Y := by
    have h1 : mat (e Y) * (1 - Y) = 1 := by
      have : (1 + Y) * (1 - Y) = 1 - Y * Y := by noncomm_ring
      rw [hexp, this, hYY, sub_zero]
    have h2 : mat (e Y)⁻¹ * mat (e Y) = 1 := by
      rw [← hmul, inv_mul_cancel]; rfl
    calc mat (e Y)⁻¹ = mat (e Y)⁻¹ * (mat (e Y) * (1 - Y)) := by rw [h1, mul_one]
      _ = 1 - Y := by rw [← mul_assoc, h2, one_mul]

  have hz2 : ∀ u, u ∉ T → β u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inl hc)
  have hz1 : ∀ u, u ∉ T → β ((e Y)⁻¹ * u) = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inr
      ⟨e Y, ⟨Y, by simpa using hYR, rfl⟩, _, hc, by simp⟩)
  set F₁ : archGroup K n → ℂ := fun u => (β ((e Y)⁻¹ * u) : ℂ) * h u with hF₁
  set F₂ : archGroup K n → ℂ := fun u => (β u : ℂ) * h u with hF₂
  have hF₁c : Continuous F₁ :=
    (Complex.continuous_ofReal.comp (hβ.cont.comp (continuous_const.mul continuous_id))).mul hhc
  have hF₂c : Continuous F₂ := (Complex.continuous_ofReal.comp hβ.cont).mul hhc
  have hF₁z : ∀ u, u ∉ T → F₁ u = 0 := fun u hu => by simp [hF₁, hz1 u hu]
  have hF₂z : ∀ u, u ∉ T → F₂ u = 0 := fun u hu => by simp [hF₂, hz2 u hu]
  have hF₁i : Integrable F₁ ν :=
    hF₁c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₁z)
  have hF₂i : Integrable F₂ ν :=
    hF₂c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₂z)
  have hsm1 : sm ν β f (g * CuspidalSpectrum.archExp Y) = ∫ u, F₁ u ∂ν := by
    rw [← integral_mul_left_eq_self (μ := ν) F₁ (e Y)]
    unfold sm
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF₁, hh, inv_mul_cancel_left, map_mul]
    rw [CuspidalSpectrum.archExp, mul_assoc]
  have hsm2 : sm ν β f g = ∫ u, F₂ u ∂ν := rfl
  rw [hsm1, hsm2, ← integral_sub hF₁i hF₂i,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := T)
      (fun u hu => by rw [hF₁z u hu, hF₂z u hu, sub_zero])]
  have hpt : ∀ u ∈ T, ‖F₁ u - F₂ u‖ ≤ L * S * ‖Y‖ * M := by
    intro u hu
    have hd : F₁ u - F₂ u = ((β ((e Y)⁻¹ * u) - β u : ℝ) : ℂ) * h u := by
      simp only [hF₁, hF₂]; push_cast; ring
    have hm : mat ((e Y)⁻¹ * u) - mat u = -(Y * mat u) := by
      rw [hmul, hinv]; noncomm_ring
    have h1 : |β ((e Y)⁻¹ * u) - β u| ≤ L * (‖Y‖ * S) := by
      refine (hL _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0)
      rw [hm, norm_neg]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hS _ ⟨u, hu, rfl⟩) (norm_nonneg _))
    have h2 : ‖h u‖ ≤ M := hM _ ⟨u, hu, rfl⟩
    rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |β ((e Y)⁻¹ * u) - β u| * ‖h u‖ ≤ (L * (‖Y‖ * S)) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = L * S * ‖Y‖ * M := by ring
  have := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := T) hT.measure_lt_top hpt
  refine this.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.Conc
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

theorem continuous_sm_of_ker : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ),
    Ker ν β → Continuous f → Continuous (sm ν β f) := by
  intro K _ _ n _ _ ν _ β f hβ hf
  have hs : IsCompact (tsupport β) := hβ.cpt
  set F : AdelicGLn.AdelicGL K n × archGroup K n → ℂ :=
    fun p => (β p.2 : ℂ) * f (p.1 * infEmb K n p.2) with hFdef
  have hF : Continuous F :=
    (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul
      (hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd)))
  have hFx : ∀ x, Continuous fun y => F (x, y) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (fun y => F (x, y)) (tsupport β) ν := fun x =>
    (hFx x).continuousOn.integrableOn_compact hs
  have e : ∀ x, sm ν β f x = ∫ y in tsupport β, F (x, y) ∂ν := fun x =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [hFdef, image_eq_zero_of_notMem_tsupport hy]).symm
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hc : 0 ≤ ν.real (tsupport β) := measureReal_nonneg
  set δ : ℝ := ε / (ν.real (tsupport β) + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hopen : IsOpen {p : AdelicGLn.AdelicGL K n × archGroup K n | dist (F p) (F (x₀, p.2)) < δ} :=
    isOpen_lt (hF.dist (hF.comp (continuous_const.prodMk continuous_snd))) continuous_const
  obtain ⟨u, v, hu, -, hxu, hsv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := x₀)) hs hopen (by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    obtain rfl : x = x₀ := hx
    simpa using hδ)
  filter_upwards [hu.mem_nhds (hxu rfl)] with x hx
  rw [e, e, dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have hb : ‖∫ y in tsupport β, (F (x, y) - F (x₀, y)) ∂ν‖ ≤ δ * ν.real (tsupport β) := by
    refine norm_setIntegral_le_of_norm_le_const hs.measure_lt_top fun y hy => ?_
    have := huv (Set.mk_mem_prod hx (hsv hy))
    simp only [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine lt_of_le_of_lt hb ?_
  rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.CompanionTheory.Conc
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Conc

theorem norm_integral_ker_le {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hk : Ker ν β)
    (g : archGroup K n → ℂ) {M : ℝ} (hg : ∀ y ∈ tsupport β, ‖g y‖ ≤ M) :
    ‖∫ y, (β y : ℂ) * g y ∂ν‖ ≤ M := by
  have hint : Integrable (fun y => β y * M) ν :=
    (hk.cont.integrable_of_hasCompactSupport hk.cpt).mul_const M
  have hpt : ∀ y, ‖(β y : ℂ) * g y‖ ≤ β y * M := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk.nonneg y)]
    by_cases hy : y ∈ tsupport β
    · exact mul_le_mul_of_nonneg_left (hg y hy) (hk.nonneg y)
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simp
  have h := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rwa [integral_mul_const, hk.mass, one_mul] at h

theorem uBnd_sm (K : Type) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type)
    (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (hk : Ker ν β) (_hf : ∀ i, Continuous (f i))
    (hb : UBnd f m) : UBnd (fun i => sm ν β (f i)) m := by
  intro ω hω hsub t₀ Q hQ
  have hQ' : IsCompact (Q * infEmb K n '' tsupport β) :=
    hQ.mul (hk.cpt.isCompact.image continuous_infEmb)
  obtain ⟨C, hC⟩ := hb ω hω hsub t₀ _ hQ'
  refine ⟨max C 0, fun i b hbω x hx q hq => ?_⟩
  refine norm_integral_ker_le ν hk _ ?_
  intro y hy
  rw [mul_assoc (b * _) q]
  refine (hC i b hbω x hx _ (Set.mul_mem_mul hq (Set.mem_image_of_mem _ hy))).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end GlobalTheory.CompanionTheory.Conc
end

section

noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open scoped NumberField.AdeleRing Pointwise
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

namespace GlobalTheory.CompanionTheory.Conc


open PositivityTheory.Rg.Rs.diffstep in
theorem diffStepU (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type)
    (f₀ f₁ : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (hrn : r < n) (hN : UFam f₁)
    (hlip' : ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
      ∀ i g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R →
        (∀ q ∈ Q₀, ‖f₀ i (g * q)‖ ≤ M) → ‖f₁ i (g * CuspidalSpectrum.archExp Y) - f₁ i g‖ ≤ C * ‖Y‖ * M)
    (hB : UBnd f₀ m) :
    UBnd (fun i g => f₁ i g - An.ctn r (f₁ i) g) (Function.update m r (m r - 1)) := by
  intro ω hω hωB t₀ Q hQ
  obtain ⟨U, hU, hlev⟩ := hN.level
  obtain ⟨M, hM, hMc⟩ := exists_natCast_conj_mem U hU hω hQ r
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_conjArch_le hω hωB hQ (Real.exp_pos (-t₀)) hr hrn
    (isCompact_scaledInfSet (K := K) M)
  obtain ⟨Q₀, C₂, hQ₀, hC₂, hlip⟩ := hlip' (C₁ * Real.exp t₀)
  obtain ⟨C₃, hC₃⟩ := hB ω hω hωB t₀ (Q * Q₀) (hQ.mul hQ₀)
  set C₃' := max C₃ 0 with hC₃'
  have hC₃'0 : 0 ≤ C₃' := le_max_right _ _
  refine ⟨C₂ * C₁ * C₃', ?_⟩
  intro i b hb x hx q hq
  set g := b * An.tor K x * q with hg
  set S := ∑ i ∈ Finset.range n, m i * An.sr x i with hS
  have hsieg := siegel_of_sr hx
  have hpt : ∀ X ∈ scaledUnipFD K n r M, ‖f₁ i g - f₁ i (unipGL X * g)‖ ≤
      C₂ * (C₁ * Real.exp (-An.sr x r)) * (C₃' * Real.exp S) := by
    intro X hX
    set Y := conjArch K n g (truncInf X) with hY
    have hYn : ‖Y‖ ≤ C₁ * Real.exp (-An.sr x r) := by
      have h := hC₁ b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) hsieg q hq (truncInf X)
        (fun p => rfl) (fun p => infinite_mem_scaledInfSet hM hX p)
      rw [exp_div_exp_eq hr hrn x] at h
      exact h
    have hYR : ‖Y‖ ≤ C₁ * Real.exp t₀ :=
      hYn.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hx r])) hC₁0)
    obtain ⟨u, hu⟩ := hMc b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) q hq (truncFin X)
      (fun p => rfl) (fun p => exists_finite_eq_natCast_mul hM hX p)
    have hu' : g⁻¹ * unipGL (truncFin X) * g =
        finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := hu
    have hdecomp : unipGL X * g = g * archExp Y * (g⁻¹ * unipGL (truncFin X) * g) := by
      rw [hY, ← conj_unipGL_eq_archExp g (truncInf X) (fun p => rfl)]
      conv_lhs => rw [← truncInf_add_truncFin X, unipGL_add]
      group
    have heq : f₁ i (unipGL X * g) = f₁ i (g * archExp Y) := by rw [hdecomp, hu', hlev]
    have hMg : ∀ q' ∈ Q₀, ‖f₀ i (g * q')‖ ≤ C₃' * Real.exp S := by
      intro q' hq'
      have h := hC₃ i b hb x hx (q * q') (Set.mul_mem_mul hq hq')
      rw [show g * q' = b * An.tor K x * (q * q') by rw [hg, mul_assoc]]
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hl := hlip i g Y (C₃' * Real.exp S) (conjArch_mul_conjArch _ _ _) hYR hMg
    rw [norm_sub_rev, heq]
    calc _ ≤ C₂ * ‖Y‖ * (C₃' * Real.exp S) := hl
      _ ≤ _ := by gcongr
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨Cc, hCc, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : IntegrableOn (fun X => f₁ i (unipGL X * g)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    (((hN.cont i).comp (continuous_unipGL.mul continuous_const)).continuousOn.integrableOn_compact
      hCc).mono_set hDC
  have hfin : unipMeasure K n r (scaledUnipFD K n r M) < ⊤ := by
    rw [hD1]
    exact ENNReal.one_lt_top
  have hct : An.ctn r (f₁ i) g = ∫ X in scaledUnipFD K n r M, f₁ i (unipGL X * g) ∂unipMeasure K n r := by
    rw [An.ctn, measureReal_def, unipMeasure_unipFundamentalDomain, ENNReal.toReal_one,
      Complex.ofReal_one, inv_one, one_mul]
    exact constantTerm_eq_setIntegral (hN.left i) hD g
  have hdiff : f₁ i g - An.ctn r (f₁ i) g =
      ∫ X in scaledUnipFD K n r M, (f₁ i g - f₁ i (unipGL X * g)) ∂unipMeasure K n r := by
    have hconst : IntegrableOn (fun _ => f₁ i g) (scaledUnipFD K n r M) (unipMeasure K n r) :=
      integrableOn_const hfin.ne enorm_ne_top
    rw [hct, integral_sub hconst hint, setIntegral_const, measureReal_def, hD1,
      ENNReal.toReal_one, one_smul]
  change ‖f₁ i g - An.ctn r (f₁ i) g‖ ≤ _
  rw [hdiff]
  refine (norm_setIntegral_le_of_norm_le_const hfin hpt).trans (le_of_eq ?_)
  rw [measureReal_def, hD1, ENNReal.toReal_one, mul_one, sum_update_sub hrn, ← hS, sub_eq_add_neg,
    Real.exp_add]
  ring

end GlobalTheory.CompanionTheory.Conc

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.reverse_ordered_product_perm_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (σ : Equiv.Perm (Fin h)) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, (y (σ a)).1 = N), IsRevOrdered Γ → IsRevOrdered (Γ ∘ σ) → (∀ i, IsLSeg (Γ i) (y i).rep) → Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ σ) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered | exact GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered | (intros; apply GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered <;> assumption)
end
