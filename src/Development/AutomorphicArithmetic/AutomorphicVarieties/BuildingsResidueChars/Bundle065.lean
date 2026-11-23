module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle082
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle003
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle001
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamLocal
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem int_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
    (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
  exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem coef_of_field {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O :=
  _root_.UpperTheory.Reformulated.B.CoefficientsOfField.coef_of_field K

private theorem mem_pow_iff {l : ℕ} [Fact l.Prime] (c : Coef l) : ∃ a : ℝ, 0 < a ∧ a < 1 ∧
    ∀ (n : ℕ) (x : c.O), x ∈ maximalIdeal c.O ^ n ↔ ‖(x : PadicAlgCl l)‖ ≤ a ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h1 : ‖(ϖ : PadicAlgCl l)‖ < 1 := (UpperTheory.V.Fr.sc_norm l c ϖ).2.1 hϖ.not_isUnit
  have h0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := norm_pos_iff.2 fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨_, h0, h1, fun n x => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (UpperTheory.V.Fr.sc_norm l c y).1
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    have hu : ‖((u : c.O) : PadicAlgCl l)‖ = 1 :=
      le_antisymm (UpperTheory.V.Fr.sc_norm l c u).1 (not_lt.1 fun h => (UpperTheory.V.Fr.sc_norm l c u).2.2 h u.isUnit)
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, hu, one_mul] at hx
    exact (pow_dvd_pow ϖ ((pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 hx)).mul_left _

theorem UpperTheory.integrality_of_norm_coefficients :
    UpperTheory.V.Sd.S3.CoefEx := by
  intro l _
  refine ⟨fun c E hE => ?_, fun c Γ _ f => ?_⟩
  · obtain ⟨c', hc'⟩ := coef_of_field E
    obtain ⟨c₁, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
    exact ⟨c₁, h1, fun y hy h => h2 (hc' y hy h)⟩
  obtain ⟨a, h0, h1, ha⟩ := mem_pow_iff c
  constructor
  · intro hf
    rw [continuous_iff_continuousAt]
    intro g₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    filter_upwards [(hf n).eventually_eq g₀] with g hg
    rw [dist_eq_norm, ← Subalgebra.coe_sub]
    exact lt_of_le_of_lt ((ha n _).1 (Ideal.Quotient.eq.1 hg)) hn
  · intro hf n
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g₀
    filter_upwards [Metric.tendsto_nhds.1 (hf.tendsto g₀) (a ^ n) (pow_pos h0 n)] with g hg
    rw [dist_eq_norm, ← Subalgebra.coe_sub] at hg
    exact Ideal.Quotient.eq.2 ((ha n _).2 hg.le)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

theorem UpperTheory.bijective_residue_unit_mul_lift :
    ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (u : w.adicCompletionIntegers F), Valued.v (u : w.adicCompletion F) = 1 → ∀ s : 𝓞 F ⧸ w.asIdeal → 𝓞 F, (∀ r, Ideal.Quotient.mk w.asIdeal (s r) = r) → Function.Bijective fun r => IsLocalRing.residue (w.adicCompletionIntegers F) (u * algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)) := by
  intro F _ _ w u hu s hs
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  have hv : ∀ k : F, Valued.v (algebraMap F (w.adicCompletion F) k) = w.valuation F k :=
    fun k => IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k
  have hmem : ∀ x : w.adicCompletionIntegers F,
      x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ↔ Valued.v (x : w.adicCompletion F) < 1 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have hx : Valued.v (x : w.adicCompletion F) ≤ 1 := x.2
    exact ⟨fun h => lt_of_le_of_ne hx h, fun h => ne_of_lt h⟩
  have hcoe : ∀ b : 𝓞 F, ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b : w.adicCompletionIntegers F) : w.adicCompletion F)
      = algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b) := fun b => rfl
  have hker : ∀ a ∈ w.asIdeal,
      ((IsLocalRing.residue (w.adicCompletionIntegers F)).comp
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F))) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmem, hcoe, hv]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem w a).mpr ha
  let g := Ideal.Quotient.lift w.asIdeal ((IsLocalRing.residue (w.adicCompletionIntegers F)).comp
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F))) hker
  have hg : ∀ r, IsLocalRing.residue (w.adicCompletionIntegers F)
      (algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)) = g r := by
    intro r
    conv_rhs => rw [← hs r]
    rfl
  have hinj : Function.Injective g := g.injective
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    have hU : {z : w.adicCompletion F | Valued.v (z - (y : w.adicCompletion F)) < 1} ∈ nhds (y : w.adicCompletion F) := by
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      simpa [Valuation.restrict_lt_iff_lt_embedding] using hz
    obtain ⟨a, ha⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) w).mem_nhds hU
    have ha' : Valued.v (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) < 1 := ha
    have hale : w.valuation F a ≤ 1 := by
      rw [← hv]
      have hy : Valued.v (y : w.adicCompletion F) ≤ 1 := y.2
      have e : algebraMap F (w.adicCompletion F) a
          = (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) + (y : w.adicCompletion F) := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le ha'.le hy)
    obtain ⟨b, hb⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer w hale 1
    have hb' : Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b - a)) < 1 := by
      rw [hv]; simpa using hb
    refine ⟨Ideal.Quotient.mk w.asIdeal b, ?_⟩
    change IsLocalRing.residue _ (algebraMap (𝓞 F) (w.adicCompletionIntegers F) b) = _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmem]
    have e : ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b - y : w.adicCompletionIntegers F) : w.adicCompletion F)
        = algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F b - a)
          + (algebraMap F (w.adicCompletion F) a - (y : w.adicCompletion F)) := by
      rw [map_sub]
      change ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) b : w.adicCompletionIntegers F) : w.adicCompletion F) - (y : w.adicCompletion F) = _
      rw [hcoe]
      ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt hb' ha')
  have hc : IsUnit (IsLocalRing.residue (w.adicCompletionIntegers F) u) :=
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hu).map _
  have hf : (fun r => IsLocalRing.residue (w.adicCompletionIntegers F)
      (u * algebraMap (𝓞 F) (w.adicCompletionIntegers F) (s r)))
      = (fun z => (hc.unit : IsLocalRing.ResidueField (w.adicCompletionIntegers F)) * z) ∘ g := by
    funext r
    simp only [Function.comp_apply, map_mul, hg, IsUnit.unit_spec]
  rw [hf]
  exact (Units.mulLeft_bijective hc.unit).comp ⟨hinj, hsurj⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

private theorem map_aff' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_zero' {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mirab' {R : Type} [CommRing R] (x : R) : aff (1 : Rˣ) x ∈ mirab R := by
  change _ = _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, aff]

open UpperTheory.V.Af.GlobalFixedVectors in
theorem UpperTheory.hilbertHolomorphic_invariant_integralTranslation :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2), IsHol k c ω φ → ∀ o : Af F, (∀ v : Pl F, Valued.v (pLoc F v o) ≤ 1) → TR.finRep F 2 (aff 1 o) φ = φ := by
  classical
  intro F _ _ _ k c ω φ hφ o ho
  have key : ∀ S : Finset (Pl F),
      (∀ x ∈ Ohat F, (∀ w ∈ S, pLoc F w x = 0) → TR.finRep F 2 (aff 1 x) φ = φ) →
      ∀ x ∈ Ohat F, TR.finRep F 2 (aff 1 x) φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun h x hx => h x hx (by simp)
    | insert w S hw ih =>
      intro h
      refine ih fun x hx hS => ?_
      have e : aff 1 x = aff 1 (x - sLoc F w (pLoc F w x)) * locGL F 2 w (aff 1 (pLoc F w x)) := gl_ext fun u => by
        rw [map_mul, map_aff', map_aff', map_sub]
        by_cases hu : u = w
        · subst hu
          rw [pLoc_locGL, pLoc_sLoc, sub_self, aff_zero', one_mul]
        · rw [pLoc_locGL_of_ne hu, pLoc_sLoc_of_ne hu, sub_zero, mul_one]
      have hK : aff 1 (pLoc F w x) ∈ K1 w (c w) := by
        refine ⟨aff 1 ⟨pLoc F w x, mem_Ohat.1 hx w⟩, ?_, map_aff' _ _⟩
        change Matrix.GeneralLinearGroup.map _ _ ∈ mirab _
        rw [map_aff']
        exact aff_mirab' _
      have h1 : TR.finRep F 2 (locGL F 2 w (aff 1 (pLoc F w x))) φ = φ := hφ.level w _ hK
      rw [e, map_mul, Module.End.mul_apply, h1]
      refine h _ (sub_mem hx (sLoc_mem w hx)) fun u hu => ?_
      rw [map_sub]
      by_cases huw : u = w
      · subst huw
        rw [pLoc_sLoc, sub_self]
      · rw [pLoc_sLoc_of_ne huw, sub_zero]
        exact hS u ((Finset.mem_insert.1 hu).resolve_left huw)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (hφ.aut.level.mem_nhds (show (1 : GL (Fin 2) (Af F)) ∈ _ by simp))
  refine key S (fun x hx h0 => hS (mem_KAway.2 ⟨⟨aff 1 ⟨x, hx⟩, ?_, map_aff' _ _⟩, fun w hw => ?_⟩)) o (mem_Ohat.2 ho)
  · haveI : Subsingleton (Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · rw [map_aff', h0 w hw, aff_zero']
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

theorem UpperTheory.exists_global_element_valuation_eq_idele_at_place :
    ∀ (F : Type) [Field F] [NumberField F] (y : (Af F)ˣ) (w : Pl F), ∃ β : F, w.valuation F β = Valued.v (pLoc F w (y : Af F)) ∧ ∀ v : Pl F, v.valuation F β ≤ Valued.v (pLoc F v (y : Af F)) := by
  intro F _ _ y w
  obtain ⟨p, hpw, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hp : algebraMap (𝓞 F) F p ≠ 0 := by simpa using hp0
  have hval : ∀ (v : Pl F) (f : F), Valued.v (pLoc F v (algebraMap F (Af F) f)) = v.valuation F f :=
    fun v f => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  set z : Af F := algebraMap F (Af F) (algebraMap (𝓞 F) F p)⁻¹ * ((y⁻¹ : (Af F)ˣ) : Af F) with hz
  have hc : Continuous fun a : Af F => z * (a - (y : Af F)) :=
    continuous_const.mul (continuous_id.sub continuous_const)
  obtain ⟨β, hβ⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open
    ((GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F)).preimage hc)
    ⟨(y : Af F), by simp⟩
  have hβ' : ∀ v : Pl F, Valued.v (pLoc F v (z * (algebraMap F (Af F) β - (y : Af F)))) ≤ 1 :=
    fun v => GroundTheory.Global.mem_integralFiniteAdeles.1 hβ v
  have e : algebraMap F (Af F) β - (y : Af F) =
      (y : Af F) * algebraMap F (Af F) (algebraMap (𝓞 F) F p) * (z * (algebraMap F (Af F) β - (y : Af F))) := by
    have h1 : algebraMap F (Af F) (algebraMap (𝓞 F) F p) * algebraMap F (Af F) (algebraMap (𝓞 F) F p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hp, map_one]
    have h2 : (y : Af F) * ((y⁻¹ : (Af F)ˣ) : Af F) = 1 := y.mul_inv
    have h3 : (y : Af F) * algebraMap F (Af F) (algebraMap (𝓞 F) F p) * z = 1 := by
      rw [hz]
      linear_combination ((y : Af F) * ((y⁻¹ : (Af F)ˣ) : Af F)) * h1 + h2
    rw [← mul_assoc, h3, one_mul]
  have key : ∀ v : Pl F, Valued.v (pLoc F v (algebraMap F (Af F) β) - pLoc F v (y : Af F)) ≤
      Valued.v (pLoc F v (y : Af F)) * v.valuation F (algebraMap (𝓞 F) F p) := fun v => by
    rw [← map_sub, e, map_mul, map_mul, map_mul, map_mul, hval]
    exact mul_le_of_le_one_right' (hβ' v)
  refine ⟨β, ?_, fun v => ?_⟩
  · rw [← hval]
    refine Valuation.map_eq_of_sub_lt _ ((key w).trans_lt ?_)
    have h0 : 0 < Valued.v (pLoc F w (y : Af F)) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (y.isUnit.map (pLoc F w)).ne_zero)
    exact (mul_lt_mul_of_pos_left ((w.valuation_lt_one_iff_mem p).2 hpw) h0).trans_eq (mul_one _)
  · rw [← hval, ← sub_add_cancel (pLoc F v (algebraMap F (Af F) β)) (pLoc F v (y : Af F))]
    exact (Valuation.map_add _ _ _).trans
      (max_le ((key v).trans (mul_le_of_le_one_right' (v.valuation_le_one p))) le_rfl)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

private theorem ab_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G',
      ∀ g : G, F (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ (f g) := by
  have hc : (commutator G).topologicalClosure ≤ ((commutator G').topologicalClosure).comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact Subgroup.le_topologicalClosure _
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  exact ⟨QuotientGroup.map _ _ f hc, fun g => rfl⟩

private theorem map_prim {A B : Type} [CommGroup A] [CommGroup B] (l : ℕ) [Fact l.Prime] (F : A →* B) {x : A}
    (hx : x ∈ CommGroup.primaryComponent A l) : F x ∈ CommGroup.primaryComponent B l := by
  obtain ⟨k, hk⟩ := (Iff.rfl : x ∈ CommGroup.primaryComponent A l ↔ ∃ k : ℕ, x ^ l ^ k = 1).mp hx
  exact (Iff.rfl : F x ∈ CommGroup.primaryComponent B l ↔ ∃ k : ℕ, F x ^ l ^ k = 1).mpr
    ⟨k, by rw [← map_pow, hk, map_one]⟩

open UpperTheory.V.W in
private theorem locAb_transport (l : ℕ) [Fact l.Prime] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (e : G ≃* G') (he : Continuous e) (he' : Continuous e.symm)
    (I : Subgroup G) (I' : Subgroup G') (hI : ∀ g, e g ∈ I' ↔ g ∈ I) (d : ℕ) (A : LocAb l G' I' d) :
    Nonempty (LocAb l G I d) := by
  obtain ⟨Fe, hFe⟩ := ab_map e.toMonoidHom he
  obtain ⟨Fs, hFs⟩ := ab_map e.symm.toMonoidHom he'
  have mu1 : ∀ g, g ∈ muG l G → e g ∈ muG l G' := by
    intro g hg
    have h1 := map_prim l Fe (x := QuotientGroup.mk' (commutator G).topologicalClosure g) hg
    have h2 := hFe g
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [h2] at h1
    exact h1
  have mu2 : ∀ g', g' ∈ muG l G' → e.symm g' ∈ muG l G := by
    intro g hg
    have h1 := map_prim l Fs (x := QuotientGroup.mk' (commutator G').topologicalClosure g) hg
    have h2 := hFs g
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [h2] at h1
    exact h1
  let bm : CommGroup.primaryComponent (TopologicalAbelianization G') l →*
      CommGroup.primaryComponent (TopologicalAbelianization G) l :=
    MonoidHom.codRestrict (Fs.comp (CommGroup.primaryComponent _ l).subtype) _
      (fun x => map_prim l Fs x.2)
  refine ⟨LocAb.mk (A.a.comp e.toMonoidHom) (A.cont.comp he) (A.surj.comp e.surjective) ?_ ?_
    ((bm.comp A.b).comp e.toMonoidHom) ?_ ?_⟩
  · intro x
    rw [← A.inertia x]
    constructor
    · rintro ⟨g, hg, h⟩
      exact ⟨e g, (hI g).2 hg, h⟩
    · rintro ⟨g', hg', h⟩
      exact ⟨e.symm g', (hI _).1 (by simpa using hg'), by simpa using h⟩
  · intro C _ _ hC χ hχo hmu
    have key := A.univ C hC (χ.comp e.symm.toMonoidHom) (hχo.preimage he') (by
      intro g' hg'
      exact (MonoidHom.mem_ker).1 (hmu (mu2 g' hg')))
    intro g hg
    have h3 : e g ∈ (χ.comp e.symm.toMonoidHom).ker :=
      key (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hg))
    have h5 := MonoidHom.mem_ker.1 h3
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h5
    exact MonoidHom.mem_ker.2 h5
  · refine Subgroup.isOpen_mono (H₁ := A.b.ker.comap e.toMonoidHom) ?_ (A.b_open.preimage he)
    intro g hg
    rw [Subgroup.mem_comap, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_one]
  · intro g hg
    show Fs ((A.b (e g)) : TopologicalAbelianization G') = _
    rw [A.b_mu _ (mu1 g hg)]
    have h4 := hFs (e g)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h4
    exact h4

open Formalism.BasicNotions.Loc in
theorem UpperTheory.nonempty_localWeilData_decompositionGroup_of_mem_place :
    ∀ (l : ℕ) [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)), IsPlaceOver A w → ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Nonempty (UpperTheory.V.W.LocAb l (Dec (F := F) A) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) (locDeg w)) := by
  intro l _ F Ω _ _ _ _ _ _ A w hA hl
  obtain ⟨j, hj⟩ := (UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).1 A w hA hl
  subst hj
  obtain ⟨-, φ, hφ, -, hran, hin, -, hidx⟩ := (UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK : ∀ τ, τ ∈ GK K ↔ ∀ x : F, τ (j (algebraMap F Ω x)) = j (algebraMap F Ω x) :=
    GlobalTheory.PlaceBridge.mem_GK_iff (E := F) (Ω := Ω) K rfl
  have hR : φ.range = GK K := by
    ext τ
    rw [hran τ, hK τ]
  have hd : Module.finrank ℚ_[l] K.1 = locDeg w := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← hidx w hA, hR]
    rfl
  obtain ⟨B⟩ := UpperTheory.V.W.lam_local l K
  rw [hd] at B
  let e := (MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hR)
  refine locAb_transport l e ?_ ?_ _ _ ?_ _ B
  · exact continuous_induced_rng.2 hφ.continuous
  · refine hφ.toIsEmbedding.continuous_iff.2 ?_
    have h : (⇑φ ∘ ⇑e.symm) = Subtype.val := funext fun τ => congrArg Subtype.val (e.apply_symm_apply τ)
    rw [h]
    exact continuous_subtype_val
  · intro g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hin g
end
