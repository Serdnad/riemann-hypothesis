module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle004
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle006
public import GroundTheory.GlobalFields.TateThesis.TateTheta
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleInfIdDetLe
public import GroundTheory.GlobalFields.TateThesis.Bundle009
public import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem integral_count_Xi (f : Xi F → ℂ) : ∫ ξ, f ξ ∂(Measure.count : Measure (Xi F)) = ∑' ξ, f ξ := by
  by_cases hf : Summable f
  · have hi : Integrable f (Measure.count : Measure (Xi F)) := by
      rw [integrable_count_iff]
      exact summable_norm_iff.mpr hf
    rw [integral_countable hi]
    simp [count_real_singleton]
  · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
    intro hi
    rw [integrable_count_iff] at hi
    exact hf (summable_norm_iff.mp hi)

theorem integral_iter_eq (S : Set {r : ℝ // 0 < r}) (hS : MeasurableSet S) {h : Pp F × Xi F → ℂ}
    (hh : Integrable h (μS F S)) :
    IntegrableOn (fun t => ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F)
        S posRealMeasure ∧
      ∫ t in S, ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F
          ∂posRealMeasure = ∫ q, h q ∂μS F S := by
  have e1 : ∀ p : Pp F, ∫ ξ, h (p, ξ) ∂(Measure.count : Measure (Xi F)) = ∑' ξ : Xi F, h (p, ξ) :=
    fun p => integral_count_Xi _
  have hG : Integrable (fun p : Pp F => ∑' ξ : Xi F, h (p, ξ))
      ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) := by
    have := hh.integral_prod_left
    simp only [e1] at this
    exact this
  refine ⟨?_, ?_⟩
  · have := hG.integral_prod_left
    exact this
  · rw [μS, integral_prod _ hh]
    simp only [e1]
    rw [integral_prod _ hG]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace L7

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open Classical in
theorem slice_congr (c : HeightOneSpectrum (𝓞 F) → ℕ) {A A' : Ad F}
    (h1 : UpperTheory.V.TR.pInf F A = UpperTheory.V.TR.pInf F A')
    (h2 : ∀ w, Valued.v (pLoc F w (pFin F A)) = Valued.v (pLoc F w (pFin F A'))) :
    slice c A = slice c A' := by
  funext B
  simp only [slice, Phi, Matrix.cons_val_zero, Matrix.cons_val_one, h1]
  congr 1
  exact if_congr (forall_congr' fun w => by rw [h2 w]) rfl rfl

theorem pInf_finiteEmbedding (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    UpperTheory.V.TR.pInf F ((finiteEmbedding w x : IdeleGroup F) : Ad F) = 1 := by
  show (UpperTheory.V.TR.infEq F).symm ((finiteEmbedding w x : IdeleGroup F) : Ad F).1 = 1
  rw [coe_finiteEmbedding]
  exact map_one _

theorem valued_finiteEmbedding (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ)
    (hx : IsUnitAt w x) (w' : HeightOneSpectrum (𝓞 F)) :
    Valued.v (pLoc F w' (pFin F ((finiteEmbedding w x : IdeleGroup F) : Ad F))) = 1 := by
  show Valued.v ((((finiteEmbedding w x : IdeleGroup F) : Ad F).2) w') = 1
  rw [coe_finiteEmbedding]
  by_cases h : w' = w
  · subst h
    show Valued.v (finiteAdeleSingle w' (x : w'.adicCompletion F) w') = 1
    rw [finiteAdeleSingle_apply_self]
    exact hx
  · show Valued.v (finiteAdeleSingle w (x : w.adicCompletion F) w') = 1
    rw [finiteAdeleSingle_apply_of_ne h]
    exact map_one _

theorem norm_unit (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    ‖(x : w.adicCompletion F)‖ = 1 := by
  have hx' : Valued.v ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (x : w.adicCompletion F) = 1 from hx, inv_one]
  refine IdeleGroup.norm_eq_one_of_mul_eq_one (b := ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F))
    x.mul_inv ?_ ?_
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).2 (le_of_eq hx)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).2 (le_of_eq hx')

theorem ideleModule_finiteEmbedding_unit (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ)
    (hx : IsUnitAt w x) : ideleModule F (finiteEmbedding w x) = 1 :=
  Subtype.ext (by rw [ideleModule_finiteEmbedding, norm_unit w x hx]; rfl)

theorem kern_mul_unit (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (σ : IdeleGroup F)
    (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    kern c Y (σ * finiteEmbedding w x) 0 = kern c Y σ 0 := by
  have hs : slice c (((σ * finiteEmbedding w x : IdeleGroup F) : Ad F) * Y) = slice c ((σ : Ad F) * Y) := by
    refine slice_congr c ?_ ?_
    · rw [Units.val_mul, map_mul, map_mul, map_mul, pInf_finiteEmbedding, mul_one]
    · intro w'
      simp only [Units.val_mul, map_mul, valued_finiteEmbedding w x hx w', mul_one]
  unfold kern
  rw [hs, map_mul, ideleModule_finiteEmbedding_unit w x hx, mul_one, map_zero, smul_zero, smul_zero]

theorem omega_diagonal (ω : HChar F) (δ : Fˣ) : ω.1 (diagonal F δ) = 1 := ω.2.2 δ

theorem coefK_mul_diagonal (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (δ : Fˣ) (ξ : F) :
    coefK c Y (τ * diagonal F δ) ξ = coefK c Y τ ξ := by
  unfold coefK
  have := (Equiv.mulLeft δ).tsum_eq (fun a => kern c Y (τ * diagonal F a) ξ)
  rw [← this]
  refine tsum_congr fun a => ?_
  rw [Equiv.coe_mulLeft, map_mul, mul_assoc]

theorem coefK_mul_unit (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F)
    (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    coefK c Y (τ * finiteEmbedding w x) 0 = coefK c Y τ 0 := by
  unfold coefK
  refine tsum_congr fun a => ?_
  rw [mul_right_comm, kern_mul_unit c Y _ w x hx]

theorem exists_unit (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (H : Hyp ω c) :
    ∃ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ), IsUnitAt w x ∧ ω.loc w x ≠ 1 := by
  obtain ⟨w, hw⟩ := H.ram
  refine ⟨w, ?_⟩
  by_contra hne
  push Not at hne
  have h0 : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} :=
    fun x hx _ => hne x hx
  exact hw (Nat.le_zero.1 ((H.cond w).2 h0))

theorem loc_eq (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    ω.1 (finiteEmbedding w x) = ω.loc w x := rfl

end L7

open L7 in
theorem null_term_holds : SFin → SKern → SNull := by
  intro _ _ F _ _ _ ω c H y yf t _
  set Y := yAd y yf
  obtain ⟨w, x, hx, hω⟩ := exists_unit ω c H
  set h : normOneSubgroup F → ℂ := fun u => coefK c Y (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ with hdef
  have hh : ∀ (δ : Fˣ) (u : normOneSubgroup F), h (u * diagonalToNormOne F δ) = h u := by
    intro δ u
    have e1 : tau t (u * diagonalToNormOne F δ) = tau t u * diagonal F δ := by
      simp only [tau, Subgroup.coe_mul, coe_diagonalToNormOne, mul_assoc]
    simp only [hdef, e1, coefK_mul_diagonal, map_mul, omega_diagonal, mul_one]
  have he1 : ideleModule F (finiteEmbedding w x) = 1 := ideleModule_finiteEmbedding_unit w x hx
  let e' : normOneSubgroup F := ⟨finiteEmbedding w x, by rw [normOneSubgroup, MonoidHom.mem_ker]; exact he1⟩
  have hshift : ∀ u, h (e' * u) = ((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ * h u := by
    intro u
    have e2 : tau t (e' * u) = tau t u * finiteEmbedding w x := by
      simp only [tau, Subgroup.coe_mul, e']
      rw [mul_comm ((finiteEmbedding w x : IdeleGroup F)) (u : IdeleGroup F), mul_assoc]
    simp only [hdef, e2, coefK_mul_unit c Y _ w x hx, map_mul, Units.val_mul, mul_inv]
    ring
  have hI := setIntegral_mul_left_eq hh e'
  simp only [hshift] at hI
  rw [integral_const_mul] at hI
  have hne : ((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ ≠ 1 := by
    rw [Ne, inv_eq_one, loc_eq]
    intro h1
    exact hω (Units.ext h1)
  have h3 : (((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ - 1) *
      ∫ u in normOneFundamentalDomain F, h u ∂normOneMeasure F = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section

noncomputable section

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def mn (M : Matrix (Fin 2) (Fin 2) (Ad F)) : ℝ := ∑ i, ∑ j, ‖UpperTheory.V.TR.pInf F (M i j)‖

theorem pLoc_pFin_algebraMap (w : HeightOneSpectrum (𝓞 F)) (x : F) :
    pLoc F w (pFin F (algebraMap F (Ad F) x)) = algebraMap F (w.adicCompletion F) x := rfl

theorem pFin_moduleSection_mul (t : {r : ℝ // 0 < r}) (a : Ideles F) :
    pFin F ((moduleSection (w0 F) t * a : Ideles F) : Ad F) = pFin F (a : Ad F) := by
  rw [Units.val_mul, map_mul]
  have h1 : pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1 := by
    rw [coe_moduleSection]; rfl
  rw [h1, one_mul]

theorem pFin_inv_moduleSection_mul (t : {r : ℝ // 0 < r}) (a : Ideles F) :
    pFin F (((moduleSection (w0 F) t * a)⁻¹ : Ideles F) : Ad F) = pFin F ((a⁻¹ : Ideles F) : Ad F) := by
  rw [mul_inv, ← map_inv, pFin_moduleSection_mul]

theorem rowA_eq (ξ : Fin 2 → F) (z : Ideles F) (M M' : Matrix (Fin 2) (Fin 2) (Ad F)) (hM : M * M' = 1) :
    rowA ξ = (rowA ξ ᵥ* ((z : Ad F) • M)) ᵥ* (((z⁻¹ : Ideles F) : Ad F) • M') := by
  rw [Matrix.vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul, hM,
    Matrix.vecMul_one]

theorem fin_part {e : HeightOneSpectrum (𝓞 F) → ℤ} (D : 𝓞 F)
    (hD : ∀ w, ∀ x : w.adicCompletion F, Valued.v x ≤ WithZero.exp (e w) →
      Valued.v (algebraMap F (w.adicCompletion F) (D : F) * x) ≤ 1)
    {K : Set (Ideles F)} (hK : IsCompact K) (Mf' : Matrix (Fin 2) (Fin 2) (Af F)) (hD0 : D ≠ 0) :
    ∃ D' : 𝓞 F, D' ≠ 0 ∧ ∀ a ∈ K, ∀ t : {r : ℝ // 0 < r}, ∀ (ξ : Fin 2 → F) (M M' : Matrix (Fin 2) (Fin 2) (Ad F)),
      M * M' = 1 → M'.map (pFin F) = Mf' →
      boxP e (rowA ξ ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M)) →
      ∀ j, ∃ r : 𝓞 F, (D' : F) * ξ j = r := by
  classical
  set S : Set (Af F) := ⋃ i : Fin 2, ⋃ j : Fin 2,
    (fun a : Ideles F => pFin F ((a⁻¹ : Ideles F) : Ad F) * Mf' i j) '' K with hSdef
  have hS : IsCompact S := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hK.image ?_
    have hc : Continuous fun a : Ideles F => pFin F ((a⁻¹ : Ideles F) : Ad F) :=
      (continuous_snd : Continuous (Prod.snd : InfiniteAdeleRing F × Af F → Af F)).comp
        (Units.continuous_coe_inv (M := Ad F))
    exact hc.mul continuous_const
  obtain ⟨D1, hD10, hD1⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  refine ⟨D * D1, mul_ne_zero hD0 hD10, fun a ha t ξ M M' hM hMf hbox j => ?_⟩
  set z : Ideles F := moduleSection (w0 F) t * a
  set v := rowA ξ ᵥ* ((z : Ad F) • M)
  have hrow := congrFun (rowA_eq ξ z M M' hM) j
  have hval : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (w.adicCompletion F) (((D * D1 : 𝓞 F) : F) * ξ j)) ≤ 1 := by
    intro w
    have h1 : algebraMap F (w.adicCompletion F) (ξ j) =
        ∑ i, pLoc F w (pFin F (v i)) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j)) := by
      rw [← pLoc_pFin_algebraMap]
      change pLoc F w (pFin F (rowA ξ j)) = _
      rw [hrow]

      simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pFin_inv_moduleSection_mul]
      congr 2
      rw [← hMf]
      rfl
    rw [map_mul, h1, Finset.mul_sum]
    refine Valuation.map_sum_le _ fun i _ => ?_
    have hA : Valued.v (algebraMap F (w.adicCompletion F) (D : F) * pLoc F w (pFin F (v i))) ≤ 1 :=
      hD w _ (hbox w i)
    have hs : pFin F ((a⁻¹ : Ideles F) : Ad F) * Mf' i j ∈ S := by
      rw [hSdef]
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨a, ha, rfl⟩⟩⟩
    have hB : Valued.v (algebraMap F (w.adicCompletion F) (D1 : F) *
        (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) ≤ 1 := by
      have := hD1 _ hs w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
      exact this
    have hc : ((D * D1 : 𝓞 F) : F) = (D : F) * (D1 : F) := by simp
    have key : algebraMap F (w.adicCompletion F) ((D * D1 : 𝓞 F) : F) *
        (pLoc F w (pFin F (v i)) * (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) =
        (algebraMap F (w.adicCompletion F) (D : F) * pLoc F w (pFin F (v i))) *
          (algebraMap F (w.adicCompletion F) (D1 : F) *
            (pLoc F w (pFin F ((a⁻¹ : Ideles F) : Ad F)) * pLoc F w (Mf' i j))) := by
      rw [hc, map_mul]
      ring
    rw [key, map_mul]
    exact (mul_le_mul' hA hB).trans_eq (one_mul 1)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F
    (((D * D1 : 𝓞 F) : F) * ξ j) fun w =>
      (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm.trans_le (hval w)
  exact ⟨r, hr.symm⟩

theorem entry_le_mn (B : Matrix (Fin 2) (Fin 2) (Ad F)) (i j : Fin 2) :
    ‖UpperTheory.V.TR.pInf F (B i j)‖ ≤ mn B := by
  unfold mn
  calc ‖UpperTheory.V.TR.pInf F (B i j)‖ ≤ ∑ j', ‖UpperTheory.V.TR.pInf F (B i j')‖ :=
        Finset.single_le_sum (f := fun j' => ‖UpperTheory.V.TR.pInf F (B i j')‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖UpperTheory.V.TR.pInf F (B i' j')‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖UpperTheory.V.TR.pInf F (B i' j')‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem mn_nonneg (B : Matrix (Fin 2) (Fin 2) (Ad F)) : 0 ≤ mn B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem mn_transpose (B : Matrix (Fin 2) (Fin 2) (Ad F)) : mn B.transpose = mn B := by
  unfold mn
  rw [Finset.sum_comm]
  rfl

theorem mn_mul_le_left (A B : Matrix (Fin 2) (Fin 2) (Ad F)) (H : ℝ)
    (hA : ∀ i k, ‖UpperTheory.V.TR.pInf F (A i k)‖ ≤ H) : mn (A * B) ≤ 8 * H * mn B := by
  have hH : 0 ≤ H := (norm_nonneg _).trans (hA 0 0)
  have h : ∀ i j, ‖UpperTheory.V.TR.pInf F ((A * B) i j)‖ ≤ 2 * H * mn B := by
    intro i j

    rw [Matrix.mul_apply, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖UpperTheory.V.TR.pInf F (A i k * B k j)‖ ≤ ∑ _k : Fin 2, H * mn B :=
          Finset.sum_le_sum fun k _ => by
            rw [map_mul]
            exact (norm_mul_le _ _).trans (mul_le_mul (hA i k) (entry_le_mn B k j) (norm_nonneg _) hH)
      _ = 2 * H * mn B := by simp [Finset.sum_const]; try ring
  calc mn (A * B) ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, 2 * H * mn B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 8 * H * mn B := by simp [Finset.sum_const]; try ring

theorem mn_mul_le_right (A B : Matrix (Fin 2) (Fin 2) (Ad F)) (H : ℝ)
    (hB : ∀ k j, ‖UpperTheory.V.TR.pInf F (B k j)‖ ≤ H) : mn (A * B) ≤ 8 * H * mn A := by
  have hH : 0 ≤ H := (norm_nonneg _).trans (hB 0 0)
  have h : ∀ i j, ‖UpperTheory.V.TR.pInf F ((A * B) i j)‖ ≤ 2 * H * mn A := by
    intro i j

    rw [Matrix.mul_apply, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖UpperTheory.V.TR.pInf F (A i k * B k j)‖ ≤ ∑ _k : Fin 2, H * mn A :=
          Finset.sum_le_sum fun k _ => by
            rw [map_mul, mul_comm H]
            exact (norm_mul_le _ _).trans (mul_le_mul (entry_le_mn A i k) (hB k j) (norm_nonneg _) (mn_nonneg A))
      _ = 2 * H * mn A := by simp [Finset.sum_const]; try ring
  calc mn (A * B) ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, 2 * H * mn A :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 8 * H * mn A := by simp [Finset.sum_const]; try ring

theorem norm_pInf_infGL_le (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i k : Fin 2) :
    ‖UpperTheory.V.TR.pInf F (((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i k)‖ ≤
      UpperTheory.V.TR.height y := by
  have := Matrix.GeneralLinearGroup.map_apply (UpperTheory.V.TR.pInf F) i k (UpperTheory.V.TR.infGL F 2 y)
  rw [UpperTheory.V.TR.pInf_infGL] at this
  rw [← this]
  have h1 : ‖(y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i k‖ ≤
      ‖UpperTheory.V.TR.toL (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))‖ :=
    (norm_le_pi_norm _ k).trans (norm_le_pi_norm _ i)
  have h2 := norm_nonneg (UpperTheory.V.TR.toL ((y⁻¹ : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)))
  unfold UpperTheory.V.TR.height
  linarith

theorem height_inv (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : UpperTheory.V.TR.height y⁻¹ = UpperTheory.V.TR.height y := by
  unfold UpperTheory.V.TR.height
  rw [inv_inv]
  ring

theorem mn_bound (g : GA F 2) : ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ y : GL (Fin 2) (UpperTheory.V.TR.Rinf F),
    mn ((g * UpperTheory.V.TR.infGL F 2 y)⁻¹ : GA F 2).val ≤ Cm * UpperTheory.V.TR.height y ∧
    mn (g * UpperTheory.V.TR.infGL F 2 y : GA F 2).val.transpose ≤ Cm * UpperTheory.V.TR.height y := by
  refine ⟨8 * (mn (g⁻¹ : GA F 2).val + mn (g : GA F 2).val),
    mul_nonneg (by norm_num) (add_nonneg (mn_nonneg _) (mn_nonneg _)), fun y => ⟨?_, ?_⟩⟩
  · have hH := one_le_height y
    rw [mul_inv_rev, ← map_inv, Units.val_mul]
    refine (mn_mul_le_left _ _ _ fun i k => (norm_pInf_infGL_le y⁻¹ i k).trans (height_inv y).le).trans ?_
    nlinarith [mn_nonneg (g⁻¹ : GA F 2).val, mn_nonneg (g : GA F 2).val]
  · have hH := one_le_height y
    rw [mn_transpose, Units.val_mul]
    refine (mn_mul_le_right _ _ _ fun k j => norm_pInf_infGL_le y k j).trans ?_
    nlinarith [mn_nonneg (g⁻¹ : GA F 2).val, mn_nonneg (g : GA F 2).val]

end UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth
end
end
