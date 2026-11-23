module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  first | exact @GlobalTheory.KZ.JInt.jK_sl_isIntegral | exact GlobalTheory.KZ.JInt.jK_sl_isIntegral | (intros; apply GlobalTheory.KZ.JInt.jK_sl_isIntegral <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.modularTower_mem_adjoin_j_of_slTwoInt_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ f : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) f = f) → f ∈ IntermediateField.adjoin Ω {X.jK} := by
  first | exact @GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv | exact GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv | (intros; apply GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.LRepTriangular

theorem firstCol_ne_zero (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ))
    (h0 : (((γ : M2) 0 0 : ℤ) : ZMod q) = 0) (h1 : (((γ : M2) 1 0 : ℤ) : ZMod q) = 0) : False := by
  have hd : (γ : M2).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hd
  have := congrArg (fun x : ℤ => (x : ZMod q)) hd
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, h0, h1] at this
  simp at this

end GlobalTheory.EisM.LRepTriangular

namespace GlobalTheory.EisM


open GlobalTheory.EisM.LRepTriangular in
theorem lRep_DT_repT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repT q) := by
  intro L q hq hqL
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, x⟩ -
    have hγ := γ.2
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
    refine ⟨?_, ?_⟩
    · show (((γ : SL(2, ℤ)) : M2) * repT q x).det = q
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul]
      cases x <;> simp [repT, repU, Matrix.det_fin_two_of]
    · show (L : ℤ) ∣ (((γ : SL(2, ℤ)) : M2) * repT q x) 1 0
      cases x <;> simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | exact hγ | exact Dvd.dvd.mul_right hγ _
  · rintro ⟨γ, x⟩ - ⟨γ', y⟩ - h
    simp only at h
    have e : ∀ i k, (((γ : SL(2, ℤ)) : M2) * repT q x) i k = (((γ' : SL(2, ℤ)) : M2) * repT q y) i k :=
      fun i k => by rw [h]
    have hxy : x = y := by
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some j' =>
          exfalso
          have e00 := e 0 0; have e10 := e 1 0
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
          apply firstCol_ne_zero q (γ' : SL(2, ℤ))
          · rw [← e00]; push_cast; simp
          · rw [← e10]; push_cast; simp
      | some j =>
        cases y with
        | none =>
          exfalso
          have e00 := e 0 0; have e10 := e 1 0
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
          apply firstCol_ne_zero q (γ : SL(2, ℤ))
          · rw [e00]; push_cast; simp
          · rw [e10]; push_cast; simp
        | some j' =>
          have e00 := e 0 0; have e10 := e 1 0; have e01 := e 0 1; have e11 := e 1 1
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10 e01 e11
          have c01 := congrArg (fun z : ℤ => (z : ZMod q)) e01
          have c11 := congrArg (fun z : ℤ => (z : ZMod q)) e11
          push_cast at c01 c11
          simp only [ZMod.natCast_self, mul_zero, add_zero, e00, e10] at c01 c11
          by_cases hJ : ((j : ℕ) : ZMod q) = ((j' : ℕ) : ZMod q)
          · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at hJ
            rw [Fin.ext hJ]
          · exfalso
            have hs : ((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q) ≠ 0 := sub_ne_zero.mpr hJ
            apply firstCol_ne_zero q (γ' : SL(2, ℤ))
            · have : (((γ' : SL(2, ℤ)) : M2) 0 0 : ZMod q) * (((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q)) = 0 := by
                rw [mul_sub, c01, sub_self]
              exact (mul_eq_zero.mp this).resolve_right hs
            · have : (((γ' : SL(2, ℤ)) : M2) 1 0 : ZMod q) * (((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q)) = 0 := by
                rw [mul_sub, c11, sub_self]
              exact (mul_eq_zero.mp this).resolve_right hs
    subst hxy
    have hm : ((γ : SL(2, ℤ)) : M2) = ((γ' : SL(2, ℤ)) : M2) := by
      have h2 := congrArg (· * (repT q x).adjugate) h
      simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
      have hdet : (repT q x).det = q := by cases x <;> simp [repT, repU, Matrix.det_fin_two_of]
      rw [hdet] at h2
      exact smul_right_injective M2 hq0 h2
    exact Prod.ext (Subtype.ext (Subtype.ext hm)) rfl
  · rintro δ ⟨hdet, hL⟩
    obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, δ = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two δ⟩
    simp [Matrix.det_fin_two_of] at hdet hL
    by_cases hac : (q : ℤ) ∣ a ∧ (q : ℤ) ∣ c
    · obtain ⟨⟨a', ha⟩, ⟨c', hc⟩⟩ := hac
      subst ha hc
      have hdet' : a' * d - b * c' = 1 := by
        apply mul_left_cancel₀ hq0; linear_combination hdet
      have hcop : IsCoprime (L : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL))
      have hLc : (L : ℤ) ∣ c' := hcop.dvd_of_dvd_mul_left hL
      let g : SL(2, ℤ) := ⟨!![a', b; c', d], by rw [Matrix.det_fin_two_of]; exact hdet'⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]; simpa [g] using (ZMod.intCast_zmod_eq_zero_iff_dvd c' L).mpr hLc
      refine ⟨(⟨g, hg⟩, none), trivial, ?_⟩
      ext i k; fin_cases i <;> fin_cases k <;> simp [g, repT, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · have hd0 : (a : ZMod q) * d - b * c = 0 := by
        have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
        push_cast at this; simpa using this
      obtain ⟨J, hb, hd⟩ : ∃ J : ZMod q, (b : ZMod q) = (a : ZMod q) * J ∧ (d : ZMod q) = (c : ZMod q) * J := by
        by_cases ha : (a : ZMod q) = 0
        · have hc : (c : ZMod q) ≠ 0 := fun hc => hac
            ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc⟩
          refine ⟨d / c, ?_, ?_⟩
          · rw [ha, zero_mul]; rw [ha, zero_mul, zero_sub, neg_eq_zero] at hd0
            exact (mul_eq_zero.mp hd0).resolve_right hc
          · field_simp
        · refine ⟨b / a, ?_, ?_⟩
          · field_simp
          · field_simp; linear_combination hd0
      obtain ⟨u, hu⟩ : (q : ℤ) ∣ b - a * ((J.val : ℕ) : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val, hb]; ring
      obtain ⟨v, hv⟩ : (q : ℤ) ∣ d - c * ((J.val : ℕ) : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val, hd]; ring
      have hdet' : a * v - u * c = 1 := by
        apply mul_left_cancel₀ hq0; linear_combination hdet - a * hv + c * hu
      let g : SL(2, ℤ) := ⟨!![a, u; c, v], by rw [Matrix.det_fin_two_of]; exact hdet'⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]; simpa [g] using (ZMod.intCast_zmod_eq_zero_iff_dvd c L).mpr hL
      refine ⟨(⟨g, hg⟩, some ⟨J.val, ZMod.val_lt J⟩), trivial, ?_⟩
      ext i k; fin_cases i <;> fin_cases k <;> simp [g, repT, repU, Matrix.mul_apply, Fin.sum_univ_two, -ZMod.natCast_val] <;> linarith

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

def ptXY (p : ℝ × ℝ) : ℍ := ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)

theorem measurable_ofComplex_hp : Measurable (ofComplex : ℂ → ℍ) := by
  classical
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) =
      fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [hw, ofComplex_apply_of_im_pos hw]
    · simp only [Function.comp, hw, if_false]
      rw [ofComplex_apply_of_im_nonpos (not_lt.mp hw),
        ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id
    measurable_const

theorem ptXY_eq (p : ℝ × ℝ) : ptXY p = ofComplex (Complex.measurableEquivRealProd.symm p) := by
  unfold ptXY
  congr 1
  apply Complex.ext <;> simp

theorem measurable_ptXY : Measurable ptXY := by
  simp only [funext ptXY_eq]
  exact measurable_ofComplex_hp.comp Complex.measurableEquivRealProd.symm.measurable

theorem volume_eq_map_ptXY : (volume : Measure ℍ) = Measure.map ptXY
    (((volume : Measure ℝ).prod (volume.restrict (Set.Ioi 0))).withDensity
      fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  have hm := measurable_ptXY
  ext s hs
  have hp : (volume : Measure ℝ).prod (volume.restrict (Set.Ioi (0 : ℝ))) =
      (volume : Measure (ℝ × ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hset : ptXY ⁻¹' s ∩ Set.univ ×ˢ Set.Ioi 0 =
      Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ioi, Set.mem_image, ptXY_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by simpa using h2
      refine ⟨_, h1, ?_⟩
      rw [ofComplex_apply_of_im_pos h3]
    · rintro ⟨z, hz, hzp⟩
      refine ⟨?_, ?_⟩
      · rw [← hzp, ofComplex_apply]; exact hz
      · have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by
          rw [← hzp]; exact z.im_pos
        simpa using h3
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset,
    volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp

theorem measurableSet_strip : MeasurableSet strip := by
  have h : strip = (fun z : ℍ => z.re) ⁻¹' (Set.Ico 0 1) := rfl
  rw [h]
  exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico

theorem ptXY_re (x y : ℝ) (hy : 0 < y) : (ptXY (x, y)).re = x := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ptXY, ofComplex_apply_of_im_pos h]
  simp [UpperHalfPlane.re]

theorem restrict_strip_eq_map : (volume : Measure ℍ).restrict strip = Measure.map ptXY
    ((((volume : Measure ℝ).restrict (Set.Ico 0 1)).prod (volume.restrict (Set.Ioi 0))).withDensity
      fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  have hm := measurable_ptXY
  have hS := hm measurableSet_strip
  have h1 : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h2 : ptXY ⁻¹' strip ∩ Set.univ ×ˢ Set.Ioi 0 = Set.Ico 0 1 ×ˢ Set.Ioi 0 := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Ioi, Set.mem_Ico, strip, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [ptXY_re x y hy] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [ptXY_re x y hy]
      exact ⟨h, hy⟩
  rw [volume_eq_map_ptXY, Measure.restrict_map hm measurableSet_strip, restrict_withDensity hS, h1,
    Measure.restrict_restrict hS, h2, Measure.prod_restrict]

theorem strip_iterated :
    (∀ F : ℍ → ENNReal, Measurable F → ∫⁻ τ in strip, F τ = ∫⁻ y in Set.Ioi (0 : ℝ),
      (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2)) ∧
    ∀ F : ℍ → ℂ, IntegrableOn F strip → ∫ τ in strip, F τ = ∫ y in Set.Ioi (0 : ℝ),
      (∫ x in (0 : ℝ)..1, F (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
  have hm := measurable_ptXY
  have hd : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2)) := by fun_prop
  refine ⟨fun F hF => ?_, fun H hH => ?_⟩
  · rw [restrict_strip_eq_map, lintegral_map hF hm, lintegral_withDensity_eq_lintegral_mul _ hd (g := fun a => F (ptXY a)) (hF.comp hm)]
    simp only [Pi.mul_apply]
    rw [lintegral_prod_symm (fun a => ENNReal.ofReal (1 / a.2 ^ 2) * F (ptXY a))
      ((hd.mul (hF.comp hm)).aemeasurable)]
    refine lintegral_congr fun y => ?_
    rw [lintegral_const_mul (ENNReal.ofReal (1 / y ^ 2)) (f := fun x : ℝ => F (ptXY (x, y)))
      (hF.comp (hm.comp (measurable_id.prodMk measurable_const))), mul_comm]
    rfl
  · unfold IntegrableOn at hH
    rw [restrict_strip_eq_map] at hH ⊢
    have hI := (integrable_map_measure hH.1 hm.aemeasurable).1 hH
    rw [integral_map hm.aemeasurable hH.1,
      integral_withDensity_eq_integral_toReal_smul hd (by simp)]
    rw [integrable_withDensity_iff_integrable_smul' hd (by simp)] at hI
    have key : ∀ y : ℝ, ∫ x in Set.Ico (0 : ℝ) 1, (ENNReal.ofReal (1 / y ^ 2)).toReal • (H ∘ ptXY) (x, y) =
        (∫ x in (0 : ℝ)..1, H (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
      intro y
      rw [integral_smul, ENNReal.toReal_ofReal (by positivity), intervalIntegral.integral_of_le zero_le_one,
        integral_Ico_eq_integral_Ioc, Complex.real_smul]
      simp only [Function.comp_apply, ptXY]
      push_cast
      ring
    refine (integral_prod_symm _ hI).trans ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => key y)

end GlobalTheory.EisM

end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem ring_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  intro E
  haveI : Nontrivial (GlobalTheory.FN.ring E) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) UpperHalfPlane.I) h
    simp at h1
  haveI : NoZeroDivisors (GlobalTheory.FN.ring E) := by
    refine ⟨fun {a b} hab => ?_⟩
    have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1
    have ha := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E a ((hmem a).1 a.2)
    have hb := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E b ((hmem b).1 b.2)
    have h0 : ∀ τ, (a : ℍ → ℂ) τ * (b : ℍ → ℂ) τ = 0 := by
      intro τ
      have := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) τ) hab
      simpa using this
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff a b ha hb h0 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_mem_ring (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) {f : ℍ → ℂ} (hf : f ∈ ring E) :
    cmp g f ∈ ring E :=
  ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1 _).2 (GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat E g f hE (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1 f).1 hf))

noncomputable def cmpHom (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) : ring E →+* ring E where
  toFun a := ⟨cmp g a, cmp_mem_ring E g hE a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cmp_cmp_inv (g : GQ) (f : ℍ → ℂ) : cmp g (cmp g⁻¹ f) = f := by
  rw [← GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.1, inv_mul_cancel, GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.1]

theorem cmp_inv_cmp (g : GQ) (f : ℍ → ℂ) : cmp g⁻¹ (cmp g f) = f := by
  rw [← GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.1, mul_inv_cancel, GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.1]

theorem cmp_ringEquiv : ∀ (E : Subring ℂ) (g : GQ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    ∃ σ : GlobalTheory.FN.ring E ≃+* GlobalTheory.FN.ring E, ∀ a, ((σ a : GlobalTheory.FN.ring E) : ℍ → ℂ) = GlobalTheory.FN.cmp g a := by
  intro E g hE
  refine ⟨{ cmpHom E g hE with
    invFun := cmpHom E g⁻¹ hE
    left_inv := fun a => Subtype.ext (cmp_inv_cmp g a)
    right_inv := fun a => Subtype.ext (cmp_cmp_inv g a) }, fun a => rfl⟩

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.qExpansion_coeffs_mem_finitelyGenerated : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N w : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω), 0 < N → Lv ε.range N w f → HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) → ∃ S : Finset Ω, ∀ k, a k ∈ Subring.closure (S : Set Ω) := by
  first | exact @GlobalTheory.FN.qcoeff_finitelyGenerated | exact GlobalTheory.FN.qcoeff_finitelyGenerated | (intros; apply GlobalTheory.FN.qcoeff_finitelyGenerated <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.oddThetaProductSiegel_modularS_transform : ∀ (τ : ℍ) (z : ℂ), th (z / (τ : ℂ)) (ModularGroup.S • τ) = -Complex.I * ee (z ^ 2 / (2 * (τ : ℂ))) * th z τ := by
  first | exact @GlobalTheory.Sieg.ThInv.th_S | exact GlobalTheory.Sieg.ThInv.th_S | (intros; apply GlobalTheory.Sieg.ThInv.th_S <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_ext_clo_inj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ (L : Type) [CommRing L] (φ ψ : T.K →+* L), (∀ a, φ (T.io a) = ψ (T.io a)) → φ = ψ) ∧ (∀ (g : GQ) (a : GlobalTheory.FN.ring ε.range), ∃ a' : GlobalTheory.FN.ring ε.range, (a' : ℍ → ℂ) = GlobalTheory.FN.cmp g a ∧ T.sl g (T.io a) = T.io a') ∧ Function.Injective T.exp ∧ Function.Injective T.an := by
  intro Ω _ _ _ ε T
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L _ φ ψ h
    ext f
    obtain ⟨a, b, hb, hf⟩ := T.io_surj f
    have hb' : T.io b ≠ 0 := by
      intro h0
      exact hb (T.io_inj (by rw [h0, map_zero]))
    have hu : IsUnit (φ (T.io b)) := (IsUnit.mk0 _ hb').map φ
    have h1 : φ f * φ (T.io b) = ψ f * φ (T.io b) := by
      rw [← map_mul, hf, h a, h b, ← map_mul, hf]
    exact hu.mul_left_injective h1
  · intro g a
    have hE := ((GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε).1)
    have hm := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1
    have ha : InR ε.range (a : ℍ → ℂ) := (hm _).1 a.2
    have hc : InR ε.range (GlobalTheory.FN.cmp g a) := GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat ε.range g _ hE ha
    refine ⟨⟨GlobalTheory.FN.cmp g a, (hm _).2 hc⟩, rfl, ?_⟩
    exact T.sl_io g a _ rfl
  · exact T.exp.toRingHom.injective
  · haveI : Nontrivial Mero := (GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units).1
    exact T.an.injective

end GlobalTheory.FN
end

end

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repT q) := by
  first | exact @GlobalTheory.EisM.lRep_DT_repT | exact GlobalTheory.EisM.lRep_DT_repT | (intros; apply GlobalTheory.EisM.lRep_DT_repT <;> assumption)

end
end

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.unitStrip_integral_eq_iterated : (∀ F : ℍ → ENNReal, Measurable F → ∫⁻ τ in strip, F τ = ∫⁻ y in Set.Ioi (0 : ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2)) ∧ ∀ F : ℍ → ℂ, IntegrableOn F strip → ∫ τ in strip, F τ = ∫ y in Set.Ioi (0 : ℝ), (∫ x in (0 : ℝ)..1, F (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
  first | exact @GlobalTheory.EisM.strip_iterated | exact GlobalTheory.EisM.strip_iterated | (intros; apply GlobalTheory.EisM.strip_iterated <;> assumption)

end
end
