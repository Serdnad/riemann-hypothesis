module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle251
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Formalism.PolynomialDimension.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.StrongApproximationSL2

section General

variable {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) (ε : R)

def prodMonoid : Submonoid (Matrix (Fin 2) (Fin 2) R) where
  carrier := {x | ∃ γ : Matrix (Fin 2) (Fin 2) K, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) R,
    h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map φ * h}
  one_mem' := ⟨1, by simp, 1, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨γ, hγ, h, hh, hε, rfl⟩ ⟨γ', hγ', h', hh', hε', rfl⟩
    set G := γ'.map φ with hG
    have hGd : G.det = 1 := by
      rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ', map_one]
    have h1 : G * G.adjugate = 1 := by rw [Matrix.mul_adjugate, hGd, one_smul]
    have h2 : G.adjugate * G = 1 := by rw [Matrix.adjugate_mul, hGd, one_smul]
    have h3 : G.adjugate.det = 1 := by
      have := congrArg Matrix.det h1
      rwa [det_mul, hGd, one_mul, det_one] at this
    refine ⟨γ * γ', by rw [det_mul, hγ, hγ', one_mul], G.adjugate * h * G * h', ?_, ?_, ?_⟩
    · rw [det_mul, det_mul, det_mul, h3, hh, hGd, hh']; simp
    · have e : G.adjugate * h * G * h' - 1 = G.adjugate * (h - 1) * G * h' + (h' - 1) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2, Matrix.sub_mul, Matrix.one_mul]
        abel
      rw [e, smul_add, hε', ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.mul_smul, hε]
    · rw [Matrix.map_mul, ← hG]
      calc γ.map φ * h * (G * h') = γ.map φ * (G * G.adjugate) * h * (G * h') := by rw [h1, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]

theorem upper_mem (hε : ε * ε = ε) (t : K) (s : R) : !![1, φ t + ε * s; 0, 1] ∈ prodMonoid φ ε := by
  refine ⟨!![1, t; 0, 1], by simp [det_fin_two], !![1, ε * s; 0, 1], by simp [det_fin_two], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lower_mem (hε : ε * ε = ε) (t : K) (s : R) : !![1, 0; φ t + ε * s, 1] ∈ prodMonoid φ ε := by
  refine ⟨!![1, 0; t, 1], by simp [det_fin_two], !![1, 0; ε * s, 1], by simp [det_fin_two], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem mem_of_elementary (M : Submonoid (Matrix (Fin 2) (Fin 2) R)) (hU : ∀ x : R, !![1, x; 0, 1] ∈ M)
    (hL : ∀ x : R, !![1, 0; x, 1] ∈ M) (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) (s u : R)
    (hu : (g 1 0 + g 1 1 * s) * u = 1) : g ∈ M := by
  rw [det_fin_two] at hg
  have e : g = !![1, (g 0 0 + g 0 1 * s - 1) * u; 0, 1] * !![1, 0; g 1 0 + g 1 1 * s, 1] *
      !![1, (g 1 1 - 1) * u; 0, 1] * !![1, 0; -s, 1] := by
    have e1 : g * !![1, 0; s, 1] = !![1, (g 0 0 + g 0 1 * s - 1) * u; 0, 1] * !![1, 0; g 1 0 + g 1 1 * s, 1] *
        !![1, (g 1 1 - 1) * u; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination (-(g 0 0 + g 0 1 * s - 1)) * hu
      · linear_combination (-(g 0 1) - (g 0 0 + g 0 1 * s - 1) * (g 1 1 - 1) * u) * hu - u * hg
      · linear_combination (-(g 1 1 - 1)) * hu
    have e2 : (!![1, 0; s, 1] * !![1, 0; -s, 1] : Matrix (Fin 2) (Fin 2) R) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← e1, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [e]
  exact M.mul_mem (M.mul_mem (M.mul_mem (hU _) (hL _)) (hU _)) (hL _)

theorem exists_unit_of_idem {c d a b : R} (haa : a * a = a) (hbb : b * b = b) (hab : a * b = 0) (hs : a + b = 1)
    (hw : IsUnit (a * c + b * d)) : ∃ s u : R, (c + d * s) * u = 1 := by
  obtain ⟨w, hw⟩ := hw.exists_right_inv
  have h1 : a * c * w = a := by linear_combination a * hw - c * w * haa - d * w * hab
  have h2 : b * d * w = b := by linear_combination b * hw - d * w * hbb - c * w * hab
  refine ⟨b * (1 - c) * w, a * w + b, ?_⟩
  have h3 : c + d * (b * (1 - c) * w) = a * c + b := by linear_combination (1 - c) * h2 - c * hs
  rw [h3]
  linear_combination hs + h1 + hbb + (c + w) * hab + c * w * haa

theorem mem_closure_of_dense [TopologicalSpace R] [IsTopologicalRing R] (hε : ε * ε = ε)
    (hd : ∀ (x : R) (U : Set R), U ∈ 𝓝 x → ∃ t : K, ∃ s : R, φ t + ε * s ∈ U)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) (s u : R) (hu : (g 1 0 + g 1 1 * s) * u = 1) :
    g ∈ closure (prodMonoid φ ε : Set (Matrix (Fin 2) (Fin 2) R)) := by
  have key : ∀ f : R → Matrix (Fin 2) (Fin 2) R, Continuous f → (∀ t s, f (φ t + ε * s) ∈ prodMonoid φ ε) →
      ∀ x, f x ∈ (prodMonoid φ ε).topologicalClosure := by
    intro f hf h x
    change f x ∈ closure _
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨t, s, hts⟩ := hd x _ (hf.continuousAt.preimage_mem_nhds hV)
    exact ⟨_, hts, h t s⟩
  refine mem_of_elementary (prodMonoid φ ε).topologicalClosure ?_ ?_ g hg s u hu
  · refine key (fun x => !![1, x; 0, 1]) ?_ (upper_mem φ ε hε)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine key (fun x => !![1, 0; x, 1]) ?_ (lower_mem φ ε hε)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end General

theorem idem_of_isPlacesIdem {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, one_mul]
    · rw [h2 w hw, zero_mul]
  · change evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)
    by_cases hv : v ∈ S₂
    · rw [h3 v hv, one_mul]
    · rw [h4 v hv, zero_mul]

theorem strongApprox_SL2 : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : Matrix (Fin 2) (Fin 2) (AF F), g.det = 1 → g ∈ closure {x : Matrix (Fin 2) (Fin 2) (AF F) | ∃ γ : Matrix (Fin 2) (Fin 2) F, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) (AF F), h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map (algebraMap F (AF F)) * h} := by
  intro F _ _ S₁ S₂ ε hε hS g hg
  have hdet : ∑ i : Fin 2, ![-g 0 1, g 0 0] i * g 1 i = 1 := by
    rw [det_fin_two] at hg
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hg
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 2) (g 1) ![-g 0 1, g 0 0] (hdet ▸ isUnit_one)
  rw [Fin.sum_univ_two] at h3 h4
  obtain ⟨s, u, hu⟩ := exists_unit_of_idem (h1 0) (h1 1) (h2 0 1 (by decide)) h3 h4
  refine mem_closure_of_dense (algebraMap F (AF F)) ε (idem_of_isPlacesIdem hε) (fun x U hU => ?_) g hg s u hu
  obtain ⟨t, -, s, h⟩ := GlobalTheory.T.additive_strongApproximation_avoiding_finset F S₁ S₂ ε hε hS x U hU ∅
  exact ⟨t, s, h⟩

end GlobalTheory.StrongApproximationSL2
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.RealWeil
open scoped Matrix ENNReal SchwartzMap

namespace GlobalTheory.SvNForm

theorem sympl_neg_self {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) : sympl w (-w) = 0 := by
  have h1 : pPart (-w) = -pPart w := rfl
  have h2 : qPart (-w) = -qPart w := rfl
  simp only [sympl, h1, h2, inner_neg_right, real_inner_comm (pPart w) (qPart w)]
  ring

theorem rhoFun_neg_cancel {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℂ) :
    rhoFun w (rhoFun (-w) u) = u := by
  rw [rhoFun_rhoFun, sympl_neg_self, add_neg_cancel, rhoFun_zero]
  simp

theorem step (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ)
    (hB : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h)
    (f f' g g' : Sch (Fin n)) (G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n)) (hGc : Continuous G)
    (hG : ∀ w, ⇑(G w) = rhoFun w ⇑f)
    (hGb : ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N) :
    (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' =
      ∫ w, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * B (G w) f' := by
  obtain ⟨L, hL⟩ := hB f'
  set ip : ℂ := ∫ x, f x * starRingEnd ℂ (g x) with hip
  set c : (Fin n ⊕ Fin n → ℝ) → ℂ := fun w => starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) with hc
  have hcc : Continuous c := Complex.continuous_conj.comp (GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g').1
  have hint : ∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) := by
    intro k m
    obtain ⟨C, N, hC⟩ := hGb k m
    set d : ℕ := Module.finrank ℝ (Fin n ⊕ Fin n → ℝ)
    obtain ⟨C', hC'⟩ := (GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g').2 (N + (d + 1))
    have hsc : Continuous fun w => SchwartzMap.seminorm ℂ k m (G w) :=
      ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin n)) ℂ).continuous_seminorm (k, m)).comp hGc
    have hI : Integrable (fun w : Fin n ⊕ Fin n → ℝ => (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by push_cast; linarith)
    refine (hI.const_mul (C' * |C|)).mono' ((hcc.norm.mul hsc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    have e1 : ‖c w‖ = ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖ := by simp [hc]
    have h1 := hC' w
    have h2 := hC w
    have hs0 : 0 ≤ SchwartzMap.seminorm ℂ k m (G w) := apply_nonneg _ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hs0, e1]
    have hrp : (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ)) = ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    rw [hrp]
    set M := ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖
    have hM : 0 ≤ M := norm_nonneg _
    have hA : (0:ℝ) < (1 + ‖w‖) ^ N := by positivity
    have hB' : (0:ℝ) < (1 + ‖w‖) ^ (d + 1) := by positivity
    have h3 : SchwartzMap.seminorm ℂ k m (G w) ≤ |C| * (1 + ‖w‖) ^ N :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hA.le)
    rw [pow_add] at h1
    calc M * SchwartzMap.seminorm ℂ k m (G w) ≤ M * (|C| * (1 + ‖w‖) ^ N) := mul_le_mul_of_nonneg_left h3 hM
      _ = |C| * (M * ((1 + ‖w‖) ^ N * (1 + ‖w‖) ^ (d + 1))) * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          field_simp
      _ ≤ |C| * C' * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          gcongr
      _ = C' * |C| * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by ring
  have hpt : ∀ x, (ip • g') x = ∫ w, c w * G w x := by
    intro x
    simp only [SchwartzMap.smul_apply, smul_eq_mul, hc, hG]
    rw [GlobalTheory.T.schrodinger_orthogonality_relation n f g g' x]
  have key := GlobalTheory.T.schwartz_functional_integral_comm (Fin n ⊕ Fin n → ℝ) volume n L G c (ip • g') hGc hcc hint hpt
  calc ip * B g' f' = B (ip • g') f' := by rw [hL, hL, map_smul, smul_eq_mul]
    _ = ∫ w, c w * L (G w) := by rw [hL]; exact key
    _ = ∫ w, c w * B (G w) f' := by simp only [hL]

theorem core : ∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hB hherm hpos hinv
  refine GlobalTheory.T.hermitian_form_const_mul_inner n B hherm hpos fun f f' g g' => ?_
  obtain ⟨G, hGc, hG, hGb⟩ := GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound n f
  obtain ⟨G', hG'c, hG', hG'b⟩ := GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound n f'
  have s1 := step n B hB f f' g g' G hGc hG hGb
  have s2 := step n B hB f' f g' g G' hG'c hG' hG'b
  set mc : Sch (Fin n) → Sch (Fin n) → (Fin n ⊕ Fin n → ℝ) → ℂ :=
    fun u v w => ∫ t, rhoFun w ⇑u t * starRingEnd ℂ (v t) with hmc
  have pw : ∀ w, starRingEnd ℂ (mc g g' w) * B (G w) f' = mc g' g (-w) * starRingEnd ℂ (B (G' (-w)) f) := by
    intro w
    have e1 : B (G w) f' = B f (G' (-w)) :=
      hinv w f (G' (-w)) (G w) f' (hG w) (by rw [hG' (-w), rhoFun_neg_cancel])
    have e2 : mc g g' w = ∫ t, g t * starRingEnd ℂ (rhoFun (-w) ⇑g' t) := by
      simp only [hmc]
      conv_lhs => rw [← rhoFun_neg_cancel w ⇑g']
      exact GlobalTheory.T.schrodinger_rep_unitary n w ⇑g (rhoFun (-w) ⇑g')
    rw [e1, hherm, e2, ← integral_conj]
    simp only [hmc, map_mul, Complex.conj_conj]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  rw [s1]
  have e3 : (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g =
      starRingEnd ℂ ((∫ x, f' x * starRingEnd ℂ (g' x)) * B g f) := by
    rw [map_mul, ← integral_conj, hherm g f]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  simp only [hmc] at pw
  rw [e3, s2, ← integral_conj]
  simp only [pw]
  have hneg := integral_neg_eq_self (fun w => (∫ t, rhoFun w ⇑g' t * starRingEnd ℂ (g t)) *
    starRingEnd ℂ (B (G' w) f)) (volume : Measure (Fin n ⊕ Fin n → ℝ))
  rw [hneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [map_mul]

theorem schrodinger_intertwiner_l2_const : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := GlobalTheory.T.rho_invariant_form_const_mul_inner core

end GlobalTheory.SvNForm
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | exact GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | (intros; apply GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.idempotentAdeleOfPlaces_mul_eq_sum_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ a : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * a = ∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w) (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapInf w).proj (AlgHom.id F E) a) + ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v) (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapFin v).proj (AlgHom.id F E) a) := by
  first | exact @GlobalTheory.PlaceIdemSum.idem_mul_eq_sum | exact GlobalTheory.PlaceIdemSum.idem_mul_eq_sum | (intros; apply GlobalTheory.PlaceIdemSum.idem_mul_eq_sum <;> assumption)
end

section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem numOf_eq_ofRecord (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (h1 : D.s.Del = (Del : ℚ))
    (h2 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) : GlobalTheory.RunDepth.numOf D L = ofRecord D L Del h0 := by
  have hm : (D.R.m : ℝ) ≠ 0 := by
    intro h
    have := L.etaSz_pos
    rw [h2, h, zero_mul] at this
    exact lt_irrefl _ this
  have e1 : ⌊((D.s.Del : ℚ) : ℝ)⌋₊ = Del := by
    rw [h1, Rat.cast_natCast, Nat.floor_natCast]
  have e2 : ⌊LevelStarExponents.h0 L⌋₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [h2, mul_div_cancel_left₀ _ hm]
    rw [this, Nat.floor_natCast]
  have e3 : (fun z => D.hc (GlobalTheory.RunDepth.plOf D z)) = fun z => D.hc (Formalism.BasicNotions.tauPl D z) := by
    funext z
    obtain ⟨b, t⟩ := z
    cases b <;> rfl
  unfold GlobalTheory.RunDepth.numOf ofRecord
  simp only [e1, e2, e3]

theorem numOf_Fj_eq_ofRecord :
    ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) → ∀ (j : ℕ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)), (GlobalTheory.RunDepth.numOf D L).Fj j w = (ofRecord D L Del h0).Fj j w := by
  intro D L Del h0 h1 h2 j w
  rw [numOf_eq_ofRecord D L Del h0 h1 h2]

end GlobalTheory.BigOn
end

section

noncomputable section

namespace GlobalTheory.Div.CoefExtension

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem exists_ext_placeEx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' (c0L i) c0' ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hW hF hM gramR c0R c0L hT i K' _ jL σ' hσ
  obtain ⟨c0', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', hc, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hM.jV hT hc hL hW hF.pl_onto hF.muVal⟩

end GlobalTheory.Div.CoefExtension
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.cmQuadraticCharacter_eq_prod_realSigns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  first | exact @GlobalTheory.EtaSignReal.eta_eq_prod_sign | exact GlobalTheory.EtaSignReal.eta_eq_prod_sign | (intros; apply GlobalTheory.EtaSignReal.eta_eq_prod_sign <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_unitaryHeckeCharacter_extending_baseCharacter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  first | exact @GlobalTheory.HeckeExtend.exists_extend_hecke | exact GlobalTheory.HeckeExtend.exists_extend_hecke | (intros; apply GlobalTheory.HeckeExtend.exists_extend_hecke <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.right_derivative_multiplicity_map_value_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau), SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) ∧ ∀ X ∈ lieAt V τ, ∃ u : M.sm τ, (u : M.H τ) = dRep (M.rep τ) X (v τ : M.H τ) ∧ Rder θ V τ X (T v) = T (Function.update v τ u) := by
  first | exact @GlobalTheory.HolRead.MultDer.rder_eq | exact GlobalTheory.HolRead.MultDer.rder_eq | (intros; apply GlobalTheory.HolRead.MultDer.rder_eq <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.kappaProduct_pow_algebraicModulusOneAll : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (m : ℕ), StandardLatticesGL3.Mod1All (B.kappa ^ m) := by
  first | exact @GlobalTheory.KappaPowMod.kappa_pow_mod1All | exact GlobalTheory.KappaPowMod.kappa_pow_mod1All | (intros; apply GlobalTheory.KappaPowMod.kappa_pow_mod1All <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.dualWeyl_dim_formula_duality_bound : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (dim la : ℚ) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) ∧ (∀ s : ℕ, (∀ i, la i ≤ s) → dim (fun i => s - la (Fin.rev i)) = dim la) ∧ ∀ w : ℤ, (dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := by
  first | exact @GlobalTheory.WeylDimBound.dim_weyl_dual_bound | exact GlobalTheory.WeylDimBound.dim_weyl_dual_bound | (intros; apply GlobalTheory.WeylDimBound.dim_weyl_dual_bound <;> assumption)
end
