module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsCommutingProjectionImage
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle012
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PartialSumRootNonneg
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ProdShiftEqAevalProd
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ProductBoundThreeFactors

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

section Map

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tL (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f f' := by
    funext g
    simp only [tMap, coefX, Pi.add_apply, Submodule.coe_add, map_add (f := _), inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [tMap, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

end Map

section Hull

variable {n : ℕ} {ε : Fin n → Bool} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem exists_kStable_finiteDimensional_submodule_of_mem_Xs (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {θ : ℝ}
    {x : Fin n → M} (hx : x ∈ Xs (LemK.eeV E) (genSub E V) θ) :
    ∃ S : Submodule ℂ (Fin n → M), S ≤ Xs (LemK.eeV E) (genSub E V) θ ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensV E) S ∧ x ∈ S := by
  classical
  have hxg := (mem_eigenTensorSpace_gen_iff.1 hx).1
  choose m hm using fun c => exists_layer_of_mem_genSub hE hVk (hxg c)
  set K := Finset.univ.sup m
  have hxK : ∀ c, x c ∈ layer ε E V K := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hfdL : FiniteDimensional ℂ (layer ε E V K) := finiteDimensional_layer hVfd K
  have hLk := layer_kStable hE hVk K
  have := pi_submodule_finiteDimensional (n := n) (layer ε E V K)
  refine ⟨Submodule.pi Set.univ (fun _ => layer ε E V K) ⊓ Xs (LemK.eeV E) (genSub E V) θ, inf_le_right,
    Submodule.finiteDimensional_of_le inf_le_left, ?_, ⟨mem_pi_submodule_iff.2 hxK, hx⟩⟩
  intro a b hab f hf
  refine ⟨mem_pi_submodule_iff.2 fun c => ?_, eigenTensorSpace_stable hE a b hf.2⟩
  rw [entry_bounds_of_partialSum]
  refine add_mem (hLk a b hab _ (mem_pi_submodule_iff.1 hf.1 c)) ?_
  split_ifs
  · exact mem_pi_submodule_iff.1 hf.1 b
  · exact zero_mem _

end Hull

section Line

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D}

theorem line_V (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hmono : StrictAnti lam) (hGL : GapLap ε lam h)
    (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (s : Fin n) {N : Type*} [AddCommGroup N] [Module ℂ N]
    (EN : Fin n → Fin n → Module.End ℂ N) :
    ∃ ys ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' → ∃ c : ℂ, w' = c • ψ ys := by
  classical
  have hK2 := (k2V n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hGL hp hq).2
  have hKD : IsKUnitary ε E := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hE : IsGlRep E := hD.glRep
  have hXG : ∀ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ∈ Submodule.pi Set.univ (fun _ => genSub E V) :=
    fun y hy => by simpa [Submodule.mem_pi] using (mem_eigenTensorSpace_gen_iff.1 hy).1

  have hlift : ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' →
        ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y ∧
          ψ y = w' := by
    intro ψ hψ w' hw' hw'K
    obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.1 hw'
    obtain ⟨S, hSX, hfd, hSk, hy₀S⟩ := exists_kStable_finiteDimensional_submodule_of_mem_Xs hE hV.1 hV.2.1 hy₀
    obtain ⟨y, hyS, hyK, hyeq⟩ := partialSum_succ_alt hKD ψ hfd hSk (fun a b _ z hz => hψ a b z (hXG z (hSX hz)))
      hy₀S hw'K
    exact ⟨y, hSX hyS, hyK, hyeq⟩
  by_cases hex : ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ≠ 0 ∧
      IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y
  · obtain ⟨ys, hysX, hys0, hysK⟩ := hex
    refine ⟨ys, hysX, fun ψ hψ w' hw' hw'K => ?_⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    obtain ⟨c₁, c₂, hne, hrel⟩ := hK2 y ys hyX hysX hyK hysK
    by_cases hc1 : c₁ = 0
    · exfalso
      rw [hc1, zero_smul, zero_add] at hrel
      exact hys0 ((smul_eq_zero.1 hrel).resolve_left (hne.resolve_left (not_not.2 hc1)))
    · refine ⟨-(c₁⁻¹ * c₂), ?_⟩
      have h2 : c₁ • y = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hrel
      have hy : y = -(c₁⁻¹ * c₂) • ys := by
        calc y = c₁⁻¹ • (c₁ • y) := by rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
          _ = -(c₁⁻¹ * c₂) • ys := by rw [h2, smul_neg, smul_smul, neg_smul]
      rw [hy, map_smul]
  · refine ⟨0, zero_mem _, fun ψ hψ w' hw' hw'K => ⟨0, ?_⟩⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    have hy0 : y = 0 := by
      by_contra hy0
      exact hex ⟨y, hyX, hy0, hyK⟩
    rw [hy0, map_zero, zero_smul]

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem finFub (hIS : S0.IntSStatement) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r) (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN)
    (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ)
    (hμ : S7.IsMu lam' μ') (v₁ v₂ : T'.V) (ξ : Vp) (F : Mat k r → ℂ) (C : ℝ)
    (hFc : ContinuousOn F (UJset ε)) (hFb : ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (hrep : ∀ x ∈ UJset ε, F x = ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪v₂, S7.PsiM T' μ' ((Formalism.MainNotions.S.umat y)⁻¹ * x) v₁⟫_ℂ ∂(Formalism.REAL.muG ε))
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hne : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x ≠ 0) :
    ∃ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      aaFun T' μ' P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x ≠ 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hHW := hB.2.2.2.2.1
  have hHN := hB.2.2.2.2.2
  haveI : SigmaFinite μW := hHW.1
  haveI : SigmaFinite μN := hHN.1
  let integrand (y : Formalism.REAL.UJ ε)
      (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Vp :=
    F (Formalism.MainNotions.S.umat y) • (finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat y) p •
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
  have hint : Integrable (Function.uncurry integrand) ((Formalism.REAL.muG ε).prod (μW.prod μN)) :=
    finFub_int' hIS k r ε u lam' h z c Vp π μW μN P hP hB hgap hlam hgl T' μ' hμ v₁ v₂ ξ F C hFc hFb x hx
  by_contra hall
  push Not at hall
  apply hne
  have hae := ae_mem_unitary_nilpotent_product z μW μN hHW hHN
  have step1 : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x =
      ∫ p, ∫ y, integrand y p ∂(Formalism.REAL.muG ε) ∂(μW.prod μN) := by
    delta per sInt
    apply integral_congr_ae
    filter_upwards [hae] with p hp'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      unitary_hermitian_form_mul_mem hp'.1.1 hp'.2.1
    have hJ := cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem hs hx)
    show F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • _ = _
    rw [hrep _ hJ, ← integral_smul_const]
    congr 1
    funext y
    exact mul_smul _ _ _
  rw [step1, ← integral_integral_swap hint]
  have hz : ∀ y, ∫ p, integrand y p ∂(μW.prod μN) = 0 := by
    intro y
    dsimp only [integrand]
    rw [integral_smul]
    have hy := unitary_matrix_mem_set ε y
    have h0 := hall _ (cayley_conj_inv_mem_hermitian_group hP hy)
    unfold aaFun sInt psiCoef at h0
    have hfun : (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat y) p •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) =
        fun p => ⟪v₂, S7.PsiM T' μ' (P * ((P⁻¹ * Formalism.MainNotions.S.umat y * P)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹) v₁⟫_ℂ •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ := by
      funext p
      delta finKer
      rw [conj_inv_mul_conj _ _ _ hd]
    rw [hfun, h0, smul_zero]
  simp only [hz, integral_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
