module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RatLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem col_coeff {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {g : GAd σ J}
    (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) (j : Fin r) :
    ∃ c : Fin r → AF F ⊗[F] E, (∀ i, j ≤ i → c i = 0) ∧
      (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j + adMat F X *ᵥ c := by
  have h := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 h
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra hne
    obtain ⟨k, -, hik, hkj⟩ := hl (Finsupp.mem_support_iff.2 hne)
    exact absurd (hik.trans_lt hkj) (not_lt.2 hi)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun i a => a • (adMat F X)ᵀ i) (fun i => zero_smul _ _)] at e
    beta_reduce at e
    have e2 : adMat F X *ᵥ ⇑l = ∑ i, l i • (adMat F X)ᵀ i := by
      rw [Matrix.mulVec_eq_sum]; simp only [op_smul_eq_smul]
    rw [e2, e, add_sub_cancel]


omit [NumberField E] in
theorem par_of_unip {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {s : ℕ} (hs : s ≤ r) {d : Fin s → ℕ}
    (hd : Monotone d) {g : GAd σ J} (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) :
    ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J g).1 * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B := by
  choose c hc hce using col_coeff hg
  refine ⟨1 + Matrix.of fun i j => c (Fin.castLE hs j) (Fin.castLE hs i), fun i j hlt => ?_, ?_⟩
  · have hji : j < i := not_le.1 fun h => absurd hlt (not_lt.2 (hd h))
    have hle : Fin.castLE hs j ≤ Fin.castLE hs i := by
      rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hji.le
    simp [Matrix.one_apply_ne hji.ne', hc _ _ hle]
  · ext k j
    have h1 := congrFun (hce (Fin.castLE hs j)) k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply] at h1
    rw [Matrix.mul_apply, Matrix.mul_add, Matrix.add_apply, Matrix.mul_one, Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.of_apply] at h1 ⊢
    rw [h1]
    congr 1
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) (fun i => rfl)
    have : s ≤ i.val := by
      by_contra hlt
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    rw [hc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castLE]; omega), mul_zero]

end GlobalTheory.RatLevi

theorem GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S T : Finset (Fin r), S ⊆ T → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T →
        ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y S ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X S, γ = m * ν := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S T _ γ hγ hγT
  obtain ⟨s, hsdef⟩ : ∃ s, s = S.sup fun k => k.val + 1 := ⟨_, rfl⟩
  have hs : s ≤ r := hsdef ▸ Finset.sup_le fun k _ => k.2
  have hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := fun i => by
    rw [hsdef, Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨d, hddef⟩ : ∃ d : Fin s → ℕ, ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card := ⟨fun i => (S.filter (· < Fin.castLE hs i)).card, fun _ => rfl⟩
  have hdm : Monotone d := fun i j hij => by
    rw [hddef, hddef]
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, lt_of_lt_of_le hk.2 ?_⟩
    rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hij
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS d hddef
  have hp : γ⁻¹ ∈ parFlag σ J (X.submatrix id (Fin.castLE hs)) d :=
    ⟨GlobalTheory.RatLevi.par_of_unip hs hdm (inv_mem hγT), by rw [inv_inv]; exact GlobalTheory.RatLevi.par_of_unip hs hdm hγT⟩
  obtain ⟨u, huF, m, hmF, hpm, hr⟩ := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 _ hp
  refine ⟨m⁻¹, inv_mem (hr (inv_mem hγ)), by rw [hl]; exact inv_mem hmF, u⁻¹, by rw [hu]; exact inv_mem huF, ?_⟩
  rw [← inv_inv γ, hpm, mul_inv_rev]
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.CuspCocpt
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem cocompact_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X S) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S
  by_cases hS0 : S = ∅
  · subst hS0
    rw [unip_empty]
    refine ⟨Set.univ, ?_, fun u => ⟨1, Subgroup.one_mem _, Set.mem_univ _⟩⟩
    exact Set.Subsingleton.isCompact fun a _ b _ => Subsingleton.elim a b
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hσ := sigma_sigma h
  have hs : m.val + 1 ≤ r := m.2
  have hS : ∀ i : Fin r, i.val < m.val + 1 ↔ ∃ k ∈ S, i ≤ k := fun i =>
    ⟨fun hi => ⟨m, hm, Fin.le_def.2 (Nat.lt_succ_iff.1 hi)⟩,
      fun ⟨k, hk, hik⟩ => Nat.lt_succ_iff.2 (le_trans (Fin.le_def.1 hik) (Fin.le_def.1 (hm' k hk)))⟩
  have e := (GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (m.val + 1) hs hS
    (fun i => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl).1
  have hC : IsIsoCols σ J (X.submatrix id (Fin.castLE hs)) := isIsoCols_of_isWittFrame hW hσ hJ hs
  exact e ▸ cocompact_unipFlag hJ hσ hC _

end GlobalTheory.CuspCocpt
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.wittFrame_rank_le_and_exists_rational_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → 2 * (r + 1) ≤ n ∧ ∃ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F Y = adMat F X ∧ (matHom _ σ J w).1 * adMat F X = adMat F Y := by
  first | exact @GlobalTheory.ResidueEisenstein.Swap.two_mul_le_and_exists_ratPts_swap | exact GlobalTheory.ResidueEisenstein.Swap.two_mul_le_and_exists_ratPts_swap | (intros; apply GlobalTheory.ResidueEisenstein.Swap.two_mul_le_and_exists_ratPts_swap <;> assumption)
end

section

open GlobalTheory.Published.AbVarRed IsLocalRing

theorem _root_.GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω, ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧ ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  first | exact @GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove | exact GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove | (intros; apply GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_injective_points_larger_field_galois : ∀ (K Ω Ω' : Type) [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A], ∃ f : (ptOver K Ω ⟶ A) →* (ptOver K Ω' ⟶ A), Function.Injective f ∧ ∀ (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → ∀ x, f (specAut σ ≫ x) = specAut σ' ≫ f x := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois | exact GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois | (intros; apply GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.residue_perfect_and_char_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField (ResidueField R)] (L W : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L], IsAbove R K (algebraMap W L).range → PerfectField (ResidueField W) ∧ ∀ m : ℕ, (m : ResidueField R) ≠ 0 → (m : ResidueField W) ≠ 0 := by
  first | exact @GlobalTheory.AbVarRedRes.residue_perfect_and_char | exact GlobalTheory.AbVarRedRes.residue_perfect_and_char | (intros; apply GlobalTheory.AbVarRedRes.residue_perfect_and_char <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finset_fixing_point_locallyFiniteType : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, ∃ s : Finset Ω, ∀ σ : Ω ≃ₐ[K] Ω, (∀ a ∈ s, σ a = a) → specAut σ ≫ x = x := by
  first | exact @GlobalTheory.PtFin.exists_finset_fix | exact GlobalTheory.PtFin.exists_finset_fix | (intros; apply GlobalTheory.PtFin.exists_finset_fix <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_fixedField_point_of_fixed_by_subgroup : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω)) (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, (∀ σ ∈ H, specAut σ ≫ x = x) → ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left, spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_fixedField_point | exact GlobalTheory.Published.AbVarRed.exists_fixedField_point | (intros; apply GlobalTheory.Published.AbVarRed.exists_fixedField_point <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.inertia_conj_mem_smul' : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (g σ : Ω ≃ₐ[K] Ω), σ ∈ inertia K V → g * σ * g⁻¹ ∈ inertia K (g • V) := by
  first | exact @GlobalTheory.inertia_conj_mem_smul | exact GlobalTheory.inertia_conj_mem_smul | (intros; apply GlobalTheory.inertia_conj_mem_smul <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.inertia_lift_of_purelyInseparable_alt : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra L Ω'] [Algebra K Ω'] (j : Ω →ₐ[K] Ω'), (∀ y : Ω', ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m) → ∀ (V' : ValuationSubring Ω') (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[L] Ω'), (∀ x, σ' (j x) = j (σ x)) → σ ∈ inertia K (V'.comap (j : Ω →+* Ω')) → σ' ∈ inertia L V' := by
  first | exact @GlobalTheory.inertia_lift_of_purelyInseparable | exact GlobalTheory.inertia_lift_of_purelyInseparable | (intros; apply GlobalTheory.inertia_lift_of_purelyInseparable <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.not_mem_div_uniformizer_pow_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → ∀ x : Ω, x ≠ 0 → ∃ n : ℕ, x / algebraMap K Ω (algebraMap R K π) ^ n ∉ V := by
  first | exact @GlobalTheory.not_mem_div_uniformizer_pow | exact GlobalTheory.not_mem_div_uniformizer_pow | (intros; apply GlobalTheory.not_mem_div_uniformizer_pow <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], (∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m) → (∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l) ∧ {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  first | exact @GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite | exact GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite | (intros; apply GlobalTheory.Proof.torsionUnramified_imp_tate_and_infinite <;> assumption)
end
