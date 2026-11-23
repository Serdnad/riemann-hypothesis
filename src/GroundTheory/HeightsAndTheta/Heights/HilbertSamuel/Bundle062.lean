module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle012
public import Mathlib.Data.Finsupp.Interval
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenDegMatAct

section Subst

variable {J : Type} [Fintype J]

def linSubst (B : Matrix J J ℚ) : MvPolynomial J ℚ →ₐ[ℚ] MvPolynomial J ℚ :=
  aeval fun i => ∑ j, C (B i j) * X j

theorem linSubst_comp (B B' : Matrix J J ℚ) :
    (linSubst B).comp (linSubst B') = linSubst (B' * B) := by
  apply MvPolynomial.algHom_ext
  intro i

  simp only [linSubst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
  Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem linSubst_one [DecidableEq J] : linSubst (1 : Matrix J J ℚ) = AlgHom.id ℚ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [linSubst, Matrix.one_apply, apply_ite C, ite_mul]

theorem exists_inv [DecidableEq J] {B : Matrix J J ℚ} (hB : IsInvMat B) : ∃ B' : Matrix J J ℚ, B * B' = 1 ∧ B' * B = 1 := by
  classical
  obtain ⟨B', h⟩ := hB
  refine ⟨B', ?_, ?_⟩ <;> rw [Matrix.ext_iff_mulVec] <;> intro v <;>
    simp [← Matrix.mulVec_mulVec, (h v).1, (h v).2]

def linEquiv [DecidableEq J] (B B' : Matrix J J ℚ) (h₁ : B * B' = 1) (h₂ : B' * B = 1) :
    MvPolynomial J ℚ ≃ₐ[ℚ] MvPolynomial J ℚ :=
  AlgEquiv.ofAlgHom (linSubst B) (linSubst B') (by rw [linSubst_comp, h₂, linSubst_one])
    (by rw [linSubst_comp, h₁, linSubst_one])

theorem isHomogeneous_linSubst (B : Matrix J J ℚ) {f : MvPolynomial J ℚ} {n : ℕ} (hf : f.IsHomogeneous n) :
    (linSubst B f).IsHomogeneous n := by
  have h := hf.aeval (fun i => ∑ j, C (B i j) * X j) (n := 1) fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C J (B i j)).mul (isHomogeneous_X ℚ j)
  simpa [linSubst] using h

end Subst

section Ideals

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem coneMap_matAct (B : Matrix J J ℚ) (x : J → Ω) :
    coneMap ℚ (matAct B x) = (coneMap ℚ x).comp (linSubst B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [coneMap, matAct, linSubst, Finset.sum_mul, mul_assoc, Polynomial.algebraMap_apply]

theorem coordIdeal_matAct (B : Matrix J J ℚ) (x : J → Ω) :
    coordIdeal ℚ (matAct B x) = (coordIdeal ℚ x).comap (linSubst B) := by
  ext f
  simp [coordIdeal, RingHom.mem_ker, coneMap_matAct]


omit [Fintype J] in
theorem map_coordIdeal_int (x : J → Ω) :
    (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) = coordIdeal ℚ x := by
  have hring : ((coneMap ℚ x : MvPolynomial J ℚ →+* Polynomial Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneMap]
    · intro i
      simp [coneMap]
  have hker : coordIdeal ℤ x = (coordIdeal ℚ x).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [coordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := J) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial J ℤ) (MvPolynomial J ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := J))) (MvPolynomial J ℚ)
    (coordIdeal ℚ x)
  rw [e] at h
  rw [hker]
  exact h

end Ideals

section Hilbert

variable {κ : Type} [Fintype κ]

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem isWeightedHomogeneous_iff (f : MvPolynomial (Ix κ) ℚ) (m : Unit → ℕ) :
    IsWeightedHomogeneous (blockWeight (GlobalTheory κ)) f m ↔ f.IsHomogeneous (m ()) := by
  have hdeg : ∀ d : Ix κ →₀ ℕ, ∑ i : κ, d ⟨(), i⟩ = Finsupp.weight 1 d := by
    intro d
    have h1 : d.degree = Finsupp.weight 1 d := by
      rw [Finsupp.degree_eq_weight_one]
      rfl
    rw [← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    exact (Fintype.sum_unique (fun u : Unit => ∑ y : GlobalTheory κ u, d ⟨u, y⟩)).symm
  have hw : ∀ d : Ix κ →₀ ℕ, Finsupp.weight (blockWeight (GlobalTheory κ)) d = fun _ => Finsupp.weight 1 d := by
    intro d
    funext u
    cases u
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
    simp [blockWeight]
  simp only [IsHomogeneous, IsWeightedHomogeneous, hw]
  constructor
  · intro h d hd
    exact congrFun (h hd) ()
  · intro h d hd
    funext u
    exact h hd

theorem mem_weighted_linSubst (B : Matrix (Ix κ) (Ix κ) ℚ) {m : Unit → ℕ} {f : MvPolynomial (Ix κ) ℚ}
    (hf : f ∈ weightedHomogeneousSubmodule ℚ (blockWeight (GlobalTheory κ)) m) :
    linSubst B f ∈ weightedHomogeneousSubmodule ℚ (blockWeight (GlobalTheory κ)) m := by
  rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff] at hf ⊢
  exact isHomogeneous_linSubst B hf

theorem hilbFn_comap [DecidableEq κ] (B B' : Matrix (Ix κ) (Ix κ) ℚ) (h₁ : B * B' = 1) (h₂ : B' * B = 1)
    (P : Ideal (MRing (GlobalTheory κ) ℚ)) : NumbersDVR.hilbFn (P.comap (linSubst B)) = NumbersDVR.hilbFn P := by
  set e := linEquiv B B' h₁ h₂
  have hc : P.comap (linSubst B) = P.comap e := by
    ext f
    rfl
  have hIJ : P = (P.comap e).map (e : MRing (GlobalTheory κ) ℚ →+* MRing (GlobalTheory κ) ℚ) :=
    (Ideal.map_comap_of_surjective _ e.surjective P).symm
  set E := Ideal.quotientEquivAlg (R₁ := ℚ) (P.comap e) P e hIJ
  have hpiece : ∀ m : Unit → ℕ, (NumbersDVR.gradedPiece (P.comap e) m).map E.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece P m := by
    intro m
    ext y
    simp only [NumbersDVR.gradedPiece, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨e f, mem_weighted_linSubst B hf, ?_⟩
      simp [E, Ideal.quotientEquivAlg_mk]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨_, ⟨e.symm g, mem_weighted_linSubst B' hg, rfl⟩, ?_⟩
      simp [E, Ideal.quotientEquivAlg_mk]
  funext m
  unfold NumbersDVR.hilbFn
  rw [hc]
  split_ifs
  · rw [← hpiece, LinearEquiv.finrank_map_eq]
  · rfl

end Hilbert

end GenDegMatAct

theorem GenDegMatAct.proof : GenDegMatAct.Statement := by
  intro D Ω _ _ κ _ x B hB
  classical
  obtain ⟨B', h₁, h₂⟩ := GenDegMatAct.exists_inv hB
  unfold genDeg
  rw [GenDegMatAct.map_coordIdeal_int, GenDegMatAct.map_coordIdeal_int, GenDegMatAct.coordIdeal_matAct]
  unfold NumbersDVR.intNum
  congr 2
  convert GenDegMatAct.hilbFn_comap B B' h₁ h₂ (coordIdeal ℚ x)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockBirationalHilbert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def blockSum (γ : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, γ ⟨k, i⟩

omit [Fintype K] in
theorem isMultiHomog_monomial {γ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (h : blockSum γ = a) (r : ℤ) :
    IsMultiHomog (monomial γ r : MRing ι) a := by
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  exact congrFun h k

omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b c : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b)
    (habc : a + b = c) : IsMultiHomog (f * g) c := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, ← habc, Pi.add_apply]

omit [Fintype K] in
theorem isMultiHomog_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (d j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h1 := isMultiHomog_monomial (ι := ι) (γ := 0) (a := 0) (by funext k; simp [blockSum]) 1
    simpa using h1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact isMultiHomog_mul (h j (Finset.mem_insert_self j s))
      (ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj')) rfl


open Classical in
def monoSet (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) :=
  (Finset.Icc 0 (Finsupp.equivFunOnFinite.symm fun p : (Σ k, ι k) => a p.1)).filter (blockSum · = a)

theorem mem_monoSet {a : K → ℕ} {γ : (Σ k, ι k) →₀ ℕ} : γ ∈ monoSet a ↔ blockSum γ = a := by
  classical
  unfold monoSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨Finset.mem_Icc.mpr ⟨by simp, fun p => ?_⟩, h⟩⟩
  rw [Finsupp.coe_equivFunOnFinite_symm, ← h]
  exact Finset.single_le_sum (f := fun i => γ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)

omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem aeval_monomial_int (y : (Σ k, ι k) → Ω) (γ : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    aeval y (monomial γ r : MRing ι) = ((r : ℚ) : Ω) * aeval y (monomial γ (1 : ℤ) : MRing ι) := by
  simp [aeval_monomial]


omit [Fintype K] in
theorem valueSpan_le (y : (Σ k, ι k) → Ω) (a : K → ℕ) (W : Submodule ℚ Ω)
    (hW : ∀ γ : (Σ k, ι k) →₀ ℕ, blockSum γ = a → aeval y (monomial γ (1 : ℤ) : MRing ι) ∈ W) :
    valueSpan y a ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩

  rw [g.as_sum, map_sum]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  rw [aeval_monomial_int, ← Rat.smul_def]
  exact W.smul_mem _ (hW γ (funext fun k => hg γ hγ k))

theorem finiteDimensional_valueSpan (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    FiniteDimensional ℚ (valueSpan y a) := by
  classical
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ
    (((monoSet a).image fun γ => aeval y (monomial γ (1 : ℤ) : MRing ι) : Finset Ω) : Set Ω))
    (valueSpan_le y a _ fun γ hγ => Submodule.subset_span ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨γ, mem_monoSet.mpr hγ, rfl⟩


omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem finrank_le_of_mul [CharZero Ω] {V W : Submodule ℚ Ω} [FiniteDimensional ℚ W] {t : Ω} (ht : t ≠ 0)
    (h : V ≤ W.comap (LinearMap.mulLeft ℚ t)) : Module.finrank ℚ V ≤ Module.finrank ℚ W := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ t) := fun a b hab => mul_left_cancel₀ ht hab
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj V)]
  exact Submodule.finrank_mono (Submodule.map_le_iff_le_comap.mpr h)

end BlockBirationalHilbert


open BlockBirationalHilbert in
theorem BlockBirationalHilbert.proof (hV : HilbFnValueSpan.Statement) : BlockBirationalHilbert.Statement := by
  intro K _ _ ι _ Ω _ _ y k₀ hy hbir m
  classical
  choose i hi using hy
  have hV' := hV K ι Ω y
  have := finiteDimensional_valueSpan (Ω := Ω) y

  have L : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else 0) =
      (Module.finrank ℚ (valueSpan y (blockDeg k₀ n)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk, blockDeg]
  have M : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else m k) =
      (Module.finrank ℚ (valueSpan y (fun k => if k = k₀ then n else m k)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk]

  set m₀ : K → ℕ := fun k => if k = k₀ then 0 else m k with hm₀
  let β : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.1 ≠ k₀ ∧ p.2 = i p.1 then m p.1 else 0
  have hβ : blockSum β = m₀ := by
    funext k
    by_cases hk : k = k₀ <;> simp [blockSum, β, hk, m₀]
  set u : Ω := aeval y (monomial β (1 : ℤ) : MRing ι) with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, aeval_monomial, map_one, one_mul, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
    rcases p with ⟨k, j⟩
    have h0 : β ⟨k, j⟩ ≠ 0 := Finsupp.mem_support_iff.mp hp
    simp only [β, Finsupp.coe_equivFunOnFinite_symm] at h0
    split_ifs at h0 with h
    · obtain ⟨_, rfl⟩ := h
      exact hi k
    · exact absurd rfl h0

  have key : ∀ α ∈ monoSet (ι := ι) m₀, ∃ (c : ℕ) (g h : MRing ι), IsMultiHomog g (blockDeg k₀ c) ∧
      IsMultiHomog h (blockDeg k₀ c) ∧ aeval y h ≠ 0 ∧
      aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y h = aeval y g * u := fun α hα =>
    hbir m₀ _ _ (isMultiHomog_monomial (mem_monoSet.mp hα) 1) (isMultiHomog_monomial hβ 1) hu
  choose c g h hg hh hh0 hgh using key
  refine ⟨∑ a ∈ (monoSet (ι := ι) m₀).attach, c a.1 a.2, fun n => ⟨?_, ?_⟩⟩
  ·
    rw [L, M]
    refine Nat.cast_le.mpr (finrank_le_of_mul hu (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨monomial β 1 * monomial γ 1,
      isMultiHomog_mul (isMultiHomog_monomial hβ 1) (isMultiHomog_monomial hγ 1) ?_, by
        simp only [map_mul, hu_def]⟩
    funext k; by_cases hk : k = k₀ <;> simp [hk, m₀, blockDeg]
  ·
    rw [M, L]
    have hH : aeval y (∏ a ∈ (monoSet (ι := ι) m₀).attach, h a.1 a.2) ≠ 0 := by
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun a _ => hh0 a.1 a.2
    refine Nat.cast_le.mpr (finrank_le_of_mul (mul_ne_zero (inv_ne_zero hu) hH)
      (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]

    set γ₀ := γ.filter (fun p => p.1 = k₀) with hγ₀
    set α := γ.filter (fun p => ¬ p.1 = k₀) with hα_def
    have hsplit : γ₀ + α = γ := Finsupp.filter_add_filter_not γ _
    have hα : blockSum α = m₀ := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, m₀]
    have hγ₀' : blockSum γ₀ = blockDeg k₀ n := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, blockDeg]
    have hαS : α ∈ monoSet (ι := ι) m₀ := mem_monoSet.mpr hα
    have hmem : (⟨α, hαS⟩ : {x // x ∈ monoSet (ι := ι) m₀}) ∈ (monoSet (ι := ι) m₀).attach :=
      Finset.mem_attach _ _
    refine Submodule.subset_span ⟨monomial γ₀ 1 * g α hαS *
      ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, h a.1 a.2,
      isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_monomial hγ₀' 1) (hg α hαS) rfl)
        (isMultiHomog_prod _ _ (fun a => blockDeg k₀ (c a.1 a.2)) fun a _ => hh a.1 a.2) ?_, ?_⟩
    · funext k
      by_cases hk : k = k₀
      · simp only [Pi.add_apply, Finset.sum_apply, blockDeg, hk, if_true]
        rw [← Finset.add_sum_erase _ _ hmem]
        ring
      · simp [blockDeg, hk, Finset.sum_apply]
    · have e1 : aeval y (monomial γ (1 : ℤ) : MRing ι) =
          aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι) := by
        rw [← map_mul, monomial_mul, hsplit, mul_one]
      rw [map_mul, map_mul, e1, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hmem]
      have e2 := hgh α hαS
      calc aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)
          = (u⁻¹ * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by
            rw [inv_mul_cancel₀ hu, one_mul]
        _ = u⁻¹ * (aeval y (g α hαS) * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by ring
        _ = u⁻¹ * (aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y (h α hαS)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by rw [e2]
        _ = u⁻¹ * (aeval y (h α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι)) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageHilb.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsBlockImage y k₀ M N x → ∀ n : ℕ,
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
          ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) =
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockImageTop.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (y : (Σ k, ι k) → Ω) (k₀ : K) (A : HermLine ι)
    (M : Matrix (Ix κ) (ι k₀) ℤ) (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω)
    (m : ConeMetric (C := ℂ) (ι := Ix κ)),
    I.IsFamily → IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ →
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsBlockImage y k₀ M N x → A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ →
    IsSmoothHerm A → IsSmoothMetric m → (∀ z ∈ mcPts (mCoordIdeal y), A.h z = m.ρ (blockMapC k₀ M z)) →
    I K ι (mCoordIdeal y) (D + 1) (fun _ => A) = top I x m D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ScaledFSHProps.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)),
    IsSemipositiveRel P0 P (scaledFSH ι) ∧ IsConjInvariantH (scaledFSH ι) ∧
      MonomialsBounded P (scaledFSH ι) (fun _ => 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
