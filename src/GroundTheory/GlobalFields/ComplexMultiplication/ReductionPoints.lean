module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

local notation "ι" => algebraMap 𝒪 K
local notation "ρ" => residue 𝒪

theorem exists_zw_of_notMem_range {X₁ Y₁ : K} (h₁ : (curveK K W).Equation X₁ Y₁)
    (hX : X₁ ∉ Set.range ι) :
    ∃ z w v : 𝒪, z ∈ maximalIdeal 𝒪 ∧ z ≠ 0 ∧ w ∈ maximalIdeal 𝒪 ∧ w ≠ 0 ∧
      w = z ^ 3 * v ∧ IsUnit v ∧ ρ v = 1 ∧ ι z / ι w = X₁ ∧ -1 / ι w = Y₁ := by
  have hι := IsFractionRing.injective 𝒪 K
  obtain ⟨t, htm, ht⟩ := exists_inv_mem_of_notMem_range K hX
  have hX0 : X₁ ≠ 0 := fun h => hX ⟨0, by rw [h, map_zero]⟩
  have hT0 : ι t ≠ 0 := by rw [ht]; exact inv_ne_zero hX0
  have ht0 : t ≠ 0 := fun h => hT0 (by rw [h, map_zero])
  have hXt : X₁ * ι t = 1 := by rw [ht]; exact mul_inv_cancel₀ hX0
  obtain ⟨u, hu⟩ : ∃ u : 𝒪, u = 1 + W.a₂ * t + W.a₄ * t ^ 2 + W.a₆ * t ^ 3 := ⟨_, rfl⟩
  have huu : IsUnit u := isUnit_of_residue_ne_zero (by
    simp [hu, residue_eq_zero_of_mem htm])
  have hE := (WeierstrassCurve.Affine.equation_iff _ _).1 h₁
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hE

  have keyK : (Y₁ * ι t ^ 2) ^ 2 + ι W.a₁ * ι t * (Y₁ * ι t ^ 2) +
      ι W.a₃ * ι t ^ 2 * (Y₁ * ι t ^ 2) = ι t * ι u := by
    rw [hu]
    simp only [map_add (f := _), map_mul, map_one, map_pow]
    linear_combination (ι t) ^ 4 * hE - (ι W.a₁ * Y₁ * ι t ^ 3 - ι t * (1 + X₁ * ι t +
      X₁ ^ 2 * ι t ^ 2) - ι W.a₂ * ι t ^ 2 * (1 + X₁ * ι t) - ι W.a₄ * ι t ^ 3) * hXt

  obtain ⟨S, hS⟩ : Y₁ * ι t ^ 2 ∈ Set.range ι := by
    by_contra hSn
    obtain ⟨s', hs'm, hs'⟩ := exists_inv_mem_of_notMem_range K hSn
    have hS0 : Y₁ * ι t ^ 2 ≠ 0 := fun h => hSn ⟨0, by rw [h, map_zero]⟩
    have hinv : Y₁ * ι t ^ 2 * ι s' = 1 := by rw [hs']; exact mul_inv_cancel₀ hS0
    have e : ι (1 + W.a₁ * t * s' + W.a₃ * t ^ 2 * s') = ι (t * u * s' ^ 2) := by
      simp only [map_add (f := _), map_mul, map_one, map_pow]
      linear_combination (ι s') ^ 2 * keyK - (1 + Y₁ * ι t ^ 2 * ι s' + ι W.a₁ * ι t * ι s' +
        ι W.a₃ * ι t ^ 2 * ι s') * hinv
    have e' := congrArg ρ (hι e)
    simp only [map_add (f := _), map_mul, map_one, map_pow, residue_eq_zero_of_mem htm] at e'
    simp at e'
  have key : S ^ 2 + W.a₁ * t * S + W.a₃ * t ^ 2 * S = t * u := by
    apply hι
    simp only [map_add (f := _), map_mul, map_pow, hS]
    exact keyK
  have hSS : S * (S + W.a₁ * t + W.a₃ * t ^ 2) ∈ maximalIdeal 𝒪 := by
    rw [show S * (S + W.a₁ * t + W.a₃ * t ^ 2) = t * u by linear_combination key]
    exact Ideal.mul_mem_right _ _ htm
  have hB : S + W.a₁ * t + W.a₃ * t ^ 2 ∈ maximalIdeal 𝒪 := by
    have hat : W.a₁ * t + W.a₃ * t ^ 2 ∈ maximalIdeal 𝒪 :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ htm)
        (Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_left _ _ htm))
    rcases (maximalIdeal.isMaximal 𝒪).isPrime.mem_or_mem hSS with h | h
    · rw [add_assoc]; exact Ideal.add_mem _ h hat
    · exact h
  obtain ⟨u', huu'⟩ : ∃ u' : 𝒪, u * u' = 1 := ⟨_, huu.mul_val_inv⟩
  obtain ⟨z, hz⟩ : ∃ z : 𝒪, z = -(S + W.a₁ * t + W.a₃ * t ^ 2) * u' := ⟨_, rfl⟩
  have htz : t = -S * z := by
    rw [hz]
    linear_combination (-u') * key - t * huu'
  have hz0 : z ≠ 0 := by rintro h; rw [h, mul_zero] at htz; exact ht0 htz
  have hS0 : S ≠ 0 := by rintro h; rw [h, neg_zero, zero_mul] at htz; exact ht0 htz
  have hzm : z ∈ maximalIdeal 𝒪 := by
    rw [hz]; exact Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 hB)
  obtain ⟨w, hw⟩ : ∃ w : 𝒪, w = t * z := ⟨_, rfl⟩
  have hwm : w ∈ maximalIdeal 𝒪 := hw ▸ Ideal.mul_mem_right _ _ htm
  have hw0 : w ≠ 0 := hw ▸ mul_ne_zero ht0 hz0
  obtain ⟨e, he⟩ : ∃ e : 𝒪, e = 1 - W.a₁ * z - W.a₂ * z ^ 2 - W.a₃ * w - W.a₄ * z * w -
      W.a₆ * w ^ 2 := ⟨_, rfl⟩
  have hwe : w * e = z ^ 3 := by
    have key' := key
    rw [hu, htz] at key'
    have : S * (w * e - z ^ 3) = 0 := by
      rw [he, hw, htz]
      linear_combination (-z ^ 2) * key'
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hS0)
  have hρe : ρ e = 1 := by
    simp [he, residue_eq_zero_of_mem hzm, residue_eq_zero_of_mem hwm]
  have heu : IsUnit e := isUnit_of_residue_ne_zero (by rw [hρe]; exact one_ne_zero)
  refine ⟨z, w, ↑heu.unit⁻¹, hzm, hz0, hwm, hw0, ?_, (heu.unit⁻¹).isUnit, ?_, ?_, ?_⟩
  · have h1 : e * ↑heu.unit⁻¹ = (1 : 𝒪) := heu.mul_val_inv
    linear_combination (↑heu.unit⁻¹ : 𝒪) * hwe - w * h1
  · have h1 : e * ↑heu.unit⁻¹ = (1 : 𝒪) := heu.mul_val_inv
    have := congrArg ρ h1
    rwa [map_mul, hρe, one_mul, map_one] at this
  · have hzK : ι z ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
    rw [hw, map_mul]
    field_simp
    linear_combination -hXt
  · have hzK : ι z ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
    have hSK := congrArg ι htz
    rw [map_mul, map_neg] at hSK
    rw [hw, map_mul]
    have hY : Y₁ = ι S / ι t ^ 2 := by rw [hS]; field_simp
    rw [hY]
    field_simp
    linear_combination (-1 : K) * hSK

theorem add_of_notMem_range' [DecidableEq K] [(W.map ι).IsElliptic]
    {X₁ Y₁ : K} (h₁ : (curveK K W).Nonsingular X₁ Y₁) (hX : X₁ ∉ Set.range ι) {x₂ y₂ : 𝒪}
    (h₂ : (curveK K W).Nonsingular (ι x₂) (ι y₂)) :
    ∃ (x₃ y₃ : 𝒪) (h₃ : (curveK K W).Nonsingular (ι x₃) (ι y₃)),
      WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ =
        WeierstrassCurve.Affine.Point.some _ _ h₃ ∧ ρ x₃ = ρ x₂ ∧ ρ y₃ = ρ y₂ := by
  obtain ⟨z', w, v, hzm, hz0, hwm, hw0, hwv, hvu, hρv, hX₁, hY₁⟩ :=
    exists_zw_of_notMem_range K W h₁.1 hX
  exact GroundTheory.Arith.Abelian.add_of_notMem_range_of_coords K W h₁ hX hzm hz0 hwm hw0 hwv hvu hρv hX₁ hY₁ h₂

section Good

variable [W.IsElliptic]

theorem nonsingular_residue_of_isElliptic {x y : 𝒪} (h : (curveK K W).Equation (ι x) (ι y)) :
    (curveRed W).Nonsingular (ρ x) (ρ y) :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_residue W (equation_of_map K W h))

variable [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem reducePoint_add (P Q : (curveK K W).Point) :
    reducePoint K W (P + Q) = reducePoint K W P + reducePoint K W Q := by
  rcases point_cases K W P with rfl | ⟨X₁, Y₁, h₁, rfl, hX₁⟩ | ⟨x₁, y₁, h₁, rfl⟩
  · rw [zero_add, reducePoint_zero, zero_add]
  · rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]
    · rw [reducePoint_some_notMem K W h₁ hX₁, reducePoint_some_notMem K W h₂ hX₂, add_zero]
      rcases point_cases K W (WeierstrassCurve.Affine.Point.some _ _ h₁ +
          WeierstrassCurve.Affine.Point.some _ _ h₂) with h0 | ⟨X, Y, h, hS, hX⟩ | ⟨x, y, h, hS⟩
      · rw [h0, reducePoint_zero]
      · rw [hS, reducePoint_some_notMem K W h hX]
      · exfalso
        have hn : (curveK K W).Nonsingular X₂ ((curveK K W).negY X₂ Y₂) :=
          (WeierstrassCurve.Affine.nonsingular_neg _ _).2 h₂
        obtain ⟨x₃, y₃, h₃, e, -, -⟩ := add_of_notMem_range' K W hn hX₂ h
        have hneg : -(WeierstrassCurve.Affine.Point.some _ _ h₂) =
            WeierstrassCurve.Affine.Point.some _ _ hn := WeierstrassCurve.Affine.Point.neg_some h₂
        have e' : WeierstrassCurve.Affine.Point.some _ _ h₁ =
            WeierstrassCurve.Affine.Point.some _ _ h₃ := by
          rw [← e, ← hS, ← hneg]; abel
        rw [WeierstrassCurve.Affine.Point.some.injEq] at e'
        exact hX₁ ⟨x₃, e'.1.symm⟩
    · have n₂ := nonsingular_residue_of_isElliptic K W h₂.1
      obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range' K W h₁ hX₁ h₂
      have n₃ : (curveRed W).Nonsingular (ρ x₃) (ρ y₃) := by rw [hx, hy]; exact n₂
      rw [e, reducePoint_some_integral K W h₃ n₃, reducePoint_some_notMem K W h₁ hX₁, zero_add,
        reducePoint_some_integral K W h₂ n₂, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
  · have n₁ := nonsingular_residue_of_isElliptic K W h₁.1
    rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]
    · obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range' K W h₂ hX₂ h₁
      rw [add_comm] at e
      have n₃ : (curveRed W).Nonsingular (ρ x₃) (ρ y₃) := by rw [hx, hy]; exact n₁
      rw [e, reducePoint_some_integral K W h₃ n₃, reducePoint_some_notMem K W h₂ hX₂, add_zero,
        reducePoint_some_integral K W h₁ n₁, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
    · have n₂ := nonsingular_residue_of_isElliptic K W h₂.1
      rw [reducePoint_some_integral K W h₁ n₁, reducePoint_some_integral K W h₂ n₂]
      by_cases hx : ρ x₁ = ρ x₂
      · by_cases hy : ρ y₁ = (curveRed W).negY (ρ x₂) (ρ y₂)
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
          rcases add_of_residue_neg K W h₁ h₂ n₁ n₂ hx hy with h0 | ⟨X, Y, h, hS, hX⟩
          · rw [h0, reducePoint_zero]
          · rw [hS, reducePoint_some_notMem K W h hX]
        · have hy' : ρ y₁ = ρ y₂ := by
            rcases WeierstrassCurve.Affine.Y_eq_of_X_eq n₁.1 n₂.1 hx with h | h
            · exact h
            · exact absurd h hy
          have hD : ρ (y₁ + y₂ + W.a₁ * x₁ + W.a₃) ≠ 0 := by
            intro h0; apply hy
            rw [map_add (f := _), map_add (f := _), map_add (f := _), map_mul] at h0
            simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁,
              WeierstrassCurve.map_a₃, ← hx]
            linear_combination h0
          obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_eq K W h₁ h₂ n₁ n₂ hx hy' hD
          rw [e, e', reducePoint_some_integral K W h₃ n₃]
      · obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_X_ne K W h₁ h₂ n₁ n₂ hx
        rw [e, e', reducePoint_some_integral K W h₃ n₃]

def reductionHom : (curveK K W).Point →+ (curveRed W).Point where
  toFun := reducePoint K W
  map_zero' := reducePoint_zero K W
  map_add' := reducePoint_add K W

theorem reductionHom_apply (P : (curveK K W).Point) : reductionHom K W P = reducePoint K W P :=
  rfl

end Good

end

end GroundTheory.Global
