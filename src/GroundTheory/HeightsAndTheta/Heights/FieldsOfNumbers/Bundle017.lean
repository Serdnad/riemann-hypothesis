module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle012
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Sub.Prod
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Graded

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
  {κ : Type*} [CommRing κ]

def blockSpecial (ρ : MRing ι F →+* κ) : MRing ι F →+* MvPolynomial K κ :=
  eval₂Hom (C.comp (ρ.comp C)) fun v => C (ρ (X v)) * X v.1

theorem blockSpecial_monomial (ρ : MRing ι F →+* κ) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    blockSpecial ρ (monomial d a) = C (ρ (monomial d a)) *
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) 1 := by
  have hT : (monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) (1 : κ)) =
      d.prod fun v n => (X v.1 : MvPolynomial K κ) ^ n := by
    rw [← prod_pow_blockWeight, monomial_eq, C_1, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [hT, blockSpecial, coe_eval₂Hom, eval₂_monomial, monomial_eq, map_mul, map_mul,
    map_finsuppProd, map_finsuppProd]
  simp only [RingHom.comp_apply, mul_pow, map_pow]
  rw [Finsupp.prod_mul, mul_assoc]

theorem coeff_blockSpecial (ρ : MRing ι F →+* κ) (f : MRing ι F) (e : K →₀ ℕ) :
    AddMonoidAlgebra.coeff (blockSpecial ρ f) e = ρ (weightedHomogeneousComponent (blockWeight ι) (⇑e) f) := by
  classical
  conv_lhs => rw [f.as_sum]

  rw [weightedHomogeneousComponent_apply, map_sum, coeff_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [blockSpecial_monomial, coeff_C_mul, coeff_monomial]
  have hiff : Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d) = e ↔
      Finsupp.weight (blockWeight ι) d = ⇑e := by
    rw [Equiv.symm_apply_eq]; rfl
  by_cases h : Finsupp.weight (blockWeight ι) d = ⇑e
  · simp [h]
  · have hn : Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d) ≠ e :=
      fun h' => h (hiff.mp h')
    simp only [hn, h, ↓reduceIte, mul_zero]

end Graded

theorem ValuativeCentre.proof : ValuativeCentre.Statement.{u} := by
  intro F _ K _ _ ι _ P hP
  have := hP.isPrime
  intro R hF
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hφ : ∀ p, φ p = 0 ↔ p ∈ P := fun p => by
    simp only [φ, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

  have hmax : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ P ∧
      ∀ j, R.valuation (φ (X ⟨k, j⟩)) ≤ R.valuation (φ (X ⟨k, i⟩)) := by
    intro k
    classical
    obtain ⟨i₀, hi₀⟩ := hP.relevant k
    obtain ⟨i, hi, hmx⟩ := Finset.exists_max_image
      (Finset.univ.filter fun j => (X ⟨k, j⟩ : MRing ι F) ∉ P)
      (fun j => R.valuation (φ (X ⟨k, j⟩))) ⟨i₀, by simp [hi₀]⟩
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun j => ?_⟩
    by_cases hj : (X ⟨k, j⟩ : MRing ι F) ∈ P
    · rw [(hφ _).mpr hj, map_zero]; exact zero_le
    · exact hmx j (by simp [hj])
  choose c hcP hcmax using hmax

  have hchart : ∀ p, chartMap P c p ∈ R := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [chartMap, aeval_C]; exact hF a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [chartMap, aeval_X, ← R.valuation_le_one_iff, map_div₀]
      have h0 : R.valuation (φ (X ⟨v.1, c v.1⟩)) ≠ 0 := by
        rw [Ne, Valuation.zero_iff, hφ]; exact hcP v.1
      exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hcmax v.1 v.2)
  let χ : MRing ι F →+* R := (chartMap P c).toRingHom.codRestrict R hchart
  have hχ : ∀ p, (χ p : L) = chartMap P c p := fun p => rfl
  let ρ : MRing ι F →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp χ
  let θ : MRing ι F →+* MvPolynomial K (IsLocalRing.ResidueField R) := blockSpecial ρ
  have hdeh : ∀ f b, IsMultiHomog f b → chartMap P c f = φ f / φ (chartMonomial c b) :=
    fun f b hf => MChartDehomog.proof F K ι P c hcP f b hf
  have hmon : ∀ b, φ (chartMonomial c b) ≠ 0 := fun b => by
    simp only [chartMonomial, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (fun h => hcP k ((hφ _).mp h))

  have hy : ∀ f, f ∈ RingHom.ker θ ↔
      ∀ b : K → ℕ, ρ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
    intro f
    rw [RingHom.mem_ker]
    constructor
    · intro h b
      have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm b)) h
      change AddMonoidAlgebra.coeff (blockSpecial ρ f) (Finsupp.equivFunOnFinite.symm b) = 0 at this
      simpa only [coeff_blockSpecial, Finsupp.coe_equivFunOnFinite_symm] using this
    · intro h
      ext e
      change AddMonoidAlgebra.coeff (blockSpecial ρ f) e = 0
      rw [coeff_blockSpecial, h]
  have hyform : ∀ f b, IsMultiHomog f b → (f ∈ RingHom.ker θ ↔ ρ f = 0) := by
    intro f b hf
    rw [hy]
    constructor
    · intro h
      have := h b
      rwa [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf] at this
    · intro h b'
      by_cases hb : b' = b
      · rw [hb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]; exact h
      · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hf hb, map_zero]
  refine ⟨RingHom.ker θ, ⟨RingHom.ker_isPrime θ, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro f hf b
    rw [hy] at hf ⊢
    intro b'
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    by_cases hbb : b' = b
    · rw [hbb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hb]; exact hf b
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hb hbb, map_zero]
  ·
    intro k
    refine ⟨c k, fun h => ?_⟩
    have hX := isWeightedHomogeneous_X F (blockWeight ι) (⟨k, c k⟩ : Σ k, ι k)
    rw [hyform _ _ hX] at h
    have h1 : χ (X ⟨k, c k⟩) = 1 := by
      apply Subtype.ext
      rw [hχ, chartMap, aeval_X]
      exact div_self (fun h' => hcP k ((hφ _).mp h'))
    simp only [ρ, RingHom.comp_apply, h1, map_one] at h
    exact one_ne_zero h
  ·
    intro f hf
    rw [hy]
    intro b
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    have h0 : χ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
      apply Subtype.ext
      rw [hχ, hdeh _ _ hb, (hφ _).mpr (hP.multiHomog f hf b), zero_div]
      rfl
    simp only [ρ, RingHom.comp_apply, h0, map_zero]
  ·
    intro b f g hf hg hgy
    change φ f / φ g ∈ R ∧ (f ∈ RingHom.ker θ ↔ φ f / φ g ∈ R.nonunits)
    have hgu : IsUnit (χ g) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact fun h => hgy ((hyform g b hg).mpr h)
    have hg0 : (χ g : L) ≠ 0 := fun h => hgu.ne_zero (Subtype.ext h)
    have hquot : φ f / φ g = ((χ f * ↑hgu.unit⁻¹ : R) : L) := by
      have e1 : φ f / φ g = (χ f : L) / (χ g : L) := by
        rw [hχ, hχ, hdeh f b hf, hdeh g b hg, div_div_div_cancel_right₀ (hmon b)]
      have e2 : (χ g : L) * ((↑hgu.unit⁻¹ : R) : L) = 1 := by
        rw [← Subring.coe_mul, IsUnit.mul_val_inv]; rfl
      rw [e1, div_eq_iff hg0, Subring.coe_mul, mul_assoc, mul_comm _ (χ g : L), e2, mul_one]
    rw [hquot, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_mul,
      hyform f b hf]
    refine ⟨Subtype.mem _, ?_⟩
    have hu : IsLocalRing.residue R (↑hgu.unit⁻¹ : R) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)
    simp only [ρ, RingHom.comp_apply, mul_eq_zero]
    exact ⟨Or.inl, fun h => h.resolve_right hu⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocLocalize.proof : DegZeroLocLocalize.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W hW y hy
  have hWp := h𝒲P W hW
  have : W.IsPrime := hWp.1.isPrime
  obtain ⟨c, f, g, hf, hg, hgP, hgW, rfl⟩ :=
    DegZeroLocQuot.proof F K ι P {W} (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact this)
      y hy
  have hgW' : g ∉ W := hgW W rfl
  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W' hW' => by
      rcases Finset.mem_insert.mp hW' with rfl | hW'
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have h' := (h𝒲P W' (h𝒲.mem_toFinset.mp hW')).1
        exact ⟨h'.isPrime, h'.multiHomog, h'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W' ∈ 𝒲, h ∉ W' := fun W' hW' =>
    hhS W' (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW'))
  obtain ⟨m, hm, hmW⟩ := exists_form_not_mem_of_isRelevant (H := W) hWp.1.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgmW : g * m ∉ W := fun h' => (this.mem_or_mem h').elim hgW' hmW
  have hgmP : g * m ∉ P := fun h' => hgmW (hWp.2 h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    ⟨_, div_mem_degZeroLoc P {W} hh hgm hgmP (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hgmW),
      ?_⟩, ?_⟩
  · rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hq0 _ hhP) (hq0 _ hgmP))]
  · have h1 := hq0 _ hgP
    have h2 := hq0 _ hhP
    simp only [map_mul]
    field_simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocSeparate.proof : DegZeroLocSeparate.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W₁ hW₁ W₂ hW₂ hle
  obtain ⟨hW₁p, hPW₁⟩ := h𝒲P W₁ hW₁
  obtain ⟨hW₂p, hPW₂⟩ := h𝒲P W₂ hW₂
  have : W₂.IsPrime := hW₂p.isPrime

  obtain ⟨f, c, hf, hfW₁, hfW₂⟩ := exists_form_mem_not_mem hW₁p.multiHomog hle

  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have hW' := (h𝒲P W (h𝒲.mem_toFinset.mp hW)).1
        exact ⟨hW'.isPrime, hW'.multiHomog, hW'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W ∈ 𝒲, h ∉ W := fun W hW =>
    hhS W (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW))

  obtain ⟨m, hm, hmW₂⟩ := exists_form_not_mem_of_isRelevant (H := W₂) hW₂p.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hfmW₂ : f * m ∉ W₂ := fun h' => (hW₂p.isPrime.mem_or_mem h').elim hfW₂ hmW₂
  have hfmP : f * m ∉ P := fun h' => hfmW₂ (hPW₂ h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, ?_, _,
    div_mem_degZeroLoc P {W₂} hh hfm hfmP
      (fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hfmW₂), ?_⟩
  ·
    rintro ⟨y, hy, hxy⟩
    obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := DegZeroLocQuot.proof F K ι P {W₁}
      (fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hW₁p.isPrime) y hy
    rw [hy', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hq0 h hhP) (hq0 g' hg'P)),
      ← map_mul, ← map_mul, ← map_mul, ← map_mul] at hxy
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ hxy)
    have h3 : h * g' ∈ W₁ := by
      have := W₁.sub_mem (W₁.mul_mem_right f' (W₁.mul_mem_right m hfW₁)) (hPW₁ h2)
      rwa [sub_sub_cancel] at this
    rcases hW₁p.isPrime.mem_or_mem h3 with h4 | h4
    exacts [hh𝒲 W₁ hW₁ h4, hg'W W₁ (Set.mem_singleton W₁) h4]
  ·
    rw [div_mul_div_comm, mul_comm (algebraMap _ _ (Ideal.Quotient.mk P (f * m))),
      div_self (mul_ne_zero (hq0 h hhP) (hq0 _ hfmP))]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocUnits.proof : DegZeroLocUnits.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲ne h𝒲
  have := hP.isPrime
  have hne : ∀ g : MRing ι F, g ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  intro x hx
  constructor
  · rintro ⟨y, hy, hxy⟩ W hW
    exact ⟨y, degZeroLoc_anti P (Set.singleton_subset_iff.mpr hW) hy, hxy⟩
  · intro h
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hx'⟩ :=
      DegZeroLocQuot.proof F K ι P 𝒲 (fun W hW => (h𝒲 W hW).1.isPrime) x hx
    by_cases hfW : ∃ W ∈ 𝒲, f ∈ W
    ·
      exfalso
      obtain ⟨W, hW, hfW⟩ := hfW
      have hWp : W.IsPrime := (h𝒲 W hW).1.isPrime
      obtain ⟨y, hy, hxy⟩ := h W hW
      obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := DegZeroLocQuot.proof F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) y hy
      rw [hx', hy', div_mul_div_comm,
        div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul,
        ← map_mul, ← map_mul] at hxy
      have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ hxy)
      have h3 : g * g' ∈ W := by
        have := W.sub_mem (W.mul_mem_right f' hfW) ((h𝒲 W hW).2 h2)
        rwa [sub_sub_cancel] at this
      rcases hWp.mem_or_mem h3 with h4 | h4
      exacts [hgW W hW h4, hg'W W (Set.mem_singleton W) h4]
    ·
      push Not at hfW
      obtain ⟨W₀, hW₀⟩ := h𝒲ne
      have hfP : f ∉ P := fun h' => hfW W₀ hW₀ ((h𝒲 W₀ hW₀).2 h')
      refine ⟨_, div_mem_degZeroLoc P 𝒲 hg hf hfP hfW, ?_⟩
      rw [hx', div_mul_div_comm, mul_comm (algebraMap _ _ _),
        div_self (mul_ne_zero (hne g hgP) (hne f hfP))]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem LocalIntegralClosureFinite.proof (hN : NoetherIntegralClosureFinite.Statement.{u})
    (hF : FunctionFieldFinite.Statement.{u}) (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (hFr : DegZeroLocFrac.Statement.{u}) :
    LocalIntegralClosureFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hdim W hW hle
  have := hP'.isPrime
  have := hW.isPrime
  set P := contractPrime j P'
  set φ := contractFracMap j P'
  set A' := (degZeroLoc P {W}).map φ
  set L := homFracDegZero P'
  choose u hu using hW.relevant
  obtain ⟨hRA, hloc⟩ := degZeroLoc_map_eq_mul_inv hQ hD P W hle u hu φ
  set S := Set.range fun v => φ (chartMap P u (X v))
  have hAL : ∀ a ∈ A', a ∈ L := by
    rintro _ ⟨a, ha, rfl⟩
    exact map_homFracDegZero_le j ι' P' ⟨a, mem_homFracDegZero_of_mem_degZeroLoc P {W} a ha, rfl⟩
  have hEL : IntermediateField.adjoin F S ≤ L :=
    IntermediateField.adjoin_le_iff.mpr fun _ hx => hAL _ (hRA (Algebra.subset_adjoin hx))
  have hAE : ∀ a ∈ A', a ∈ IntermediateField.adjoin F S := fun a ha => by
    obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
    exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin F S hr)
      (inv_mem (IntermediateField.algebra_adjoin_le_adjoin F S hd))
  have hκE : (homFracDegZero P).map φ ≤ IntermediateField.adjoin F S := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, w, hw, -, rfl⟩ := hFr F K (fun k => ι' (j k)) P
      (isMultiProjPrime_contractPrime j ι' hP') {W} (Set.finite_singleton W)
      (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hW) z hz
    rw [map_div₀]
    exact div_mem (hAE _ ⟨y, hy, rfl⟩) (hAE _ ⟨w, hw, rfl⟩)
  have hdeg : IntermediateField.relfinrank ((homFracDegZero P).map φ) L ≠ 0 :=
    hF F K K' j ι' P' hP' hdim
  rw [← IntermediateField.relfinrank_mul_relfinrank hκE hEL,
    IntermediateField.relfinrank_eq_finrank_of_le hEL] at hdeg
  exact exists_finset_integral_span hN (Set.finite_range _) A' L hRA hloc hEL
    (FiniteDimensional.of_finrank_pos (Nat.pos_of_ne_zero (right_ne_zero_of_mul hdeg)))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
