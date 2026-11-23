module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle040
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem blowUpOf_mono {P W : Ideal (MRing ι R)} (h : P ≤ W) (u : J → MRing ι R) :
    blowUpOf P u ≤ blowUpOf W u := by
  intro F hF
  let φ := Polynomial.mapRingHom (Ideal.Quotient.factor h)
  have key : φ.comp (aeval (R := R) (blowUpSubst P u)).toRingHom =
      (aeval (R := R) (blowUpSubst W u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ]
      rfl
    · rintro ⟨_ | k, i⟩
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
  have e := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
  rw [blowUpOf, RingHom.mem_ker] at hF ⊢
  rw [← e, hF, map_zero]

theorem blowUpOf_isPrime {W : Ideal (MRing ι R)} (hW : W.IsPrime) (u : J → MRing ι R) :
    (blowUpOf W u).IsPrime := by
  have := hW
  exact RingHom.ker_isPrime _

theorem blowUpOf_comap_le {P : Ideal (MRing ι R)} {u : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) (hPH : blowUpOf P u ≤ H) {j₀ : J}
    (hj₀ : u j₀ ∉ H.comap (liftForm (ι := ι) (J := J) (R := R))) :
    blowUpOf (H.comap (liftForm (ι := ι) (J := J) (R := R))) u ≤ H := by
  have := hH
  let L := FractionRing (MRing (extIdx ι J) R ⧸ H)
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk H)
  have hq : ∀ y, q y = 0 ↔ y ∈ H := by
    intro y
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have hu₀ : q (liftForm (u j₀)) ≠ 0 := fun h0 => hj₀ ((hq _).mp h0)
  let ψ : MRing ι R ⧸ H.comap (liftForm (ι := ι) (J := J) (R := R)) →+* L :=
    Ideal.Quotient.lift _ (q.comp (liftForm (ι := ι) (J := J) (R := R)).toRingHom) fun a ha => (hq _).mpr ha
  let ε : Polynomial (MRing ι R ⧸ H.comap (liftForm (ι := ι) (J := J) (R := R))) →+* L :=
    Polynomial.eval₂RingHom ψ (q (newVar j₀) / q (liftForm (u j₀)))
  have hψ : ∀ a : MRing ι R, ψ (Ideal.Quotient.mk _ a) = q (liftForm a) := fun a =>
    Ideal.Quotient.lift_mk _ _ _

  have hrelq : ∀ j : J, q (newVar j) * q (liftForm (u j₀)) = q (liftForm (u j)) * q (newVar j₀) := by
    intro j
    have hr : newVar j * liftForm (u j₀) - newVar j₀ * liftForm (u j) ∈ H :=
      hPH (mem_blowUpOf_of_sub (P := P) (u := u) (j := j) (j' := j₀) (a := u j₀) (a' := u j)
        (by rw [show u j * u j₀ - u j₀ * u j = 0 from by ring]; exact P.zero_mem))
    have h1 := (hq _).mpr hr
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
    rw [h1, mul_comm]
  have key : ε.comp (aeval (R := R) (blowUpSubst (H.comap (liftForm (ι := ι) (J := J) (R := R))) u)).toRingHom =
      q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C,
        Polynomial.algebraMap_apply, ← Ideal.Quotient.mk_algebraMap]
      simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [hψ, AlgHom.commutes]
      rfl
    · rintro ⟨_ | k, i⟩
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        show ε (Polynomial.C (Ideal.Quotient.mk _ (u i)) * Polynomial.X) = q (newVar i)
        simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [hψ, ← mul_div_assoc, div_eq_iff hu₀]
        exact (hrelq i).symm
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        show ε (Polynomial.C (Ideal.Quotient.mk _ (X ⟨k, i⟩))) = q (X ⟨some k, i⟩)
        simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        rw [hψ, liftForm_X]
  intro F hF
  rw [blowUpOf, RingHom.mem_ker] at hF
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [hF, map_zero] at h3
  exact (hq F).mp h3.symm

end Helpers

theorem BlowUpHorizontalStrict.full : BlowUpHorizontalStrict.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hj
  obtain ⟨j₀, hj₀⟩ := hj
  obtain ⟨hWp, hBW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hPW₀ : P ≤ W.comap (liftForm (ι := ι) (J := J) (R := O)) := fun p hp => hBW (liftForm_mem_blowUpOf hp)
  have hle := blowUpOf_comap_le hWp hBW hj₀
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine le_antisymm (hmin.2 ⟨blowUpOf_isPrime (Ideal.comap_isPrime _ _) u,
    sup_le (blowUpOf_mono hPW₀ u) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hle) hle
  exact liftForm_mem_blowUpOf (P := W.comap (liftForm (ι := ι) (J := J) (R := O))) hxW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem BlowUpHorizontalMult.proof (hmin : BlowUpHorizontalMinimal.Statement.{u})
    (hchart : BlowUpHorizontalChartLength.Statement.{u}) : BlowUpHorizontalMult.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  have hm := hmin O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW
  obtain ⟨hWp, hBW, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  obtain ⟨-, -, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hrel
  have hcond : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    unfold divCycle at hW
    rw [dite_eq_right h] at hW
    exact hW rfl
  have hch := hchart O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  have := hWp
  have hp := PolynomialLocalizedLength.full (MRing ι O) (W.comap (liftForm (ι := ι) (J := J) (R := O))) (P ⊔ Ideal.span {x})
  unfold divCycle
  rw [dite_eq_left ⟨hm, hrel₀⟩, dite_eq_left hcond]
  congr 2
  exact (hp.symm.trans hch.symm : _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Chart

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

def chartSubst (a : J → MRing ι R) : (Σ o, extIdx ι J o) → Polynomial (MRing ι R)
  | ⟨none, j⟩ => Polynomial.C (a j) * Polynomial.X
  | ⟨some k, i⟩ => Polynomial.C (X ⟨k, i⟩)

theorem aeval_chartSubst_liftForm (a : J → MRing ι R) (p : MRing ι R) :
    aeval (chartSubst a) (liftForm p) = Polynomial.C p := by
  have e : (aeval (chartSubst a)).comp (liftForm : MRing ι R →ₐ[R] MRing (extIdx ι J) R) =
      Polynomial.CAlgHom := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftForm, chartSubst]
  exact DFunLike.congr_fun e p

theorem aeval_chartSubst_mem_of_mem_blowUpOf {P : Ideal (MRing ι R)} (hP : P.IsPrime)
    {u a : J → MRing ι R} {u₀ g : MRing ι R} (hg : g ∉ P) (h : ∀ j, u₀ * u j - g * a j ∈ P)
    {F : MRing (extIdx ι J) R} (hF : F ∈ blowUpOf P u) :
    aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P := by
  let π := Polynomial.mapRingHom (Ideal.Quotient.mk P)
  have key : (Polynomial.compRingHom (Polynomial.C (Ideal.Quotient.mk P g) * Polynomial.X)).comp
        (π.comp (aeval (R := R) (chartSubst a)).toRingHom) =
      (Polynomial.compRingHom (Polynomial.C (Ideal.Quotient.mk P u₀) * Polynomial.X)).comp
        (aeval (R := R) (blowUpSubst P u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [π, Polynomial.compRingHom]
      rfl
    · rintro ⟨_ | k, i⟩
      · have e : Ideal.Quotient.mk P (u₀ * u i) = Ideal.Quotient.mk P (g * a i) :=
          Ideal.Quotient.eq.mpr (h i)
        simp only [map_mul] at e
        simp [π, chartSubst, blowUpSubst, Polynomial.compRingHom]
        have e' : Polynomial.C (Ideal.Quotient.mk P (a i)) * Polynomial.C (Ideal.Quotient.mk P g) =
            Polynomial.C (Ideal.Quotient.mk P (u i)) * Polynomial.C (Ideal.Quotient.mk P u₀) := by
          rw [← Polynomial.C_mul, ← Polynomial.C_mul, mul_comm (Ideal.Quotient.mk P (u i)), e, mul_comm]
        rw [← mul_assoc, ← mul_assoc, e']
      · simp [π, chartSubst, blowUpSubst, Polynomial.compRingHom]
  have hF' : π (aeval (chartSubst a) F) = 0 := by
    have e := DFunLike.congr_fun key F
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
    rw [show aeval (blowUpSubst P u) F = 0 from RingHom.mem_ker.mp hF, map_zero] at e
    have hg' : Ideal.Quotient.mk P g ∈ nonZeroDivisors (MRing ι R ⧸ P) :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    exact (Polynomial.comp_C_mul_X_eq_zero_iff hg').mp e
  have hk : aeval (chartSubst a) F ∈ RingHom.ker π := hF'
  rwa [Polynomial.ker_mapRingHom, Ideal.mk_ker] at hk

theorem mem_of_aeval_chartSubst_mem {a : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) {P' : Ideal (MRing ι R)} (hP'H : P' ≤ H.comap (liftForm (J := J))) (j₀ : J)
    (ha : liftForm (a j₀) ∉ H)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ H)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P') :
    F ∈ H := by
  let L := FractionRing (MRing (extIdx ι J) R ⧸ H)
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk H)
  have hq : ∀ y, q y = 0 ↔ y ∈ H := by
    intro y
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have ha' : q (liftForm (a j₀)) ≠ 0 := fun h0 => ha ((hq _).mp h0)
  let ε : Polynomial (MRing ι R) →+* L :=
    Polynomial.eval₂RingHom (q.comp (liftForm (J := J) : MRing ι R →ₐ[R] _).toRingHom)
      (q (newVar j₀) / q (liftForm (a j₀)))
  have key : ε.comp (aeval (R := R) (chartSubst a)).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ε, liftForm_C]
    · rintro ⟨_ | k, i⟩
      · have h1 := (hq _).mpr (hrel i)
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
        simp only [ε, chartSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [← mul_div_assoc, div_eq_iff ha', mul_comm]
        exact h1.symm
      · simp [ε, chartSubst, liftForm]
  have hε : Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) P' ≤ RingHom.ker ε := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    exact (hq _).mpr (hP'H hp)
  have h2 := RingHom.mem_ker.mp (hε hF)
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [h3] at h2
  exact (hq F).mp h2

end Chart

theorem BlowUpStrictTransform.proof : BlowUpStrictTransform.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP e m H hϖH hH
  set Q := blowUpOf P (blowUpGens s g f m e) with hQ
  have hPp : P.IsPrime := hP.multiProj.isPrime

  obtain ⟨x, hx, hHmin⟩ : ∃ x : MRing (extIdx ι (BlowUpIdx ι)) O,
      (x = liftForm s ∨ x = newVar none) ∧ H ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    have hm : ∀ {F}, divCycle Q F H ≠ 0 → H ∈ (Q ⊔ Ideal.span {F}).minimalPrimes := by
      intro F hF
      unfold divCycle at hF
      split_ifs at hF with hW
      · exact hW.1
      · exact absurd rfl hF
    rcases hH with hH | hH
    · exact ⟨_, Or.inl rfl, hm hH⟩
    · exact ⟨_, Or.inr rfl, hm hH⟩
  obtain ⟨hHp, hQH, hHrel⟩ : H.IsPrime ∧ Q ≤ H ∧ IsRelevant H := by
    rcases hH with hH | hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
  have mnm : ∀ {y z}, y ∉ H → z ∉ H → y * z ∉ H := fun hy hz hyz => (hHp.mem_or_mem hyz).elim hy hz
  have hxH : x ∈ H := hHmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  set H₀ := H.comap (liftForm (J := BlowUpIdx ι)) with hH₀
  obtain ⟨hH₀p, hPH₀, hrel₀, -⟩ := comap_liftForm_facts hHp hQH hHrel
  have hϖH₀ : (C ϖ : MRing ι O) ∉ H₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖH

  obtain ⟨u₀, v₀, hu, hv, h⟩ := hD.unit_off_special H₀ hH₀p hPH₀ hrel₀ hϖH₀
  obtain ⟨i, hpm, hYi, -⟩ := blowUp_offSpecial hPp e hD.den_not_mem hHp hQH hHrel (u₀ := u₀) hv h
  set a := blowUpCof s m e u₀ v₀ with ha_def
  have haS : liftForm (a (some (some i))) ∉ H := by
    show liftForm (v₀ * powMonomial e i) ∉ H
    rw [map_mul]; exact mnm hv hpm
  have hrelH : ∀ j, newVar j * liftForm (a (some (some i))) -
      newVar (some (some i)) * liftForm (a j) ∈ H :=
    fun j => hQH (blowUpCof_relation hPp e hD.den_not_mem h j _)

  have hsH₀ : s ∈ H₀ := by
    rcases hx with rfl | rfl
    · exact hxH
    · have h3 := H.sub_mem (H.mul_mem_right (liftForm (a (some (some i)))) hxH) (hrelH none)
      rw [sub_sub_cancel] at h3
      have h4 : liftForm (u₀ * s) ∈ H := (hHp.mem_or_mem h3).resolve_left hYi
      rw [map_mul] at h4
      exact (hHp.mem_or_mem h4).resolve_left hu

  have hmin₀ : H₀ ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
    refine ⟨⟨hH₀p, sup_le hPH₀ ((Ideal.span_singleton_le_iff_mem _).mpr hsH₀)⟩,
      fun P' hP' hP'H₀ => ?_⟩
    have := hP'.1
    have hsP' : s ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
      (aeval (R := O) (chartSubst a))
    have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hQQ' : Q ⊔ Ideal.span {x} ≤ Q' := by
      refine sup_le (fun F hF => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      · exact Ideal.map_mono (le_sup_left.trans hP'.2)
          (aeval_chartSubst_mem_of_mem_blowUpOf hPp hD.den_not_mem (fun j => blowUpCof_spec e h j) hF)
      · rw [Ideal.mem_comap]
        rcases hx with rfl | rfl
        · rw [aeval_chartSubst_liftForm]
          exact Ideal.mem_map_of_mem _ hsP'
        · simp only [newVar, aeval_X, chartSubst]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (P'.mul_mem_left _ hsP'))
    have hQ'H : Q' ≤ H := fun F hF => mem_of_aeval_chartSubst_mem hHp hP'H₀ _ haS hrelH hF
    have hHQ' := hHmin.2 ⟨hQ'p, hQQ'⟩ hQ'H
    intro p hp
    have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
      rw [← aeval_chartSubst_liftForm a p]
      exact hHQ' hp
    simpa using Ideal.mem_map_C_iff.mp h5 0

  have := hH₀p
  unfold divCycle
  rw [dite_eq_left ⟨hmin₀, hrel₀⟩]
  have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {s}) H₀ hmin₀
  have hnz : multAt (P ⊔ Ideal.span {s}) H₀ ≠ 0 := by
    unfold multAt
    rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    intro hs
    obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr (hmin₀.1.2 hr0)
  have htn : (multAt (P ⊔ Ideal.span {s}) H₀).toNat ≠ 0 :=
    fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
  exact_mod_cast htn

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord pullDeg liftVar assocDeg assocVar FlagModel)

namespace FlagModelJoinLeftAlt

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocDeg_pullDeg (a : K → ℤ) :
    assocDeg (K₂ := K₂) (pullDeg (K' := K') a) = pullDeg (K' := K' ⊕ K₂) a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem assocVar_comp_liftVar :
    assocVar (ι := ι) (ι' := ι') ι₂ ∘ liftVar ι' = liftVar (Sum.elim ι' ι₂) :=
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := K') a - pullDeg (K' := K') b = pullDeg (K' := K') (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end FlagModelJoinLeftAlt


open FlagModelJoinLeftAlt in
theorem FlagModelJoinLeftAlt.proof (hVert : JoinVerticalDivisor.Statement)
    (hFlag : FlagPairJoinLeft.Statement) (hNum : PairNumberJoinLeft.Statement) :
    FlagModelJoinLeftAlt.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' _ _ F K₂ _ ι₂ _ w hZ hfn EB E'B hp hp'
  obtain ⟨ψ, -, -, -, hdeg, hdeg', hf, hg⟩ :=
    hFlag O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w N V E E' F.EB F.E'B F.pull F.pull' F.flag EB E'B hp hp'
  refine ⟨ψ, fun I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ => ?_⟩
  have hvert : ∀ i, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (joinCoord x F.z))
      (Fin.append F.flag.deg (fun l => pullDeg (K' := F.K') (y l)) i -
        Fin.append F.flag.deg' (fun l => pullDeg (K' := F.K') (y' l)) i)
      (Fin.append F.flag.f (fun l => rename (liftVar F.ι') (f l)) i)
      (Fin.append F.flag.g (fun l => rename (liftVar F.ι') (g l)) i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact F.flag.vert j
    · simp only [Fin.append_right, pullDeg_sub]
      exact hVert O Ω K ι x F.K' F.ι' F.z _ _ _ (hv j)
  have hH : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (d + 1) := by
    have h : (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q).IsHomogeneous (c + (d + 1 - c)) :=
      hG.rename_isHomogeneous.mul hQ.rename_isHomogeneous
    rwa [show c + (d + 1 - c) = d + 1 by omega] at h
  unfold FlagModel.value
  refine (hNum O Ω K ι x F.K' F.ι' F.z K₂ ι₂ w d F.model hZ
    (hfn.trans F.birat.symm) I I₁ hI hI₁ (N + r) _ _ _ _ hvert _ hH).trans ?_
  congr 1 <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [hdeg, hdeg', hf, hg, assocDeg_pullDeg, assocVar_comp_liftVar]

end GroundTheory.Heights₂.Heights.NumbersDVR
end
