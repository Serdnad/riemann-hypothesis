module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ActsByFrameAct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.HTOsmulRight
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
public import Mathlib.Algebra.AffineMonoid.Basic
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

@[expose] public section

section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

section Prime

variable (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hint : IntLat Λ)
  (e : Fin r → S.V) (hind : LinearIndependent E e) (he : ∀ i, e i ∈ Λ) (P : HeightOneSpectrum (𝓞 E))
  (hloc : ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range e) →
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 E) (Set.range e))

include hU hint hind he hloc in
theorem residue_onto (c : Fin r) :
    ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧
      ∀ i, (o i - if i = c then 1 else 0) ∈ P.asIdeal := by
  haveI := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let mk := Ideal.Quotient.mk P.asIdeal
  let U : Submodule (𝓞 E ⧸ P.asIdeal) (Fin r → 𝓞 E ⧸ P.asIdeal) :=
    { carrier := {φ | ∃ y ∈ Λ, ∃ o : Fin r → 𝓞 E, (∀ i, S.hT y (e i) = (o i : E)) ∧ ∀ i, φ i = mk (o i)}
      zero_mem' := ⟨0, Λ.zero_mem, 0, fun i => by simp, fun i => by simp⟩
      add_mem' := by
        rintro φ ψ ⟨y, hy, o, ho, hφ⟩ ⟨y', hy', o', ho', hψ⟩
        refine ⟨y + y', Λ.add_mem hy hy', o + o', fun i => ?_, fun i => ?_⟩
        · simp [map_add (f := _), ho, ho']
        · simp [hφ, hψ]
      smul_mem' := by
        rintro κ φ ⟨y, hy, o, ho, hφ⟩
        obtain ⟨κ', rfl⟩ := Ideal.Quotient.mk_surjective κ
        refine ⟨cj κ' • y, Λ.smul_mem _ hy, fun i => κ' * o i, fun i => ?_, fun i => ?_⟩
        · rw [hT_cj_left, ho]; push_cast; ring
        · simp [hφ, mk] }
  have hUtop : U = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.mpr hne)
    let α : Fin r → 𝓞 E ⧸ P.asIdeal := fun i => f (fun j => if i = j then 1 else 0)
    have hfα : ∀ φ, f φ = ∑ i, φ i * α i := by
      intro φ
      rw [LinearMap.pi_apply_eq_sum_univ f φ]
      simp [α, smul_eq_mul]
    have hα0 : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      apply hf0
      refine LinearMap.ext fun φ => ?_
      rw [hfα, LinearMap.zero_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]
    choose α' hα' using fun i => Ideal.Quotient.mk_surjective (α i)
    have hmem := coeff_mem_P Λ hU e hind P hloc α' (by
      intro y hy
      choose o ho using fun i => hint y hy (e i) (he i)
      have hφ : (fun i => mk (o i)) ∈ U := ⟨y, hy, o, ho, fun i => rfl⟩
      have hz : f (fun i => mk (o i)) = 0 := hfU hφ
      rw [hfα] at hz
      refine ⟨∑ i, o i * α' i, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem]

        simpa [map_sum, map_mul, hα', mk] using hz
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hT_osmul_right, ho]; ring)
    obtain ⟨i, hi⟩ := hα0
    apply hi
    rw [← hα' i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
  have hc : (fun i => if i = c then (1 : 𝓞 E ⧸ P.asIdeal) else 0) ∈ U := by rw [hUtop]; trivial
  obtain ⟨y, hy, o, ho, hφ⟩ := hc
  refine ⟨y, hy, o, ho, fun i => ?_⟩
  rw [← Ideal.Quotient.eq]
  have := hφ i
  simp only at this
  by_cases hic : i = c
  · simp only [hic, if_true] at this ⊢; rw [map_one]; exact this.symm
  · simp only [hic, if_false] at this ⊢; rw [map_zero]; exact this.symm

include hU hint hind he hloc in
theorem exact_dual (c : Fin r) :
    ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (e i) = 0) ∧ ∃ o : 𝓞 E, S.hT y (e c) = (o : E) ∧ o ∉ P.asIdeal := by
  choose y hy o ho hP using fun j => residue_onto Λ hU hint e hind he P hloc j
  let G : Matrix (Fin r) (Fin r) (𝓞 E) := fun j i => o j i
  have hdet : G.det ∉ P.asIdeal := by
    intro hmem
    have h1 : (Ideal.Quotient.mk P.asIdeal).mapMatrix G = 1 := by
      ext j i
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
      have := Ideal.Quotient.eq.mpr (hP j i)
      rw [this]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    have := RingHom.map_det (Ideal.Quotient.mk P.asIdeal) G
    rw [h1, Matrix.det_one, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at this
    exact zero_ne_one this
  have key : ∀ i, S.hT (∑ j, cj (G.adjugate c j) • y j) (e i) = ((G.adjugate * G) c i : E) := by
    intro i

    rw [map_sum, LinearMap.sum_apply, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT_cj_left, ho]
  rw [Matrix.adjugate_mul] at key
  refine ⟨∑ j, cj (G.adjugate c j) • y j, Λ.sum_mem fun j _ => Λ.smul_mem _ (hy j), fun i hi => ?_,
    G.det, ?_, hdet⟩
  · rw [key, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hi)]; simp
  · rw [key, Matrix.smul_apply, Matrix.one_apply_eq]; simp

end Prime

end PI.NRL
end
end

section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem diffIdeal_ne_bot (D : D7) :
    Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ := by
  have h0 : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
    first
      | exact differentIdeal_ne_bot
      | exact differentIdeal_ne_bot (A := ℤ)
  first
    | exact Ideal.map_ne_bot_of_ne_bot h0
    | exact fun h => h0 ((Ideal.map_eq_bot_iff_of_injective
        (NoZeroSMulDivisors.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))).mp h)
    | exact fun h => h0 ((Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))).mp h)

theorem one_mem_ddS_neg (D : D7) (m : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hpow : ddS D ^ m = ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
      (differentIdeal ℤ (𝓞 D.host.F)) ^ m : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [ddS, FractionalIdeal.coeIdeal_pow]
  have hI : ddS D ^ m ≠ 0 := by
    rw [hpow, Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact pow_ne_zero _ (diffIdeal_ne_bot D)
  have hle : ddS D ^ m ≤ 1 := by
    rw [hpow]
    exact FractionalIdeal.coeIdeal_le_one
  rw [zpow_neg, zpow_natCast, ← FractionalIdeal.one_le]
  have h1 := FractionalIdeal.inv_anti_mono hI hle
  rwa [inv_one] at h1

theorem e_mem_lam (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : IsRowLat D F0 Λ) (a : Fin D.R.rS) : F0.e a ∈ Λ := by
  have hx : F0.e a ∈ XS D F0 := by
    apply Submodule.subset_span
    refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
    have h1 := one_mem_ddS_neg D (D.R.rS - (a : ℕ))
    rwa [Nat.cast_sub a.isLt.le] at h1
  rw [← hΛ.2.2] at hx
  exact (Submodule.mem_inf.mp hx).1

end PI.NRL
end
end
