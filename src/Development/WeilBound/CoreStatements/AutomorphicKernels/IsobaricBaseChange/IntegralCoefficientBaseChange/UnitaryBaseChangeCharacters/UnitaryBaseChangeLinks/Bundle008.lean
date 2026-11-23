module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1381
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.Bundle006
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormHasseCent

theorem inv_hh {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (k : GL (Fin n) K) : (k.val * cT σ k.val)⁻¹ = cT σ (k⁻¹).val * (k⁻¹).val :=
  Matrix.inv_eq_right_inv (by rw [Matrix.mul_assoc, cT_units_left', Units.mul_inv])

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  intro E _ _ _ hU n γ h hγ hP hconj hloc
  set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσdef
  have hσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  set N := cT σ (h⁻¹).val * (h⁻¹).val with hN
  have hγ' : cT σ γ.val * 1 * γ.val = 1 := hγ
  have hinv := inv_of_unit σ h γ hconj
  have hγγ : γ.val * cT σ γ.val = 1 := by
    rw [Matrix.mul_one] at hγ'; exact mul_eq_one_comm.1 hγ'
  have hcomm : γ.val * N = N * γ.val := by
    have := congrArg (γ.val * ·) hinv
    simp only [← Matrix.mul_assoc, hγγ, Matrix.one_mul] at this
    rw [hN]; simpa only [Matrix.mul_assoc] using this.symm
  obtain ⟨m, hm⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val N hP.2.2.1 hcomm
  have hherm : cT σ (aeval γ.val m) = aeval γ.val m := by
    rw [← hm]; exact herm_of σ hσ h
  have hM : (h.val * cT σ h.val)⁻¹ = aeval γ.val m := by rw [inv_hh, ← hN, hm]
  have hsr := GlobalTheory.T.isConjSelfReciprocal_of_dvd_elliptic_polynomial E n _ hP
  have hfix := GlobalTheory.T.involution_fixes_polynomial_image E n γ hγ hP m hherm
  have hloc' : ∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E)) := (fun w hw => by
    obtain ⟨c, hc1, hc2⟩ := hloc w hw
    refine ⟨c, hc1, ?_⟩
    rw [hc2, inv_hh, ← hm, hN, ← map_inv]
    rw [Matrix.map_mul, cT_map hU w hw]; rfl)
  have hfin : ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
    intro r Q hQ hx v
    by_cases hs : ∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v
    · exact GlobalTheory.T.local_norm_at_split_place E r Q _ hx v hs
    · refine GlobalTheory.T.nonsplit_centraliser_norm_element E hU n γ hγ hP m hloc' r Q hQ hx v (fun w w' hw hw' => ?_)
      by_contra hne
      exact hs ⟨w, w', hne, hw, hw'⟩
  have hinf := GlobalTheory.T.totally_positive_real_places E n γ hγ hP m (fun τ => by rw [← hm]; exact GlobalTheory.T.conj_transpose_mul_posDef E n h τ)
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_norm_solution_fields E n γ hγ hP hsr m (fun r Q hQ =>
    GlobalTheory.T.global_norm_of_local_norms E r Q _ (hfix r Q hQ) (hfin r Q hQ (hfix r Q hQ)) (hinf r Q hQ (hfix r Q hQ)))
  exact ⟨c, hc1, by rw [hc2, hM]⟩

end GlobalTheory.NormHasseCent
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPolySupp

theorem int_pts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (y : GLw n w), y ∈ GlobalTheory.LFun.KGL w (n := n) → (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ 1 := by
  intro E _ _ _ n w y hy
  obtain ⟨M, rfl⟩ := hy
  have hint : ∀ z : Ov E w, Valued.v (z : w.adicCompletion E) ≤ 1 := fun z =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 z.2
  refine ⟨fun k => ?_, ?_⟩
  · have : (bc (Ov E w).subtype M).val = (M.val).map (Ov E w).subtype := rfl
    rw [this, Matrix.charpoly_map, coeff_map]; exact hint _
  · rw [← map_inv]
    have : (bc (Ov E w).subtype M⁻¹).val = ((M⁻¹).val).map (Ov E w).subtype := rfl
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hint _
end GlobalTheory.FinPolySupp

namespace GlobalTheory.FinPolySupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem val_alg (w : Pl E) (x : E) : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem pl_ext {u u' : Pl E} (h : ∀ x : E, u.valuation E x = u'.valuation E x) : u = u' := by
  apply HeightOneSpectrum.ext
  ext a
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), h]

theorem transfer {n : ℕ} (w : Pl E) (y : GLw n w) (P : E[X]) (hP : y.val.charpoly = atPl w P)
    (γ : WithZero (Multiplicative ℤ))
    (h1 : ∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) (h2 : Valued.v (y⁻¹ : GLw n w).val.det ≤ γ) :
    (∀ k, w.valuation E (P.coeff k) ≤ γ) ∧ w.valuation E (P.coeff 0)⁻¹ ≤ γ := by
  have hc : ∀ k, algebraMap E (w.adicCompletion E) (P.coeff k) = y.val.charpoly.coeff k := by
    intro k; rw [hP, atPl, coeff_map]
  refine ⟨fun k => ?_, ?_⟩
  · rw [← val_alg, hc]; exact h1 k
  · rw [← val_alg, map_inv₀, hc]
    have hdet : y.val.det = (-1) ^ Fintype.card (Fin n) * y.val.charpoly.coeff 0 :=
      Matrix.det_eq_sign_charpoly_coeff _
    have hmul : (y⁻¹ : GLw n w).val.det * y.val.det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    have hinv : (y⁻¹ : GLw n w).val.det = (y.val.det)⁻¹ := eq_inv_of_mul_eq_one_left hmul
    have hv : Valued.v y.val.det = Valued.v (y.val.charpoly.coeff 0) := by
      rw [hdet, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    rw [hinv, map_inv₀, hv] at h2
    rw [map_inv₀]; exact h2

theorem bound_at (n : ℕ) (w : Pl E) (f : UL n w → ℂ) (hf : HasCompactSupport f) :
    ∃ γ : WithZero (Multiplicative ℤ), (f = (KL n w : Set (UL n w)).indicator 1 → γ = 1) ∧
      ∀ P : E[X], (∃ y : UL n w, f y ≠ 0 ∧ y.1.val.charpoly = atPl w P) →
        (∀ k, w.valuation E (P.coeff k) ≤ γ) ∧ w.valuation E (P.coeff 0)⁻¹ ≤ γ := by
  by_cases hind : f = (KL n w : Set (UL n w)).indicator 1
  · refine ⟨1, fun _ => rfl, ?_⟩
    rintro P ⟨y, hy, hP⟩
    have hyK : y ∈ KL n w := by
      by_contra hn
      apply hy
      rw [hind]
      exact Set.indicator_of_notMem hn _
    have hy1 : y.1 ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf).1 hyK
    obtain ⟨h1, h2⟩ := int_pts E n w y.1 hy1
    exact transfer w y.1 P hP 1 h1 h2
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL E n w (Subtype.val '' tsupport f) (hf.image continuous_subtype_val)
    refine ⟨γ, fun h => absurd h hind, ?_⟩
    rintro P ⟨y, hy, hP⟩
    obtain ⟨h1, h2⟩ := hγ y.1 ⟨y, subset_tsupport f hy, rfl⟩
    exact transfer w y.1 P hP γ h1 h2

theorem conj_coeff (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (k : ℕ) :
    IsCMField.complexConj E (P.coeff k) = if k ≤ n then P.coeff (n - k) * (P.coeff 0)⁻¹ else 0 := by
  obtain ⟨h0, hcsr⟩ := GlobalTheory.T.elliptic_charpoly_self_reciprocal E n P hP
  have hdeg : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (RingHom.injective _)]; exact hP.2.1
  have key : ∀ j ≤ n, IsCMField.complexConj E (P.coeff 0) * P.coeff j =
      IsCMField.complexConj E (P.coeff (n - j)) := by
    intro j hj
    have := congrArg (fun Q => Q.coeff j) hcsr
    simp only [coeff_C_mul, coeff_reverse, hdeg, coeff_map] at this
    rw [revAt_le hj] at this
    exact this
  have hc0 : IsCMField.complexConj E (P.coeff 0) = (P.coeff 0)⁻¹ := by
    have := key 0 (Nat.zero_le _)
    have hn : P.coeff n = 1 := by rw [← hP.2.1]; exact hP.1
    rw [Nat.sub_zero, hn, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  split_ifs with hk
  · have := key (n - k) (Nat.sub_le n k)
    rw [Nat.sub_sub_self hk, hc0] at this
    rw [← this]; field_simp
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hP.2.1]; omega), map_zero]

theorem finpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ f : ∀ w : Pl E, UL n w → ℂ, (∀ w, HasCompactSupport (f w)) → (∀ᶠ w in (cofinite : Filter (Pl E)), f w = (KL n w : Set (UL n w)).indicator 1) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ _ n S hS f hcpt hev
  choose γ hγ1 hγ using fun w => bound_at n w (f w) (hcpt w)
  have hpart := GlobalTheory.T.exists_mem_section_valuation_eq_conj E S hS
  let p : Pl E → Pl E := fun u => if h : u ∈ S then u else (hpart u h).choose
  have hpS : ∀ u, u ∉ S → p u ∈ S ∧ ∀ x : E, u.valuation E x = (p u).valuation E (IsCMField.complexConj E x) := by
    intro u hu; simp only [p, dif_neg hu]; exact (hpart u hu).choose_spec
  let Γ : Pl E → WithZero (Multiplicative ℤ) := fun u => if u ∈ S then γ u else γ (p u) * γ (p u)
  have hB : {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}.Finite := Filter.eventually_cofinite.1 hev
  have hΓ : ∀ᶠ u in cofinite, Γ u ≤ 1 := by
    rw [Filter.eventually_cofinite]
    have hsub : {u | ¬ Γ u ≤ 1} ⊆ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1} ∪
        {u | u ∉ S ∧ p u ∈ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}} := by
      intro u hu
      by_cases huS : u ∈ S
      · left; intro hf; apply hu; simp [Γ, huS, hγ1 u hf]
      · right; refine ⟨huS, fun hf => hu ?_⟩; simp [Γ, huS, hγ1 _ hf]
    refine (hB.union ?_).subset hsub
    refine Set.Finite.of_finite_image (f := p) (hB.subset ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩; exact hu.2
    · intro u hu u' hu' he
      apply pl_ext; intro x
      rw [(hpS u hu.1).2, (hpS u' hu'.1).2, he]
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_common_integer_denominator_of_valuation_bounds E Γ hΓ
  refine (GlobalTheory.T.finite_monic_unitRoots_bounded_denominator_numberField E n d hd0).subset ?_
  rintro P ⟨hP, hPS⟩
  refine ⟨hP.1, hP.2.1, hP.2.2.2, fun k => hd _ fun u => ?_⟩
  by_cases huS : u ∈ S
  · simp only [Γ, if_pos huS]; exact (hγ u P (hPS u huS)).1 k
  · simp only [Γ, if_neg huS]
    obtain ⟨hpu, hv⟩ := hpS u huS
    obtain ⟨hb1, hb2⟩ := hγ (p u) P (hPS _ hpu)
    rw [hv, conj_coeff n P hP k]
    split_ifs
    · rw [map_mul]; exact mul_le_mul' (hb1 _) hb2
    · rw [map_zero]; exact zero_le'

end GlobalTheory.FinPolySupp
end
end
