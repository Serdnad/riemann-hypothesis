module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section

namespace GlobalTheory.StabRef

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem intAt_zero : IntAt P (0 : E) := by
  have := IntAt.coe P 0
  rwa [map_zero] at this

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (intAt_zero (P := P))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mem_locP' {n : ℕ} (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) :
    x ∈ localization₂ P.asIdeal L ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ L := Iff.rfl

theorem mem_stdLat' {n : ℕ} (x : Sp E n) : x ∈ stdLat E n ↔ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]

theorem mem_locStd {n : ℕ} (x : Sp E n) : x ∈ localization₂ P.asIdeal (stdLat E n) ↔ ∀ i, IntAt P (x i) := by
  constructor
  · intro hx i
    obtain ⟨s, hs, h⟩ := (mem_locP' _ x).1 hx
    obtain ⟨r, hr⟩ := (mem_stdLat' _).1 h i
    exact ⟨r, s, hs, by rw [hr, Pi.smul_apply, Algebra.smul_def]⟩
  · intro H
    have : x = ∑ i, (Pi.single i (x i) : Sp E n) := (Finset.univ_sum_single x).symm
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, h⟩ := H i
    refine (mem_locP' _ _).2 ⟨s, hs, ?_⟩
    have e : s • (Pi.single i (x i) : Sp E n) = Pi.single i (algebraMap (𝓞 E) E r) := by
      rw [← Pi.single_smul, Algebra.smul_def, ← h]
    rw [e]
    rw [mem_stdLat']
    intro j
    by_cases hj : j = i
    · subst hj
      exact ⟨r, by simp⟩
    · exact ⟨0, by simp [hj]⟩

theorem mem_sclLat {N : ℕ} (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ LocE.sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold LocE.sclLat stdAt
  rw [Submodule.mem_comap, mem_locStd]
  simp [LinearMap.pi_apply, smul_eq_mul]

end GlobalTheory.StabRef
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.SymTieExists
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] {F : Type} [CommRing F]

end Local

section Res
variable {E k : Type} [Field E] [NumberField E]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reduction_spec (P : HeightOneSpectrum (𝓞 E)) {a : E} (h : IntAt P a) :
    ∃ r, ∃ s ∉ P.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  obtain ⟨r, s, hs, e⟩ := h
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hex : ∃ c r, ∃ s ∉ P.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨(Ideal.Quotient.mk P.asIdeal s)⁻¹ * Ideal.Quotient.mk P.asIdeal r, r, s, hs, e, mul_inv_cancel_left₀ hs' _⟩
  unfold redP
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem exists_residue (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) (hint : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a)
    (hd : DenseRange ι) :
    ∃ r : 𝒪[k] →+* 𝓞 E ⧸ P.asIdeal, Function.Surjective r ∧ (∀ x : 𝒪[k], r x = 0 ↔ valuation k (x : k) < 1) ∧
      ∀ a (h : ι a ∈ 𝒪[k]), r ⟨ι a, h⟩ = redP P a := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hlt : ∀ y : 𝒪[k], IsLocalRing.residue 𝒪[k] y = 0 ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  let j : 𝓞 E →+* 𝒪[k] := (ι.comp (algebraMap (𝓞 E) E)).codRestrict _ fun r =>
    (hint _).2 ⟨r, 1, h1, by simp⟩
  have hj : ∀ r, (j r : k) = ι (algebraMap (𝓞 E) E r) := fun _ => rfl
  let φ : 𝓞 E →+* 𝓀[k] := (IsLocalRing.residue 𝒪[k]).comp j
  have hker : ∀ r ∈ P.asIdeal, φ r = 0 := by
    intro r hr
    refine (hlt _).2 ?_
    by_contra hlt'
    have hv : valuation k (j r : k) = 1 :=
      le_antisymm ((Valuation.mem_integer_iff _ _).1 (j r).2) (not_lt.1 hlt')
    have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
      intro h
      rw [hj, h] at hv
      simp at hv
    obtain ⟨t, s, hs, e⟩ := (hint (algebraMap (𝓞 E) E r)⁻¹).1 (by
      rw [Valuation.mem_integer_iff, map_inv₀, map_inv₀, ← hj, hv, inv_one])
    apply hs
    have : s = t * r := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [map_mul, ← e, inv_mul_cancel_right₀ hr0]
    rw [this]
    exact Ideal.mul_mem_left _ _ hr
  let φ' : 𝓞 E ⧸ P.asIdeal →+* 𝓀[k] := Ideal.Quotient.lift _ φ hker
  have hφ' : ∀ r, φ' (Ideal.Quotient.mk _ r) = IsLocalRing.residue 𝒪[k] (j r) := fun _ => rfl
  have hred : ∀ a (h : ι a ∈ 𝒪[k]), φ' (redP P a) = IsLocalRing.residue 𝒪[k] ⟨ι a, h⟩ := by
    intro a h
    obtain ⟨r, s, hs, e, e'⟩ := reduction_spec P ((hint a).1 h)
    have hs' : φ' (Ideal.Quotient.mk P.asIdeal s) ≠ 0 := by
      rwa [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    apply mul_left_cancel₀ hs'
    rw [← map_mul, e', hφ', hφ', ← map_mul]
    congr 1
    apply Subtype.ext
    change ι (algebraMap (𝓞 E) E r) = ι (algebraMap (𝓞 E) E s) * ι a
    rw [← map_mul, e]
  have hsurj : Function.Surjective φ' := by
    intro t
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective t
    have hn : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
      rw [IsValuativeTopology.mem_nhds_iff']
      exact ⟨1, by simp⟩
    obtain ⟨a, ha⟩ := hd.mem_nhds hn
    have ha' : valuation k (ι a - x) < 1 := ha
    have hm : ι a ∈ 𝒪[k] := by
      have := add_mem ((Valuation.mem_integer_iff _ _).2 ha'.le) x.2
      simpa using this
    refine ⟨redP P a, ?_⟩
    rw [hred a hm, ← sub_eq_zero, ← map_sub]
    exact (hlt _).2 ha'
  let e := RingEquiv.ofBijective φ' ⟨φ'.injective, hsurj⟩
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue 𝒪[k]), e.symm.surjective.comp IsLocalRing.residue_surjective,
    fun x => ?_, fun a h => ?_⟩
  · rw [← hlt]
    exact map_eq_zero_iff _ e.symm.injective
  · change e.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    exact (hred a h).symm

end Res

end GlobalTheory.SymTieExists
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Ker

namespace GlobalTheory

theorem exists_not_mem_dvd_locally_away (E : Type) [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ t : 𝓞 E, t ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q →
      ∃ w : 𝓞 E, w ∉ Q'.asIdeal ∧ ∃ z : 𝓞 E, w * t = r * z := by
  have hI : Ideal.span {r} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hnu : ¬ IsUnit Q.asIdeal := fun h => Q.isPrime.ne_top (Ideal.isUnit_iff.1 h)
  obtain ⟨J, hJ, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hnu hI).exists_eq_pow_mul_and_not_dvd
  set m := multiplicity Q.asIdeal (Ideal.span {r})
  have hJle : ¬ J ≤ Q.asIdeal := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htJ, htQ⟩ := Set.not_subset.1 hJle
  refine ⟨t, htQ, fun Q' hQ' => ?_⟩
  have hnle : ¬ Q.asIdeal ^ m ≤ Q'.asIdeal := by
    intro h
    have h1 : Q.asIdeal ≤ Q'.asIdeal := Q'.isPrime.le_of_pow_le h
    have h2 : Q.asIdeal = Q'.asIdeal := Q.isMaximal.eq_of_le Q'.isPrime.ne_top h1
    exact hQ' (HeightOneSpectrum.ext h2.symm)
  obtain ⟨w, hwm, hwQ'⟩ := Set.not_subset.1 hnle
  refine ⟨w, hwQ', ?_⟩
  have hmem : w * t ∈ Ideal.span {r} := by
    rw [hJ]; exact Ideal.mul_mem_mul hwm htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨z, by rw [← hz, mul_comm]⟩

end GlobalTheory
end
