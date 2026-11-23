module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle010
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit
public import Formalism.SatakeDualWeyl.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.RamificationInertia.Galois
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime], ∃ κ : 𝓞 F ⊗[ℤ] ℤ_[ℓ] ≃+* cenOrder ℓ F, ∀ c : 𝓞 F, (κ (c ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := by
  first | (exact @GlobalTheory.CenOrderIso.cenOrder_equiv) | (exact GlobalTheory.CenOrderIso.cenOrder_equiv) | (intros; apply GlobalTheory.CenOrderIso.cenOrder_equiv  <;> assumption)
end

section

namespace GlobalTheory.ClassResidueGenerators

theorem residue_eq_of_generators {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A]
    (S : Set A) (ψ ψ' : ↥(Algebra.adjoin O S) →ₐ[O] O)
    (h : ∀ (a : A) (ha : a ∈ S),
      IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin ha⟩) =
        IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin ha⟩))
    (x : A) (hx : x ∈ Algebra.adjoin O S) :
    IsLocalRing.residue O (ψ ⟨x, hx⟩) = IsLocalRing.residue O (ψ' ⟨x, hx⟩) := by
  induction hx using Algebra.adjoin_induction with
  | mem a ha => exact h a ha
  | algebraMap r =>
    have e : (⟨algebraMap O A r, Subalgebra.algebraMap_mem _ r⟩ : ↥(Algebra.adjoin O S)) =
        algebraMap O _ r := rfl
    rw [e, ψ.commutes, ψ'.commutes]
  | add a b ha hb iha ihb =>
    have e : (⟨a + b, add_mem ha hb⟩ : ↥(Algebra.adjoin O S)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), iha, ihb]
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, mul_mem ha hb⟩ : ↥(Algebra.adjoin O S)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_mul, iha, ihb]

theorem cls_eq_of_generators : ∀ {O K V : Type} [inst : CommRing O] [inst_1 : Field K] [inst_2 : Algebra O K] [inst_3 : AddCommGroup V] [inst_4 : Module K V] [inst_5 : Module O V] [inst_6 : IsScalarTower O K V] [inst_7 : IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : ↥(Algebra.adjoin O S) →ₐ[O] O), (∀ (a : Module.End K V) (h : a ∈ S), (IsLocalRing.residue O : O → IsLocalRing.ResidueField O) ((ψ : ↥(Algebra.adjoin O S) → O) (⟨a, Algebra.subset_adjoin h⟩ : ↥(Algebra.adjoin O S))) = (IsLocalRing.residue O : O → IsLocalRing.ResidueField O) ((ψ' : ↥(Algebra.adjoin O S) → O) (⟨a, Algebra.subset_adjoin h⟩ : ↥(Algebra.adjoin O S)))) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  intro O K V _ _ _ _ _ _ _ _ S ψ ψ' h
  unfold Formalism.L2.NCov.cls
  congr 1
  ext ⟨x, hx⟩
  exact residue_eq_of_generators S ψ ψ' h x hx

end GlobalTheory.ClassResidueGenerators
end

section

open NumberField

noncomputable section

namespace GlobalTheory.EmbSepUnram

open GlobalTheory.Proof.IdempotentLatticeSequence (primeOf mem_primeOf primeOf_isMaximal natCast_mem_primeOf norm_int_le)

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_int_le {E : Type} [Field E] (φ ψ : E →+* ℂ_[p]) (y : 𝓞 E) : ‖φ (y : E) - ψ (y : E)‖ ≤ 1 :=
  by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_int_le φ y) ?_)
  rw [norm_neg]; exact norm_int_le ψ y

theorem exists_algEquiv {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] [IsGalois ℚ E]
    (ψ₁ ψ₂ : E →+* ℂ_[p]) (h : ∀ x : K, ψ₁ (algebraMap K E x) = ψ₂ (algebraMap K E x)) :
    ∃ σ : E ≃ₐ[K] E, ∀ x, ψ₁ x = ψ₂ (σ x) := by
  let _ : Algebra E ℂ_[p] := ψ₂.toAlgebra
  have _ := IsScalarTower.of_algebraMap_eq (R := ℚ) (S := E) (A := ℂ_[p]) fun x => by
    show algebraMap ℚ ℂ_[p] x = ψ₂ (algebraMap ℚ E x)
    rw [eq_ratCast (algebraMap ℚ ℂ_[p]), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let τ : E ≃ₐ[ℚ] E := (ψ₁.toRatAlgHom).restrictNormal' E
  have hτ : ∀ x, ψ₂ (τ x) = ψ₁ x := fun x => (ψ₁.toRatAlgHom).restrictNormal_commutes E x
  let σ : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x => ψ₂.injective (by
    change ψ₂ (τ _) = _
    rw [hτ]; exact h x)
  exact ⟨σ, fun x => (hτ x).symm⟩

theorem norm_le_of_mem_sq {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ r) {z : 𝓞 E} (hz : z ∈ primeOf φ ^ 2) :
    ‖φ (z : E)‖ ≤ r * r := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · change ‖φ (algebraMap (𝓞 E) E (a * b))‖ ≤ r * r
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_mul (h a ha) (h b hb) (norm_nonneg _) hr
  · change ‖φ (algebraMap (𝓞 E) E (a + b))‖ ≤ r * r
    rw [map_add (f := _), map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem embSep : Formalism.L2.Th1.GD.EmbSep := by
  intro p _ K E _ _ _ _ _ _ φ ψ₁ ψ₂ ⟨π, hπ1, hπ⟩ hK hφ hne
  by_contra hc
  push Not at hc
  have h1 : ∀ y : 𝓞 E, ‖ψ₂ (y : E) - ψ₁ (y : E)‖ < 1 := fun y => by
    have a := lt_of_le_of_ne (norm_sub_int_le φ ψ₁ y) (hc y)
    have e : ψ₂ (y : E) - ψ₁ (y : E) = (φ (y : E) - ψ₁ (y : E)) + -(φ (y : E) - ψ₂ (y : E)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a ?_)
    rw [norm_neg]; exact hφ y
  have hP : ∀ z : 𝓞 E, ‖ψ₂ (z : E)‖ < 1 → z ∈ primeOf φ := fun z hz => by
    change ‖φ (z : E)‖ < 1
    rw [← sub_add_cancel (φ (z : E)) (ψ₂ (z : E))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hφ z) hz)
  obtain ⟨σ, hσ⟩ := exists_algEquiv ψ₁ ψ₂ hK
  have : IsGalois K E := IsGalois.tower_top_of_isGalois ℚ K E
  have := primeOf_isMaximal φ
  have hP0 : primeOf φ ≠ ⊥ := fun h => by
    have := natCast_mem_primeOf φ
    rw [h, Ideal.mem_bot] at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have : IsGaloisGroup (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) := IsGaloisGroup.of_isFractionRing (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) K E
  have hp0 : (primeOf φ).under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0

  set r := ‖φ (algebraMap K E (π : K))‖ with hr
  have hr0 : 0 < r := by
    refine lt_of_lt_of_le ?_ (hπ (p : 𝓞 E) (natCast_mem_primeOf φ))
    rw [norm_pos_iff]
    have : ((p : 𝓞 E) : E) = (p : E) := rfl
    rw [this, map_natCast]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsq : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 E)) ((primeOf φ).under (𝓞 K)) ≤ primeOf φ ^ 2 := fun hle => by
    have hπP : algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ ^ 2 :=
      hle (Ideal.mem_map_of_mem _ (show algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ from hπ1))
    have := norm_le_of_mem_sq φ hr0.le hπ hπP
    change r ≤ r * r at this
    nlinarith
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) ((primeOf φ).under (𝓞 K)) (primeOf φ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) (E ≃ₐ[K] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) hp0,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hsq)] at hcard
  have hs : σ ∈ (primeOf φ).inertia (E ≃ₐ[K] E) := AddSubgroup.mem_inertia.2 fun x => hP _ (by
    change ‖ψ₂ (σ (x : E) - (x : E))‖ < 1
    rw [map_sub, ← hσ]
    exact h1 x |> fun h => by rwa [norm_sub_rev] at h)
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hne (RingHom.ext fun x => by rw [hσ, hs]; rfl)

end GlobalTheory.EmbSepUnram
end
end

section

namespace GlobalTheory.TransportLemma

theorem transport {V : Type} [AddCommGroup V] [Module ℂ V] [DecidableEq V] (T : V ≃+ V)
    {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S)
    (h₁ : ∀ x : V, (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁)
    (h₂ : ∀ x : V, (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) := by
  obtain ⟨hmem, hinj, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact (h₂ s).mpr (hmem s hs)
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have h : (T : V → V) (s - t) ∈ M₁ := by
      rw [map_sub]; exact hxy
    rw [hinj s hs t ht ((h₁ _).mp h)]
  · intro y hy
    have hy' : T.symm y ∈ Λ₂ := (h₂ _).mp (by simpa using hy)
    obtain ⟨s, hs, hd⟩ := hcov _ hy'
    refine ⟨(T : V → V) s, Finset.mem_image_of_mem _ hs, ?_⟩
    have h : (T : V → V) (T.symm y - s) ∈ M₁ := (h₁ _).mpr hd
    rw [map_sub] at h
    simpa using h

theorem main : ∀ {V : Type} [inst : AddCommGroup V] [Module ℂ V] [inst_2 : DecidableEq V] (T : V ≃+ V) {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V}, Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S → (∀ (x : V), (T : V → V) x ∈ M₁ ↔ x ∈ Λ₁) → (∀ (x : V), (T : V → V) x ∈ M₂ ↔ x ∈ Λ₂) → Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → V) S) :=
  @transport

end GlobalTheory.TransportLemma
end

section

namespace GlobalTheory.RepresentativesImage

theorem isReps_image {V W : Type} [AddCommGroup V] [AddCommGroup W] [DecidableEq W] (T : V ≃+ W)
    {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S) (h₁ : ∀ x : V, T x ∈ M₁ ↔ x ∈ Λ₁) (h₂ : ∀ x : V, T x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → W) S) := by
  unfold Formalism.L2.Th1.H.IsReps at hS ⊢
  obtain ⟨hmem, hdist, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact (h₂ v).2 (hmem v hv)
  · intro a ha b hb hab
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb
    rw [← map_sub] at hab
    rw [hdist v hv u hu ((h₁ _).1 hab)]
  · intro w hw
    obtain ⟨v, rfl⟩ := T.surjective w
    obtain ⟨u, hu, hvu⟩ := hcov v ((h₂ v).1 hw)
    exact ⟨T u, Finset.mem_image_of_mem _ hu, by rw [← map_sub]; exact (h₁ _).2 hvu⟩

end GlobalTheory.RepresentativesImage
end

section

noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.TraceNormCoordinates

theorem exists_coords (b : ℤ) (d : ℕ) (hd : 0 < d) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) :
    ∃ p q : ℚ, x = (p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs_def
  have hs : s * s = -(d : ℂ) := by
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    calc s * s = (Complex.I * Complex.I) * (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) := by
          rw [hs_def]; ring
      _ = -(d : ℂ) := by rw [Complex.I_mul_I, h2]; ring
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨(b : ℚ) / 2, 1 / 2, ?_⟩
    simp only [PI.UnitDetRootDefs.cmTheta, hs_def]
    push_cast
    ring
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨p, q, rfl⟩ := ihx
    obtain ⟨p', q', rfl⟩ := ihy
    exact ⟨p + p', q + q', by push_cast; ring⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨p, q, rfl⟩ := ihx
    obtain ⟨p', q', rfl⟩ := ihy
    refine ⟨p * p' - d * q * q', p * q' + q * p', ?_⟩
    push_cast
    linear_combination (q : ℂ) * q' * hs
  | inv x _ ih =>
    obtain ⟨p, q, rfl⟩ := ih
    by_cases h0 : p = 0 ∧ q = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact ⟨0, 0, by simp⟩
    · have hN : p ^ 2 + d * q ^ 2 ≠ 0 := by
        intro hz
        apply h0
        have h1 : p ^ 2 = 0 := by nlinarith [sq_nonneg p, mul_nonneg hdq.le (sq_nonneg q)]
        have h2 : q ^ 2 = 0 := by nlinarith [sq_nonneg p, sq_nonneg q, mul_nonneg hdq.le (sq_nonneg q)]
        exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1, pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2⟩
      have hNc : ((p : ℂ) ^ 2 + (d : ℂ) * (q : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hN
      refine ⟨p / (p ^ 2 + d * q ^ 2), -q / (p ^ 2 + d * q ^ 2), ?_⟩
      apply inv_eq_of_mul_eq_one_right
      clear_value s
      have e : ((p : ℂ) + q * s) * (((p / (p ^ 2 + d * q ^ 2) : ℚ) : ℂ) + ((-q / (p ^ 2 + d * q ^ 2) : ℚ) : ℂ) * s)
          = ((p : ℂ) ^ 2 - (q : ℂ) ^ 2 * (s * s)) / ((p : ℂ) ^ 2 + (d : ℂ) * (q : ℂ) ^ 2) := by
        push_cast
        ring
      rw [e, hs, div_eq_one_iff_eq hNc]
      ring

theorem norm_le_one_of_trace {F : Type*} [NormedField F] [IsUltrametricDist F] {y y' : F}
    (h : y * y' = 1) (ht : ‖y + y'‖ ≤ 1) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hn : ‖y‖ * ‖y'‖ = 1 := by rw [← norm_mul, h, norm_one]
  have hy' : ‖y'‖ < ‖y‖ := by nlinarith [norm_nonneg y', norm_nonneg y]
  have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy')
  rw [hmax, max_eq_left hy'.le] at ht
  linarith

theorem norm_eq_one {a : ℕ} {b c : ℤ} {d : ℕ} (hok : PI.UnitDetRootDefs.CmOK a b c d) (l : ℕ)
    [inst : Fact (Nat.Prime l)]
    (hT : ∀ T v : ℚ_[l], T ^ 2 + (d : ℚ_[l]) * v ^ 2 = 4 → ‖T‖ ≤ 1)
    (ι : ℂ ≃+* ℂ_[l]) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) (h1 : x * conj x = 1) :
    ‖ι x‖ = 1 := by
  have hd : 0 < d := hok.2.2.2.pos
  obtain ⟨p, q, rfl⟩ := exists_coords b d hd hx
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs_def
  have hs : s * s = -(d : ℂ) := by
    have h2 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    calc s * s = (Complex.I * Complex.I) * (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) := by
          rw [hs_def]; ring
      _ = -(d : ℂ) := by rw [Complex.I_mul_I, h2]; ring
  have hcs : conj s = -s := by simp [hs_def]
  have hconj : conj ((p : ℂ) + (q : ℂ) * s) = (p : ℂ) - (q : ℂ) * s := by
    rw [map_add (f := _), map_mul, hcs, map_ratCast, map_ratCast]; ring
  rw [hconj] at h1

  have hpq : (p ^ 2 + d * q ^ 2 : ℚ) = 1 := by
    have : (((p ^ 2 + d * q ^ 2 : ℚ)) : ℂ) = 1 := by
      push_cast
      linear_combination h1 + (q : ℂ) ^ 2 * hs
    exact_mod_cast this
  have hT' : ‖((2 * p : ℚ) : ℚ_[l])‖ ≤ 1 := by
    apply hT _ ((2 * q : ℚ) : ℚ_[l])
    have : ((2 * p) ^ 2 + d * (2 * q) ^ 2 : ℚ) = 4 := by linear_combination 4 * hpq
    exact_mod_cast congrArg (fun r : ℚ => (r : ℚ_[l])) this
  set y := ι ((p : ℂ) + (q : ℂ) * s)
  set y' := ι ((p : ℂ) - (q : ℂ) * s)
  have hyy : y * y' = 1 := by rw [← map_mul, h1, map_one]
  have hnr : ∀ r : ℚ, ‖(r : ℂ_[l])‖ = ‖(r : ℚ_[l])‖ := by
    intro r
    rw [← PadicComplex.norm_extends', map_ratCast, PadicComplex.coe_eq, map_ratCast]
  have hsum : y + y' = ((2 * p : ℚ) : ℂ_[l]) := by
    rw [← map_add (f := _)]
    have : (p : ℂ) + (q : ℂ) * s + ((p : ℂ) - (q : ℂ) * s) = ((2 * p : ℚ) : ℂ) := by push_cast; ring
    rw [this, map_ratCast]
  have htr : ‖y + y'‖ ≤ 1 := by rw [hsum, hnr]; exact hT'
  have hle : ‖y‖ ≤ 1 := norm_le_one_of_trace hyy htr
  have hle' : ‖y'‖ ≤ 1 := norm_le_one_of_trace (by rw [mul_comm]; exact hyy) (by rw [add_comm]; exact htr)
  have hn : ‖y‖ * ‖y'‖ = 1 := by rw [← norm_mul, hyy, norm_one]
  nlinarith [norm_nonneg y, norm_nonneg y']

end GlobalTheory.TraceNormCoordinates
end
end

section

open Matrix

noncomputable section

namespace GlobalTheory.UnramReps

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem le_ofAdd_neg_one_of_lt_one' {y : WithZero (Multiplicative ℤ)} (h : y < 1) :
    y ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction y using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

theorem exists_residue_reps' {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = q ^ 2) :
    ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ x ∈ Formalism.UG.intL L, ∃ r ∈ R,
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) (x - r) < 1 := by
  classical
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
  have hfin : Finite (v.integer ⧸ IsLocalRing.maximalIdeal v.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI : Finite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring) := hfin
  haveI := Fintype.ofFinite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring)
  let f : v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring → L :=
    fun c => ((Ideal.Quotient.mk_surjective c).choose : L)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    show _ ∈ v.integer
    rw [Valuation.mem_integer_iff]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (Ideal.Quotient.mk_surjective c).choose.2
  · intro x hx
    have hx' : x ∈ v.valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).2 ((Valuation.mem_integer_iff _ _).1 hx)
    let xs : v.valuationSubring := ⟨x, hx'⟩
    let c := Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring) xs
    refine ⟨f c, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
    have hspec := (Ideal.Quotient.mk_surjective c).choose_spec
    have hmem : xs - (Ideal.Quotient.mk_surjective c).choose ∈
        IsLocalRing.maximalIdeal v.valuationSubring :=
      Ideal.Quotient.eq.1 (hspec.symm)
    rw [Valuation.mem_maximalIdeal_iff] at hmem
    simpa [xs, f] using hmem

theorem exists_reps_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧
      ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K := by
  intro L _ _ ϖ σ q hU
  classical
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := hU
  obtain ⟨R, hRO, hR⟩ := exists_residue_reps' (L := L) hq hcard
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
  have h0 : v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  have hϖ1 : v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    norm_num
  have hϖO : ϖ ∈ Formalism.UG.intL L := (Valuation.mem_integer_iff _ _).2 hϖ1
  intro K
  induction K with
  | zero =>
    refine ⟨{0}, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_singleton.1 hr]; exact (Formalism.UG.intL L).zero_mem
    · intro x hx
      refine ⟨0, Finset.mem_singleton_self 0, ?_⟩
      rw [sub_zero, pow_zero]
      exact (Valuation.mem_integer_iff _ _).1 hx
  | succ N ih =>
    obtain ⟨T, hTO, hT⟩ := ih
    refine ⟨Finset.image₂ (fun r t => r + ϖ * t) R T, ?_, ?_⟩
    · intro z hz
      obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_image₂.1 hz
      exact (Formalism.UG.intL L).add_mem (hRO r hr) ((Formalism.UG.intL L).mul_mem hϖO (hTO t ht))
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := hR x hx
      have hle : v (x - r) ≤ v ϖ := hϖ ▸ le_ofAdd_neg_one_of_lt_one' hxr
      set y := (x - r) * ϖ⁻¹ with hy
      have hϖ0 : ϖ ≠ 0 := fun h => h0 (by rw [h, map_zero])
      have hyO : y ∈ Formalism.UG.intL L := by
        apply (Valuation.mem_integer_iff _ _).2
        rw [hy, map_mul, map_inv₀]
        calc v (x - r) * (v ϖ)⁻¹ ≤ v ϖ * (v ϖ)⁻¹ := mul_le_mul' hle le_rfl
          _ = 1 := mul_inv_cancel₀ h0
      obtain ⟨t, ht, hyt⟩ := hT y hyO
      refine ⟨r + ϖ * t, Finset.mem_image₂.2 ⟨r, hr, t, ht, rfl⟩, ?_⟩
      have he : x - (r + ϖ * t) = ϖ * (y - t) := by
        rw [hy]; field_simp; ring
      show v (x - (r + ϖ * t)) ≤ v ϖ ^ (N + 1)
      rw [he, map_mul, pow_succ']
      exact mul_le_mul' le_rfl hyt

end GlobalTheory.UnramReps
end
end
