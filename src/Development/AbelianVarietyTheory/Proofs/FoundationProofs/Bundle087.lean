module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle051
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions : (∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) fun n => (c n : ℂ)) ∧ ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) fun n => (c n : ℂ) := by
  first | exact @GlobalTheory.FN.dd_div_q_and_q_div_dd | exact GlobalTheory.FN.dd_div_q_and_q_div_dd | (intros; apply GlobalTheory.FN.dd_div_q_and_q_div_dd <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem norm_surjective_of_norm_form {K L : Type} [Field K] [Field L] [Algebra K L] (hC : IsFirstChernClassOfLineBundle K) (m : ℕ) (hm0 : 0 < m)
    (B : Module.Basis (Fin m) K L) (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous m)
    (hnorm : ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => B.repr x i) f)
    (hpow : ∀ a : K, Algebra.norm K (algebraMap K L a) = a ^ m)
    (b : K) : ∃ x : L, Algebra.norm K x = b := by
  let g : MvPolynomial (Fin (m + 1)) K :=
    MvPolynomial.rename Fin.succ f - MvPolynomial.C b * MvPolynomial.X 0 ^ m
  have hg : g.IsHomogeneous m := by
    refine (hf.rename_isHomogeneous).sub ?_
    have := (MvPolynomial.isHomogeneous_C (Fin (m + 1)) b).mul (MvPolynomial.isHomogeneous_X_pow (0 : Fin (m + 1)) m)
    rwa [zero_add] at this
  obtain ⟨y, hy0, hy⟩ := hC (m + 1) m g hg hm0 (Nat.lt_succ_self m)
  let x : L := B.equivFun.symm (fun i => y i.succ)
  have hrepr : ∀ i, B.repr x i = y i.succ := by
    intro i
    have h := congrFun (B.equivFun.apply_symm_apply (fun i => y i.succ)) i
    rw [Module.Basis.equivFun_apply] at h
    exact h
  have hev : Algebra.norm K x = b * y 0 ^ m := by
    have h1 := hy
    simp only [g, map_sub, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_C,
      MvPolynomial.eval_X] at h1
    rw [hnorm]
    have e : (fun i => B.repr x i) = y ∘ Fin.succ := funext hrepr
    rw [e]; exact sub_eq_zero.mp h1
  have hnz : ∀ z : L, Algebra.norm K z = 0 → z = 0 := by
    intro z hz
    by_contra hz'
    have hu : IsUnit z := (isUnit_iff_ne_zero).mpr hz'
    exact (hu.map (Algebra.norm K)).ne_zero hz
  have hy00 : y 0 ≠ 0 := by
    intro h0
    apply hy0
    have hx : x = 0 := hnz x (by rw [hev, h0, zero_pow hm0.ne', mul_zero])
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    have := hrepr j
    rw [hx, map_zero] at this
    simpa using this.symm
  refine ⟨x * algebraMap K L (y 0)⁻¹, ?_⟩
  rw [map_mul, hpow, hev, mul_assoc, ← mul_pow, mul_inv_cancel₀ hy00, one_pow, mul_one]

theorem norm_surjective_of_is_c1 : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
    ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  intro K L _ _ _ _ hC b _
  obtain ⟨f, hf, hnorm⟩ := GlobalTheory.T.algebraNorm_eq_homogeneous_polynomial_in_coordinates K L
  exact norm_surjective_of_norm_form hC _ Module.finrank_pos (Module.finBasis K L) f hf hnorm
    (fun a => Algebra.norm_algebraMap a) b

end GlobalTheory
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummer_carry_cocycle_coboundary_of_norms : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w ∧ ∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h) := by
  first | exact @GlobalTheory.NeedB.NormCob.carry_coboundary | exact GlobalTheory.NeedB.NormCob.carry_coboundary | (intros; apply GlobalTheory.NeedB.NormCob.carry_coboundary <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  first | exact @GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq | exact GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq | (intros; apply GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kum_eq_of_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ} (hN : 0 < N) {ζ θ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) (g : Ω ≃ₐ[K] Ω) (i : ZMod N) (hg : g θ = ζ ^ i.val * θ) :
    kum ζ θ g = i := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hex : ∃ j : ZMod N, g θ = ζ ^ j.val * θ := ⟨i, hg⟩
  unfold kum
  rw [dite_eq_left hex]
  have h1 := hex.choose_spec
  have h2 : ζ ^ i.val = ζ ^ hex.choose.val := mul_right_cancel₀ hθ (hg.symm.trans h1)
  have h3 := (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)) h2
  exact (ZMod.val_injective N h3).symm

theorem eta_kummer_galoisInvariant : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
  α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b → ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
  (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ IntermediateField.adjoin K {α, β} ∧
    (∀ g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup, η g = kum ζ θ g) ∧
    ∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix a b α β ha hb hα hβ η hη hcob
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  set E := IntermediateField.adjoin K ({α, β} : Set Ω) with hE
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hα; exact ha ((map_eq_zero _).mp hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hβ; exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨-, hαapp, hαmul, hαker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨-, hβapp, hβmul, hβker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  let x : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ α g)) (fun g h => by simp [hαmul, ofAdd_add])
  let y : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ β g)) (fun g h => by simp [hβmul, ofAdd_add])
  obtain ⟨-, hconj, hhom⟩ := GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary (Ω ≃ₐ[K] Ω) N x y η (fun g h => hcob g h)

  have memH : ∀ g : Ω ≃ₐ[K] Ω, g ∈ E.fixingSubgroup ↔ g α = α ∧ g β = β := by
    intro g
    constructor
    · intro hg
      exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg α
          (IntermediateField.subset_adjoin K _ (by simp)),
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg β
          (IntermediateField.subset_adjoin K _ (by simp))⟩
    · rintro ⟨h1, h2⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem w hw =>
        rcases hw with rfl | rfl
        · exact h1
        · exact h2
      | algebraMap r => exact g.commutes r
      | add u v _ _ hu hv => rw [map_add (f := _), hu, hv]
      | inv u _ hu => rw [map_inv₀, hu]
      | mul u v _ _ hu hv => rw [map_mul, hu, hv]
  have kα0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ α g = 0 := fun g hg => (hαker g).2 ((memH g).1 hg).1
  have kβ0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ β g = 0 := fun g hg => (hβker g).2 ((memH g).1 hg).2
  have hηhom : ∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, η (g * h) = η g + η h :=
    fun g hg h _ => hhom g h (kα0 g hg)
  obtain ⟨θ, hθ0, hθE, hθapp⟩ := GlobalTheory.T.exists_kummer_generator_of_locallyConstant_hom K Ω N ζ hN hζ hfix E η hη hηhom
  have hkθ : ∀ g ∈ E.fixingSubgroup, η g = kum ζ θ g := fun g hg =>
    (kum_eq_of_apply hN hζ hθ0 g (η g) (hθapp g hg)).symm
  refine ⟨θ, hθ0, hθE, hkθ, fun s => ?_⟩

  have hconjH : ∀ m ∈ E.fixingSubgroup, s⁻¹ * m * s ∈ E.fixingSubgroup ∧ η (s⁻¹ * m * s) = η m := by
    intro m hm
    obtain ⟨hmα, hmβ⟩ := (memH m).1 hm
    have hsα : m (s α) = s α := by
      rw [hαapp s, map_mul, map_pow, hfix m, hmα]
    have hsβ : m (s β) = s β := by
      rw [hβapp s, map_mul, map_pow, hfix m, hmβ]
    refine ⟨(memH _).2 ⟨?_, ?_⟩, ?_⟩
    · show s⁻¹ (m (s α)) = α
      rw [hsα]; exact s.symm_apply_apply α
    · show s⁻¹ (m (s β)) = β
      rw [hsβ]; exact s.symm_apply_apply β
    · have := hconj s⁻¹ m
      rw [inv_inv] at this
      rw [this]
      simp [x, y, kα0 m hm, kβ0 m hm]
  set u := s θ / θ with hu
  have hsθ0 : s θ ≠ 0 := by simpa using hθ0
  have hu0 : u ≠ 0 := div_ne_zero hsθ0 hθ0
  refine ⟨u, ?_, hu0, ?_⟩
  · rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro m hm
    obtain ⟨hmem, hηeq⟩ := hconjH m hm
    have h1 : m θ = ζ ^ (η m).val * θ := hθapp m hm
    have h2 : (s⁻¹ * m * s) θ = ζ ^ (η m).val * θ := by rw [← hηeq]; exact hθapp _ hmem
    have h3 : m (s θ) = ζ ^ (η m).val * s θ := by
      have : s ((s⁻¹ * m * s) θ) = m (s θ) := by
        show s (s⁻¹ (m (s θ))) = m (s θ)
        exact s.apply_symm_apply _
      rw [← this, h2, map_mul, map_pow, hfix s]
    have hz : ζ ^ (η m).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [hu, map_div₀, h1, h3, mul_div_mul_left _ _ hz]
  · rw [map_pow, hu, div_pow, mul_div_cancel₀ _ (pow_ne_zero N hθ0)]

end GlobalTheory
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.KA

theorem shCoc_quot_coord : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ν : G ℚ Ω → (Qbar l)ˣ)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (m : ℕ),
    GlobalTheory.KA.ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l m)⁻¹ (Y m) →
    (∀ s ∈ Dec (F := ℚ) A, ρ s 1 0 = 0 ∧ ρ s 1 1 = (ν s : Qbar l)) →
    ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
      Y m (s * t) x 1 = Y m s x 1 + (ν s : Qbar l) * Y m t (x * (cycMod ℚ Ω l m s)⁻¹) 1 := by
  intro l _ Ω _ _ A ρ ν Y m hY hρ s hs t _ x
  simpa only [Pi.add_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, (hρ s hs).1,
    (hρ s hs).2, zero_mul, zero_add, MonoidHom.inv_apply] using congrFun (hY s t x) 1

end GlobalTheory.KA
end
