module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle185
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle189
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle060
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle184
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.Card

@[expose] public section

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

noncomputable section

namespace GlobalTheory.PsChar

open MvPolynomial

theorem aeval_eq_zero_of_polyApprox {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type} {θ : J → k}
    {S : Set (J → k)} (h : PolyApprox θ S) (P : MvPolynomial J ℤ) (hP : ∀ η ∈ S, aeval η P = 0) :
    aeval θ P = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨s, c, hs, hb⟩ := h ε hε
  have hz : ∑ η ∈ s, c η * aeval η P = 0 :=
    Finset.sum_eq_zero fun η hη => by rw [hP η (hs hη), mul_zero]
  have := hb P
  rw [hz, sub_zero] at this
  simpa using this

theorem isPsChar_trc {Γ A : Type} [Group Γ] [CommRing A] (a : ℕ) (ρ : Γ →* GL (Fin a) A) : IsPsChar a (trc ρ) :=
  isPsChar_trace Γ A a ((Units.coeHom (Matrix (Fin a) (Fin a) A)).comp ρ)

theorem isPsChar_of_polyApprox_trc : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l)
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T := by
  intro l _ Γ _ a T C h
  have key : ∀ P : MvPolynomial Γ ℤ, (∀ ρ ∈ C, aeval (trc ρ) P = 0) → aeval T P = 0 := fun P hP =>
    aeval_eq_zero_of_polyApprox h P (by rintro η ⟨ρ, hρ, rfl⟩; exact hP ρ hρ)
  have hm : ∀ (η : Γ → PadicAlgCl l) (x : Fin (a + 1) → Γ),
      aeval η (alt (fun g => (X g : MvPolynomial Γ ℤ)) (a + 1) x) = alt η (a + 1) x := fun η x => by
    have := map_alt (aeval η).toRingHom (fun g => (X g : MvPolynomial Γ ℤ)) (a + 1) x
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have := key (X 1 - (a : MvPolynomial Γ ℤ)) fun ρ _ => by simp [(isPsChar_trc a ρ).one]
    simpa [sub_eq_zero] using this
  · intro x y
    have := key (X (x * y) - X (y * x)) fun ρ _ => by simp [(isPsChar_trc a ρ).comm x y]
    simpa [sub_eq_zero] using this
  · intro x
    have := key _ fun ρ _ => by rw [hm]; exact (isPsChar_trc a ρ).alt_eq_zero x
    rwa [hm] at this

end GlobalTheory.PsChar

end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourier_preserves_test_fixes_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  first | exact @GlobalTheory.fourier_test_unit | exact GlobalTheory.fourier_test_unit | (intros; apply GlobalTheory.fourier_test_unit <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 → ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  first | exact @GlobalTheory.UnitaryTransitive.uO_transitive | exact GlobalTheory.UnitaryTransitive.uO_transitive | (intros; apply GlobalTheory.UnitaryTransitive.uO_transitive <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.invariant_image_openClosed_local_sections : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by
  first | exact @GlobalTheory.JR.image_openClosed_section | exact GlobalTheory.JR.image_openClosed_section | (intros; apply GlobalTheory.JR.image_openClosed_section <;> assumption)
end

section

open Formalism.MainNotions.N GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ x : R, IsNilpotent x → T x = 0 := by
  first | exact @GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent | exact GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent | (intros; apply GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent <;> assumption)
end

section

open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

section
variable {M A : Type*} [Monoid M] [CommRing A]

theorem alt_const_idem (T : M → A) (e : M) (he : e * e = e) :
    ∀ n : ℕ, alt T n (fun _ => e) = ∏ i ∈ Finset.range n, (T e - (i : A))
  | 0 => by simp [alt]
  | n + 1 => by
    have h1 : Fin.tail (fun _ : Fin (n + 1) => e) = fun _ : Fin n => e := rfl
    have h2 : ∀ i : Fin n, Function.update (fun _ : Fin n => e) i e = fun _ => e := by
      intro i; exact Function.update_eq_self i (fun _ : Fin n => e)
    rw [alt.eq_2]
    simp only [h1, he, h2, alt_const_idem T e he n, Finset.prod_range_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem alt_idem_last (T : M → A) (e y : M) (he : e * e = e) (hy : e * y = y) (h0 : T e = 0) :
    ∀ n : ℕ, alt T (n + 1) (fun i => if i.val = n then y else e)
      = (-1) ^ n * (n.factorial : A) * T y
  | 0 => by simp [alt]
  | n + 1 => by
    have h1 : Fin.tail (fun i : Fin (n + 1 + 1) => if i.val = n + 1 then y else e)
        = fun i : Fin (n + 1) => if i.val = n then y else e := by
      funext i; simp [Fin.tail]
    have h2 : ∀ i : Fin (n + 1), Function.update (fun i : Fin (n + 1) => if i.val = n then y else e) i
        (e * (if i.val = n then y else e)) = fun i => if i.val = n then y else e := by
      intro i
      have : e * (if i.val = n then y else e) = (if i.val = n then y else e) := by
        split_ifs <;> assumption
      rw [this]
      exact Function.update_eq_self i (fun i : Fin (n + 1) => if i.val = n then y else e)
    have h3 : (if ((0 : Fin (n + 1 + 1)) : ℕ) = n + 1 then y else e) = e := by simp
    rw [alt.eq_2]
    simp only [h1, h3, h0, h2, alt_idem_last T e y he hy h0 n, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.factorial_succ]
    push_cast
    ring

end

theorem isPsChar_idempotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ e : R, IsIdempotentElem e → (∃ m : ℕ, m ≤ d ∧ T e = m) ∧ (T e = 0 → ∀ y : R, T (e * y) = 0) := by
  intro k R _ _ _ _ d T hT e he
  have he' : e * e = e := he
  refine ⟨?_, fun h0 y => ?_⟩
  · have h := hT.alt_eq_zero (fun _ => e)
    rw [alt_const_idem _ e he', Finset.prod_eq_zero_iff] at h
    obtain ⟨m, hm, h⟩ := h
    exact ⟨m, Nat.lt_succ_iff.mp (Finset.mem_range.mp hm), sub_eq_zero.mp h⟩
  · have h := hT.alt_eq_zero (fun i => if i.val = d then e * y else e)
    rw [alt_idem_last (fun x => T x) e (e * y) he' (by rw [← mul_assoc, he']) h0 d] at h
    have h1 : ((-1 : k) ^ d * (d.factorial : k)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr d.factorial_ne_zero)
    exact (mul_eq_zero.mp h).resolve_left h1

end GlobalTheory.PsChar
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.NormSec

theorem normsec : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  intro F E _ _ _ _ hU r A₀ hA hsep M hM
  classical
  have hA' : star A₀ = A₀ := by rw [Matrix.star_eq_conjTranspose]; exact hA
  obtain ⟨f, hfA, hff, hffs, haniso⟩ := GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian E r A₀ hA hsep
  have hcomm := GlobalTheory.T.matrix_commute_of_commute_separable_charpoly E r A₀ hsep
  have hstarC : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → star m * A₀ = A₀ * star m := by
    intro m hm
    have := congrArg star hm
    rw [star_mul, star_mul, hA'] at this
    exact this.symm
  set g := star f with hg
  set e : Matrix (Fin r) (Fin r) E := 1 - f - g with he
  have hes : star e = 1 - g - f := by rw [he, star_sub, star_sub, star_one, hg, star_star]
  let R := Subring.centralizer ({A₀} : Set (Matrix (Fin r) (Fin r) E))
  have memR : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → m ∈ R := by
    intro m hm
    rw [Subring.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hm.symm
  have memR' : ∀ m ∈ R, m * A₀ = A₀ * m := by
    intro m hm
    exact ((Subring.mem_centralizer_iff.1 hm) A₀ rfl).symm
  letI : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun a b => Subtype.ext (hcomm a.1 b.1 (memR' _ a.2) (memR' _ b.2)) }
  let V : Submodule E (Matrix (Fin r) (Fin r) E) :=
    { carrier := {z | z * A₀ = A₀ * z ∧ z * e = z}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [add_mul, mul_add, ha1, hb1], by rw [add_mul, ha2, hb2]⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        exact ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, ha1], by rw [Matrix.smul_mul, ha2]⟩ }
  have hV : ∀ z ∈ V, z * star z = 0 → z = 0 := by
    rintro z ⟨hz1, hz2⟩ h0
    have h := haniso z hz1
    rw [hz2] at h
    exact h h0
  let M₁ := (fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) '' M
  let M₂ := (fun u : GL (Fin r) E => ((u⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) '' M
  have hM₁ : IsCompact M₁ := hM.image Units.continuous_val
  have hM₂ : IsCompact M₂ := hM.image Units.continuous_coe_inv
  let B₁ := (fun x => x * e) '' M₁
  let B₂ := (fun x => x * e) '' M₂
  have hB₁ : IsCompact B₁ := hM₁.image (continuous_mul_const e)
  have hB₂ : IsCompact B₂ := hM₂.image (continuous_mul_const e)
  have hT₁ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₁ hB₁
  have hT₂ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₂ hB₂
  let P₁ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₁} ×ˢ M₁)
  let P₂ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₂} ×ˢ M₂)
  have hP₁ : IsCompact P₁ := (hT₁.prod hM₁).image (by fun_prop)
  have hP₂ : IsCompact P₂ := (hT₂.prod hM₂).image (by fun_prop)
  refine ⟨{s | (s : Matrix (Fin r) (Fin r) E) ∈ P₁ ∧ ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ P₂}, ?_, ?_⟩
  · have := Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hP₁.prod (hP₂.image MulOpposite.continuous_op))
    convert this using 1
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    rw [MulOpposite.op_injective.mem_set_image]
  rintro t ht ⟨m, hmM, hm⟩
  set T : Matrix (Fin r) (Fin r) E := (t : Matrix (Fin r) (Fin r) E) with hT
  set Ti : Matrix (Fin r) (Fin r) E := ((t⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hTi
  set mm : Matrix (Fin r) (Fin r) E := (m : Matrix (Fin r) (Fin r) E) with hmm
  set mi : Matrix (Fin r) (Fin r) E := ((m⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hmi
  have cTi : Ti * A₀ = A₀ * Ti := Commute.units_inv_left (u := t) ht
  have cm : mm * A₀ = A₀ * mm := by
    rw [← hm, mul_assoc, hstarC _ ht, ← mul_assoc, ht, mul_assoc]
  have cmi : mi * A₀ = A₀ * mi := Commute.units_inv_left (u := m) cm
  let xT : R := ⟨T, memR _ ht⟩
  let xTp : R := ⟨star T, memR _ (hstarC _ ht)⟩
  let xTi : R := ⟨Ti, memR _ cTi⟩
  let xTip : R := ⟨star Ti, memR _ (hstarC _ cTi)⟩
  let xmi : R := ⟨mi, memR _ cmi⟩
  let xf : R := ⟨f, memR _ hfA⟩
  let xg : R := ⟨g, memR _ (hstarC _ hfA)⟩
  have hfR : xf * xf = xf := Subtype.ext hff
  have hgR : xg * xg = xg := Subtype.ext (by show star f * star f = star f; rw [← star_mul, hff])
  have hfgR : xf * xg = 0 := Subtype.ext hffs
  have hTiR : xT * xTi = 1 := Subtype.ext (Units.mul_inv t)
  have hTpiR : xTp * xTip = 1 := Subtype.ext (by
    show star T * star Ti = 1
    rw [← star_mul, hT, hTi, Units.inv_mul, star_one])
  have hmiR : xmi * (xT * xTp) = 1 := Subtype.ext (by
    show mi * (T * star T) = 1
    rw [hm, hmi, hmm, Units.inv_mul])
  have heR : (1 - xf - xg) * (1 - xf - xg) = 1 - xf - xg := by linear_combination hfR + hgR + 2 * hfgR
  have hefR : (1 - xf - xg) * xf = 0 := by linear_combination -hfR - hfgR
  have hegR : (1 - xf - xg) * xg = 0 := by linear_combination -hgR - hfgR
  let X₀ : R := xT * (1 - xf - xg) + xT * xTp * xf + xg
  let X₁ : R := xTi * (1 - xf - xg) + xmi * xf + xg
  have h01 : X₀ * X₁ = 1 := by
    linear_combination (1 - xf - xg) * (1 - xf - xg) * hTiR + heR + xT * xmi * hefR + xT * hegR +
      xT * xTp * xTi * hefR + xf * xf * hmiR + hfR + xT * xTp * hfgR + xTi * hegR + xmi * hfgR + hgR
  have h10 : X₁ * X₀ = 1 := by rw [mul_comm]; exact h01
  let s : GL (Fin r) E := ⟨X₀.1, X₁.1, congrArg Subtype.val h01, congrArg Subtype.val h10⟩
  have hX₀ : X₀.1 = T * e + mm * f + g := by
    show T * (1 - f - g) + T * star T * f + g = _
    rw [hm]
  have hX₁ : X₁.1 = Ti * e + mi * f + g := rfl
  refine ⟨s, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨(T * e, mm), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₀.symm⟩
    · exact memR' _ (xT * (1 - xf - xg)).2
    · have : xT * (1 - xf - xg) * (1 - xf - xg) = xT * (1 - xf - xg) := by linear_combination xT * heR
      exact congrArg Subtype.val this
    · refine ⟨mm, ⟨m, hmM, rfl⟩, ?_⟩
      have : xT * xTp * (1 - xf - xg) = xT * (1 - xf - xg) * ((1 - xg - xf) * xTp) := by
        linear_combination (-(xT * xTp)) * heR
      have h2 := congrArg Subtype.val this
      show mm * e = T * e * star (T * e)
      rw [star_mul, hes, ← hm]
      exact h2
  · refine ⟨(Ti * e, mi), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₁.symm⟩
    · exact memR' _ (xTi * (1 - xf - xg)).2
    · have : xTi * (1 - xf - xg) * (1 - xf - xg) = xTi * (1 - xf - xg) := by linear_combination xTi * heR
      exact congrArg Subtype.val this
    · refine ⟨mi, ⟨m, hmM, rfl⟩, ?_⟩
      have hTT : xTi * xTip = xmi := by
        linear_combination (-(xTi * xTip)) * hmiR + xmi * xTp * xTip * hTiR + xmi * hTpiR
      have : xmi * (1 - xf - xg) = xTi * (1 - xf - xg) * ((1 - xg - xf) * xTip) := by
        linear_combination (-(xTi * xTip)) * heR - (1 - xf - xg) * hTT
      have h2 := congrArg Subtype.val this
      show mi * e = Ti * e * star (Ti * e)
      rw [star_mul, hes]
      exact h2
  · exact memR' _ X₀.2
  · have : X₀ * ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf) = xT * xTp := by
      linear_combination xT * xTp * heR + xT ^ 2 * xTp * hegR + xT * hefR + xT * xTp ^ 2 * hefR +
        xT ^ 2 * xTp ^ 2 * hfgR + xT * xTp * hfR + xTp * hegR + xT * xTp * hgR + hfgR
    have h2 := congrArg Subtype.val this
    have hst : star X₀.1 = ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf).1 := by
      show star (T * (1 - f - g) + T * star T * f + g) = (1 - g - f) * star T + g * (T * star T) + f
      rw [hg]
      simp only [star_add, star_mul, star_sub, star_one, star_star]
    show X₀.1 * star X₀.1 = T * star T
    rw [hst]
    exact h2

end GlobalTheory.NormSec
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → CountIdentity := by
  first | exact @GlobalTheory.CountId.countIdentity_of_unitMatch | exact GlobalTheory.CountId.countIdentity_of_unitMatch | (intros; apply GlobalTheory.CountId.countIdentity_of_unitMatch <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by
  first | exact @GlobalTheory.JR.annihilator_small | exact GlobalTheory.JR.annihilator_small | (intros; apply GlobalTheory.JR.annihilator_small <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  first | exact @GlobalTheory.UnitLemma.torus_mod_intUnits_structure | exact GlobalTheory.UnitLemma.torus_mod_intUnits_structure | (intros; apply GlobalTheory.UnitLemma.torus_mod_intUnits_structure <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.fourier_indicator_hermitianIntegralLattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  first | exact @GlobalTheory.JR.fourB_indicator_intLattice | exact GlobalTheory.JR.fourB_indicator_intLattice | (intros; apply GlobalTheory.JR.fourB_indicator_intLattice <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.whittaker_bound_big_cell : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  first | exact @GlobalTheory.JR.LamBound.main | exact GlobalTheory.JR.LamBound.main | (intros; apply GlobalTheory.JR.LamBound.main <;> assumption)
end
