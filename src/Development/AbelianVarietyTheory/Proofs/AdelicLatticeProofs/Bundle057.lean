module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimes
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle040
import Mathlib.Algebra.MvPolynomial.Funext
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle052
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle033
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem index_sqs_top_eq {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs (⊤ : Subgroup U)).index = (sqs U).relIndex U := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_subgroupOf,
    powMonoidHom_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using h)⟩

private theorem relIndex_sqs_range_eq {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    (sqs j.range).relIndex j.range = (sqs (⊤ : Subgroup U)).index := by
  rw [← Subgroup.index_comap]
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap,
    powMonoidHom_apply, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨y, hj (by simpa using h)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨j y, ⟨y, rfl⟩, by simp⟩

private theorem arith_first_ineq (m n e s t : ℕ) (hd : m ∣ n) (h : 2 * 2 ^ e * n = (2 ^ s) ^ 2)
    (hs : 2 * s ≤ e + t) : m ≠ 0 ∧ 2 * m ≤ 2 ^ t := by
  have hn : n ≠ 0 := by
    rintro rfl
    have : 0 < (2 ^ s) ^ 2 := by positivity
    omega
  refine ⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h1 : 2 ^ e * (2 * n) ≤ 2 ^ e * 2 ^ t := by
    calc 2 ^ e * (2 * n) = (2 ^ s) ^ 2 := by rw [← h]; ring
      _ = 2 ^ (2 * s) := by ring
      _ ≤ 2 ^ (e + t) := Nat.pow_le_pow_right (by norm_num) hs
      _ = 2 ^ e * 2 ^ t := pow_add _ _ _
  have h2 : 2 * n ≤ 2 ^ t := Nat.le_of_mul_le_mul_left h1 (by positivity)
  omega

theorem first_inequality_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
      admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) →
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤
          2 ^ (tFin F δ S + tReal F δ) := by
  intro F _ _ δ S hS hδ hns
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square F δ hns
  obtain ⟨SE, hSE⟩ := (GlobalTheory.T.heightOneSpectrum_places_over_finite_set F E).1 S
  obtain ⟨hinv, hfix, -, hnorm, -, -, -⟩ := GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ hq
  obtain ⟨hup, hσ⟩ := GlobalTheory.T.sUnits_places_over_and_quadratic_conj F E δ θ σ hq S SE hSE
  have h90 := GlobalTheory.T.hilbert90_sUnits_quadratic_extension_of_adm F E δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)
  have hcf := GlobalTheory.T.two_mul_card_places_le_card_over_quadratic F E δ θ σ hq S SE hSE
  have hci := GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic F E δ θ σ hq
  let τ : sUnits E SE →* sUnits E SE :=
    ((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ y y.2)
  have hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E) :=
    fun _ => rfl
  let j : sUnits F S →* sUnits E SE :=
    ((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _
      (fun y => (hup y).2 y.2)
  have hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F) :=
    fun _ => rfl
  have hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b :=
    fun a b h => Subtype.ext (Units.ext h)
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  have hm : (-1 : Eˣ) ∈ sUnits E SE := by
    rw [mem_sUnits]
    intro v _
    simp
  have hrange : τ.eqLocus (MonoidHom.id _) = j.range := by
    ext y
    rw [MonoidHom.mem_range]
    change τ y = y ↔ _
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hfix ((y : Eˣ) : E) (by rw [← hτ, h])
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact (y : Eˣ).ne_zero (by simpa using ha)
      have hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y :=
        Units.ext (by simpa using ha.symm)
      refine ⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩
      rw [hj, ha]; rfl
    · rintro ⟨x, rfl⟩
      apply hext
      rw [hτ, hj, AlgEquiv.commutes]
  have key := GlobalTheory.T.index_formula_norms_involution (sUnits E SE) τ ⟨-1, hm⟩
    (fun a => hext _ _ (by rw [hτ, hτ, hinv]))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) * σ ((a : Eˣ) : E) = 1 := by
        rw [← hτ]
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      obtain ⟨y, hy, h⟩ := h90 a a.2 h1
      refine ⟨⟨y, hy⟩, hext _ _ ?_⟩
      rw [h, Subgroup.coe_div, Units.val_div_eq_div_val, hτ])
    (fun h => by
      have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) h
      simp only [Units.val_neg, Units.val_one, OneMemClass.coe_one] at this
      norm_num at this)
    (hext _ _ (by simp))
    (hext _ _ (by rw [hτ]; simp))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) ^ 2 = 1 := by
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      rcases sq_eq_one_iff.1 h1 with h | h
      · exact Or.inl (hext _ _ (by simpa using h))
      · exact Or.inr (hext _ _ (by simpa using h)))
  rw [hrange, relIndex_sqs_range_eq j hjinj, index_sqs_top_eq, index_sqs_top_eq,
    GlobalTheory.T.relIndex_squares_sUnitsNumberField E SE, GlobalTheory.T.relIndex_squares_sUnitsNumberField F S, ← Subgroup.index_comap] at key
  refine arith_first_ineq _ _ _ _ _ ?_ key (by omega)
  apply Subgroup.index_dvd_of_le
  rintro x ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, mem_normSub]
  obtain ⟨a, b, hab⟩ := hnorm ((y : Eˣ) : E)
  refine ⟨a, b, ?_⟩
  apply (algebraMap F E).injective
  simp only [RingHom.id_apply]
  rw [← hab, ← hj, ← hy, ← hτ]
  simp

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.ReynoldsLtr

variable {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul] at hp ⊢
    rw [hp]
    simp [ltr, Matrix.mul_apply]


omit [DecidableEq ι] in
theorem isInv_iff (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f := by
  constructor
  · intro h g hg
    apply MvPolynomial.funext
    intro x
    have h1 := evC_ltr g (Matrix.of fun i j => x (i, j)) f
    rw [h g hg] at h1
    simpa [evC] using h1
  · intro h g hg y
    rw [← evC_ltr, h g hg]

theorem exists_isReynolds : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ Rey, IsReynolds Γ Rey := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, h1, h2, -, -, h5, h6⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ)
    ((fun g => (ltr g).toLinearMap) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible ι Γ hΓ hss U
        (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ f hf
      exact hU' g hg f hf)
  refine ⟨Rey, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [isInv_iff]
    intro g hg
    exact h1 f _ ⟨g, hg, rfl⟩
  · intro f hf
    rw [isInv_iff] at hf
    apply h2
    rintro _ ⟨g, hg, rfl⟩
    exact hf g hg
  · intro a f ha
    rw [isInv_iff] at ha
    refine h5 (LinearMap.mulLeft ℂ a) ?_ f
    rintro _ ⟨g, hg, rfl⟩ v
    simp only [LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul, ha g hg]
  · intro U hU
    apply h6
    rintro _ ⟨g, hg, rfl⟩ f hf
    exact hU g hg f hf

end GlobalTheory.ClassFin.ReynoldsLtr
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem invariant_form_eq_sum_invariant_tensors : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ (n : ℕ) (F : MvPolynomial (ι × ι) ℂ), IsInv Γ F → F.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, (∀ b, ∀ g ∈ Γ, l b ᵥ* tpow n g = l b) ∧ ∀ y : Matrix ι ι ℂ, evC F y = ∑ b, (l b ᵥ* tpow n y) b := by
  intro ι _ _ Γ hP hS n F hF hhom
  obtain ⟨-, hinv, -, hp⟩ := GlobalTheory.T.leftTranslateMatrixPoly_tensorForm_properties ι
  obtain ⟨p, hpev, hpl, hpsurj⟩ := hp n
  obtain ⟨l, hl⟩ := hpsurj F hhom
  obtain ⟨R₁, h1a, -, -, h1d, -, -⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' ((Fin n → ι) → ℂ)
    ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.completelyReducible_kroneckerPower_transpose ι Γ hP hS n U (by
        rintro _ ⟨g, hg, rfl⟩ v hv
        simpa [Matrix.toLin'_apply] using hU _ ⟨g, hg, rfl⟩ v hv)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ v hv
      simpa [Matrix.toLin'_apply] using hU' _ ⟨g, hg, rfl⟩ v hv)
  obtain ⟨R₂, -, h2b, h2c, -, -, -⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ)
    ((fun g => (ltr g).toLinearMap) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible ι Γ hP hS U (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ v hv
      exact hU' g hg v hv)
  have hfix : ∀ v, ∀ g ∈ Γ, R₁ v ᵥ* tpow n g = R₁ v := by
    intro v g hg
    have := h1a v _ ⟨g, hg, rfl⟩
    simpa [Matrix.toLin'_apply, Matrix.mulVec_transpose] using this
  have hkill : ∀ b, ∀ x ∈ Submodule.span ℂ
      {x | ∃ s ∈ ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ), ∃ w, x = s w - w}, R₂ (p b x) = 0 := by
    intro b x hx
    have hle : Submodule.span ℂ
        {x | ∃ s ∈ ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ), ∃ w, x = s w - w}
        ≤ LinearMap.ker (R₂ ∘ₗ p b) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, rfl⟩, w, rfl⟩
      have h := h2c (p b w) _ ⟨g, hg, rfl⟩
      simp only [AlgHom.toLinearMap_apply, hpl] at h
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, map_sub,
        Matrix.toLin'_apply, Matrix.mulVec_transpose, h, sub_self]
    exact hle hx
  have hb : ∀ b v, R₂ (p b v) = p b (R₁ v) := by
    intro b v
    have h0 := hkill b _ (h1d v)
    rw [map_sub, map_sub, sub_eq_zero] at h0
    rw [h0]
    apply h2b
    rintro _ ⟨g, hg, rfl⟩
    simp only [AlgHom.toLinearMap_apply, hpl, hfix v g hg]
  have hRF : R₂ F = F := by
    apply h2b
    rintro _ ⟨g, hg, rfl⟩
    exact (hinv Γ F).1 hF g hg
  have hF' : F = ∑ b, p b (R₁ (l b)) := by

    rw [← hRF, hl, map_sum]
    exact Finset.sum_congr rfl fun b _ => hb b _
  refine ⟨fun b => R₁ (l b), fun b g hg => hfix _ g hg, fun y => ?_⟩
  rw [hF']
  simp only [← hpev]
  unfold evC

  rw [map_sum]

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_complexPoly_blockDiagPart_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC f x = evC b (blk e x) := by
  first | exact @GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const | exact GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const | (intros; apply GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  first | exact @GlobalTheory.ClassFin.RatClosure.ratClosure | exact GlobalTheory.ClassFin.RatClosure.ratClosure | (intros; apply GlobalTheory.ClassFin.RatClosure.ratClosure <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.unitaryGroup_weak_approximation_at_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N D : ℕ), IsUnA c G g.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N D (fm F γ.1 * g.1) := by
  first | exact @GlobalTheory.UnRep.WeakApprox.weak_approximation | exact GlobalTheory.UnRep.WeakApprox.weak_approximation | (intros; apply GlobalTheory.UnRep.WeakApprox.weak_approximation <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_sup_finNorm_ne_top : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → sUnits F S ⊔ finNorm p F δ S ≠ ⊤ := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hr htop
  obtain ⟨h0, h1⟩ := GlobalTheory.T.first_inequality_sUnits_prime_degree p F ζ δ S hp hζ hS hδ hr
  obtain ⟨-, h2⟩ := GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ δ S hp hζ
  have hle : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S :=
    le_iInf₂ fun _ _ => (GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).2 F _ _ _
  have h3 : (finNorm p F δ S).index = (finNorm p F δ S).relIndex (sUnits F S) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h4 := Subgroup.relIndex_le_of_le_left hle h0
  have h5 := Nat.mul_le_mul_right ((kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S)) hp.two_le
  omega

end GlobalTheory.CNorm
end
