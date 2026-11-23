module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Mathlib.Analysis.Meromorphic.Order
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePoint
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_clear_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (P : Polynomial T.K), P ≠ 0 → ∃ (p : ℕ → GlobalTheory.FN.ring ε.range) (u : T.K), u ≠ 0 ∧ p P.natDegree ≠ 0 ∧ ∀ i, T.io (p i) = u * P.coeff i := by
  first | exact @GlobalTheory.FN.clear_denominators | exact GlobalTheory.FN.clear_denominators | (intros; apply GlobalTheory.FN.clear_denominators <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (p q : Fin n → k) (a : Fin n) (u : kˣ), valuation k (u : k) = 1 → g.val = 1 + Matrix.vecMulVec p q → (∀ i, p i * q i = if i = a then (u : k) - 1 else 0) → theta ψ g = (ψ a u : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_rankOne | exact GlobalTheory.PsType.theta_rankOne | (intros; apply GlobalTheory.PsType.theta_rankOne <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_of_triangular | exact GlobalTheory.PsType.theta_of_triangular | (intros; apply GlobalTheory.PsType.theta_of_triangular <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ m : Fin n, ¬ Triv (ψ m / nxt ψ m) 1 → (∀ a ∈ grp ψ, valuation k (minor a m) = 1) ∧ ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, Triv (ψ m / nxt ψ m) (minor (a * b) m - minor a m * minor b m) := by
  first | exact @GlobalTheory.PsType.minor_mul_mod | exact GlobalTheory.PsType.minor_mul_mod | (intros; apply GlobalTheory.PsType.minor_mul_mod <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesType_data_depend_only_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧ ∀ r, Cut ψ r → Cut ω r := by
  first | exact @GlobalTheory.PsType.agree_main | exact GlobalTheory.PsType.agree_main | (intros; apply GlobalTheory.PsType.agree_main <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def congrAlg (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) :
    Subalgebra 𝒪[k] (Matrix (Fin n) (Fin n) 𝒪[k]) where
  carrier := {M | ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) ((M i j : 𝒪[k]) : k)}
  mul_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
      (triv_zero _) ?_
    intro l _
    have hAv : valuation k ((A i l : 𝒪[k]) : k) ≤ 1 := (A i l).2
    have hBv : valuation k ((B l j : 𝒪[k]) : k) ≤ 1 := (B l j).2
    have h1 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((B l j : 𝒪[k]) : k) := mul_le_of_le_one_left' hAv
    have h2 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((A i l : 𝒪[k]) : k) := mul_le_of_le_one_right' hBv
    rcases le_or_gt l i with hli | hil
    · refine triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) ?_
      exact hψ l i j j hli hij.le le_rfl _ (hB l j (lt_of_le_of_lt hli hij))
    rcases le_or_gt j l with hjl | hlj
    · refine triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) ?_
      exact hψ i i j l le_rfl hij.le hjl _ (hA i l hil)
    · have e : ψ i / ψ l * (ψ l / ψ j) = ψ i / ψ j := div_mul_div_cancel _ _ _
      rw [← e]
      exact triv_mul _ _ _ (triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) (hA i l hil))
        (triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) (hB l j hlj))
  one_mem' := by
    intro i j hij
    simp [Matrix.one_apply_ne hij.ne, triv_zero]
  add_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    simpa using triv_add _ _ _ (hA i j hij) (hB i j hij)
  zero_mem' := by
    intro i j hij
    simp [triv_zero]
  algebraMap_mem' := by
    intro c i j hij
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply_ne _ hij.ne, triv_zero]

theorem inv_val_mem_adjoin {R : Type} [CommRing R] {m : ℕ} (g : GL (Fin m) R) :
    ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) ∈ Algebra.adjoin R {(g : Matrix (Fin m) (Fin m) R)} := by
  set A : Matrix (Fin m) (Fin m) R := (g : Matrix (Fin m) (Fin m) R)
  set p := A.charpoly
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  have hdec : p.divX * Polynomial.X + Polynomial.C (p.coeff 0) = p := Polynomial.divX_mul_X_add p
  have hdet : A.det = (-1) ^ Fintype.card (Fin m) * p.coeff 0 := Matrix.det_eq_sign_charpoly_coeff A
  have hu : IsUnit (p.coeff 0) := by
    have h := (Matrix.isUnit_iff_isUnit_det A).mp (Units.isUnit g)
    rw [hdet] at h
    exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hu
  have h1 : Polynomial.aeval A p.divX * A = -algebraMap R _ (p.coeff 0) := by
    rw [← hdec] at hCH
    simp only [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
    exact eq_neg_of_add_eq_zero_left hCH
  have key : ((-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX) * A = 1 := by
    rw [smul_mul_assoc, h1, Algebra.algebraMap_eq_smul_one, ← hu, neg_smul_neg, smul_smul,
      Units.inv_mul, one_smul]
  have e : ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = (-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX :=
    Units.inv_eq_of_mul_eq_one_left key
  rw [e]
  exact Subalgebra.smul_mem _ (Polynomial.aeval_mem_adjoin_singleton R A) _

end GlobalTheory.PsType


open GlobalTheory.PsType in
theorem GlobalTheory.PsType.grp_inv_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, a⁻¹ ∈ grp ψ := by
  intro k _ _ _ _ n ψ hψ a ha
  obtain ⟨haK, hat⟩ := ha
  obtain ⟨g, rfl⟩ := haK
  have hg : (g : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ := fun i j hij => hat i j hij
  have hinv : ((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hg) (inv_val_mem_adjoin g)
  refine ⟨inv_mem ⟨g, rfl⟩, ?_⟩
  intro i j hij
  rw [← map_inv]
  exact hinv i j hij
end
end

section

open Matrix GlobalTheory.KZ
open Filter Topology

theorem _root_.GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ), τ ∈ Hs → ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  first | exact @GlobalTheory.KZ.ValAt.exists_place | exact GlobalTheory.KZ.ValAt.exists_place | (intros; apply GlobalTheory.KZ.ValAt.exists_place <;> assumption)
end

section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.exists_derivationOn_iSup_of_compatible : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B : ℕ → Subalgebra A S), Monotone B → ∀ D : ℕ → S → M, (∀ m, IsDerOn (B m) (D m)) → (∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) → ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  first | exact @GlobalTheory.AlmostEt.isDerOn_iSup_glue | exact GlobalTheory.AlmostEt.isDerOn_iSup_glue | (intros; apply GlobalTheory.AlmostEt.isDerOn_iSup_glue <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_int_exponent_congr_cyclotomicCharacter : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ), 0 < M → l ^ n ∣ M → ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧ (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  first | exact @GlobalTheory.KZ.exists_int_exponent_cyclotomic | exact GlobalTheory.KZ.exists_int_exponent_cyclotomic | (intros; apply GlobalTheory.KZ.exists_int_exponent_cyclotomic <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.localPowerUnitsTower_closure_properties : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 1 ∈ X.Un m ∧ (∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m) ∧ (∀ f, f ∈ X.Un m → f⁻¹ ∈ X.Un m) ∧ (∀ g : X.Kˣ, g ^ m ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un (m * k) → f ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un m → f ^ k ∈ X.Un m) ∧ ∀ (k : ℕ) (g : X.Kˣ), 0 < m → g ^ m ∈ X.Un (m * k) → g ∈ X.Un k := by
  first | exact @GlobalTheory.KZ.UnClosure.un_closure | exact GlobalTheory.KZ.UnClosure.un_closure | (intros; apply GlobalTheory.KZ.UnClosure.un_closure <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory


open scoped MatrixGroups TensorProduct in
open Matrix in
theorem _root_.GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l n M : ℕ) [Fact l.Prime] (hM : 0 < M) (hn : l ^ n ∣ M) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧ ∃ i : ℕ, i.Coprime M ∧ s ζ = ζ ^ i ∧
      (i : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hcard : Nat.card (rootsOfUnity M Ω) = M := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω M
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  set c := modularCyclotomicCharacter Ω hcard s.toRingEquiv with hc
  have hsζ : s ζ = ζ ^ (c : ZMod M).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard s.toRingEquiv hζ.toRootsOfUnity.2
    simpa using h
  refine ⟨ζ, hζ, (c : ZMod M).val, ZMod.val_coe_unit_coprime c, hsζ, ?_⟩
  rw [cyclotomicCharacter.toZModPow]
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hcard' : Nat.card (rootsOfUnity (l ^ n) Ω) = l ^ n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)
  set c' := modularCyclotomicCharacter Ω hcard' s.toRingEquiv
  have hζ' : IsPrimitiveRoot (ζ ^ (M / l ^ n)) (l ^ n) :=
    hζ.pow hM (Nat.div_mul_cancel hn).symm
  have h1 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c : ZMod M).val := by
    rw [map_pow, hsζ, ← pow_mul, ← pow_mul, mul_comm]
  have h2 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c' : ZMod (l ^ n)).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard' s.toRingEquiv hζ'.toRootsOfUnity.2
    simpa using h
  have hfin : IsOfFinOrder (ζ ^ (M / l ^ n)) :=
    orderOf_pos_iff.1 (by rw [← hζ'.eq_orderOf]; exact Nat.pos_of_ne_zero (NeZero.ne _))
  have h3 := hfin.pow_eq_pow_iff_modEq.1 (h1.symm.trans h2)
  rw [← hζ'.eq_orderOf] at h3
  rw [← ZMod.natCast_zmod_val (c' : ZMod (l ^ n))]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3


open scoped MatrixGroups TensorProduct in
open Matrix in
theorem _root_.GlobalTheory.exists_sl2_conj_diag_zmod (M i : ℕ) (hi : i.Coprime M) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), (_root_.GlobalTheory.KZ.en γ 0 0 : ZMod M) = _root_.GlobalTheory.KZ.en δ 0 0 ∧
      (_root_.GlobalTheory.KZ.en γ 0 1 : ZMod M) = (i : ZMod M) * _root_.GlobalTheory.KZ.en δ 0 1 ∧
      (i : ZMod M) * _root_.GlobalTheory.KZ.en γ 1 0 = _root_.GlobalTheory.KZ.en δ 1 0 ∧
      (_root_.GlobalTheory.KZ.en γ 1 1 : ZMod M) = _root_.GlobalTheory.KZ.en δ 1 1 := by
  set u : (ZMod M)ˣ := ZMod.unitOfCoprime i hi
  have hu : (u : ZMod M) = i := rfl
  have hγdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hγdet
  set m : Matrix (Fin 2) (Fin 2) (ZMod M) :=
    !![((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod M),
      ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M);
      (i : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M),
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod M)] with hm_def
  have hm : m.det = 1 := by
    rw [hm_def, Matrix.det_fin_two_of]
    have h1 : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (i : ZMod M) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 := congrArg (Int.cast : ℤ → ZMod M) hγdet
    push_cast at h2
    linear_combination h2 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M) * h1
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M ⟨m, hm⟩
  have he : ∀ a b, (((δ : Matrix (Fin 2) (Fin 2) ℤ) a b : ℤ) : ZMod M) = m a b := fun a b => by
    have h := congrArg (fun g : SL(2, ZMod M) => (g : Matrix (Fin 2) (Fin 2) (ZMod M)) a b) hδ
    simpa using h
  refine ⟨δ, ?_, ?_, ?_, ?_⟩ <;> simp only [_root_.GlobalTheory.KZ.en, he, hm_def]
  · simp
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← mul_assoc, ← hu, Units.mul_inv, one_mul]
  · simp
  · simp

theorem exists_conj_level_exponent :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N l n M : ℕ) [Fact l.Prime], 0 < M → N ∣ M → l ∣ M →
      l ^ n ∣ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)), γ ∈ Gam N l → ∃ γ'' ∈ Gam N l, ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧
      ∃ d : ℤ, s ζ = ζ ^ d ∧ ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧
        (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) ∧
        (d : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  intro Ω _ _ _ N l n M _ hM hN hl hn s γ hγ
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hn s
  obtain ⟨δ, h00, h01, h10, h11⟩ := exists_sl2_conj_diag_zmod M i hi γ
  have red : ∀ {K : ℕ}, K ∣ M → ∀ {x y : ℤ}, (x : ZMod M) = y → (x : ZMod K) = y := fun {K} hK x y h => by
    simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h
  have h10' : (((i : ℤ) * en γ 1 0 : ℤ) : ZMod M) = en δ 1 0 := by push_cast; exact h10
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a1, a2, a3⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ1
  have a4 := CongruenceSubgroup.Gamma0_mem.1 hγ0
  refine ⟨δ, Subgroup.mem_inf.2 ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨?_, ?_, ?_⟩,
    CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ζ, hζ, i, by rw [zpow_natCast, hs], ⟨h00, ?_, ?_, h11⟩, ?_⟩
  · exact (red hN h00).symm.trans a1
  · exact (red hN h11).symm.trans a2
  · refine (red hN h10').symm.trans ?_
    have : (en γ 1 0 : ZMod N) = 0 := a3
    rw [Int.cast_mul, this, mul_zero]
  · refine (red hl h10').symm.trans ?_
    have : (en γ 1 0 : ZMod l) = 0 := a4
    rw [Int.cast_mul, this, mul_zero]
  · simpa only [Int.cast_natCast] using h01
  · simpa only [Int.cast_natCast] using h10
  · simpa only [Int.cast_natCast] using hχ

end GlobalTheory
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.HeckeUNormInv

theorem coe_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  simp [toGQ, h]

theorem coe_ofSL (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  simp [ofSL]

theorem det_mj (j l : ℤ) (hl : 0 < l) : 0 < (!![1, j; 0, l] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  simp [Matrix.det_fin_two]; exact hl

theorem key (N l n : ℕ) (hn : 0 < n) (hl : 0 < l) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n))
    (j : ℕ) : ∃ γ' ∈ CongruenceSubgroup.Gamma1 (N * l ^ n),
      toGQ !![1, (j : ℤ); 0, (l : ℤ)] * ofSL γ =
        ofSL γ' * toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)] := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨ha, hd, hc⟩ := (CongruenceSubgroup.Gamma1_mem _ _).1 hγ
  have hdvd : l ∣ N * l ^ n := dvd_mul_of_dvd_right (dvd_pow_self l hn.ne') N
  have ha' : ((γ 0 0 : ℤ) : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) ha; rwa [map_intCast, map_one] at this
  have hd' : ((γ 1 1 : ℤ) : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) hd; rwa [map_intCast, map_one] at this
  have hc' : ((γ 1 0 : ℤ) : ZMod l) = 0 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) hc; rwa [map_intCast, map_zero] at this
  have hk : ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ) = (γ 0 1 + j) % (l : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [hk]
  set k : ℤ := (γ 0 1 + j) % (l : ℤ) with hkdef
  obtain ⟨b', hb'⟩ : (l : ℤ) ∣ γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ha', hd', hc', hkdef, ZMod.intCast_mod]
    push_cast; ring
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0 + j * γ 1 0, b'; l * γ 1 0, γ 1 1 - k * γ 1 0], by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + γ 1 0 * hb'⟩
  have hbq : ((γ 0 1 : ℚ) + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) = l * b' := by exact_mod_cast hb'
  refine ⟨γ', ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [γ'] <;> push_cast <;> simp [ha, hd, hc]
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [coe_toGQ _ (det_mj _ _ (by omega)), coe_toGQ _ (det_mj _ _ (by omega)), coe_ofSL, coe_ofSL]
    ext i i'
    fin_cases i <;> fin_cases i' <;> simp [Matrix.mul_apply, γ'] <;> push_cast <;> first | linear_combination | linear_combination hbq

theorem emod_toNat_lt (x : ℤ) {l : ℕ} (hl : 0 < l) : (x % (l : ℤ)).toNat < l := by
  have h1 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by omega)
  omega

theorem emod_inv (b : ℤ) {l : ℕ} (hl : 0 < l) (a : ℕ) (ha : a < l) :
    ((((((b + a) % (l : ℤ)).toNat : ℕ) : ℤ) - b) % (l : ℤ)).toNat = a := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.sub_emod, Int.emod_emod, ← Int.sub_emod,
    add_sub_cancel_left, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem emod_inv' (b : ℤ) {l : ℕ} (hl : 0 < l) (a : ℕ) (ha : a < l) :
    ((b + ((((a : ℤ) - b) % (l : ℤ)).toNat : ℤ)) % (l : ℤ)).toNat = a := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.add_emod, Int.emod_emod, ← Int.add_emod,
    add_sub_cancel, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

end GlobalTheory.HeckeUNormInv


open GlobalTheory.HeckeUNormInv in
theorem GlobalTheory.normInv_gamma1 : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ g : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g →
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) := by
  intro Ω _ _ ε X N l _ n hn g hg γ hγ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  rw [map_prod]
  have step : ∀ j : ℕ, X.sl (ofSL γ) (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) =
      X.sl (toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)]) g := by
    intro j
    obtain ⟨γ', hγ', heq⟩ := key N l n hn hl γ hγ j
    rw [← X.sl_mul, heq, X.sl_mul, hg γ' hγ']
  rw [Finset.prod_congr rfl (fun j _ => step j)]
  exact Finset.prod_nbij' (fun j => ((γ 0 1 + j) % (l : ℤ)).toNat) (fun k => (((k : ℤ) - γ 0 1) % (l : ℤ)).toNat)
    (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl)) (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl))
    (fun a ha => emod_inv _ hl a (Finset.mem_range.1 ha)) (fun a ha => emod_inv' _ hl a (Finset.mem_range.1 ha))
    (fun _ _ => rfl)
end
