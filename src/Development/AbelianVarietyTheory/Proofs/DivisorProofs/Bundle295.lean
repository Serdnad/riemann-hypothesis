module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeEqZpowStdInertCompletion
public import Formalism.SatakeDualWeyl.StatementG
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle180
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

@[expose] public section

section

open NumberField

theorem _root_.GlobalTheory.T.twistedProjector_orthogonal_of_unitary_action : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL), ∀ σ : LL →+* ℂ, A.eOp eC ∘ₗ A.eOp eC = A.eOp eC →
    (∀ g x y, inner ℂ (A.j σ (A.ρ g x)) (A.j σ (A.ρ g y)) = inner ℂ (A.j σ x) (A.j σ y)) →
    (∀ g, σ (eC g⁻¹) = starRingEnd ℂ (σ (eC g))) →
    ∀ x y, ‖A.j σ (A.eOp eC x + (y - A.eOp eC y))‖ ^ 2 = ‖A.j σ (A.eOp eC x)‖ ^ 2 + ‖A.j σ (y - A.eOp eC y)‖ ^ 2 := by
  first | exact @GlobalTheory.twistedProjector_orthogonal_of_unitary | exact GlobalTheory.twistedProjector_orthogonal_of_unitary | (intros; apply GlobalTheory.twistedProjector_orthogonal_of_unitary <;> assumption)
end

section

noncomputable section

open Polynomial Formalism.UG

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL_of {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {x : L} (hx : x ∈ intL L) :
    σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]; exact hx

def sigO (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  σ.restrict (intL L) (intL L) fun _ hx => mem_intL_of hσ hx

def piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : intL L :=
  ⟨ϖ, by
    change Valued.v ϖ ≤ 1
    rw [h.2.2.2.1]
    exact_mod_cast (WithZero.coe_le_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1))⟩

@[simp] theorem coe_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : ((piO h : intL L) : L) = ϖ := rfl

def unitFil {R : Type} [CommRing R] (I : Ideal R) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have e : ((a * b : Rˣ) : R) - 1 = (a : R) * ((b : R) - 1) + ((a : R) - 1) := by push_cast; ring
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [e]; exact I.add_mem (I.mul_mem_left _ hb) ha
  inv_mem' := fun {a} ha => by
    have e : ((a⁻¹ : Rˣ) : R) - 1 = -((a⁻¹ : Rˣ) : R) * ((a : R) - 1) := by
      rw [neg_mul, mul_sub, Units.inv_mul, mul_one]; ring
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [e]; exact I.mul_mem_left _ ha

theorem mem_unitFil {R : Type} [CommRing R] {I : Ideal R} {u : Rˣ} : u ∈ unitFil I ↔ (u : R) - 1 ∈ I := Iff.rfl

def piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (m : ℕ) :
    Ideal (AdjoinRoot P.1) :=
  Ideal.span {algebraMap (intL L) (AdjoinRoot P.1) (piO h) ^ m}

def filt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (m : ℕ) :
    Subgroup (AdjoinRoot P.1)ˣ :=
  unitFil (piPow h P m)

theorem mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} {h : IsUnramInv ϖ σ q} {P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)} {m : ℕ}
    {u : (AdjoinRoot P.1)ˣ} : u ∈ filt h P m ↔ (u : AdjoinRoot P.1) - 1 ∈ piPow h P m := Iff.rfl

theorem piPow_antitone {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    Antitone (piPow h P) := fun a b hab => by
  unfold piPow
  rw [Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow _ hab

theorem filt_antitone {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    Antitone (filt h P) := fun a b hab _ hu => piPow_antitone h P hab hu

theorem filt_zero {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    filt h P 0 = ⊤ := by
  ext u; simp [filt, mem_unitFil, piPow]

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem piO_mem_of_isMaximal {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {M : Ideal (intL L)}
    (hM : M.IsMaximal) : piO h ∈ M := by
  by_contra hϖ
  obtain ⟨y, i, hi, e⟩ := hM.exists_inv hϖ
  have hlt : Valued.v ((y : L) * ϖ) < 1 := by
    rw [map_mul, h.2.2.2.1]
    have hy : Valued.v (y : L) ≤ 1 := y.2
    calc Valued.v (y : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul]
          exact_mod_cast (WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))
  have hi1 : (i : L) = 1 - (y : L) * ϖ := by
    have := congrArg Subtype.val e
    simp only [Subring.coe_add, Subring.coe_mul, coe_piO, OneMemClass.coe_one] at this
    linear_combination this
  have hv : Valued.v (i : L) = 1 := by rw [hi1]; exact Valuation.map_one_sub_of_lt _ hlt
  have hi0 : (i : L) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hinv : (i : L)⁻¹ ∈ intL L := by
    change Valued.v ((i : L)⁻¹) ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hu : IsUnit i := isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hi0])⟩
  exact hM.ne_top (M.eq_top_of_isUnit_mem hi hu)

theorem isUnit_one_add_piO_mul {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (a : AdjoinRoot P.1) :
    IsUnit (1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a) := by
  by_contra hn
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  letI : Module.Finite (intL L) (AdjoinRoot P.1) := .of_basis (AdjoinRoot.powerBasis' P.2.1).basis
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap (intL L) (AdjoinRoot P.1))
    (RingHom.IsIntegral.of_finite (RingHom.finite_algebraMap.mpr inferInstance)) M
  have hϖ : algebraMap (intL L) (AdjoinRoot P.1) (piO h) ∈ M := piO_mem_of_isMaximal h hmax
  have h1 : 1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a ∈ M := hxM (Ideal.mem_span_singleton_self _)
  have : (1 : AdjoinRoot P.1) ∈ M := by
    have := M.sub_mem h1 (M.mul_mem_right a hϖ)
    simpa using this
  exact hM.ne_top ((Ideal.eq_top_iff_one M).2 this)

theorem isUnit_of_sub_one_mem {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) {m : ℕ} (hm : 1 ≤ m) {x : AdjoinRoot P.1} (hx : x - 1 ∈ piPow h P m) :
    IsUnit x := by
  have hx1 : x - 1 ∈ piPow h P 1 := piPow_antitone h P hm hx
  unfold piPow at hx1
  rw [pow_one, Ideal.mem_span_singleton'] at hx1
  obtain ⟨a, ha⟩ := hx1
  have := isUnit_one_add_piO_mul h P a
  rwa [mul_comm, ha, add_sub_cancel] at this

end GlobalTheory.NormEq
end
end

section

open Polynomial Matrix GlobalTheory.LatOrb

theorem _root_.GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq : ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  first | exact @GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | exact GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | (intros; apply GlobalTheory.LatOrb.mem_GLint_iff_matLat_std <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open NumberField

theorem _root_.GlobalTheory.T.cayleyTransform_skew_mem_unitaryGroup : ∀ {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J S : Matrix (Fin n) (Fin n) E),
    J.det ≠ 0 → Formalism.UG.cT σ S * J + J * S = 0 → (1 - S).det ≠ 0 →
    ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ σ J ∧ (γ : Matrix (Fin n) (Fin n) E) = (1 + S) * (1 - S)⁻¹ := by
  first | exact @GlobalTheory.CayleyUnitary.cayley_mem_UJ | exact GlobalTheory.CayleyUnitary.cayley_mem_UJ | (intros; apply GlobalTheory.CayleyUnitary.cayley_mem_UJ <;> assumption)
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField

theorem _root_.GlobalTheory.T.mvPolynomial_eq_zero_of_vanish_skewHermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → σ ≠ AlgHom.id F E → Module.finrank F E = 2 →
    ∀ {ι : Type} [Fintype ι] (ψ : ι → (E →+* ℂ)), Function.Injective (fun τ => (ψ τ).comp (algebraMap F E)) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) J = J → J.det ≠ 0 →
    ∀ Q : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ S : Matrix (Fin n) (Fin n) E, Formalism.UG.cT (σ : E →+* E) S * J + J * S = 0 →
        MvPolynomial.eval (fun p => ψ p.1 (S p.2.1 p.2.2)) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.SkewDense.eq_zero_of_vanish_skew | exact GlobalTheory.SkewDense.eq_zero_of_vanish_skew | (intros; apply GlobalTheory.SkewDense.eq_zero_of_vanish_skew <;> assumption)
end
end

section

open IsDedekindDomain NumberField
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_lattice_eq_zpow_std_inert_completion : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ (ϖ : P.adicCompletion E), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (n : ℕ) (L : AddSubgroup (Fin n → P.adicCompletion E)) (N : P.adicCompletion E), N ≠ 0 → (∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L) → (∀ w : Fin n → P.adicCompletion E, (∀ i, Valued.v (w i) ≤ 1) → N • w ∈ L) → (∀ w ∈ L, ∀ i, Valued.v (N * w i) ≤ 1) → (∀ U : GL (Fin n) (P.adicCompletion E), U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L) → ∃ k : ℤ, ∀ w, w ∈ L ↔ ∀ i, Valued.v (ϖ ^ k * w i) ≤ 1 := by
  first | exact @GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std | exact GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std | (intros; apply GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.valuation_algebraMap_eq_of_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  first | exact @GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt | exact GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt | (intros; apply GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.valuation_algHom_eq_of_inertPrime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ x : E, w.valuation E (σ x) = w.valuation E x := by
  first | exact @GlobalTheory.InertConjVal.val_conj | exact GlobalTheory.InertConjVal.val_conj | (intros; apply GlobalTheory.InertConjVal.val_conj <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.InertDifferentGen

theorem exists_mul_valuation_eq_one {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ δ ∈ J⁻¹, ∃ z ∈ J, w.valuation E (δ * z) = 1 := by
  by_contra h
  push Not at h
  have h1 : J⁻¹ * J = 1 := inv_mul_cancel₀ hJ
  have hone : (1 : E) ∈ J⁻¹ * J := by rw [h1]; exact FractionalIdeal.one_mem_one _
  have key : w.valuation E (1 : E) < 1 := by
    refine FractionalIdeal.mul_induction_on (C := fun x => w.valuation E x < 1) hone ?_ ?_
    · intro a ha b hb
      have hm : a * b ∈ J⁻¹ * J := FractionalIdeal.mul_mem_mul ha hb
      rw [h1, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨x, hx⟩ := hm
      refine lt_of_le_of_ne ?_ (h a ha b hb)
      rw [← hx]
      exact w.valuation_le_one x
    · intro x y hx hy
      exact Valuation.map_add_lt _ hx hy
  simp at key

theorem mem_dual_one_iff {E : Type} [Field E] [NumberField E] (e : E) :
    e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e)) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 E)⁰ E))]
  constructor
  · intro h o
    obtain ⟨k, hk⟩ := h (o : E) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at hk
    rw [← hk]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h o)
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, mul_comm]
    exact hk

theorem exists_generator_different_of_isInertAt :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ ∃ s₁ s₂ : E, w.valuation E s₁ = 1 ∧ w.valuation E s₂ = 1 ∧
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) := by
  intro F E _ _ _ _ _ v w hin
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  obtain ⟨δ, hδ, z, hz, hδz⟩ := exists_mul_valuation_eq_one w _ hJ
  obtain ⟨t, ht⟩ := v.valuation_surjective F (w.valuation E δ)
  rw [← GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hin] at ht
  have hδ0 : w.valuation E δ ≠ 0 := by
    intro h0
    rw [map_mul, h0, zero_mul] at hδz
    exact zero_ne_one hδz
  have htE : algebraMap F E t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ht
    exact hδ0 ht.symm
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htE (map_zero _)
  refine ⟨t, ht0, δ / algebraMap F E t, algebraMap F E t * z, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, ht, div_self hδ0]
  · rw [map_mul, ht, ← map_mul, hδz]
  · intro e he
    rw [div_mul_cancel₀ _ htE]
    have hm := FractionalIdeal.mul_mem_mul hδ ((mem_dual_one_iff e).2 he)
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at hm
    exact hm
  · rw [mul_comm (algebraMap F E t) z, mul_inv_cancel_right₀ htE]
    exact (mem_dual_one_iff z).1 hz

end GlobalTheory.InertDifferentGen
end

section

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def gram2E (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x z : Fin M → E) : E :=
  hE σ J x x * hE σ J z z - hE σ J x z * hE σ J z x

def gram2R (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin M → R ⊗[F] E) : R ⊗[F] E :=
  hR R σ J a a * hR R σ J b b - hR R σ J a b * hR R σ J b a

def IsUnitNorm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R ⊗[F] E) : Prop :=
  ∃ s : R ⊗[F] E, IsUnit s ∧ s * sigR R σ s = a

theorem IsUnitNorm.isUnit {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {a : R ⊗[F] E}
    (h : IsUnitNorm R σ a) : IsUnit a := by
  obtain ⟨s, hs, rfl⟩ := h
  exact hs.mul (hs.map (sigR R σ))

end GlobalTheory.PlaneNorm
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.galois_stable_lattice_rational_span_inclusions : ∀ (K K' L : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L] [Algebra K K'] [IsGalois K K'] [Algebra K' L] (n : ℕ) (M : Submodule (𝓞 K') (Fin n → K')), (∀ (s : K' ≃ₐ[K] K'), ∀ x ∈ M, (fun i => s (x i)) ∈ M) → Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) ≤ Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ∧ (differentIdeal ℤ (𝓞 K')).map (algebraMap (𝓞 K') (𝓞 L)) • Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ≤ Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) := by
  first | exact @GlobalTheory.span_rational_le_span_and_different_smul_le | exact GlobalTheory.span_rational_le_span_and_different_smul_le | (intros; apply GlobalTheory.span_rational_le_span_and_different_smul_le <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.DifferentElement

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

theorem mult_ratio (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (l : ℕ) (hl : l.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsPrime) (hlP : (l : 𝓞 E) ∈ P) :
    (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P (Ideal.span {(l : 𝓞 E)}) : ℚ) =
      ((NumberField.discr E).natAbs.factorization l : ℚ) / (Module.finrank ℚ E : ℚ) := by
  classical
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hd : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E l
    ((NumberField.discr E).natAbs.factorization l) (ordCompl[l] (NumberField.discr E).natAbs) hl
    (Nat.not_dvd_ordCompl hl hd) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm P hP hlP
  have hpos := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos E l hl hP hlP
  simp only [multiplicity_eq_count_normalizedFactors hirr, normalize_eq]
  have hn : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [div_eq_div_iff (by exact_mod_cast hpos.ne') hn]
  convert congrArg (fun t : ℕ => (t : ℚ)) h using 1 <;> push_cast <;> ring

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement


end GlobalTheory.DifferentElement
end
end
