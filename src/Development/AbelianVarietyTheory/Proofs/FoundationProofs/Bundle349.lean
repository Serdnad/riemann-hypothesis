module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.CoefJoin

theorem isIntegral_iff_norm_le {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem coef_of_finite : ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (Qbar l)), FiniteDimensional ℚ_[l] E →
    ∃ c : Coef l, ∀ x : Qbar l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  intro l _ E hE
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E
  let f : E →ₐ[ℤ_[l]] PadicAlgCl l := E.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] E).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, ?_⟩
  intro x
  have hn := fun y : E => isIntegral_iff_norm_le (l := l) E.val y
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (hn y).1 hy⟩
  · rintro ⟨hx, hle⟩
    exact ⟨⟨x, hx⟩, (hn ⟨x, hx⟩).2 hle, rfl⟩

end GlobalTheory.CoefJoin
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Coef.norm_le_norm_pow_iff_dvd :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O),
      ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  intro l _ c n x
  have hlnorm : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  obtain ⟨-, -, -, -, -, he0, -, he, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have key := UpperTheory.V.Base.normO l c.O x hx
  set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def
  have hEtop : UpperTheory.V.Base.eO l c.O ≠ ⊤ := by
    rw [he]; exact fun h => hl0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have hEcast : UpperTheory.V.Base.eO l c.O = (e : ℕ∞) := (ENat.coe_toNat hEtop).symm
  have hepos : e ≠ 0 := by
    intro h0; apply he0; rw [hEcast, h0]; rfl
  have hxtop : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ :=
    fun h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def
  have hvcast : IsDiscreteValuationRing.addVal c.O x = (v : ℕ∞) := (ENat.coe_toNat hxtop).symm
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hllt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : l.Prime).one_lt)
  rw [norm_pow, hlnorm, ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    ← he, hEcast, hvcast, ← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hepos, key, ← pow_mul,
    pow_le_pow_iff_right_of_lt_one₀ hlpos hllt]
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.CycIndex

theorem nsmul_mem_span_of_card_le : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (C r : ℕ), ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (H : Type) [AddCommGroup H] [Module c.O H] [Finite H], (∀ h : H, ((l : ℕ) : c.O) ^ n • h = 0) → Nat.card H ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) → ∀ z : H, (∀ x : c.O, x • z = 0 → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ h : H, ∃ x : c.O, m • h = x • z := by
  intro l _ c C r
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hfin : ∀ k : ℕ, Finite (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ k)) := fun k =>
    (UpperTheory.V.X.So.levFacts l c.O _ (pow_ne_zero k hl0) _ ⟨LinearEquiv.refl _ _⟩).1
  refine ⟨(C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ r))).factorial, Nat.factorial_pos _, ?_⟩
  intro n H _ _ _ hkill hcard z hann h
  set L : c.O := ((l : ℕ) : c.O) with hL
  haveI := hfin n
  haveI := hfin r
  let f : UpperTheory.V.X.Lev (L ^ n) →ₗ[c.O] H :=
    (Ideal.span {L ^ n}).liftQ (LinearMap.toSpanSingleton c.O H z) (by
      rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hkill z)
  have hf : ∀ x : c.O, f (UpperTheory.V.X.Lev.mk (L ^ n) x) = x • z := fun x => rfl
  let g : UpperTheory.V.X.Lev (L ^ r) →ₗ[c.O] UpperTheory.V.X.Lev (L ^ n) :=
    (Ideal.span {L ^ r}).liftQ ((L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n)) (by
      rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul,
        UpperTheory.V.X.Lev.mk_eq_zero, smul_eq_mul, ← pow_add]
      exact pow_dvd_pow _ (by omega))
  have hg : ∀ w : c.O, g (UpperTheory.V.X.Lev.mk (L ^ r) w) = UpperTheory.V.X.Lev.mk (L ^ n) (L ^ (n - r) * w) := by
    intro w
    show (L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n) w = _
    rw [← map_smul, smul_eq_mul]
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro y hy
    obtain ⟨x, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective (L ^ n) y
    rw [LinearMap.mem_ker, hf] at hy
    obtain ⟨w, rfl⟩ := hann x hy
    exact ⟨UpperTheory.V.X.Lev.mk (L ^ r) w, hg w⟩
  have hK : Nat.card (LinearMap.ker f) ≤ Nat.card (UpperTheory.V.X.Lev (L ^ r)) :=
    (Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hker)).trans
      (Nat.card_le_card_of_surjective _ g.surjective_rangeRestrict)
  have h1 : Nat.card (UpperTheory.V.X.Lev (L ^ n)) =
      Nat.card (LinearMap.ker f) * Nat.card (UpperTheory.V.X.Lev (L ^ n) ⧸ LinearMap.ker f) :=
    Submodule.card_eq_card_quotient_mul_card _
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have h2 : Nat.card H = Nat.card (LinearMap.range f) * Nat.card (H ⧸ LinearMap.range f) :=
    Submodule.card_eq_card_quotient_mul_card _
  have hSpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have hQ : Nat.card (H ⧸ LinearMap.range f) ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ r)) := by
    have : Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) ≤
        (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))) * Nat.card (LinearMap.range f) := by
      calc Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) = Nat.card H := by
              rw [h2, mul_comm]
        _ ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ n)) := hcard
        _ = C * (Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f)) := by rw [h1]
        _ ≤ C * (Nat.card (UpperTheory.V.X.Lev (L ^ r)) * Nat.card (LinearMap.range f)) := by gcongr
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hSpos
  haveI : Finite (H ⧸ LinearMap.range f) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hdvd : Nat.card (H ⧸ LinearMap.range f) ∣ (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial :=
    Nat.dvd_factorial Nat.card_pos hQ
  obtain ⟨k, hk⟩ := hdvd
  have hmem : (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial • h ∈ LinearMap.range f := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_nsmul, hk, mul_comm, mul_nsmul,
      card_nsmul_eq_zero']
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨x, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective (L ^ n) y
  exact ⟨x, by rw [← hy, hf]⟩

end GlobalTheory.CycIndex
end
end
