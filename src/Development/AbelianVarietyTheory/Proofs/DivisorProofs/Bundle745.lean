module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterEqOneCayleyRotation
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Trace
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.JointShapeUniq

theorem length_pad {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) :
    (pad x (n - x.length - y.length) y).length = n := by
  simp [pad]; omega

theorem ofFn_getD {L : List ℚ} {n : ℕ} (h : L.length = n) :
    List.ofFn (fun i : Fin n => L.getD i 0) = L := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem h2]

theorem filter_pos {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) (k : ℕ) :
    (x ++ List.replicate k 0 ++ y).filter (fun v => decide (0 < v)) = x := by
  rw [List.filter_append, List.filter_append, List.filter_eq_self.2 (by simpa using hx),
    List.filter_eq_nil_iff.2 (by simp),
    List.filter_eq_nil_iff.2 (fun v hv => by have := hy v hv; simp; omega)]
  simp

theorem filter_neg {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) (k : ℕ) :
    (x ++ List.replicate k 0 ++ y).filter (fun v => decide (v < 0)) = y := by
  rw [List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.2 (fun v hv => by have := hx v hv; simp; omega),
    List.filter_eq_nil_iff.2 (by simp), List.filter_eq_self.2 (by simpa using hy)]
  simp

theorem pad_inj {x y x' y' : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0)
    (hx' : ∀ v ∈ x', 0 < v) (hy' : ∀ v ∈ y', v < 0) {n : ℕ}
    (h : x.length + y.length ≤ n) (h' : x'.length + y'.length ≤ n)
    (e : ∀ i : Fin n, (pad x (n - x.length - y.length) y).getD i 0 =
      (pad x' (n - x'.length - y'.length) y').getD i 0) : x = x' ∧ y = y' := by
  have e1 : pad x (n - x.length - y.length) y = pad x' (n - x'.length - y'.length) y' := by
    rw [← ofFn_getD (length_pad h), ← ofFn_getD (length_pad h'), funext e]
  have e2 := List.map_injective_iff.2 (Int.cast_injective (α := ℚ)) e1
  exact ⟨by rw [← filter_pos hx hy, e2, filter_pos hx' hy'],
    by rw [← filter_neg hx hy, e2, filter_neg hx' hy']⟩

def absSum (x : List ℤ) : ℚ := (x.map fun v : ℤ => |(v : ℚ)|).sum

theorem sum_abs_pad {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) :
    ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| = absSum x + absSum y := by
  have : ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| =
      ((pad x (n - x.length - y.length) y).map fun v => |v|).sum := by
    conv_rhs => rw [← ofFn_getD (length_pad h), List.map_ofFn, List.sum_ofFn]
    rfl
  rw [this]
  simp [pad, absSum, Function.comp_def]

theorem shiftNu_injective {p q : ℕ} (c : ℚ) :
    Function.Injective (shiftNu (p := p) (q := q) c) := by
  intro μ μ₁ h
  funext a
  have := congrFun h a
  rcases a with a | a <;> simpa [shiftNu] using this

theorem jointShape_unique_deg : ∀ (p q r s : ℕ) (μ μ₁ : Ix p q → ℚ) (μ' μ₁' : Ix r s → ℚ),
    JointShape p q r s μ μ' → JointShape p q r s μ₁ μ₁' →
      (μ = μ₁ ↔ μ' = μ₁') ∧ degW (cPair r s) μ = degW (cPair p q) μ' := by
  intro p q r s μ μ₁ μ' μ₁' h h₁
  obtain ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, e1, e2⟩ := h
  obtain ⟨a', b', c', d', ha', hc', hb', hd', -, -, -, -, l1', l2', l3', l4', e1', e2'⟩ := h₁
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · subst h
    have e := e1.symm.trans e1'
    obtain ⟨rfl, rfl⟩ := pad_inj ha hb ha' hb' l1 l1' fun i => congrFun e (.inl i)
    obtain ⟨rfl, rfl⟩ := pad_inj hc hd hc' hd' l2 l2' fun i => congrFun e (.inr i)
    exact shiftNu_injective _ (e2.trans e2'.symm)
  · subst h
    have e := e2.symm.trans e2'
    obtain ⟨rfl, rfl⟩ := pad_inj ha hd ha' hd' l3 l3' fun i => congrFun e (.inl i)
    obtain ⟨rfl, rfl⟩ := pad_inj hc hb hc' hb' l4 l4' fun i => congrFun e (.inr i)
    exact shiftNu_injective _ (e1.trans e1'.symm)
  · simp only [degW, e1, e2, Fintype.sum_sum_type, ofBlocks]
    rw [sum_abs_pad l1, sum_abs_pad l2, sum_abs_pad l3, sum_abs_pad l4]
    ring

end GlobalTheory.JointShapeUniq
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial MeasureTheory

namespace GlobalTheory.SchurPol

theorem polarise_integral {G H : Type*} [MeasurableSpace G] [AddCommGroup H] [Module ℂ H]
    (μ : Measure G) (F : H → H → G → ℂ) (R : H → H → ℂ) (c : ℂ)
    (hF : ∀ x y g, F x y g = (1 / 4 : ℂ) * ((F (x + y) (x + y) g - F (x - y) (x - y) g) +
      c * (F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g)))
    (hR : ∀ x y, R x y = (1 / 4 : ℂ) * ((R (x + y) (x + y) - R (x - y) (x - y)) +
      c * (R (x + Complex.I • y) (x + Complex.I • y) -
        R (x - Complex.I • y) (x - Complex.I • y))))
    (hd : ∀ x, Integrable (F x x) μ ∧ ∫ g, F x x g ∂μ = R x x) (x y : H) :
    Integrable (F x y) μ ∧ ∫ g, F x y g ∂μ = R x y := by
  have e : F x y = fun g => (1 / 4 : ℂ) * ((F (x + y) (x + y) g - F (x - y) (x - y) g) +
      c * (F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g)) := funext (hF x y)
  have h1 : Integrable (fun g => F (x + y) (x + y) g - F (x - y) (x - y) g) μ :=
    (hd _).1.sub (hd _).1
  have h2 : Integrable (fun g => F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g) μ := (hd _).1.sub (hd _).1
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (h1.add (h2.const_mul c)).const_mul _
  · rw [hR x y]
    simp only [hF x y]
    rw [integral_const_mul, integral_add h1 (h2.const_mul c), integral_const_mul,
      integral_sub (hd _).1 (hd _).1, integral_sub (hd _).1 (hd _).1,
      (hd _).2, (hd _).2, (hd _).2, (hd _).2]

theorem schur_half {p q : ℕ} {T : GrpData p q} (D : DSRep T) (w u₁ u₂ : D.U.H) :
    Integrable (fun g => inner ℂ w (D.U.π g u₁) * star (inner ℂ w (D.U.π g u₂))) T.haar ∧
      ∫ g, inner ℂ w (D.U.π g u₁) * star (inner ℂ w (D.U.π g u₂)) ∂T.haar =
        ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ w w) := by
  refine polarise_integral T.haar
    (fun x y g => inner ℂ w (D.U.π g x) * star (inner ℂ w (D.U.π g y)))
    (fun x y => ((D.fdeg : ℂ))⁻¹ * inner ℂ y x * star (inner ℂ w w)) Complex.I ?_ ?_ ?_ u₁ u₂
  · intro x y g
    simp only [map_add (f := _), map_sub, map_smul, inner_add_right, inner_sub_right, inner_smul_right,
      star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * (inner ℂ w (D.U.π g x) * (starRingEnd ℂ) (inner ℂ w (D.U.π g y))
      - inner ℂ w (D.U.π g y) * (starRingEnd ℂ) (inner ℂ w (D.U.π g x))) * Complex.I_mul_I
  · intro x y
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, inner_sub_left,
      inner_smul_left, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * ((D.fdeg : ℂ))⁻¹ * star (inner ℂ w w) *
      (inner ℂ y x - inner ℂ x y) * Complex.I_mul_I
  · intro x
    have e : ∀ g, inner ℂ w (D.U.π g x) * star (inner ℂ w (D.U.π g x)) =
        ((‖inner ℂ w (D.U.π g x)‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e]
    refine ⟨(D.schur x w).1.ofReal, ?_⟩
    rw [integral_complex_ofReal, (D.schur x w).2, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K]
    simp only [Complex.star_def, map_pow, Complex.coe_algebraMap, Complex.conj_ofReal]
    push_cast
    ring

theorem schur_polarised (p q : ℕ) (T : GrpData p q) (D : DSRep T) (u₁ w₁ u₂ w₂ : D.U.H) :
    Integrable (fun g => inner ℂ w₁ (D.U.π g u₁) * star (inner ℂ w₂ (D.U.π g u₂))) T.haar ∧
      ∫ g, inner ℂ w₁ (D.U.π g u₁) * star (inner ℂ w₂ (D.U.π g u₂)) ∂T.haar =
        ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ w₂ w₁) := by
  refine polarise_integral T.haar
    (fun x y g => inner ℂ x (D.U.π g u₁) * star (inner ℂ y (D.U.π g u₂)))
    (fun x y => ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ y x)) (-Complex.I) ?_ ?_
    (fun x => schur_half D x u₁ u₂) w₁ w₂
  · intro x y g
    simp only [inner_add_left, inner_sub_left, inner_smul_left, map_add (f := _), map_sub, map_mul, map_neg,
      star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I, neg_neg]
    linear_combination (1 / 2 : ℂ) *
      (inner ℂ x (D.U.π g u₁) * (starRingEnd ℂ) (inner ℂ y (D.U.π g u₂))
      - inner ℂ y (D.U.π g u₁) * (starRingEnd ℂ) (inner ℂ x (D.U.π g u₂))) * Complex.I_mul_I
  · intro x y
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, inner_sub_left,
      inner_smul_left, Complex.conj_I, Complex.star_def, map_add, map_sub, map_mul, map_neg,
      neg_neg]
    linear_combination (1 / 2 : ℂ) * ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ *
      ((starRingEnd ℂ) (inner ℂ y x) - (starRingEnd ℂ) (inner ℂ x y)) * Complex.I_mul_I

end GlobalTheory.SchurPol
end

section

open scoped Matrix
open Formalism.BasicNotions.TH

theorem _root_.GlobalTheory.T.indefiniteUnitaryCharacter_maximalCompact_det_pow : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∃ x y : ℤ, ∀ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ), aᴴ * a = 1 → dᴴ * d = 1 →
      χ (Matrix.fromBlocks a 0 0 d) = a.det ^ x * d.det ^ y := by
  first | exact @GlobalTheory.KChar.kchar | exact GlobalTheory.KChar.kchar | (intros; apply GlobalTheory.KChar.kchar <;> assumption)
end

section

open scoped Matrix
open Formalism.BasicNotions.TH

theorem _root_.GlobalTheory.T.indefiniteUnitaryCharacter_eq_one_cayleyRotation : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∀ (i0 : Fin R) (j0 : Fin S) (x : ℝ),
      χ (Matrix.fromBlocks (Matrix.diagonal (Function.update 1 i0 ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)))) 0 0
        (Matrix.diagonal (Function.update 1 j0 ((1 - 2 * Complex.I * x) / (1 + 2 * Complex.I * x))))) = 1 := by
  first | exact @GlobalTheory.UnitaryCharRot.char_eq_one_rot | exact GlobalTheory.UnitaryCharRot.char_eq_one_rot | (intros; apply GlobalTheory.UnitaryCharRot.char_eq_one_rot <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Host

namespace GlobalTheory.MuConj

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_involutive (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

noncomputable def starAlg (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : E ≃ₐ[F] E :=
  { (starRingAut : E ≃+* E) with commutes' := hF }

theorem mem_above_iff (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P ≠ P) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = P.under (𝓞 F) ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  have hc : starAlg hF ≠ 1 := by
    intro h
    apply hP
    ext x
    have e : cO E x = x := by
      apply RingOfIntegers.ext
      exact congrArg (fun σ : E ≃ₐ[F] E => σ (x : E)) h
    rw [mem_conjP, e]
  rw [GlobalTheory.Mem.Chr.under_eq_iff_conjPl (starAlg hF) hr hc P Q, GlobalTheory.Mem.Chr.conjPl_iff_mem]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · ext y
    rw [mem_conjP]
    refine (h (cO E y) y ?_).symm
    exact (star_star (y : E)).symm
  · subst h
    intro x y hxy
    have e : y = cO E x := RingOfIntegers.ext hxy
    rw [e, mem_conjP, cO_cO]


omit [StarRing E] in
theorem valuation_up (Q : HeightOneSpectrum (𝓞 E))
    (h : ¬ (Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q.asIdeal ^ 2) (x : F) :
    Q.valuation E (algebraMap F E x) = (Q.under (𝓞 F)).valuation F x := by
  have : Q.asIdeal.LiesOver (Q.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have he : Ideal.ramificationIdx' (Q.under (𝓞 F)).asIdeal Q.asIdeal = 1 := by
    by_contra hne
    exact h ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hne)
  rw [← HeightOneSpectrum.valuation_liesOver E (Q.under (𝓞 F)) Q,
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Q.under (𝓞 F)).ne_bot, he, pow_one]

end General

theorem mem_divs_of_mem {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) {P : HeightOneSpectrum A}
    (h : a ∈ P.asIdeal) : P ∈ divs a := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h1 := Ideal.finite_factors (I := Ideal.span {a}) (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha)
    refine h1.subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  unfold divs
  rw [dite_eq_left hfin, Set.Finite.mem_toFinset]
  exact h

theorem g_notMem {X : Fields} {Pr : Primes X} (h : Pr.Ok) (P : HeightOneSpectrum (𝓞 X.E)) (h1 : P ∉ Pr.vGs)
    (h2 : conjPrime₂ P ∉ Pr.vGs) (i : Fin 2) : ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  have hg : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (h.g_prime i).ne_zero
  rw [← h.piG_norm i] at hm hg
  have hsub : ∀ Q, Q ∈ Pr.vG i → Q ∈ Pr.vGs := by
    intro Q hQ
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases i
    · exact Or.inl hQ
    · exact Or.inr hQ
  have hne : X.conjO (Pr.piG i) ≠ 0 := right_ne_zero_of_mul hg
  rcases P.isPrime.mem_or_mem hm with h3 | h3
  · refine h2 (hsub _ (mem_divs_of_mem hne ?_))
    show cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal
    rw [cO_cO]
    exact h3
  · exact h1 (hsub _ (mem_divs_of_mem hne h3))

end GlobalTheory.MuConj
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.LatOfMult

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → (∀ a : 𝓞 K, MulStable Λ (ι a)) ∧ MulStable Λ (ι δ) ∧ (ι δ).im ≠ 0 ∧ IsIntegral ℤ δ := by
  intro K _ _ d δ ι 𝔞 Λ hd hδ hL
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ x ∈ (𝔞 : Set K), ι x = z := by
    intro z
    have := congrArg (fun S : Set ℂ => z ∈ S) hL
    simpa using this
  have hstab : ∀ a : 𝓞 K, MulStable Λ (ι a) := by
    intro a ω hω
    obtain ⟨x, hx, rfl⟩ := (hmem ω).1 hω
    refine (hmem _).2 ⟨(a : K) * x, ?_, by simp⟩
    have h1 : a • x ∈ (𝔞 : Submodule (𝓞 K) K) := Submodule.smul_mem _ a hx
    rwa [Algebra.smul_def] at h1
  have hint : IsIntegral ℤ δ := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hδ]
  refine ⟨hstab, ?_, ?_, hint⟩
  · exact hstab ⟨δ, hint⟩
  · intro him
    have h2 : (ι δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
    have h3 := congrArg Complex.re h2
    simp [pow_two, Complex.mul_re, him] at h3
    have : (0:ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg (ι δ).re]

end GlobalTheory.LatOfMult
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IntLatMul

theorem main : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  intro d Λ hd hΛ
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwi : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast, hw2]
    ring
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxi, a, b, hab⟩ := (hΛ x).1 hx
    refine (hΛ _).2 ⟨hwi.mul hxi, -(b * d), a, ?_⟩
    rw [hab]
    push_cast
    linear_combination (b : ℂ) * hw2
  · have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    simp [hw, hs.ne']

end GlobalTheory.IntLatMul
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem finrank_range_mulLeft_idem : ∀ (K H : Type) [Field K] [CharZero K] [Group H] [Finite H] (a : MonoidAlgebra K H), a * a = a → ((finrank K (LinearMap.range (LinearMap.mulLeft K a)) : ℕ) : K) = (Nat.card H : K) * a.coeff 1 := by
  intro K H _ _ _ _ a ha
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hi : IsIdempotentElem (LinearMap.mulLeft K a) := by
    change LinearMap.mulLeft K a * LinearMap.mulLeft K a = LinearMap.mulLeft K a
    refine LinearMap.ext fun x => ?_
    change a * (a * x) = a * x
    rw [← mul_assoc, ha]
  rw [← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace]
  rw [LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis H K), Matrix.trace]
  have h : ∀ g : H, Matrix.diag (LinearMap.toMatrix (MonoidAlgebra.basis H K)
      (MonoidAlgebra.basis H K) (LinearMap.mulLeft K a)) g = a.coeff 1 := by
    intro g
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
      LinearMap.mulLeft_apply]
    change (a * MonoidAlgebra.single g 1).coeff g = a.coeff 1
    rw [MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  rw [Finset.sum_congr rfl (fun g _ => h g), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

end GlobalTheory.BadCount
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.exists_map_comap_inf_sup_pow_eq : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by
  first | exact @GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq | exact GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq | (intros; apply GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧ IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | exact GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | (intros; apply GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field <;> assumption)
end
