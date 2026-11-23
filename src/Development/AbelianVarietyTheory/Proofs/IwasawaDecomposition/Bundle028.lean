module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle009
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle008
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowers
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle011
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle010
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain

namespace GlobalTheory

noncomputable def unitaryCharToCircle {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) : A →* Circle where
  toFun y := ⟨(a y : ℂ), by simpa [Submonoid.unitSphere] using ha y⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    exact (congrArg (fun u : ℂˣ => (u : ℂ)) (map_mul a x y)).trans (Units.val_mul _ _)

theorem toUnits_unitaryCharToCircle {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) (y : A) :
    Circle.toUnits (unitaryCharToCircle a ha y) = a y := by
  ext
  rfl

private lemma continuous_toUnits_comp {X : Type} [TopologicalSpace X] {f : X → Circle}
    (hf : Continuous f) : Continuous fun x => Circle.toUnits (f x) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val.comp hf, ?_⟩
  have h : (fun x => (((Circle.toUnits (f x))⁻¹ : ℂˣ) : ℂ)) = fun x => (((f x)⁻¹ : Circle) : ℂ) := by
    funext x
    simp
  rw [h]
  exact continuous_subtype_val.comp hf.inv

theorem exists_unitary_char_of_open_subgroup_and_hom :
    ∀ (G A : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup A] (U : Subgroup G), IsOpen (U : Set G) → ∀ (α : A →* G) (a : A →* ℂˣ) (ψ : G →* ℂˣ), Continuous ψ → (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) → (∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) → (∀ y, α y ∈ U → a y = ψ (α y)) → ∃ χ : G →* ℂˣ, Continuous χ ∧ (∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ x ∈ U, χ x = ψ x) ∧ ∀ y, χ (α y) = a y := by
  intro G A _ _ _ _ U hU α a ψ hψc hψ ha hagree
  let _ : TopologicalSpace A := ⊥
  have _ : DiscreteTopology A := ⟨rfl⟩

  set ψ₁ : G →* Circle := unitaryCharToCircle ψ hψ
  set a₁ : A →* Circle := unitaryCharToCircle a ha
  have hψ₁c : Continuous ψ₁ := Continuous.subtype_mk (Units.continuous_val.comp hψc) _
  have hψ₁coe : ∀ x, ((ψ₁ x : Circle) : ℂ) = (ψ x : ℂ) := fun x => rfl
  have ha₁coe : ∀ y, ((a₁ y : Circle) : ℂ) = (a y : ℂ) := fun y => rfl

  let H : Subgroup (G × A) := U.prod ⊤
  have hH : IsOpen (H : Set (G × A)) := by
    simpa [H, Subgroup.coe_prod] using hU.prod isOpen_univ
  let N : Subgroup (G × A) := (MonoidHom.prod α (MonoidHom.id A)).range
  let φ : H →* Circle :=
    ((ψ₁.comp (MonoidHom.fst G A)) / (a₁.comp (MonoidHom.snd G A))).comp H.subtype
  have hφ : ∀ x : H, φ x = ψ₁ (x : G × A).1 / a₁ (x : G × A).2 := fun x => rfl
  have hφc : Continuous φ := by
    have h1 : Continuous fun x : H => ψ₁ (x : G × A).1 :=
      hψ₁c.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : H => a₁ (x : G × A).2 :=
      continuous_of_discreteTopology.comp (continuous_snd.comp continuous_subtype_val)
    have hfun : (φ : H → Circle) = fun x : H => ψ₁ (x : G × A).1 / a₁ (x : G × A).2 := funext hφ
    rw [hfun]
    exact h1.div' h2

  have htriv : ∀ x : H, (x : G × A) ∈ N → φ x = 1 := by
    rintro ⟨x, hxH⟩ ⟨y, rfl⟩
    have hyU : α y ∈ U := (Subgroup.mem_prod.1 hxH).1
    change ψ₁ (α y) / a₁ y = 1
    rw [div_eq_one]
    apply Circle.ext
    rw [hψ₁coe, ha₁coe, hagree y hyU]
  obtain ⟨χ₂, hχ₂c, hχ₂N, hχ₂H⟩ :=
    exists_continuous_circle_char_extension (G × A) H N φ hH hφc htriv

  refine ⟨Circle.toUnits.comp (χ₂.comp (MonoidHom.inl G A)), ?_, ?_, ?_, ?_⟩
  · exact continuous_toUnits_comp (hχ₂c.comp (continuous_id.prodMk continuous_const))
  · intro x
    exact Circle.norm_coe _
  · intro x hx
    have hxH : ((x, 1) : G × A) ∈ H := Subgroup.mem_prod.2 ⟨hx, Subgroup.mem_top 1⟩
    have h : χ₂ (x, 1) = ψ₁ x / a₁ 1 := hχ₂H ⟨(x, 1), hxH⟩
    change Circle.toUnits (χ₂ (x, 1)) = ψ x
    rw [h, map_one, div_one]
    exact toUnits_unitaryCharToCircle ψ hψ x
  · intro y
    have hN : ((α y, y) : G × A) ∈ N := ⟨y, rfl⟩
    have h0 : χ₂ (α y, y) = 1 := hχ₂N _ hN
    have hyH : ((1, y) : G × A) ∈ H := Subgroup.mem_prod.2 ⟨U.one_mem, Subgroup.mem_top y⟩
    have h1 : χ₂ (1, y) = ψ₁ 1 / a₁ y := hχ₂H ⟨(1, y), hyH⟩
    have hsplit : ((α y, y) : G × A) = (α y, 1) * (1, y) :=
      Prod.ext (mul_one _).symm (one_mul _).symm
    rw [hsplit, map_mul, h1, map_one, one_div, mul_inv_eq_one] at h0
    change Circle.toUnits (χ₂ (α y, 1)) = a y
    rw [h0]
    exact toUnits_unitaryCharToCircle a ha y

end GlobalTheory
end

section

open MeasureTheory
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.schur_orthogonality_subgroup_measure_one : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G] (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G), MeasurableSet (Ω : Set G) → ν (Ω : Set G) = 1 → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W), (∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) → (∀ x y : W, Measurable fun g => ⟪x, ρ g y⟫_ℂ) → (∀ U : Submodule ℂ W, (∀ g ∈ Ω, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ a a' x x' : W, IntegrableOn (fun g => star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ) Ω ν ∧ (Module.finrank ℂ W : ℂ) * ∫ g in (Ω : Set G), star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ ∂ν = ⟪a', a⟫_ℂ * ⟪x, x'⟫_ℂ := by
  first | exact @GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality | exact GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality | (intros; apply GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.contDiff_of_continuous_oneParameter_hom : ∀ (A : Type) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (T : ℝ → A), Continuous T → T 0 = 1 → (∀ s t, T (s + t) = T s * T t) → ContDiff ℝ ∞ T := by
  first | exact @GlobalTheory.contDiff_of_continuous_oneParameter | exact GlobalTheory.contDiff_of_continuous_oneParameter | (intros; apply GlobalTheory.contDiff_of_continuous_oneParameter <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ i j, ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by
  first | exact @GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | exact GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | (intros; apply GlobalTheory.inv_entry_norm_le_of_sub_posSemidef <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef → (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  first | exact @GlobalTheory.det_map_ofReal_norm_le | exact GlobalTheory.det_map_ofReal_norm_le | (intros; apply GlobalTheory.det_map_ofReal_norm_le <;> assumption)
end

section

namespace GlobalTheory.CommonReading

open scoped NNReal

section
variable {l : ℕ} [Fact l.Prime] {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]

theorem exists_extend [Module.Finite A B] (hi : Function.Injective (algebraMap A B)) (κ : A →+* ℂ_[l])
    (hκ : Function.Injective κ) :
    ∃ ι : FractionRing B →+* ℂ_[l], ∀ y, ι (algebraMap B (FractionRing B) (algebraMap A B y)) = κ y := by
  let _ : Algebra A ℂ_[l] := κ.toAlgebra
  have hAF : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hi
  have : Module.IsTorsionFree A ℂ_[l] := Module.isTorsionFree_iff_algebraMap_injective.mpr hκ
  have : Module.IsTorsionFree A (FractionRing B) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hAF
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  have : Algebra.IsAlgebraic A (FractionRing B) :=
    (IsFractionRing.isAlgebraic_iff' A B (FractionRing B)).1 inferInstance
  let φ : FractionRing B →ₐ[A] ℂ_[l] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, fun y => ?_⟩
  rw [← IsScalarTower.algebraMap_apply A B (FractionRing B) y]
  exact φ.commutes y

theorem v_le_one [Module.Finite A B] (j : B →+* ℂ_[l]) (hκ : ∀ y, Valued.v (j (algebraMap A B y)) ≤ (1 : ℝ≥0)) (b : B) :
    Valued.v (j b) ≤ (1 : ℝ≥0) := by
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  have hroot : p.eval₂ (j.comp (algebraMap A B)) (j b) = 0 := by
    rw [← Polynomial.hom_eval₂, hp, map_zero]
  by_contra hle
  have hlt := not_le.mp hle
  rw [hpm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hroot
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hroot
  have hxn := eq_neg_of_add_eq_zero_left hroot
  have hn : p.natDegree ≠ 0 := by
    intro h0
    rw [h0] at hxn
    simp at hxn
  have h1 : Valued.v (j b ^ p.natDegree) ≤ Valued.v (j b) ^ (p.natDegree - 1) := by
    rw [hxn, Valuation.map_neg]
    apply Valuation.map_sum_le
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc Valued.v ((j.comp (algebraMap A B)) (p.coeff i)) * Valued.v (j b) ^ i
        ≤ 1 * Valued.v (j b) ^ (p.natDegree - 1) :=
          mul_le_mul' (hκ _) (pow_le_pow_right₀ hlt.le (by omega))
      _ = _ := one_mul _
  rw [map_pow] at h1
  have h2 : Valued.v (j b) ^ (p.natDegree - 1) < Valued.v (j b) ^ p.natDegree :=
    pow_lt_pow_right₀ hlt (by omega)
  exact absurd h1 (not_le.mpr h2)

theorem mem_range_iff [IsDiscreteValuationRing B] (ι : FractionRing B →+* ℂ_[l])
    (h : ∀ b, Valued.v (ι (algebraMap B (FractionRing B) b)) ≤ (1 : ℝ≥0)) (x : FractionRing B) :
    x ∈ (algebraMap B (FractionRing B)).range ↔ Valued.v (ι x) ≤ (1 : ℝ≥0) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact h b
  · intro hx
    by_contra hxn
    set φ : B →+* ℂ_[l] := ι.comp (algebraMap B (FractionRing B)) with hφ
    have hφ1 : ∀ b, Valued.v (φ b) ≤ (1 : ℝ≥0) := fun b => h b
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxn (RingHom.mem_range.mpr ⟨0, map_zero _⟩)
    obtain ⟨b, hb⟩ : ∃ b, algebraMap B (FractionRing B) b = x⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger B x with h1 | h1
      · exact absurd (RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h1)) hxn
      · exact RingHom.mem_rangeS.mp h1
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact hx0 (inv_eq_zero.mp hb.symm)
    have hbu : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      apply hxn
      refine RingHom.mem_range.mpr ⟨(↑u⁻¹ : B), ?_⟩
      rw [map_units_inv, hb, inv_inv]
    have hl1 : Valued.v ((l : ℕ) : ℂ_[l]) < 1 := by
      rw [PadicComplex.valuation_p, one_div]
      have : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      exact inv_lt_one_of_one_lt₀ this
    have hl0 : ((l : ℕ) : B) ≠ 0 := by
      intro h0
      have h2 : φ ((l : ℕ) : B) = 0 := by rw [h0, map_zero]
      rw [map_natCast] at h2
      exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h2
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hbu (hk.symm.isUnit (by simp))
    have hdvd : ((l : ℕ) : B) ∣ b ^ n := by
      have h2 : ϖ ^ n ∣ ϖ ^ (k * n) :=
        pow_dvd_pow ϖ (by have := Nat.pos_of_ne_zero hk0; nlinarith)
      have h3 : ϖ ^ (k * n) ∣ b ^ n := by
        rw [pow_mul]
        exact (hk.pow_pow (n := n)).symm.dvd
      exact hn.dvd.trans (h2.trans h3)
    obtain ⟨c, hc⟩ := hdvd
    have hvb : Valued.v (φ b) < 1 := by
      by_contra hlt'
      have hge := not_lt.mp hlt'
      have h1 : 1 ≤ Valued.v (φ b) ^ n := one_le_pow₀ hge
      rw [← map_pow Valued.v, ← map_pow φ, hc, map_mul, map_mul, map_natCast] at h1
      exact absurd h1 (not_le.mpr (mul_lt_one_of_nonneg_of_lt_one_left (by positivity) hl1 (hφ1 c)))
    have h1 : Valued.v (ι x) * Valued.v (φ b) = 1 := by
      rw [← map_mul]
      have h3 : ι x * φ b = 1 := by
        show ι x * ι (algebraMap B (FractionRing B) b) = 1
        rw [← map_mul, hb, mul_inv_cancel₀ hx0, map_one]
      rw [h3, map_one]
    exact absurd h1 (ne_of_lt (mul_lt_one_of_nonneg_of_lt_one_right hx (by positivity) hvb))

end

theorem exists_factor {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] (g : L →+* ℂ_[l]) :
    ∃ e : L →+* PadicAlgCl l, ∀ x, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = g x := by
  have hmem : ∀ x : L, g x ∈ (algebraMap (PadicAlgCl l) ℂ_[l]).range := by
    intro x
    obtain ⟨f, hf0, hf⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x
    have hg : (f.map (algebraMap ℚ ℂ_[l])).eval (g x) = 0 := by
      have h1 : g (Polynomial.eval₂ (algebraMap ℚ L) x f) = 0 := by
        rw [← Polynomial.aeval_def, hf, map_zero]
      rw [Polynomial.hom_eval₂] at h1
      rw [Polynomial.eval_map]
      have e : g.comp (algebraMap ℚ L) = algebraMap ℚ ℂ_[l] := RingHom.ext_rat _ _
      rwa [e] at h1
    have hsplit : (f.map (algebraMap ℚ (PadicAlgCl l))).Splits := IsAlgClosed.splits _
    have hP0 : f.map (algebraMap ℚ (PadicAlgCl l)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ (PadicAlgCl l)).injective).mpr hf0
    have hmap : f.map (algebraMap ℚ ℂ_[l]) =
        (f.map (algebraMap ℚ (PadicAlgCl l))).map (algebraMap (PadicAlgCl l) ℂ_[l]) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_rat _ _
    have hroot : g x ∈ ((f.map (algebraMap ℚ (PadicAlgCl l))).map (algebraMap (PadicAlgCl l) ℂ_[l])).roots := by
      rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff (algebraMap (PadicAlgCl l) ℂ_[l]).injective).mpr hP0)]
      show Polynomial.eval _ _ = 0
      rw [← hmap]
      exact hg
    rw [hsplit.roots_map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, Multiset.mem_map] at hroot
    obtain ⟨β, -, hβ⟩ := hroot
    exact RingHom.mem_range.mpr ⟨β, hβ⟩
  have hr : Function.Bijective (algebraMap (PadicAlgCl l) ℂ_[l]).rangeRestrict :=
    ⟨fun a b hab => (algebraMap (PadicAlgCl l) ℂ_[l]).injective (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  let E := RingEquiv.ofBijective _ hr
  refine ⟨E.symm.toRingHom.comp (g.codRestrict _ hmem), fun x => ?_⟩
  exact congrArg Subtype.val (E.apply_symm_apply (g.codRestrict _ hmem x))

theorem exists_common {l : ℕ} [Fact l.Prime] {A B L : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] (hi : Function.Injective (algebraMap A B))
    (κ : A →+* ℂ_[l]) (hκ : Function.Injective κ) (hv : ∀ y, Valued.v (κ y) ≤ (1 : ℝ≥0))
    [Field L] [NumberField L] (eB : L →+* FractionRing B) (e : L →+* PadicAlgCl l)
    (he : ∀ x, eB x ∈ (algebraMap B (FractionRing B)).range ↔ ‖e x‖ ≤ 1) :
    ∃ (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (ι : FractionRing B →+* ℂ_[l]),
      (∀ y, ι (algebraMap B (FractionRing B) (algebraMap A B y)) = κ y) ∧
      ∀ x, ι (eB x) = algebraMap (PadicAlgCl l) ℂ_[l] (σ (e x)) := by
  obtain ⟨ι, hι⟩ := exists_extend hi κ hκ
  have hB : ∀ b, Valued.v (ι (algebraMap B (FractionRing B) b)) ≤ (1 : ℝ≥0) := by
    intro b
    refine v_le_one (A := A) (ι.comp (algebraMap B (FractionRing B))) (fun y => ?_) b
    rw [RingHom.comp_apply, hι]
    exact hv y
  obtain ⟨e', he'⟩ := exists_factor (ι.comp eB)
  have hcond : ∀ x, ‖e x‖ ≤ 1 ↔ ‖e' x‖ ≤ 1 := by
    intro x
    rw [← he x, mem_range_iff ι hB, ← RingHom.comp_apply ι eB, ← he' x, ← PadicComplex.coe_eq,
      PadicComplex.valuation_extends, PadicAlgCl.valuation_def, ← NNReal.coe_le_coe, coe_nnnorm,
      NNReal.coe_one]
  obtain ⟨σ, hσ⟩ := GlobalTheory.EmbUnitBallConj.exists_conj l L e e' hcond
  refine ⟨σ, ι, hι, fun x => ?_⟩
  rw [hσ, he']
  rfl

end GlobalTheory.CommonReading
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : PadicAlgCl l), IsIntegral ℚ_[l] ζ → ∃ (n : ℕ) (C : ℝ), ∀ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))), ‖x‖ ≤ 1 → ∃ c : Fin n → ℂ_[l], (∀ i, c i ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖c i‖ ≤ C) ∧ x = ∑ i, c i * (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (i : ℕ) := by
  first | exact @GlobalTheory.closure_adjoin_unitBall_coeff_bound | exact GlobalTheory.closure_adjoin_unitBall_coeff_bound | (intros; apply GlobalTheory.closure_adjoin_unitBall_coeff_bound <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂] (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂), (∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) → (∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ N₂ x) → (∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) → (∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y) → (∀ x, N₂ (Δ x) ≤ N₁ x) → (∀ x y, N₂ (i x * j y) = N₁ x * N₁ y) → ∀ y : B₁, (∃ K : ℝ, ∀ k : ℕ, N₁ (y ^ k) ≤ K) → N₂ (Δ y - i y - j y) ≤ 1 → ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → N₁ (a • y) ≤ 1 := by
  first | exact @GlobalTheory.NearlyPrimitive.norm_smul_le_one | exact GlobalTheory.NearlyPrimitive.norm_smul_le_one | (intros; apply GlobalTheory.NearlyPrimitive.norm_smul_le_one <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.finiteDimensional_ker_aeval_of_eigenspaces' : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M), (∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) → ∀ p : Polynomial ℂ, p ≠ 0 → FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  first | exact @GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces | exact GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces | (intros; apply GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.unitriangular_induction_on_transvections : ∀ (n : ℕ) (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) → (∀ (i j : Fin n), i < j → ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s → P B) → ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → P U := by
  first | exact @GlobalTheory.unitriangular_induction_transvection | exact GlobalTheory.unitriangular_induction_transvection | (intros; apply GlobalTheory.unitriangular_induction_transvection <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.GL_upperTriangular_eq_diagonal_mul_unitriangular' : ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ, B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧ U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  first | exact @GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular | exact GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular | (intros; apply GlobalTheory.GL_upperTriangular_eq_diagonal_mul_unitriangular <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.schur_complement_block_quadratic_lower_bound : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z := by
  first | exact @GlobalTheory.schur_block_lower_bound | exact GlobalTheory.schur_block_lower_bound | (intros; apply GlobalTheory.schur_block_lower_bound <;> assumption)
end
