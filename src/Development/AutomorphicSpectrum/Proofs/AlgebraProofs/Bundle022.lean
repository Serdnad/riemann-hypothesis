module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle002
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle007
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_valuationSubring_of_padicEmbedding :
    ∀ (F : IntermediateField ℚ ℂ) (p : Nat.Primes) (κ : F →+* ℂ_[p]),
      ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧
        ∀ x : F, ‖κ x‖ ≤ 1 ↔ (x : ℂ) ∈ W := by
  intro F p κ
  have hna : ∀ a b : ℂ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := fun a b =>
    IsUltrametricDist.norm_add_le_max a b
  have hone : ‖κ 1‖ = 1 := by simp
  let A : Subring ℂ :=
    { carrier := {a | ∃ x : F, (x : ℂ) = a ∧ ‖κ x‖ ≤ 1}
      mul_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x * y, by simp, ?_⟩
        rw [map_mul, norm_mul]
        exact mul_le_one₀ hx (norm_nonneg _) hy
      one_mem' := ⟨1, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x + y, by simp, ?_⟩
        rw [map_add (f := _)]
        exact (hna _ _).trans (max_le hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      neg_mem' := by
        rintro _ ⟨x, rfl, hx⟩
        exact ⟨-x, by simp, by simpa using hx⟩ }
  let I : Ideal A :=
    { carrier := {a | ∃ x : F, (x : ℂ) = (a : ℂ) ∧ ‖κ x‖ < 1}
      add_mem' := by
        rintro a b ⟨x, hxa, hx⟩ ⟨y, hyb, hy⟩
        refine ⟨x + y, by simp [hxa, hyb], ?_⟩
        rw [map_add (f := _)]
        exact (hna _ _).trans_lt (max_lt hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      smul_mem' := by
        rintro ⟨c, z, hzc, hz⟩ a ⟨x, hxa, hx⟩
        refine ⟨z * x, by simp [hzc, hxa], ?_⟩
        rw [map_mul, norm_mul]
        calc ‖κ z‖ * ‖κ x‖ ≤ 1 * ‖κ x‖ := by gcongr
          _ < 1 := by simpa using hx }
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := by rw [htop]; trivial
    obtain ⟨x, hx1, hx⟩ := h1
    have hx1' : x = 1 := by
      apply Subtype.ext
      simpa using hx1
    rw [hx1', hone] at hx
    exact lt_irrefl _ hx
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have key : ∀ x : F, ‖κ x‖ < 1 → (x : ℂ) ∈ W.nonunits := by
    intro x hx
    have hxA : (x : ℂ) ∈ A := ⟨x, rfl, hx.le⟩
    exact hIW ⟨⟨(x : ℂ), hxA⟩, ⟨x, rfl, hx⟩, rfl⟩
  refine ⟨W, ?_, fun x => ⟨fun hx => hAW ⟨x, rfl, hx⟩, fun hxW => ?_⟩⟩
  · have hnorm : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
      rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
        ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
        Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
    have := key ((p : ℕ) : F) (by simpa using hnorm)
    simpa using this
  · by_contra hlt
    have hlt' : 1 < ‖κ x‖ := not_le.mp hlt
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hlt'
      linarith
    have hinv : ‖κ x⁻¹‖ < 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_lt_one_of_one_lt₀ hlt'
    have hnu := key x⁻¹ hinv
    rw [ValuationSubring.mem_nonunits_iff] at hnu
    have hle : W.valuation (x : ℂ) ≤ 1 := (W.valuation_le_one_iff _).2 hxW
    have hprod : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) = 1 := by
      rw [← map_mul]
      have : (x : ℂ) * ((x⁻¹ : F) : ℂ) = 1 := by
        have h0 : (x : ℂ) ≠ 0 := by simpa using hx0
        simp [h0]
      rw [this, map_one]
    have : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hle) hnu
    exact absurd hprod this.ne

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.padic_integral_iff_denominator : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (x : E), ((∀ j : E →+* ℂ_[p], ‖j x‖ ≤ 1) ↔ ∃ (n : ℕ) (a : 𝓞 E), ¬ (p : ℕ) ∣ n ∧ (n : E) * x = a) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator | exact GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator | (intros; apply GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_real_different_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : Nat.Primes, ∃ δ ∈ differentIdeal ℤ (𝓞 E), δ ≠ 0 ∧ IsCMField.complexConj E (δ : E) = δ ∧ ∀ j : E →+* ℂ_[p], Real.log ‖j (δ : E)‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_real_different_generator | exact GlobalTheory.CompanionTheory.Relay.exists_real_different_generator | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_real_different_generator <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.locally_free_of_short_exact : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), LocFree R (r₁ + r₂) L → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R r₁ (L.comap i.toAddMonoidHom) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.locally_free_base_change_quotient : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GraphRestrict.main | exact GlobalTheory.CompanionTheory.Ar.GraphRestrict.main | (intros; apply GlobalTheory.CompanionTheory.Ar.GraphRestrict.main <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem pt_af_type_main : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (MM : Submodule RC ((I → ZMod p) → C)), MM ≤ intFun RC _ → ∀ {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (χ : F → RC), χ 0 = 0 → χ 1 = 1 → ∀ (i : (Fin n → F) →+ (I → ZMod p)) (π : (I → ZMod p) →+ (Fin n → F)), (∀ y, π (i y) = y) → (∀ h ∈ MM, (fun x => h (i (π x))) ∈ MM) → (MM.map (LinearMap.funLeft RC C (i : (Fin n → F) → (I → ZMod p)))).toAddSubgroup = D.M → ∀ (Pm : Matrix (Fin n) I RC) (J : Matrix I (Fin n) RC), Pm * J = 1 → (∀ (k : Fin n) (x : I → ZMod p), (∑ j, Pm k j * ((x j).val : RC)) - χ (π x k) ∈ Ideal.span {(p : RC)}) → (∀ l ∈ afLat p MM, Matrix.vecMul l (J * Pm) ∈ afLat p MM) → (∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔ Matrix.vecMul l Pm ∈ afLat p MM) ∧ ∀ u : Fin n → C, u ∈ D.hh RC p (fun a => (χ a : C)) ↔ ∀ l ∈ afLat p MM, (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j) ∈ RC :=
  @PositivityTheory.Xgn.t_pt_af_type

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.locally_free_base_change_summand : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] (b : V →ₗ[Ω] Vc), IsBaseChange C b → ∀ (L : AddSubgroup V) (U : Submodule Ω V), (∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) → Summand L U → Summand (spanOver RC (b '' L)) (Submodule.span C (b '' U)) ∧ spanOver RC (b '' L) ⊓ (Submodule.span C (b '' U)).toAddSubgroup = spanOver RC (b '' (L ⊓ U.toAddSubgroup : AddSubgroup V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange | exact GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.locally_free_summand_criterion : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot | exact GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

theorem _root_.GlobalTheory.T.short_exact_standard_lattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.glue_gamdel_graphs | exact GlobalTheory.CompanionTheory.Ar.Num.glue_gamdel_graphs | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.glue_gamdel_graphs <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.kernel_graph_base_change_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (∀ i, (D.bc RC).kk τ i = spanOver RC (bcMap Ω C _ '' D.kk τ i)) ∧ ∀ i, (D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C _) '' D.stepGraph τ (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change | exact GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat

theorem exists_minor_ne_zero {Ω : Type*} [Field Ω] {M i : ℕ} (A : Fin M → Fin i → Ω)
    (hA : ∀ t : Fin i → Ω, t ∈ Submodule.span Ω (Set.range A)) :
    ∃ I : Fin i → Fin M, Matrix.det (Matrix.of fun a b : Fin i => A (I a) b) ≠ 0 := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent Ω (Set.range A)
  have htop : (⊤ : Submodule Ω (Fin i → Ω)) ≤ Submodule.span Ω (Set.range ((↑) : b → Fin i → Ω)) := by
    rw [Subtype.range_coe, hspan]
    exact fun t _ => hA t
  let bas := Module.Basis.mk hli htop
  have e : b ≃ Fin i := bas.indexEquiv (Pi.basisFun Ω (Fin i))
  have hI : ∀ a : Fin i, ∃ l, A l = (e.symm a : Fin i → Ω) := fun a => hb (e.symm a).2
  choose I hI using hI
  refine ⟨I, ?_⟩
  have hrow : LinearIndependent Ω (Matrix.of fun a b : Fin i => A (I a) b).row := by
    have : (Matrix.of fun a b : Fin i => A (I a) b).row = ((↑) : b → Fin i → Ω) ∘ e.symm := by
      funext a
      exact hI a
    rw [this]
    exact hli.comp _ e.symm.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hrow
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem chartRing_le_fnField (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}
    (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) {r : Ω} (hr : r ∈ chartRing O (mseg x) s) :
    r ∈ fnField O x := by
  rw [chartRing] at hr
  induction hr using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    show (∏ k, x ⟨k, t k⟩) / (∏ k, x ⟨k, s k⟩) ∈ fnField O x
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, (t k, s k)⟩, rfl⟩)
  | algebraMap c => exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

theorem mem_span_of_twistedDualGens (E : ChartBundle O (mseg x) N V) {M : ℕ} {a : K → ℤ}
    {φ : Fin M → Module.Dual Ω V} (hg : IsTwistedDualGens x E a φ) {s₀ : ∀ k, ι k}
    (hs : mseg x s₀ ≠ 0) (ψ : Module.Dual Ω V) : ψ ∈ Submodule.span Ω (Set.range φ) := by
  classical
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := E.frame s₀ hs
  have hne : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  obtain ⟨l, hl⟩ := hne
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  let bas := Module.Basis.mk hli hsp.ge
  obtain ⟨kg, G, hG, hgen⟩ := GroundTheory.Heights₂.Heights.Model.chartBundle_exists_gens E hs
  have hcoord : ∀ q, bas.coord q ∈ Submodule.span Ω (Set.range φ) := by
    intro q
    have h1 : ∀ g, ∃ n : ℕ, f l ^ n * bas.coord q (G g) ∈ chartRing O (mseg x) s₀ := by
      intro g
      obtain ⟨a', ha', he⟩ := (hiff (G g)).1 ⟨0, by simpa using hG g⟩
      have : bas.coord q (G g) = a' q := by

        rw [he, map_sum]
        simp only [map_smul]
        have hbq : ∀ q', bas.coord q (b q') = if q' = q then 1 else 0 := by
          intro q'
          have : b q' = bas q' := (Module.Basis.mk_apply hli hsp.ge q').symm
          rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        simp [hbq]
      rw [this]
      exact ha' q
    choose n hn using h1
    set n₀ := Finset.univ.sup n with hn₀
    have h2 : ∀ g, f l ^ n₀ * bas.coord q (G g) ∈ chartRing O (mseg x) s₀ := by
      intro g
      have hle : n g ≤ n₀ := Finset.le_sup (Finset.mem_univ g)
      rw [← pow_sub_mul_pow _ hle, mul_assoc]
      exact mul_mem (pow_mem (hf l) _) (hn g)
    have h3 : ∀ v ∈ E.lat s₀, (f l ^ n₀ • bas.coord q) v ∈ chartRing O (mseg x) s₀ := by
      intro v hv
      obtain ⟨β, hβ, rfl⟩ := hgen v hv

      simp only [LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      refine sum_mem fun g _ => ?_
      exact mul_mem (hβ g) (h2 g)
    obtain ⟨u, -, hu⟩ := hg.generate s₀ hs _ h3
    have h4 : f l ^ n₀ • bas.coord q ∈ Submodule.span Ω (Set.range φ) := by
      rw [hu]
      exact sum_mem fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    have h5 := Submodule.smul_mem _ (f l ^ n₀)⁻¹ h4
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul] at h5
  rw [← bas.sum_dual_apply_smul_coord ψ]
  exact sum_mem fun q _ => Submodule.smul_mem _ _ (hcoord q)

theorem exists_flagMinor_ne_zero {M : ℕ} {φ : Fin M → Module.Dual Ω V}
    (hφ : ∀ ψ : Module.Dual Ω V, ψ ∈ Submodule.span Ω (Set.range φ))
    (w : Module.Basis (Fin N) Ω V) (i : ℕ) (hi : i ≤ N) :
    ∃ I : Fin i → Fin M, flagMinor φ w i hi I ≠ 0 := by
  classical
  let L : Module.Dual Ω V →ₗ[Ω] (Fin i → Ω) :=
    LinearMap.pi fun b => Module.Dual.eval Ω V (w (Fin.castLE hi b))
  refine exists_minor_ne_zero (fun l b => φ l (w (Fin.castLE hi b))) fun t => ?_
  let ψ : Module.Dual Ω V := ∑ b, t b • w.coord (Fin.castLE hi b)
  have hL : L ψ = t := by
    funext b
    simp [L, ψ, Module.Dual.eval_apply, Finsupp.single_apply, Fin.castLE_inj]
  have h := Submodule.mem_map_of_mem (f := L) (hφ ψ)
  rw [Submodule.map_span, ← Set.range_comp, hL] at h
  exact h

theorem flagMinor_div_mem (E : ChartBundle O (mseg x) N V) {M : ℕ} {a : K → ℤ}
    {φ : Fin M → Module.Dual Ω V} (hg : IsTwistedDualGens x E a φ) {s₀ : ∀ k, ι k}
    (hs : mseg x s₀ ≠ 0) (w : Module.Basis (Fin N) Ω V)
    (hw : ∀ i, ∃ c : O, algebraMap O Ω c ≠ 0 ∧ algebraMap O Ω c • w i ∈ E.lat s₀)
    (i : ℕ) (hi : i ≤ N) (I I' : Fin i → Fin M) :
    flagMinor φ w i hi I / flagMinor φ w i hi I' ∈ fnField O x := by
  classical
  choose c hc0 hc using hw
  have hr : ∀ l b, ∃ r ∈ chartRing O (mseg x) s₀,
      φ l (algebraMap O Ω (c b) • w b) = r * ∏ k, x ⟨k, s₀ k⟩ ^ a k :=
    fun l b => hg.sections s₀ hs l _ (hc b)
  choose r hrm hr using hr
  set T : Ω := ∏ k, x ⟨k, s₀ k⟩ ^ a k with hT
  let D : Fin i → Ω := fun b => (algebraMap O Ω (c (Fin.castLE hi b)))⁻¹ * T
  have hφw : ∀ l b, φ l (w b) = (algebraMap O Ω (c b))⁻¹ * T * r l b := by
    intro l b
    have := hr l b
    rw [map_smul, smul_eq_mul] at this
    field_simp [hc0 b]
    linear_combination this
  have hdet : ∀ J : Fin i → Fin M, flagMinor φ w i hi J = (∏ b, D b) *
      Matrix.det (Matrix.of fun a' b : Fin i => r (J a') (Fin.castLE hi b)) := by
    intro J
    rw [← Matrix.det_mul_row]
    unfold flagMinor
    congr 1
    ext a' b
    simp [hφw, D]
  have hmem : ∀ J : Fin i → Fin M,
      Matrix.det (Matrix.of fun a' b : Fin i => r (J a') (Fin.castLE hi b)) ∈ fnField O x := by
    intro J
    rw [Matrix.det_apply']
    refine sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun b _ => ?_)
    exact chartRing_le_fnField O x s₀ (hrm _ _)
  rw [hdet I, hdet I']
  by_cases hD : ∏ b, D b = 0
  · simp [hD, zero_mem]
  · rw [mul_div_mul_left _ _ hD]
    exact div_mem (hmem I) (hmem I')

end GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat

open GlobalTheory.CompanionTheory.Ar.Num.PluckerBirat in
theorem GlobalTheory.CompanionTheory.Ar.Num.plucker_birat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (J : Type) [Fintype J] [DecidableEq J] (E : J → ChartBundle O (mseg x) N V) (M : J → ℕ) (a : J → K → ℤ) (φ : ∀ j, Fin (M j) → Module.Dual Ω V), (∀ j, IsTwistedDualGens x (E j) (a j) (φ j)) → ∀ (w : Module.Basis (Fin N) Ω V) (s₀ : ∀ k, ι k), mseg x s₀ ≠ 0 → (∀ k, ∃ I, pluckerCoord φ w ⟨k, I⟩ ≠ 0) ∧ ((∀ j i, ∃ c : O, algebraMap O Ω c ≠ 0 ∧ algebraMap O Ω c • w i ∈ (E j).lat s₀) → fnField O (joinCoord x (pluckerCoord φ w)) = fnField O x) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ J _ _ E M a φ hg w s₀ hs
  refine ⟨fun k => ?_, fun hw => le_antisymm ?_ ?_⟩
  · exact exists_flagMinor_ne_zero (mem_span_of_twistedDualGens (E k.1) (hg k.1) hs) w k.2
      (Nat.lt_succ_iff.mp k.2.2)
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, p, q⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · rcases k with k | k
      · exact Subfield.subset_closure (Or.inr ⟨⟨k, (p, q)⟩, rfl⟩)
      · exact flagMinor_div_mem (E k.1) (hg k.1) hs w (hw k.1) k.2 (Nat.lt_succ_iff.mp k.2.2) p q
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, p, q⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨Sum.inl k, (p, q)⟩, rfl⟩)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaLattice

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ {ι : Type} [Fintype ι] (N : ℕ) (L : AddSubgroup (ι → Ω)), LocFree R N L → ∀ v : ι → Ω, (∃ m : ℕ, (p : Ω) ^ m • v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → bcMap Ω C ι v ∈ spanOver RC (bcMap Ω C ι '' L)) → v ∈ L :=
  @PositivityTheory.Xgn.t_ha_lattice

end GlobalTheory.CompanionTheory.Ar.Num.HaLattice
end
