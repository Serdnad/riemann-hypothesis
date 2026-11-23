module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_fraction_evalSection_affine_near_point : ∀ (R : Type) [CommRing R] (W : (Sp R).Opens) (s : Γ(Sp R, W)) (x : PrimeSpectrum R), x ∈ W → ∃ α β : R, β ∉ x.asIdeal ∧ ∀ (F : Type) [Field F] (e : R →+* F) (h : ⊤ ≤ spMap e ⁻¹ᵁ W), WtRat.ev (spMap e) W h s * e β = e α := by
  first | exact @GlobalTheory.SS.WtRat.exists_frac_ev | exact GlobalTheory.SS.WtRat.exists_frac_ev | (intros; apply GlobalTheory.SS.WtRat.exists_frac_ev <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_generic_functionField_point : ∀ (Y : Scheme.{0}) [IsIntegral Y], ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ Y) (hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ g ⁻¹ᵁ V), (∀ (V : Y.Opens) (hV : (V : Set Y).Nonempty), Function.Injective (WtRat.ev g V (hg V hV))) ∧ (∀ τ : Y ≅ Y, ∃ σ : F →+* F, spMap σ ≫ g = g ≫ τ.hom) ∧ ∀ U : Y.Opens, (U : Set Y).Nonempty → ∀ (I : Type) [Fintype I] (x : I → F), ∃ (U' : Y.Opens) (hU' : (U' : Set Y).Nonempty) (s : I → Γ(Y, U')), U' ≤ U ∧ ∀ j, WtRat.ev g U' (hg U' hU') (s j) = x j ∧ (x j ≠ 0 → IsUnit (s j)) := by
  first | exact @GlobalTheory.SS.WtRat.exists_generic_field_point | exact GlobalTheory.SS.WtRat.exists_generic_field_point | (intros; apply GlobalTheory.SS.WtRat.exists_generic_field_point <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf.TwoVarSetup

theorem exists_liftAway {k R F : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing F] [Algebra k F]
    (x : R) (τ : R →ₐ[k] F) (h : IsUnit (τ x)) :
    ∃ τ' : Localization.Away x →ₐ[k] F, ∀ y, τ' (algebraMap R _ y) = τ y := by
  have hu : ∀ y : Submonoid.powers x, IsUnit (τ y) := by
    rintro ⟨y, n, rfl⟩
    show IsUnit (τ (x ^ n))
    rw [map_pow]; exact h.pow n
  exact ⟨IsLocalization.liftAlgHom (S := Localization.Away x) hu, fun x => by simp⟩

variable {k : Type} [Field k]

theorem laurent_ext {F : Type} [CommRing F] [Algebra k F] {a b : FractionRing (PowerSeries k) →ₐ[k] F}
    (h : ∀ x : PowerSeries k, a (algebraMap _ _ x) = b (algebraMap _ _ x)) : a = b := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k))
  exact RingHom.ext h

theorem hasSubst_diag :
    MvPowerSeries.HasSubst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> exact PowerSeries.constantCoeff_X

theorem hasSubst_var (i : Fin 2) :
    PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp)

theorem diag_var (i : Fin 2) :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k)
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) = PowerSeries.X := by
  rw [MvPowerSeries.subst_X hasSubst_diag]
  fin_cases i <;> rfl

theorem diag_subst (i : Fin 2) (x : PowerSeries k) :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k)
      (x.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) = x := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_var i).const hasSubst_diag]
  simp only [diag_var]
  rw [← PowerSeries.subst_def]
  simp

theorem exists_diag : ∃ τ : MvPowerSeries (Fin 2) k →ₐ[k] FractionRing (PowerSeries k), ∀ y,
    τ y = algebraMap (PowerSeries k) _
      (MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) y) :=
  ⟨(IsScalarTower.toAlgHom k (PowerSeries k) _).comp (MvPowerSeries.substAlgHom hasSubst_diag), fun y => by
    rw [AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]; rfl⟩

theorem exists_copy (i : Fin 2) : ∃ s : FractionRing (PowerSeries k) →ₐ[k]
      Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k),
    ∀ x : PowerSeries k, s (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _
      (x.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)
  rw [map_mul] at hu
  obtain ⟨s, hs⟩ := exists_lift ((IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k)
    (Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))).comp
      (PowerSeries.substAlgHom (hasSubst_var i))) (by
    rw [AlgHom.comp_apply, PowerSeries.substAlgHom_X]
    fin_cases i
    · exact isUnit_of_mul_isUnit_left hu
    · exact isUnit_of_mul_isUnit_right hu)
  refine ⟨s, fun x => ?_⟩
  rw [hs, AlgHom.comp_apply, PowerSeries.coe_substAlgHom]; rfl

theorem point_one {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} (h : algOverHom ε ≫ j = 1) (F : Type) [CommRing F] [Algebra k F] :
    algOverHom ((Algebra.ofId k F).comp ε) ≫ j = 1 := by
  rw [algOverHom_comp, Category.assoc, h, MonObj.comp_one]

theorem exists_twoVar : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ a : algOver k (FractionRing (PowerSeries k)) ⟶ G, ∃ (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) d ≠ 0 ∧ (∀ i, MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) (h i) = 0) ∧ TwoVar j f a h d := by
  intro k _ G _ A _ _ j ε r f hc a
  obtain ⟨τ₀, hτ₀⟩ := exists_diag (k := k)
  obtain ⟨s₀, hs₀⟩ := exists_copy (k := k) 0
  obtain ⟨s₁, hs₁⟩ := exists_copy (k := k) 1
  have hinj := IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))
  have hX : ∀ i, τ₀ (MvPowerSeries.X i) ≠ 0 := fun i => by
    rw [hτ₀, diag_var]
    exact (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  have hx : τ₀ (MvPowerSeries.X 0 * MvPowerSeries.X 1) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero (hX 0) (hX 1)
  generalize (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = x at s₀ s₁ hs₀ hs₁ hx
  obtain ⟨δ, hδ⟩ := exists_liftAway x τ₀ hx.isUnit
  have hδ₀ : δ.comp s₀ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₀, hδ, hτ₀, diag_subst]; rfl
  have hδ₁ : δ.comp s₁ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₁, hδ, hτ₀, diag_subst]; rfl
  obtain ⟨e, he, hfac⟩ := GlobalTheory.SS.ArcInf.exists_basicOpen_factor k G A _ (FractionRing (PowerSeries k)) j
    ((algOverHom s₁ ≫ a) * (algOverHom s₀ ≫ a)⁻¹) δ ((Algebra.ofId k _).comp ε) hc.1 (by
      rw [point_one hc.2.1, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
        ← algOverHom_comp, ← algOverHom_comp, hδ₀, hδ₁, mul_inv_cancel])
  obtain ⟨n, e₀, he₀⟩ := IsLocalization.Away.surj x e
  have hτe : τ₀ e₀ ≠ 0 := by
    rw [← hδ, ← he₀, map_mul, map_pow, hδ]
    exact mul_ne_zero he (pow_ne_zero _ hx)
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (x * e₀)) (x * e₀)
  rw [map_mul] at hu
  obtain ⟨ρ, hρ⟩ := exists_liftAway x
    (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (Localization.Away (x * e₀)))
    (isUnit_of_mul_isUnit_left hu)
  simp only [IsScalarTower.coe_toAlgHom'] at hρ
  have hρe : IsUnit (ρ e) := by
    have h1 := isUnit_of_mul_isUnit_right hu
    rw [← hρ, ← he₀, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨χ, hχ⟩ := hfac _ ρ hρe
  obtain ⟨⟨b, M, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (x * e₀)) (fun i => χ (f i))
  choose h hh using hb
  simp only [Algebra.smul_def] at hh
  have hd : τ₀ ((x * e₀) * (x * e₀) ^ M) ≠ 0 := by
    rw [← pow_succ', map_pow, map_mul]
    exact pow_ne_zero _ (mul_ne_zero hx hτe)
  have htv : TwoVar j f a (fun i => (x * e₀) * h i) ((x * e₀) * (x * e₀) ^ M) := by
    intro F _ _ τ σ₀ σ₁ hτ hσ₀ hσ₁
    have h0 : τ (x * e₀) ≠ 0 := by
      rw [map_mul] at hτ; exact left_ne_zero_of_mul hτ
    obtain ⟨τ', hτ'⟩ := exists_liftAway (x * e₀) τ h0.isUnit
    have e0 : τ'.comp (ρ.comp s₀) = σ₀ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₀, hρ, hτ', hσ₀]
    have e1 : τ'.comp (ρ.comp s₁) = σ₁ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₁, hρ, hτ', hσ₁]
    refine ⟨τ'.comp χ, fun i => ?_, ?_⟩
    · rw [map_mul τ (x * e₀) (h i), ← hτ' (h i), hh, map_mul τ', hτ', map_mul τ (x * e₀),
        AlgHom.comp_apply]
      ring
    · rw [algOverHom_comp, Category.assoc, hχ, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
        GrpObj.comp_inv]
      simp only [← Category.assoc, ← algOverHom_comp]
      rw [e0, e1, inv_mul_cancel_right]
  refine ⟨_, _, ?_, fun i => ?_, htv⟩
  · intro h0
    apply hd
    rw [hτ₀, h0, map_zero]
  · obtain ⟨χ', h1, h2⟩ := htv _ τ₀ (AlgHom.id k _) (AlgHom.id k _) hd
      (fun y => by rw [hτ₀, diag_subst]; rfl) (fun y => by rw [hτ₀, diag_subst]; rfl)
    have h3 : χ' = (Algebra.ofId k _).comp ε := by
      apply eq_of_comp_eq hc.1
      rw [point_one hc.2.1]
      exact right_eq_mul.1 h2
    apply hinj
    rw [← hτ₀, map_zero, ← h1 i, h3, AlgHom.comp_apply, hc.2.2.2 i, map_zero, zero_mul]

end GlobalTheory.SS.ArcInf.TwoVarSetup
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_lift_var (k : Type) [Field k] (n : Fin 2) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (MvPowerSeries (Fin 2) k),
      ∀ x : PowerSeries k, σ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _
        (x.subst (MvPowerSeries.X n : MvPowerSeries (Fin 2) k)) := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X n : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hX : (MvPowerSeries.X n : MvPowerSeries (Fin 2) k) ≠ 0 := by
    intro h0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single n 1)) h0
    simp [MvPowerSeries.coeff_X] at this
  obtain ⟨σ, hσ⟩ := exists_lift (k := k)
    ((IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))).comp
      (PowerSeries.substAlgHom (R := k) hs)) (by
      rw [AlgHom.comp_apply, PowerSeries.substAlgHom_X, isUnit_iff_ne_zero, IsScalarTower.toAlgHom_apply]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hX)
  refine ⟨σ, fun x => ?_⟩
  rw [hσ, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, PowerSeries.coe_substAlgHom]

theorem extends_of_regular_second_axis :
    ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ (a : algOver k (FractionRing (PowerSeries k)) ⟶ G) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → TwoVar j f a h d → (∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) → ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a := by
  intro k _ G _ A _ _ j ε r f hc a h d hd ht hreg
  obtain ⟨σ₀, h0⟩ := exists_lift_var k 0
  obtain ⟨σ₁, h1⟩ := exists_lift_var k 1
  obtain ⟨L, hloc, hmem, hL0, hL1⟩ := GlobalTheory.TwoVarValRing.exists_local_ring_second_variable k σ₀ σ₁ h0 h1
  have hd' : algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k)) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hd
  obtain ⟨χ, hχ, he⟩ := ht (FractionRing (MvPowerSeries (Fin 2) k))
    (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))) σ₀ σ₁ hd' h0 h1
  have hf : ∀ i, χ (f i) ∈ L := by
    intro i
    obtain ⟨u, v, hv, huv⟩ := hreg i
    refine hmem _ u v hv ?_
    have e1 := hχ i
    simp only [IsScalarTower.toAlgHom_apply] at e1
    have e2 := congrArg (algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))) huv
    rw [map_mul, map_mul, ← e1] at e2
    apply mul_left_cancel₀ hd'
    rw [← e2]
    ring
  have hall : ∀ x, χ x ∈ L := by
    have : Algebra.adjoin k (Set.range f) ≤ L.comap χ :=
      Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hf i)
    intro x
    exact this (by rw [hc.2.2.1]; trivial)
  refine GlobalTheory.SS.ArcInf.exists_extend_of_localSubring k G (PowerSeries k) (FractionRing (PowerSeries k)) (FractionRing (MvPowerSeries (Fin 2) k))
    _ σ₁ L hloc (IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))) hL1 a
    ((algOverHom (χ.codRestrict L hall) ≫ j) * (algOverHom (σ₀.codRestrict L hL0) ≫ a)) ?_
  rw [he, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← algOverHom_comp, ← algOverHom_comp]
  rfl

end GlobalTheory.SS.ArcInf
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.ModelPoints

theorem exists_push_equiv {S S' : Scheme.{0}} (f : S' ⟶ S) (H : Over S) [GrpObj H] (T : Over S')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H),
      ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_comp_equiv {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (e : G ≅ H) [IsMonHom e.hom]
    (T : Over S) : ∃ π : (T ⟶ G) ≃* (T ⟶ H), ∀ y, π.symm y = y ≫ e.inv :=
  ⟨{ toFun := fun x => x ≫ e.hom
     invFun := fun y => y ≫ e.inv
     left_inv := fun x => by simp
     right_inv := fun x => by simp
     map_mul' := fun x y => MonObj.mul_comp x y e.hom }, fun _ => rfl⟩

theorem exists_equiv {S₁ S₂ S : Scheme.{0}} (f : S ⟶ S₁) (g : S ⟶ S₂) (A : Over S₁) [GrpObj A]
    (G : Over S₂) [GrpObj G] (e : (Over.pullback g).obj G ≅ (Over.pullback f).obj A) [IsMonHom e.hom]
    {T : Scheme.{0}} (t : T ⟶ S) (s₁ : T ⟶ S₁) (s₂ : T ⟶ S₂) (h₁ : s₁ = t ≫ f) (h₂ : s₂ = t ≫ g) :
    ∃ θ : (Over.mk s₁ ⟶ A) ≃* (Over.mk s₂ ⟶ G), ∀ (x : Over.mk s₁ ⟶ A) (z : T ⟶ pullback A.hom f),
      z ≫ pullback.fst A.hom f = x.left → z ≫ pullback.snd A.hom f = t →
      (θ x).left = z ≫ e.inv.left ≫ pullback.fst G.hom g := by
  obtain ⟨π₁, p₁⟩ := exists_push_equiv f A (Over.mk t) s₁ h₁
  obtain ⟨π₂, p₂⟩ := exists_push_equiv g G (Over.mk t) s₂ h₂
  obtain ⟨π, p⟩ := exists_comp_equiv e (Over.mk t)
  refine ⟨π₁.symm.trans (π.symm.trans π₂), fun x z hz hz' => ?_⟩
  have hx : π₁.symm x = Over.homMk z hz' := by
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hz.symm.trans (p₁ (Over.homMk z hz')).symm)
  show (π₂ (π.symm (π₁.symm x))).left = _
  rw [p₂, p, hx, Over.comp_left, Category.assoc]
  rfl

theorem spMap_comp_of_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap h = spMap g ≫ spMap f := by
  subst e
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem spMap_cancel {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {g : B →+* C}
    (hg : Function.Injective g) {a b : Sp B ⟶ Sp A} (e : spMap g ≫ a = spMap g ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at e
  congr 1
  ext x
  exact hg (congrArg (fun q => q.hom x) e)

theorem points_model : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by
  intro K W L _ _ _ _ _ A _ G _ ⟨e, he⟩ Ω _ _ _ j hK hW
  obtain ⟨θ, hθ⟩ := exists_equiv (spMap (algebraMap K L)) (spMap (algebraMap W L)) A G e (spMap j)
    _ _ (spMap_comp_of_eq hK) (spMap_comp_of_eq hW)
  refine ⟨θ, fun τ hτ x x' hx => ?_, fun K' _ i j' hj x y hy ρ hρ => ?_⟩
  · have w : x.left ≫ A.hom = spMap j ≫ spMap (algebraMap K L) :=
      (Over.w x).trans (spMap_comp_of_eq hK)
    rw [hθ x (pullback.lift x.left (spMap j) w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
      hθ x' (spMap τ ≫ pullback.lift x.left (spMap j) w)
        (by rw [Category.assoc, pullback.lift_fst, hx])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hτ]), Category.assoc]
  · have w : y ≫ A.hom = spMap i ≫ spMap (algebraMap K L) := by
      apply spMap_cancel j'.injective
      rw [← Category.assoc, hy, ← Category.assoc, ← spMap_comp_of_eq hj]
      exact (Over.w x).trans (spMap_comp_of_eq hK)
    have w' : (pullback.lift y (spMap i) w ≫ e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap W L))) ≫ G.hom
        = spMap ρ := by
      have h₁ : e.inv.left ≫ pullback.snd G.hom (spMap (algebraMap W L))
          = pullback.snd A.hom (spMap (algebraMap K L)) := Over.w e.inv
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% h₁, pullback.lift_snd_assoc]
      exact (spMap_comp_of_eq hρ.symm).symm
    have hU : spMap j' ≫ spMap ρ = spMap (algebraMap W Ω) :=
      (spMap_comp_of_eq (by rw [hρ, ← RingHom.comp_assoc, hj, hW])).symm
    let U : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap ρ) := Over.homMk (spMap j') hU
    let y' : Over.mk (spMap ρ) ⟶ G := Over.homMk _ w'
    have hxy : θ x = U ≫ y' := by
      apply Over.OverMorphism.ext
      rw [hθ x (spMap j' ≫ pullback.lift y (spMap i) w)
        (by rw [Category.assoc, pullback.lift_fst, hy])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hj]), Category.assoc]
      rfl
    refine ⟨y', fun c => ?_⟩
    rw [map_pow, hxy, ← MonObj.comp_pow]
    rfl

end GlobalTheory.SS.ModelPoints
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

theorem _root_.GlobalTheory.T.exists_basicOpen_factor_fieldPoint_affineOpen : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  first | exact @GlobalTheory.SS.ArcInf.exists_basicOpen_factor | exact GlobalTheory.SS.ArcInf.exists_basicOpen_factor | (intros; apply GlobalTheory.SS.ArcInf.exists_basicOpen_factor <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.abelianVariety_torsion_finite_endomorphism_divisible : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ ∀ f : B ⟶ B, IsMonHom f → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ^ n = 1 → x ≫ f = 1) → ∃ g : B ⟶ B, IsMonHom g ∧ f = g ^ n := by
  first | exact @GlobalTheory.TorsionDivisible.finite_torsion_and_divisible | exact GlobalTheory.TorsionDivisible.finite_torsion_and_divisible | (intros; apply GlobalTheory.TorsionDivisible.finite_torsion_and_divisible <;> assumption)
end
