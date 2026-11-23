module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_difference : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ → ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 → IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  first | exact @GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div | exact GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div | (intros; apply GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ → ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧ IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  first | exact @GlobalTheory.WpInt.main | exact GlobalTheory.WpInt.main | (intros; apply GlobalTheory.WpInt.main <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValInj

theorem eq_zero_of_val_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  intro A _ g L u hA U b hb
  haveI : Smooth A.hom := hA.smooth
  haveI : IsReduced A.left := isReduced_of_smooth A.hom
  refine GlobalTheory.ComplexPoints.eq_of_valAt'_eq A.hom U b 0 fun x hx hxU => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  have hzx : (u.ex z).left = x := by rw [hz]; rfl
  have h1 : val u.ex U b z = 0 := hb z (by show ⊤ ≤ (u.ex z).left ⁻¹ᵁ U; rw [hzx]; exact hxU)
  rw [show val u.ex U b z = valAt' (u.ex z).left U b from rfl, hzx] at h1
  rw [h1]
  unfold valAt' valAt
  split_ifs <;> simp

end GlobalTheory.ValInj
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem locally_standardSmooth_sec (A : Over (Sp ℂ)) (g : ℕ) (h : SmoothOfRelativeDimension g A.hom) (U : A.left.affineOpens) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap ℂ (Sec (str A) U.1)) := by
  have h' : SmoothOfRelativeDimension g (str A) := by
    simpa [str] using h
  have h1 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) (str A) h' ⟨⊤, isAffineOpen_top _⟩ U le_top
  have hr := RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := g))
  exact hr.2 _ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv h1

theorem kaehler_sec_finite_projective_rank : ∀ (A : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ U : A.left.affineOpens, Module.Finite (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ Module.Projective (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ ∀ p : PrimeSpectrum (Sec (str A) U.1), Module.rankAtStalk Ω[Sec (str A) U.1⁄ℂ] p = g := by
  intro A g h U
  have hl := locally_standardSmooth_sec A g h U
  haveI := GlobalTheory.AugCot.smooth_of_locally hl
  exact ⟨inferInstance, inferInstance, GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally hl⟩

end GlobalTheory.CechPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MaxPoints

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens), IsAffineOpen U → ∀ m : Ideal Γ(A.left, U), m.IsMaximal →
      ∃ z ∈ pre u.ex U, ∀ b, b ∈ m ↔ val u.ex U b z = 0 := by
  intro A _ g L u hA U hU m hm
  haveI : Smooth A.hom := hA.smooth
  have hft : LocallyOfFiniteType A.hom := inferInstance
  let c : ℂ →+* Γ(A.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ A.hom.appLE ⊤ U (fun _ _ => trivial)).hom
  have hc : c.FiniteType := by
    have h1 : (A.hom.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType A.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(A.left, U) := c.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(A.left, U) := hc
  haveI : IsJacobsonRing Γ(A.left, U) := isJacobsonRing_of_finiteType (A := ℂ)
  letI : Field (Γ(A.left, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(A.left, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(A.left, U) ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (Γ(A.left, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (Γ(A.left, U) ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hb
  let e : Γ(A.left, U) →ₐ[ℂ] ℂ := (i.symm : (Γ(A.left, U) ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)
  have he : ∀ a, e.toRingHom (constFn A.hom U a) = a := fun a => e.commutes a
  obtain ⟨x, ⟨hxU, hx⟩, -⟩ := GlobalTheory.existsUnique_point_of_ringHom A U hU e.toRingHom he
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨z, hxU, fun b => ?_⟩
  change b ∈ m ↔ valAt' (u.ex z).left U b = 0
  rw [hx b]
  change b ∈ m ↔ i.symm (Ideal.Quotient.mk m b) = 0
  rw [← map_zero i.symm, i.symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPoints
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClearDen

theorem exists_pow_mul_eq_val : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens), IsAffineOpen U → ∀ (r : Γ(A.left, U)) (k : (Fin g → ℂ) → ℂ), IsReg u.ex (A.left.basicOpen r) k → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, U), ∀ z ∈ pre u.ex (A.left.basicOpen r), val u.ex U b z = val u.ex U r z ^ N * k z := by
  intro A _ g L u U hU r k ⟨f, hf⟩
  have hloc := hU.isLocalization_basicOpen r
  obtain ⟨⟨b₀, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers r) f
  simp only at hb
  refine ⟨n, fun N hN => ⟨r ^ (N - n) * b₀, fun z hz => ?_⟩⟩
  have hzU : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U := GlobalTheory.top_le_preimage_mono _ (A.left.basicOpen_le r) hz
  have key : ∀ c : Γ(A.left, U), val u.ex (A.left.basicOpen r) (algebraMap Γ(A.left, U) Γ(A.left, A.left.basicOpen r) c) z = val u.ex U c z := by
    intro c
    exact GlobalTheory.valAt'_map _ (homOfLE (A.left.basicOpen_le r)).op c hz
  have e0 := congrArg (fun y => val u.ex (A.left.basicOpen r) y z) hb
  have e1 : val u.ex (A.left.basicOpen r) f z * val u.ex U r z ^ n = val u.ex U b₀ z := by
    rw [← key b₀, ← e0]
    delta GlobalTheory.CechPer.val
    rw [GlobalTheory.valAt'_mul]
    congr 1
    have hrest : ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left (A.left.basicOpen r)
        (algebraMap Γ(A.left, U) Γ(A.left, A.left.basicOpen r) (r ^ n)) =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left U (r ^ n) := key (r ^ n)
    rw [hrest, GlobalTheory.valAt'_pow _ hzU]
  have e2 : val u.ex U (r ^ (N - n) * b₀) z = val u.ex U r z ^ (N - n) * val u.ex U b₀ z := by
    delta GlobalTheory.CechPer.val
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_pow _ hzU]
  rw [e2, ← e1, hf z hz, ← Nat.sub_add_cancel hN, pow_add, Nat.add_sub_cancel]
  ring

end GlobalTheory.ClearDen
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer


open Opposite in
theorem periods_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ x y q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ y q' → IsPer u.ex u.Λ (x + y) (q + q') ∧ IsPer u.ex u.Λ (x - y) (q - q')) ∧ ∀ (a : ℂ) x q, IsPer u.ex u.Λ x q → IsPer u.ex u.Λ (a • x) (a • q) := by
  intro A _ g L u
  have hO : ∀ U : A.left.Opens, IsOpen (pre u.ex U) := fun U ↦ (u.hol U 0).1
  have vadd : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z :=
    fun U b b' z ↦ valAt'_add _ _ _ _
  have vsub : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z :=
    fun U b b' z ↦ valAt'_sub _ _ _ _
  have vsmul : ∀ (U : A.left.Opens) (a : ℂ) (b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a • b) z = a * val u.ex U b z := by
    intro U a b z hz
    have e : (u.ex z).left ≫ str A = 𝟙 (Sp ℂ) := by
      rw [str, Category.comp_id]; exact Over.w (u.ex z)
    have k : valAt' (u.ex z).left U ((secMap (str A) U).hom a) = a :=
      (valAt'_appLE (u.ex z).left (str A) ⊤ U le_top _ hz).trans
        ((congrArg (fun p ↦ valAt' p ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (valAt'_id_top a))
    exact (valAt'_mul (u.ex z).left U ((secMap (str A) U).hom a) b).trans (congrArg (· * val u.ex U b z) k)
  have dA : ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (U : A.left.affineOpens),
      DifferentiableOn ℂ (k U) (pre u.ex U.1) → ∀ z ∈ pre u.ex U.1, DifferentiableAt ℂ (k U) z :=
    fun k U hk z hz ↦ hk.differentiableAt ((hO _).mem_nhds hz)
  refine ⟨fun x y q q' hx hy ↦ ?_, fun a x q hx ↦ ?_⟩
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    obtain ⟨c', h', rfl, ⟨h1', h2', h3'⟩, hp'⟩ := hy
    constructor
    · refine ⟨c + c', fun U z ↦ h U z + h' U z, map_add _ _ _,
        ⟨fun U ↦ (h1 U).add (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z + h' V z = (h U z + h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f + c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vadd V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z + h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) + c'.1.2 (op U))
        rw [fderiv_fun_add (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_add (f := _), h3 U z hz, h3' U z hz]
      · simp only [Pi.add_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
    · refine ⟨c - c', fun U z ↦ h U z - h' U z, map_sub _ _ _,
        ⟨fun U ↦ (h1 U).sub (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z - h' V z = (h U z - h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f - c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vsub V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z - h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) - c'.1.2 (op U))
        rw [fderiv_fun_sub (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_sub, h3 U z hz, h3' U z hz]
      · simp only [Pi.sub_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    refine ⟨a • c, fun U z ↦ a * h U z, map_smul _ _ _,
      ⟨fun U ↦ (h1 U).const_mul a, fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
    · change a * h V z = a * h U z + val u.ex V.1 (a • c.1.1 (op U) (op V) f) z
      refine Eq.trans ?_ (congrArg _ (vsmul V.1 a _ z hz).symm)
      rw [h2 U V f z hz]; ring
    · change fderiv ℂ (fun z ↦ a * h U z) z = evForm u.ex U.1 z (a • c.1.2 (op U))
      rw [fderiv_const_mul (dA h U (h1 U) z hz), map_smul, h3 U z hz]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hp U l z hz]; ring

end GlobalTheory.CechPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPer

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left}

theorem holUnif_ex_left_comp_str (u : HolUnif A L g) (w : Fin g → ℂ) : (u.ex w).left ≫ str A = 𝟙 (Sp ℂ) := by
  have := Over.w (u.ex w)
  simp [str, this]

theorem holUnif_val_algebraMap (u : HolUnif A L g) (U : A.left.Opens) (w : Fin g → ℂ) (hw : w ∈ pre u.ex U) (c : ℂ) :
    val u.ex U (algebraMap ℂ (Sec (str A) U) c) w = c := by
  show valAt' (u.ex w).left U (((str A).appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
  rw [valAt'_appLE (u.ex w).left (str A) ⊤ U le_top _ hw, holUnif_ex_left_comp_str]
  exact valAt'_id_top c

theorem holUnif_val_mul (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a * b) = fun w => val u.ex U a w * val u.ex U b w :=
  funext fun w => valAt'_mul (u.ex w).left U a b

theorem holUnif_val_add (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a + b) = fun w => val u.ex U a w + val u.ex U b w :=
  funext fun w => valAt'_add (u.ex w).left U a b

theorem holUnif_differentiableAt_val (u : HolUnif A L g) (U : A.left.Opens) (b : Sec (str A) U) {z : Fin g → ℂ}
    (hz : z ∈ pre u.ex U) : DifferentiableAt ℂ (val u.ex U b) z :=
  (u.hol U b).2.differentiableAt (((u.hol U b).1).mem_nhds hz)

theorem exists_isEv (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    ∃ E, IsEv u.ex U z E := by
  let N := (Fin g → ℂ) →L[ℂ] ℂ
  let e : Sec (str A) U →+* ℂ := valAtHom (u.ex z).left U hz
  have he : ∀ a, e a = val u.ex U a z := fun a => (valAt'_eq_valAtHom (u.ex z).left hz a).symm
  letI : Module (Sec (str A) U) N := Module.compHom N e
  haveI : IsScalarTower ℂ (Sec (str A) U) N := ⟨fun c a n => by
    show e (c • a) • n = c • (e a • n)
    rw [Algebra.smul_def, map_mul, mul_smul, he (algebraMap ℂ _ c), holUnif_val_algebraMap u U z hz]⟩
  have hc : ∀ (c : ℂ) (b : Sec (str A) U), val u.ex U (c • b) =ᶠ[nhds z] fun w => c * val u.ex U b w := by
    intro c b
    filter_upwards [((u.hol U b).1).mem_nhds hz] with w hw
    rw [Algebra.smul_def, holUnif_val_mul]
    exact congrArg (· * val u.ex U b w) (holUnif_val_algebraMap u U w hw c)
  let Dl : Sec (str A) U →ₗ[ℂ] N :=
    { toFun := fun b => fderiv ℂ (val u.ex U b) z
      map_add' := fun a b =>
        (congrArg (fun f => fderiv ℂ f z) (holUnif_val_add u U a b)).trans
          (fderiv_add (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz))
      map_smul' := fun c b =>
        (hc c b).fderiv_eq.trans (fderiv_const_mul (holUnif_differentiableAt_val u U b hz) c) }
  let D' : Derivation ℂ (Sec (str A) U) N :=
    { Dl with
      map_one_eq_zero' := by
        show fderiv ℂ (val u.ex U 1) z = 0
        have h1 : val u.ex U (1 : Sec (str A) U) =ᶠ[nhds z] fun _ => (1 : ℂ) := by
          filter_upwards [((u.hol U 1).1).mem_nhds hz] with w hw
          exact valAt'_one (u.ex w).left hw
        exact h1.fderiv_eq.trans (fderiv_const_apply 1)
      leibniz' := fun a b => by
        show fderiv ℂ (val u.ex U (a * b)) z = e a • fderiv ℂ (val u.ex U b) z + e b • fderiv ℂ (val u.ex U a) z
        rw [he, he]
        exact (congrArg (fun f => fderiv ℂ f z) (holUnif_val_mul u U a b)).trans
          (fderiv_mul (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz)) }
  refine ⟨D'.liftKaehlerDifferential.restrictScalars ℂ, fun a b => ?_⟩
  show D'.liftKaehlerDifferential (a • KaehlerDifferential.D ℂ (Sec (str A) U) b) = _
  rw [LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D]
  show e a • fderiv ℂ (val u.ex U b) z = _
  rw [he]

theorem isEv_evForm (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    IsEv u.ex U z (evForm u.ex U z) := by
  have h := exists_isEv u U hz
  rw [evForm, dite_eq_left h]
  exact h.choose_spec

theorem evForm_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens),
    ∀ z ∈ pre u.ex U, IsEv u.ex U z (evForm u.ex U z) ∧
      (∀ (a : Sec (str A) U) ξ, evForm u.ex U z (a • ξ) = val u.ex U a z • evForm u.ex U z ξ) ∧
      ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
  intro A _ g L u U z hz
  have hE := isEv_evForm u U hz
  have hone : val u.ex U (1 : Sec (str A) U) z = 1 := valAt'_one (u.ex z).left hz
  have hD : ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
    intro b
    have := hE 1 b
    rwa [one_smul, hone, one_smul] at this
  refine ⟨hE, fun a ξ => ?_, hD⟩
  have hspan := KaehlerDifferential.span_range_derivation ℂ (Sec (str A) U)
  have hξ : ξ ∈ Submodule.span (Sec (str A) U) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U))) := by
    rw [hspan]; exact Submodule.mem_top
  revert a
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    intro a
    rw [hE a b, hD]
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | smul s x _ hx =>
    intro a
    rw [smul_smul, hx, hx, smul_smul, holUnif_val_mul]

end GlobalTheory.CechPer
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPer

theorem ex_add_lattice {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left} (u : HolUnif A L g) (l : u.Λ) (z : Fin g → ℂ) :
    u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem pre_val_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ U, IsOpen (pre u.ex U)) ∧ (∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)) ∧ (∀ U (l : u.Λ) (z : Fin g → ℂ), z + l ∈ pre u.ex U ↔ z ∈ pre u.ex U) ∧ (∀ U b (l : u.Λ) (z : Fin g → ℂ), val u.ex U b (z + l) = val u.ex U b z) ∧ (∀ U V, pre u.ex (U ⊓ V) = pre u.ex U ∩ pre u.ex V) ∧ (∀ U V, V ≤ U → pre u.ex V ⊆ pre u.ex U) ∧ (∀ (K : Type) (W : K → A.left.Opens) z, z ∈ pre u.ex (⨆ i, W i) ↔ ∃ i, z ∈ pre u.ex (W i)) ∧ (∀ U z, z ∈ pre u.ex U → ∃ W : A.left.affineOpens, W.1 ≤ U ∧ z ∈ pre u.ex W.1) ∧ (∀ U V (h : V ≤ U) (b : Sec (str A) U), ∀ z ∈ pre u.ex V, val u.ex V (Sec.res (str A) h b) z = val u.ex U b z) ∧ (∀ U, ∀ z ∈ pre u.ex U, ∃ e : Sec (str A) U →ₐ[ℂ] ℂ, ∀ b, val u.ex U b z = e b) ∧ (∀ U b z, z ∈ pre u.ex (A.left.basicOpen b) ↔ val u.ex U b z ≠ 0) ∧ ∀ z, z ∈ pre u.ex ⊤ := by
  intro A _ g L u
  refine ⟨fun U ↦ (u.hol U 0).1, fun U b ↦ (u.hol U b).2, fun U l z ↦ ?_, fun U b l z ↦ ?_, fun U V ↦ ?_,
    fun U V h z hz ↦ top_le_preimage_mono _ h hz, fun K W z ↦ ?_, fun U z hz ↦ ?_,
    fun U V h b z hz ↦ valAt'_map (u.ex z).left (homOfLE h).op b hz, fun U z hz ↦ ?_,
    fun U b z ↦ top_le_preimage_basicOpen_iff _ U b, fun z ↦ le_top (α := (Sp ℂ).Opens)⟩
  · simp only [pre, Set.mem_setOf_eq, ex_add_lattice]
  · simp only [val, ex_add_lattice]
  · ext z
    exact top_le_preimage_inf _ U V
  · refine (top_le_preimage_iff_mem (u.ex z).left _).trans (TopologicalSpace.Opens.mem_iSup.trans ?_)
    exact exists_congr fun i ↦ (top_le_preimage_iff_mem (u.ex z).left _).symm
  · have h1 := (top_le_preimage_iff_mem (u.ex z).left _).1 hz
    obtain ⟨W, hW, h2, h3⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.left.isBasis_affineOpens) h1
    exact ⟨⟨W, hW⟩, h3, (top_le_preimage_iff_mem (u.ex z).left _).2 h2⟩
  · refine ⟨{ toRingHom := valAtHom (u.ex z).left U hz, commutes' := fun a ↦ ?_ }, fun b ↦ valAt'_eq_valAtHom _ hz b⟩
    refine (valAt'_eq_valAtHom (u.ex z).left hz _).symm.trans ?_
    refine valAt'_constFn (u.ex z).left (str A) ?_ U a hz
    exact (congrArg _ (Category.comp_id _)).trans (Over.w (u.ex z))

end GlobalTheory.CechPer
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RegAlg

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ U : A.left.Opens, (∀ a : ℂ, IsReg u.ex U fun _ => a) ∧ (∀ k k', IsReg u.ex U k → IsReg u.ex U k' → IsReg u.ex U (k + k') ∧ IsReg u.ex U (k - k') ∧ IsReg u.ex U (k * k')) ∧ (∀ k k', IsReg u.ex U k → (∀ z ∈ pre u.ex U, k' z = k z) → IsReg u.ex U k') ∧ (∀ V, V ≤ U → ∀ k, IsReg u.ex U k → IsReg u.ex V k) ∧ (∀ k, IsReg u.ex U k → DifferentiableOn ℂ k (pre u.ex U)) ∧ ∀ (n : ℕ) (k : Fin n → (Fin g → ℂ) → ℂ), (∀ i, IsReg u.ex U (k i)) → IsReg u.ex U (fun z => ∑ i, k i z) := by
  intro A _ g L u U
  refine ⟨fun a => ?_, fun k k' hk hk' => ?_, fun k k' hk he => ?_, fun V hV k hk => ?_, fun k hk => ?_, fun n k hk => ?_⟩
  · refine ⟨constFn A.hom U a, fun z hz => ?_⟩
    have hp : (u.ex z).left ≫ A.hom = 𝟙 _ := by
      simpa using Over.w (u.ex z)
    exact (GlobalTheory.valAt'_constFn (u.ex z).left A.hom hp U a hz).symm
  · obtain ⟨b, hb⟩ := hk
    obtain ⟨b', hb'⟩ := hk'
    refine ⟨⟨b + b', fun z hz => ?_⟩, ⟨b - b', fun z hz => ?_⟩, ⟨b * b', fun z hz => ?_⟩⟩
    · delta GlobalTheory.CechPer.val at hb hb' ⊢
      simp only [Pi.add_apply, GlobalTheory.valAt'_add, hb z hz, hb' z hz]
    · delta GlobalTheory.CechPer.val at hb hb' ⊢
      simp only [Pi.sub_apply, GlobalTheory.valAt'_sub, hb z hz, hb' z hz]
    · delta GlobalTheory.CechPer.val at hb hb' ⊢
      simp only [Pi.mul_apply, GlobalTheory.valAt'_mul, hb z hz, hb' z hz]
  · obtain ⟨b, hb⟩ := hk
    exact ⟨b, fun z hz => (he z hz).trans (hb z hz)⟩
  · obtain ⟨b, hb⟩ := hk
    refine ⟨resG A.left hV b, fun z hz => ?_⟩
    have hzU : z ∈ pre u.ex U := GlobalTheory.top_le_preimage_mono _ hV hz
    rw [hb z hzU]
    exact (GlobalTheory.valAt'_res (u.ex z).left hV b hz).symm
  · obtain ⟨b, hb⟩ := hk
    exact (u.hol U b).2.congr fun z hz => hb z hz
  · choose b hb using hk
    refine ⟨∑ i, b i, fun z hz => ?_⟩
    delta GlobalTheory.CechPer.val at hb ⊢
    simp only [GlobalTheory.valAt'_sum]
    exact Finset.sum_congr rfl fun i _ => hb i z hz

end GlobalTheory.RegAlg
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cohomologyDerivativeRelation_pairing_wellDefined : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x y' w' → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = ∑ k, l (w' k) • y' k := by
  first | exact @GlobalTheory.AbCoh.derivClass_eq | exact GlobalTheory.AbCoh.derivClass_eq | (intros; apply GlobalTheory.AbCoh.derivClass_eq <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.obstructionClass_natural : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → ∀ (x : HO1 s') (z : HO2 s₀) (z' : HO2 q₀), Bock h.w h₀.w t x z → Bock k.w k₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
  first | exact @GlobalTheory.AbCoh.bock_natural | exact GlobalTheory.AbCoh.bock_natural | (intros; apply GlobalTheory.AbCoh.bock_natural <;> assumption)
end
