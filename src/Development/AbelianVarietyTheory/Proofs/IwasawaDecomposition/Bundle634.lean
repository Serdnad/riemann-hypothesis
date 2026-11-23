module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle165
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotInternalOfRead
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.CoordUniq

section Lin

variable {K : Type} [Field K] {m n : ℕ}

theorem tri_of_mul {T₁ T₂ M : Fin m → Fin m → K} (h₁ : ∀ i k, i < k → T₁ i k = 0) (h₂ : ∀ i k, i < k → T₂ i k = 0)
    (hd : ∀ i, T₂ i i ≠ 0) (h : ∀ i k, T₁ i k = ∑ j, T₂ i j * M j k) (i : Fin m) : ∀ k, i < k → M i k = 0 := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro k hk
    have e := h i k
    rw [h₁ i k hk, Finset.sum_eq_single i (fun j _ hj => by
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [ih j hj k (hj.trans hk), mul_zero]
      · rw [h₂ i j hj, zero_mul]) (by simp)] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (hd i)

theorem diag_of_mul {T₂ M : Fin m → Fin m → K} (h₂ : ∀ i k, i < k → T₂ i k = 0) (hM : ∀ i k, i < k → M i k = 0)
    (i : Fin m) : ∑ j, T₂ i j * M j i = T₂ i i * M i i :=
  Finset.sum_eq_single i (fun j _ hj => by
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hM j i hj, mul_zero]
    · rw [h₂ i j hj, zero_mul]) (by simp)

theorem indep_of_tri {T : Fin m → Fin m → K} (h : ∀ i k, i < k → T i k = 0) (hd : ∀ i, T i i ≠ 0)
    {e : Fin m → Fin n → K} (hg : ∀ a : Fin m → K, ∑ i, a i • ∑ j, T i j • e j = 0 → a = 0)
    {b : Fin m → K} (hb : ∑ j, b j • e j = 0) : b = 0 := by
  have hdet : IsUnit (Matrix.of T).det := by
    rw [Matrix.det_of_isLowerTriangular (Matrix.of T) (fun i k hk => h i k hk)]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have e1 : Matrix.vecMul (Matrix.vecMul b (Matrix.of T)⁻¹) (Matrix.of T) = b := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  have e2 := hg (Matrix.vecMul b (Matrix.of T)⁻¹) (by
    rw [← hb]
    conv_rhs => rw [← e1]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    rfl)
  rw [← e1, e2, Matrix.zero_vecMul]

end Lin

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_matrix {R : Type} [CommRing R] [IsLocalRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ f₂ : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ M : Fin (Dw.mult τ) → Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∃ T₁ T₂ : Fin (Dw.mult τ) → Fin (Dw.mult τ) → k,
        (∀ i, T₁ i i = t₁ τ i) ∧ (∀ i, T₂ i i = t₂ τ i) ∧ (∀ i k, i < k → T₁ i k = 0) ∧ (∀ i k, i < k → T₂ i k = 0) ∧
          ∀ i k, T₁ i k = ∑ j, T₂ i j * ψ (M j k) := by
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan τ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan τ i)
  choose M hM using fun i => (f₁.basis τ _ (f₂.tan τ i) (f₂.eig τ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v τ = fun j => vec Z.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  refine ⟨M, fun {k} _ ψ φ' x' g t₁ t₂ h₁ h₂ => ?_⟩
  obtain ⟨rfl, rfl, h₁⟩ := h₁
  obtain ⟨-, -, h₂⟩ := h₂
  choose T₁ a₁ b₁ c₁ using h₁ τ
  choose T₂ a₂ b₂ c₂ using h₂ τ
  letI : Algebra R k := ψ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  change ∀ cc, vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec Z.t x xc cc at hv
  choose G hG using fun i => vec_exists hx' _ (g.tan τ i)
  have d₁ : ∀ i, G i = ∑ j, T₁ i j • (ψ ∘ e₁ j) := fun i => by
    have := c₁ i
    simp only [he₁, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have d₂ : ∀ i, G i = ∑ j, T₂ i j • (ψ ∘ e₂ j) := fun i => by
    have := c₂ i
    simp only [he₂, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have hind : ∀ a : Fin (Dw.mult τ) → k, ∑ i, a i • G i = 0 → a = 0 := fun a ha => by
    have hb := g.basis τ _ (vec_tan hx' 0) ((vec_eig_iff hx' _ _).2 (Submodule.zero_mem _))
    rw [show g.v τ = fun j => vec Z.t _ xc' (G j) from funext hG] at hb
    exact hb.unique ((comb_iff hx' _ _ _).2 ha.symm) ((comb_iff hx' _ _ _).2 (by simp))
  refine ⟨T₁, T₂, a₁, a₂, b₁, b₂, fun i k' => ?_⟩
  have := indep_of_tri b₁ (fun i => a₁ i ▸ (t₁ τ i).ne_zero) (e := fun j => ψ ∘ e₁ j)
    (fun a ha => hind a (by simpa only [d₁] using ha))
    (b := fun k' => T₁ i k' - ∑ j, T₂ i j * ψ (M j k')) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← d₁, d₂, sub_eq_zero]
      funext q

      simp only [hM', Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm)
  exact sub_eq_zero.1 (congrFun this k')

theorem exists_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, (t₁ τ i : k) = t₂ τ i * ψ (u τ i) := by
  obtain rfl : φ₁ = φ₂ := RingHom.ext fun a => hι ((RingHom.congr_fun h₁.2.1 a).symm.trans (RingHom.congr_fun h₂.2.1 a))
  choose M hM using exists_matrix f₁ f₂
  have hT : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hk => by
    obtain ⟨T₁, T₂, -, a₂, b₁, b₂, h⟩ := hM τ ι f₀ t₁ t₂ h₁ h₂
    exact hι ((tri_of_mul (M := fun i k => ι (M τ i k)) b₁ b₂ (fun i => a₂ i ▸ (t₂ τ i).ne_zero) h i k hk).trans
      (map_zero ι).symm)
  refine ⟨fun τ i => M τ i i, fun {k} _ ψ φ' x' g s₁ s₂ g₁ g₂ τ i => ?_⟩
  obtain ⟨T₁, T₂, a₁, a₂, -, b₂, h⟩ := hM τ ψ g s₁ s₂ g₁ g₂
  rw [← a₁, ← a₂, h]
  exact diag_of_mul (M := fun i k => ψ (M τ i k)) b₂ (fun i k hk => by simp only [hT τ i k hk, map_zero]) i

theorem exists_unit_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Rˣ, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, t₁ τ i = t₂ τ i * Units.map (ψ : R →* k) (u τ i) := by
  obtain ⟨u, hu⟩ := exists_ratio f₁ f₂ hι h₁ h₂
  obtain ⟨v, hv⟩ := exists_ratio f₂ f₁ hι h₂ h₁
  have huv : ∀ τ i, u τ i * v τ i = 1 := fun τ i => hι (by
    have a := hu ι f₀ _ _ h₁ h₂ τ i
    have b := hv ι f₀ _ _ h₂ h₁ τ i
    rw [a, mul_assoc] at b
    rw [map_mul, map_one]
    exact (mul_left_cancel₀ (t₂ τ i).ne_zero ((mul_one _).trans b)).symm)
  exact ⟨fun τ i => Units.mkOfMulEqOne _ _ (huv τ i), fun ψ _ _ g s₁ s₂ g₁ g₂ τ i =>
    Units.ext (hu ψ g s₁ s₂ g₁ g₂ τ i)⟩

end Frames

theorem isLocalHom_of_algebraic {R F k : Type} [CommRing R] [IsLocalRing R] [Field F] [CharZero F] (φ : F →+* R)
    [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k] (ψ : R →+* k) : IsLocalHom ψ := by
  letI : Algebra ℚ R := (φ.comp (algebraMap ℚ F)).toAlgebra
  let ψ' : R →ₐ[ℚ] k := { ψ with commutes' := fun q => by simp }
  refine ⟨fun a ha => ?_⟩
  have h0 : ψ a ≠ 0 := ha.ne_zero
  have hi : IsIntegral ℚ (ψ a) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hc := minpoly.coeff_zero_ne_zero hi h0
  have h1 : ψ (Polynomial.aeval a (minpoly ℚ (ψ a))) = 0 :=
    (Polynomial.aeval_algHom_apply ψ' a _).symm.trans (minpoly.aeval ℚ (ψ a))
  have h2 : ¬ IsUnit (Polynomial.aeval a (minpoly ℚ (ψ a))) := fun h => (h.map ψ).ne_zero h1
  by_contra hna
  rw [← Polynomial.X_mul_divX_add (minpoly ℚ (ψ a)), map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  have h3 : algebraMap ℚ R ((minpoly ℚ (ψ a)).coeff 0) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem (IsLocalRing.maximalIdeal R) h2
      (Ideal.mul_mem_right (Polynomial.aeval a (minpoly ℚ (ψ a)).divX) _ hna)
    rwa [add_sub_cancel_left] at this
  exact h3 (hc.isUnit.map _)

theorem stalk_ext {X : Scheme.{0}} {k : Type} [Field k] {y y' : X} {ψ : X.presheaf.stalk y →+* k}
    {ψ' : X.presheaf.stalk y' →+* k} (h : IsLocalHom ψ) (h' : IsLocalHom ψ')
    (e : spMap ψ ≫ X.fromSpecStalk y = spMap ψ' ≫ X.fromSpecStalk y') : y = y' ∧ HEq ψ ψ' := by
  have := (SpecToEquivOfLocalRing X (.of k)).symm.injective (a₁ := ⟨y, CommRingCat.ofHom ψ, h⟩)
    (a₂ := ⟨y', CommRingCat.ofHom ψ', h'⟩) e
  obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 this
  exact ⟨rfl, heq_of_eq (congrArg (fun f => f.1.hom) (eq_of_heq e'))⟩

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

end Coord

end GlobalTheory.ShFam.CoordUniq
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CechPic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.InvertIdeal

section General

variable {X : Scheme.{0}} [IsIntegral X]

theorem exists_mul_pow {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) (α : Γ(X, U))
    (hα : genericPoint X ∈ X.basicOpen α) {f : X.functionField} (hf : ∀ x ∈ X.basicOpen α, RegAt x f) :
    ∃ (n : ℕ) (γ : Γ(X, U)), fnOf U h γ = f * fnOf U h α ^ n := by
  obtain ⟨β, rfl⟩ := exists_fnOf_eq hα hf
  have := hU.isLocalization_basicOpen α
  obtain ⟨n, γ, e⟩ := IsLocalization.Away.surj α β
  refine ⟨n, γ, ?_⟩
  have e' := congrArg (fnOf _ hα) e
  rw [map_mul, map_pow] at e'
  have r (a : Γ(X, U)) : fnOf _ hα (algebraMap _ Γ(X, X.basicOpen α) a) = fnOf U h a :=
    fnOf_resG (X.basicOpen_le α) hα a
  rw [r, r] at e'
  exact e'.symm

theorem exists_denom {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) {x : X} (hx : x ∈ U)
    {f : X.functionField} (hf : RegAt x f) :
    ∃ β γ : Γ(X, U), x ∈ X.basicOpen β ∧ fnOf U h γ = f * fnOf U h β := by
  obtain ⟨W, hW, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨α, hle, hα⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hW⟩ hx
  obtain ⟨n, γ, e⟩ := exists_mul_pow hU h α (gen_mem hα) fun y hy => regAt_fnOf (hle hy) (gen_mem hW) a
  refine ⟨α ^ (n + 1), γ * α, by rwa [X.basicOpen_pow α n.succ_pos], ?_⟩
  rw [map_mul, e, map_pow, pow_succ, mul_assoc]


theorem exists_unitAt {x : X} {ι : Type} [Fintype ι] {c g : ι → X.functionField} (hc : ∀ i, RegAt x (c i))
    (hg : ∀ i, RegAt x (g i)) (e : ∑ i, c i * g i = 1) : ∃ i, UnitAt x (g i) := by
  by_contra! H
  have : ZeroAt x (∑ i, c i * g i) := Finset.sum_induction _ _ (fun _ _ => ZeroAt.add) (zeroAt_zero x) fun i _ =>
    mul_comm (g i) (c i) ▸ (zeroAt_iff.2 ⟨hg i, H i⟩).mul (hc i)
  exact (zeroAt_iff.1 (e ▸ this)).2 (unitAt_one x)

theorem exists_common_open {x : X} {ι : Type} [Finite ι] {g : ι → X.functionField} (hg : ∀ i, RegAt x (g i)) :
    ∃ (W : X.Opens) (hx : x ∈ W), ∀ i, ∃ a : Γ(X, W), fnOf W (gen_mem hx) a = g i := by
  choose U hU a ha using fun i => (hg i).exists_fnOf
  let W : X.Opens := ⟨⋂ i, U i, isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hle (i) : W ≤ U i := Set.iInter_subset (fun i => (U i : Set X)) i
  exact ⟨W, Set.mem_iInter.2 hU, fun i => ⟨resG X (hle i) (a i), (fnOf_resG _ _ _).trans (ha i)⟩⟩

end General

variable {F : Type} [Field F] [NumberField F]

end GlobalTheory.InvertIdeal
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Models (LevComp)

namespace GlobalTheory.LocM.Cocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}

theorem exists_sab_of_isTrans {i i₂ : Idx H p} {τ : (Y i₂).X ⟶ (Y i).X} {mu : SABMap (Y i₂).t (Y i).t τ}
    (h : IsTrans i i₂ τ mu) :
    ∃ (b : i.c.V W →+* i₂.c.V W) (r : (Xo i₂.l).XF i₂.c ⟶ (Xo i.l).XF i.c) (ν : SABMap (Y i₂).oF.t (Y i).oF.t r),
      IsIncl b ∧ (Y i₂).j ≫ τ = r ≫ (Y i).j ∧ τ ≫ (Y i).s = (Y i₂).s ≫ spMap b ∧
      ν.φ ≫ (Y i).m.φ = (Y i₂).m.φ ≫ mu.φ ∧ LevComp (Y i₂).oF (Y i).oF r ν := by
  obtain ⟨b, π', r, hb, h₁, h₂, -, h₃, h₄, h₅⟩ := h
  have e : τ ≫ (Y i).s = (Y i₂).s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨n, hn⟩ := LevelCover.sab_comp (Y i₂).m mu h₃
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel (Y i).m n r rfl
  refine ⟨b, r, ν, hb, h₃, e, hν.trans hn, fun a => ?_, fun a => ?_⟩
  · exact LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₄ a)
  · exact LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₅ a)

end GlobalTheory.LocM.Cocycle
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.isFrame_compose_ringHom_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  first | exact @GlobalTheory.ShFam.Pad.isFrame_baseChange | exact GlobalTheory.ShFam.Pad.isFrame_baseChange | (intros; apply GlobalTheory.ShFam.Pad.isFrame_baseChange <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtFam

open GlobalTheory.CechPic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem relAmple_iff_of_cls {S : Scheme.{0}} {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) : Out.RelAmple A M ↔ Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hL, relAmple_iff_isAmpleLB A hM]
  refine forall_congr' fun U => forall_congr' fun hU => ?_
  refine Iff.trans (isAmpleLB_congr (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)
    ((cls_eq_iff (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)).1 ?_)) (isAmpleLB_pow_iff (pull_isLB hL _) hd)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

section OneModel

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

theorem exists_keyAt (M : GChart Y) {R : Type} [CommRing R] {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hd : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, θ, ⟨hw, hr⟩, hθ, hne⟩ :=
    exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  have cast : ∀ (p q : Sp R ⟶ Y.X) (_ : p = q) (n : SABMap t Y.t p), ∃ n' : SABMap t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ _ (FlagMod.spMap_ev z M.hU hz).symm m
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp R) :=
    { A := t.G, g := M.n, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := hA, ktriv := hK
      isAb := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ _) m.base)
  have hrig : ∀ (e : Sp R ⟶ Y.X) (_ : m.cm.e = e) (he : eSec t.G ≫ m.φ = e ≫ eSec Y.t.G),
      rigPullOf m.φ e he Y.t.PP.L Y.t.PP.rig = m.cm.rigPull Y.t.PP.L Y.t.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨⟨P, hn, t.PP.rig, t.PP.rigGen, θ, fun s => ?_, v, hb⟩, rfl, m.φ, he, w, rfl, m.cart, hw, ?_,
    fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hne s
    exact ⟨g, hg, Opens.mem_iSup.2 ⟨i, hi⟩⟩
  · rw [hrig z m.base he]
    exact hr
  · exact (hθ (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))
  · rw [← hm']
    exact hv i

theorem exists_keyAt_of_point (M : GChart Y) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U) {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) {K : Type} [Field K] [CharZero K] (f : R →+* K) {x₀ : KeyIn K}
    (h₀ : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x₀) :
    ∃ x : KeyIn R, x.P.g = x₀.P.g ∧ KeyAt M z hz x := by
  obtain ⟨φ, -, w, hg, hc, hw, -⟩ := h₀
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : x₀.P.A.left ⟶ t.G.left, ψ ≫ m.φ = φ ∧ ψ ≫ t.G.hom = x₀.P.A.hom ≫ spMap f :=
    ⟨m.cart.1.lift φ (x₀.P.A.hom ≫ spMap f) (by rw [hc.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _,
      m.cart.1.lift_snd _ _ _⟩
  subst h₁
  have g : IsGrpPullback x₀.P.A t.G (spMap f) ψ := m.cart.cancel hc h₂
  have e : LBIso x₀.P.L (t.PP.L.pull ψ) :=
    LBIso.trans x₀.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB t.PP.isLB _) ⟨w, hw⟩
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ rfl).symm
  have hG : IsAbelianScheme t.G := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
  have q : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hK⟩ := KTrivGlob.exists_open t.PP.isLB x₀.P.isLB hG hA g e x₀.P.ktriv q
  have : CharZero R := f.charZero
  have : CharZero Γ(Sp R, ⊤) := charZero_of_injective_ringHom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  have kt := KTrivSpread.kTriv_of_open_integral GlobalTheory.firstFiveLaws.1 (Sp R) (fun n hn => Nat.cast_ne_zero.2 hn) U
    ⟨_, hU⟩ t.G t.PP t.cub hG hA hK
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (spMap f q))
  obtain rfl : d = M.n := (H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g.1 hd)
    x₀.P.smoothDim (eSec x₀.P.A q)).trans hg
  obtain ⟨x, hx, h⟩ := exists_keyAt M hz m hp hA kt hd (hg ▸ x₀.g_pos)
  exact ⟨x, hx.trans hg.symm, h⟩

end OneModel

end GlobalTheory.KeyAtFam
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.NRows.L0

theorem parts_positive_scalars_without_congruence_lengths : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → (Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D) ∧ GlobalTheory.NRows.LamUsed D := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost
  exact ⟨GlobalTheory.IsotSum.L0.isotInternal_of_read h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost,
    GlobalTheory.NRows.LamUsedProof.L0.main h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost⟩

end GlobalTheory.NRows.L0
end
