module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle482
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle050
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOne
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle812
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle814
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.IncomingBounds.Bundle001
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.HeightOneHom

theorem primitive_apply_mul {k C : Type} [Field k] [CommRing C] [HopfAlgebra k C]
    [IsCocomm k C] [Module.Finite k C] {φ : CartierDual k C} (hφ : cobOne k (CartierDual k C) φ = 0) (a b : C) :
    φ.ofConv (a * b) = counitAlgHom k C a • φ.ofConv b + counitAlgHom k C b • φ.ofConv a := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff] at hφ
  have h := hφ a b
  rw [map_add (f := _), LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply] at h
  change φ (a * b) = _
  rw [← h]
  simp only [counitAlgHom_apply, smul_eq_mul]
  ring

theorem eq_algebraMap_counit_of_cotMap_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
    (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D]
    (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 →
    ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  intro p _ k _ _ C _ _ _ _ D _ _ _ _ f hpow hcot d
  have hgen := GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p k C hpow
  have hzero : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → ∀ x, φ (f x) = 0 := by
    intro φ hφ x
    have h1 := AugCot.lift_d (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (f x)
    have h2 : dUnit (R := k) (f x) = 0 := by
      rw [← cotMap_d f x, hcot, LinearMap.zero_apply]
    change φ.ofConv (f x) = 0
    rw [← h1]
    change AugCot.lift (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (dUnit (R := k) (f x)) = 0
    rw [h2, map_zero]
  have hone : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → φ 1 = 0 := by
    intro φ hφ
    have := AugCot.pointDer_algebraMap (primitive_apply_mul hφ) (1 : k)
    rwa [map_one] at this
  let T : CartierDual k C →ₐ[k] CartierDual k D :=
    (Algebra.ofId k _).comp (counitAlgHom k (CartierDual k C))
  have hT : ∀ φ : CartierDual k C, ∀ x : D, T φ x = φ 1 * counit (R := k) x := by
    intro φ x
    change (algebraMap k (CartierDual k D) (counit (R := k) φ)) x = _
    rw [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]
    change φ 1 • (1 : CartierDual k D) x = _
    rw [CartierDual.one_apply, smul_eq_mul]
  have hM : (CartierDual.map f : CartierDual k C →ₐ[k] CartierDual k D) = T := by
    refine AlgHom.ext_of_adjoin_eq_top hgen fun φ hφ => ?_
    refine CartierDual.ext_apply fun x => ?_
    change CartierDual.map f φ x = T φ x
    rw [CartierDual.map_apply, hT, hzero φ hφ x, hone φ hφ, zero_mul]
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  have h1 : CartierDual.map f φ d = T φ d := by
    rw [← hM]; rfl
  rw [CartierDual.map_apply, hT] at h1
  rw [h1, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.HeightOneHom
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

open scoped nonZeroDivisors

theorem GlobalTheory.UCls.selfDual_latOf_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  intro E _ _ _ r G Λ g0 hΛ hua
  obtain ⟨hG, hdet, hfg, hspan, hsd⟩ := hΛ
  obtain ⟨hunit, hpres⟩ := hua
  let g : GL (Fin r) (RA (maximalRealSubfield E) E) := Matrix.nonsingInvUnit g0 hunit
  have hg : (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) = g0 := rfl
  obtain ⟨L, hL, hLfg, hLspan, hLhat⟩ :=
    GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E r Λ g hfg hspan
  rw [hg] at hL hLhat
  have hmem : ∀ x : E, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ x := by
    intro x
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.isIntegral_coe
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hsd' : ∀ v : Fin r → E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * G a b * (IsCMField.complexConj E) (y b)) ∈
      (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔ v ∈ Λ := by
    intro v
    simp only [hmem]
    exact hsd v
  have key := GlobalTheory.AdLat.latOf_selfDual (maximalRealSubfield E) E r Λ (IsCMField.complexConj E) G 1 g
    hfg hspan (IsCMField.complexConj_apply_apply E) hG hdet one_ne_zero hsd' (by rw [hg]; exact hpres)
  rw [hg] at key
  refine ⟨L, hL, hLhat, hG, hdet, hLfg, hLspan, fun x => ?_⟩
  have := key x
  rw [← hL] at this
  simp only [hmem, SetLike.mem_coe] at this
  exact this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_complex_linear_of_pure_types_of_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La) (N : ℕ), 0 < N → (∀ v : D.La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) → (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ N hN hsp h₁ h₂
  obtain ⟨r, hr⟩ := exists_real_extension_of_lattice P hP.2.1 hP.2.2.1 hP.2.2.2.1
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  have hr' : ∀ a, r (P a) = P' (Φ a) := hr
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hre : H.rt0.re = 0 ∧ H.rt0.im ≠ 0 := by
    have e₁ := congrArg Complex.re H.sqrt_neg_disc_sq
    have e₂ := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [pow_two] at e₁ e₂
    have him : H.rt0.im ≠ 0 := fun h => by
      rw [h] at e₁; nlinarith [mul_self_nonneg H.rt0.re]
    refine ⟨?_, him⟩
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hρ : H.rt0 = (H.rt0.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre.1]
  have key : ∀ (ρ : ℂ) (a : D.La), a ∈ lat hP ρ → Φ a ∈ lat hP' ρ → r (ρ • P a) = ρ • r (P a) := by
    intro ρ a ha ha'
    rw [← period_rt_smul hP ha, hr', hr', map_smul, period_rt_smul hP' ha']
  have hPN : ∀ a, r (H.rt0 • P (N • a)) = H.rt0 • r (P (N • a)) := by
    intro a
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hsp a)
    rw [← hxy]
    have k₁ := key _ x hx (h₁ x hx)
    have k₂ := key _ y hy (h₂ y hy)
    rw [neg_smul, neg_smul, map_neg, neg_inj] at k₂
    rw [map_add (f := _), smul_add, map_add (f := _), map_add (f := _), smul_add, k₁, k₂]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hP0 : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    have h := hPN a
    rw [map_nsmul, smul_comm H.rt0 N, map_nsmul, map_nsmul, smul_comm H.rt0 N,
      ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h
    exact smul_right_injective _ hNc h
  have h0 : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range P) := by rw [hP.2.2.2.1]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hP0 a
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
    | smul c x _ hx => rw [smul_comm, r.map_smul, r.map_smul, hx, smul_comm]
  have hI : ∀ v, r (Complex.I • v) = Complex.I • r v := by
    intro v
    have := h0 v
    rw [hρ, mul_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_smul] at this
    exact smul_right_injective _ hre.2 this
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r
      map_add' := r.map_add
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← Complex.re_add_im c, add_smul, add_smul, mul_smul, mul_smul, Complex.coe_smul,
          Complex.coe_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul, hI] }
  have hsurj : Function.Surjective L := by
    show Function.Surjective r
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hP'.2.2.2.1, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨P (Φ.symm a), by rw [hr', Φ.apply_symm_apply]⟩
  exact ⟨LinearEquiv.ofBijective L ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩, fun a => (hr' a).symm⟩

end GlobalTheory.CompRat
end

section

open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.UpperBoundDescent

theorem desc : ∀ (p : ℕ) [Fact p.Prime] (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ¬ IsUnit (p : T.V) → ∀ (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ) (FT : Fin dd → PS T.V 2 dd) (actT : OE → Fin dd → PS T.V 1 dd), UpFBr.UpFLaw p T'.V OE dd (fun i => MvPowerSeries.map φ (FT i)) (fun a i => MvPowerSeries.map φ (actT a i)) → UpFBr.UpFLaw p T.V OE dd FT actT := by
  intro p _ T T' φ hφ hfin hp OE _ _ dd FT actT h C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hb hf r W hW j
  have hinj : Function.Injective ((algebraMap O C).comp iota) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hp0 : (p : T.V) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    obtain ⟨m, u', hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
    have h1 : ((algebraMap O C).comp iota) ϖ = 0 := by
      rw [map_mul, map_pow, mul_eq_zero] at ha
      rcases ha with ha | ha
      · exact absurd ha (u.isUnit.map _).ne_zero
      · exact pow_eq_zero_iff'.1 ha |>.1
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp (by rw [hm]; simp)
    have h2 := congrArg ((algebraMap O C).comp iota) hm
    rw [map_natCast, map_mul, map_pow, h1, zero_pow hm0, mul_zero] at h2
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h2)
  obtain ⟨ι', hl, hc⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ hφ hfin.to_isIntegral iota hinj
  have key : ∀ {σ : Type} (f : MvPowerSeries σ T.V),
      MvPowerSeries.map ι' (MvPowerSeries.map φ f) = MvPowerSeries.map iota f := by
    intro σ f
    ext n
    simp only [MvPowerSeries.coeff_map, ← hc, RingHom.comp_apply]
  have := h C v O hv ι' hl w t hb hf r W (by simpa only [key] using hW) j
  simpa only [key] using this

end GlobalTheory.UpperBoundDescent
end

section

open Formalism.L2.DIV

namespace GlobalTheory.CuspMult

theorem idemOf_coeff_real : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ)
    (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X →
    ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  intro K G _ _ _ σ X hX hS g

  rw [coeff_idemOf, map_sum, star_sum]
  refine Finset.sum_nbij' (fun χ t => χ t⁻¹) (fun χ t => χ t⁻¹) hS hS
    (fun χ _ => by simp) (fun χ _ => by simp) fun χ hχ => ?_
  have h1 := (hX χ hχ).map_inv σ 1
  have h2 := (hX χ hχ).map_inv σ g⁻¹
  simp only [map_mul, map_div₀, map_natCast, star_mul', star_div₀, star_natCast]
  rw [h1, h2]
  rfl

end GlobalTheory.CuspMult
end

section

open NumberField

noncomputable section

namespace GlobalTheory.CovTop

open Formalism.L2.DIV

theorem prod_hom_pow_eq_one {H M ι : Type} [Group H] [CommMonoid M] (s : Finset ι) (f : ι → H →* M) (N : ℕ)
    (h : ∀ i x, f i x ^ N = 1) (x : H) : (∏ i ∈ s, f i) x ^ N = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have ih' : (∏ i ∈ s, f i x) ^ N = 1 := by simpa using ih
    simp [hi, mul_pow, h, ih']

theorem ofLocal_chi_pow {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (Hl : (PP : Pg) → Subgroup (GL (Fin r) (kP PP.1))) (cl : (PP : Pg) → Hl PP →* LLˣ) (N : ℕ)
    (h : ∀ PP x, cl PP x ^ N = 1) (g : (LevelP.ofLocal Hl cl).H) : (LevelP.ofLocal Hl cl).chi g ^ N = 1 :=
  prod_hom_pow_eq_one (H := Subgroup.pi Set.univ Hl) Finset.univ _ N (fun PP x => h PP _) g

theorem unipotentTypeLevel_char_pow_eq_one {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : (PP : Pl E) → AddChar (kP PP) LL) (N : ℕ) (hN : ∀ PP : Pg, (N : kP PP.1) = 0)
    (g : (P0 Pg r ψ).H) : (P0 Pg r ψ).chi g ^ N = 1 := by
  refine ofLocal_chi_pow _ _ N (fun PP x => ?_) g
  apply Units.ext
  simp only [addCharHom, Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits, Units.val_one, MonoidHom.comp_apply,
    AddChar.toMonoidHom_apply]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hN PP, zero_mul, AddChar.map_zero_eq_one]

theorem det_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

end GlobalTheory.CovTop
end
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (χ : G → K), IsAbsIrrChar χ → ∀ (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ), ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) = (Fintype.card P : K) → ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧ Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
  first | exact @GlobalTheory.MultOneRealised.exists_rep_of_mult_one | exact GlobalTheory.MultOneRealised.exists_rep_of_mult_one | (intros; apply GlobalTheory.MultOneRealised.exists_rep_of_mult_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree

namespace GlobalTheory.BigOn

theorem canonical_error_real {ι J : Type} [Fintype J] (T : Finset ι) (I F err err0 J0 : ι → J → ℝ)
    (e c l : ι → ℝ) (D E E' : ℝ) (hD : 0 < D) (he : ∀ w, 0 < e w) (hl : ∀ w, 0 ≤ l w) (hE : 2 * E ≤ E')
    (hJ : ∀ w ∈ T, ∀ j, 0 ≤ J0 w j)
    (h0 : ∀ w j, err0 w j =
      max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) / (e w * (Fintype.card J : ℝ)))
    (h1 : ∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err w j) + c w) * D)
    (h2 : ∀ w ∈ T, ∀ j, 0 ≤ err w j)
    (h3 : ∀ j, ∑ w ∈ T, l w * (e w * err w j + e w * J0 w j) ≤ E) :
    (∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err0 w j) + c w) * D) ∧
    (∀ w ∈ T, ∀ j, 0 ≤ err0 w j) ∧
    ∀ j, ∑ w ∈ T, l w * (e w * err0 w j + e w * J0 w j) ≤ E' := by
  refine ⟨fun w hw => ?_, fun w _ j => ?_, fun j => ?_⟩
  · rcases isEmpty_or_nonempty J with hJe | hJn
    · simpa using h1 w hw
    · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
      have hew := he w
      have hs : ∑ j, e w * err0 w j =
          max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        simp only [h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      rw [Finset.sum_add_distrib, hs, ← div_le_iff₀ hD]
      have := le_max_right 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w)
      linarith
  · rw [h0]
    exact div_nonneg (le_max_left _ _) (mul_nonneg (he w).le (Nat.cast_nonneg _))
  · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨j⟩)
    have hA : ∀ w ∈ T, (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) ≤ ∑ j', l w * (e w * err w j') := by
      intro w hw
      have hew := he w
      have hs : (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) =
          l w * max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        rw [h0]; field_simp
      rw [hs, ← Finset.mul_sum _ _ (l w)]
      refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (hl w)
      · exact Finset.sum_nonneg fun j' _ => mul_nonneg hew.le (h2 w hw j')
      · have h := h1 w hw
        rw [Finset.sum_add_distrib, ← div_le_iff₀ hD] at h
        linarith
    have hB : ∀ j', ∑ w ∈ T, l w * (e w * err w j') ≤ E := fun j' =>
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg (he w).le (hJ w hw j'))) (hl w)) (h3 j')
    have hC : ∑ w ∈ T, l w * (e w * J0 w j) ≤ E :=
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (he w).le (h2 w hw j))) (hl w)) (h3 j)
    have hF : (Fintype.card J : ℝ) * ∑ w ∈ T, l w * (e w * err0 w j) ≤ (Fintype.card J : ℝ) * E := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum hA) ?_
      rw [Finset.sum_comm]
      refine le_trans (Finset.sum_le_sum fun j' _ => hB j') ?_
      simp
    have hG := le_of_mul_le_mul_left hF hn
    simp only [mul_add, Finset.sum_add_distrib]
    linarith

theorem on_of_onWith_canonical :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (Z : IndefScale Bs) (C C' CH CH' : ℝ) (err : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ), 0 < S.D → 0 ≤ Z.E1u → 2 * C ≤ C' → (∀ w ∈ S.Tw, ∀ j, 0 ≤ Z.J0 (S.μ w) w j) → (∀ w j, S.err0 w j = max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) - ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * Z.F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) / ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))) → ONwith S (Z.num C CH) err → S.ON (Z.num C' CH') := by
  intro K _ _ _ Bs Df S Z C C' CH CH' err hD hE hC hJ h0 h
  rw [on_iff_with]
  obtain ⟨h1, h2, h3⟩ := h
  exact canonical_error_real S.Tw
    (fun w j => (S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ)) Z.F0 err S.err0
    (fun w j => Z.J0 (S.μ w) w j) (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ))
    (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) (fun w => Formalism.DivisionValues.lw w) (S.D : ℝ)
    (C * Z.E1u) (C' * Z.E1u) (by exact_mod_cast hD) (fun w => ramw_pos w) (fun w => (lw_pos w).le)
    (by nlinarith [mul_le_mul_of_nonneg_right hC hE]) hJ h0 h1 h2 h3

end GlobalTheory.BigOn
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualNumber_unit_translate_eq_id_field_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  first | exact @GlobalTheory.InfTranslPts.transl_points | exact GlobalTheory.InfTranslPts.transl_points | (intros; apply GlobalTheory.InfTranslPts.transl_points <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.tensor_map_nilpotent_sub_and_pow_of_projection : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A : Type) [CommRing A] [Algebra k A] (π : A →ₐ[k] A), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : A ⊗[k] A, IsNilpotent (a - Algebra.TensorProduct.map π π a)) ∧ ∀ a : A ⊗[k] A, ∃ b : A ⊗[k] A, Algebra.TensorProduct.map π π a = Algebra.TensorProduct.map π π b ^ p) := by
  first | exact @GlobalTheory.tensorSquare_perfectProjection | exact GlobalTheory.tensorSquare_perfectProjection | (intros; apply GlobalTheory.tensorSquare_perfectProjection <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_closedSubscheme_finite_intersection : ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H), (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h := by
  first | (exact @GlobalTheory.closedSubscheme_iInter_exists) | (exact GlobalTheory.closedSubscheme_iInter_exists) | (intros; apply GlobalTheory.closedSubscheme_iInter_exists  <;> assumption)
end
