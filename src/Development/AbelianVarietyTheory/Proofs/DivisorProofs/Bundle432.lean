module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FibreRegular

theorem quot_localization_regular (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal R) [p.IsPrime] (n : Ideal S) [n.IsPrime]
    (hn : n.comap (algebraMap R S) = p) :
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime n))) := by
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  let N : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P} := ⟨⟨n, inferInstance⟩, PrimeSpectrum.ext hn⟩
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum (p.Fiber S),
      q.asIdeal.comap (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)) = n :=
    ⟨PrimeSpectrum.preimageEquivFiber R S P N,
      congrArg (fun z => z.1.asIdeal) ((PrimeSpectrum.preimageEquivFiber R S P).symm_apply_apply N)⟩
  subst hq
  have hreg : IsRegularRing (p.Fiber S) := GlobalTheory.isRegularRing_of_smooth p.ResidueField (p.Fiber S)
  have := isRegularRing_iff.mp hreg q.asIdeal
  exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ p q.asIdeal).toRingEquiv

end GlobalTheory.FibreRegular

namespace GlobalTheory.FibreRegular

theorem isRegularLocalRing_stalk_quot_maximalIdeal :
    ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) [Smooth π] (y : Y),
      IsRegularLocalRing (Y.presheaf.stalk y ⧸
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  intro X Y π _ y
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ π ⁻¹ᵁ U from hxU) (π ⁻¹ᵁ U).isOpen
  replace hWle : W ≤ π ⁻¹ᵁ U := hWle
  have hs : (π.appLE U W hWle).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) π inferInstance ⟨U, hU⟩ ⟨W, hW⟩ hWle
  letI := (π.appLE U W hWle).hom.toAlgebra
  haveI : Algebra.Smooth Γ(X, U) Γ(Y, W) := hs
  letI := X.presheaf.algebra_section_stalk (⟨π y, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨π y, hxU⟩
  letI := Y.presheaf.algebra_section_stalk (⟨y, hyW⟩ : W)
  haveI := hW.isLocalization_stalk ⟨y, hyW⟩
  set p := (hU.primeIdealOf ⟨π y, hxU⟩).asIdeal with hp
  set n := (hW.primeIdealOf ⟨y, hyW⟩).asIdeal with hn

  have e : ∀ r : Γ(X, U), (Y.presheaf.germ W y hyW).hom ((π.appLE U W hWle).hom r) =
      (π.stalkMap y).hom ((X.presheaf.germ U (π y) hxU).hom r) := by
    have e' : π.appLE U W hWle ≫ Y.presheaf.germ W y hyW =
        X.presheaf.germ U (π y) hxU ≫ π.stalkMap y := by
      refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap π U y hxU).symm
      rw [Scheme.Hom.appLE, Category.assoc, Y.presheaf.germ_res]
    intro r
    exact congr($(e').hom r)
  have hmemU : ∀ a : Γ(X, U), (X.presheaf.germ U (π y) hxU).hom a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (π y)) ↔ a ∈ p := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (π y)) p a
  have hmemW : ∀ a : Γ(Y, W), (Y.presheaf.germ W y hyW).hom a ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ↔ a ∈ n := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y) n a
  have hlies : n.comap (algebraMap Γ(X, U) Γ(Y, W)) = p := by
    ext r
    rw [Ideal.mem_comap, ← hmemW, ← hmemU]
    change (Y.presheaf.germ W y hyW).hom ((π.appLE U W hWle).hom r) ∈ _ ↔ _
    rw [e, ← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap]
  have hreg := quot_localization_regular Γ(X, U) Γ(Y, W) p n hlies

  have hI : (IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom =
      (p.map (algebraMap Γ(X, U) Γ(Y, W))).map (algebraMap Γ(Y, W) (Y.presheaf.stalk y)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (X.presheaf.stalk (π y)), Ideal.map_map,
      Ideal.map_map]
    congr 1
    ext r
    exact (e r).symm
  let eA := IsLocalization.algEquiv n.primeCompl (Y.presheaf.stalk y) (Localization.AtPrime n)
  let eS : Y.presheaf.stalk y ≃+* Localization.AtPrime n := eA.toRingEquiv
  have hcomp : (eS : Y.presheaf.stalk y →+* Localization.AtPrime n).comp
      (algebraMap Γ(Y, W) (Y.presheaf.stalk y)) = algebraMap Γ(Y, W) (Localization.AtPrime n) :=
    RingHom.ext fun r => eA.commutes r
  have hJ : (p.map (algebraMap Γ(X, U) Γ(Y, W))).map (algebraMap Γ(Y, W) (Localization.AtPrime n)) =
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom).map
        (eS : Y.presheaf.stalk y →+* Localization.AtPrime n) := by
    rw [hI, Ideal.map_map (algebraMap Γ(Y, W) (Y.presheaf.stalk y)), hcomp]
  exact IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquiv _ _ eS hJ).symm

end GlobalTheory.FibreRegular
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) (W₁ W₂ : Type) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] (σ : W₁ → H) (t : W₂ → H) (D₁ : W₁ →L[ℝ] (ι → Fin r → Fin r → ℂ)) (D₂ : W₂ →L[ℝ] (ι → Fin r → Fin r → ℂ)), σ 0 = 1 → t 0 = 1 → HasStrictFDerivAt (fun w => fun τ i j => ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₁ 0 → HasStrictFDerivAt (fun w => fun τ i j => ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₂ 0 → HasStrictFDerivAt (fun w : W₁ × W₂ => fun τ i j => ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂) + D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) 0 := by
  intro ι _ r H W₁ W₂ _ _ _ _ σ t D₁ D₂ hσ ht h₁ h₂
  set f₁ : W₁ → ι → Fin r → Fin r → ℂ := fun w τ i j =>
    ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf₁
  set f₂ : W₂ → ι → Fin r → Fin r → ℂ := fun w τ i j =>
    ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf₂
  have e : (fun w : W₁ × W₂ => fun τ i j =>
      ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) =
      fun w τ i j => ∑ c, f₁ w.1 τ i c * f₂ w.2 τ c j := by
    funext w τ i j
    simp [hf₁, hf₂, Matrix.mul_apply]
  have z₁ : ∀ τ i c, f₁ 0 τ i c = (1 : Matrix (Fin r) (Fin r) ℂ) i c := by
    intro τ i c; simp [hf₁, hσ]
  have z₂ : ∀ τ c j, f₂ 0 τ c j = (1 : Matrix (Fin r) (Fin r) ℂ) c j := by
    intro τ c j; simp [hf₂, ht]
  have g₁ : HasStrictFDerivAt (fun w : W₁ × W₂ => f₁ w.1)
      (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂)) (0 : W₁ × W₂) :=
    h₁.comp (0 : W₁ × W₂) (hasStrictFDerivAt_fst (p := (0 : W₁ × W₂)))
  have g₂ : HasStrictFDerivAt (fun w : W₁ × W₂ => f₂ w.2)
      (D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) (0 : W₁ × W₂) :=
    h₂.comp (0 : W₁ × W₂) (hasStrictFDerivAt_snd (p := (0 : W₁ × W₂)))
  rw [e]
  refine hasStrictFDerivAt_pi'.2 fun τ => hasStrictFDerivAt_pi'.2 fun i =>
    hasStrictFDerivAt_pi'.2 fun j => ?_
  have a₁ : ∀ c, HasStrictFDerivAt (fun w : W₁ × W₂ => f₁ w.1 τ i c)
      ((ContinuousLinearMap.proj c).comp ((ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.proj τ).comp (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂))))) 0 :=
    fun c => hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 g₁ τ) i) c
  have a₂ : ∀ c, HasStrictFDerivAt (fun w : W₁ × W₂ => f₂ w.2 τ c j)
      ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj c).comp
        ((ContinuousLinearMap.proj τ).comp (D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂))))) 0 :=
    fun c => hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 g₂ τ) c) j
  have hs0 := HasStrictFDerivAt.sum (u := Finset.univ) (A := fun c (w : W₁ × W₂) => f₁ w.1 τ i c * f₂ w.2 τ c j)
    (fun c _ => (a₁ c).mul (a₂ c))
  have ef : (fun w : W₁ × W₂ => ∑ c, f₁ w.1 τ i c * f₂ w.2 τ c j) =
      ∑ c, (fun (w : W₁ × W₂) => f₁ w.1 τ i c * f₂ w.2 τ c j) := by
    funext w
    simp [Finset.sum_apply]
  rw [ef]
  refine hs0.congr_fderiv ?_
  clear ef hs0 a₁ a₂ g₁ g₂ e
  clear_value f₁ f₂
  clear hf₁ hf₂ h₁ h₂ hσ ht σ t
  refine ContinuousLinearMap.ext fun w => ?_
  simp [z₁, z₂, Matrix.one_apply, Finset.sum_add_distrib, ite_mul]
  ring
end

section

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharSep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := (SplitWeil.isCompact_int k).exists_bound_of_continuousOn
    (f := fun y => ψ0 (x * y)) (hc.comp (continuous_const.mul continuous_id)).continuousOn
  have hpow : ∀ m : ℕ, ‖ψ0 x‖ ^ m ≤ B := fun m => by
    have hm : ((m : k)) ∈ 𝒪[k] := by
      simpa using (Subring.natCast_mem (𝒪[k]) m)
    have := hB _ hm
    rwa [show x * (m : k) = m • x by rw [nsmul_eq_mul, mul_comm], AddChar.map_nsmul_eq_pow, norm_pow] at this
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop B |>.exists
  exact absurd (hpow m) (not_le.mpr hm)

theorem norm_eq_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ = 1 := by
  have h1 := norm_le_one ψ0 hc x
  have h2 := norm_le_one ψ0 hc (-x)
  have hm : ψ0 x * ψ0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 x‖ * ‖ψ0 (-x)‖ = 1 := by rw [← norm_mul, hm, norm_one]
  by_contra hne
  have hlt : ‖ψ0 x‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖ψ0 x‖ * ‖ψ0 (-x)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
  linarith

def toCircle (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (h x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (show ψ0 (a + b) = ψ0 a * ψ0 b from AddChar.map_add_eq_mul ψ0 a b)

theorem toCircle_apply (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) (x : k) :
    ((toCircle ψ0 h x : Circle) : ℂ) = ψ0 x := rfl

theorem unitary_and_separates : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1 := by
  intro k _ _ _ _ ψ0 hc h1
  have hu := norm_eq_one ψ0 hc
  refine ⟨hu, fun a ha => ?_⟩
  set ψ := toCircle ψ0 hu
  have hψc : Continuous ψ := Continuous.subtype_mk hc _
  have hψ1 : ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [ψ, toCircle_apply] using this
  obtain ⟨c₀, hc₀⟩ := SplitWeil.exists_hasConductor_of_continuous ψ hψc hψ1
  have hx : a ∉ SplitWeil.cball (c₀ * c₀⁻¹) := by
    rw [mul_inv_cancel]
    intro h
    exact ha ((Valuation.mem_integer_iff _ _).mpr (by simpa [SplitWeil.cball] using h))
  obtain ⟨t, ht, hne⟩ := hc₀.exists_ne_one c₀ hx
  refine ⟨t, fun y hy => ?_, fun h => hne (Circle.ext (by simpa [ψ, toCircle_apply] using h))⟩
  have hy' : valuation k y ≤ 1 := hy
  have : t * y ∈ SplitWeil.cball c₀ := by
    simp only [SplitWeil.cball, Set.mem_setOf_eq, map_mul] at ht ⊢
    exact (mul_le_mul' le_rfl hy').trans (by rw [mul_one]; exact ht)
  have := hc₀.eq_one this
  simpa [ψ, toCircle_apply] using congrArg (fun z : Circle => (z : ℂ)) this

end GlobalTheory.CharSep
end
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem weighted_lintegral_sobolev_pointwise : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ), finrank ℝ E = m + 1 → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0)) → ∀ (k : ℕ) (x : E), ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
  intro E _ _ _ _ _ μ _ m hdim
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set B : Set E := Metric.closedBall (0:E) 1 with hB
  set β : ℝ≥0∞ := μ B with hβ
  have hβ0 : β ≠ 0 := (Metric.measure_closedBall_pos μ (0:E) one_pos).ne'
  have hβtop : β ≠ ∞ := (measure_closedBall_lt_top).ne
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (m.factorial : ℝ)) * ENNReal.ofReal (1 / ((m : ℝ) + 1)) with hc
  refine ⟨2 * c / β, ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hβ0, ?_⟩
  intro F _ _ _ G hG hdec k x
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector'' ℝ x
  set S : Set E := B ∩ {v | 0 ≤ φ v} with hS
  have hSmeas : MeasurableSet S :=
    Metric.isClosed_closedBall.measurableSet.inter (measurableSet_le measurable_const φ.continuous.measurable)
  open scoped Pointwise in
  have hβS : β ≤ 2 * μ S := by
    have hsub : B ⊆ S ∪ -S := by
      intro v hv
      by_cases h : 0 ≤ φ v
      · exact Or.inl ⟨hv, h⟩
      · right
        refine ⟨?_, ?_⟩
        · simpa [hB, Metric.mem_closedBall, norm_neg] using hv
        · show 0 ≤ φ (-v)
          rw [map_neg]
          linarith [not_le.mp h]
    calc β ≤ μ (S ∪ -S) := measure_mono hsub
      _ ≤ μ S + μ (-S) := measure_union_le _ _
      _ = 2 * μ S := by rw [Measure.measure_neg, two_mul]
  have hDc : Continuous (fun z => ‖iteratedFDeriv ℝ (m + 1) G z‖) :=
    (hG.continuous_iteratedFDeriv (by exact_mod_cast (le_top : ((m+1 : ℕ) : ℕ∞) ≤ ⊤))).norm
  set Ψ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (‖x + y‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + y)‖) with hΨ
  have hΨm : Measurable Ψ := by
    apply ENNReal.measurable_ofReal.comp
    exact (((continuous_const.add continuous_id).norm.pow k).mul
      (hDc.comp (continuous_const.add continuous_id))).measurable
  set a : ℝ≥0∞ := ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) with ha
  set H : E → ℝ≥0∞ := fun v => ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) with hH
  have hpt : ∀ v ∈ S, v ≠ 0 → a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := by
    intro v hvS hv0
    have hray : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0) := by
      intro j hj
      refine (hdec j hj).comp ?_
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have h1 : Tendsto (fun t : ℝ => t * ‖v‖ + -‖x‖) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hvpos)
      refine tendsto_atTop_mono (fun t => ?_) h1
      have e1 : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
        simpa using norm_sub_le (x + t • v) x
      have e2 : t * ‖v‖ ≤ ‖t • v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg v)
      show t * ‖v‖ + -‖x‖ ≤ ‖x + t • v‖
      linarith
    have hR := GlobalTheory.T.norm_le_lintegral_ray_iteratedFDeriv' G m x v hG hray
    have hxk : (0:ℝ) ≤ ‖x‖ ^ k := by positivity
    calc a = ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal ‖G x‖ := by rw [ha, ENNReal.ofReal_mul hxk]
      _ ≤ ENNReal.ofReal (‖x‖ ^ k) * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
            (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by gcongr
      _ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
            (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (m.factorial : ℝ)) *
            (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v)) := by
          refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
          have ht0 : (0:ℝ) ≤ t := le_of_lt ht
          have hmono : ‖x‖ ≤ ‖x + t • v‖ := by
            have h1 : φ x ≤ φ (x + t • v) := by
              rw [map_add (f := _), map_smul, smul_eq_mul]
              have : 0 ≤ φ v := hvS.2
              nlinarith
            have h2 : φ (x + t • v) ≤ ‖x + t • v‖ := by
              calc φ (x + t • v) ≤ |φ (x + t • v)| := le_abs_self _
                _ = ‖φ (x + t • v)‖ := (Real.norm_eq_abs _).symm
                _ ≤ ‖φ‖ * ‖x + t • v‖ := φ.le_opNorm _
                _ ≤ 1 * ‖x + t • v‖ := mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _)
                _ = ‖x + t • v‖ := one_mul _
            have h0 : φ x = ‖x‖ := by simpa using hφx
            linarith
          have hpow : ‖x‖ ^ k ≤ ‖x + t • v‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) hmono k
          have hfac : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
          have hP : 0 ≤ t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖) := by positivity
          have hA : 0 ≤ t ^ m * ‖v‖ ^ (m + 1) := by positivity
          have hf : 0 ≤ 1 / (m.factorial : ℝ) := by positivity
          show ENNReal.ofReal (‖x‖ ^ k) * ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) ≤
            ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) *
              ENNReal.ofReal (‖x + t • v‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖))
          rw [← ENNReal.ofReal_mul hxk, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hf]
          apply ENNReal.ofReal_le_ofReal
          have e : 1 / (m.factorial : ℝ) * (t ^ m * ‖v‖ ^ (m + 1) * (‖x + t • v‖ ^ k *
              ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) = ‖x + t • v‖ ^ k * (t ^ m / (m.factorial : ℝ) *
              (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right hpow hP
      _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hae : ∀ᵐ v ∂(μ.restrict S), a ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v := by
    rw [ae_restrict_iff' hSmeas]
    have h0 : ∀ᵐ v ∂μ, v ≠ (0:E) := by
      rw [ae_iff]
      simp [measure_singleton]
    filter_upwards [h0] with v hv0 hvS
    exact hpt v hvS hv0
  have hI : ∫⁻ y, Ψ y ∂μ = ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ :=
    lintegral_add_left_eq_self (μ := μ) (fun z => ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖)) x
  have hmain : μ S * a ≤ c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
    calc μ S * a = ∫⁻ _ in S, a ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ v in S, ENNReal.ofReal (1 / (m.factorial : ℝ)) * H v ∂μ := lintegral_mono_ae hae
      _ = ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ v in S, H v ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * ∫⁻ v in B, H v ∂μ := by
          gcongr
          exact inter_subset_left
      _ ≤ ENNReal.ofReal (1 / (m.factorial : ℝ)) * (ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ) := by
          gcongr
          exact GlobalTheory.T.lintegral_unit_ball_ray_average_le μ Ψ m hΨm hdim
      _ = c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
          rw [hI, hc, mul_assoc]
  have h2 : a * β ≤ 2 * (c * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ) := by
    calc a * β ≤ a * (2 * μ S) := by gcongr
      _ = 2 * (μ S * a) := by ring
      _ ≤ _ := by gcongr
  have h3 := (ENNReal.le_div_iff_mul_le (Or.inl hβ0) (Or.inl hβtop)).mpr h2
  calc a ≤ _ := h3
    _ = 2 * c / β * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring

end GlobalTheory
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_sq_add_prime_odd_mod_three_unit :
    ∀ (p : ℕ) (V : ValuationSubring ℂ), p.Prime → 3 < p →
      ∃ a N : ℕ, N = a ^ 2 + p ∧ Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 := by
  intro p V hp h3
  have h2 : p % 2 = 1 := by
    by_contra h
    rcases hp.eq_one_or_self_of_dvd 2 (by omega) with h' | h' <;> omega
  have h3' : p % 3 ≠ 0 := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 (by omega) with h' | h' <;> omega
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ 2 + p) (4 ^ 2 + p) := by
      have hg1 := Nat.gcd_dvd_left (2 ^ 2 + p) (4 ^ 2 + p)
      have hg2 := Nat.gcd_dvd_right (2 ^ 2 + p) (4 ^ 2 + p)
      have h12 : Nat.gcd (2 ^ 2 + p) (4 ^ 2 + p) ∣ 12 := by
        have := Nat.dvd_sub hg2 hg1
        have e : 4 ^ 2 + p - (2 ^ 2 + p) = 12 := by omega
        rwa [e] at this
      have hle := Nat.le_of_dvd (by norm_num) h12
      unfold Nat.Coprime
      generalize Nat.gcd (2 ^ 2 + p) (4 ^ 2 + p) = g at hg1 hg2 h12 hle
      norm_num at hg1 hg2
      interval_cases g <;> omega
    rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with hv | hv
    · exact ⟨2, 2 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
    · exact ⟨4, 4 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
  · have hcop : Nat.Coprime (0 ^ 2 + p) (6 ^ 2 + p) := by
      have hg1 := Nat.gcd_dvd_left (0 ^ 2 + p) (6 ^ 2 + p)
      have hg2 := Nat.gcd_dvd_right (0 ^ 2 + p) (6 ^ 2 + p)
      have h36 : Nat.gcd (0 ^ 2 + p) (6 ^ 2 + p) ∣ 36 := by
        have := Nat.dvd_sub hg2 hg1
        have e : 6 ^ 2 + p - (0 ^ 2 + p) = 36 := by omega
        rwa [e] at this
      have hle := Nat.le_of_dvd (by norm_num) h36
      unfold Nat.Coprime
      generalize Nat.gcd (0 ^ 2 + p) (6 ^ 2 + p) = g at hg1 hg2 h36 hle
      norm_num at hg1 hg2
      interval_cases g <;> omega
    rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with hv | hv
    · exact ⟨0, 0 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
    · exact ⟨6, 6 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩

end GlobalTheory.CMModel
end
