module

import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle588
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.EtaleCohomology.TateTwists.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Bundle002
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle539
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle540
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.Connected
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

open NumberField MeasureTheory

namespace GlobalTheory.CMTypeNorm

theorem place_bijective {K : Type} [Field K] [NumberField K] {I : Type} {φ : I → K →+* ℂ} (h : GlobalTheory.CMVal.IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by
  apply GlobalTheory.CMVal.Model.IsCMType.bijective <;> assumption

theorem prod_norm_sq_eq_absNorm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K,
        ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  intro K _ _ _ I _ φ h α
  have h1 : ∏ i, ‖φ i (α : K)‖ ^ 2 = ∏ w : InfinitePlace K, w (α : K) ^ w.mult := by
    refine Fintype.prod_bijective _ (place_bijective h) _ _ fun i => ?_
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  rw [h1, InfinitePlace.prod_eq_abs_norm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

end GlobalTheory.CMTypeNorm
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroBC

theorem preimage_surj : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  apply GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug <;> assumption

end GlobalTheory.SqZeroBC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exactIff_loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem exactIff_map_comp {R : Type} [CommRing R] {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem exactIff_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have := congrArg (fun m => m.hom x) (φ.hom.naturality g.op)
  simpa using this

theorem exactIff_kernel_sec {R : Type} [CommRing R] {G K : Shv R} (ψ : G ⟶ K) {U : Scheme.{0}}
    (b : Sec G U) (hb : Sec.map ψ b = 0) : ∃ k : Sec (kernel ψ) U, Sec.map (kernel.ι ψ) k = b := by
  let Φ : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
    sheafToPresheaf Scheme.etaleTopology _ ⋙ (evaluation _ _).obj (op U)
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel ψ)
  have hTm : Mono T.f := inferInstanceAs (Mono (kernel.ι ψ))
  have hP : PreservesLimit (parallelPair T.g 0) Φ := inferInstanceAs (PreservesLimit (parallelPair ψ 0) Φ)
  have h2 := (ShortComplex.moduleCat_exact_iff _).1 (hT.map_of_mono_of_preservesKernel Φ hTm hP) b hb
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, hk⟩

theorem exactIff : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  apply LateralTheory.EtaleFoundations.acycIffPf.exact_iff <;> assumption

end GlobalTheory.EtC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.ConnOpen

theorem isOpen_connectedComponent_noetherian {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    IsOpen (connectedComponent y) := by
  apply CrystallineSemistableComparison.isOpen_connectedComponent_of_noetherianSpace <;> assumption

end GlobalTheory.ConnOpen

theorem GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian :
    ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  intro X hX x
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let y' : (U : Set X) := ⟨y, hyU⟩
  refine ⟨Subtype.val '' connectedComponent y', ?_,
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian y'),
    ⟨y', mem_connectedComponent, rfl⟩⟩
  have hc : _root_.IsPreconnected (Subtype.val '' connectedComponent y' : Set X) :=
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have := hc.subset_connectedComponent ⟨y', mem_connectedComponent, rfl⟩
  rwa [← connectedComponent_eq hy] at this
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

theorem _root_.GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f g : V ⟶ W), (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map g → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map g := by
  first | exact @GlobalTheory.baseChange_map_eq_of_fieldExtension | exact GlobalTheory.baseChange_map_eq_of_fieldExtension | (intros; apply GlobalTheory.baseChange_map_eq_of_fieldExtension <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

theorem _root_.GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [AddCommGroup A] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (f : splitTorus (Spec (CommRingCat.of R)) A ⟶ G), IsMonHom f → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map 1 → ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f = (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map 1 := by
  first | exact @GlobalTheory.splitTorus_hom_trivial_mod_pow | exact GlobalTheory.splitTorus_hom_trivial_mod_pow | (intros; apply GlobalTheory.splitTorus_hom_trivial_mod_pow <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

theorem _root_.GlobalTheory.T.closedImmersion_of_baseChange_field_ext : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f : V ⟶ W), IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left → IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left := by
  first | exact @GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension | exact GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension | (intros; apply GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension <;> assumption)
end

section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.RootDiscrExp

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem finrank_le_two_mul_padicValInt_discr (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (hp : p.Prime) (hd : (p : ℤ) ∣ discr E) : Module.finrank ℚ E ≤ 2 * padicValInt p (discr E) := by
  classical
  have := Fact.mk hp
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  obtain ⟨a, m, hm, hdisc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have ha : padicValInt p (discr E) = a := by
    rw [padicValInt, hdisc, Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hm
    have h1 := Int.natCast_dvd.1 hd
    rwa [hdisc, pow_zero, one_mul] at h1
  have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨P, hPmax, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hP : P.IsPrime := hPmax.isPrime
  have hpP : (p : 𝓞 E) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by
      rw [← hPo.over]
      exact Ideal.mem_span_singleton_self _
    rwa [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  have h := diffExp E p a m hp hm hdisc P hP hpP
  have hpos := count_span_pos E p hp hP hpP
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hI0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := span_nat_ne_bot p
  have hdvd : P ^ (multiplicity P (Ideal.span {(p : 𝓞 E)}) - 1) ∣ differentIdeal ℤ (𝓞 E) := by
    refine pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P _ hp0 ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact pow_multiplicity_dvd _ _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) p ((Submodule.mem_bot _).1 hpP)
  have fD := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP0 hP) hD0
  have hd' := fD.le_multiplicity_of_pow_dvd hdvd
  have hc : ∀ X : Ideal (𝓞 E), X ≠ ⊥ → (normalizedFactors X).count P = multiplicity P X := fun X hX =>
    (⟨P, hP, hP0⟩ : HeightOneSpectrum (𝓞 E)).count_normalizedFactors_eq_multiplicity hX
  rw [hc _ hD0, hc _ hI0] at h
  rw [hc _ hI0] at hpos
  rw [ha]
  generalize multiplicity P (differentIdeal ℤ (𝓞 E)) = k at h hd'
  generalize multiplicity P (Ideal.span {(p : 𝓞 E)}) = e at h hd' hpos
  generalize Module.finrank ℚ E = n at h ⊢
  have hk : k ≠ 0 := by
    rintro rfl
    have : a * e ≠ 0 := mul_ne_zero ha0 hpos.ne'
    apply this
    nlinarith
  have hek : e ≤ 2 * k := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  nlinarith [Nat.mul_le_mul_left n hek]

theorem half_le_delta_two_vp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type)
    [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ →
    (1 / 2 : ℝ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E 2 := by
  intro E _ _ _ _ I _ d φ h
  have h1 := finrank_le_two_mul_padicValInt_discr E 2 Nat.prime_two (by exact_mod_cast h.2.2.2.2.1)
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h2 : (Module.finrank ℚ E : ℝ) ≤ 2 * (padicValInt 2 (discr E) : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp, le_div_iff₀ hn]
  linarith

end GlobalTheory.RootDiscrExp
end

section

noncomputable section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff

namespace GlobalTheory.WeightTwoSum

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def risingS (σ : ℂ) (m : I → ℕ) : ℂ := ∏ i, ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j))

def eTerm (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (2 + m i) * ((‖defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ))

def dz (j : I) : (I → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℂ) j

def dzbar (j : I) : (I → ℂ) →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (dz j)

def homFac (z : I → ℂ) : ℂ := ∏ i, ((1 + z i) / (2 * (Real.pi : ℂ) * Complex.I))

def logFac (z : I → ℂ) : ℂ := ((Real.log (Complex.normSq (homFac z)) : ℝ) : ℂ)

def modPt {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (z : I → ℂ) : Φ → ℂ :=
  fun τ => defCoord φ z θ (e.symm τ) / (1 + z (e.symm τ))

@[simp] theorem dz_apply (j : I) (v : I → ℂ) : dz j v = v j := rfl

@[simp] theorem dzbar_apply (j : I) (v : I → ℂ) : dzbar j v = starRingEnd ℂ (v j) := rfl

theorem eTerm_zero (φ : I → E →+* ℂ) (σ : ℂ) (z : I → ℂ) (x : E) : eTerm φ 0 σ z x = defTerm φ 2 z σ x := by
  simp [eTerm, defTerm]

theorem eTerm_origin (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E) :
    eTerm φ m σ 0 x = risingS σ m * term φ 2 m σ x := by
  unfold eTerm risingS term
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

theorem risingS_zero (m : I → ℕ) : risingS 0 m = risingFactor 2 m := by
  simp [risingS, risingFactor]

theorem differentiable_risingS (m : I → ℕ) : Differentiable ℂ fun σ => risingS σ m := by
  unfold risingS
  fun_prop

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

omit [Fintype I] in
theorem one_add_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) (i : I) : 1 + z i ≠ 0 := by
  intro h
  have h1 : z i = -1 := by linear_combination h
  have h2 := hz i
  rw [h1] at h2
  simp at h2

theorem homFac_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) : homFac z ≠ 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ => div_ne_zero (one_add_ne_zero hz i)
    (mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero)

theorem contDiff_homFac : ContDiff ℂ ∞ (homFac : (I → ℂ) → ℂ) := by
  unfold homFac
  exact contDiff_prod fun i _ => (contDiff_const.add (contDiff_apply ℂ (fun _ => ℂ) i)).div_const _

theorem contDiffOn_logFac : ContDiffOn ℝ ∞ (logFac : (I → ℂ) → ℂ) (polydisc I) := by
  have h1 : ContDiff ℝ ∞ (homFac : (I → ℂ) → ℂ) := contDiff_homFac.restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun z : I → ℂ => Complex.normSq (homFac z)) := by
    simp only [Complex.normSq_apply]
    exact ((Complex.reCLM.contDiff.comp h1).mul (Complex.reCLM.contDiff.comp h1)).add
      ((Complex.imCLM.contDiff.comp h1).mul (Complex.imCLM.contDiff.comp h1))
  have h3 : ContDiffOn ℝ ∞ (fun z : I → ℂ => Real.log (Complex.normSq (homFac z))) (polydisc I) :=
    h2.contDiffOn.log fun z hz => (Complex.normSq_pos.2 (homFac_ne_zero hz)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h3

theorem contDiffOn_modPt {Φ : Type} [Fintype Φ] (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) :
    ContDiffOn ℂ ∞ (modPt φ e θ) (polydisc I) := by
  refine contDiffOn_pi.2 fun τ => ?_
  unfold modPt defCoord
  refine ContDiffOn.div ?_ ?_ fun z hz => one_add_ne_zero hz _
  · exact (contDiff_const.add ((contDiff_apply ℂ (fun _ => ℂ) _).mul contDiff_const)).contDiffOn
  · exact (contDiff_const.add (contDiff_apply ℂ (fun _ => ℂ) _)).contDiffOn


omit [Fintype I] in
theorem modPt_im_pos {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (hθ : ∀ i, 0 < (φ i θ).im)
    {z : I → ℂ} (hz : z ∈ polydisc I) (τ : Φ) : 0 < (modPt φ e θ z τ).im := by
  unfold modPt defCoord
  set i := e.symm τ
  have h0 : 0 < Complex.normSq (1 + z i) := Complex.normSq_pos.2 (one_add_ne_zero hz i)
  have h1 : Complex.normSq (z i) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := hz i
    nlinarith [norm_nonneg (z i)]
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ h0
  rw [Complex.normSq_apply] at h1
  have h2 := hθ i
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  nlinarith [mul_pos h2 (sub_pos.2 h1)]

end GlobalTheory.WeightTwoSum
end
end

section

noncomputable section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates

namespace GlobalTheory.DeformedSum

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def dTerm (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (k + m i))

theorem dTerm_zero (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (x : E) :
    dTerm φ k 0 z x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
  simp [dTerm]

theorem dTerm_origin (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E) :
    dTerm φ k m 0 x = risingFactor k m * ∏ i, ((φ i x)⁻¹ ^ (k + m i) * (starRingEnd ℂ (φ i x)) ^ m i) := by
  unfold dTerm risingFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

end GlobalTheory.DeformedSum
end
end

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ZetaValUnique

theorem classZeta_eqOn {E : Type} [Field E] [NumberField E] {C : ClassGroup (GlobalTheory.CMVal.OF E)} {Z Z' : ℂ → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZeta C Z) (h' : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZeta C Z') :
    Set.EqOn Z Z' {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  refine (h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc
    (z₀ := 2) (by norm_num) ?_
  have hh : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hh.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (h.2 s hs).unique (h'.2 s hs)

theorem classZetaVals_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k →
    ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z →
      GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  intro E _ _ k hk z z' hz hz'
  funext C
  obtain ⟨Z, hZ, hZv⟩ := hz C
  obtain ⟨Z', hZ', hZv'⟩ := hz' C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_self, Nat.cast_eq_zero]
    omega
  have := classZeta_eqOn hZ hZ' hne
  rw [hZv, hZv'] at this
  exact_mod_cast this

end GlobalTheory.ZetaValUnique
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.base_change_lift_class_function : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f : GL (Fin n) F → ℂ), IsCl f → (∀ δ γ, IsNorm s δ γ → shLift s f δ = f γ) ∧ ∀ δ y : GL (Fin n) F', shLift s f (y⁻¹ * δ * galAct F F' n s y) = shLift s f δ := by
  first | (exact @GlobalTheory.Shin.shLift_isNorm_and_twisted_inv) | (exact GlobalTheory.Shin.shLift_isNorm_and_twisted_inv) | (intros; apply GlobalTheory.Shin.shLift_isNorm_and_twisted_inv <;> assumption)
end
