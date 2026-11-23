module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle198
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FunctionFieldEtale

theorem finiteDimensional_fractionRing_of_etale {R S K L : Type} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] (φ : R →+* S) (hφ : φ.Etale) (ψ : K →+* L)
    (h : ∀ r, ψ (algebraMap R K r) = algebraMap S L (φ r)) :
    letI := ψ.toAlgebra; FiniteDimensional K L := by
  letI : Algebra K L := ψ.toAlgebra
  letI : Algebra R S := φ.toAlgebra
  haveI : Algebra.Etale R S := hφ
  letI : Algebra R L := (ψ.comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq (fun r => h r)
  haveI : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  let g : K ⊗[R] S →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L)
    (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K g.range :=
    Module.Finite.of_surjective g.rangeRestrict.toLinearMap g.rangeRestrict_surjective
  have hS : ∀ s : S, algebraMap S L s ∈ g.range := fun s => ⟨1 ⊗ₜ s, by simp [g]⟩
  have hinv : ∀ x ∈ g.range, x⁻¹ ∈ g.range := fun x hx =>
    Subalgebra.inv_mem_of_algebraic (A := g.range) (x := ⟨x, hx⟩)
      ((Algebra.IsAlgebraic.isAlgebraic (R := K) (⟨x, hx⟩ : g.range)).algHom g.range.val)
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) y
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ (hS a) (hinv _ (hS b))
  exact Module.Finite.of_surjective g.toLinearMap hsurj

theorem finiteDimensional_functionField_of_etale_on_open : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty →
    letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  intro M W _ _ f _ U hf hU
  have hξU : genericPoint M ∈ U :=
    ((genericPoint_spec M).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  obtain ⟨V, hV, hfξV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f (genericPoint M))
    (U := ⊤) trivial
  let x : U := ⟨genericPoint M, hξU⟩
  have hx : x ∈ (U.ι ≫ f) ⁻¹ᵁ V := hfξV
  obtain ⟨V', hV', hxV', hV'sub⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : V' ≤ (U.ι ≫ f) ⁻¹ᵁ V := fun _ h => hV'sub h
  let U' : M.Opens := U.ι ''ᵁ V'
  have hU' : IsAffineOpen U' := hV'.image_of_isOpenImmersion U.ι
  have hξU' : genericPoint M ∈ U' := ⟨x, hxV', rfl⟩
  have e' : U' ≤ f ⁻¹ᵁ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hV'sub hy
  haveI : Nonempty V := ⟨⟨_, hfξV⟩⟩
  haveI : Nonempty U' := ⟨⟨_, hξU'⟩⟩
  have het0 := HasRingHomProperty.appLE (P := @Etale) (f := U.ι ≫ f) hf ⟨V, hV⟩ ⟨V', hV'⟩ hle
  have key : (U.ι ≫ f).appLE V V' hle = f.appLE V U' e' := by
    rw [Scheme.Hom.comp_appLE]
    erw [Scheme.Opens.ι_appLE]
    rfl
  have het : (f.appLE V U' e').hom.Etale := by
    rw [← key]; exact het0
  haveI := functionField_isFractionRing_of_isAffineOpen W V hV
  haveI := functionField_isFractionRing_of_isAffineOpen M U' hU'
  refine finiteDimensional_fractionRing_of_etale (f.appLE V U' e').hom het (functionFieldMap f) ?_
  intro r
  have := functionFieldMap_algebraMap f (genericPoint M) (W.presheaf.germ V _ hfξV r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at this
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  refine this.trans ?_
  rw [Scheme.Hom.germ_stalkMap_apply]
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hfξV⟩⟩
  erw [Scheme.algebraMap_germ_eq_germToFunctionField]
  show M.presheaf.germ _ _ _ (f.app V r) =
    M.presheaf.germ U' _ hξU' (M.presheaf.map (homOfLE e').op (f.app V r))
  rw [TopCat.Presheaf.germ_res_apply]

end GlobalTheory.FunctionFieldEtale
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem formallyUnramified_of_dvr_of_essFiniteType : ∀ (R T V : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing T] [Algebra R T] [Algebra.FormallyUnramified R T] [Algebra.EssFiniteType R T] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] (μ : T →ₐ[R] V), (∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R V r ∈ IsLocalRing.maximalIdeal V) → Function.Injective (algebraMap R V) → (∀ v : V, ∃ a b : T, μ b ≠ 0 ∧ v * μ b = μ a) → Algebra.FormallyUnramified R V := by
  intro R T V _ _ _ _ _ _ _ _ _ _ _ μ hm hinj hfrac
  let Q : Ideal T := (IsLocalRing.maximalIdeal V).comap μ
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  let D := Localization.AtPrime Q
  haveI : Algebra.FormallyUnramified T D := .of_isLocalization Q.primeCompl
  haveI : Algebra.FormallyUnramified R D := .comp R T D
  haveI : Algebra.EssFiniteType T D := .of_isLocalization D Q.primeCompl
  haveI : Algebra.EssFiniteType R D := .comp R T D
  have hQ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R T r ∈ Q := fun r hr => by
    show μ (algebraMap R T r) ∈ IsLocalRing.maximalIdeal V
    rw [μ.commutes]; exact hm r hr
  haveI : IsLocalHom (algebraMap R D) := ⟨fun r hr => by
    by_contra hnu
    rw [IsScalarTower.algebraMap_apply R T D, IsLocalization.AtPrime.isUnit_to_map_iff D Q] at hr
    exact hr (hQ r ((IsLocalRing.mem_maximalIdeal _).2 hnu))⟩
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R D) = IsLocalRing.maximalIdeal D :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hunit : ∀ y : Q.primeCompl, IsUnit (μ y) := fun y => by
    by_contra h; exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  let ν : D →ₐ[R] V := IsLocalization.liftAlgHom (M := Q.primeCompl) (f := μ) hunit
  have hν : ∀ t, ν (algebraMap T D t) = μ t := fun t => IsLocalization.lift_eq _ _
  have hνu : ∀ d, IsUnit (ν d) → IsUnit d := by
    intro d hd
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl d
    have e : IsLocalization.mk' D x s * algebraMap T D s = algebraMap T D x :=
      IsLocalization.mk'_spec D x s
    have hx : IsUnit (μ x) := by
      have := congrArg ν e
      rw [map_mul, hν, hν] at this
      rw [← this]; exact hd.mul (hunit s)
    have hxQ : x ∈ Q.primeCompl := fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
    have : IsUnit (algebraMap T D x) := IsLocalization.map_units D (⟨x, hxQ⟩ : Q.primeCompl)
    rw [← e] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmD : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap R D ϖ} := by
    rw [← hmax, hmR, Ideal.map_span, Set.image_singleton]
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hS := GlobalTheory.T.subring_eq_univ_of_uniformizer_generates V (ν : D →+* V).range (algebraMap R V ϖ) ⟨algebraMap R D ϖ, ν.commutes ϖ⟩
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (hm ϖ hϖm) ?_ ?_ ?_
  · refine Algebra.FormallyUnramified.of_surjective ν fun v => ?_
    have hv : v ∈ (ν : D →+* V).range := hS ▸ Subring.mem_top v
    obtain ⟨d, hd⟩ := hv
    exact ⟨d, hd⟩
  · rintro _ ⟨d, rfl⟩ hs
    have hu : IsUnit (ν d) := by
      by_contra h; exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu'⟩ := hνu d hu
    refine ⟨ν ↑u⁻¹, ⟨_, rfl⟩, ?_⟩
    change ν d * ν ↑u⁻¹ = 1
    rw [← map_mul, ← hu', Units.mul_inv, map_one]
  · rintro _ ⟨d, rfl⟩ hs
    have hd : d ∈ IsLocalRing.maximalIdeal D := (IsLocalRing.mem_maximalIdeal _).2 fun h =>
      (IsLocalRing.mem_maximalIdeal _).1 hs (h.map ν)
    rw [hmD] at hd
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hd
    refine ⟨ν a, ⟨a, rfl⟩, ?_⟩
    change ν (a * algebraMap R D ϖ) = _
    rw [map_mul, ν.commutes, mul_comm]
  · intro v
    obtain ⟨a, b, hb, hab⟩ := hfrac v
    exact ⟨μ a, ⟨_, hν a⟩, μ b, ⟨_, hν b⟩, hb, hab⟩

end GlobalTheory

namespace GlobalTheory

theorem trace_dvr_formallyUnramified_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ (V : ValuationSubring M.functionField) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap (functionFieldMap f))], DominatesStalk V z → letI := ((functionFieldMap f).restrict (V.comap (functionFieldMap f)) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap (functionFieldMap f)) V := by
  intro M W _ _ f _ U hU z hz V _ _ hV
  obtain ⟨-, hfe, hess⟩ :=
    stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict M W f U hU z hz
  set φ := functionFieldMap f with hφ
  set R := V.comap φ
  let A := W.presheaf.stalk (f z)
  let B := M.presheaf.stalk z
  let g : A →+* B := (f.stalkMap z).hom
  letI : Algebra A B := g.toAlgebra
  haveI : Algebra.FormallyEtale A B := hfe
  haveI : Algebra.EssFiniteType A B := hess
  have hcomp : ∀ a : A, φ (algebraMap A W.functionField a) = algebraMap B M.functionField (g a) :=
    fun a => functionFieldMap_algebraMap f z a
  have hαR : ∀ a : A, algebraMap A W.functionField a ∈ R := fun a => by
    change φ _ ∈ V
    rw [hcomp]; exact hV.1 _
  let αR : A →+* R := (algebraMap A W.functionField).codRestrict R hαR
  let βV : B →+* V := (algebraMap B M.functionField).codRestrict V hV.1
  letI algRV : Algebra R V := (φ.restrict R V fun _ hx => hx).toAlgebra
  letI : Algebra A R := αR.toAlgebra
  letI : Algebra A V := (βV.comp g).toAlgebra
  haveI : IsScalarTower A R V := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hcomp a).symm
  let gV : B →ₐ[A] V := { βV with commutes' := fun _ => rfl }
  let μ : TensorProduct A R B →ₐ[R] V :=
    Algebra.TensorProduct.lift (Algebra.ofId R V) gV fun _ _ => Commute.all _ _
  haveI : Algebra.FormallyUnramified R (TensorProduct A R B) := Algebra.FormallyUnramified.base_change R
  haveI : Algebra.EssFiniteType R (TensorProduct A R B) := Algebra.EssFiniteType.baseChange A B R
  refine formallyUnramified_of_dvr_of_essFiniteType R (TensorProduct A R B) V μ ?_ ?_ ?_
  · intro r hr
    by_contra hnu
    have hu : IsUnit (algebraMap R V r) := by
      by_contra h; exact hnu ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have hw' : φ (r : W.functionField) * (w : M.functionField) = 1 := congrArg Subtype.val hw
    have hr0 : (r : W.functionField) ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hw'; exact zero_ne_one hw'
    have hinv : (r : W.functionField)⁻¹ ∈ R := by
      change φ _ ∈ V
      rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hw']
      exact w.2
    exact (IsLocalRing.mem_maximalIdeal _).1 hr
      (isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hr0)⟩)
  · intro x y hxy
    exact Subtype.ext (φ.injective (congrArg Subtype.val hxy))
  · intro v
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) (v : M.functionField)
    have hμ : ∀ c : B, ((μ (1 ⊗ₜ c) : V) : M.functionField) = algebraMap B M.functionField c := by
      intro c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_, ?_⟩
    · intro h0
      apply nonZeroDivisors.ne_zero hb
      apply IsFractionRing.injective B M.functionField
      rw [map_zero]
      rw [← hμ, h0]; rfl
    · apply Subtype.ext
      rw [Subring.coe_mul, hμ, hμ]
      rw [← hab, div_mul_cancel₀]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.HeckeUOps

variable {D : D7}

theorem phase_ne_zero (τ : D.what₂.Tau) (a : D.host.Eˣ) :
    embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ) ≠ 0 := by
  have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  exact div_ne_zero h (by exact_mod_cast (norm_ne_zero_iff.2 h))

def mul {N₁ N₂ : ℕ} (N : ℕ) (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (h : Even ((N₁ : ℤ) + N₂ - N)) : HeckeU D N where
  f := χ₁.f * χ₂.f
  n := χ₁.n + χ₂.n
  unitary x := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, χ₁.unitary, χ₂.unitary, one_mul]
  cont := by
    obtain ⟨m₁, hm₁, h₁⟩ := χ₁.cont
    obtain ⟨m₂, hm₂, h₂⟩ := χ₂.cont
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun u hu ⟨s, hs, e⟩ => ?_⟩
    rw [MonoidHom.mul_apply, h₁ u hu ⟨m₂ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; push_cast; ring⟩,
      h₂ u hu ⟨m₁ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; push_cast; ring⟩, one_mul]
  aut a := by
    have h1 := χ₁.aut a
    have h2 := χ₂.aut a
    have e : ∀ τ ∈ Finset.univ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ ((χ₁.n + χ₂.n) τ) =
        (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₁.n τ) *
          (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₂.n τ) := fun τ _ => by
      rw [Pi.add_apply, zpow_add₀ (phase_ne_zero τ a)]
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, MonoidHom.mul_apply, Units.val_mul]
    calc _ = (((χ₁.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₁.n τ)) *
        (((χ₂.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₂.n τ)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  norm x := by rw [MonoidHom.mul_apply, χ₁.norm, χ₂.norm, one_mul]
  par τ := by
    have := (χ₁.par τ).add ((χ₂.par τ).add h)
    have e : (χ₁.n + χ₂.n) τ - (N : ℤ) = χ₁.n τ - N₁ + (χ₂.n τ - N₂ + (N₁ + N₂ - N)) := by
      simp only [Pi.add_apply]; ring
    rw [e]; exact this
  unr u hu hz := by rw [MonoidHom.mul_apply, χ₁.unr u hu hz, χ₂.unr u hu hz, one_mul]

def inv {N : ℕ} (N' : ℕ) (χ : HeckeU D N) (h : Even ((N : ℤ) - N')) : HeckeU D N' where
  f := χ.f⁻¹
  n := -χ.n
  unitary x := by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, χ.unitary, inv_one]
  cont := by
    obtain ⟨m, hm, h₁⟩ := χ.cont
    exact ⟨m, hm, fun u hu hs => by rw [MonoidHom.inv_apply, h₁ u hu hs, inv_one]⟩
  aut a := by
    have h1 := χ.aut a
    have e : ∀ τ ∈ Finset.univ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ ((-χ.n) τ) =
        ((embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ.n τ))⁻¹ := fun τ _ => by
      rw [Pi.neg_apply, zpow_neg]
    rw [Finset.prod_congr rfl e, Finset.prod_inv_distrib, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, ← mul_inv, h1,
      inv_one]
  norm x := by rw [MonoidHom.inv_apply, χ.norm, inv_one]
  par τ := by
    have := ((χ.par τ).neg.sub h).sub (even_two_mul (N' : ℤ))
    have e : (-χ.n) τ - (N' : ℤ) = -(χ.n τ - N) - (N - N') - 2 * N' := by
      simp only [Pi.neg_apply]; ring
    rw [e]; exact this
  unr u hu hz := by rw [MonoidHom.inv_apply, χ.unr u hu hz, inv_one]

def ofChar (N : ℕ) (χ : HChar D.host.E) (n : D.what₂.Tau → ℤ) (hu : χ.IsUnitary) (hi : χ.HasInf (embT D) n)
    (hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1)
    (hn : ∀ x, χ.1 (finIdl D (x * sgU D x)) = 1) (hp : ∀ τ, Even (n τ - (N : ℤ)))
    (hr : ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1) :
    HeckeU D N where
  f := χ.1.comp (finIdl D)
  n := n
  unitary _ := hu _
  cont := hc
  aut a := by
    have h1 := χ.2.2 a
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, mul_comm] at h1
    have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one] at h3
    rw [← h3]
    exact congrArg _ (hi a).symm
  norm := hn
  par := hp
  unr := hr

@[simp] theorem mul_f {N₁ N₂ N : ℕ} (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (h) (x) :
    (mul N χ₁ χ₂ h).f x = χ₁.f x * χ₂.f x := rfl

@[simp] theorem inv_f {N N' : ℕ} (χ : HeckeU D N) (h) (x) : (inv N' χ h).f x = (χ.f x)⁻¹ := rfl

end GlobalTheory.HeckeUOps
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Col2.SplitChar

namespace GlobalTheory.SplitCharGen

variable {D : D7}

def ofHChar (N : ℕ) (χ : _root_.Formalism.L2.Host.HChar D.host.E) (n : D.what₂.Tau → ℤ) (hu : χ.IsUnitary)
    (hi : χ.HasInf (_root_.Formalism.L2.Host.embTau D) n) (hp : ∀ τ, Even (n τ - (N : ℤ)))
    (hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1)
    (hn : ∀ x, χ.1 (finIdl D (x * sgU D x)) = 1)
    (hr : ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1) :
    HeckeU D N where
  f := χ.1.comp (finIdl D)
  n := n
  unitary := fun _ => hu _
  cont := hc
  aut := fun a => by
    have h1 := χ.2.2 a
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU, mul_comm] at h1
    have h2 := hi a
    have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one] at h3
    rw [← h3]
    exact congrArg _ h2.symm
  norm := hn
  par := hp
  unr := hr

end GlobalTheory.SplitCharGen
end
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

theorem _root_.GlobalTheory.T.integral_eq_rankOneFactorSL2_of_geometric_on_shells : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℕ), 2 ≤ q → ∀ (a : ℂ), ‖a‖ < 1 →
    ∀ (H : ℕ → Set X), (∀ j, MeasurableSet (H j)) → Monotone H → ⋃ j, H j = Set.univ →
    (∀ j, μ (H j) = (q : ENNReal) ^ j) → ∀ (F : X → ℂ), (∀ x ∈ H 0, F x = 1) →
    (∀ j x, x ∈ H (j + 1) → x ∉ H j → F x = (a / q) ^ (j + 1)) →
    Integrable F μ ∧ ∫ x, F x ∂μ = cSL q a ∧ ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ := by
  first | exact @GlobalTheory.integral_geometric_shells | exact GlobalTheory.integral_geometric_shells | (intros; apply GlobalTheory.integral_geometric_shells <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SuppFin

theorem cLoc_mem_KGL_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n),
    ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ _ n y
  set P : GL (Fin n) (Af E) := GeneralLinearGroup.map (pFin E) (y : GA E n) with hP
  have h1 : ∀ᶠ w in cofinite, ∀ i j, (P.val i j) w ∈ HeightOneSpectrum.adicCompletionIntegers E w := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact (P.val i j).2
  have h2 : ∀ᶠ w in cofinite, ∀ i j, ((P⁻¹).val i j) w ∈ HeightOneSpectrum.adicCompletionIntegers E w := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact ((P⁻¹).val i j).2
  filter_upwards [h1, h2] with w hw1 hw2
  have hmul : ∀ (A B : GL (Fin n) (Af E)), A * B = 1 →
      (A.val.map (pLoc E w)) * (B.val.map (pLoc E w)) = 1 := by
    intro A B h
    rw [← Matrix.map_mul, ← Units.val_mul, h, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  let M : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.of fun i j => ⟨(P.val i j) w, hw1 i j⟩
  let N : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.of fun i j => ⟨((P⁻¹).val i j) w, hw2 i j⟩
  have hM : M.map (Ov E w).subtype = P.val.map (pLoc E w) := Matrix.ext fun i j => rfl
  have hN : N.map (Ov E w).subtype = (P⁻¹).val.map (pLoc E w) := Matrix.ext fun i j => rfl
  have hinj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype) :=
    Matrix.map_injective Subtype.val_injective
  let k : GL (Fin n) (Ov E w) :=
    { val := M
      inv := N
      val_inv := hinj (by
        simp only
        rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hmul _ _ (mul_inv_cancel P))
      inv_val := hinj (by
        simp only
        rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hmul _ _ (inv_mul_cancel P)) }
  exact ⟨k, Units.ext (Matrix.ext fun i j => rfl)⟩

end GlobalTheory.BCT.SuppFin
end
