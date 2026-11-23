module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle029
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFrames
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle027
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle011
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle030
import Formalism.GaussIdealIdentity.GaussIdealPrimality.GaussLocalizationLengthHolds
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle012
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.enveloping_map_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau), Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  first | exact @GlobalTheory.EnvWords.envOf_surjective | exact GlobalTheory.EnvWords.envOf_surjective | (intros; apply GlobalTheory.EnvWords.envOf_surjective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.exists_envelopingAlgHom_unitaryLieAlgebra : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  first | exact @GlobalTheory.EnvelopingExtension.exists_algHom_unitary | exact GlobalTheory.EnvelopingExtension.exists_algHom_unitary | (intros; apply GlobalTheory.EnvelopingExtension.exists_algHom_unitary <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.unitary_lie_generators_rep : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∃ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) ∧ ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → Formalism.REAL.GlRel (fun a b => ρ (P a b) + Complex.I • ρ (Q a b)) ∧ ∀ X, ρ X ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => ρ (P p.1 p.2) + Complex.I • ρ (Q p.1 p.2)) := by
  first | exact @GlobalTheory.UnitaryLieComplexification.glRel_and_span | exact GlobalTheory.UnitaryLieComplexification.glRel_and_span | (intros; apply GlobalTheory.UnitaryLieComplexification.glRel_and_span <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntFramesCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames GlobalTheory.Reg

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Linear

variable {S : Type} [Field S] {x : Sp S ⟶ Xo.X} {m : ℕ} {u v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

end Linear

section Basis

variable {S : Type} [Field S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} {τ : E →+* ℂ}
  {u v : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

theorem exists_eigenBasisAt (hx0 : x ≫ Xo.s = sOf c S) (τ : E →+* ℂ) : ∃ u, IsEigenBasisAt Xo c x τ u := by
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  let B : Module.Basis (Fin (Dw.mult τ)) S (gfpEig (c := c) hx τ) :=
    Module.finBasisOfFinrankEq S _ (gfp_finrank hx0 hx τ)
  have hd : LinearIndependent S ((gfpEig (c := c) hx τ).subtype ∘ B) :=
    B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _)
  have hW : ∀ i, ((gfpEig (c := c) hx τ).subtype ∘ B) i ∈ gfpEig (c := c) hx τ := fun i => (B i).2
  exact ⟨fun i => gfpVec x xc (((gfpEig (c := c) hx τ).subtype ∘ B) i), fun i => gfp_tan hx _,
    fun i => (gfp_eig_iff hx τ _).2 (hW i), fun w hw he => gfp_basis hx0 hx τ _ hd hW w hw he⟩

end Basis

section Generic

end Generic

variable (Xo c)

end GlobalTheory.IntFramesCompare
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

open ReciprocityTheory.ChartRestriction.G

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
  (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

local instance gaussCompletionOpIsLocalRing : IsLocalRing (Op X la N) :=
  IsLocalization.AtPrime.isLocalRing (Op X la N) (gI X la N)

local instance gaussCompletionOpIsDomain : IsDomain (Op X la N) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors

local instance gaussCompletionKpField : Field (Kp X la N) :=
  inferInstanceAs (Field (FractionRing (Op X la N)))

local instance gaussCompletionKpAlgebra : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la)
    (g := (algebraMap (Op X la N) (FractionRing (Op X la N))).comp
      (algebraMap (X.Ol la) (Op X la N)))
    ((IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp
      (Op.algebraMap_injective X la N))).toAlgebra

theorem exists_gaussRing_map :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ)
      (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ)
      (σ : T0.TVar D' N' ≃ Idx D j N),
      ∃ (f : T0.Op D' N' la →+* Op X la N) (φ : T0.KTf B.KO D' N' →+* Kp X la N),
        f.Flat ∧ IsLocalHom f ∧
        Ideal.map f (IsLocalRing.maximalIdeal (T0.Op D' N' la)) =
          IsLocalRing.maximalIdeal (Op X la N) ∧
        (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧
        (∀ o, φ (T0.OpToKT D' N' la o) = algebraMap (Op X la N) (FractionRing (Op X la N)) (f o)) ∧
        (∀ a : B.KO, φ (algebraMap B.KO (T0.KTf B.KO D' N') a) =
          algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧
        ∀ q, φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N') (MvPolynomial.X q)) =
          algebraMap (Op X la N) (FractionRing (Op X la N)) (Tv X la N (σ q)) := by
  intro D B P j X la N D' N' σ
  let : Algebra (MvPolynomial (T0.TVar D' N') (X.Ol la)) (Op X la N) :=
    ((algebraMap (Pol X la N) (Op X la N)).comp
      (MvPolynomial.renameEquiv (X.Ol la) σ).toRingEquiv.toRingHom).toAlgebra
  have halg (p : MvPolynomial (T0.TVar D' N') (X.Ol la)) :
      algebraMap (MvPolynomial (T0.TVar D' N') (X.Ol la)) (Op X la N) p =
        algebraMap (Pol X la N) (Op X la N) (MvPolynomial.rename σ p) := rfl
  let Q := Formalism.DV.gaussIdeal (T0.TVar D' N') (X.Ol la)
  have : Q.IsPrime :=
    Formalism.DV.GaussP.gaussIdeal_isPrime (T0.TVar D' N') (X.Ol la)
  have : IsLocalization.AtPrime (Op X la N) Q :=
    isLocalization_rename (IsLocalRing.maximalIdeal (X.Ol la)) σ (gI X la N) rfl Q rfl
  obtain ⟨-, f, hf, hflat, hlocal, hmax, hres⟩ :=
    GlobalTheory.gaussRing_completion B.KO D' N' la (X.Ol la)
      (algebraMap_injective la) (map_asIdeal la) (exists_sub_mem la) Q rfl (Op X la N)
  have hinj : Function.Injective (algebraMap (Pol X la N) (Op X la N)) :=
    IsLocalization.injective _ (gI X la N).primeCompl_le_nonZeroDivisors
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (T0.laT D' N' la).primeCompl x
    have hzero := congrArg f h
    rw [map_mul, hx, zero_mul, hf, halg] at hzero
    have hp : p = 0 := by
      have hrename := hinj (hzero.symm.trans (map_zero _).symm)
      have hmap := MvPolynomial.rename_injective σ σ.injective (hrename.trans (map_zero _).symm)
      exact MvPolynomial.map_injective _ (algebraMap_injective la) (hmap.trans (map_zero _).symm)
    simp only [hp, map_zero] at h
    exact (IsLocalization.map_units (T0.Op D' N' la) s).mul_left_eq_zero.mp h
  let := T0.algOpKT (K := B.KO) D' N' la
  have := T0.isFractionRing_Op (K := B.KO) D' N' la
  let ι : Op X la N →+* Kp X la N := algebraMap (Op X la N) (FractionRing (Op X la N))
  have hg : Function.Injective (ι.comp f) :=
    (IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp hfinj
  let φ : T0.KTf B.KO D' N' →+* Kp X la N :=
    IsFractionRing.lift (A := T0.Op D' N' la) hg
  have hφ (o : T0.Op D' N' la) : φ (T0.OpToKT D' N' la o) = ι (f o) :=
    IsFractionRing.lift_algebraMap (A := T0.Op D' N' la) hg o
  have hφp (p : T0.OT B.KO D' N') :
      φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N')
        (MvPolynomial.map (algebraMap (𝓞 B.KO) B.KO) p)) =
      ι (algebraMap (Pol X la N) (Op X la N)
        (MvPolynomial.rename σ (MvPolynomial.map (algebraMap (𝓞 B.KO) (X.Ol la)) p))) := by
    rw [← halg, ← hf, ← hφ, T0.OpToKT, IsLocalization.lift_eq]
    rfl
  refine ⟨f, φ, hflat, hlocal, hmax, hres, hφ, ?_, ?_⟩
  · have hconst : φ.comp (algebraMap B.KO (T0.KTf B.KO D' N')) =
        (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)) := by
      refine IsFractionRing.ringHom_ext (A := 𝓞 B.KO) fun a => ?_
      have h := hφp (MvPolynomial.C a)
      rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.rename_C] at h
      simp only [RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply B.KO (T0.KTp B.KO D' N') (T0.KTf B.KO D' N'),
        MvPolynomial.algebraMap_eq, h, ← Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO]
      change ι (algebraMap (Pol X la N) (Op X la N)
          (MvPolynomial.C (algebraMap (𝓞 B.KO) (X.Ol la) a))) =
        (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la) _
          (algebraMap (X.Ol la) (X.Kl la) (algebraMap (𝓞 B.KO) (X.Ol la) a)) : FractionRing (Op X la N))
      rw [IsFractionRing.lift_algebraMap]
      change ι (algebraMap (Pol X la N) (Op X la N)
          (MvPolynomial.C (algebraMap (𝓞 B.KO) (X.Ol la) a))) =
        ι (algebraMap (X.Ol la) (Op X la N) (algebraMap (𝓞 B.KO) (X.Ol la) a))
      rw [IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N),
        MvPolynomial.algebraMap_eq]
    intro a
    exact DFunLike.congr_fun hconst a
  · intro q
    have h := hφp (MvPolynomial.X q)
    rw [MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.rename_X] at h
    exact h

end

end GlobalTheory.GaussCompletion
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.SecEval

theorem exists_quot_maps {K L C : Type*} [CommRing K] [CommRing L] [CommRing C] [Algebra K L] [Algebra K C]
    (A : Subalgebra K L) (J : Ideal A) (H : Submodule A L) (Λ : L →ₐ[K] C) (hJ : ∀ r ∈ J, Λ (r : L) = 0) :
    ∃ (ψ : (A ⧸ J) →ₐ[K] C) (Ψ : (H ⧸ J • (⊤ : Submodule A H)) →ₗ[K] C),
      (∀ x : A, ψ (Ideal.Quotient.mk J x) = Λ x) ∧ ∀ y : H, Ψ (Submodule.Quotient.mk y) = Λ y := by
  have hH : ∀ z ∈ J • (⊤ : Submodule A H), Λ (z : L) = 0 := by
    intro z hz
    refine Submodule.smul_induction_on (p := fun z : H => Λ (z : L) = 0) hz ?_ ?_
    · intro r hr m _
      rw [Submodule.coe_smul, Algebra.smul_def, map_mul]
      have : Λ (algebraMap A L r) = 0 := hJ r hr
      rw [this, zero_mul]
    · intro x y hx hy
      rw [Submodule.coe_add, map_add (f := _), hx, hy, add_zero]
  let l : H →ₗ[K] C := Λ.toLinearMap ∘ₗ (H.subtype.restrictScalars K)
  refine ⟨Ideal.Quotient.liftₐ J (Λ.comp A.val) hJ,
    (((J • (⊤ : Submodule A H)).restrictScalars K).liftQ l (fun z hz => hH z hz)) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv K (J • (⊤ : Submodule A H))).symm.toLinearMap,
    fun x => rfl, fun y => rfl⟩

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem exists_evalRp (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)
    (C : Type) [CommRing C] [Algebra (Kp X la N) C] (χ : X.Forms →+* C)
    (hχ : ∀ (a : B.KO) (f : X.Forms), χ (a • f) =
      algebraMap (Kp X la N) C (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) * χ f) :
    ∃ Θ : Rp X la N →ₐ[Kp X la N] C, ∀ F, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F) = χ F := by
  letI : Algebra (X.Kl la) C := ((algebraMap (Kp X la N) C).comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  letI : Algebra B.KO C := ((algebraMap (Kp X la N) C).comp
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X.Kl la) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X.Kl la) (Kp X la N) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : X.Forms →ₐ[B.KO] C :=
    { χ with
      commutes' := fun a => by
        show χ (algebraMap B.KO X.Forms a) = _
        rw [Algebra.algebraMap_eq_smul_one, hχ, map_one, mul_one]
        rfl }
  let vl : X.Vl la →ₐ[X.Kl la] C :=
    Algebra.TensorProduct.lift (Algebra.ofId (X.Kl la) C) g (fun _ _ => Commute.all _ _)
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId (Kp X la N) C) vl (fun _ _ => Commute.all _ _), fun F => ?_⟩
  rw [emb_apply]
  erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
  erw [map_one, map_one, one_mul, one_mul]
  rfl

theorem exists_section_maps : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL u : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (C : Type) [CommRing C] [Algebra (Kp X la N) C] (χ : X.Forms →+* C), (∀ (a : B.KO) (f : X.Forms), χ (a • f) = algebraMap (Kp X la N) C (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) * χ f) → (∀ i : Fin (WeightFamilies.dimY D j), ∑ k, algebraMap (Kp X la N) C (@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (i.succ, k))) * χ (X.inc wL (w k)) = 0) → IsUnit (∑ k, algebraMap (Kp X la N) C (@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (0, k))) * χ (X.inc wL (w k))) → ∃ (Θ : Rp X la N →ₐ[Kp X la N] C) (ψ : OsK X la w →ₐ[Kp X la N] C) (Ψ : SectionSheafQuotient X la w u →ₗ[Kp X la N] C), (∀ F, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N F) = χ F) ∧ IsUnit (Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) ∧ (∀ (x : OsK X la w) (a : SectionSheafQuotient X la w u), Ψ (x • a) = ψ x * Ψ a) ∧ (∀ (k : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k))), ψ (toOsK X la w (fr0 X la w k g)) * Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) ^ k = Θ g) ∧ ∀ f : ↥(Vw X la N u), Ψ (rho0 X la w u f) = Θ f := by
  intro D B P j X la N wL u w C _ _ χ hχ h0 h1
  obtain ⟨Θ, hΘ⟩ := exists_evalRp X la N C χ hχ
  have hsec : ∀ i, Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) = ∑ k, algebraMap (Kp X la N) C
      (@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) * χ (X.inc wL (w k)) := by
    intro i
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hΘ, Algebra.smul_def]
  have hu : IsUnit (Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) := by rw [hsec]; exact h1
  have hu' : IsUnit ((Θ : Rp X la N →+* C) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) := hu
  let Λ₀ : Lw X la w →+* C := IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) hu'
  have hΛ₀ : ∀ r, Λ₀ (algebraMap (Rp X la N) (Lw X la w) r) = Θ r := fun r => IsLocalization.lift_eq _ r
  let Λ : Lw X la w →ₐ[Kp X la N] C :=
    { Λ₀ with
      commutes' := fun c => by
        show Λ₀ (algebraMap (Kp X la N) (Lw X la w) c) = _
        rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), hΛ₀, AlgHom.commutes] }
  have hΛ : ∀ r, Λ (algebraMap (Rp X la N) (Lw X la w) r) = Θ r := hΛ₀
  have hinv : Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) * Λ (w0inv X la w) = 1 := by
    rw [← hΛ, ← map_mul, section_mul_inverse_eq_one, map_one]
  have hfr : ∀ (k : ℕ) (g : Rp X la N),
      Λ (frac X la w k g) * Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) ^ k = Θ g := by
    intro k g
    rw [frac_apply, map_mul, map_pow, hΛ, mul_assoc, ← mul_pow, mul_comm (Λ _), hinv, one_pow, mul_one]
  have hJ : ∀ r ∈ Jid X la w, Λ (r : Lw X la w) = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [coe_sfr, frac_apply, map_mul, hΛ, hsec, h0 i, zero_mul]
    | zero => simp
    | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add (f := _), hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, hx, mul_zero]
  obtain ⟨ψ₀, Ψ₀, hψ₀, hΨ₀⟩ := exists_quot_maps (Frac0 X la w) (Jid X la w) (HK X la w u) Λ hJ
  let ψ : OsK X la w →ₐ[Kp X la N] C := ψ₀
  let Ψ : SectionSheafQuotient X la w u →ₗ[Kp X la N] C := Ψ₀
  have hψ : ∀ x, ψ (toOsK X la w x) = Λ x := hψ₀
  have hΨ : ∀ y, Ψ (toA0K X la w u y) = Λ y := hΨ₀
  refine ⟨Θ, ψ, Ψ, hΘ, hu, ?_, ?_, ?_⟩
  · intro x a
    obtain ⟨x, rfl⟩ := toOsK_surjective X la w x
    obtain ⟨y, rfl⟩ := reductionMap_surjective X la w u a
    have e : toOsK X la w x • toA0K X la w u y = toA0K X la w u (x • y) := by
      rw [map_smul]
      exact algebraMap_smul (OsK X la w) x _
    rw [e, hΨ, hΨ, hψ, Submodule.coe_smul, Algebra.smul_def, map_mul]
    rfl
  · intro k g
    rw [hψ, coe_weightZeroFraction, hfr]
  · intro f
    rw [restriction_apply_eq_reduction, hΨ, coe_toHK0, hΛ]

end GlobalTheory.SecEval
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  first | exact @GlobalTheory.QNorm.exists_idele_not_mul_norm | exact GlobalTheory.QNorm.exists_idele_not_mul_norm | (intros; apply GlobalTheory.QNorm.exists_idele_not_mul_norm <;> assumption)
end
