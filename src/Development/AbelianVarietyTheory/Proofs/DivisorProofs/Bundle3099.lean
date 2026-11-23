module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle113
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.multiplicationPullbacks_differ_by_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    u.IsGen →
    ∀ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    uG.IsGen → ∀ (b : W) (σ' : H0 T.U.LG.L 1) (σ : SecK C.P.L.L T.β 1), T.Carries b σ' σ →
    ∀ (σ₂ : SecK C.P.L.L T.β (m ^ 2)) (σ'' : H0 T.U.LG.L (m ^ 2)),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
      sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) →
    ∃ v : Wˣ, T.Carries (b * v) σ'' σ₂ := by
  first | exact @GlobalTheory.Mum.Trait.carries_mulPull | exact GlobalTheory.Mum.Trait.carries_mulPull | (intros; apply GlobalTheory.Mum.Trait.carries_mulPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.closedFibre_torusCoordinates_isImmersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (ψ : Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0) ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ _ ψ) → IsImmersion ψ.left := by
  first | exact @GlobalTheory.Mum.ClosedFibreImm.main | exact GlobalTheory.Mum.ClosedFibreImm.main | (intros; apply GlobalTheory.Mum.ClosedFibreImm.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_expandsAt_section_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G), IsSemiAbelian G → ∀ k : ℕ, 1 ≤ k → ∀ F : IntFam (maximalIdeal R) D.toPre k, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ F.f := by
  first | exact @GlobalTheory.Mum.IntFam.exists_expandsAt | exact GlobalTheory.Mum.IntFam.exists_expandsAt | (intros; apply GlobalTheory.Mum.IntFam.exists_expandsAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_integralThetaExpansion_of_section_power_ge_three : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ s : H0 U.LG.L k, ∃ f : IntFam (maximalIdeal R) D.toPre k, ∀ e : ℕ, U.ExpandsAt e k s f.f := by
  first | exact @GlobalTheory.Mum.SecExp.exists_intFam | exact GlobalTheory.Mum.SecExp.exists_intFam | (intros; apply GlobalTheory.Mum.SecExp.exists_intFam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.expansion_scalar_arbitrary_of_members_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∀ α j, (F.f α).f j = 0) → ∀ a b : W, T.Exp a b s F → ∀ b' : W, T.Exp a b' s F := by
  first | exact @GlobalTheory.Mum.ZeroFam.exp_of_members_zero | exact GlobalTheory.Mum.ZeroFam.exp_of_members_zero | (intros; apply GlobalTheory.Mum.ZeroFam.exp_of_members_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.multiplicationPullback_trait_genericCondition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ) (a : W)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ₀ (p ≫ (mulA C.A.A m).left) z J) →
    ∀ (σ : SecK C.P.L.L T.β 1) (σ₂ : SecK C.P.L.L T.β (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval θ₀ p' z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ₂ p z J = gs p z ⊤ (scal T.G.hom a) * sval S p' z J := by
  first | exact @GlobalTheory.Mum.pullMul_trait_generic | exact GlobalTheory.Mum.pullMul_trait_generic | (intros; apply GlobalTheory.Mum.pullMul_trait_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaImmersion_points_agree_near_of_equal_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k N : ℕ) (τ : Fin (N + 1) → SecK D.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤), IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) → ∀ (T : Over (Sp R)) (y y' : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (∀ j l : Fin (N + 1), sval (τ j) y.left z J * sval (τ l) y'.left z J = sval (τ l) y.left z J * sval (τ j) y'.left z J) → ∃ W : T.left.Opens, z ∈ W ∧ W.ι ≫ y.left = W.ι ≫ y'.left := by
  first | exact @GlobalTheory.Mum.ThetaSep.agree_near_of_minors | exact GlobalTheory.Mum.ThetaSep.agree_near_of_minors | (intros; apply GlobalTheory.Mum.ThetaSep.agree_near_of_minors <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_expBy_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
      (F₀ : IntFam (maximalIdeal R) D.toPre k), ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀ := by
  intro R _ _ _ hR D C k hk W _ _ _ T F₀
  have := hR.2
  have hW := T.cdvr
  have := hW.1
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have cW : CharZero W := charZero_of_injective_ringHom T.inj
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨F', hF'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F₀
  obtain ⟨σ', hσ'⟩ := GlobalTheory.Mum.IntFam.exists_expandsAt W ⟨bW, cW⟩ T.D' T.A T.G T.U hGs k hk F'
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso C.P.L.L T.U.LG.L T.β T.ℓ C.P.L.isLB T.U.LG.isLB T.ℓ_gen k σ'
  refine ⟨σ, σ', F'.f, fun Z r z J J' hJ hJ' => ?_, hF', hσ'⟩
  have h1 : scal T.G.hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  rw [hσ Z r z J J' hJ hJ', h1, gs_eq r z ⊤ (by trivial), map_one, map_one, _root_.one_mul]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.eq_comp_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) {F : Type} [Field F]
    (ψ : FractionRing R →+* F) (x : Sp F ⟶ M.S) (hx : x ≫ M.π = spMap ψ ≫ jK R) : x = spMap ψ ≫ M.gp := by
  have := M.integral
  have hd := M.dominant
  let pt : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  obtain ⟨B, e₀, hoi, P, hP⟩ : ∃ (B : CommRingCat) (e₀ : Spec B ⟶ M.S), IsOpenImmersion e₀ ∧ ∃ P, e₀ P = x pt :=
    ⟨_, M.S.affineCover.f (M.S.affineCover.idx (x pt)), M.S.affineCover.map_prop _, M.S.affineCover.covers (x pt)⟩
  have hsub : Set.range M.gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  have hsub' : Set.range x ⊆ Set.range e₀ := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y pt]
    exact ⟨P, hP⟩
  obtain ⟨g', hfac⟩ : ∃ g', g' ≫ e₀ = M.gp := ⟨_, IsOpenImmersion.lift_fac e₀ M.gp hsub⟩
  obtain ⟨x', hfx⟩ : ∃ x', x' ≫ e₀ = x := ⟨_, IsOpenImmersion.lift_fac e₀ x hsub'⟩
  obtain ⟨g, rfl⟩ := Spec.map_surjective g'
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective x'
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (e₀ ≫ M.π)
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfac, M.gp_π]
  have hcomp₁ : ρ ≫ g₁ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfx, hx, Spec.map_comp]
  have hc : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => congrArg (fun f => f.hom r) hcomp
  have hc₁ : ∀ r, g₁.hom (ρ.hom r) = ψ (algebraMap R (FractionRing R) r) := fun r => congrArg (fun f => f.hom r) hcomp₁
  have hden : DenseRange (Spec.map g) := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ Spec.map g) = M.gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hinj : Function.Injective g.hom := by
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 hden
    have hr := (affine_isReduced_iff _).1 (isReduced_of_isOpenImmersion e₀)
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have key : g₁ = g ≫ CommRingCat.ofHom ψ := by
    ext b
    show g₁.hom b = ψ (g.hom b)
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom b)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * b = ρ.hom a := hinj (by rw [map_mul, hc, hc, ← hxs, mul_div_cancel₀ _ hs0])
    have h1 := congrArg g₁.hom h0
    rw [map_mul, hc₁, hc₁] at h1
    rw [← hxs, map_div₀, ← h1, mul_div_cancel_left₀ _ ((map_ne_zero ψ).2 hs0)]
  rw [← hfx, ← hfac, key, Spec.map_comp, Category.assoc]

theorem PullB.unique {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b₁ b₂ : D'.SecB k x} (H₁ : PullB hD x b b₁) (H₂ : PullB hD x b b₂) : b₁ = b₂ := by
  refine DVR.SecOps.sec_ext fun q => fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.famφB x κ y))
  have e₁ := H₁ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  have e₂ := H₂ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem PullB.eq_zero {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X}
    {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x} (H : PullB hD x b b') (h : ∀ q, b'.f q = 0) (p) : b.f p = 0 := by
  have : IsDominant (specOf φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hφ]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (specOf φ)
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsSchemeTheoreticallyDominant (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (pull_grp hD).1.flip
  have : QuasiCompact (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (pull_grp hD).1.flip inferInstance
  apply (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)).app_injective
  rw [map_zero]
  refine fn_ext fun y hy => ?_
  choose q hq using fun κ => exists_chart D'.P.isLB (D'.famφB x κ y)
  have e := H _ (𝟙 _) y p q (fun κ => by
    have a := Set.mem_iInter.1 hy κ
    exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) (ExpGTrans.famφB_pull hD x κ)).mpr a) hq
  have e' := e.trans ((congrArg _ ((congrArg (gs _ y _) (h q)).trans (DVR.hr_gs_zero _ _ _))).trans (mul_zero _))
  exact (gs_pull _ _ y _ hy _).trans (e'.trans (DVR.hr_gs_zero _ _ _).symm)

theorem expands_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) :
    U.Expands k DVR.SecOps.secZero 0 := by
  refine ⟨1, one_ne_zero, DVR.SecOps.secZero, fun _ => DVR.SecOps.secZero, fun j₁ j₂ _ => ?_, fun α j₁ j₂ _ => ?_,
    fun e => ⟨∅, fun α _ j => map_zero _, fun p j₁ jf jt _ _ => ?_⟩⟩
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (mul_zero _)).trans (Finset.sum_empty).symm

theorem IntFam.f_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {k : ℕ} (F : IntFam I D k)
    (h : F.F = 0) (x : D.X) (q) : (F.f x).f q = 0 := by
  have h₀ : GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) x) (DegPre.famε k) (F.F.s x)
      (D.famφB x) (DegPre.famε k) DVR.SecOps.secZero (DegPre.prB D (FractionRing R)).left 1 := by
    rw [h]
    intro j₁ j₂ _
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  exact (IntegralExpansion.secIsMul_of_secScal D.P.isLB D.P.A.hom (a := 1) (IntegralExpansion.prB_app_injective D) h₀
    (by rw [Over.w (DegPre.prB D (FractionRing R))]; exact F.ext x) q).trans (mul_zero _)

theorem IntFam.eq_zero_of_two_scalars {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k)
    (F : IntFam I D.toPre k) {σ₁ σ₂ : H0 U.LG.L k} (e₁ : ∀ e, U.ExpandsAt e k σ₁ F.f) (e₂ : ∀ e, U.ExpandsAt e k σ₂ F.f)
    {b b' : W} (hb : b ≠ b') (H : ∀ y J, Good U.LG.L y J → ∃ u : ((pullback G.hom (jK W)).presheaf.stalk y)ˣ,
      gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) * u.val * sval σ₁ (pullback.fst G.hom (jK W)) y J =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') * u.val * sval σ₂ (pullback.fst G.hom (jK W)) y J) :
    F.F = 0 := by
  have res : ∀ σ : H0 U.LG.L k, (∀ e, U.ExpandsAt e k σ F.f) → ∃ s : U.SecK k, U.Expands k s F.F ∧
      ∀ y J, Good U.LG.L y J → sval σ (pullback.fst G.hom (jK W)) y J = sval s (𝟙 _) y J := fun σ e => by
    obtain ⟨s, hs⟩ := UnifBaseChange.exists_secScal_one U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (pullback.fst G.hom (jK W)) (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm) σ
    refine ⟨s, ⟨1, one_ne_zero, σ, F.f, ?_, F.ext, e⟩, fun y J hJ => ?_⟩
    · rw [UnifBaseChange.scal_one]; exact hs
    · have v := DVR.hr_secScal_sval hs (𝟙 _) y hJ
      rwa [Category.id_comp, gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at v
  obtain ⟨s₁, x₁, v₁⟩ := res σ₁ e₁
  obtain ⟨s₂, x₂, v₂⟩ := res σ₂ e₂
  obtain rfl : s₁ = s₂ := ((U.expand k hk).2 F.F).unique x₁ x₂
  have hz : s₁ = DVR.SecOps.secZero := by
    refine DVR.SecOps.sec_ext (sec_ext_val U.LG.isLB fun y J hJ => ?_)
    obtain ⟨u, e⟩ := H y J hJ
    rw [v₁ y J hJ, v₂ y J hJ, ← sub_eq_zero, ← sub_mul, ← sub_mul] at e
    have hu : IsUnit (gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b'))) := by
      rw [GenericCross.gs_scal, pullback.condition]
      exact GenericCross.isUnit_cst _ y (sub_ne_zero.2 hb)
    have hs : gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b')) =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) - gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') := by
      simp only [gs_eq _ y ⊤ trivial, scal, map_sub]
    rw [hs] at hu
    exact ((hu.mul u.isUnit).mul_right_eq_zero.1 e).trans (DVR.hr_gs_zero _ _ _).symm
  rw [hz] at x₁
  exact ((U.expand k hk).1 _).unique x₁ (expands_zero U.toUnifPre k)

theorem exists_fractionRing_square {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W) (h : Function.Injective φ) :
    ∃ ψ : FractionRing R →+* FractionRing W, jK W ≫ spMap φ = spMap ψ ≫ jK R := by
  have hi : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp h
  have h₀ : (algebraMap W (FractionRing W)).comp φ = (IsFractionRing.lift hi).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => by rw [RingHom.comp_apply (IsFractionRing.lift hi), IsFractionRing.lift_algebraMap]
  refine ⟨IsFractionRing.lift hi, ?_⟩
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← h₀]

theorem Trait.exists_generic_map {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    ∃ p' : pullback T.G.hom (jK W) ⟶ C.A.A.left, pullback.fst T.G.hom (jK W) ≫ T.β = p' ≫ C.α := by
  obtain ⟨ψ, h₀⟩ := exists_fractionRing_square T.φ T.inj
  have hψ : jK W ≫ T.ξ = spMap ψ ≫ C.gp := C.toModif.eq_comp_gp ψ _ (by rw [Category.assoc, T.ξ_π, h₀])
  have w₁ : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
  have w₂ : pullback.fst T.G.hom (jK W) ≫ T.G.hom = pullback.snd T.G.hom (jK W) ≫ jK W := pullback.condition
  have w₃ : (pullback.fst T.G.hom (jK W) ≫ T.β) ≫ C.G.hom = (pullback.snd T.G.hom (jK W) ≫ spMap ψ) ≫ C.gp := by
    rw [Category.assoc, w₁, reassoc_of% w₂, hψ, Category.assoc]
  have hp : IsPullback C.α C.A.A.hom C.G.hom C.gp := C.α_cart.1
  exact ⟨hp.lift _ _ w₃, (hp.lift_fst _ _ w₃).symm⟩

theorem Trait.exp_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∃ α j, (F.f α).f j ≠ 0) → ∀ a b b' : W, a ≠ 0 → T.Exp a b s F → T.Exp a b' s F → b = b' := by
  intro R _ _ _ hR D C W _ _ _ T k hk s F hF a b b' _ h₁ h₂
  obtain ⟨α, j, hne⟩ := hF
  obtain ⟨σ₁, ⟨σ₁', f₁, c₁, p₁, e₁⟩, g₁⟩ := h₁
  obtain ⟨σ₂, ⟨σ₂', f₂, c₂, p₂, e₂⟩, g₂⟩ := h₂
  by_contra hb
  apply hne
  obtain ⟨F', hF'⟩ := exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F
  rw [show f₁ = F'.f from funext fun x => (p₁ x).unique (hF' x)] at e₁
  rw [show f₂ = F'.f from funext fun x => (p₂ x).unique (hF' x)] at e₂
  obtain ⟨p', hp'⟩ := T.exists_generic_map
  have h₀ : F'.F = 0 := F'.eq_zero_of_two_scalars T.U hk e₁ e₂ hb fun y J' hJ' => by
    choose J hJ using fun χ : pullback T.G.hom (jK W) ⟶ C.G.left => exists_chart C.P.L.isLB (χ y)
    exact ⟨_, (c₁ _ _ y J J' hJ hJ').symm.trans ((g₁ _ _ p' hp' y J hJ).trans
      ((g₂ _ _ p' hp' y J hJ).symm.trans (c₂ _ _ y J J' hJ hJ')))⟩
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  exact (hF' x).eq_zero T.inj (F'.f_eq_zero h₀ x) j

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.traitExpansions_same_family_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  first | exact @GlobalTheory.Mum.Trait.exp_pair | exact GlobalTheory.Mum.Trait.exp_pair | (intros; apply GlobalTheory.Mum.Trait.exp_pair <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W)))), w₀.IsGen → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ s', T.U.ExpandsF F (C.n ^ j) w₀ (E' s') s') → ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s' : Fam T.D'.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((s').s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1) → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JG Jt, Good C.P.L.L z JP → Good T.U.LG.L z JG → Good T.A.L z Jt → sval σ p z JP = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' s') q z Jt := by
  first | exact @GlobalTheory.Mum.TraitValue.value | exact GlobalTheory.Mum.TraitValue.value | (intros; apply GlobalTheory.Mum.TraitValue.value <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.Four N₁ → ∀ v : ∀ y, (Φ.V y)ˣ, (∀ e : ℕ, ∃ a : A, ∀ y, Φ.ev y a - ((v y)⁻¹ : (Φ.V y)ˣ) ∈ (maximalIdeal A ^ e).map (Φ.ev y)) → (Φ.rescale v).Four N₁ := by
  first | exact @GlobalTheory.Poinc.VPre.four_rescale | exact GlobalTheory.Poinc.VPre.four_rescale | (intros; apply GlobalTheory.Poinc.VPre.four_rescale <;> assumption)
end
