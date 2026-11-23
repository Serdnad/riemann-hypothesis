module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle212
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle213
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.WeilBound.CoreStatements.SesquilinearFractions.CmLieModelAction
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle214
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsPullSnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVDesc
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem triv_of_section_of_locally_triv : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X), e ≫ p = 𝟙 S → (∀ U : S.Opens, IsIso (p.app U)) → ∀ M : LB X, M.IsLB → GlobalTheory.AbLaw.Triv (M.pull e) → (∀ x : S, ∃ U : S.Opens, x ∈ U ∧ GlobalTheory.AbLaw.Triv (M.pull (p ⁻¹ᵁ U).ι)) → GlobalTheory.AbLaw.Triv M :=
  fun _ _ p e he hp _ hM h₀ loc =>
    GlobalTheory.CubeGlue.triv_of_locally_triv hM p e he (GlobalTheory.CubeGlue.surjective_restrict p hp) h₀ loc

end GlobalTheory.CompanionTheory.Ar.Approx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU


theorem _root_.GlobalTheory.T.cubical_weil_pairing_iso_invariant : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂), LBIso L₁.L L₂.L → ∀ (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ), CubWeil c₁ N x y ζ → CubWeil c₂ N x y ζ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso | exact GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso | (intros; apply GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem integers_regular {F : Type} [Field F] [NumberField F] (hN : Flat.NormalCpt ξ) (σ : 𝓞 F →+* Ω) (q : Cpt ξ)
    (a : 𝓞 F) : σ a ∈ regAt ξ q := by
  refine hN q _ ?_
  have h : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
  exact h.tower_top

theorem unitAt_nat {q : Cpt ξ} [CharZero Ω] (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simpa using Flat.ZUnit.one
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact Flat.ZUnit.mul (ha (left_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_right b))
      (hb (right_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_left a))

theorem unitAt_natAbs_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q (((discr F).natAbs : ℕ) : Ω) :=
  unitAt_nat _ (Int.natAbs_ne_zero.2 (discr_ne_zero F)) fun p hp hd =>
    h p hp (Int.natCast_dvd.2 hd)

theorem natAbs_discr_mem_different (F : Type) [Field F] [NumberField F] :
    (((discr F).natAbs : ℕ) : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
  have h := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 F))
  rwa [absNorm_differentIdeal F] at h

theorem htW_eq_htDual {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (L : Semi.LB G.left) (n : ℕ) {F : Type} [Field F] [NumberField F] (ρ : 𝓞 F →+* Module.End Ω Li)
    (σ : 𝓞 F →+* Ω) (q : Cpt ξ) (hσ : ∀ a, σ a ∈ regAt ξ q)
    (hu : unitAt ξ q (((discr F).natAbs : ℕ) : Ω)) :
    M.htW L n ρ σ (differentIdeal ℤ (𝓞 F)) q = M.htDual L n ρ σ q := by
  apply le_antisymm
  · refine Submodule.span_le.2 fun e he => ?_
    have h1 := he.2 _ (natAbs_discr_mem_different F)
    rw [map_natCast] at h1
    have h2 := Submodule.smul_mem _ (⟨_, hu.2.2⟩ : regAt ξ q) h1
    have h3 : (⟨_, hu.2.2⟩ : regAt ξ q) • (((discr F).natAbs : ℕ) : Ω) • e = e := by
      show (((discr F).natAbs : ℕ) : Ω)⁻¹ • (((discr F).natAbs : ℕ) : Ω) • e = e
      exact inv_smul_smul₀ hu.1 e
    rw [h3] at h2
    exact h2
  · intro e he
    refine Submodule.subset_span ⟨M.mem_eigSp_of_mem_htDual L n ρ σ he, fun d _ => ?_⟩
    exact Submodule.smul_mem _ (⟨σ d, hσ d⟩ : regAt ξ q) he

theorem exists_mul_of_isCp {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {κ w : Ω} (hκ : HT.IsCp p κ) (hw : HT.IsCp p w)
    (R : Subring Ω) (hR : w ∈ R) : ∃ u ∈ R, w = u * κ := by
  unfold HT.IsCp at hκ hw
  rw [if_neg h2] at hκ hw
  obtain ⟨z, hz, rfl⟩ := hκ
  obtain ⟨z', hz', rfl⟩ := hw
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨j, -, hj⟩ := hz'.eq_pow_of_pow_eq_one hz.pow_eq_one
  obtain ⟨k, -, hk⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  have h1 : z' ∈ R := by simpa using R.add_mem hR R.one_mem
  have h3 : z ∈ R := hj ▸ R.pow_mem h1 j
  refine ⟨∑ i ∈ Finset.range k, z ^ i, R.sum_mem fun i _ => R.pow_mem h3 i, ?_⟩
  rw [geom_sum_mul, hk]

theorem sandwich_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ κ w : Ω, HT.IsCp p κ → HT.IsCp p w → HT.Sandwich 𝔐 p κ → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → w ∈ regAt 𝔐.ξ q → ∀ t : CMType H ⊕ CMType H, 𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, w • e ∈ 𝔐.dR t q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 p hp _ h2 hd κ w hκ hw hS q hq hwq t
  haveI : CharZero Ω := ⟨fun a b h => by
    have h' : 𝔐.cst (a : c.F) = 𝔐.cst (b : c.F) := by rw [map_natCast, map_natCast, h]
    exact Nat.cast_injective (𝔐.cst.injective h')⟩
  have hN : Flat.NormalCpt 𝔐.ξ := GlobalTheory.CompanionTheory.Ar.XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  have hu : unitAt 𝔐.ξ q (((discr E).natAbs : ℕ) : Ω) := unitAt_natAbs_discr fun r hr hrd => by
    by_contra hn
    have : r = p := GlobalTheory.CompanionTheory.Ar.inFibre_unique hp.out hr hq hn
    exact hd (this ▸ hrd)
  have hHT : 𝔐.HT p t q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb t) q := by
    cases t with
    | inl τ => exact htW_eq_htDual 𝔐.M _ _ 𝔐.ρ _ q (integers_regular hN _ q) hu
    | inr τ => rfl
  obtain ⟨-, -, -, hs⟩ := hS q hq
  obtain ⟨h1, h3⟩ := hs t
  obtain ⟨u, huR, rfl⟩ := exists_mul_of_isCp hp.out h2 hκ hw (regAt 𝔐.ξ q) hwq
  rw [hHT]
  refine ⟨h1, fun e he => ?_⟩
  rw [mul_smul]
  exact Submodule.smul_mem _ (⟨u, huR⟩ : regAt 𝔐.ξ q) (h3 e he)

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.generic_point_normal_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), ∀ e ∈ genericPoints Y.X, ∃ (K : Type) (_ : Field K) (_ : CharZero K) (n : ℕ) (x : Fin n → K) (y : Sp K ⟶ Xo.XF c), CoordTie ℤ (y ≫ Y.j) x ∧ Flat.NormalCpt (y ≫ Y.j) ∧ GlobalTheory.CompanionTheory.Ar.genPt (y ≫ Y.j) = e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.exists_cpt_of_genericPoint | exact GlobalTheory.CompanionTheory.Ar.XR.exists_cpt_of_genericPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.exists_cpt_of_genericPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.flat_gen_frame_complex_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : c.F, a ≠ 0 ∧ ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w = β a * φ₀ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.flatGen_unique | exact GlobalTheory.CompanionTheory.Ar.Flat.flatGen_unique | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.flatGen_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_lie_metric : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), Nonempty (LieMetric M y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MetricAny.exists_lieMetric | exact GlobalTheory.CompanionTheory.Ar.MetricAny.exists_lieMetric | (intros; apply GlobalTheory.CompanionTheory.Ar.MetricAny.exists_lieMetric <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

theorem _root_.GlobalTheory.T.lie_model_constants_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l)
    (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀]
    [CharZero Ω] [Algebra Ω₀ Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (cst : c.F →+* Ω₀) (V V' : Type) [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω₀ V) (ρ' : 𝓞 E →+* Module.End Ω V')
    (L : CMType H ⊕ CMType H → Lat ξ V) (j : V →+ V') (r : CMType H ⊕ CMType H → ℕ)
    (b : ∀ s, Fin (r s) → V'),
    IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) →
    (∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q)) →
    (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) →
    M'.lat = M.lat.pull ξ' f j →
    (∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
      j e ∈ eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) →
    (∀ s, ((L s).pull ξ' f j).IsFlagVBOn Set.univ (b s)) →
    ∀ s, (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))).IsFlagVBOn
      {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q} (b s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 | exact GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.point_frame_specialization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → y ≫ pullback.snd _ _ = spMap σ → (Z.eig τ).IsFrameAt b₁ ⟨_, h⟩ → (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt b₂ ⟨_, h⟩ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values | exact GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.TorsExist

open GlobalTheory.CompanionTheory.Ar.Sl.Transl

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem exists_mulGen {P : RigLB G} (c : CubicalStr G P) (hs : P.IsSymmetric) (N : ℕ) :
    ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen := by
  refine (genOf_pow c hs (𝟙 G) N).inv.gen P.isLB fun U _ h => ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, Over.id_left, mul_inv, inv_inv]
  norm_cast
  exact mul_comm _ _

theorem valF_spMap {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens)
    (a : Γ(X, U)) : valF (spMap f ≫ x) U a = f (valF x U a) := by
  have z' : Sp F' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F')
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · have h' : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U :=
      (top_le_iff_mem _ U z').2 ((top_le_iff_mem x U (spMap f z')).1 h)
    have e₀ : (spMap f).appLE ⊤ ⊤ (by first | exact le_rfl | simp) = (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have e : (spMap f ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap f).appTop := by
      rw [← e₀]
      exact (Scheme.Hom.appLE_comp_appLE (spMap f) x U ⊤ ⊤ h _).symm
    have n := congrArg (fun φ => φ.hom ((x.appLE U ⊤ h).hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    rw [valF, valF, dite_eq_left h, dite_eq_left h', e]
    exact n
  · have h' : ¬ ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U := fun k =>
      h ((top_le_iff_mem x U (spMap f z')).2 ((top_le_iff_mem _ U z').1 k))
    rw [valF, valF, dite_eq_right h, dite_eq_right h', map_zero]

theorem val_ne_zero {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)ˣ)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : valF x U f.val ≠ 0 := by
  unfold valF
  rw [dite_eq_left h]
  exact ((f.isUnit.map _).map _).ne_zero

theorem exists_torsVal {P : RigLB G} (c : CubicalStr G P) (hs : P.IsSymmetric) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F]
    {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) {N : ℕ} (hN : 1 ≤ N) (hy : y ^ N = 1) : ∃ T : F, TorsVal P s y N T := by
  obtain ⟨w, hw⟩ := exists_mulGen c hs N
  have z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  obtain ⟨i₀, h₀⟩ := exists_chart P.isLB ((1 : Over.mk b ⟶ G).left z)
  obtain ⟨i, hi⟩ := exists_chart P.isLB (y.left z)
  have e₁ : (1 : Over.mk b ⟶ G).left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    rw [left_pow, one_pow]
  have e₂ : b ≫ eSec G = (1 : Over.mk b ⟶ G).left := (one_left (Over.mk b)).symm
  have m₁ : (1 : Over.mk b ⟶ G).left z ∈ LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![i₀, i₀] := by
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show (((1 : Over.mk b ⟶ G).left ≫ ((𝟙 G : G ⟶ G) ^ N).left) z) ∈ P.L.U i₀
      rw [e₁]; exact h₀
    · exact h₀
  have m₂ : b z ∈ LB.wchart P.L (K := PUnit) (fun _ => eSec G) (fun _ => i₀) := by
    refine Set.mem_iInter.2 fun _ => ?_
    show (b ≫ eSec G) z ∈ P.L.U i₀
    rw [e₂]; exact h₀
  have n₁ := val_ne_zero _ _ (w.s ![i₀, i₀]) ((top_le_iff_mem _ _ z).2 m₁)
  have n₂ := val_ne_zero (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀) ((top_le_iff_mem _ _ z).2 m₂)
  refine ⟨valF y.left _ (s.f fun _ => i) ^ (N ^ 2) * valF y.left _ (w.s ![i₀, i]).val ^ n /
    (valF (1 : Over.mk b ⟶ G).left _ (w.s ![i₀, i₀]).val *
        valF (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n, hN, hy, w, i₀, i, hw,
    (top_le_iff_mem _ _ z).2 h₀, (top_le_iff_mem _ _ z).2 hi, ?_⟩
  exact div_mul_cancel₀ _ (pow_ne_zero _ (mul_ne_zero n₁ (pow_ne_zero _ n₂)))

theorem alg {R : Type*} [CommRing R] (t t' s : R) (A Y A' Y' r : Rˣ) (M n : ℕ) (hc : A' * A⁻¹ = Y' * Y⁻¹)
    (e : t * (A.val * r.val ^ M) ^ n = s ^ M * Y.val ^ n) (e' : t' * (A'.val * r.val ^ M) ^ n = s ^ M * Y'.val ^ n) :
    t = t' := by
  obtain ⟨c, rfl⟩ : ∃ c : Rˣ, A' = c * A := ⟨A' * A⁻¹, by simp⟩
  obtain rfl : Y' = c * Y := by
    have : c = Y' * Y⁻¹ := by simpa using hc
    rw [this]; simp
  simp only [Units.val_mul] at e'
  have u : IsUnit ((c.val * (A.val * r.val ^ M)) ^ n) := ((c.isUnit.mul A.isUnit).mul (r.isUnit.pow M)).pow n |>.map (RingHom.id R) |> fun h => by
    simpa [_root_.mul_assoc] using h
  apply u.mul_left_injective
  calc t * (c.val * (A.val * r.val ^ M)) ^ n = c.val ^ n * (t * (A.val * r.val ^ M) ^ n) := by rw [mul_pow]; ring
    _ = c.val ^ n * (s ^ M * Y.val ^ n) := by rw [e]
    _ = s ^ M * (c.val * Y.val) ^ n := by rw [mul_pow]; ring
    _ = t' * (c.val * A.val * r.val ^ M) ^ n := e'.symm
    _ = _ := by rw [_root_.mul_assoc]

theorem torsVal_unique (hp : Function.Surjective G.hom.appTop.hom) (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F]
    {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) {N : ℕ} {T T' : F} (hT : TorsVal P s y N T) (hT' : TorsVal P s y N T') : T = T' := by
  have z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  choose J hJ using fun χ : Sp F ⟶ G.left => exists_chart P.isLB (χ z)
  obtain ⟨w, hw, e⟩ := torsVal_charts P s y N T hT z J hJ
  obtain ⟨w', hw', e'⟩ := torsVal_charts P s y N T' hT' z J hJ
  have hb : (1 : Over.mk b ⟶ G).left ≫ G.hom = y.left ≫ G.hom := (Over.w (1 : Over.mk b ⟶ G)).trans (Over.w y).symm
  have hc := FG.v_const (z := z) (J := J) P.isLB ((mulFG w' hw').mul (mulFG w hw).inv) (fun U _ h => by
    simp only [FG.sum_mul, FG.sum_inv, sum_mulFG, mul_inv_cancel]) G.hom hp hb hJ
  rw [FG.v_mul hJ, FG.v_mul hJ, FG.v_inv, FG.v_inv] at hc
  exact (toStk z).injective (alg _ _ _ _ _ _ _ _ _ _ hc e e')

theorem torsVal_map {P : RigLB G} {n : ℕ} (s : Out.H0 P.L n) {F F' : Type} [Field F] [Field F'] (f : F →+* F') {b : Sp F ⟶ S}
    (y : Over.mk b ⟶ G) (y' : Over.mk (spMap f ≫ b) ⟶ G) (hy' : y'.left = spMap f ≫ y.left) {N : ℕ} {T : F}
    (hT : TorsVal P s y N T) : TorsVal P s y' N (f T) := by
  obtain ⟨hN, hy, w, i₀, i, hw, h₀, hi, hE⟩ := hT
  let g : Over.mk (spMap f ≫ b) ⟶ Over.mk b := Over.homMk (spMap f) rfl
  have ey : y' = g ≫ y := by ext1; exact hy'
  have e₁ : (1 : Over.mk (spMap f ≫ b) ⟶ G).left = spMap f ≫ (1 : Over.mk b ⟶ G).left := by
    rw [one_left, one_left]
    simp
  have z' : Sp F' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F')
  refine ⟨hN, by rw [ey, ← MonObj.comp_pow, hy, MonObj.comp_one], w, i₀, i, hw, ?_, ?_, ?_⟩
  · rw [e₁]
    exact (top_le_iff_mem _ _ z').2 ((top_le_iff_mem _ _ (spMap f z')).1 h₀)
  · rw [hy']
    exact (top_le_iff_mem _ _ z').2 ((top_le_iff_mem _ _ (spMap f z')).1 hi)
  · have := congrArg f hE
    simp only [map_mul, map_pow] at this
    simp only [e₁, hy', valF_spMap]
    exact this

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem appTop_surjective (D : PPData H L) : Function.Surjective D.t.G.hom.appTop.hom := by
  have cart := D.m.cart.1
  have := D.t.semi.smooth
  have := D.tK.semi.smooth
  have hprop : IsProper D.tK.G.hom := D.princ.1
  have hab := GlobalTheory.globalFns_holds _ D.tK.G (AbelianSchemeGerms.isAbelianScheme_of_proper D.tK.G D.tK.semi)
  have hj : Function.Injective (spMap (algebraMap (𝓞 L) L)).appTop :=
    specMap_appTop_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hinj := GlobalTheory.ProperFunctions.injective_appTop_of_isPullback cart hj
  have comp : ∀ {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Γ(Z, ⊤)),
      (a ≫ b).appTop.hom x = a.appTop.hom (b.appTop.hom x) := fun a b x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  let e' : Sp (𝓞 L) ⟶ D.t.G.left := eSec D.t.G
  have he : e' ≫ D.t.G.hom = 𝟙 _ := Over.w (η[D.t.G])
  let sK : Sp L ⟶ D.tK.G.left := cart.lift (spMap (algebraMap (𝓞 L) L) ≫ e') (𝟙 _) (by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : sK ≫ D.m.cm.F = spMap (algebraMap (𝓞 L) L) ≫ e' := cart.lift_fst _ _ _
  have h₂ : sK ≫ D.tK.G.hom = 𝟙 _ := cart.lift_snd _ _ _
  intro f
  obtain ⟨c, hc⟩ := hab.2 (D.m.cm.F.appTop.hom f)
  refine ⟨e'.appTop.hom f, hinj ?_⟩
  show D.m.cm.F.appTop.hom (D.t.G.hom.appTop.hom (e'.appTop.hom f)) = D.m.cm.F.appTop.hom f
  rw [← comp, ← comp, cart.w, Category.assoc, ← h₁, comp, comp, ← hc, ← comp sK, h₂]
  simp

theorem torsVal_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (F : Type) [Field F] (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → (∃! T : F, TorsVal D.t.PP s y N T) ∧ ∀ (F' : Type) [Field F'] (f : F →+* F') (y' : Over.mk (spMap f ≫ b) ⟶ D.t.G) (T : F), y'.left = spMap f ≫ y.left → TorsVal D.t.PP s y N T → TorsVal D.t.PP s y' N (f T) := by
  intro E _ _ _ H L _ _ D n s F _ b y N hN hy
  obtain ⟨T, hT⟩ := exists_torsVal D.t.cub D.t.sym s y hN hy
  exact ⟨⟨T, hT, fun T' hT' => torsVal_unique (appTop_surjective D) _ s y hT' hT⟩,
    fun F' _ f y' T e h => torsVal_map s f y y' e h⟩

end GlobalTheory.CompanionTheory.Ar.Sl.TorsExist
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_sections_cusp_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (a : WZ E) (x : ℝ), (Lat.secZ Xo c a 0 = secZ Xo c a ∧ Lat.cuspZ U a 0 = cuspZ Xo c U a ∧ Lat.lieZ Dw x a = lieFacZ Dw x a ∧ ∀ f, f ∈ Lat.latZ U a 0 ↔ f ∈ cuspZ Xo c U a ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) ∧ ∀ b, WEq Dw a b → secZ Xo c a = secZ Xo c b ∧ cuspZ Xo c U a = cuspZ Xo c U b ∧ lieFacZ Dw x a = lieFacZ Dw x b ∧ towerWt Dw a = towerWt Dw b ∧ (∀ σ, GoodEmb c σ → laZ (U σ) a = laZ (U σ) b) ∧ ∀ Z, cuspOn U h a Z = cuspOn U h b Z ∧ latOn U h a Z = latOn U h b Z := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws | exact GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws | (intros; apply GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_lie_model_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP), ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)) (lam : ∀ b, PureType.lat hP (sgnRt H b) → Fin g → X.K), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ b a u, X.IsImage b a u ↔ u = M.pt (lam b a)) ∧ (∀ b (s : 𝓞 E) a, lam b (s • a) = ρ s (lam b a)) ∧ (∀ b a a', lam b (a + a') = lam b a + lam b a') ∧ (∀ b (s : X.K) a, (s : ℂ) = sgnRt H b → ρ H.rt (lam b a) = s • lam b a) ∧ ∀ b (τ : E →+* ℂ) a v, X.IsCMVec b τ a v ↔ v = M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam b a)) := by
  first | exact @PositivityTheory.Xgf.cm_lie_model_action | exact PositivityTheory.Xgf.cm_lie_model_action
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.tangent_vector_lie_model_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (v : epsOver T.V T.V ⟶ G.G), IsTan v → ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan <;> assumption)
end
