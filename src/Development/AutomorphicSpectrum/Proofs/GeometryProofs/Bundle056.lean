module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle009
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle040
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
import Aesop.Main
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.regular_rings_equal_images_equal : ∀ (P X₁ X₂ : Scheme.{0}) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ P) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (f₁ : X₁ ⟶ P) (f₂ : X₂ ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → IsCptGen ξ₁ → IsCptGen ξ₂ → ξ₁ ≫ f₁ = ξ₀ → ξ₂ ≫ f₂ = ξ₀ → ∀ (p₁ : Cpt ξ₁) (p₂ : Cpt ξ₂), regAt ξ₁ p₁ = regAt ξ₂ p₂ → f₁ p₁.1 = f₂ p₂.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq | exact GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.image_eq_of_regAt_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.dominates_of_coords_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω'), CoordTie o ξ x → IsCptGen ξ' → (∀ q : X', genPt ξ' ⤳ q) → (∀ (r : o) (p' : Cpt ξ'), i (algebraMap o Ω r) ∈ regAt ξ' p') → (∀ p' : Cpt ξ', ∃ c, InChart ξ' (fun k => i (x k)) c p') → ∃ f : X' ⟶ X, Dominates ξ' ξ f i ∧ ∀ (p' : Cpt ξ') (c : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map | exact GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem z_value_of_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u :=
  @PositivityTheory.Xgn.valuation_at_centre_order

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtHoriz

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] {L : Type} [AddCommGroup L] [Module R L]

theorem map_add_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (a b : L) : j (a + b) = j a + j b := by
  have key : ∀ e, M.pt (j e) = LieCarrier.epsHom k x ξ hx ≫ M₀.pt e :=
    fun e => Over.OverMorphism.ext (hj e)
  apply M.inj
  rw [M.add, key, key, key, M₀.add, MonObj.comp_mul]

theorem map_smul_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (c : R) (e : L) : j (c • e) = k c • j e := by
  apply M.inj
  apply Over.OverMorphism.ext
  rw [hj, M₀.smul, M.smul, hj, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, LieCarrier.dualMap_epsMul]

theorem isHT_add_natCast_smul {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {i : Γ.G.left ⟶ G.left}
    {L : Type} [AddCommGroup L] [Module R L] {M : LieModel G x L} {N : ℕ} {χ : T →* Rˣ}
    {w : Module.Dual R L} (h : Γ.IsHT i M N χ w) (u : Module.Dual R L) :
    Γ.IsHT i M N χ (w + (N : R) • u) := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := h e
  refine ⟨v, h1, h2, h3.trans ?_⟩
  congr 2
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨-u e, by simp⟩

theorem natCast_smul_isHTFormOver (M : LieModel G ξ E) (N : ℕ) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (hk : Function.Injective k) (h : M.IsHTFormOver N x k 0)
    (w : Module.Dual Ω E)
    (hw : ∀ (e : E) (v : epsAt x ⟶ G), IsTanAt G x v →
      (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left → w e ∈ k.range) :
    M.IsHTFormOver N x k ((N : Ω) • w) := by
  obtain ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, ht, hj, hHT, h0⟩ := h
  have hreg : ∀ e, ∃ r, k r = w (j e) := fun e => hw (j e) (M₀.pt e) (M₀.tan e) (hj e)
  choose f hf using hreg
  let u : Module.Dual R L :=
    { toFun := f
      map_add' := fun a b => hk (by rw [map_add (f := _), hf, hf, hf, map_add_of_compat M hx M₀ j hj, map_add (f := _)])
      map_smul' := fun c e => hk (by
        simp only [RingHom.id_apply, smul_eq_mul, map_mul]
        rw [hf, hf, map_smul_of_compat M M₀ j hj, map_smul, smul_eq_mul]) }
  refine ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀ + (N : R) • u, ht, hj, isHT_add_natCast_smul Γ hHT u, fun e => ?_⟩
  have h1 : k (w₀ e) = 0 := (h0 e).symm
  have h2 : k (u e) = w (j e) := hf e
  simp [h1, h2]

end GlobalTheory.CompanionTheory.Ar.HtHoriz

namespace GlobalTheory.CompanionTheory.Ar

theorem htLat_le_omLat_and_smul_mem : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (N : ℕ) (p : Cpt ξ),
    IsCptGen ξ → Smooth G.hom → M.htLat N p ≤ M.omLat p ∧
      (M.IsHTFormAt N p 0 → ∀ w ∈ M.omLat p, (N : Ω) • w ∈ M.htLat N p) := by
  intro X Ω _ ξ G _ _ V _ _ M N p hξ _
  refine ⟨?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro w ⟨_, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, -, hj, -, hw⟩ e he
    obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ V M p).1 e).1 he
    obtain ⟨e₀, rfl⟩ := M₀.onto v hv
    have : j e₀ = e := M.inj (Over.OverMorphism.ext ((hj e₀).trans hev.symm))
    subst this
    exact ⟨w₀ e₀, (hw e₀).symm⟩
  · intro h w hw
    exact Submodule.subset_span (HtHoriz.natCast_smul_isHTFormOver M N (LieCarrier.genMap_fromSpecStalk p) (hξ.inj p) h w
      fun e v hv hev => hw e (Submodule.subset_span ⟨v, hv, hev⟩))

end GlobalTheory.CompanionTheory.Ar
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.complex_point_conjugate : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ), PtOver y φ σ z → PtOver y φ (ComplexEmbedding.conjugate σ) (fun p => (starRingEnd ℂ) (z p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ptOver_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.ptOver_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ptOver_conj <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem nonvanishing_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact @PositivityTheory.Xgn.nonvanishing_points_dense

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_ptOver_ne : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (g : MRing ι) (d : K → ℕ), OverInt y φ → IsMultiHomog g d → g ∉ mCoordIdeal y → ∃ z, PtOver y φ σ z ∧ evC z g ≠ 0 :=
  @PositivityTheory.Xgn.exists_point_over_nonvanishing

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_rep_avoiding : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ), IsMultiProjPrime P → IsMultiProjPrime W → P ≤ W → IsMultiHomog f df → IsMultiHomog g dg → g ∉ P → IsUnitSec P f g → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = (df k : ℤ) - dg k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * g - g' * f ∈ P ∧ IsUnitSec P f' g' :=
  @PositivityTheory.Xgn.exists_representative_avoiding_ideal

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.CompanionTheory.Relay.normal_affine_chart_exists : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ q : Cpt ξ, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω), IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsOpenImmersion x ∧ q.1 ∈ Set.range x ∧ (∀ y ∈ Set.range x, genPt ξ ⤳ y) ∧ spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ := by
  first | exact @PositivityTheory.HtPt.Mk.ht_lat_chart | exact PositivityTheory.HtPt.Mk.ht_lat_chart
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

section Basic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem conjPt_conjPt (z : (Σ k, ι k) → ℂ) : conjPt (conjPt z) = z := by
  funext p
  simp [conjPt]

theorem evC_conjPt (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    evC (conjPt z) f = starRingEnd ℂ (evC z f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq =>
    simp only [evC, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]
    simp [conjPt]

def conjCLM : ((Σ k, ι k) → ℂ) →L[ℝ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p =>
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (Σ k, ι k) => ℂ) p)

theorem conjCLM_apply (z : (Σ k, ι k) → ℂ) : conjCLM z = conjPt z := by
  funext p
  simp [conjCLM, conjPt]

theorem conjPt_mem_mcPts_iff (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) :
    conjPt z ∈ mcPts P ↔ z ∈ mcPts P := by
  have key : ∀ w : (Σ k, ι k) → ℂ, w ∈ mcPts P → conjPt w ∈ mcPts P := by
    rintro w ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := h1 k
      exact ⟨i, by simpa [conjPt] using hi⟩
    · have := evC_conjPt w f
      simp only [evC] at this
      rw [this, h2 f hf, map_zero]
  refine ⟨fun h => ?_, key z⟩
  simpa [conjPt_conjPt] using key _ h

theorem conjLine_smooth (A : HermLine ι) (hA : IsSmoothHerm A) : IsSmoothHerm (conjLine A) := by
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => conjCLM z)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := (conjCLM (ι := ι)).contDiff.contDiffOn
  have := ContDiffOn.comp (g := A.h) (f := fun z : (Σ k, ι k) → ℂ => conjCLM z)
    (s := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (t := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA hc (fun z hz k => by
      obtain ⟨i, hi⟩ := hz k
      refine ⟨i, ?_⟩
      show conjCLM z ⟨k, i⟩ ≠ 0
      rw [conjCLM_apply]
      simpa [conjPt] using hi)
  unfold IsSmoothHerm
  refine this.congr fun z _ => ?_
  simp [conjLine, conjCLM_apply]

theorem logNorm_conjLine (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm (conjLine A) s z = logNorm A s (conjPt z) := by
  have h := evC_conjPt z s
  simp only [evC] at h
  simp only [logNorm, conjLine]
  rw [h, RCLike.norm_conj]

theorem conjLine_tensor (A B : HermLine ι) :
    conjLine (A.tensor B) = (conjLine A).tensor (conjLine B) := rfl

theorem conjLine_conjLine (A : HermLine ι) : conjLine (conjLine A) = A := by
  cases A with
  | mk a h pos smul =>
    simp only [conjLine, HermLine.mk.injEq, heq_eq_eq, true_and]
    funext z
    rw [conjPt_conjPt]

end Basic

theorem conj_basic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], (∀ (P : Ideal (MRing ι)) z, conjPt z ∈ mcPts P ↔ z ∈ mcPts P) ∧ (∀ (z : (Σ k, ι k) → ℂ) f, evC (conjPt z) f = starRingEnd ℂ (evC z f)) ∧ (∀ A : HermLine ι, IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ (∀ (A : HermLine ι) s z, logNorm (conjLine A) s z = logNorm A s (conjPt z)) ∧ (∀ A B : HermLine ι, conjLine (A.tensor B) = (conjLine A).tensor (conjLine B)) ∧ ∀ A : HermLine ι, conjLine (conjLine A) = A :=
  fun _ _ _ _ => ⟨conjPt_mem_mcPts_iff, evC_conjPt, conjLine_smooth, logNorm_conjLine, conjLine_tensor, conjLine_conjLine⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtEnd

theorem pullPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {A B : Over X} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.comp_mul, ih]

theorem homPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {Z : Over X} (a : G ⟶ G) [IsMonHom a] (x : Z ⟶ G) (n : ℕ) :
    (x ^ n) ≫ a = (x ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.mul_comp, ih]

theorem epiSp {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  haveI : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom a)) := by
    rw [AlgebraicGeometry.surjective_iff]
    intro y
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

theorem powDescend {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω K : Type} [Field Ω] [Field K]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {N : ℕ} (a : Ω →+* K)
    {g₀ : Over.mk ξ ⟶ G} {g : Over.mk (spMap a ≫ ξ) ⟶ G} (e : g.left = spMap a ≫ g₀.left) (hg : g ^ N = 1) :
    g₀ ^ N = 1 := by
  let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a)
  haveI : Epi ψ := Over.epi_of_epi_left ψ (hk := epiSp a)
  have hψ : ψ ≫ g₀ = g := Over.OverMorphism.ext (by simp [ψ, e])
  apply (cancel_epi ψ).mp
  rw [pullPow, hψ, hg, CategoryTheory.MonObj.comp_one]

theorem secVal_app {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z ⟶ Z')
    (W : Z'.Opens) (f : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) :
    secVal x (φ ⁻¹ᵁ W) h ((φ.app W).hom f) = secVal (x ≫ φ) W h' f := by
  simp only [secVal, Scheme.Hom.comp_appLE]
  rfl

end GlobalTheory.CompanionTheory.Ar.HtEnd


open GlobalTheory.CompanionTheory.Ar.HtEnd in
theorem GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  intro X _ Ω _ _ ξ _ _ G _ _ L n _ hFT ep hW E _ _ M a _ A hA y y' hy hy' hyy' q w hH
  obtain ⟨hw, W, f, hη, P1, P2⟩ := hH
  have hExt : ∀ {e' : E} {v}, M.Extends q e' v → M.Extends q (A e') (v ≫ a) := by
    intro e' v hv
    refine ⟨?_, ?_⟩
    · have h1 := hv.1
      unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, CategoryTheory.MonObj.one_comp]
    · rw [hA e', Over.comp_left, hv.2]
      erw [Category.assoc]
  have hlat : ∀ e' ∈ M.lat q, A e' ∈ M.lat q := by
    intro e' he'
    have hle : M.lat q ≤ (M.lat q).comap (A.restrictScalars (regAt ξ q)) := by
      refine Submodule.span_le.mpr ?_
      rintro e'' ⟨v, hv⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      exact Submodule.subset_span ⟨v ≫ a, hExt hv⟩
    exact hle he'
  have hw' : ∀ e' ∈ M.lat q, w e' ∈ regAt ξ q := hw
  refine ⟨?_, a.left ⁻¹ᵁ W, (a.left.app W).hom f, ?_, ?_, ?_⟩
  · show ∀ e' ∈ M.lat q, (w ∘ₗ A) e' ∈ regAt ξ q
    intro e' he'
    exact hw' (A e') (hlat e' he')
  · have h1 : (η[G] ≫ a).left = (η[G]).left := by rw [IsMonHom.one_hom]
    show a.left ((η[G]).left q.1) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
    exact hη
  · intro k _ _ i xk g c h hx hg hWe
    have h2 : ⊤ ≤ (g.left ≫ a.left) ⁻¹ᵁ W := h
    rw [secVal_app g.left a.left W f h h2]
    obtain ⟨g₀, hg₀⟩ := hFT k i g hg
    have hg₀n : g₀ ^ n = 1 := powDescend i hg₀ hg
    have hga : (g ≫ a) ^ n = 1 := by rw [← homPow, hg, CategoryTheory.MonObj.one_comp]
    have hg₀a : (g₀ ≫ a) ^ n = 1 := by rw [← homPow, hg₀n, CategoryTheory.MonObj.one_comp]
    have hc : (c : k) = i (ep y' g₀) := (hW.weil y' g₀ hy' hg₀n k i xk g c hx hg₀).mp hWe
    rw [hyy' g₀ hg₀n] at hc
    let xk0 : Over.mk (spMap i ≫ ξ) ⟶ G := Over.homMk (spMap i ≫ y.left)
    have hg' : (g ≫ a).left = spMap i ≫ (g₀ ≫ a).left := by
      rw [Over.comp_left, Over.comp_left, hg₀, Category.assoc]
    have hWa := (hW.weil y (g₀ ≫ a) hy hg₀a k i xk0 (g ≫ a) c rfl hg').mpr hc
    exact P1 k i xk0 (g ≫ a) c h2 rfl hga hWa
  · intro e' v hv h
    have h2 : ⊤ ≤ (v.left ≫ a.left) ⁻¹ᵁ W := h
    obtain ⟨r, hr, hE⟩ := P2 (A e') (v ≫ a) (hExt hv) h2
    refine ⟨r, hr, ?_⟩
    rw [LinearMap.comp_apply, secVal_app v.left a.left W f h h2]
    exact hE
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HostAutTrans

theorem existsUnique_hostAut_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [IsGalois ℚ E] (τ τ' : E →+* ℂ), τ (H.rt : E) = H.rt0 → τ' (H.rt : E) = H.rt0 → ∃! g : HostAut H, τ' = τ.comp g.σ.toRingHom := by
  intro E _ _ _ H _ τ τ' hτ hτ'
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) τ τ'
    (Subsingleton.elim _ _)
  have key : ∀ x, τ' x = τ (σ.symm x) := fun x => by rw [← hσ]; rfl
  refine ⟨⟨σ.symm.toRingEquiv, τ.injective ((key _).symm.trans (hτ'.trans hτ.symm))⟩, ?_, ?_⟩
  · exact RingHom.ext fun x => key x
  · rintro ⟨g₀, hfix⟩ hg
    have hx : ∀ x, g₀ x = σ.symm x := fun x =>
      τ.injective ((RingHom.congr_fun hg x).symm.trans (key x))
    have h0 : g₀ = σ.symm.toRingEquiv := RingEquiv.ext fun x => hx x
    subst h0
    rfl

end GlobalTheory.CompanionTheory.Ar.HostAutTrans
end
