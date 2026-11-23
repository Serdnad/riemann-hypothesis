module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigen
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle746
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle131
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle138
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Formalism.HarderNarasimhan.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle012
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_hodgeFiltrationOne_of_frobenius_pull_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 k) s (dp0 k) s (frobR p k hk) (GlobalTheory.VB.frob X p hX)) (c : FirstDeRham s), h.pull1 c = 0 → c ∈ F1 s := by
  first | exact @GlobalTheory.ConjSeq.mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero | exact GlobalTheory.ConjSeq.mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero | (intros; apply GlobalTheory.ConjSeq.mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.EigenDescent
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EigenDescent

theorem topIso_inv_eq_appLE {X : Scheme.{0}} (W : X.Opens) (h : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W) :
    W.topIso.inv = W.ι.appLE W ⊤ h :=
  (Scheme.Opens.topIso_inv W).trans (Eq.trans rfl (Scheme.Opens.ι_appLE W W ⊤ h).symm)

theorem topIso_inv_appTop {X Z : Scheme.{0}} (W : X.Opens) (y : Z ⟶ W.toScheme)
    (h : (⊤ : Z.Opens) ≤ (y ≫ W.ι) ⁻¹ᵁ W) :
    W.topIso.inv ≫ y.appTop = (y ≫ W.ι).appLE W ⊤ h := by
  have h0 : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  rw [topIso_inv_eq_appLE W h0]
  refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE y W.ι W ⊤ ⊤ h0 le_rfl)
  congr 1
  exact (Scheme.Hom.appLE_eq_app _).symm

theorem topIso_inv_restrict_appTop {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) :
    U.topIso.inv ≫ (π ∣_ U).appTop = π.app U ≫ (π ⁻¹ᵁ U).topIso.inv := by
  have h0 : (⊤ : (π ⁻¹ᵁ U).toScheme.Opens) ≤ (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ U) := fun x _ => x.2
  have h1 : ∀ g : (π ⁻¹ᵁ U).toScheme ⟶ Y, g = (π ⁻¹ᵁ U).ι ≫ π → ∀ h : ⊤ ≤ g ⁻¹ᵁ U,
      g.appLE U ⊤ h = π.app U ≫ (π ⁻¹ᵁ U).topIso.inv := by
    rintro _ rfl h
    rw [topIso_inv_eq_appLE _ h0, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [topIso_inv_appTop U (π ∣_ U) (fun x _ => ((π ∣_ U) x).2)]
  exact h1 _ (morphismRestrict_ι π U) _

theorem evU_val_restrict {X Z : Scheme.{0}} (W : X.Opens) (y : Z ⟶ W.toScheme)
    (h : ∀ z, (y ≫ W.ι) z ∈ W) (r : Γ(X, W)ˣ) :
    (evU (y ≫ W.ι) h r).val = y.appTop.hom (W.topIso.inv.hom r.val) := by
  have e := congrArg (fun φ => φ.hom r.val) (topIso_inv_appTop W y (fun z _ => h z))
  exact e.symm

theorem appTop_injective_of_epi {X Y : Scheme.{0}} (Q : X ⟶ Y) [Epi Q] :
    Function.Injective Q.appTop.hom := by
  intro a b hab
  have e : Q ≫ Out.TLinPf.mOf a = Q ≫ Out.TLinPf.mOf b := by
    rw [Out.TLinPf.comp_mOf, Out.TLinPf.comp_mOf, hab]
  rw [cancel_epi] at e
  rw [← Out.TLinPf.fnOf_mOf a, e, Out.TLinPf.fnOf_mOf]

theorem unit_descends : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] [IsAffineHom π] (U : Y.Opens) (r : Γ(X, π ⁻¹ᵁ U)ˣ),
    (∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ∀ z, g₁ z ∈ π ⁻¹ᵁ U) (h₂ : ∀ z, g₂ z ∈ π ⁻¹ᵁ U),
      g₁ ≫ π = g₂ ≫ π → evU g₁ h₁ r = evU g₂ h₂ r) →
    ∃ u : Γ(Y, U)ˣ, pullU π U u = r := by
  intro X Y π _ _ _ U r hr
  have hS : Surjective (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict π U).flip inferInstance
  have hA : IsAffineHom (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict π U).flip inferInstance
  have hE : Epi (π ∣_ U) := Flat.epi_of_flat_of_surjective _
  have key : ∀ {Z : Scheme.{0}} (y₁ y₂ : Z ⟶ (π ⁻¹ᵁ U).toScheme), y₁ ≫ π ∣_ U = y₂ ≫ π ∣_ U →
      evU (y₁ ≫ (π ⁻¹ᵁ U).ι) (fun z => (y₁ z).2) r = evU (y₂ ≫ (π ⁻¹ᵁ U).ι) (fun z => (y₂ z).2) r := by
    intro Z y₁ y₂ e
    refine hr Z _ _ _ _ ?_
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]
  obtain ⟨v, hv⟩ := Out.TLinPf.descend_gen (π ∣_ U) ((π ⁻¹ᵁ U).topIso.inv.hom r.val) (by
    intro Z y₁ y₂ e
    rw [← evU_val_restrict _ y₁ (fun z => (y₁ z).2), ← evU_val_restrict _ y₂ (fun z => (y₂ z).2),
      key y₁ y₂ e])
  obtain ⟨v', hv'⟩ := Out.TLinPf.descend_gen (π ∣_ U) ((π ⁻¹ᵁ U).topIso.inv.hom (r⁻¹).val) (by
    intro Z y₁ y₂ e
    rw [← evU_val_restrict _ y₁ (fun z => (y₁ z).2), ← evU_val_restrict _ y₂ (fun z => (y₂ z).2)]
    have k := key y₁ y₂ e
    simp only [evU, map_inv] at k ⊢
    rw [k])
  have hvv : v * v' = 1 := by
    apply appTop_injective_of_epi (π ∣_ U)
    rw [map_mul, hv, hv', ← map_mul, Units.mul_inv, map_one, map_one]
  have h1 : U.topIso.hom.hom v * U.topIso.hom.hom v' = 1 := by
    rw [← map_mul, hvv, map_one]
  refine ⟨⟨U.topIso.hom.hom v, U.topIso.hom.hom v', h1, by rw [mul_comm, h1]⟩, Units.ext ?_⟩
  change (π.app U).hom (U.topIso.hom.hom v) = r.val
  have e := congrArg (fun φ => φ.hom (U.topIso.hom.hom v)) (topIso_inv_restrict_appTop π U)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [Iso.hom_inv_id_apply, hv] at e
  exact ((π ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv.injective e).symm

end GlobalTheory.EigenDescent
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_scaled_periodPair : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair,
    (∀ z, c * z ∈ L'.lattice ↔ z ∈ L.lattice) ∧ L'.g₂ = (c ^ 4)⁻¹ * L.g₂ ∧
      L'.g₃ = (c ^ 6)⁻¹ * L.g₃ ∧
      (∀ z, L'.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z) ∧
      (latticeCurve L').j = (latticeCurve L).j := by
  intro L c hc
  have hH : IsHomothetic c L (scalePeriods L c hc) := isHomothetic_scalePeriods L c hc
  have h2 : (scalePeriods L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := by
    rw [PeriodPair.g₂, PeriodPair.g₂, hH.G_eq]; ring
  have h3 : (scalePeriods L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := by
    rw [PeriodPair.g₃, PeriodPair.g₃, hH.G_eq]; ring
  refine ⟨scalePeriods L c hc, hH, h2, h3, hH.derivWeierstrassP_mul, ?_⟩
  have hi : (c ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  have hD : (scalePeriods L c hc).g₂ ^ 3 - 27 * (scalePeriods L c hc).g₃ ^ 2 =
      (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h2, h3]; ring
  have hn : (scalePeriods L c hc).g₂ ^ 3 = (c ^ 12)⁻¹ * L.g₂ ^ 3 := by rw [h2]; ring
  rw [latticeCurve_j_eq, latticeCurve_j_eq, hD, hn, mul_left_comm, mul_div_mul_left _ _ hi]

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LatticeJInt

theorem main : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 →
    _root_.IsIntegral ℤ (latticeCurve L).j := by
  intro L β hβ him
  obtain ⟨c, τ, hτ⟩ := ReciprocityTheory.ChartRestriction.L1.latTau L
  have hj := GlobalTheory.JInt.main L c τ β hτ hβ him
  rw [← ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT hτ] at hj
  rw [latticeCurve_j_eq]
  exact hj

end GlobalTheory.CMModel.LatticeJInt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.HeckeLabels

section Abstract

theorem forall_exists_transfer {X X' Z Z' : Type} {L : X → Prop} {L' : X' → Prop} {I : Z → Prop} {I' : Z' → Prop}
    (p : X → X') (q : Z → Z') (p1 : ∀ y, L y → L' (p y)) (p2 : ∀ y', L' y' → ∃ y, L y ∧ p y = y')
    (q1 : ∀ z, I z → I' (q z)) (q2 : ∀ z', I' z' → ∃ z, I z ∧ q z = z') {P : X → Z → Prop} {P' : X' → Z' → Prop}
    (h : ∀ y z, P y z ↔ P' (p y) (q z)) :
    (∀ y, L y → ∃ z, I z ∧ P y z) ↔ ∀ y', L' y' → ∃ z', I' z' ∧ P' y' z' := by
  constructor
  · intro H y' hy'
    obtain ⟨y, hy, rfl⟩ := p2 y' hy'
    obtain ⟨z, hz, e⟩ := H y hy
    exact ⟨q z, q1 z hz, (h y z).1 e⟩
  · intro H y hy
    obtain ⟨z', hz', e⟩ := H _ (p1 y hy)
    obtain ⟨z, hz, rfl⟩ := q2 z' hz'
    exact ⟨z, hz, (h y z).2 e⟩

variable {R : Type} [CommRing R] {n : ℕ}

def StdDiv (O : Subring R) (ε : R) (t : Fin n → R) (m : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, z i ∈ O) → ∀ i, (ε • B *ᵥ z) i ∈ O) ∧
    (∀ y : Fin n → R, (∀ i, y i ∈ O) → ∃ z : Fin n → R, (∀ i, z i ∈ O) ∧ ε • y = ε • B *ᵥ z) ∧
    (∀ y : Fin n → R, (∀ i, y i ∈ O) → ∃ z : Fin n → R, (∀ i, z i ∈ O) ∧ ε • m *ᵥ y = ε • B *ᵥ (t * z)) ∧
    (∀ z : Fin n → R, (∀ i, z i ∈ O) → ∃ y : Fin n → R, (∀ i, y i ∈ O) ∧ ε • m *ᵥ y = ε • B *ᵥ (t * z))

theorem conj_mem_UJ (σ : R →+* R) {J J' : Matrix (Fin n) (Fin n) R} {h : GL (Fin n) R}
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = J') {g : GL (Fin n) R} (hg : g ∈ Formalism.UG.UJ σ J) :
    h⁻¹ * g * h ∈ Formalism.UG.UJ σ J' := by
  have hg' : Formalism.UG.cT σ g.1 * J * g.1 = J := hg
  show Formalism.UG.cT σ (h⁻¹ * g * h).1 * J' * (h⁻¹ * g * h).1 = J'
  have e : h.1 * (h⁻¹ * g * h).1 = g.1 * h.1 := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  calc _ = Formalism.UG.cT σ (h.1 * (h⁻¹ * g * h).1) * J * (h.1 * (h⁻¹ * g * h).1) := by
        rw [← hh, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ h.1 * (Formalism.UG.cT σ g.1 * J * g.1) * h.1 := by
        rw [e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg', hh]

theorem inv_frame (σ : R →+* R) {J J' : Matrix (Fin n) (Fin n) R} {h : GL (Fin n) R}
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = J') : Formalism.UG.cT σ (h⁻¹).1 * J' * (h⁻¹).1 = J := by
  calc _ = Formalism.UG.cT σ (h.1 * (h⁻¹).1) * J * (h.1 * (h⁻¹).1) := by
        rw [← hh, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_reps {G : Type} [Group G] {K : Subgroup G} {g : G}
    (hK : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) :
    ∃ R : Finset G, (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K :=
  _root_.UpperTheory.Reformulated.B.Yt3.exists_reps hK

theorem relIndex_conj_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J U L : Subgroup G}
    (hJ : IsCompact (J : Set G)) (hU : IsOpen (U : Set G)) (hL : ∀ k ∈ L, k ∈ U → k ∈ J) {g : G} (hg : g ∈ L) :
    ((J ⊓ L).map (MulAut.conj g).toMonoidHom).relIndex (J ⊓ L) ≠ 0 := by
  let U' : Subgroup G := U.comap (MulAut.conj g⁻¹).toMonoidHom
  have hU' : IsOpen (U' : Set G) := hU.preimage (show Continuous fun u : G => g⁻¹ * u * g⁻¹⁻¹ by fun_prop)
  have : CompactSpace J := isCompact_iff_compactSpace.1 hJ
  have h1 : U'.relIndex J ≠ 0 := by
    have : Finite (J ⧸ U'.subgroupOf J) :=
      Subgroup.quotient_finite_of_isOpen _ (hU'.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  have h2 : U'.relIndex (J ⊓ L) ≠ 0 := fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  rw [← Subgroup.inf_relIndex_right] at h2
  refine fun h => h2 (Subgroup.relIndex_eq_zero_of_le_left ?_ h)
  rintro k ⟨hk, hk'⟩
  have h3 : g⁻¹ * k * g⁻¹⁻¹ ∈ L := mul_mem (mul_mem (inv_mem hg) hk'.2) (inv_mem (inv_mem hg))
  exact ⟨g⁻¹ * k * g⁻¹⁻¹, ⟨hL _ h3 hk, h3⟩, by simp [mul_assoc]⟩

end Abstract

section Place

open GlobalTheory.PlaceComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : CMData F E) (V : HSpace E) {v : HeightOneSpectrum (𝓞 F)}

theorem divG_iff {e : AF F ⊗[F] E} (he : ∀ w, w ≠ v → evF E w (finP F E e) = 0)
    {h : GL (Fin V.rank) (Fv F v ⊗[F] E)} (hh : IsFrameAt V v h) (ϖ : E) (d : Fin V.rank → ℤ)
    (g : HA (AF F) hc.sig V.gram) :
    DivG hc V e ϖ d g ↔ StdDiv (ordAt E v) (evF E v (finP F E e)) (fun i => inclR (Fv F v) (ϖ ^ d i))
      (h⁻¹ * locMat hc V v g * h).1 := by
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1 *ᵥ ((h⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1 *ᵥ (h.1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let q : (Fin V.rank → Af F ⊗[F] E) → Fin V.rank → Fv F v ⊗[F] E := fun z i => evF E v (z i)
  let p : (Fin V.rank → Af F ⊗[F] E) → Fin V.rank → Fv F v ⊗[F] E := fun y => (h⁻¹).1 *ᵥ q y
  have p1 : ∀ y, y ∈ lamHat F V → ∀ i, p y i ∈ ordAt E v := fun y hy => (hh _).1 ((mem_lamHat_iff V _).1 hy v)
  have p2 : ∀ y' : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y' i ∈ ordAt E v) → ∃ y, y ∈ lamHat F V ∧ p y = y' :=
    fun y' hy' => ⟨_, GlobalTheory.PlaceDiv.sgT_mem_lamHat V v ((hh (h.1 *ᵥ y')).2 (by rwa [hback'])), by
      simp only [p, q, evF_sgT_self]; exact hback' y'⟩
  have q1 : ∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∀ i, q z i ∈ ordAt E v :=
    fun z hz i => (IntLocal.mem_intA_iff F E _).1 (hz i) v
  have q2 : ∀ z' : Fin V.rank → Fv F v ⊗[F] E, (∀ i, z' i ∈ ordAt E v) →
      ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧ q z = z' :=
    fun z' hz' => ⟨_, fun i => GlobalTheory.PlaceDiv.sgT_mem_intA v (hz' i), funext fun i => evF_sgT_self v _⟩
  have qv : ∀ (A : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E)) z, q (A *ᵥ z) = A.map (evF E v) *ᵥ q z :=
    fun A z => funext fun i => RingHom.map_mulVec (evF E v) A z i
  have qe : ∀ X, q (fun a => finP F E e * X a) = evF E v (finP F E e) • q X :=
    fun X => funext fun i => map_mul (evF E v) _ _
  have key : ∀ X Y : Fin V.rank → Af F ⊗[F] E, ((fun a => finP F E e * X a) = fun a => finP F E e * Y a) ↔
      evF E v (finP F E e) • p X = evF E v (finP F E e) • p Y := by
    intro X Y
    simp only [p, ← Matrix.mulVec_smul, ← qe]
    refine ⟨fun H => by rw [H], fun H => funext fun a => evF_ext fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      have := congrArg (h.1 *ᵥ ·) H
      simp only [hback] at this
      exact congrFun this a
    · rw [map_mul, map_mul, he w hw, zero_mul, zero_mul]
  have pB : ∀ (B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E)) z,
      p (B *ᵥ z) = ((h⁻¹).1 * B.map (evF E v)) *ᵥ q z := fun B z => by
    simp only [p, qv, Matrix.mulVec_mulVec]
  have pg : ∀ y, p (finMat hc.sig V.gram g *ᵥ y) = (h⁻¹ * locMat hc V v g * h).1 *ᵥ p y := fun y => by
    simp only [p, qv, Units.val_mul, ← Matrix.mulVec_mulVec, hback, locMat_val]
  have qt : ∀ z : Fin V.rank → Af F ⊗[F] E, q (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) =
      (fun i => inclR (Fv F v) (ϖ ^ d i)) * q z := fun z => funext fun i => by
    show evF E v _ = _ * evF E v _
    rw [map_mul, evF_finP_incl]
  have c1 : ∀ X : Fin V.rank → Af F ⊗[F] E, (fun a => finP F E e * X a) ∈ lamHat F V ↔
      ∀ i, (evF E v (finP F E e) • p X) i ∈ ordAt E v := by
    intro X
    simp only [p, ← Matrix.mulVec_smul, ← qe]
    refine ⟨p1 _, fun H => (mem_lamHat_iff V _).2 fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      exact (hh _).2 H
    · simp only [map_mul, he w hw, zero_mul]
      exact zero_mem _
  have sB : ∀ B' : Matrix (Fin V.rank) (Fin V.rank) (Fv F v ⊗[F] E),
      ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E), (h⁻¹).1 * B.map (evF E v) = B' := fun B' => by
    refine ⟨(h.1 * B').map (sgT E v), ?_⟩
    have : ((h.1 * B').map (sgT E v)).map (evF E v) = h.1 * B' := Matrix.ext fun i j => evF_sgT_self v _
    rw [this, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold DivG StdDiv
  rw [Function.Surjective.exists sB]
  refine exists_congr fun B => and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · intro H z' hz'
      obtain ⟨z, hz, rfl⟩ := q2 z' hz'
      rw [← pB, ← c1]
      exact H z hz
    · intro H z hz
      rw [c1, pB]
      exact H _ (q1 z hz)
  · exact forall_exists_transfer p q p1 p2 q1 q2 fun y z => by rw [key, pB]
  · exact forall_exists_transfer p q p1 p2 q1 q2 fun y z => by rw [key, pg, pB, qt]
  · exact forall_exists_transfer q p q1 q2 p1 p2 fun z y => by rw [key, pg, pB, qt]

end Place

section CM

open GlobalTheory.PlaceComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_div_iff (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    {e f : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (hf : IsIdemOf E v f) (hef : e * f = e)
    (ϖ : E) (d : ℕ → ℤ) {n : ℕ} (hn : V.rank = n) :
    (∃ g, Supp hc V f g ∧ DivG hc V e ϖ (fun i => d i.1) g) ↔
      ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
        StdDiv (ordAt E v) (evF E v (finP _ E e)) (fun i => inclR (Fv _ v) (ϖ ^ d i.1)) u.1 := by
  subst hn
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  have he : ∀ w, w ≠ v → evF E w (finP _ E e) = 0 := fun w hw => by
    rw [← hef, map_mul, map_mul, hf.2.2 w hw, mul_zero]
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨_, conj_mem_UJ _ hon (locMat_mem hc V v g), (divG_iff hc V he hfr ϖ _ g).1 hg⟩
  · rintro ⟨u, hu, hd⟩
    obtain ⟨g, hg, e1⟩ := (GlobalTheory.SuppLocal.supp_local _ E hc V v f hf).2.2 _ (conj_mem_UJ _ (inv_frame _ hon) hu)
    refine ⟨g, hg, (divG_iff hc V he hfr ϖ _ g).2 ?_⟩
    have : h⁻¹ * locMat hc V v g * h = u := by rw [e1]; group
    rwa [this]

end CM

section Host

open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Host

end GlobalTheory.HeckeLabels
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_cartier_locus_over_dense_open_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ (U : (Sp R).Opens) (c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme), (U : Set (Sp R)).Nonempty ∧ IsLocus c ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.DivStart.exists_locus_over_dense_open | exact GlobalTheory.DivStart.exists_locus_over_dense_open | (intros; apply GlobalTheory.DivStart.exists_locus_over_dense_open <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonvanishingLocus_extend_from_big_open : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V W : X.Opens, IsAffineOpen V → V ≤ W → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic X, IsLocus (GlobalTheory.CechPic.pull W.ι c) (W.ι ⁻¹ᵁ V) → IsLocus c V := by
  first | exact @GlobalTheory.extend_isLocus_of_big_open | exact GlobalTheory.extend_isLocus_of_big_open | (intros; apply GlobalTheory.extend_isLocus_of_big_open <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.range_relativeFrobenius_primitiveDeRham_eq_conjugate : GlobalTheory.Published.AbelianDeRham.BaseChange → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left) (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) (F : A ⟶ A₁) [IsMonHom F] (hF : F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A)) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LinearMap.range (primPull (dp0 R) (𝟙 _) F) = conjDR p R hR A ∧ PrimitiveSubmodule A₁ ≤ LinearMap.ker (primPull (dp0 R) (𝟙 _) F) := by
  first | exact @GlobalTheory.ConjSeq.range_primPull_relFrob | exact GlobalTheory.ConjSeq.range_primPull_relFrob | (intros; apply GlobalTheory.ConjSeq.range_primPull_relFrob <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.riemannianHaar_specialUnitary_eq_smul_haar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (ν : Measure (realSU X.Ψ X.Gm)), 1 ≤ r → IsOrth X x → ν.IsHaarMeasure → (∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x) → riemHaar X.Ψ X.Gm x = ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  first | exact @GlobalTheory.RiemConst.riemHaar_eq_smul | exact GlobalTheory.RiemConst.riemHaar_eq_smul | (intros; apply GlobalTheory.RiemConst.riemHaar_eq_smul <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.opNormAt_pairing_sq_le_of_value_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (c n : ℕ) (X : InfinitePlace K → Matrix (Fin c) (Fin c) ℂ) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K)) (v : InfinitePlace K) (A : ℝ), IsUnit (X v).det → IsUnit (X0 v).det → (∀ y F, v (g y F) ^ 2 ≤ Real.exp A * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin c)) X v y ^ 2 * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2) → Formalism.HN.opNormAt (Pi.basisFun K (Fin c)) X (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v g ^ 2 ≤ Real.exp A := by
  first | exact @GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le | exact GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le | (intros; apply GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.finite_semilocal_hom_lattice_classes_mod : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E L → Submodule.IsLattice E L' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ∧ Nat.card (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ≤ (cA * c) ^ (Module.finrank ℚ E * a * b) := by
  first | exact @GlobalTheory.SemilocalClasses.finite_card_classes | exact GlobalTheory.SemilocalClasses.finite_card_classes | (intros; apply GlobalTheory.SemilocalClasses.finite_card_classes <;> assumption)
end
