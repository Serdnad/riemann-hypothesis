module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle138
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle139
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoords
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle144
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle006
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle142
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlagBasisAtStalk
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle140
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_isHopfOrder_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) := by
  exact @GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.charVal_multiplicative : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] (a : Sp A ⟶ S), (∀ t t' : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = charVal t' χ) → t = t') ∧ (∀ (t t' : Over.mk a ⟶ splitTorus S X) (χ : X), charVal (t * t') χ = charVal t χ * charVal t' χ) ∧ (∀ χ : X, charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1) ∧ (∀ (t : Over.mk a ⟶ splitTorus S X), charVal t 0 = 1 ∧ ∀ χ χ', charVal t (χ + χ') = charVal t χ * charVal t χ') ∧ (∀ w : Multiplicative X →* A, ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = w (Multiplicative.ofAdd χ)) ∧ ∀ (A' : Type) [CommRing A'] (g : A →+* A') (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk (spMap g ≫ a) ⟶ splitTorus S X), t'.left = spMap g ≫ t.left → ∀ χ, charVal t' χ = g (charVal t χ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusPoints.main | exact GlobalTheory.CompanionTheory.Ar.TorusPoints.main | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusPoints.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.snc_model_reindexed_coords : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K'] (J' : K' → Type) [∀ k, Fintype (J' k)] (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (e : ℕ) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → (∀ q₁ q₂ : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q₁) → g q₁.1 = g q₂.1 → q₁ = q₂) → Cmp.IsSncModel y e bd → Cmp.IsSncModel y' e (bd.map (MvPolynomial.rename fun p : (Σ k, J k) => (⟨bk p.1, bx p.1 p.2⟩ : Σ k, J' k))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRefine.isSncModel_refine | exact GlobalTheory.CompanionTheory.Ar.SncRefine.isSncModel_refine | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRefine.isSncModel_refine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TieArith

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar ReciprocityTheory.ChartRestriction.G.AI.I4

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem aeval_eq_ratioPt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    MvPolynomial.aeval y g = MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have h1 := mConeMap_eq_scale y c hc g
  rw [ConeTrdeg.mConeMap_of_isMultiHomog y hg, ConeTrdeg.mConeMap_of_isMultiHomog (ratioPt y c) hg] at h1
  have h2 : scaleT (fun k ↦ y ⟨k, c k⟩)
      (MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g) * ∏ k, MvPolynomial.X k ^ d k) =
      MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k) *
        ∏ k, MvPolynomial.X k ^ d k := by
    simp only [scaleT, map_mul, map_prod, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, mul_pow, Finset.prod_mul_distrib]
    ring
  rw [h2] at h1
  have h3 : (∏ k, MvPolynomial.X k ^ d k : MvPolynomial K Ω) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k)
  exact MvPolynomial.C_injective _ _ (mul_right_cancel₀ h3 h1)

theorem birational_of_ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) : Birational y := by
  intro s
  obtain ⟨d, g, h, hg, hh, n, e⟩ := rep_of_mem y c hc (x := s) (by rw [htop]; trivial)
  have hU : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · rw [aeval_eq_ratioPt y c hc hh]
    exact mul_ne_zero n hU
  · rw [aeval_eq_ratioPt y c hc hg, aeval_eq_ratioPt y c hc hh, e, _root_.mul_assoc]

theorem isArithVar_of_ratioField_eq_top [Nonempty K] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hd : Algebra.trdeg ℤ Ω = d) : IsArithVar (mCoordIdeal y) (d + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = d := by
    rw [hb, ← hd]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr]
  have h4 : (((d : Cardinal) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    rw [map_add (f := _), Cardinal.toENat_nat, Cardinal.toENat_nat]
    push_cast
    ring
  rw [h4]
  rfl

end Forms

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

def genCpt : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩

theorem mem_regAt_genCpt (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  show (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
    Scheme.stalkClosedPointTo ξ).hom s = a
  rw [e]
  exact hs

variable {K : Type} [Fintype K] {J : K → Type} [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)

theorem adjoin_le_ratioField {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) : a ∈ ratioField y c := by
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ (ratioField y c).toSubalgebra.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show _ ∈ ratioField y c
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, j k⟩, rfl⟩
  exact hle ha

end Chart

end GlobalTheory.CompanionTheory.Ar.TieArith

namespace GlobalTheory.CompanionTheory.Ar


open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar TieArith in
theorem coordTie_birational_isArithVar (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [Nonempty K] [CharZero Ω] (d : ℕ)
    (h : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hd : Algebra.trdeg ℤ Ω = d) : Birational y ∧ IsArithVar (mCoordIdeal y) (d + 1) := by
  obtain ⟨c, hchart⟩ := h.cover (TieArith.genCpt ξ)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦
    (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)
  have htop : GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ h c (TieArith.genCpt ξ) hchart a).mp
      (TieArith.mem_regAt_genCpt ξ h.gen a)
    have h1 := TieArith.adjoin_le_ratioField y c hs
    have h2 := TieArith.adjoin_le_ratioField y c hsa
    have h3 := div_mem h2 h1
    rwa [mul_div_cancel_left₀ _ hu.1] at h3
  exact ⟨TieArith.birational_of_ratioField_eq_top y c hc htop,
    TieArith.isArithVar_of_ratioField_eq_top y c hc htop d hd⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.EigDir

open GlobalTheory.HolHom GlobalTheory.DerivEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem isComb_iff_isCombAt (x : Sp ℂ ⟶ Xo.X) {n : ℕ} (c : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ Formalism.L2.Pj.IsCombAt x (fun i => (v i).left) c w.left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, by rw [hw]⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, Over.OverMorphism.ext hw.symm⟩

theorem isTanAt_of_isEigVec (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (v : epsAt x ⟶ Xo.univ.t.G)
    (h : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act x χ v) : Formalism.L2.Pj.IsTanAt x v.left :=
  ⟨Over.w v, h.1⟩

theorem isEigVec_of_isDerivAt0 (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty P) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (hχ : ∀ a : 𝓞 E, χ a = τ (a : E))
    (w : Fin g → ℂ) (hw : ∀ k, w k ≠ 0 → ty k = τ) (v : epsAt (FU.u i P) ⟶ Xo.univ.t.G)
    (hv : IsDerivAt0 (fun z => (FU.ex i P z).left) w v.left) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ v := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have hhol : HolAt (fun z => (FU.ex i P z).left) 0 := holAt_of_isHolTo (isHolTo_ex FU i hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  refine ⟨(h1 _ _ hv).2, fun a => ?_⟩
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
    ContinuousLinearMap.pi fun k => ty k (a : E) • ContinuousLinearMap.proj k
  have e1 := hv'.comp (Xo.univ.t.act.act a).left
  have e2 : (fun t => (FU.ex i P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (FU.ex i P (L t)).left := by
    funext t
    rw [← Over.comp_left, ← FU.ex_lin i P hP a t]
    rfl
  rw [e2] at e1
  have e3 := isDerivAt_of_comp_linear hhol L e1
  have e4 : L w = χ a • w := by
    funext k
    by_cases hk : w k = 0
    · simp [L, hk]
    · simp [L, hw k hk, hχ a]
  rw [e4] at e3
  exact e3.unique (isDerivAt_epsMul hv' _)

end GlobalTheory.CompanionTheory.Ar.Flat.EigDir


open GlobalTheory.CompanionTheory.Ar.Flat.EigDir in
theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σK : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (n : ℕ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)), IsPeriod (FU.Di i) ty P → x = FU.u i P → (∀ a : 𝓞 E, χ a = τ (a : E)) → IsEigFrame Xo.univ.t.act x χ v → ∃ V : Fin n → Fin g → ℂ, (∀ a u, IsDerivAt0 (fun z => (FU.ex i P z).left) u (v a).left ↔ u = V a) ∧ LinearIndependent ℂ V ∧ ∀ z, tyPart ty τ z ∈ Submodule.span ℂ (Set.range V) := by
  intro E _ _ _ H D l Xo σK g ty FU i P x χ τ n v hP hx hχ hF
  subst hx
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have ht : ∀ a, Formalism.L2.Pj.IsTanAt (FU.u i P) (v a).left := fun a => isTanAt_of_isEigVec _ χ _ (hF.1 a)
  choose V hV hVu using fun a => h3 _ (ht a)
  have comb : ∀ (c : Fin n → ℂ) (w : epsAt (FU.u i P) ⟶ Xo.univ.t.G),
      GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, c k • V k) w.left := fun c w =>
    (isComb_iff_isCombAt _ c v w).trans
      (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV c w.left)
  refine ⟨V, fun a u => ⟨fun h => hVu a u h, fun h => h ▸ hV a⟩, ?_, fun z => ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 0
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ 0 (fun k hk => absurd rfl hk) w hw
    obtain ⟨c₀, -, hu⟩ := hF.2 w hw'
    have a1 := hu c ((comb c w).2 (by rw [hc]; exact hw))
    have a2 := hu 0 ((comb 0 w).2 (by simpa using hw))
    intro k
    exact congrFun (a1.trans a2.symm) k
  · obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 (tyPart ty τ z)
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ _ (fun k hk => ?_) w hw
    · obtain ⟨c, hc, -⟩ := hF.2 w hw'
      have e := (h3 _ (isTanAt_of_isEigVec _ χ _ hw')).unique ((comb c w).1 hc) hw
      rw [← e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · by_contra hne
      exact hk (by simp [tyPart, hne])
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeCpt

theorem lieMult_label_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), LieMult 𝔐.t.act 𝔐.ξ (𝔐.emb s) (labelRk D s) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y 𝔐 s
  letI := 𝔐.acg
  letI := 𝔐.mod
  obtain ⟨U, hU, b, hspan, hfr⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_refl _⟩ (Set.mem_univ _)
  exact (Fl.Test.lieMult_iff_exists_frame _ _ _ _).2
    ⟨_, (Fl.Test.isEigFrame_iff 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act (𝔐.emb s) b).2
      ⟨(hfr _ (Set.mem_univ _) hU).1, hspan⟩⟩

end GlobalTheory.CompanionTheory.Ar.HodgeCpt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.pair_lattice_sum_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H), a ≠ b → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB (labelRk D a + labelRk D b) ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup | exact GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartFieldChange

theorem exists_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ := by
  intro E _ _ _ H S t L L' _ _ z P e
  obtain ⟨P', mK, mB, h₁, h₂, -⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange E H S t L L' z P e
  exact ⟨P', mK, mB, h₁, h₂⟩

end GlobalTheory.CompanionTheory.Ar.AbPartFieldChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_flag_basis_at_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ b : ∀ s, Fin (labelRk D s) → 𝔐.Li, (∀ s (i : ℕ), flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) ∧ (∀ s (i : ℕ), ∀ e ∈ flagStep Ω (b s) i, e ∈ 𝔐.M.lat p → e ∈ Submodule.span (regAt 𝔐.ξ p) (b s '' {k | (k : ℕ) < i})) ∧ LinearIndependent Ω (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ Submodule.span Ω (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) = ⊤ ∧ 𝔐.M.lat p = Submodule.span (regAt 𝔐.ξ p) (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames | exact GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_away_from_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), Function.Injective β → ∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → (∀ s, 𝔐.V s q = 𝔐.dR s q) ∧ (∀ p : ℕ, p.Prime → ∀ s, 𝔐.HT p s q = 𝔐.dR s q) ∧ 𝔐.M.lat q = ⨆ s, 𝔐.dR s q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero | exact GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

theorem _root_.GlobalTheory.T.frobenius_labels_shape : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E], (∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) → ∀ (H : Host E) (l : Level H) (c : Coeff l) [Fintype (CMType H)] [DecidableEq (CMType H)], ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p : ℕ, p.Prime → IsFrobLabels c p (φ p)) ∧ FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels | exact GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.eigen_lattice_vector_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → (Z.eig τ).IsVBOn Z.genFib D.p (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsVBOn Z.genFib D.q (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) ∧ (∀ x ∈ Z.genFib, ∃ g : ℕ, ∃ b : Fin g → Z.V, Z.M.lat.IsFrameAt b x ∧ ∀ σ' : E →+* ℂ, ∃ S : Finset (Fin g), Z.eig σ' x = Submodule.span (regAt _ x) (b '' S)) ∧ Z.genFib.Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib | exact GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib <;> assumption)
end
