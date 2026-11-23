module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle034
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle122
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentIntegralClosure
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperModelGenericFibreCompare
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem valR_mem_adjoin_of_affine {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} (ξ : Sp Ω ⟶ X)
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ξ W₀ h₀).hom = A) {O : X.Opens} (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (t : Γ(X, O)) :
    valR ξ O t ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  have hmem : ∀ a : Γ(X, W₀), valR ξ W₀ a ∈ IntermediateField.adjoin ℚ (A : Set Ω) := fun a => by
    apply IntermediateField.subset_adjoin
    rw [valR_eq ξ W₀ h₀, ← hA]
    exact ⟨a, rfl⟩
  let z : Sp Ω := IsLocalRing.closedPoint Ω
  obtain ⟨b, hbO, hxb⟩ := hW₀.exists_basicOpen_le (V := O) ⟨ξ z, hO trivial⟩ (h₀ trivial)
  have hD : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen b := fun y _ => by
    rw [Subsingleton.elim y z]
    exact hxb
  have hloc := hW₀.isLocalization_basicOpen b
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers b)
    ((X.presheaf.map (homOfLE hbO).op).hom t)
  have hres : ∀ c : Γ(X, W₀), valR ξ (X.basicOpen b) (algebraMap Γ(X, W₀) Γ(X, X.basicOpen b) c) =
      valR ξ W₀ c := fun c => valR_res ξ (X.basicOpen_le b) hD c
  have hv := congrArg (valR ξ (X.basicOpen b)) h
  simp only at hv
  rw [valR_mul ξ _ hD, valR_res ξ hbO hD, hres, hres, valR_pow ξ _ h₀] at hv
  have hunit : valR ξ W₀ b ≠ 0 := ((le_preimage_basicOpen_iff ξ h₀ b).1 hD).ne_zero
  have e : valR ξ O t = valR ξ W₀ a / valR ξ W₀ b ^ n := by
    rw [eq_div_iff (pow_ne_zero n hunit)]
    exact hv
  rw [e]
  exact div_mem (hmem a) (pow_mem (hmem b) n)

theorem valR_appIso_inv {C : Type} [CommRing C] {X Y : Scheme.{0}} (r : Y ⟶ X) [IsOpenImmersion r] (y : Sp C ⟶ Y)
    (V : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V) (t : Γ(Y, V)) :
    valR (y ≫ r) (r ''ᵁ V) ((r.appIso V).inv.hom t) = valR y V t := by
  rw [← valR_appLE y r (r.preimage_image_eq V).ge h, ← Scheme.Hom.appIso_hom']
  congr 1
  exact congrArg (fun φ => φ.hom t) (r.appIso V).inv_hom_id

theorem valR_mem_adjoin_of_modification : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  intro Ω _ _ X X' ξ _ _ f U _ ζ hζ hU W₀ hW₀ h₀ A hA W' h' s
  haveI : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hr : Set.range ζ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hU (Set.mem_univ y)
  let y : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι ζ hr
  have hy : y ≫ (f ⁻¹ᵁ U).ι = ζ := IsOpenImmersion.lift_fac _ _ _
  have hyr : y ≫ ((f ⁻¹ᵁ U).ι ≫ f) = ξ := by rw [← Category.assoc, hy, hζ]
  have hV : ⊤ ≤ y ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ W') := fun z hz => by
    have : z ∈ ζ ⁻¹ᵁ W' := h' hz
    rw [← hy] at this
    exact this
  have e1 : valR ζ W' s = valR y _ (((f ⁻¹ᵁ U).ι.app W').hom s) := by
    conv_lhs => rw [← hy]
    exact valR_comp y _ W' s
  rw [e1, ← valR_appIso_inv ((f ⁻¹ᵁ U).ι ≫ f) y _ hV]
  subst hyr
  exact valR_mem_adjoin_of_affine _ hW₀ h₀ A hA (fun z hz => ((( (f ⁻¹ᵁ U).ι ≫ f).preimage_image_eq _).ge (hV hz) : _)) _

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.dot_dual_lattice_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.dotDual_latFamily | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.dotDual_latFamily | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.dotDual_latFamily <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.hermitian_pairing_torsion_free : ∀ (E : Type) [Field E] [NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact p.Prime], 1 ≤ R → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)), (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv cc a • y)) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ¬ IsUnit (p : O) → ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) → ∃ C : Matrix (Fin N) (Fin N) Ω, (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ (Matrix.of fun i j => ∑ k, σ (HT.dualInt E k) * ((e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)) * C = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem trivflag_nef_fibre : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : Top.RootModel Ψ N) [CharZero M.Ω] (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o M.Ω] (ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω)), (∀ τ, Num.TrivFlagMod o (p : o) M.y N (fun i => M.xdeg (τ, i))) → ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0 :=
  @PositivityTheory.HtPt.Gf.trivflag_nef

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.dvr_localization_constants : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem _root_.GlobalTheory.T.model_descent_integral_closure : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O), Irreducible ϖ → ∀ p : ℕ, (p ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair J O (Ψ × Fin N)), T.IsVert (pointIdeal O y) ϖ → FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p j φ (T.map (algebraMap O O')) → FlagChernComparison (pointIdeal O y) d p j φ T) ∧ ∀ (r s : ℕ) (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)), lie.IsVert (pointIdeal O y) ϖ → om.IsVert (pointIdeal O y) ϖ → BundleChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (lie.map (algebraMap O O')) (om.map (algebraMap O O')) → BundleChernComparison (pointIdeal O y) d p lie om := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.model_descends_from_dvr_ext | exact GlobalTheory.CompanionTheory.Ar.Num.model_descends_from_dvr_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.model_descends_from_dvr_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.torsion_subgroup_base_change : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.BaseChange.torsion_isBaseChange | exact GlobalTheory.CompanionTheory.Ar.BT.BaseChange.torsion_isBaseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.BaseChange.torsion_isBaseChange <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptTrdeg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem trdeg_residueField_of_isIntegral {K B : Type} [Field K] [CharZero K] [CommRing B] [Algebra K B]
    [Algebra.IsIntegral K B] (q : Ideal B) [q.IsPrime] :
    Algebra.trdeg ℤ q.ResidueField = Algebra.trdeg ℤ K := by
  have hcm : (Ideal.comap (algebraMap K B) q).IsMaximal :=
    Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)
  have hmax : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := K) q hcm
  have hs : Function.Surjective (IsScalarTower.toAlgHom K B q.ResidueField) :=
    Ideal.algebraMap_residueField_surjective q
  have : Algebra.IsIntegral K q.ResidueField := Algebra.IsIntegral.of_surjective _ hs
  have : CharZero q.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K q.ResidueField).injective
  have h0 : Algebra.trdeg K q.ResidueField = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq ℤ K (A := q.ResidueField), h0, add_zero]

theorem trdeg_int_eq_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (e : A ≃+* B) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ B :=
  (AlgEquiv.ofRingEquiv (f := e) (fun n => by simp [eq_intCast (algebraMap ℤ A), eq_intCast (algebraMap ℤ B)])).trdeg_eq

theorem residueFieldMap_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun b => ?_⟩
  obtain ⟨c, rfl⟩ := X.residue_surjective x b
  obtain ⟨d, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective f x c
  exact ⟨Y.residue (f x) d, congr($(Scheme.residue_residueFieldMap f x).hom d)⟩

theorem trdeg_residueField_of_fst {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] [CharZero Ω₀]
    (s : X ⟶ Sp O) (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hγ : Function.Injective g₀)
    (hF : letI := β.toAlgebra; ∀ u : F, ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u))
    {y : ↥(pullback s (spMap β))} (hy : pullback.fst s (spMap β) y = genPt ξ₀) :
    Algebra.trdeg ℤ ((pullback s (spMap β)).residueField y) = Algebra.trdeg ℤ Ω₀ := by
  letI := β.toAlgebra
  letI := g₀.toAlgebra
  have hsurj : SurjectiveOnStalks ξ₀ := by
    have : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]
    infer_instance
  obtain ⟨z, rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y
    (IsLocalRing.closedPoint Ω₀) hy
  have sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀)
      (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β) := by
    rw [← hs]
    exact (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert
      (IsPullback.of_hasPullback s (spMap β))
  let e := sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := HodgeBasic.isIntegral_tensor hγ hF
  let p : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z
  have h1 : Algebra.trdeg ℤ p.asIdeal.ResidueField = Algebra.trdeg ℤ Ω₀ :=
    trdeg_residueField_of_isIntegral (K := Ω₀) p.asIdeal
  have hst : SurjectiveOnStalks (pullback.fst (pullback.fst s (spMap β)) ξ₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip hsurj
  have h2 := trdeg_int_eq_of_ringEquiv (RingEquiv.ofBijective _ (residueFieldMap_bijective
    (pullback.fst (pullback.fst s (spMap β)) ξ₀) z))
  have h3 := trdeg_int_eq_of_ringEquiv (asIso (e.hom.residueFieldMap z)).commRingCatIsoToRingEquiv
  have h4 : Algebra.trdeg ℤ ((Spec (.of (Ω₀ ⊗[O] F))).residueField p) = Algebra.trdeg ℤ p.asIdeal.ResidueField :=
    trdeg_int_eq_of_ringEquiv (B := p.asIdeal.ResidueField)
      (Scheme.Spec.residueFieldIso (.of (Ω₀ ⊗[O] F)) p).commRingCatIsoToRingEquiv
  exact h2.trans (h3.symm.trans (h4.trans h1))

theorem trdeg_eq_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Function.Injective β → IsCptGen ξ₀ → x ≫ Y.j = Spec.map (CommRingCat.ofHom i) ≫ ξ₀ → Algebra.trdeg ℤ Ω₀ = ((D.dim : ℕ) : Cardinal) := by
  intro E _ _ _ H D l Xo c O _ β Y Ω₀ _ ξ₀ Ω _ x i hβ h₀ hx
  have := c.fin
  have := Y.jQ_open

  let g₀ : O →+* Ω₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have hs : ξ₀ ≫ Y.s = spMap g₀ := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (ξ₀ ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let str := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let cst : c.F →+* Ω := (Spec.preimage (x ≫ str)).hom
  have hc : x ≫ str = spMap cst := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (x ≫ str)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hj : Y.j ≫ Y.s = str ≫ spMap β := by
    simp only [Model.j, Category.assoc, pullback.condition]
    rw [← Category.assoc, Y.jQ_over]
  have hcomp : i.comp g₀ = cst.comp β := by
    have h1 : spMap (i.comp g₀) = spMap (cst.comp β) := by
      have h2 : spMap i ≫ ξ₀ ≫ Y.s = x ≫ str ≫ spMap β := by
        rw [← hj, ← Category.assoc, ← Category.assoc, ← hx]
      rw [hs, ← Category.assoc, hc] at h2
      simpa only [spMap, CommRingCat.ofHom_comp, Spec.map_comp] using h2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hg : Function.Injective g₀ := by
    refine Function.Injective.of_comp (f := i) ?_
    have h3 : (i ∘ g₀) = cst ∘ β := congrArg DFunLike.coe hcomp
    rw [h3]
    exact cst.injective.comp hβ
  have hΩ : CharZero Ω := charZero_of_injective_ringHom cst.injective
  have hΩ₀ : CharZero Ω₀ := (RingHom.charZero_iff i.injective).2 hΩ

  let w : Xo.XF c := x (IsLocalRing.closedPoint Ω)
  have hy : pullback.fst Y.s (spMap β) (Y.jQ w) = genPt ξ₀ := by
    have h4 : pullback.fst Y.s (spMap β) (Y.jQ w) = (x ≫ Y.j) (IsLocalRing.closedPoint Ω) := rfl
    have h6 : (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) (IsLocalRing.closedPoint Ω) =
        ξ₀ ((Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint Ω)) := rfl
    have h5 : (Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint Ω₀ :=
      Subsingleton.elim (α := PrimeSpectrum _) _ _
    rw [h4, hx, h6, h5]
    rfl
  have hF := HodgeBasic.exists_integral_multiple_of_injective β hβ
  have hw : ∀ w' : Xo.XF c, w' ⤳ w → w' = w := fun w' h =>
    Y.jQ.isOpenEmbedding.injective
      (HodgeBasic.eq_of_specializes_of_fst Y.s β g₀ ξ₀ h₀ hs hg hF hy (h.map Y.jQ.continuous))

  have hsm : SmoothOfRelativeDimension D.dim str :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  obtain ⟨-, htr⟩ := GlobalTheory.residueField_fg_trdeg_of_smoothOfRelativeDimension str D.dim hsm w hw
  letI : Algebra c.F ((Xo.XF c).residueField w) :=
    (Spec.preimage ((Xo.XF c).fromSpecResidueField w ≫ str)).hom.toAlgebra
  have : CharZero ((Xo.XF c).residueField w) :=
    charZero_of_injective_algebraMap (algebraMap c.F ((Xo.XF c).residueField w)).injective
  have h6 : Algebra.trdeg ℤ ((Xo.XF c).residueField w) = (D.dim : Cardinal) := by
    have hal : Algebra.IsAlgebraic ℤ c.F :=
      ⟨fun u => (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic u)⟩
    have h0 : Algebra.trdeg ℤ c.F = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq ℤ c.F (A := (Xo.XF c).residueField w), h0, zero_add]
    exact htr
  have h7 := trdeg_int_eq_of_ringEquiv (asIso (Y.jQ.residueFieldMap w)).commRingCatIsoToRingEquiv
  have h8 := trdeg_residueField_of_fst Y.s β g₀ ξ₀ h₀ hs hg hF hy
  rw [← h8, h7, h6]

end GlobalTheory.CompanionTheory.Ar.CptTrdeg
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.integral_points_eq_of_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B Ω], Function.Injective (algebraMap B Ω) → (∀ c', x c' / x c ∈ (algebraMap B Ω).range) → ∀ z z' : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z = ξ → Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z' = ξ → z = z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.coordTie_points_eq | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.coordTie_points_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.coordTie_points_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem inChart_unitAt_of_inFrameDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segreCoord y) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f : Ω) (h : genPt ξ ⤳ centre z), CoordsAt ξ y z w → InFrameDomain y cc f w → InChart ξ (segreCoord y) cc ⟨centre z, h⟩ ∧ unitAt ξ ⟨centre z, h⟩ f := by
  intro X Ω _ ξ K _ J _ y hT z w cc f h hw hd
  have hu : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hd.1 k)
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hw.2 k (cc k) (hu k)).1
  have reg : ∀ {a : Ω} {r : ℂ}, ValAt ξ z a r → a ∈ regAt ξ ⟨centre z, h⟩ := by
    rintro a r ⟨_, s, hs, -⟩
    exact ⟨s, hs⟩
  refine ⟨⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩, ?_⟩
  · choose r hr _ using fun k => (hw.2 k (cc k) (hu k)).2 (c' k)
    have hp : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, y ⟨k, c' k⟩ / y ⟨k, cc k⟩) (∏ k ∈ s, r k) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using CxVal.one h
      | insert k s hk ih =>
        rw [Finset.prod_insert hk, Finset.prod_insert hk]
        exact CxVal.mul (hr k) ih
    have e : segreCoord y c' / segreCoord y cc = ∏ k, y ⟨k, c' k⟩ / y ⟨k, cc k⟩ := by
      simp only [segreCoord, Finset.prod_div_distrib]
    rw [e]
    exact reg (hp Finset.univ)
  · obtain ⟨v, hv, hv0⟩ := hd.2
    have hf : ValAt ξ z f v := (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w h hw f v).2 hv
    refine ⟨?_, reg hf, reg (CxVal.inv hf hv0)⟩
    obtain ⟨_, s, hs, hsv⟩ := hf
    have hs0 : (Scheme.stalkClosedPointTo z).hom s ≠ 0 := by rw [hsv]; exact hv0
    have := (CxVal.isUnit s hs0).map (genMap ξ ⟨centre z, h⟩)
    rw [hs] at this
    exact this.ne_zero

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.UnitValue

theorem mem_regAt_of_pow_mul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {f u : Ω} (hf : f ≠ 0) (hf' : f⁻¹ ∈ regAt ξ p) {n : ℕ} (h : f ^ n * u ∈ regAt ξ p) : u ∈ regAt ξ p := by
  have hu : u = f⁻¹ ^ n * (f ^ n * u) := by
    rw [← _root_.mul_assoc, ← _root_.mul_pow, inv_mul_cancel₀ hf, _root_.one_pow, _root_.one_mul]
  rw [hu]
  exact mul_mem (pow_mem hf' n) h

private theorem valAt_unique_lemma {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : GlobalTheory.CompanionTheory.Ar.IsCptGen ξ) {z : Spec (CommRingCat.of ℂ) ⟶ X} {a : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a r') : r = r' := by
  obtain ⟨h, s, hs, rfl⟩ := h1
  obtain ⟨h', s', hs', rfl⟩ := h2
  have hss : s = s' := hg.inj ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (hs.trans hs'.symm)
  rw [hss]

private theorem ne_zero_and_inv_mem_regAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre z) {a : Ω} {v : ℂ}
    (hv : v ≠ 0) (h : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a v) :
    a ≠ 0 ∧ a⁻¹ ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ := by
  obtain ⟨h', s, hs, hsv⟩ := h
  have hsu : IsUnit s := by
    have hi : IsUnit ((Scheme.stalkClosedPointTo z).hom s) := by
      rw [hsv]; exact hv.isUnit
    have hloc : IsLocalHom (Scheme.stalkClosedPointTo z).hom := by infer_instance
    exact hloc.map_nonunit s hi
  refine ⟨?_, ?_⟩
  · rw [← hs]
    exact (hsu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h'⟩)).ne_zero
  · have hva : ∃ r : ℂ, GlobalTheory.CompanionTheory.Ar.ValAt ξ z a⁻¹ r := by
      refine ⟨_, h', ↑hsu.unit⁻¹, ?_, rfl⟩
      rw [map_units_inv, IsUnit.unit_spec, hs]
    obtain ⟨r, hr⟩ := hva
    exact GlobalTheory.CompanionTheory.Ar.ChgUnit.mem_regAt_of_valAt hr _ rfl

theorem valAt_ne_zero_of_isUnitOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f u : Ω), CoordTie ℤ ξ (segreCoord y) → genPt ξ ⤳ centre z → CoordsAt ξ y z w → InFrameDomain y cc f w → IsUnitOn y cc f u → valAt y u w ≠ 0 ∧ ValAt ξ z u (valAt y u w) := by
  intro X Ω _ ξ K _ J _ y z w cc f u hT hz hC hF hU
  have hequiv := GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hC
  have hch := GlobalTheory.CompanionTheory.Ar.ChgUnit.inChart_of_coordsAt hC cc (fun k => (hF.1 k).isUnit)
    ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ rfl
  have hreg : ∀ a, a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) cc →
      a ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ :=
    fun a ha => (hT.ring cc hch.1 a).1 ha _ hch
  obtain ⟨v, hv, hv0⟩ := hF.2
  obtain ⟨hf0, hfi⟩ := ne_zero_and_inv_mem_regAt_of_valAt hz hv0 ((hequiv f v).2 hv)
  obtain ⟨hu0, ⟨n, hn⟩, ⟨m, hm⟩⟩ := hU
  have hu := mem_regAt_of_pow_mul hf0 hfi (hreg _ hn)
  have hui := mem_regAt_of_pow_mul hf0 hfi (hreg _ hm)
  obtain ⟨r, hr0, hr⟩ := GlobalTheory.CompanionTheory.Ar.ChgUnit.exists_value_of_unit hT.gen z hz hu0 hu hui
  have hex : ∃ v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y u w v := ⟨r, (hequiv u r).1 hr⟩
  have hval : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w = hex.choose := by
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dite_eq_left hex]
  have hc : GlobalTheory.CompanionTheory.Ar.ValAt ξ z u hex.choose := (hequiv u _).2 hex.choose_spec
  have heq : hex.choose = r := valAt_unique_lemma hT.gen hc hr
  rw [hval, heq]
  exact ⟨hr0, hr⟩

end GlobalTheory.CompanionTheory.Ar.UnitValue
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.proper_model_generic_fibre_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [IsProper s] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (C : Type) [Field C] [Algebra O C] [Algebra C Ω'] (s' : X' ⟶ Spec (CommRingCat.of C)), ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → Function.Injective (algebraMap O C) → IsPullback f s' s (Spec.map (CommRingCat.ofHom (algebraMap O C))) → ξ' ≫ s' = Spec.map (CommRingCat.ofHom (algebraMap C Ω')) → Dominates ξ' ξ f i → IsCptGen ξ → IsCptGen ξ' → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t' : Ω'), L.IsVBOn (genFibre O ξ) 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' t') → ∃ (t : Ω) (c : C), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) ∧ t' = algebraMap C Ω' c * i t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension <;> assumption)
end
