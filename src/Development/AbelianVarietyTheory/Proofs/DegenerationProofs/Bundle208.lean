module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormTorsionSumShortestVectorEq
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.lift_valuation_integral_norm : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) (o : Full D C) (M : Mdl o) (f : O' →+* M.W) (u₀ : M.W), A.ν.IntN → Roots u r → ‖(u : C)‖ < 1 → (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → (∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)) → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → (∀ j, o.I.ζ (n ^ j) = A.I.ζ (n ^ j) ∧ ∀ p : D.La → (A.N.twist A.be u).QT ((n ^ j) ^ 2), (∀ x, TwRel A.be u (r ((n ^ j) ^ 2)) (A.q _ x) (p x)) → o.Theta (n ^ j) fun x => (A.N.twist A.be u).tx (n ^ j) (p x)) → ∃ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N'), (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) ∧ (∀ j x (p : (A.N.twist A.be u).QT (n ^ j)) (q' : N'.QT (n ^ j)) p' z, TwRel A.be u (r (n ^ j)) (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev (n ^ j) x).left ≫ M.φ → M.P.ToA C (n ^ j) p' z) ∧ ∃ (DW : DegPre M.W) (_ : Module (𝓞 E) DW.X) (oW : letI := H.starRing; DW.OAct (𝓞 E)) (φ : _) (he : _) (w : _) (e : _) (νW : NumOf DW C (A.N.twist A.be u)), GlobalTheory.LN.Match a f u₀ DW oW φ he w e ∧ (∀ y, νW.eX y = e (A.ν.eX y)) ∧ (∀ x, (νW.eA x).left ≫ φ = (A.ν.eA x).left) ∧ GeoIso νW ν' J.toIso := by
  first | exact @GlobalTheory.ModelData.data_of_model | exact GlobalTheory.ModelData.data_of_model | (intros; apply GlobalTheory.ModelData.data_of_model <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.UU GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] GlobalTheory.UnifNormal.grpObjPolAVPullback

theorem _root_.GlobalTheory.T.exists_uniformisation_completeLocalNormalDomain : Laws → Laws2 → Laws3 → Laws4 → Laws5 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) := by
  first | exact @GlobalTheory.UnifNormal.exists_unif_psiUnitOn | exact GlobalTheory.UnifNormal.exists_unif_psiUnitOn | (intros; apply GlobalTheory.UnifNormal.exists_unif_psiUnitOn <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) := by
  first | exact @GlobalTheory.TestFibre.exists_norm_FF_eq | exact GlobalTheory.TestFibre.exists_norm_FF_eq | (intros; apply GlobalTheory.TestFibre.exists_norm_FF_eq <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem finiteDimensional_of_finite_of_isFractionRing (V K W L : Type) [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [Field L] [Algebra V W] [Algebra W L] [Algebra K L]
    [IsFractionRing W L] [Module.Finite V W]
    (e : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K)) :
    FiniteDimensional K L := by
  letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
  haveI : FaithfulSMul V W := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

theorem exists_ringHom_integralClosure (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W L : Type) [CommRing W] [IsDomain W] [Field L]
    [Algebra (integralClosure ℤ_[p] K) W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    [Module.Finite (integralClosure ℤ_[p] K) W]
    (e : (algebraMap W L).comp (algebraMap (integralClosure ℤ_[p] K) W) =
      (algebraMap K L).comp (algebraMap (integralClosure ℤ_[p] K) K)) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (τ : L →+* K') (f : W →+* integralClosure ℤ_[p] K'),
        τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom ∧
        τ.comp (algebraMap W L) = (algebraMap (integralClosure ℤ_[p] K') K').comp f := by
  haveI := finiteDimensional_of_finite_of_isFractionRing _ K W L e
  let σ : L →ₐ[K] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let K' : IntermediateField ℚ_[p] (PadicAlgCl p) := σ.fieldRange.restrictScalars ℚ_[p]
  have h : K ≤ K' := fun x hx => ⟨algebraMap K L ⟨x, hx⟩, σ.commutes _⟩
  let τ : L →+* K' := σ.toRingHom.codRestrict K' fun x => ⟨x, rfl⟩
  have hτ : τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom :=
    RingHom.ext fun x => Subtype.ext (σ.commutes x)
  have hK' : FiniteDimensional ℚ_[p] K' := by
    letI : Algebra ℚ_[p] L := ((algebraMap K L).comp (algebraMap ℚ_[p] K)).toAlgebra
    haveI : IsScalarTower ℚ_[p] K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℚ_[p] L := Module.Finite.trans K L
    let τ' : L →ₐ[ℚ_[p]] K' := { τ with commutes' := fun x => Subtype.ext (σ.commutes (algebraMap ℚ_[p] K x)) }
    refine Module.Finite.of_surjective τ'.toLinearMap ?_
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hint : ∀ w : W, IsIntegral ℤ_[p] (τ (algebraMap W L w)) := fun w => by
    have h₁ : (algebraMap (integralClosure ℤ_[p] K) W).IsIntegralElem w := Algebra.IsIntegral.isIntegral w
    letI alg : Algebra (integralClosure ℤ_[p] K) K' :=
      ((IntermediateField.inclusion h).toRingHom.comp (algebraMap (integralClosure ℤ_[p] K) K)).toAlgebra
    haveI tower : IsScalarTower ℤ_[p] (integralClosure ℤ_[p] K) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h₂ := h₁.map (τ.comp (algebraMap W L))
    rw [RingHom.comp_assoc, e, ← RingHom.comp_assoc, hτ] at h₂
    change IsIntegral (integralClosure ℤ_[p] K) (τ (algebraMap W L w)) at h₂
    exact @isIntegral_trans _ _ _ _ _ _ alg _ _ tower _ _ h₂
  exact ⟨K', h, hK', τ, (τ.comp (algebraMap W L)).codRestrict _ hint, hτ, RingHom.ext fun _ => rfl⟩

theorem exists_semiAbelian_model_padic_polAV : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (P : Out.PolAV (Sp K)), ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧ ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧ ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left, IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  intro p _ K _ P
  haveI := GlobalTheory.DiscEval.isAdicComplete_integralClosure K
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, -, G, _, ⟨i, hi⟩, hG⟩ :=
    GlobalTheory.T.principallyPolarizedAbelianVariety_potentialSemiAbelianModel (integralClosure ℤ_[p] K) K (GlobalTheory.DiscEval.finite_residueField_integralClosure K) P
  obtain ⟨K', h, hK', τ, f, hτ, hf⟩ := exists_ringHom_integralClosure p K W L e
  refine ⟨K', h, hK', (Over.pullback (spMap f)).obj G, inferInstance, IsSemiAbelian.pullback _ G hG, ?_⟩
  exact GlobalTheory.SplitReduction.exists_isGrpPullback_of_square hf hτ G P.A
    (((isGrpPullback_of_iso i).comp (isGrpPullback_pullback P.A (spMap (algebraMap K L)))).congr
      (Category.id_comp _) rfl)

end GlobalTheory.SS
end
