module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.WeilEqAdd

theorem weilIs_mul_right {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} (x y y' : T ⟶ P.A)
    (c c' : Γ(T.left, ⊤)ˣ) (h : Out.WeilIs P.A P.L k x y c) (h' : Out.WeilIs P.A P.L k x y' c') :
    Out.WeilIs P.A P.L k x (y * y') (c * c') := by
  have h₁ := GlobalTheory.CommPairing.weilIs_symm P.isLB h
  have h₂ := GlobalTheory.CommPairing.weilIs_symm P.isLB h'
  have h₃ := GlobalTheory.CommPairing.weilIs_symm P.isLB
    (GlobalTheory.weilIs_mul_left GlobalTheory.globalFns_holds S P k T y y' x _ _ h₁ h₂)
  have e : (c⁻¹ * c'⁻¹)⁻¹ = c * c' := by rw [mul_inv, inv_inv, inv_inv, mul_comm]
  rwa [e] at h₃

end GlobalTheory.WeilEqAdd

namespace GlobalTheory


open WeilEqAdd in
theorem weilEq_mul_right_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g₁ g₂ : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g₁ →
    IsMonHom g₂ → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f g₁ A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f g₂ A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (g₁ * g₂) A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f g₁ g₂ _ _ _ r₁ r₂ h₁ h₂ n x y c hn hx hy
  haveI : IsCommMonObj A.pol.A := A.ab.comm
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have ex : ∀ r : 𝓞 E, ∃ u : ℂˣ,
      Out.WeilIs A.t.G A.t.PP.L n (x ≫ A.t.act.act r) (y ≫ 𝟙 _) (unitOn u) := by
    intro r
    haveI := A.t.act.hom r
    have hxr : (x ≫ A.t.act.act r) ^ n = 1 := by
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hy' : (y ≫ 𝟙 _) ^ n = 1 := by rw [Category.comp_id]; exact hy
    exact GlobalTheory.TorsionGenerators.exists_weilIs hL A.pol (σ₁.comp (algebraMap (𝓞 K) K)) hxr hy'
  have um : ∀ a b : ℂˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  obtain ⟨c₁, e₁⟩ := ex r₁
  obtain ⟨c₂, e₂⟩ := ex r₂
  have hA : Out.WeilIs A.t.G A.t.PP.L n (x ≫ A.t.act.act (r₁ + r₂)) (y ≫ 𝟙 _) (unitOn (c₁ * c₂)) := by
    rw [A.t.act.add, MonObj.comp_mul, um]
    exact GlobalTheory.weilIs_mul_left GlobalTheory.globalFns_holds _ A.pol n _ _ _ _ _ _ e₁ e₂
  have hB : Out.WeilIs B.t.G B.t.PP.L n (x ≫ f) (y ≫ (g₁ * g₂)) (unitOn (c₁ * c₂)) := by
    rw [MonObj.comp_mul, um]
    exact weilIs_mul_right B.pol n _ _ _ _ _ ((h₁ n x y c₁ hn hx hy).2 e₁) ((h₂ n x y c₂ hn hx hy).2 e₂)
  constructor
  · intro h
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → ∃ (σ : LB.Sec t.PP.L) (k : t.PP.L.ι), σ.f k ≠ 0 := by
  first | exact @GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt | exact GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt | (intros; apply GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.familySection_span_pullbacks_unitBall : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (S : ValuationSubring C), (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) → ∀ (k : ℕ), 1 ≤ k → ∀ (β : D.toPre.X) (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), ∃ (n : ℕ) (a : Fin n → C) (σ : Fin n → D.toPre.SecB k β) (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) (σF i) (D.toPre.famφB β) (DegPre.famε k) (σ i) (DegPre.prB D.toPre C).left 1) ∧ ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre C (a i) _ * (σF i).f j := by
  first | exact @GlobalTheory.SpanBall.span_ball | exact GlobalTheory.SpanBall.span_ball | (intros; apply GlobalTheory.SpanBall.span_ball <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)


theorem _root_.GlobalTheory.T.mu0_and_chiH_unrAt_outside_S0 : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ Lc.Q t → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (Lc.C.mu0 j).UnrAt w ∧ (G.ch.chiH (D.R.m - i)).UnrAt w := by
  first | exact @GlobalTheory.TwistUnr.mu0_chiH_unrAt | exact GlobalTheory.TwistUnr.mu0_chiH_unrAt | (intros; apply GlobalTheory.TwistUnr.mu0_chiH_unrAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.auxiliary_place_not_dvd_different_base_field : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc), ¬ G.pl.v0.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  first | exact @GlobalTheory.DifferentAtBasePlace.not_dvd_different | exact GlobalTheory.DifferentAtBasePlace.not_dvd_different | (intros; apply GlobalTheory.DifferentAtBasePlace.not_dvd_different <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RepsInj
open Matrix GlobalTheory.AdLat GlobalTheory.UCls

theorem cc_eq (D : D7) : IsCMField.complexConj D.host.E = GlobalTheory.Member.cF D :=
  AlgEquiv.ext fun x => ((GlobalTheory.Member.latHat_eq_hat_and_gram D D.sp.X').2.2.2.2.2.1 x).symm

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem hermA_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hermA c G (Pi.single i 1) (Pi.single j 1) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G i j := by
  simp [hermA, Pi.single_apply]

theorem hermA_mulVec_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) (i j : Fin n) :
    hermA c G (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1) =
      (gᵀ * G.map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) i j := by
  simp only [hermA, Matrix.mul_apply, Finset.sum_mul, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  rfl

theorem transpose_form' {A : Type} [CommRing A] {m : ℕ} (s : A →+* A) (J g : Matrix (Fin m) (Fin m) A) :
    gᵀ * Jᵀ * g.map s = Jᵀ ↔ Formalism.UG.cT s g * J * g = J := by
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, ← Matrix.mul_assoc, Formalism.UG.cT]

theorem unitary_of_isUA (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (h : IsUA c (-Jᵀ) g) :
    Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E)) g * JR (FiniteAdeleRing (𝓞 F) F) J * g =
      JR (FiniteAdeleRing (𝓞 F) F) J := by
  rw [← transpose_form']
  have key : gᵀ * (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
    ext i j
    rw [← hermA_mulVec_single, h.2, hermA_single, Matrix.map_apply]
  have e : (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) = -(JR (FiniteAdeleRing (𝓞 F) F) J)ᵀ := by
    ext i j; simp [JR, inclR, TensorProduct.tmul_neg]
  rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at key
  exact key

theorem af_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  refine ⟨0, 1, fun h => ?_⟩
  have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
  exact zero_ne_one h2

theorem incl_inj : Function.Injective (inclR (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) :=
  haveI := af_nontrivial (F := F)
  Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective

theorem cT_map_inclR (R : Type) [CommRing R] [Algebra F R] (c : E →ₐ[F] E) (γ : Matrix (Fin n) (Fin n) E) :
    (Formalism.UG.cT (c : E →+* E) γ).map (inclR R) = Formalism.UG.cT (sigR R c) (γ.map (inclR R)) := by
  ext i j
  simp [Formalism.UG.cT, sigR, inclR]

theorem rat_unitary (c : E ≃ₐ[F] E) (J γ : Matrix (Fin n) (Fin n) E) (h : IsUA c (-Jᵀ) (ratM F γ)) :
    γ.det ≠ 0 ∧ Formalism.UG.cT ((c : E →ₐ[F] E) : E →+* E) γ * J * γ = J := by
  have hr : ratM F γ = γ.map (inclR (FiniteAdeleRing (𝓞 F) F)) := rfl
  constructor
  · intro h0
    have hu := h.1
    rw [hr, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
    haveI := af_nontrivial (F := F)
    haveI : Nontrivial (RA F E) := (incl_inj (F := F) (E := E)).nontrivial
    exact not_isUnit_zero hu
  · have hu := unitary_of_isUA c J _ h
    apply Matrix.map_injective (incl_inj (F := F) (E := E))
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
    exact hu

end Gen

theorem gq_of_isUA (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (h : IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (ratM (maximalRealSubfield D.host.E) γ)) :
    ∃ γ₀ ∈ GQ V, ((finHom V γ₀).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) =
      ratM (maximalRealSubfield D.host.E) γ := by
  rw [cc_eq] at h
  obtain ⟨hd, hu⟩ := rat_unitary _ _ _ h
  let γu : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det γ).2 (Ne.isUnit hd)).unit
  have hU : γu ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := hu
  have hm : Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) γu ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT _ (γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) * JR (AF D.host.F) V.gram * γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) =
      JR (AF D.host.F) V.gram
    rw [← cT_map_inclR, JR, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) hU
  refine ⟨⟨_, hm⟩, ⟨γu, hU, rfl⟩, ?_⟩
  ext i j
  rfl

theorem kf_of_isKM (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (M : ℕ) (Kf : Subgroup (GA D V)) (hK : IsLevelK V M Kf)
    (κ : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    (h : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M κ) :
    ∃ κA ∈ Kf, ((finHom V κA).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = κ := by
  rw [cc_eq] at h
  have hu := unitary_of_isUA _ _ _ h.1
  let κu : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := ((Matrix.isUnit_iff_isUnit_det κ).2 h.1.1).unit
  have hmem : κu ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := hu
  obtain ⟨κA, hG, hf⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 κu hmem
  refine ⟨κA, (hK κA).2 ⟨hG, ?_⟩, by rw [hf]; rfl⟩
  intro z hz
  rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
  rw [hf]
  exact h.2.1 z hz

theorem reps_inj : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (gA : Comp → GA D V),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ k, (dict (gA k)).1 = k) → ∀ k k',
      GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (gA k)).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
        ((finHom V (gA k')).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) → k = k' := by
  intro D V Comp X dict Kf th M gA hK _ hD hgA k k' hE
  obtain ⟨γ, hγ, κ, hκ, he⟩ := hE
  obtain ⟨γ₀, hγ₀, hγf⟩ := gq_of_isUA D V γ hγ
  obtain ⟨κA, hκA, hκf⟩ := kf_of_isKM D V M Kf hK κ hκ
  have hfin : finHom V (gA k') = finHom V (γ₀ * gA k * κA) := by
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact he.trans (by rw [← hγf, ← hκf])
  have hx : (γ₀ * gA k * κA)⁻¹ * gA k' ∈ GinfC V := by
    show finHom V _ = 1
    rw [map_mul, map_inv, hfin, inv_mul_cancel]
  have hk' : gA k' = γ₀ * gA k * κA * ((γ₀ * gA k * κA)⁻¹ * gA k') := by group
  obtain ⟨h1, h2, ⟨x0, -, h3⟩, -⟩ := hD
  have s3 : (dict (gA k')).1 = (dict (γ₀ * gA k * κA)).1 := by
    obtain ⟨γ', -, e⟩ := h3 (γ₀ * gA k * κA) _ hx
    rw [hk', e]
  have s2 : (dict (γ₀ * gA k * κA)).1 = (dict (γ₀ * gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h2 κA hκA (γ₀ * gA k)
    rw [e]
  have s1 : (dict (γ₀ * gA k)).1 = (dict (gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h1 γ₀ hγ₀ (gA k)
    rw [e]
  rw [← hgA k, ← hgA k', s3, s2, s1]

end GlobalTheory.RepsInj
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinUA

theorem hermA_neg_transpose {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) x y =
      -((fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) ⬝ᵥ
        ((J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) *ᵥ x)) := by
  unfold GlobalTheory.AdLat.hermA
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply,
    TensorProduct.tmul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hermA_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (h : (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ *
      (J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) * g =
      J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E))
    (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) (g *ᵥ x) (g *ᵥ y) = GlobalTheory.AdLat.hermA c (-Jᵀ) x y := by
  rw [hermA_neg_transpose, hermA_neg_transpose]
  congr 1
  have e : (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ((g *ᵥ y) b)) =
      (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
    funext b

    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e]
  conv_rhs => rw [← h]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (Matrix.transpose _),
    Matrix.vecMul_transpose]

theorem isUA_finHom : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : GA D V),
    GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) := by
  intro D V g
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 (finHom V g).isUnit, fun x y => hermA_mulVec _ _ _ ?_ x y⟩
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1 * JR (AF D.host.F) V.gram * g.1.1
      = JR (AF D.host.F) V.gram := g.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hc : ∀ t, D.sp.cm.sig t = IsCMField.complexConj D.host.E t :=
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.1
  have hφ : ∀ z, φ (sigR (AF D.host.F) D.sp.cm.sig z) =
      GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E) (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [φ, sigR, GlobalTheory.AdLat.sg, hc]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hJ : (JR (AF D.host.F) V.gram).map φ =
      V.gram.map fun t => ((1 : Af D.host.F) ⊗ₜ[D.host.F] t : Af D.host.F ⊗[D.host.F] D.host.E) := by
    ext a b
    simp [φ, JR, inclR]
  have h2 := congrArg (fun M => Matrix.map M φ) h
  simp only [Matrix.map_mul] at h2
  rw [hJ] at h2
  have hg : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1).map φ =
      ((g.1.1.map φ).map (GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E)))ᵀ := by
    ext a b
    exact hφ _
  rw [hg] at h2
  exact h2

end GlobalTheory.FinUA
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.small_place_not_nonsplit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ G.pl.S0 → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  first | exact @GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt | exact GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt | (intros; apply GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_place_under_not_nonSplit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  first | exact @GlobalTheory.SplitTwistPlaces.not_nonSplitAt | exact GlobalTheory.SplitTwistPlaces.not_nonSplitAt | (intros; apply GlobalTheory.SplitTwistPlaces.not_nonSplitAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.grid_characters_unramified : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ i : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) ∧ GlobalTheory.WeilParts.UnramAt e Lc.eta := by
  first | exact @GlobalTheory.GridUnr.chi_eta_unramAt | exact GlobalTheory.GridUnr.chi_eta_unramAt | (intros; apply GlobalTheory.GridUnr.chi_eta_unramAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v = G.pl.v0 → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  first | exact @GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent | exact GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent | (intros; apply GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_character_unramified_mu : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → (∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → ∀ j : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1)) := by
  first | exact @GlobalTheory.BotTripleUnr.unramAt_mu | exact GlobalTheory.BotTripleUnr.unramAt_mu | (intros; apply GlobalTheory.BotTripleUnr.unramAt_mu <;> assumption)
end
