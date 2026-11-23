module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCoordinateConstantAdditiveInCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullCubicalOfGenericOfExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpan
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.psi_twisted_eq_psi_mul_character_of_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₂ : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen → GlobalTheory.PsiCompare.LevelOneEq D.toPre f → GlobalTheory.PsiCompare.LevelOneEq D₂.toPre f₂ → (¬ ∀ mu j, (f₂ mu).f j = 0) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  first | exact @GlobalTheory.MumCmp.psi_maps_twist | exact GlobalTheory.MumCmp.psi_maps_twist | (intros; apply GlobalTheory.MumCmp.psi_maps_twist <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

theorem _root_.GlobalTheory.T.coordinate_logDeriv_minus_potentials_chart_independent : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α := by
  first | exact @GlobalTheory.HeatConn.chartFree | exact GlobalTheory.HeatConn.chartFree | (intros; apply GlobalTheory.HeatConn.chartFree <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

theorem _root_.GlobalTheory.T.exists_descended_heat_connection_on_abelian_fibre : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∃ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb ∧ IsDesc Y h ν m₀ V ed pb := by
  first | exact @GlobalTheory.HeatConn.exists_connK_desc | exact GlobalTheory.HeatConn.exists_connK_desc | (intros; apply GlobalTheory.HeatConn.exists_connK_desc <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

theorem _root_.GlobalTheory.T.heat_operator_fourier_term_along_fibre_connection : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ (α : Q.X) (c : K), CoordEq Y h ν m₀ V pb α c → ∀ (σ σ' : Q.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ U : A₀.left.Opens, U ≤ m₀ ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j)) → (∀ j, U ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) U = 2 * (e : Γ(A₀.left, U)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) U + pbT m₀ (σ.f (fun j => h.j (i j))) U * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, U)) * pbT (T j) (pb (i j)) U + constFn A₀.hom U c)) := by
  first | exact @GlobalTheory.HeatConn.heat_term_fibre | exact GlobalTheory.HeatConn.heat_term_fibre | (intros; apply GlobalTheory.HeatConn.heat_term_fibre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

theorem _root_.GlobalTheory.T.raynaud_coordinate_constant_additive_in_character : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ (α β : Q.X) (c₁ c₂ c₃ : K), CoordEq Y h ν m₀ V pb α c₁ → CoordEq Y h ν m₀ V pb β c₂ → CoordEq Y h ν m₀ V pb (α + β) c₃ → c₃ = c₁ + c₂ := by
  first | exact @GlobalTheory.HeatConn.coordEq_const_add | exact GlobalTheory.HeatConn.coordEq_const_add | (intros; apply GlobalTheory.HeatConn.coordEq_const_add <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.extendsGenericRigidifiedGenerator_toricChartPowerSeriesRing : ∀ (k : Type) [Field k] (m n : ℕ), GlobalTheory.ChartCubExt.ExtendGenAt (ChartRing k m n) (FractionRing (ChartRing k m n)) := by
  first | exact @GlobalTheory.ChartCubExt.extendGenAt_chartRing | exact GlobalTheory.ChartCubExt.extendGenAt_chartRing | (intros; apply GlobalTheory.ChartCubExt.extendGenAt_chartRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SpreadPoint

set_option backward.isDefEq.respectTransparency false

theorem isStalkMap_atPrime (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    GlobalTheory.UPoinc.LocSpread.IsStalkMap (algebraMap R (Localization.AtPrime 𝔭)) := by
  let x : PrimeSpectrum R := ⟨𝔭, inferInstance⟩
  let T := (Spec.structureSheaf R).presheaf.stalk x
  haveI : IsLocalization x.asIdeal.primeCompl T := StructureSheaf.IsLocalization.to_stalk R x
  let e : T ≃ₐ[R] Localization.AtPrime 𝔭 := IsLocalization.algEquiv x.asIdeal.primeCompl T _
  refine ⟨x, asIso (Spec.map (e.toRingEquiv.toCommRingCatIso).hom), ?_, fun a ha =>
    IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨a, ha⟩ : 𝔭.primeCompl)⟩
  rw [Spec.fromSpecStalk_eq', asIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  exact e.commutes a

end GlobalTheory.SpreadPoint

theorem GlobalTheory.SpreadPoint.exists_away : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := by
  intro B _ X q _ R _ β 𝔭 _ f₀ hf₀
  set σ := algebraMap R (Localization.AtPrime 𝔭)
  have hσ := GlobalTheory.SpreadPoint.isStalkMap_atPrime R 𝔭
  let q' : pullback q (spMap β) ⟶ Sp R := pullback.snd q (spMap β)
  have hP : IsPullback (spMap σ) (𝟙 _) (𝟙 (Sp R)) (spMap σ) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hcomp : ∀ {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (f : A →+* C) (g : C →+* D),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm
  let u₀ : Sp (Localization.AtPrime 𝔭) ⟶ pullback q (spMap β) :=
    pullback.lift f₀ (spMap σ) (by rw [hf₀, hcomp])
  obtain ⟨a, ha, H⟩ := GlobalTheory.UPoinc.LocSpread.exists_hom hσ (𝟙 (Sp R)) q' hP u₀ (by simp [u₀, q'])
  have ha' : a ∉ 𝔭 := by
    intro h
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 a).1 ha h
  let g := algebraMap R (Localization.Away a)
  obtain ⟨u, hu, hu₀⟩ := H (Localization.Away a) g (IsLocalization.Away.algebraMap_isUnit a) (Sp (Localization.Away a))
    (spMap g) (𝟙 _) (by simp)
  let j : Localization.Away a →+* Localization.AtPrime 𝔭 := IsLocalization.Away.lift a ha
  have hj : j.comp g = σ := IsLocalization.Away.lift_comp _ _
  refine ⟨a, ha', j, u ≫ pullback.fst q (spMap β), hj, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (u ≫ q') ≫ _ = _
    rw [hu, Category.comp_id, hcomp]
  · rw [← Category.assoc, hu₀ (spMap j) (by rw [hcomp, hj])]
    exact pullback.lift_fst _ _ _
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

namespace GlobalTheory.TautPull

theorem lamIso_comp_exists : ∀ {S S' S₁ : Scheme.{0}} {B : Over S₁} {G : Over S} {G' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {M : LB B.left} {L : LB G.left} {L' : LB G'.left} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f φ) {β₂ : (G2 G).left ⟶ (G2 B).left}, M.IsLB → L.IsLB → L'.IsLB → ∀ (w : LB.Iso (abelian₂ G L) ((abelian₂ B M).pull β₂)) (v : LB.Iso L' (L.pull φ)), w.IsGen → v.IsGen → ∃ w'' : LB.Iso (abelian₂ G' L') ((abelian₂ B M).pull (sqOf gp ≫ β₂)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w'' p z J J' = lamVal w (p ≫ sqOf gp) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S' S₁ B G G' _ _ _ _ _ _ M L L' f φ gp β₂ hM hL hL' w v hw hv
  have hΛB : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛ : (abelian₂ G L).IsLB := DVR.linComb_isLB _ hL _ _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w'', T⟩ := exists_comp hΛ w (lamIso gp v) ((isGen_iff _).1 hw)
    (pgen_lamIso gp v ((isGen_iff v).1 hv)) hΛB hΛ'
  refine ⟨w'', (isGen_iff _).2 (T.pgen_comp hΛ ((isGen_iff _).1 hw)
    (pgen_lamIso gp v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂) ≫ lamφ B I))
    (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ G I)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂) ≫ lamφ B I))
    (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ G I))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂ ≫ lamφ B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ G I))
    simp only [Category.assoc]
  · rw [gw_lamIso gp v p z _ _ (fun I => by
      have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ G I)
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
      exact this) (fun I => hJ' (p ≫ lamφ G' I))]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [Category.assoc, sqOf_lamφ, ← Category.assoc]

end GlobalTheory.TautPull
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem _root_.GlobalTheory.T.theta_key_section_valuation_bounds_different : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : (Rul Xo c)ˣ), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) ∧ v (K : Rul Xo c) ≤ ((4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.KeyIntegralVal.key_valuation_bounds | exact GlobalTheory.KeyIntegralVal.key_valuation_bounds | (intros; apply GlobalTheory.KeyIntegralVal.key_valuation_bounds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerLim

theorem tendsto_of_inv_mulVec_span {α : Type} {l : Filter α} {N n : ℕ} (M : α → Matrix (Fin N) (Fin N) ℂ)
    (u : Fin n → Fin N → ℂ) (L : Fin n → Fin N → ℂ) (hdet : ∀ᶠ w in l, (M w).det ≠ 0)
    (ht : ∀ j, Tendsto (fun w => Matrix.mulVec (M w)⁻¹ (u j)) l (𝓝 (L j)))
    (hs : Submodule.span ℂ (Set.range L) = ⊤) : ∃ L0, Tendsto M l (𝓝 L0) := by
  have hc : ∀ a : Fin N, ∃ c : Fin n → ℂ, ∑ j, c j • L j = Pi.single a 1 := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hs ▸ Submodule.mem_top)
  choose c hc using hc
  let W : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun b a => ∑ j, c a j * u j b
  have hR : Tendsto (fun w => (M w)⁻¹ * W) l (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a' => tendsto_pi_nhds.2 fun a => ?_
    have e : ∀ w, ((M w)⁻¹ * W) a' a = ∑ j, c a j * (Matrix.mulVec (M w)⁻¹ (u j)) a' := by
      intro w
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, W, Matrix.of_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
    have lim : (1 : Matrix (Fin N) (Fin N) ℂ) a' a = ∑ j, c a j * L j a' := by
      have := congrFun (hc a) a'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, Pi.single_apply, Matrix.one_apply]
    simp only [e]
    rw [lim]
    exact tendsto_finsetSum _ fun j _ => ((ht j).apply_nhds a').const_mul _
  have hRi : Tendsto (fun w => ((M w)⁻¹ * W)⁻¹) l (𝓝 1) := by
    have h0 : ContinuousAt Ring.inverse (1 : Matrix (Fin N) (Fin N) ℂ).det := by
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h1 := ((continuousAt_matrix_inv (1 : Matrix (Fin N) (Fin N) ℂ) h0).tendsto).comp hR
    rw [inv_one] at h1
    exact h1
  have hRd : ∀ᶠ w in l, ((M w)⁻¹ * W).det ≠ 0 := by
    have h1 : Tendsto (fun w => ((M w)⁻¹ * W).det) l (𝓝 (1 : Matrix (Fin N) (Fin N) ℂ).det) :=
      ((Continuous.matrix_det continuous_id).tendsto (1 : Matrix (Fin N) (Fin N) ℂ)).comp hR
    rw [Matrix.det_one] at h1
    exact h1.eventually_ne one_ne_zero
  refine ⟨W, ?_⟩
  have hlim : Tendsto (fun w => W * ((M w)⁻¹ * W)⁻¹) l (𝓝 (W * 1)) :=
    ((continuous_const.matrix_mul continuous_id).tendsto _).comp hRi
  rw [Matrix.mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hdet, hRd] with w h1 h2
  have e1 : M w * ((M w)⁻¹ * W) = W := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.one_mul]
  calc W * ((M w)⁻¹ * W)⁻¹ = M w * ((M w)⁻¹ * W) * ((M w)⁻¹ * W)⁻¹ := by rw [e1]
    _ = M w := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h2), Matrix.mul_one]

theorem periods_bounded_outside_cmType_of_definite_arc_lift_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift hp0 v
  obtain ⟨n, vv, Lp, Lm, hLp, -, hsp⟩ := GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x
    fr ψ r y k T M γ xx hσ hU harc hm horb hlift
  have hdom : ∀ᶠ w in imTop, xx w ∈ (U.X k).dom := by
    filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)] with w hw
    exact horb.2.2.2.1 w hw
  have hmat : ∀ τ' : (U.X k).Ψ, ∃ L0, Tendsto (fun w => mat (xx w) τ') imTop (𝓝 L0) := by
    intro τ'
    refine tendsto_of_inv_mulVec_span (fun w => mat (xx w) τ') (fun j => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 (vv j))
      (fun j i => Lp j τ' ⟨i, by omega⟩) ?_ ?_ ?_
    · filter_upwards [hdom] with w hw
      exact (hw τ').1
    · intro j
      refine tendsto_pi_nhds.2 fun i => ?_
      have hi : (i : ℕ) < N - (U.X k).p0 := by omega
      refine (hLp j τ' ⟨i, hi⟩).congr fun w => ?_
      unfold perFr
      rw [dite_eq_left τ'.2, dite_eq_left (by simp only [hp0]; omega)]
      congr 1
      ext
      simp [hp0]
    · exact span_proj (fun j => Lp j τ') (hsp τ').1 (fun i => ⟨i, by omega⟩)
        (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
  choose L0 hL0 using hmat
  let F : ℂ → ((U.X k).Ψ → Fin N → ℂ) := fun w τ' a =>
    ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (mat (xx w) τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v)
  have hF : Tendsto F imTop (𝓝 (fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v))) := by
    refine tendsto_pi_nhds.2 fun τ' => tendsto_pi_nhds.2 fun a => ?_
    have hc : Continuous fun Mx : Matrix (Fin N) (Fin N) ℂ =>
        ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col Mx a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.hermC col
      fun_prop
    exact (hc.tendsto _).comp (hL0 τ')
  refine ⟨‖(fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) :
      (U.X k).Ψ → Fin N → ℂ)‖ + 1, ?_⟩
  filter_upwards [hF.norm.eventually (gt_mem_nhds (lt_add_one _))] with w hw
  intro τ i hτ
  unfold perFr
  rw [dite_eq_right hτ]
  split_ifs with h' hj
  · exact ((norm_le_pi_norm (F w ⟨_, h'⟩) ⟨_, hj⟩).trans (norm_le_pi_norm (F w) ⟨_, h'⟩)).trans hw.le
  · simp only [norm_zero]; positivity
  · simp only [norm_zero]; positivity

end GlobalTheory.ShFam.PerLim
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.weilPairing_condition_locus_isClopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := by
  first | (exact @GlobalTheory.HTWeilLocus.weil_locus_clopen) | (exact GlobalTheory.HTWeilLocus.weil_locus_clopen) | (intros; apply GlobalTheory.HTWeilLocus.weil_locus_clopen  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_baseChange_polarisation_translate_two_torsion : ∀ (K K' : Type) [Field K] [Field K'] (io : K →+* K') (A : PolAV (Sp K)) (y : Over.mk (spMap io) ⟶ A.A), y * y = 1 → ∃ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (t : 𝟙_ (Over (Sp K')) ⟶ A₁.A), IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ t.left ≫ α₁ = y.left ∧ LBIso A₁.L (GlobalTheory.RigidTranslate.rigTransl (A.L.pull α₁) t) := by
  first | exact @GlobalTheory.BaseTransl.exists_baseChange_translate | exact GlobalTheory.BaseTransl.exists_baseChange_translate | (intros; apply GlobalTheory.BaseTransl.exists_baseChange_translate <;> assumption)
end
