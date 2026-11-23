module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle498
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle429
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle499
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle500
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle501
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle491
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle293
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.normalized_mul_pullback_commutes_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := by
  first | exact @GlobalTheory.HeckeExBC.isMulPull_baseChange | exact GlobalTheory.HeckeExBC.isMulPull_baseChange | (intros; apply GlobalTheory.HeckeExBC.isMulPull_baseChange <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fock_creation_operator_reading : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := by
  first | exact @GlobalTheory.FockTransl.Jet.rd_aPlusAll | exact GlobalTheory.FockTransl.Jet.rd_aPlusAll | (intros; apply GlobalTheory.FockTransl.Jet.rd_aPlusAll <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

theorem _root_.GlobalTheory.T.completed_diagonal_coordinate_mem_completion_conj_AA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : GlobalTheory.Asc.Frames G}, Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (x : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))), x ∈ hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) → ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ x ⬝ (F.dB ρ h).jY) p p ∈ complId D.host.AAbar := by
  first | exact @GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem | exact GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem | (intros; apply GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice : ∀ {D : D7} (S : HSp D) (fr : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1 → ∀ Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), SD D Ls → ∃ Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), (Λ : Set (Fin S.rank → D.host.E)) = GlobalTheory.MovedDict.inV fr Ls ∧ IsSelfDualC S Λ := by
  first | exact @GlobalTheory.MovedDict.isSelfDualC_inV | exact GlobalTheory.MovedDict.isSelfDualC_inV | (intros; apply GlobalTheory.MovedDict.isSelfDualC_inV <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.exists_generator_heckeIsogeny_lineBundle_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), ∃ β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (hkMap Z hx hx') ((p : ℤ) ^ 2)), β.IsGen := by
  first | exact @GlobalTheory.HeckeEx.exists_gen_isoLB | exact GlobalTheory.HeckeEx.exists_gen_isoLB | (intros; apply GlobalTheory.HeckeEx.exists_gen_isoLB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.heckeUniversalIsogenyOnFibres_linear_at_ringPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), IsLinHom (hkMap Z hx hx') := by
  first | exact @GlobalTheory.HeckeEx.isLinHom_hkMap_target | exact GlobalTheory.HeckeEx.isLinHom_hkMap_target | (intros; apply GlobalTheory.HeckeEx.isLinHom_hkMap_target <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.heckeUniversalIsogenyOnFibres_preserves_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  first | exact @GlobalTheory.HeckeEx.hkMap_ptSec_one | exact GlobalTheory.HeckeEx.hkMap_ptSec_one | (intros; apply GlobalTheory.HeckeEx.hkMap_ptSec_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → ∀ (e : GA D (G.V i j).V = GA D (G'.V (.grid i j))) (φ : GA D (G'.V (.grid i j)) → ℂ),
      IsCuspListed W.θ (.grid i j) φ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) (fun g => φ (cast e g)) := by
  first | exact @GlobalTheory.ListedTypeConj.isCuspListed_grid_iff | exact GlobalTheory.ListedTypeConj.isCuspListed_grid_iff | (intros; apply GlobalTheory.ListedTypeConj.isCuspListed_grid_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges : ∀ {T : Type} (m : ℕ) (t : T), (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.givenPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.givenPath t m) = GlobalTheory.SplitFlip.givenPath m) ∧ (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.oppPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.oppPath t m) = GlobalTheory.SplitFlip.oppositePath m) ∧ ∀ {X Y : Node} (p q : Path T X Y), GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.FlipRun.OnGrid m t q → GlobalTheory.FlipRun.edges p = GlobalTheory.FlipRun.edges q → p = q := by
  first | exact @GlobalTheory.FlipPaths.given_opp_paths | exact GlobalTheory.FlipPaths.given_opp_paths | (intros; apply GlobalTheory.FlipPaths.given_opp_paths <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.gridPath_cut_at_square_swap_route : ∀ {T : Type} (m : ℕ) (t : T) (i j : ℕ), i < m → j < m → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.SplitFlip.PassesThrough i j (GlobalTheory.FlipRun.edges p) → ∃ (A : Path T X (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) Y), p = (A.comp (routeSmall t i j)).comp Bp ∧ GlobalTheory.FlipRun.OnGrid m t A ∧ GlobalTheory.FlipRun.OnGrid m t Bp ∧ GlobalTheory.FlipRun.OnGrid m t ((A.comp (routeBig t i j)).comp Bp) ∧ GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp) = GlobalTheory.SplitFlip.flipPath i j (GlobalTheory.FlipRun.edges p) := by
  first | exact @GlobalTheory.PathCut.cut_at_square | exact GlobalTheory.PathCut.cut_at_square | (intros; apply GlobalTheory.PathCut.cut_at_square <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flippedFiniteTensor_of_representing_oppositePath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (Φ : G.Datum) (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G (oppPath t D.R.m)), GlobalTheory.FlipRun.RepFin B ρ t (oppPath t D.R.m) τ (Tflip W B t Φ) → ∃ τ', GlobalTheory.RowClaim.IsFlipFin t B ρ Φ τ' ∧ GlobalTheory.FlipRun.tensE W (oppPath t D.R.m) Q τ = GlobalTheory.RowClaim.oppTens W t (Q.mapDomain GlobalTheory.FlipRun.toOpp) τ' := by
  first | exact @GlobalTheory.OppConv.flipFin_of_repFin | exact GlobalTheory.OppConv.flipFin_of_repFin | (intros; apply GlobalTheory.OppConv.flipFin_of_repFin <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinAvgSpan

open Formalism.REAL MeasureTheory GlobalTheory.SeriesToClosure Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom

theorem continuous_integral_K {n : ℕ} {ε : Fin n → Bool} {X : Type*} [TopologicalSpace X] (F : X → KG ε → ℂ)
    (hF : Continuous (Function.uncurry F)) : Continuous fun x => ∫ k, F x k ∂(muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  let L : C(KG ε, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ k, g k ∂(muK ε)
      map_add' := fun g h => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (GlobalTheory.ExpansionAverage.integrable_K g.continuous)
          (GlobalTheory.ExpansionAverage.integrable_K h.continuous)
      map_smul' := fun c g => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hL : Continuous L := AddMonoidHomClass.continuous_of_bound L ((muK ε).real Set.univ) fun g => by
    show ‖∫ k, g k ∂(muK ε)‖ ≤ _
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k =>
      ContinuousMap.norm_coe_le_norm g k)).trans (le_of_eq (mul_comm _ _))
  exact hL.comp (ContinuousMap.curry ⟨_, hF⟩).continuous

variable {D : D7} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {ε : Fin V.rank → Bool}
  {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem continuous_conjAt (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) :
    Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
  (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
    fun k => conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))

theorem continuous_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    Continuous (Function.uncurry fun (x : GA D V) (k : KG ε) => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) :=
  (he.comp continuous_snd).mul (hφ.comp (continuous_fst.mul ((continuous_conjAt hθ hP hJ).comp continuous_snd)))

theorem integrable_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) (x : GA D V) :
    Integrable (fun k => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) (muK ε) :=
  GlobalTheory.ExpansionAverage.integrable_K (he.mul (hφ.comp (continuous_const.mul (continuous_conjAt hθ hP hJ))))

theorem continuous_avg (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) : Continuous (avg θ V τ ε P e φ) :=
  continuous_integral_K _ (continuous_integrand hθ hP hJ he hφ)

theorem avg_add_left (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e₁ e₂ : KG ε → ℂ} (h₁ : Continuous e₁) (h₂ : Continuous e₂) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    avg θ V τ ε P (e₁ + e₂) φ = avg θ V τ ε P e₁ φ + avg θ V τ ε P e₂ φ := funext fun x => by
  simp only [avg, Pi.add_apply, add_mul]
  exact integral_add (integrable_integrand hθ hP hJ h₁ hφ x) (integrable_integrand hθ hP hJ h₂ hφ x)

theorem avg_smul_left (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P (c • e) φ = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem avg_add_right (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ₁ φ₂ : GA D V → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) :
    avg θ V τ ε P e (φ₁ + φ₂) = avg θ V τ ε P e φ₁ + avg θ V τ ε P e φ₂ := funext fun x => by
  simp only [avg, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand hθ hP hJ he h₁ x) (integrable_integrand hθ hP hJ he h₂ x)

theorem avg_smul_right (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P e (c • φ) = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_left_comm (e _) c]
  exact integral_const_mul c _

theorem rTr_avg_same (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : P * g * P⁻¹ ∈ Kset ε) :
    ∃ k₀ : KG ε, ∀ (e : KG ε → ℂ) (φ : GA D V → ℂ),
      rTr V (atTau θ V τ g) (avg θ V τ ε P e φ) = avg θ V τ ε P (fun k => e (k₀⁻¹ * k)) φ := by
  obtain ⟨k₀, hk₀'⟩ : P * g * P⁻¹ ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
  have hk₀ : toMK k₀ = P * g * P⁻¹ := hk₀'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have eg : g = P⁻¹ * toMK k₀ * P := by
    rw [hk₀]
    calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [Matrix.nonsing_inv_mul _ hd, one_mul, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨k₀, fun e φ => funext fun x => ?_⟩
  have key : ∀ k : KG ε, atTau θ V τ g * atTau θ V τ (P⁻¹ * toMK k * P) =
      atTau θ V τ (P⁻¹ * toMK (k₀ * k) * P) := fun k => by
    rw [eg, ← at_mul hθ hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k₀)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))]
    rfl
  simp only [rTr, avg, mul_assoc x, key]
  rw [← integral_mul_left_eq_self (μ := muK ε)
    (fun k => e (k₀⁻¹ * k) * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) k₀]
  simp only [inv_mul_cancel_left]

theorem rTr_avg_other (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ')) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    rTr V (atTau θ V τ' g) (avg θ V τ ε P e φ) = avg θ V τ ε P e (rTr V (atTau θ V τ' g) φ) := funext fun x => by
  simp only [rTr, avg, mul_assoc x]
  congr 1
  funext k
  rw [GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne _
    (conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))) g hg]

end GlobalTheory.KFinAvgSpan

namespace GlobalTheory.KFinAvgSpan



theorem exists_stab_insert : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ s : Set D.what₂.Tau, τ ∉ s → ∀ W' : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W' → (∀ f ∈ W', Continuous f) → GlobalTheory.KFinCuspApprox.KStab θ N s W' → ∃ W : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab θ N (insert τ s) W ∧ ∀ f ∈ W', GlobalTheory.KFinCuspApprox.avgN θ N τ e f ∈ W := by
  intro D θ hθ N τ e he s hτs W' hW'fin hW'c hW'stab
  obtain ⟨F, hFfin, heF, hFc, hFtr⟩ := he
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI := hFfin
  haveI := hW'fin
  let B : F →ₗ[ℂ] W' →ₗ[ℂ] (GA D N.V → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ)
        (b : GA D N.V → ℂ))
      (fun a₁ a₂ b => avg_add_left hθ hP hJ (hFc _ a₁.2) (hFc _ a₂.2) (hW'c _ b.2))
      (fun c a b => avg_smul_left c _ _)
      (fun a b₁ b₂ => avg_add_right hθ hP hJ (hFc _ a.2) (hW'c _ b₁.2) (hW'c _ b₂.2))
      (fun c a b => avg_smul_right c _ _)
  have hB : ∀ (a : F) (b : W'), TensorProduct.lift B (a ⊗ₜ b) =
      GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ) :=
    fun a b => by rw [TensorProduct.lift.tmul]; rfl
  have hcont : ∀ t, Continuous (TensorProduct.lift B t) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact continuous_const
    | tmul a b => rw [hB]; exact continuous_avg hθ hP hJ (hFc _ a.2) (hW'c _ b.2)
    | add u v hu hv => rw [map_add (f := _)]; exact hu.add hv
  refine ⟨LinearMap.range (TensorProduct.lift B), inferInstance, ?_, ?_, fun f hf => ⟨⟨e, heF⟩ ⊗ₜ ⟨f, hf⟩, hB _ _⟩⟩
  · rintro _ ⟨t, rfl⟩
    exact hcont t
  · intro τ'' hτ'' g hg hK w hw
    obtain ⟨t, rfl⟩ := hw
    suffices h : ∀ (a : F) (b : W'), rTr N.V (atTau θ N.V τ'' g)
        (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)) ∈
          LinearMap.range (TensorProduct.lift B) by
      induction t using TensorProduct.induction_on with
      | zero =>
        rw [map_zero]
        exact zero_mem _
      | tmul a b => rw [hB]; exact h a b
      | add u v hu hv =>
        rw [map_add (f := _)]
        exact add_mem hu hv
    intro a b
    rcases hτ'' with h | hs
    · rw [h] at hK ⊢
      obtain ⟨k₀, hk⟩ := rTr_avg_same hθ hP hJ hK
      have hk' := hk (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)
      refine ⟨⟨_, (hFtr _ a.2 k₀⁻¹).1⟩ ⊗ₜ b, ?_⟩
      rw [hB, hk']
    · have hne : τ ≠ τ'' := fun h => hτs (h ▸ hs)
      rw [rTr_avg_other hθ hP hJ hne hg]
      exact ⟨a ⊗ₜ ⟨_, hW'stab τ'' hs g hg hK b b.2⟩, hB _ _⟩

end GlobalTheory.KFinAvgSpan

end
end
