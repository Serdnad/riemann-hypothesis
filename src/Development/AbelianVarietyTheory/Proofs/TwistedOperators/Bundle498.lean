module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle463
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralScalarOfPulledBackGeneratorExtendsModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceOrthogonality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle466
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  first | exact @GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff | exact GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff | (intros; apply GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.fibreIsogenyPair_defined_over_finite_subextension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  first | exact @GlobalTheory.HkIntegral.pair_defined_over_finite | exact GlobalTheory.HkIntegral.pair_defined_over_finite | (intros; apply GlobalTheory.HkIntegral.pair_defined_over_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.lieLattice_onto_of_monHom_pair_pow_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (p : ℕ) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), IsUnit (p : T.V) → IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F ≫ F' = 𝟙 _ ^ (p ^ 2) → F' ≫ F = 𝟙 _ ^ (p ^ 2) → (∀ a, I.G.act.act a ≫ F = F ≫ I'.G.act.act a) → (∀ a, I'.G.act.act a ≫ F' = F' ≫ I.G.act.act a) → letI := io.toAlgebra; (∀ τ j, IsLieImageH p f.left (y.1.u τ j) (v τ j)) → ∃ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) ∧ ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (v τ i) := by
  first | exact @GlobalTheory.HkLie.lie_lattice_onto | exact GlobalTheory.HkLie.lie_lattice_onto | (intros; apply GlobalTheory.HkLie.lie_lattice_onto <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (N M : ℕ) (a : T.Fr) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F' ≫ F = 𝟙 _ ^ N → IsUnit (N : T.V) → letI := io.toAlgebra; IsPullOf M f a y'.1.s t → Reg I M t → a ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg | exact GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg | (intros; apply GlobalTheory.HkIntegral.PullScalar.mem_range_of_reg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.isThetaTrace_conj_iff_of_rigIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (y z : FrPt Xo c K) (y' z' : FrPt Xo c L) (f : Fib Xo y.x ⟶ Fib Xo z.x) (f' : Fib Xo z.x ⟶ Fib Xo y.x) (g : Fib Xo y'.x ⟶ Fib Xo z'.x) (p : ℕ), 0 < p → FrMap φ y y' → FrMap φ z z' → IsPair (p ^ 2) f f' → IsBC φ.toRingHom f g → AllRat Xo y.x (p ^ 2) → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) ((p : ℤ) ^ 2) β) → (IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) p y.s z.s ↔ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y'.x z'.x g.left) p y'.s z'.s) := by
  first | exact @GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff | exact GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff | (intros; apply GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.exists_orth_pull_isTranslSum_of_isThetaTrace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K), p.Prime → IsPair (p ^ 2) f f' → AllRat Xo x' (p ^ 3) → a ≠ 0 → (∀ i, s'.f i = scal x' a i * s₀.f i) → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s' → ∃ (b ζ : K) (m : ℕ), ζ ^ p = 1 ∧ a * b = (p : K) ^ m * ζ ∧ ∃ f₂ : Fib Xo x' ⟶ Fib Xo x, IsMonHom f₂ ∧ f ≫ f₂ = 𝟙 _ ^ (p ^ 3) ∧ ∃ t, IsPullOf (p ^ 2) f₂ b s t ∧ IsTranslSum (p ^ 2) s₀ t := by
  first | exact @GlobalTheory.TraceOrth.thetaTrace_orthogonality | exact GlobalTheory.TraceOrth.thetaTrace_orthogonality | (intros; apply GlobalTheory.TraceOrth.thetaTrace_orthogonality <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.frames_differ_by_isometry_of_triangular_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (h : QMatch X X' N a), 0 < N → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → ∃ b ∈ Bor X'.Ψ r, x' = rmul (lact a (castFr h.psi x)) b ∧ (IsUnitFr X x → IsUnitFr X' x' → (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ τ, ∀ i < m τ, ‖A τ i i‖ = 1) := by
  first | exact @GlobalTheory.PeriodBorelQ.borel_of_periods_q | exact GlobalTheory.PeriodBorelQ.borel_of_periods_q | (intros; apply GlobalTheory.PeriodBorelQ.borel_of_periods_q <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.mem_kernel_of_geometric_fibres_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsReduced T] (x x' : Sp T ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G), Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → ∃ b ∈ transKer Xo.univ.t.G Ψ₁, b.left = spMap χ ≫ a.left) → a ∈ transKer Xo.univ.t.G Ψ := by
  first | exact @GlobalTheory.HeckeEx.mem_transKer_of_geometric | exact GlobalTheory.HeckeEx.mem_transKer_of_geometric | (intros; apply GlobalTheory.HeckeEx.mem_transKer_of_geometric <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translation_commutes_canonical_baseChange_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := by
  first | exact @GlobalTheory.HeckeEx.translT_comp_isCan | exact GlobalTheory.HeckeEx.translT_comp_isCan | (intros; apply GlobalTheory.HeckeEx.translT_comp_isCan <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.lie_divided_hom_tangent_image_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T Ω : Type) [CommRing T] [CommRing Ω] (χ : T →+* Ω) (x x' : Sp T ⟶ Xo.X) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') (p : ℕ) (v w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left) (w₁ : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left), IsUnit (p : Ω) → IsFib χ Ψ Ψ₁ → IsLieImg p Ψ v w → IsLieImg p Ψ₁ (spMap (dualMap χ) ≫ v) w₁ → w₁ = spMap (dualMap χ) ≫ w := by
  first | exact @GlobalTheory.HeckeLieBC.lieImg_baseChange | exact GlobalTheory.HeckeLieBC.lieImg_baseChange | (intros; apply GlobalTheory.HeckeLieBC.lieImg_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaTraceBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

theorem exists_isRigIso_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ pm pm' k β hc hc' hΨ h0 hβ
  let σ : (Over.mk x₁ : Over Xo.X) ⟶ Over.mk x := Over.homMk (spMap χ) hc.1.symm
  let σ' : (Over.mk x₁' : Over Xo.X) ⟶ Over.mk x' := Over.homMk (spMap χ) hc'.1.symm
  have epm : pm = (σ ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc.2.1, ← Over.comp_left, whiskerRight_snd])
  have epm' : pm' = (σ' ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc'.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc'.2.1, ← Over.comp_left, whiskerRight_snd])
  obtain ⟨β₁, h₁, hv⟩ := isRigIso_pull (σ := σ) (σ' := σ') rfl (by rw [← epm, ← epm']; exact hΨ) h0 hβ
  exact ⟨β₁, h₁, fun Z r z J hJ => by rw [hv r z hJ, ← epm]⟩

end GlobalTheory.HeckeEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeExBC

theorem isMulPull_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x₁ pm p s s' s₁ hc hv h
  obtain ⟨hx, h₁, h₂⟩ := hc
  let σ : (Over.mk x₁ : Over Xo.X) ⟶ Over.mk x := Over.homMk (spMap χ) hx.symm
  have hpm : pm = (σ ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [h₂, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [h₁, ← Over.comp_left, whiskerRight_snd])
  obtain ⟨s'', hs''⟩ := exists_pullRel Xo.univ.t.PP.L 1 (σ ▷ Xo.univ.t.G) (whiskerRight_snd σ Xo.univ.t.G) s
  have e : s'' = s' := GlobalTheory.ThetaTrace.sec_ext (sec_ext_val (L := Xo.univ.t.PP.L)
    (φ := fun _ : Fin 1 => (snd (Over.mk x₁) Xo.univ.t.G).left) Xo.univ.t.PP.isLB fun z J hJ =>
      (GlobalTheory.ThetaTraceBC.sv_of_pullRel hs'' _ z hJ).trans (by rw [← hpm]; exact (hv _ _ z J hJ).symm))
  subst e
  obtain ⟨s₁', hm, hr⟩ := GlobalTheory.ThetaTraceBC.isMulPull_pull σ hs'' h
  exact ⟨s₁', hm, fun Z r z J hJ => (GlobalTheory.ThetaTraceBC.sv_of_pullRel hr r z hJ).trans (by rw [hpm])⟩

end GlobalTheory.HeckeExBC
end
end
