module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DegreeMultiplicationNorm
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundCharZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeightEstimate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle207
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle218
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NatAbsDiscrMemDifferent
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle219
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.Flat.finrank_kernel_pow_degree_eq_norm_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : SAB H (Sp k)), IsProper t.G.hom → ∀ (d : ℕ) (_ : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E), a ≠ 0 → (∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : Module.Finite k A) (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left) ∧ ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → Module.finrank k A ^ Module.finrank ℚ E = (Algebra.norm ℤ a).natAbs ^ (2 * d) :=
  PositivityTheory.Xgn.degree_multiplication_norm
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.local_subring_coord_ratio_value : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ (A : Subring Ω) (_ : IsLocalRing A), (∀ (k : K) (a b : J k), z ⟨k, b⟩ ≠ 0 → y ⟨k, b⟩ ≠ 0 ∧ y ⟨k, a⟩ / y ⟨k, b⟩ ∈ A) ∧ (∀ n : ℕ, (n : L) ≠ 0 → (n : Ω) ≠ 0 ∧ (n : Ω)⁻¹ ∈ A) ∧ ∀ s ∈ A, s⁻¹ ∈ A → s ≠ 0 → ∃ w : L, w ≠ 0 ∧ Small.HasVal y (0 : K → ℤ) s z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing | exact GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ClosLoc.exists_localRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.lie_metric_frame_projection_at : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)) (i : Fin r), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (s : ℂ),
      (∀ j, f j ∈ flagStep Ω b i) → e ∈ flagStep Ω b (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      ValAt ξ z (π i e) s → s ≠ 0 → (gramAt h z v).det ≠ 0 →
      (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ -
          Real.log ‖(gramAt h z v).det‖) =
        Real.log ‖s‖ + (1 / 2) * (Real.log ‖(gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)).det‖ -
          Real.log ‖(gramAt h z fun l : Fin i => B (Fin.castLE i.2.le l)).det‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_val | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_val | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.coord_degree_bound_char_zero : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F₀ F₁ : Submodule (𝓞 L) B.carrier), IsSubFibre M (flagStep Ω b₀ i) z MB F₀ →
      IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB F₁ → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ φ : F₁ →ₗ[𝓞 L] L, (∀ (x : F₁) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (t : Ω) (u : L),
          e ∈ flagStep Ω b₀ (i + 1) → M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (x : B.carrier)).left) →
          IsCls b₀ i e t → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u → φ x = u) →
        ∀ v : FinitePlace L, (∀ x, v (φ x) ≤ (v (m : L))⁻¹ * locRatio a w c₀ v) ∧
          ∃ x, v (m : L) * locRatio a w c₀ v ≤ v (φ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.coord_size | exact GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.coord_size | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.coord_size <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_type_lattice_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j → ∀ p ∈ genFibre ℤ 𝔐.ξ, 𝔐.f p.1 ∈ Subtype.val '' Z.genFib ∧ 𝔐.V (.inl τ) p = (Z.eig τ.1).pull 𝔐.ξ 𝔐.f j p ∧ 𝔐.V (.inr τ) p = (Z.eig (ComplexEmbedding.conjugate τ.1)).pull 𝔐.ξ 𝔐.f j p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main | exact GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

theorem triIn_of_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (y' : FrPt Xo c F) (t : Ix Dw → Fˣ), FrBor t y y' → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u yb : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → (∀ i, (MC.pt (yb i)).left ≫ m.φ = Small.tanY Y y' τ (Fin.cast hr i)) → FinRd.Roots.TriIn u (fun i => (t (some ⟨τ, Fin.cast hr i⟩) : F)) yb := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hy y' t hb τ r hr u yb hu hyb
  subst hr
  intro i
  obtain ⟨hx, hcomb, -⟩ := hb
  obtain ⟨cf, h1, h2, h3⟩ := hcomb τ i
  refine ⟨cf, h1, h2, ?_⟩
  obtain ⟨hw, hval⟩ := GlobalTheory.T.abelian_map_lie_model_field_point E H Dw l Xo c O β Y X tX f m F g EC MC y hy (Dw.mult τ) (y.u τ)
    (fun j => y.tan τ j) u hu cf (y'.u τ i) h3
  have hF : Small.ptF y' = Small.ptF y := by
    apply Limits.pullback.hom_ext
    · rw [Small.ptF_fst, Small.ptF_fst, hx]
    · rw [Small.ptF_snd, Small.ptF_snd]
  have htan : FinRd.Roots.LieBasis.tanW Y y (y'.u τ i) hw = Small.tanY Y y' τ i := by
    unfold FinRd.Roots.LieBasis.tanW Small.tanY
    congr 1
    apply Small.eq_tanF
    · exact IsPullback.lift_fst _ _ _ _
    · rw [hF]
      exact IsPullback.lift_snd _ _ _ _
  have hleft : (MC.pt (yb i)).left = (MC.pt (∑ j, cf j • u j)).left := by
    apply m.cart.1.hom_ext
    · rw [hval, htan]
      exact hyb i
    · rw [Over.w (MC.pt (yb i)), Over.w (MC.pt (∑ j, cf j • u j))]
  exact MC.inj (Over.OverMorphism.ext hleft)

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.root_origin_frame_height_estimate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∈ SS → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), ∀ s : CMType H ⊕ CMType H, Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC ≤ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC ∧ ∃ D : T.V, (p : ℝ) ^ (-((padicValInt p (discr E) : ℝ) / Module.finrank ℚ E)) ≤ FinRd.absT p la T e (algebraMap T.V T.Fr D) ∧ ∀ w ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC, D • w ∈ Or.𝔐.M.fibAt (Or.𝔐.M.htDual Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) Or.𝔐.ρ (Or.𝔐.emb s)) zV MC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.fib_V_htDual | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.fib_V_htDual | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.OnW.fib_V_htDual <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem tanW_injective (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {w w' : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left}
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (hw' : w' ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (h : tanW Y y w hw = tanW Y y w' hw') : w = w' := by
  have a₁ : w ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [hw, Category.assoc, Small.ptF_fst]
  have a₂ : w' ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [hw', Category.assoc, Small.ptF_fst]
  have e : Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₁ =
      Y.m0.cart.1.lift w' (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₂ :=
    Y.m.cart.1.hom_ext h (by rw [IsPullback.lift_snd, IsPullback.lift_snd])
  rw [← Y.m0.cart.1.lift_fst w _ a₁, e, IsPullback.lift_fst]

theorem comp_unit {T : Scheme.{0}} {A B M : CategoryTheory.Over T} [GrpObj M] (u : B ⟶ A) : u ≫ (1 : A ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (toUnit B)]

theorem eps_alg {S : Type} [CommRing S] (a : S) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S (DualNumber S)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem eps_zero {S : Type} [CommRing S] :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (0 : S)) =
      spMap (algebraMap S (DualNumber S)) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_alg {S : Type} [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem isTanAt_one {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) :
    Formalism.L2.Pj.IsTanAt x (1 : tEps x ⟶ Xo.univ.t.G).left := by
  refine ⟨Over.w _, ?_⟩
  let k : Over.mk x ⟶ tEps x := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Category.assoc, fst_alg, Category.id_comp])
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

theorem eps_one {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) (a : S) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (1 : tEps x ⟶ Xo.univ.t.G).left =
      (1 : tEps x ⟶ Xo.univ.t.G).left := by
  let k : tEps x ⟶ tEps x := Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Category.assoc, eps_alg])
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

theorem isEigAt_one {S : Type} [CommRing S] [Algebra c.F S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) (τ : E →+* ℂ) :
    Formalism.L2.Pj.IsEigAt c τ (Xo := Xo) (1 : tEps x ⟶ Xo.univ.t.G).left := by
  intro a
  rw [eps_one]
  haveI := Xo.univ.t.act.hom a
  have h : (1 : tEps x ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act a = 1 := by
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  exact congrArg (fun z => z.left) h

theorem eps_zero_comp {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X)
    (v : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left) (hv : Formalism.L2.Pj.IsTanAt x v) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (0 : S)) ≫ v = (1 : tEps x ⟶ Xo.univ.t.G).left := by
  rw [eps_zero, Category.assoc, hv.2]
  let k : tEps x ⟶ Over.mk x := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

def combPt {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) (a : Fin n → S) (i : Fin n) : tEps x ⟶ Xo.univ.t.G :=
  Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (a i)) ≫ v i) (by
    change (_ ≫ v i) ≫ _ = _ ≫ x
    rw [Category.assoc, (hv i).1, ← Category.assoc, eps_alg])

theorem exists_comb {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) (a : Fin n → S) : ∃ w, IsCombAt x v a w :=
  ⟨_, combPt x v hv a, fun _ => rfl, rfl⟩

theorem comb_zero {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) :
    IsCombAt x v (0 : Fin n → S) (1 : tEps x ⟶ Xo.univ.t.G).left :=
  ⟨fun _ => 1, fun i => (eps_zero_comp x (v i) (hv i)).symm, by
    simp [List.ofFn_const, List.prod_replicate]⟩

theorem coeff_zero_of_unit {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (τ : E →+* ℂ)
    (a : Fin (Dw.mult τ) → S) (h : IsCombAt y.x (y.u τ) a (1 : tEps y.x ⟶ Xo.univ.t.G).left) : a = 0 :=
  (y.basis τ _ (isTanAt_one y.x) (isEigAt_one y.x τ)).unique h (comb_zero y.x (y.u τ) (y.tan τ))

theorem coeff_zero_of_tanW {S : Type} [CommRing S] [Algebra c.F S] (Y : Model Xo c β) (y : FrPt Xo c S) (τ : E →+* ℂ)
    (a : Fin (Dw.mult τ) → S) {w w₁ : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt y.x (y.u τ) a w) (h₁ : IsCombAt y.x (y.u τ) (0 : Fin (Dw.mult τ) → S) w₁)
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (hw₁ : w₁ ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (e : tanW Y y w hw = tanW Y y w₁ hw₁) : a = 0 := by
  have e₁ : w₁ = (1 : tEps y.x ⟶ Xo.univ.t.G).left := by
    obtain ⟨U, hU, rfl⟩ := h₁
    have : U = fun _ => 1 := by
      funext i
      apply CategoryTheory.Over.OverMorphism.ext
      rw [hU i]
      exact eps_zero_comp y.x (y.u τ i) (y.tan τ i)
    subst this
    simp [List.ofFn_const, List.prod_replicate]
  have := tanW_injective Y y hw hw₁ e
  rw [this, e₁] at h
  exact coeff_zero_of_unit y τ a h

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

theorem GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → LinearIndependent F u := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hy τ r hr u hu
  subst hr
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have comb := GlobalTheory.T.abelian_map_lie_model_field_point E H Dw l Xo c O β Y X tX f m F g EC MC y hy (Dw.mult τ) (y.u τ) (y.tan τ) u hu
  obtain ⟨w, hc⟩ := FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) a
  obtain ⟨w₁, h1⟩ := FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) (0 : Fin (Dw.mult τ) → F)
  obtain ⟨hw, ew⟩ := comb a w hc
  obtain ⟨hw1, e1⟩ := comb 0 w₁ h1
  have hz := FinRd.Roots.LieBasis.coeff_zero_of_tanW Y y τ a hc h1 hw hw1 (by
    rw [← ew, ← e1, ha]
    simp)
  intro i
  exact congrFun hz i
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem htLattice_eq_dR_of_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → Nonempty (GenTors 𝔐 p) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q :=
  @PositivityTheory.Xgn.lattice_height_unit

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.frobenius_torsion_generator_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), y ^ p = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), κ.IsGen → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), τ.IsGen → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold | exact GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold <;> assumption)
end

section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.PropFTop_holds : PropFTop := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.propFTop | exact GlobalTheory.CompanionTheory.Ar.Flat.propFTop | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.propFTop <;> assumption)
end

section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.ModFree

open NumberField Module
open scoped nonZeroDivisors TensorProduct

theorem exists_map_of_basis {O B M Mb : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    (S : Submonoid O) (hS : S ≤ O⁰) [IsLocalization S B] [AddCommGroup M] [Module O M]
    [AddCommGroup Mb] [Module O Mb] [Module B Mb] [IsScalarTower O B Mb] (f : M →ₗ[O] Mb)
    [IsLocalizedModule S f] {n : ℕ} (b : Basis (Fin n) B Mb) :
    ∃ φ : (Fin n → O) →ₗ[O] M, Function.Injective φ ∧
      ∀ m, ∃ s : S, ∃ y, (s : O) • m = φ y := by
  choose p hp using fun i => IsLocalizedModule.surj S f (b i)
  have hinj : Function.Injective (algebraMap O B) := IsLocalization.injective B hS
  refine ⟨Fintype.linearCombination O (fun i => (p i).1), ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [Fintype.linearCombination_apply] at hy
    have h1 : ∑ i, algebraMap O B (y i * (p i).2) • b i = 0 := by
      have h := congrArg f hy

      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, algebraMap_smul, mul_smul]
    have h2 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h1
    funext i
    have h3 : y i * (p i).2 = 0 := hinj (by rw [h2 i, map_zero])
    exact (mul_eq_zero.mp h3).resolve_right (nonZeroDivisors.ne_zero (hS (p i).2.2))
  · intro x
    have hx := b.sum_repr (f x)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples S Finset.univ
      (fun i => b.repr (f x) i * ((IsLocalization.map_units B (p i).2).unit⁻¹ : Bˣ))
    choose a ha using fun i => RingHom.mem_rangeS.mp (ht i (Finset.mem_univ i))
    have hc : ∀ i, algebraMap O B (a i) * algebraMap O B (p i).2 =
        algebraMap O B t * b.repr (f x) i := by
      intro i
      rw [ha i, Algebra.smul_def, mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have key : f ((t : O) • x) = f (Fintype.linearCombination O (fun i => (p i).1) a) := by

      rw [map_smul, Fintype.linearCombination_apply, map_sum, ← hx, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, ← algebraMap_smul B (a i),
        ← algebraMap_smul B ((p i).2 : O), smul_smul, hc i, mul_smul, algebraMap_smul]
    obtain ⟨c, hc'⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) key
    refine ⟨c * t, (c : O) • a, ?_⟩
    rw [map_smul, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, hc', Submonoid.smul_def]

theorem exists_free_map_mod (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (𝓞 E) M] : Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M →
    ∀ (n N : ℕ), Module.finrank (𝓞 E) M = n → 0 < N →
    ∃ φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M, (∀ m, ∃ x b, m = φ x + N • b) ∧
      ∀ x b, φ x = N • b → ∃ x', x = N • x' := by
  intro hfin hproj n N hn hN
  set S := GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N with hSdef
  have hS : S ≤ (𝓞 E)⁰ := by
    rintro s ⟨k, hk0, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hk0)
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  have : IsPrincipalIdealRing (Localization S) :=
    GlobalTheory.PlaceInt.LocBasis.isPrincipalIdealRing_loc E N hN hS (Localization S)
  have hrank : Module.finrank (Localization S) (LocalizedModule S M) = n := by
    rw [IsLocalization.finrank_eq (Localization S) S hS,
      IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hS, hn]
  let b := Module.finBasisOfFinrankEq (Localization S) (LocalizedModule S M) hrank
  obtain ⟨φ, hφ, hsurj⟩ := exists_map_of_basis S hS (LocalizedModule.mkLinearMap S M) b
  have hunit : ∀ s : S, ∃ k : ℕ, (s : 𝓞 E) = k ∧ ∃ u v : ℤ, u * k + v * N = 1 := by
    rintro ⟨_, k, -, hkc, rfl⟩
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hkc
    exact ⟨k, rfl, u, v, huv⟩
  refine ⟨φ, fun m => ?_, fun x c hxc => ?_⟩
  · obtain ⟨s, y, hs⟩ := hsurj m
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    refine ⟨u • y, v • m, ?_⟩
    calc m = ((u * k + v * N : ℤ)) • m := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • m) + (N : ℤ) • (v • m) := by
        rw [add_smul, mul_smul, mul_comm v, mul_smul]
      _ = φ (u • y) + N • (v • m) := by
        rw [map_zsmul, ← hs, natCast_zsmul, natCast_zsmul]
  · obtain ⟨s, y, hs⟩ := hsurj c
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    have hNy : N • y = k • x := by
      apply hφ
      rw [map_nsmul, map_nsmul, ← hs, hxc, smul_comm]
    refine ⟨u • y + v • x, ?_⟩
    calc x = ((u * k + v * N : ℤ)) • x := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • x) + v • ((N : ℤ) • x) := by
        rw [add_smul, mul_smul, mul_smul]
      _ = N • (u • y + v • x) := by
        rw [natCast_zsmul, natCast_zsmul, ← hNy, smul_add, smul_comm u N y, smul_comm v N x]

end GlobalTheory.CompanionTheory.ModFree
end
end
