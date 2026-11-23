module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle029
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle038
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle023
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle002
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jrel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t'.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t' (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t' (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u' (v ≫ n.φ) → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ hstar V _ _ t t' n hs d B B' κ κ' _ _ tg tg' uv uv' x x' e e' hc hc' hu hu' hf hf'
  obtain ⟨y, hy, hyu, hyc, hycomb⟩ := GlobalTheory.T.pushChartAlt E H V t t' n d x
  obtain ⟨_, _, _, _, _, w, hw⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  obtain ⟨hg, h1, h2, h3, h4⟩ := (isFrameG_iff t _ d x _ _ _ _ _ _ e).1 hf
  obtain ⟨f, hp⟩ := GlobalTheory.T.exists_pushFr_of_isGen E H V t t' n w d x y e hw.1 hy hg
  have hfy : IsFrameG t' (𝟙 (Sp V)) d y B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad f :=
    (isFrameG_iff t' _ d y _ _ _ _ _ _ f).2
      ⟨fun m => (hp m).1,
        GlobalTheory.T.firstPartialLaw_push_along_tripleMap E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h1,
        GlobalTheory.T.secondPartialLaw_push_along_tripleMap E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h2,
        GlobalTheory.T.famSy_of_pushFr_cubIso E H V t t' n w d x y e f hw hy hg hp _ h3,
        GlobalTheory.T.adjointness_series_transport_frames E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h4⟩
  obtain ⟨φ, φi, hj, hd⟩ := GlobalTheory.T.chartsWithFrames_related_allOrders E H hstar V t' hs d B B' κ κ' (fun l => tg l ≫ n.φ) tg' uv uv' y x' f e'
    (hyc _ _ κ tg uv hc) hc' (hyu hu) hu' hfy hf'
  exact ⟨φ, φi, hj, fun u u' v h h' => hd u u' _ (hycomb u v h) h'⟩

end GlobalTheory.ChartCmp
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.harmonic_germ_value_chart_independent : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := by
  first | exact @GlobalTheory.harmonicValue_chart_independent | exact GlobalTheory.harmonicValue_chart_independent | (intros; apply GlobalTheory.harmonicValue_chart_independent <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusExtTorsion

theorem finite_torsion_abelian_geomPoint {S : Scheme.{0}} (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S) (n : ℕ)
    (hn : 1 ≤ n) : Finite {x : Over.mk t ⟶ B // x ^ n = 1} := by
  have hA : IsAbelianScheme ((Over.pullback t).obj B) :=
    { comm := by have := hB.comm; infer_instance
      smooth := by have := hB.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hB.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hB.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have h := abelian_torsion_finite_and_mulN_surjective.1 Ω ((Over.pullback t).obj B) hA n hn
  have hp := isGrpPullback_pullback B t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp Ω)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst B.hom t = y.left ≫ pullback.fst B.hom t :=
        congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp Ω))).hom (Over.w y))
        (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ B // x ^ n = 1} := by
    refine Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun x => x ^ n = 1) fun x => ?_)
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp Ω))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

theorem finite_torsion_geomPoint : ∀ (S : Scheme.{0}) (G B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → IsAbelianScheme B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S) (N : ℕ), 1 ≤ N → Finite {x : Over.mk t ⟶ G // x ^ N = 1} := by
  intro S G B _ _ _ X _ _ _ q i hq hi hk hB Ω _ _ t n hn
  refine SemiAbTorsion.finite_pow_eq_one_of_extension (IsMonHom.monoidHom i (Over.mk t))
    (IsMonHom.monoidHom q (Over.mk t)) ?_ ?_ n ?_
    (finite_torsion_abelian_geomPoint B hB Ω t n hn)
  · intro a b h
    exact hk.hom_ext h (toUnit_unique _ _)
  · intro x hx
    have hx' : x ≫ q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · haveI : IsDomain Γ((Over.mk t).left, ⊤) := inferInstanceAs (IsDomain Γ(Sp Ω, ⊤))
    haveI := SemiAbTorsion.finite_chars_pow_eq_one X Γ((Over.mk t).left, ⊤) hn
    let e := splitTorusPointsEquiv S X (Over.mk t)
    refine Finite.of_injective (fun s => (⟨e s.1, by rw [← map_pow, s.2, map_one]⟩ :
      {s : Multiplicative X →* Γ((Over.mk t).left, ⊤)ˣ // s ^ n = 1})) ?_
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))

end GlobalTheory.TorusExtTorsion
end
