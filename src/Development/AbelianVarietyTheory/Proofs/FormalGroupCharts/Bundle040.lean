module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.formal_biextensions_related_of_triple_map_over_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t'.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t' (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t' (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u' (v ≫ n.φ) → u = (dLin φ).mulVec u' := by
  first | exact @GlobalTheory.ChartCmp.jrel_of_sabMap | exact GlobalTheory.ChartCmp.jrel_of_sabMap | (intros; apply GlobalTheory.ChartCmp.jrel_of_sabMap <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

noncomputable local instance (priority := high) grpObjPullbackForFiniteTorsion {S T : Scheme.{0}}
    (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

noncomputable local instance (priority := high) overHomOfNatOneForFiniteTorsion
    {S : Scheme.{0}} {Y G : Over S} [MonObj G] : OfNat (Y ⟶ G) 1 := ⟨toUnit Y ≫ η⟩

theorem finite_torsion_of_pullback {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) (t : Z ⟶ S')
    (r : Z ⟶ S) (hr : t ≫ f = r) (N : ℕ)
    (h : Finite {x : Over.mk t ⟶ (Over.pullback f).obj G // x ^ N = 1}) :
    Finite {x : Over.mk r ⟶ G // x ^ N = 1} := by
  subst hr
  let e := ObjPull.pushEquiv (isGrpPullback_pullback G f) (Over.mk t)
  refine Finite.of_injective (β := {x : Over.mk t ⟶ (Over.pullback f).obj G // x ^ N = 1})
    (fun x => ⟨e.symm x.1, ?_⟩) ?_
  · have hx : (show Over.mk ((Over.mk t).hom ≫ f) ⟶ G from x.1) ^ N = 1 := x.2
    rw [← map_pow, hx, map_one]
  · intro x y hxy
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val hxy))

theorem finite_torsion_special_fibre_of_unif : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (β : T →+* Ω), (∀ a ∈ maximalIdeal T, β a = 0) → ∀ N : ℕ, 1 ≤ N → Finite {x : Over.mk (spMap β) ⟶ G // x ^ N = 1} := by
  intro T _ _ _ G _ _ D A U Ω _ _ β hβ N hN
  let β' : T ⧸ (maximalIdeal T) ^ (0 + 1) →+* Ω :=
    Ideal.Quotient.lift _ β (fun a ha => hβ a (by simpa using ha))
  have g := U.gt 0
  have : IsCommMonObj (Out.thickObj T (maximalIdeal T) 0 G) := Functor.isCommMonObj_obj
  have h := GlobalTheory.TorusExtTorsion.finite_torsion_geomPoint _ (Out.thickObj T (maximalIdeal T) 0 G) (Out.thickObj T (maximalIdeal T) 0 D.toPre.P.A)
    D.toPre.X g.q g.i g.q_hom g.i_hom g.isKernel (Out.TLinPf.isAb_pullback _ _ D.toPre.P.isAb) Ω
    (Geo.Tor.spMap β') N hN
  refine finite_torsion_of_pullback G (Out.thick T (maximalIdeal T) 0) (Geo.Tor.spMap β') _ ?_ N h
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory
end
