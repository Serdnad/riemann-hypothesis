module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle670
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.ImportsAlt
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.LseSmoothRIffReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle672
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle673
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle674
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preimage_connectedComponent_rationalPoint_baseChange : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by
  intro k k' _ _ X X' f f' p q e e' hf hP he he' hq
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set x : X := e (IsLocalRing.closedPoint k) with hx
  set x' : X' := e' (IsLocalRing.closedPoint k') with hx'
  have hopen : IsOpen (connectedComponent x) := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' X hN x
  let U : X.Opens := ⟨connectedComponent x, hopen⟩
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hrange : Set.range e ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim y (IsLocalRing.closedPoint k)]
    exact mem_connectedComponent
  let eU : Spec (CommRingCat.of k) ⟶ U.toScheme := IsOpenImmersion.lift U.ι e hrange
  have heU : eU ≫ U.ι = e := IsOpenImmersion.lift_fac _ _ _
  have hUc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := x))
  have hgc : GeometricallyConnected (U.ι ≫ f) :=
    GlobalTheory.T.geometricallyConnected_of_smooth_of_section' k U.toScheme (U.ι ≫ f) eU inferInstance (by rw [← Category.assoc, heU, he]) hUc
  have hP1 : IsPullback (q ∣_ U) (q ⁻¹ᵁ U).ι U.ι q := isPullback_morphismRestrict q U
  have hP2 : IsPullback (q ∣_ U) ((q ⁻¹ᵁ U).ι ≫ f') (U.ι ≫ f) p := hP1.paste_vert hP
  have hc : ConnectedSpace (q ⁻¹ᵁ U).toScheme :=
    GeometricallyConnected.geometrically_connectedSpace (f := U.ι ≫ f) p _ _ hP2
  have hc' : _root_.IsConnected (q ⁻¹' connectedComponent x) :=
    isConnected_iff_connectedSpace.mpr hc
  have hmem : x' ∈ q ⁻¹' connectedComponent x := by
    have : q x' = x := by
      have h1 : q x' = (e' ≫ q) (IsLocalRing.closedPoint k') := rfl
      have h2 : (p ≫ e) (IsLocalRing.closedPoint k') = e (p (IsLocalRing.closedPoint k')) := rfl
      rw [h1, hq, h2]
      exact congrArg e (Subsingleton.elim _ _)
    rw [Set.mem_preimage, this]
    exact mem_connectedComponent
  have hclopen : IsClopen (q ⁻¹' connectedComponent x) :=
    IsClopen.preimage ⟨isClosed_connectedComponent, hopen⟩ q.continuous
  exact Set.Subset.antisymm (hc'.subset_connectedComponent hmem)
    (hclopen.connectedComponent_subset hmem)

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem glue_wdb_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  intro n Y _ _ _ _ _ ι La _ A C la u i v w j hu hv
  have hopen : IsOpen (A.chart i).target := (A.chart i).open_target
  have hchi : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v := by
    intro a
    have h1 : ContDiffOn ℝ ∞ (C.chi a ∘ (A.chart i).symm) (A.chart i).target := C.smooth a i
    have h2 : DifferentiableAt ℝ (C.chi a ∘ (A.chart i).symm) v :=
      (h1.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by simp)
    exact ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal h2
  have key : ∀ a, DifferentiableAt ℝ (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v ∧
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x))) v =
      wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v *
        (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
          u a (A.chart (C.idx a) ((A.chart i).symm v))) := by
    intro a
    by_cases hs : (A.chart i).symm v ∈ tsupport (C.chi a)
    · have hsrc := (C.supp a hs).1
      have hball : A.chart (C.idx a) ((A.chart i).symm v) ∈ ball (C.c a) (C.r a) := (C.supp a hs).2
      have hovl : IsOpen (ovl A.chart i (C.idx a)) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
      have hmem : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hsrc⟩
      have hg : DifferentiableAt ℂ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_g _ i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have htr : DifferentiableAt ℂ (A.chart (C.idx a) ∘ (A.chart i).symm) v :=
        (A.holo_trans i (C.idx a)).differentiableAt (hovl.mem_nhds hmem)
      have hua : DifferentiableAt ℂ (u a) (A.chart (C.idx a) ((A.chart i).symm v)) :=
        (hu a).differentiableAt (isOpen_ball.mem_nhds hball)
      have hh : DifferentiableAt ℂ (fun x => A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) v :=
        hg.mul (hua.comp v htr)
      have heq : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =
          (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x)))) := by
        funext x; ring
      rw [heq]
      refine ⟨(hchi a).mul (hh.restrictScalars ℝ), ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_mul (hchi a) (hh.restrictScalars ℝ),
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt hh]
      ring
    · have hn : (A.chart i).symm ⁻¹' (tsupport (C.chi a))ᶜ ∈ 𝓝 v :=
        ((A.chart i).continuousAt_symm hv).preimage_mem_nhds
          ((isClosed_tsupport _).isOpen_compl.mem_nhds hs)
      have hz : ∀ᶠ x in 𝓝 v, C.chi a ((A.chart i).symm x) = 0 :=
        Filter.mem_of_superset hn fun x hx => image_eq_zero_of_notMem_tsupport hx
      have hf0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ) *
          A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
          u a (A.chart (C.idx a) ((A.chart i).symm x))) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hc0 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => (0 : ℂ) :=
        hz.mono fun x hx => by simp [hx]
      have hw0 : wdb n j (fun _ : V n => (0 : ℂ)) v = 0 :=
        ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
      refine ⟨(differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hf0, ?_⟩
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr n j _ _ v hf0,
        ReciprocityTheory.L2DbarEstimates.wdb_congr n j _ _ v hc0, hw0, zero_mul]
  have hglue : glue C la u i ∘ (A.chart i).symm = fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm x) *
        u a (A.chart (C.idx a) ((A.chart i).symm x)) := by
    funext x; rfl
  have hone : (fun x => ∑ a, (C.chi a ((A.chart i).symm x) : ℂ)) = fun _ : V n => (1 : ℂ) := by
    funext x; rw [← Complex.ofReal_sum, C.sum_one]; simp
  have hsum0 : ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
    rw [← ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => hchi a), hone]
    exact ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt (differentiableAt_const _)
  rw [hglue, ReciprocityTheory.L2DbarEstimates.wdb_sum Finset.univ (fun a _ => (key a).1)]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun a _ => (key a).2

end GlobalTheory
end

section

namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def laS (X : Data E r) (k : ℕ) : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then (k : ℤ) else -(k : ℤ)

def qS (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x : Frame X.Ψ r) : ℂ :=
  ∏ τ, ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k

theorem qS_pow (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x : Frame X.Ψ r) :
    qS X x0 k x = qS X x0 1 x ^ k := by
  simp only [qS, pow_one, Finset.prod_pow]

theorem qS_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)) :
    qS X x0 k (cpt X x0 z) = 1 := by
  unfold qS
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [KU.Mx_cpt X ho, KU.tl_nM₂₂, ExF.det_unipotentFrame_eq_one, KU.tl, Matrix.det_submatrix_equiv_self, ExF.det_nM]
  simp

end

end GlobalTheory.ScalarPoin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.holUnif_comp_linearEquiv_exists : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  exact @GlobalTheory.KeyFam.holUnif_transport_linearEquiv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tau_period_val_neg_cubical_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (D.tau (-a) (-b)) (𝟙 _) z J * cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c (-a)) (toUnit (TK R) ≫ D.c b) * (cubV D.cub z J (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c (-b)) (toUnit (TK R) ≫ D.c (-a)))⁻¹ := by
  first | exact @GlobalTheory.TauNeg.val_tau_neg | exact GlobalTheory.TauNeg.val_tau_neg | (intros; apply GlobalTheory.TauNeg.val_tau_neg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ValuationCompositionDivisor

theorem valR_comp {A : Type} [CommRing A] {X Y : Scheme.{0}} (p : Sp A ⟶ X) (ψ : X ⟶ Y)
    (U : Y.Opens) (f : Γ(Y, U)) :
    valR (p ≫ ψ) U f = valR p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  unfold valR
  rfl

end GlobalTheory.ValuationCompositionDivisor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem gen_transl_ratio : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB →
    ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
        r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
        gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  intro X X' π Q₁ Q₂ hQ₁ hQ₂ w hw τ hτ
  have hπτ : ∀ x : X, π (τ x) = π x := fun x => by
    rw [← Scheme.Hom.comp_apply, hτ]
  have hmem : ∀ {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)},
      x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → τ x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
    intro x k hx
    rw [mem_divPull] at hx ⊢
    rw [hπτ]; exact hx
  have hle : ∀ k, (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ τ ⁻¹ᵁ (LB.div (Q₂.pull π) (Q₁.pull π)).U k :=
    fun k x hx => hmem hx
  let u : ∀ k, Γ(X, (LB.div (Q₂.pull π) (Q₁.pull π)).U k)ˣ := fun k =>
    res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm r z _ (u k) = gm (r ≫ τ) z _ (w.s k) * (gm r z _ (w.s k))⁻¹ := by
    intro Z r z k hz
    show gm r z _ (res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹) = _
    rw [map_mul, map_inv, gm_res r z (hle k) hz, gm_pull r τ z _ (hmem hz)]
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k l, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U l →
      gm (r ≫ τ) z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) = gm r z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) := by
    intro Z r z k l hk hl
    have hk' := hmem hk
    have hl' := hmem hl
    rw [germ_div_g _ _ (r ≫ τ) z hk' hl', germ_div_g _ _ r z hk hl]
    have hk₀ := mem_divPull.1 hk
    have hl₀ := mem_divPull.1 hl
    have hk₁ := mem_divPull.1 hk'
    have hl₁ := mem_divPull.1 hl'
    rw [gm_pull_g Q₂ π (r ≫ τ) z hk₁.1 hl₁.1, gm_pull_g Q₁ π (r ≫ τ) z hk₁.2 hl₁.2,
      gm_pull_g Q₂ π r z hk₀.1 hl₀.1, gm_pull_g Q₁ π r z hk₀.2 hl₀.2, Category.assoc, hτ]
  have hc : (⊤ : X.Opens) ≤ iSup (LB.div (Q₂.pull π) (Q₁.pull π)).U := by
    intro x _
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => i, fun _ => j), mem_divPull.2 ⟨hi, hj⟩⟩
  obtain ⟨f, hf⟩ := glue_unit (⊤ : X.Opens) (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => le_top) hc u (by
    intro k l x hx
    rw [hu _ _ _ k hx.1, hu _ _ _ l hx.2, gen_germ hw (𝟙 X ≫ τ) x (hmem hx.1) (hmem hx.2),
      gen_germ hw (𝟙 X) x hx.1 hx.2, hg _ _ _ k l hx.1 hx.2]
    simp only [← div_eq_mul_inv]
    exact mul_div_mul_left_eq_div _ _ _)
  refine ⟨f, fun Z r z k hz => ?_⟩
  rw [← gm_res r z (le_top : (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ ⊤) hz f, hf k, hu Z r z k hz,
    inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem mul_inv_axis_comm_identity {G : Type*} [CommGroup G] (a b W R₁ R₂ : G) :
    a * b⁻¹ * W * (b * R₁) * (a * R₂)⁻¹ = W * R₁ * R₂⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem axis_unit : ∀ (A₀ A₀' X X' : Scheme.{0}) (ψ : A₀ ⟶ A₀') (e : A₀ ⟶ X) (e' : A₀' ⟶ X') (π : X ⟶ X'),
    e ≫ π = ψ ≫ e' → ∀ (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen →
    ∀ (ρ₁ : LB.Gen (Q₁.pull e')) (ρ₂ : LB.Gen (Q₂.pull e')), ρ₁.IsGen → ρ₂.IsGen →
    ∃ g : Γ(A₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
      e (r z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) = gm r z ⊤ g * gm (r ≫ ψ) z _ (ρ₂.s k.1) := by
  intro A₀ A₀' X X' ψ e e' π h Q₁ Q₂ hQ₁ hQ₂ w hw ρ₁ ρ₂ hρ₁ hρ₂
  have hpt : ∀ x : A₀, π (e x) = e' (ψ x) := fun x => by
    have := congrArg (fun f : A₀ ⟶ X' => f x) h
    simpa using this
  set D := LB.div (Q₂.pull π) (Q₁.pull π)
  let W : D.ι → A₀.Opens := fun k => e ⁻¹ᵁ D.U k
  have h₁ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₁.pull e').U k.2 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).2
    rw [hpt] at hb
    exact mem_pull.2 hb
  have h₂ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₂.pull e').U k.1 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).1
    rw [hpt] at hb
    exact mem_pull.2 hb
  let u : ∀ k, Γ(A₀, W k)ˣ := fun k =>
    pullU e _ (w.s k) * res (h₁ k) (pullU ψ _ (ρ₁.s k.2)) * (res (h₂ k) (pullU ψ _ (ρ₂.s k.1)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : D.ι) (hz : r z ∈ W k),
      gm r z (W k) (u k) = gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) * (gm (r ≫ ψ) z _ (ρ₂.s k.1))⁻¹ := by
    intro Z r z k hz
    simp only [u, map_mul, map_inv]
    rw [gm_res r z (h₁ k) hz, gm_res r z (h₂ k) hz, gm_pull r e z _ hz, gm_pull r ψ z _ (h₁ k hz),
      gm_pull r ψ z _ (h₂ k hz)]
  have hcov : (⊤ : A₀.Opens) ≤ iSup W := fun x _ => by
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π (e x))
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π (e x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨((fun _ => i), (fun _ => j)), mem_divPull.2 ⟨hi, hj⟩⟩
  have hcomp : ∀ k l, ∀ x ∈ W k ⊓ W l, gm (𝟙 A₀) x (W k) (u k) = gm (𝟙 A₀) x (W l) (u l) := by
    intro k l x hx
    rw [hu _ _ x k hx.1, hu _ _ x l hx.2]
    simp only [Category.id_comp]
    have hk : e x ∈ D.U k := hx.1
    have hl : e x ∈ D.U l := hx.2
    have hk' := mem_divPull.1 hk
    have hl' := mem_divPull.1 hl
    have hk₁ : ψ x ∈ (Q₁.pull e').U k.2 := h₁ k hx.1
    have hl₁ : ψ x ∈ (Q₁.pull e').U l.2 := h₁ l hx.2
    have hk₂ : ψ x ∈ (Q₂.pull e').U k.1 := h₂ k hx.1
    have hl₂ : ψ x ∈ (Q₂.pull e').U l.1 := h₂ l hx.2
    have E := gen_germ hw e x hk hl
    rw [germ_div_g _ _ e x hk hl] at E
    rw [show e = 𝟙 A₀ ≫ e from (Category.id_comp e).symm] at E
    rw [gm_pull_g Q₂ π (𝟙 A₀ ≫ e) x hk'.1 hl'.1, gm_pull_g Q₁ π (𝟙 A₀ ≫ e) x hk'.2 hl'.2] at E
    simp only [Category.id_comp] at E
    have R₁ := gen_germ hρ₁ ψ x hk₁ hl₁
    have R₂ := gen_germ hρ₂ ψ x hk₂ hl₂
    rw [show ψ = 𝟙 A₀ ≫ ψ from (Category.id_comp ψ).symm] at R₁ R₂
    rw [gm_pull_g Q₁ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₁) (mem_pull.1 hl₁)] at R₁
    rw [gm_pull_g Q₂ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₂) (mem_pull.1 hl₂)] at R₂
    simp only [Category.id_comp, ← h] at E R₁ R₂
    rw [E, R₁, R₂]
    exact mul_inv_axis_comm_identity _ _ _ _ _
  obtain ⟨g, hg⟩ := glue_unit (⊤ : A₀.Opens) W (fun _ => le_top) hcov u hcomp
  refine ⟨g, fun Z r z k hk => ?_⟩
  have hz : r z ∈ W k := hk
  have e₁ : gm r z ⊤ g = gm r z (W k) (u k) := by rw [← hg k, gm_res r z le_top hz]
  rw [e₁, hu Z r z k hz, inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianScheme_units_lift_artinPinch : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (B : Over (Spec R₀)) [GrpObj B], IsAbelianScheme B → ∀ (X₁ : Scheme.{0}) (q : X₁ ⟶ Spec R₁) (ρ : B.left ⟶ X₁), ρ ≫ q = B.hom ≫ Spec.map g₁ → ∀ u : Γ(B.left, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : B.left, gm ρ x ⊤ v = gm (𝟙 B.left) x ⊤ u := by
  first | exact @GlobalTheory.PinchUnitLift.main | exact GlobalTheory.PinchUnitLift.main | (intros; apply GlobalTheory.PinchUnitLift.main <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CoverDeg

def GoodCover {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ)
    (U : X.Opens) : Prop :=
  IsAffineOpen U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
    (∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale) ∧
    (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧
    (letI := (π.app U).hom.toAlgebra
     Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = δ)

end GlobalTheory.CoverDeg
end
end
