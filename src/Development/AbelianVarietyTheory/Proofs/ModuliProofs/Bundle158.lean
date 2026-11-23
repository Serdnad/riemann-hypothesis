module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle155
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PrimDense

theorem exists_gen_cube_eSec {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (u : A ⟶ A) [IsMonHom u] : ∃ c : ((cubeLB A ![𝟙 A, u] L).pull (eSec A)).Gen, c.IsGen := by
  have e₁ : (1 : 𝟙_ (Over S) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  have key : ∀ I, η[A] ≫ psum A ![𝟙 A, u] I = η[A] := fun I => by
    refine (psum_hom (preHom (G := A) η[A]) _ I).trans ?_
    have : (fun i => preHom (G := A) η[A] (![𝟙 A, u] i)) = fun i => (1 : (A ⟶ A) →* (𝟙_ (Over S) ⟶ A)) (![𝟙 A, u] i) := by
      funext i
      fin_cases i
      · exact (Category.comp_id _).trans e₁.symm
      · exact (IsMonHom.one_hom u).trans e₁.symm
    rw [this, ← psum_hom]
    exact e₁
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := fun _ : ULift.{0} (Finset (Fin 2)) => eSec A)
    (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ k => (Fintype.prod_empty _).trans (by
      have : ∑ I : ULift.{0} (Finset (Fin 2)), (-1 : ℤ) ^ (2 - I.down.card) = 0 := by decide
      have e := congrArg Additive.toMul (map_sum (zmultiplesHom (Additive U) (Additive.ofMul (k (eSec A))))
        (fun I : ULift.{0} (Finset (Fin 2)) => (-1 : ℤ) ^ (2 - I.down.card)) Finset.univ)
      rw [this, map_zero, toMul_sum] at e
      exact e)) (LB.oneGen L (Y := (𝟙_ (Over S)).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact gen_chartPull (chartPullOut L _ _ (eSec A) _ fun I => congrArg (fun z => z.left) (key I.down).symm) t ht

end GlobalTheory.PrimDense

namespace GlobalTheory

theorem lbIso_cube_of_dense : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.Rigidified A L → IsMonHom u → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ LBIso L' (cubeLB G ![𝟙 G, u'] L')} → LBIso L (cubeLB A ![𝟙 A, u] L) := by
  intro hG S _ A _ _ L u hA hL hamp hrig hu hd
  have hM : (cubeLB A ![𝟙 A, u] L).IsLB := DVR.linComb_isLB _ hL _ _
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG S A L hA hL hamp S A.left (𝟙 _) (𝟙 _) A.hom (LB.div (cubeLB A ![𝟙 A, u] L) L)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) (LB.isLB_div hM hL) (hd.mono ?_) (eSec A) (Over.w η[A]) ?_
  · rintro p ⟨K, _, x, G, _, _, φ, L', u', hp, h, hL', H, hu', H'⟩
    refine ⟨K, inferInstance, x, G.left, φ, G.hom, hp, h.1, ?_⟩
    have i : LBIso (cubeLB G ![𝟙 G, u'] L') ((cubeLB A ![𝟙 A, u] L).pull φ) := by
      obtain ⟨w, hw⟩ := H
      refine LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ _ fun I => ?_) (iso_linComb ((isGen_iff w).1 hw) _ _)
      refine psum_push h _ _ (Over.homMk φ h.1.w) (fun i => ?_) I.down
      fin_cases i
      exacts [Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm), Over.OverMorphism.ext hu']
    have a' : (cubeLB G ![𝟙 G, u'] L').IsLB := DVR.linComb_isLB _ hL' _ _
    obtain ⟨w, hw⟩ := LBIso.trans (LB.isLB_pull hL φ) hL' (LB.isLB_pull hM φ) H.symm
      (LBIso.trans hL' a' (LB.isLB_pull hM φ) H' i)
    exact gen_chartPull (IsoDescent.chartPullDiv _ L _) w hw
  · obtain ⟨c, hc⟩ := hrig
    obtain ⟨c', hc'⟩ := PrimDense.exists_gen_cube_eSec hL u
    obtain ⟨w, hw⟩ := IsoDescent.lbIso_of_gens hL hM _ _ _ _ c hc c' hc'
    exact gen_chartPull (IsoDescent.chartPullDiv _ L _) w hw

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.MulFiniteFlat

open GlobalTheory.AbLaw.MulN

theorem finite_preimage_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map f).left) (y : Y.left) : (f.left ⁻¹' {y}).Finite := by
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  have hv : pullback.fst Y.hom t (v p) = y := by
    rw [← Scheme.Hom.comp_apply]
    have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
    rw [this]
    exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)
  have hfin := ((Over.pullback t).map f).left.finite_preimage_singleton (v p)
  refine (hfin.image (pullback.fst X.hom t)).subset fun x hx => ?_
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback (isPullback_baseChange t f) x (v p)
    ((show f.left x = y from hx).trans hv.symm)
  exact ⟨z, hz₂, hz₁⟩

theorem pullback_map_mulA {S T : Scheme.{0}} (t : T ⟶ S) (A : Over S) [GrpObj A] (n : ℕ) :
    (Over.pullback t).map (mulA A n) = mulA ((Over.pullback t).obj A) n := by
  change (Over.pullback t).map (𝟙 A ^ n) = 𝟙 _ ^ n
  induction n with
  | zero => rw [pow_zero, pow_zero, Functor.map_one]
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih, CategoryTheory.Functor.map_id]

theorem isFinite_and_flat_mul : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 A) ^ k : A ⟶ A).left ∧ Flat ((𝟙 A) ^ k : A ⟶ A).left := by
  intro S _ A _ _ hA k hk
  change IsFinite (mulA A k).left ∧ Flat (mulA A k).left
  have hsm := hA.smooth
  have hpr := hA.proper
  have hm := isMonHom_mulA A k
  have hg : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map (mulA A k)).left := fun K _ _ t => by
    rw [pullback_map_mulA]
    exact GlobalTheory.MulFiniteAny.isFinite_mulA K _ (TLinPf.isAb_pullback t A hA) k hk
  have h1 : IsProper ((mulA A k).left ≫ A.hom) := by rw [Over.w]; exact hpr
  have h2 : IsProper (mulA A k).left := IsProper.of_comp _ A.hom
  have h3 : LocallyQuasiFinite (mulA A k).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_preimage_of_geomFibres _ hg)
  have hf : IsFinite (mulA A k).left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance hf
    fun K _ _ t => ?_⟩
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (TLinPf.isAb_pullback t A hA) _ inferInstance (hg K t)).1

end GlobalTheory.MulFiniteFlat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.KCriterion

theorem mono_of_unramified_of_geometric_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := ⟨fun z => by
    let κ : Type := (pullback f f).residueField z
    let y : Sp (AlgebraicClosure κ) ⟶ pullback f f :=
      spMap (algebraMap κ (AlgebraicClosure κ)) ≫ (pullback f f).fromSpecResidueField z
    have e := h _ (y ≫ pullback.fst f f) (y ≫ pullback.snd f f)
      ((Category.assoc _ _ _).trans ((congrArg _ pullback.condition).trans (Category.assoc _ _ _).symm))
    have e' : (y ≫ pullback.fst f f) ≫ pullback.diagonal f = y := by
      refine pullback.hom_ext ?_ ?_
      · simp
      · simp [e]
    exact ⟨(y ≫ pullback.fst f f) (IsLocalRing.closedPoint _),
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) e').trans (Scheme.fromSpecResidueField_apply z _)⟩⟩
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

theorem triv_of_inK_local {S : Scheme.{0}} {A : Over S} [GrpObj A] {M : LB A.left} {K : Type} [CommRing K]
    [IsLocalRing K] {t : Sp K ⟶ S} {x : Over.mk t ⟶ A} (hx : InK A M x) : Triv (Out.translDiff A M x) := by
  obtain ⟨V, hp, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  have := exists_isGen_translDiff_comp A M x (𝟙 _) V (fun q => hV.ge trivial) c hc
  rwa [Category.id_comp] at this

theorem kTriv_of_points_of_tangents : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (∀ x : specO R K ⟶ A, Triv (Out.translDiff A M x) → x = 1) ∧ ∀ x : specO R (DualNumber K) ⟶ A, ptMap (TrivSqZeroExt.fstHom R K K) ≫ x = 1 → Triv (Out.translDiff A M x) → x = 1) → Out.KTriv A M := by
  intro hL R _ A _ _ hA hP M hM hK
  obtain ⟨hO, -, hT⟩ := TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns R A hA hP M (pw M 0) hM hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ A), InK A M x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hT _ rfl T x).trans (hH T x)
  have := hA.proper
  have hft : LocallyOfFiniteType H.hom := by rw [← Over.w j]; infer_instance
  have hpt : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    exact fun y => (hK k).1 (y ≫ j) (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
  have htan : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R)
      (y : Over.mk (TangentCrit.dualBase k ≫ t) ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    have e : TangentCrit.dualBase k ≫ Spec.map φ = spMap (algebraMap R (DualNumber k)) :=
      (Spec.map_comp _ _).symm
    rw [e]
    intro y
    refine (hK k).2 (y ≫ j) ?_ (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
    rw [← Category.assoc]
    exact hpt k _ _
  have hext : ∀ {T : Scheme.{0}} {t : T ⟶ Sp R}, (∀ y : Over.mk t ⟶ H, y ≫ j = 1) →
      ∀ w w' : T ⟶ H.left, w ≫ H.hom = t → w' ≫ H.hom = t → w = w' := fun h w w' e e' =>
    (cancel_mono j.left).1 (congrArg (fun q => q.left)
      ((h (Over.homMk w e)).trans (h (Over.homMk w' e')).symm))
  have hu : FormallyUnramified H.hom :=
    TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw =>
      hext (htan k (TangentCrit.dualPt k ≫ w ≫ H.hom)) _ _ hw (by simp only [Category.assoc])
  have hm : Mono H.hom := mono_of_unramified_of_geometric_points H.hom fun k _ _ y y' e =>
    hext (hpt k (y' ≫ H.hom)) _ _ e rfl
  refine kTriv_iff_forall.2 fun T x hx => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hx
  obtain ⟨y', hy'⟩ := (hrep T 1).1 (inK_one hM T)
  have : y = y' := Over.OverMorphism.ext ((cancel_mono H.hom).1 ((Over.w y).trans (Over.w y').symm))
  rw [this, hy']

end GlobalTheory.KCriterion
end
