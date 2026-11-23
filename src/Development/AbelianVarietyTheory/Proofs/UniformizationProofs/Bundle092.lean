module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle079
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle084
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinAffineCover
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle085
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TorusQuotLift

theorem isMonHom_of_points {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H)
    (key : ∀ {T : Over S} (x y : T ⟶ G), (x * y) ≫ φ = (x ≫ φ) * (y ≫ φ)) : IsMonHom φ := by
  apply GlobalTheory.GroupGlue.isMonHom_of_points <;> assumption

private lemma pullback_fst_comp_mul_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] (f : S' ⟶ S) {T : Over S'}
    (u v : T ⟶ (Over.pullback f).obj G) :
    (u * v).left ≫ pullback.fst G.hom f =
      ((Over.homMk (U := Over.mk (T.hom ≫ f)) (V := G) (u.left ≫ pullback.fst G.hom f)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w u))) *
        (Over.homMk (U := Over.mk (T.hom ≫ f)) (V := G) (v.left ≫ pullback.fst G.hom f)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w v)))).left := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, Over.comp_left, Over.comp_left, Over.comp_left,
    Category.assoc, Category.assoc]
  have hmap : ((Over.pullback f).map μ[G]).left ≫ pullback.fst G.hom f =
      pullback.fst (G ⊗ G).hom f ≫ μ[G].left :=
    GlobalTheory.TorusLift.map_left_fst f μ[G]
  rw [hmap, ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst]
    erw [pullback.lift_fst_assoc, pullback.lift_fst]
    · rfl
    all_goals exact (Over.w _).trans (Over.w _).symm
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd]
    erw [pullback.lift_snd_assoc, pullback.lift_snd]
    · rfl
    all_goals exact (Over.w _).trans (Over.w _).symm

theorem exists_iso_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    ∃ e : G' ≅ (Over.pullback f).obj G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst G.hom f = F := by
  obtain ⟨hpb, hmul⟩ := h
  let e : G' ≅ (Over.pullback f).obj G :=
    Over.isoMk hpb.isoPullback (by simp)
  have he : e.hom.left ≫ pullback.fst G.hom f = F := by
    simp [e]
  refine ⟨e, ?_, he⟩
  apply isMonHom_of_points
  intro T x y
  apply GlobalTheory.TorusLift.hom_ext_fst f
  rw [pullback_fst_comp_mul_left]
  rw [Over.comp_left, Category.assoc, he]
  symm
  apply hmul T x y
  · simp [he]
  · simp [he]

theorem exists_isAffineOpen {R : Type} [CommRing R] [IsLocalRing R] {X : Type} [AddCommGroup X]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (Q : TQ G X) :
    ∃ W : G.left.Opens, IsAffineOpen W ∧ Q.i.left ⁻¹ᵁ W = ⊤ := by
  have := Q.q_affine
  let s₀ : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := Q.B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((η[Q.B]).left s₀)) isOpen_univ
  refine ⟨Q.q.left ⁻¹ᵁ V, hV.preimage Q.q.left, ?_⟩

  have hw : Q.i.left ≫ Q.q.left = (splitTorus _ X).hom ≫ (η[Q.B]).left := by
    have := congrArg CommaMorphism.left Q.isKernel.w
    simpa using this

  have htop : (η[Q.B]).left ⁻¹ᵁ V = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff (R := R) _).mp hbV
  have hpre : Q.i.left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) = (splitTorus _ X).hom ⁻¹ᵁ ((η[Q.B]).left ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
  rw [hpre, htop, Scheme.Hom.preimage_top]

theorem exists_torus (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left)
    (h : IsGrpPullback G₀ G (red J) F) (Q₀ : TQ G₀ X) :
    ∃ i : splitTorus _ X ⟶ G, IsMonHom i ∧ TorusCompat (red J) F Q₀.i i := by
  have hi₀hom := Q₀.i_hom
  obtain ⟨e, he_hom, he_fst⟩ := exists_iso_pullback h

  have hJtop : J ≠ ⊤ := by
    intro hJt
    obtain ⟨n, hn⟩ := hJ
    rw [hJt, Ideal.top_pow, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

  let i₀ : (Over.pullback (red J)).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (red J)).obj G :=
    (SplitTorus.bcIso (red J) X).inv ≫ Q₀.i ≫ e.hom
  have hi₀ : IsMonHom i₀ := by
    dsimp only [i₀]
    infer_instance
  obtain ⟨W₀, hW₀, hW₀top⟩ := exists_isAffineOpen Q₀
  have hcomp : i₀.left ≫ e.inv.left = (SplitTorus.bcIso (red J) X).inv.left ≫ Q₀.i.left := by
    simp [i₀]
  have hW : ∃ W : ((Over.pullback (red J)).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤ := by
    have : IsIso e.inv.left :=
      ⟨e.hom.left, by rw [← Over.comp_left, e.inv_hom_id, Over.id_left],
        by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]⟩
    refine ⟨e.inv.left ⁻¹ᵁ W₀, hW₀.preimage _, ?_⟩
    rw [← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, hW₀top, Scheme.Hom.preimage_top]
  obtain ⟨i, ⟨hi, hmap⟩, -⟩ := GlobalTheory.TorusLift.main A J hJ X G i₀ hi₀ hW
  refine ⟨i, hi, ?_⟩
  rw [torusCompat_iff, ← SplitTorus.bcIso_hom_fst, Category.assoc, ← GlobalTheory.TorusLift.map_left_fst, hmap]
  simp only [i₀, Over.comp_left, Category.assoc, he_fst]
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]

theorem main : (∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ Q₀ : TQ G₀ X, ∃ Q : TQ G X, TorusCompat (red J) F Q₀.i Q.i) := by
  intro A _ _ J hJ X _ _ _ G _ _ _ G₀ _ F h Q₀
  obtain ⟨i, hi, hc⟩ := exists_torus A J hJ X G G₀ F h Q₀
  obtain ⟨B, q, j, hjpb, -, haff, hloc⟩ := GlobalTheory.T.exists_torus_quotient_scheme_over_nilpotent_thickening A J hJ X G G₀ F h Q₀ i hi hc
  obtain ⟨hmono, hflat, hsurj, hsmooth, hcoset⟩ := GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets _ X G B i q hi haff hloc
  have : IsAffineHom q.left := haff
  obtain ⟨grpB, hcommB, hq, hker⟩ := GlobalTheory.grpObj_of_flat_coset_quotient _ G (splitTorus _ X) B i q
    hi hmono hflat hsurj inferInstance hcoset
  have hBsmooth : Smooth B.hom := hsmooth inferInstance

  have hB₀ := Q₀.isAb
  have hsnd : pullback.snd B.hom (red J) = hjpb.isoPullback.inv ≫ Q₀.B.hom := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  have hPG := GlobalTheory.NilProper.isProper_and_geometricallyConnected_of_isNilpotent A J hJ B
  have hAb : IsAbelianScheme B := by
    constructor
    case comm => exact hcommB
    case smooth => exact hBsmooth
    case proper =>
      refine hPG.1 ?_
      rw [hsnd]
      have := hB₀.proper
      infer_instance
    case geomConnected =>
      refine hPG.2 ?_
      rw [hsnd]
      have := hB₀.geomConnected
      have hst : MorphismProperty.IsStableUnderBaseChange (@GeometricallyConnected.{0}) := inferInstance
      have hRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{0}) :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected.{0}) _ _).mpr this
  have hloc' : ∀ (b : B.left) (χ : X), ∃ V : B.left.Opens, b ∈ V ∧
      ∃ u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ, IsWt i _ u.val χ := by
    intro b χ
    obtain ⟨V, hbV, -, -, -, -, u, hu⟩ := hloc b
    exact ⟨V, hbV, u (Multiplicative.ofAdd χ), hu χ⟩
  exact ⟨⟨B, hAb, q, i, hq, hi, hflat, hsurj, haff, hker, hloc'⟩, hc⟩

end GlobalTheory.TorusQuotLift
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvOfProd

theorem sum_conv {X A : Type} [AddCommGroup X] [CommRing A] (s s' S : Finset X) (F G : X → A)
    (hG : ∀ v ∉ s', G v = 0) (hS : ∀ β ∈ s, ∀ v ∈ s', β + v ∈ S) :
    ∑ α ∈ S, ∑ β ∈ s, F β * G (α - β) = (∑ β ∈ s, F β) * ∑ v ∈ s', G v := by
  classical
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_bij_ne_zero (fun v _ _ => β + v) (fun v h _ => hS β hβ v h)
    (fun a _ _ b _ _ e => add_left_cancel e) (fun α _ h => ?_) (fun v _ _ => by rw [add_sub_cancel_left])
  exact ⟨α - β, by by_contra hn; exact h (hG _ hn), h, add_sub_cancel β α⟩

theorem exists_sub_sum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Ix : Type}
    (S : LB.Sec (LB.LinComb L φ ε)) (p : Ix → LB.Sec (LB.LinComb L φ ε)) (s : Finset Ix) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval S r z J - ∑ i ∈ s, sval (p i) r z J := by
  apply GlobalTheory.MulSupp.exists_sub_sum <;> assumption

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem over_eq {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left) :
    x ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom = r ≫ (T ⊗ D.P.A).hom := by
  rw [← Over.w g.pG, ← Over.w (snd T D.P.A), ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ D.P.A.hom) hr.symm

theorem prod_mul_coord {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {k l m : ℕ} {β ga α : D.X}
    (hα : β + ga = α) {a : SecBT D T k β} {b : SecBT D T l ga} {c : SecBT D T m α} (H : IsProdB a b c) {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left)
    (z : Z) (J) (hJ : Good D.P.L z J) :
    sval c r z J * (val (g.t α) x z J).val =
      sval a r z J * (val (g.t β) x z J).val * (sval b r z J * (val (g.t ga) x z J).val) := by
  subst hα
  let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
  let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
  let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq g x r hr)
  have h₁ := H FinalForm ro z J hJ
  have h₂ := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.t_mul β ga) x).trans (val_mul hJ _ _ _))
  have h₃ := val_cub D.cub xo (z := z) hJ (DVR.cP D _ β) (DVR.cP D _ ga) g.pG
  have h₄ : xo ≫ g.pG = ro ≫ snd T D.P.A := Over.OverMorphism.ext hr.symm
  rw [DVR.comp_cP, DVR.comp_cP, h₄] at h₃
  have h₅ := congrArg Units.val ((congrArg (val (g.t (β + ga)) x z J * ·) h₃).symm.trans h₂)
  rw [Units.val_mul, Units.val_mul] at h₅
  refine (congrArg (· * (val (g.t (β + ga)) x z J).val) h₁).trans ?_
  rw [_root_.mul_mul_mul_comm, ← h₅]
  exact (_root_.mul_assoc _ _ _).trans (congrArg _ (mul_comm _ _))

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (f : ∀ α, SecBT D T k α) (g : ∀ α, SecBT D T l α) (h : ∀ α, SecBT D T (k + l) α) (σ : U.SecGT T (k + l)), U.ProdExp T f g σ → U.ExpT T (k + l) σ h → ConvT I f g h := by
  intro R _ _ I D A G _ _ U T k l f g h σ hP hE α₀
  classical
  choose p hp using fun α β => exists_isProdB R D T k l β (α - β) α (add_sub_cancel β α) (f β) (g (α - β))
  refine ⟨p α₀, hp α₀, fun e => ?_⟩
  obtain ⟨s, s', hP⟩ := hP e
  obtain ⟨s'', hE⟩ := hE e
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left),
      r ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → ∀ (z : Z) (J), Good D.P.L z J →
      (∀ α ∉ s, sval (f α) r z J = 0) ∧ (∀ α ∉ s', sval (g α) r z J = 0) ∧ (∀ α ∉ s'', sval (h α) r z J = 0) ∧
      ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
        (∑ α ∈ s, sval (f α) r z J * (val ((U.gt e).t α) x z J).val) *
          ∑ α ∈ s', sval (g α) r z J * (val ((U.gt e).t α) x z J).val := by
    intro Z x r hr z J hJ
    let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
    let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
    let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq (U.gt e) x r hr)
    let rG : FinalForm ⟶ T ⊗ G := lift (ro ≫ fst _ _) (xo ≫ fstG I e G)
    have e₁ : rG.left ≫ (snd T G).left = x ≫ (fstG I e G).left := congrArg (fun q : FinalForm ⟶ G => q.left) (lift_snd _ _)
    have e₂ : r ≫ (fst T D.P.A).left = rG.left ≫ (fst T G).left :=
      congrArg (fun q : FinalForm ⟶ T => q.left) (lift_fst (ro ≫ fst _ _) (xo ≫ fstG I e G)).symm
    choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
    obtain ⟨a₁, a₂, a₃⟩ := hP Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    obtain ⟨b₁, b₂⟩ := hE Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    exact ⟨a₁, a₂, b₁, b₂.symm.trans a₃⟩
  choose d hd using fun α => exists_sub_sum (h α) (p α) s
  let S : Finset D.X := insert α₀ (s'' ∪ Finset.image₂ (· + ·) s s')
  have hd0 := GlobalTheory.sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) (Fin 4)
    (famφT D T) (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      obtain ⟨-, k₂, k₃, k₄⟩ := key Z x r hr z J hJ
      have c := sum_conv s s' S (fun β => sval (f β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun β => sval (g β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun v hv => by rw [k₂ v hv, zero_mul])
        (fun β hβ v hv => Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hβ hv)))
      have c' : ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
          ∑ α ∈ S, sval (h α) r z J * (val ((U.gt e).t α) x z J).val :=
        Finset.sum_subset (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
          (fun a _ ha => by rw [k₃ a ha, zero_mul])
      rw [← sub_eq_zero.2 (c'.symm.trans (k₄.trans c.symm)), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hd α Z r z J hJ, sub_mul, Finset.sum_mul]
      exact congrArg _ (Finset.sum_congr rfl fun β _ =>
        prod_mul_coord (U.gt e) (add_sub_cancel β α) (hp α β) x r hr z J hJ)) α₀ (Finset.mem_insert_self _ _)
  refine ⟨s, fun Z r hl z J hJ => ⟨fun β hβ => ?_, ?_⟩⟩
  · refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (p α₀ β)
      (fun Z x r hr z J hJ => ?_) Z r hl z J hJ
    have c := prod_mul_coord (U.gt e) (add_sub_cancel β α₀) (hp α₀ β) x r hr z J hJ
    rw [(key Z x r hr z J hJ).1 β hβ, zero_mul, zero_mul] at c
    exact (Units.mul_left_eq_zero _).1 c
  · have c := GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (d α₀) hd0 Z r hl z J hJ
    rw [hd α₀ Z r z J hJ] at c
    exact sub_eq_zero.1 c

end GlobalTheory.ConvOfProd
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormVan

variable {X X' Z : Scheme.{0}}

def zeroSec (M : LB X) : LB.Sec M := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩

theorem gs_zero (r : Z ⟶ X) (z : Z) (U : X.Opens) : gs r z U 0 = 0 := by
  by_cases h : r z ∈ U
  · rw [gs_eq r z U h, map_zero, map_zero]
  · exact dif_neg h

theorem sval_zeroSec (M : LB X) (π : X' ⟶ X) (r : Z ⟶ X') (z : Z) (J : (Z ⟶ X) → M.ι) :
    sval (zeroSec (M.pull π)) r z J = 0 := gs_zero r z _

theorem exists_pull_id {M : LB X} (τ : LB.Sec M) : ∃ s : LB.Sec (M.pull (𝟙 X)),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : PUnit → M.ι), r z ∈ M.U (j PUnit.unit) →
      gs r z ((M.pull (𝟙 X)).U j) (s.f j) = gs r z (M.U (j PUnit.unit)) (τ.f (j PUnit.unit)) := by
  have le : ∀ j : PUnit → M.ι, (M.pull (𝟙 X)).U j ≤ M.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : PUnit → M.ι), r z ∈ M.U (j PUnit.unit) →
      gs r z ((M.pull (𝟙 X)).U j) (rs X (le j) (τ.f (j PUnit.unit))) =
        gs r z (M.U (j PUnit.unit)) (τ.f (j PUnit.unit)) :=
    fun Z r z j hj => gs_res r z (le j) (mem_pull.2 hj) _
  refine ⟨⟨fun j => rs X (le j) (τ.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => ?_⟩, v⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) := ⟨le j hy.1, le j' hy.2⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (v _ _ y j hm.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans
      (congrArg Units.val (gm_pull_g M (𝟙 X) (𝟙 X) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 X) y _ hy _).trans (v _ _ y j' hm.2)))).symm)
  rw [Category.id_comp]
  exact (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (τ.compat _ _)).trans
    ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))

theorem eval₂Hom_scale {κ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : κ → A)
    {P : MvPolynomial κ R} {e : ℕ} (hP : P.IsHomogeneous e) :
    MvPolynomial.eval₂Hom φ (fun j => c * x j) P = c ^ e * MvPolynomial.eval₂Hom φ x P := by
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hP (MvPolynomial.mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

def formSec {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {κ : Type} (σ : κ → LB.Sec N)
    {d : ℕ} {F : MvPolynomial κ R} (hF : F.IsHomogeneous d) : LB.Sec (pw N d) where
  f := fun k => MvPolynomial.eval₂Hom (cst p (N.U k)) (fun j => (σ j).f k) F
  compat := fun i j => by
    have c : ∀ {U V : X.Opens} (h : V ≤ U), (rs X h).comp (cst p U) = cst p V :=
      fun h => RingHom.ext (rs_cst p h)
    change rs X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (MvPolynomial.eval₂Hom _ _ F) =
      (N.g i j ^ (d : ℤ)).val * rs X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (MvPolynomial.eval₂Hom _ _ F)
    rw [MvPolynomial.map_eval₂Hom, MvPolynomial.map_eval₂Hom, c, c, zpow_natCast, Units.val_pow_eq_pow_val,
      ← eval₂Hom_scale _ _ _ hF]
    congr 2
    exact funext fun a => (σ a).compat i j

theorem sec_eq_zero (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (hI : IsAdicComplete I R)
    (Y : Over (Spec (CommRingCat.of R))) (hs : Smooth Y.hom) (hp : IsProjBy Y.hom) (M : LB Y.left) (hM : M.IsLB)
    (τ : LB.Sec M) (h : ∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : M.ι),
      pullback.fst Y.hom (thick R I e) z ∈ M.U k → gs (pullback.fst Y.hom (thick R I e)) z (M.U k) (τ.f k) = 0)
    (k : M.ι) : τ.f k = 0 := by
  obtain ⟨s, hv⟩ := exists_pull_id τ
  have e : s = zeroSec _ := (GlobalTheory.SecAlg.existsUnique_sec R I hI Y hs hp M hM (fun _ => zeroSec _)
    (fun e z J _ => (sval_zeroSec _ _ _ z J).trans (sval_zeroSec _ _ _ z J).symm)).unique
    (fun e z J hJ => by
      have hm : (fstG I e Y).left z ∈ M.U (J ((fstG I e Y).left ≫ 𝟙 _)) := hJ ((fstG I e Y).left ≫ 𝟙 _)
      exact (hv _ _ z _ hm).trans ((h e z _ hm).trans (sval_zeroSec _ _ _ z J).symm))
    (fun e z J _ => (sval_zeroSec _ _ _ z J).trans (sval_zeroSec _ _ _ z J).symm)
  refine fn_ext fun y hy => ?_
  rw [← hv _ (𝟙 _) y (fun _ => k) hy, e, gs_zero]
  exact gs_zero _ _ _

theorem form_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (N : LB Y.left) (κ : Type) (σ : κ → LB.Sec N) (d : ℕ) (F : MvPolynomial κ R), N.IsLB → F.IsHomogeneous d → (∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : N.ι), pullback.fst Y.hom (thick R I e) z ∈ N.U k → gs (pullback.fst Y.hom (thick R I e)) z (N.U k) (MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F) = 0) → ∀ k, MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F = 0 :=
  fun R _ _ I hI Y hs hp N _ σ d _ hN hF h k =>
    sec_eq_zero R I hI Y hs hp (pw N d) (isLB_pw hN d) (formSec Y.hom σ hF) h k

end GlobalTheory.FormVan
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
namespace GlobalTheory.PrimVan

theorem cechLB_acyclic_of_primitive :
    ∀ (K : Type) [Field K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B],
      IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB →
      (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → B.left.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → ∀ n, (cechLB B.hom M D).ExactAt n ∧ IsZero ((cechLB B.hom M D).homology n) ∧
          Module.finrank K ((cechLB B.hom M D).homology n) = 0 := by
  intro K _ B _ _ hB hP M hM hu hn κ _ _ D hD hc n
  have := hB.proper
  have h := acyclic_of_kuenneth GlobalTheory.AbLaw.finrank_cechLB_homology_extProd hB hM (lbIso_pull_mul hM hu) (subsingleton_sec hB hM hu hn)
    hD hc (GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K _ _ M κ D hM inferInstance hP hD hc)
    (GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K _ _ _ κ D (Inh.trivLB_isLB _) inferInstance hP hD hc) n
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h
  have := ModuleCat.isZero_iff_subsingleton.1 hz
  exact ⟨h, hz, Module.finrank_zero_of_subsingleton⟩

theorem acyclic_cechLB_of_primitive :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (B.left).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (B.hom) (M) D).Acyclic) :=
  fun K _ _ B _ _ hB hP M hM hu hn κ _ _ D hD hc n =>
    (cechLB_acyclic_of_primitive K B hB hP M hM hu hn κ D hD hc n).1

end GlobalTheory.PrimVan
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.existsUnique_theta_const_of_odd : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th : SecA A F 1) (x : TFK (R := R) F ⟶ A.A), x ^ (m ^ 2) = 1 → (∃! q : SecA A F (m ^ 2) × F, ThC A ρ m th x q.1 q.2) := by
  first | exact @GlobalTheory.existsUnique_thetaConst | exact GlobalTheory.existsUnique_thetaConst | (intros; apply GlobalTheory.existsUnique_thetaConst <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  first | exact @GlobalTheory.AddEig.main | exact GlobalTheory.AddEig.main | (intros; apply GlobalTheory.AddEig.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaOperator_point_zero_of_power_eigen : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  first | exact @GlobalTheory.ThetaEigen.main | exact GlobalTheory.ThetaEigen.main | (intros; apply GlobalTheory.ThetaEigen.main <;> assumption)
end
