module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.isFinite_of_pull_veryAmple_iso_pow : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (n : ℕ) (s : Fin (n + 1) → LB.Sec H') (d : ℕ), H.IsLB → H'.IsLB → IsSeparated f → VeryAmpleBy (φ ≫ f) H' s → 1 ≤ d → LBIso (pw H' d) (H.pull φ) → IsFinite φ := by
  first | exact @GlobalTheory.PullAmpleFinite.isFinite_of_pull_iso_pow | exact GlobalTheory.PullAmpleFinite.isFinite_of_pull_iso_pow | (intros; apply GlobalTheory.PullAmpleFinite.isFinite_of_pull_iso_pow <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_shift_finrank_sec_pull_bounds : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Etale φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  first | exact @GlobalTheory.finrank_sec_pull_sandwich | exact GlobalTheory.finrank_sec_pull_sandwich | (intros; apply GlobalTheory.finrank_sec_pull_sandwich <;> assumption)
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.CubicalPackage

theorem surjective_appTop_of_injective {X S P S' : Scheme.{0}} {p : X ⟶ S} {q : P ⟶ S'} {d : P ⟶ X} {f : S' ⟶ S}
    (w : d ≫ p = q ≫ f) {e : S ⟶ X} {e' : S' ⟶ P} (he' : e' ≫ q = 𝟙 _) (hee : e' ≫ d = f ≫ e)
    (hd : Function.Injective d.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective p.appTop.hom := by
  intro a
  obtain ⟨b, hb⟩ := hq (d.appTop.hom a)
  have c : ∀ {A B C : Scheme.{0}} (g : A ⟶ B) (h : B ⟶ C) (x : Γ(C, ⊤)),
      g.appTop.hom (h.appTop.hom x) = (g ≫ h).appTop.hom x := fun g h x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  refine ⟨e.appTop.hom a, hd ?_⟩
  rw [c, w, ← c, c f e, ← hee, ← c, ← hb, c e' q, he', Scheme.Hom.id_appTop]
  rfl

variable {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {A : Over (Spec (CommRingCat.of K))} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem surjective_cube_of_generic [Flat G.hom] (gp : IsGrpPullback A G (etaK V K) F)
    (h : Function.Surjective (G3 A).hom.appTop.hom) : Function.Surjective (G3 G).hom.appTop.hom := by
  have hp := gp.1
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd (G3 G).hom (etaK V K))
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
  have hx : ∀ i, (x i).left ≫ F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
  let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
  have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have hl : l.left ≫ (cubeMapOf gp).F3 = pullback.fst (G3 G).hom (etaK V K) := hom_ext_triple _ fun i => by
    rw [Category.assoc, f3, ← Category.assoc, ← Over.comp_left, lx, hx]
  have inj : Function.Injective (l.left ≫ (cubeMapOf gp).F3).appTop.hom := by
    rw [hl]
    exact Exist.CubicalExtension.app_injective_generic (IsPullback.of_hasPullback _ _) ⊤
  refine surjective_appTop_of_injective (d := (cubeMapOf gp).F3) (f := etaK V K)
    (Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2)))))
    (e := eSec (G3 G)) (e' := eSec (G3 A)) (Over.w η[G3 A]) ?_ ?_ h
  · rw [CubeExtension.eSec_three, CubeExtension.eSec_three]
    refine hom_ext_triple _ fun i => ?_
    have a : ∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B],
        (lift (1 : 𝟙_ (Over S) ⟶ B) (lift (1 : 𝟙_ (Over S) ⟶ B) (1 : 𝟙_ (Over S) ⟶ B))).left ≫ (x3 B i).left =
          eSec B := fun B _ _ => by
      rw [← Over.comp_left, eSec]
      fin_cases i <;> simp [x3, Hom.one_def]
    rw [Category.assoc, f3, ← Category.assoc, a, Category.assoc, a]
    exact (cubeMapOf gp).e_comm
  · rw [Scheme.Hom.comp_appTop] at inj
    exact Function.Injective.of_comp (f := l.left.appTop.hom) inj

theorem exists_package : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G), LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → ∃ P : CP G, P.L = L) := by
  intro laws V _ _ _ hV A G _ _ hG eA hA L h₁
  have := hV.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := A.isAb.comm
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK V) (eA.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  have hi : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨w, hw⟩ : LBIso A.L (L.L.pull (eA.inv.left ≫ pullback.fst G.hom (jK V))) :=
    LBIso.chartPull (chartPullSec A.L _ eA.inv.left hi) (chartPullSame L.L _ _ _ eA.inv.left fun _ => rfl) h₁
  obtain ⟨c⟩ := (laws.cube _ A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  obtain ⟨c'⟩ := PolExtension.nonempty_cubical laws.cubicalExtends gp L c w hw
  obtain ⟨s, hs, hs'⟩ := PolExtension.exists_symmetry gp L.isLB A.isLB A.sym w hw
  exact ⟨CP.ofSurjective (surjective_cube_of_generic gp (surjective_cube laws.globalFns A.isAb)) L c' s hs hs', rfl⟩

end GlobalTheory.CubicalPackage
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem quasiCompact_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X : Scheme.{0}} (f : X ⟶ Sp V)
    (h₁ : QuasiCompact (pullback.snd f (spMap (IsLocalRing.residue V))))
    (h₂ : QuasiCompact (pullback.snd f (jK V))) : QuasiCompact f := by
  have c₁ : CompactSpace ↥(pullback f (spMap (IsLocalRing.residue V))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have c₂ : CompactSpace ↥(pullback f (jK V)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have hu : Set.range (pullback.fst f (spMap (IsLocalRing.residue V))) ∪ Set.range (pullback.fst f (jK V)) =
      Set.univ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro x
    have hx : (Sp V).fromSpecResidueField (f x) (default : PrimeSpectrum _) = f x :=
      Scheme.fromSpecResidueField_apply _ _
    rcases ZJ.field_point_factor_dvr V ((Sp V).residueField (f x)) ((Sp V).fromSpecResidueField (f x)) with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
    · exact Or.inr ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
  have : CompactSpace X := ⟨hu ▸ (isCompact_range (pullback.fst f _).continuous).union
    (isCompact_range (pullback.fst f _).continuous)⟩
  exact (quasiCompact_iff_compactSpace f).2 this

noncomputable local instance (priority := high) grpObjPullbackForSemiAbelian {S T : Scheme.{0}} (f : T ⟶ S)
    (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

theorem isSemiAbelian_of_unifPre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], UnifPre (maximalIdeal V) D A G → IsSemiAbelian G := by
  intro V _ _ _ D A G _ _ U
  obtain ⟨E, -, -, -, -, hE⟩ := gtCoord_isGt V (maximalIdeal V) D.toPre 0 G ⟨U.gt 0⟩
  have h0 := isSemiAbelian_of_isGt _ E _ hE
  have := U.gen_hom
  have hK : IsSemiAbelian ((Over.pullback (jK V)).obj G) :=
    isSemiAbelian_of_grpIso U.gen (isSemiAbelian_of_isAbelianScheme A.A A.isAb)
  let ρ : V ⧸ (maximalIdeal V) ^ (0 + 1) →+* ResidueField V :=
    Ideal.Quotient.factor (Ideal.pow_le_self (by norm_num))
  have hr : spMap (residue V) = spMap ρ ≫ thick V (maximalIdeal V) 0 := by
    rw [← Spec.map_comp]
    congr 1
  have hk : IsSemiAbelian ((Over.pullback (spMap (residue V))).obj G) := by
    rw [hr]
    exact isSemiAbelian_of_grpIso (pullCompIso (spMap ρ) (thick V (maximalIdeal V) 0) G)
      (IsSemiAbelian.pullback (spMap ρ) _ h0)
  exact ZJ.isSemiAbelian_of_fibres_dvr V G U.smooth U.separated
    (quasiCompact_of_fibres_dvr V G.hom hk.quasiCompact hK.quasiCompact) hk hK

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_iso_of_compatible_abelianThickenings : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A) (v : ∀ e : ℕ, LB.Iso (P'.L.pull (fstG I e P'.A).left) (P.L.pull ((β e).hom.left ≫ (fstG I e P.A).left))), (∀ e, (v e).IsGen) → (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι), (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' → Geo.Tor.gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z j (fun _ => j') = Geo.Tor.gw (v e) r z j (fun _ => j')) → ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso P'.L (P.L.pull Φ.hom.left)), w.IsGen ∧ ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι), (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' → Geo.Tor.gw w (r ≫ (fstG I e P'.A).left) z j j' = Geo.Tor.gw (v e) r z j (fun _ => j') := by
  first | exact @GlobalTheory.exists_iso_of_compatible_thickenings | exact GlobalTheory.exists_iso_of_compatible_thickenings | (intros; apply GlobalTheory.exists_iso_of_compatible_thickenings <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_automorphism_of_multiplicative_section_family : ∀ (F : Type) [Field F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), 1 ≤ N → ∀ Φ : ∀ k : ℕ, LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)) ≃ LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)), (∀ k (s s' s'' : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (c : Γ((Over.mk t).left, ⊤)), (∀ j, s''.f j = liftFun P.A _ c * s.f j + s'.f j) → ∀ j, (Φ k s'').f j = liftFun P.A _ c * (Φ k s).f j + (Φ k s').f j) → (∀ k l (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t))) (s'' : LB.Sec (LPow P.A P.L ((N * (k + l + 1 + 1) : ℕ) : ℤ) (Over.mk t))), (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) → ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ (k + l + 1) s'').f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j)) → ∃ (ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A) (_ : ψ.hom ≫ fst _ _ = fst _ _), ∀ k, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk t) P.A).left, (ψ.hom ≫ snd _ _).left] ![((N * (k + 1) : ℕ) : ℤ), -((N * (k + 1) : ℕ) : ℤ)]), α.IsGen ∧ ∀ s, IsTwistPull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl _ _ α s (Φ k s) := by
  first | exact @GlobalTheory.exists_iso_of_multiplicative_section_family | exact GlobalTheory.exists_iso_of_multiplicative_section_family | (intros; apply GlobalTheory.exists_iso_of_multiplicative_section_family <;> assumption)
end
