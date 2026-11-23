module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSmulEqSumMulOfIsDomain
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle086
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbTriv

variable {X X' S S' : Scheme.{0}} {N : LB X}

theorem exists_normalised (hN : N.IsLB) {p : X ⟶ S} {e : S ⟶ X} (he : e ≫ p = 𝟙 S)
    (c : LB.Gen (N.pull e)) (hc : c.IsGen) {π : X' ⟶ X} {p' : X' ⟶ S'} {g : S' ⟶ S}
    (h : IsPullback π p' p g) (ht : Triv (N.pull π)) :
    ∃ t : LB.Gen (N.pull π), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (b : Z ⟶ S) (z : Z) (J),
      Good N z J → r ≫ π = b ≫ e → val t r z J = val c b z J := by
  obtain ⟨t, ht⟩ := ht
  let n : X' ⟶ X' := h.lift ((π ≫ p) ≫ e) p' (by rw [Category.assoc, he, Category.comp_id, h.w])
  have n₁ : n ≫ π = (π ≫ p) ≫ e := h.lift_fst _ _ _
  have n₂ : n ≫ p' = p' := h.lift_snd _ _ _
  obtain ⟨t', ht', hv⟩ := exists_gen hN (K' := PUnit) (φ' := fun _ => π) (ε' := fun _ => 1)
    (fun V _ k => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, n₁, mul_inv_cancel,
        _root_.mul_one])
    (LB.mulGen N _ _ _ _ t (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ c (π ≫ p))
      (LB.invGen N _ _ (LB.pullGen N _ _ t n))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hc _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n))))
  refine ⟨t', ht', fun Z r b z J hJ hr => ?_⟩
  have hb : r ≫ π ≫ p = b := by rw [← Category.assoc, hr, Category.assoc, he, Category.comp_id]
  have hn : r ≫ n = r := h.hom_ext
    (by rw [Category.assoc, n₁, ← Category.assoc, hb, hr]) (by rw [Category.assoc, n₂])
  rw [hv Z r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, hn, hb, mul_comm (val c b z J),
    mul_inv_cancel_left]

theorem triv_of_pull_id (h : Triv (N.pull (𝟙 X))) : Triv N := by
  obtain ⟨t, ht⟩ := h
  have le : ∀ i, N.U i ≤ (N.pull (𝟙 X)).U (fun _ => i) := fun i x hx => mem_pull.2 hx
  refine ⟨⟨fun i => res (le i) (t.s fun _ => i)⟩, fun i j => unit_ext fun x hx => ?_⟩
  have e := gen_trans ht (𝟙 X) x (le i hx.1) (le j hx.2)
  simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp] at e
  refine ((gm_res _ x _ hx _).trans (gm_res _ x _ hx.1 _)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ x _ hx _).trans (gm_res _ x _ hx.2 _)))

theorem eq_top_of_closed_fibre {V : Type} [CommRing V] [IsLocalRing V] (p : X ⟶ Spec (CommRingCat.of V))
    [UniversallyClosed p] (U : X.Opens) (h : ∀ x, p x = IsLocalRing.closedPoint V → x ∈ U) : U = ⊤ := by
  have hc : IsClosed (p '' (U : Set X)ᶜ) := p.isClosedMap _ U.isOpen.isClosed_compl
  have := DVR.eq_top_of_closedPoint_mem (V := V) ⟨_, hc.isOpen_compl⟩ (by
    rintro ⟨x, hx, e⟩
    exact hx (h x e))
  refine eq_top_iff.2 fun x _ => by_contra fun hx => ?_
  have hm : p x ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) := trivial
  rw [← this] at hm
  exact hm ⟨x, hx, rfl⟩

theorem closedPoint_mem_range {V : Type} [CommRing V] [IsLocalRing V] (e : ℕ) :
    IsLocalRing.closedPoint V ∈ Set.range (thick V (IsLocalRing.maximalIdeal V) e) := by
  have h := range_comap_of_surjective _ _
    (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal V ^ (e + 1)))
  refine h.ge ?_
  rw [Ideal.mk_ker]
  exact Ideal.pow_le_self (Nat.succ_ne_zero e)

theorem triv_of_forall_thick : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ N : LB B.left, N.IsLB → (∀ e, Triv (N.pull (fstG (IsLocalRing.maximalIdeal V) e B).left)) → Triv N := by
  intro hG V _ _ _ hV B _ hB hp N hN ht
  let I := IsLocalRing.maximalIdeal V
  let o : Spec (CommRingCat.of V) ⟶ B.left := (η[B]).left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local N hN (K := PUnit) (fun _ => o) (fun _ => 1)
  have pb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) :=
    fun e => IsPullback.of_hasPullback B.hom (thick V I e)
  choose t tg tv using fun e => exists_normalised hN ho c hc (pb e) (ht e)
  have tm : ∀ e, thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have compat : ∀ e z J, Good N z J → val (t (e + 1)) (thickMap V I e B) z J = val (t e) (𝟙 _) z J := by
    intro e z J hJ
    let a := (pb e).lift (thick V I e ≫ o) (𝟙 _) (by rw [Category.assoc, ho, Category.comp_id, Category.id_comp])
    have a₁ : a ≫ (fstG I e B).left = thick V I e ≫ o := (pb e).lift_fst _ _ _
    have key := gen_unique' hN (fun U _ k => by simp only [tm e]) (thickObj V I e B).hom a ((pb e).lift_snd _ _ _)
      (hG _ _ (TLinPf.isAb_pullback (thick V I e) B hB)).2 (tg e)
      (DVR.pullGen_isGen _ _ _ _ (tg (e + 1)) (thickMap V I e B))
      (fun y J hJ => (tv e _ a _ y J hJ a₁).trans ((val_pull hJ _ _ _).trans
        (tv (e + 1) _ _ _ y J hJ (by rw [Category.assoc, tm e, a₁]))).symm) _ (𝟙 _) z J hJ
    rw [val_pull hJ, Category.id_comp] at key
    exact key.symm
  obtain ⟨s, hs, -⟩ := GlobalTheory.SecAlg.existsUnique_sec V I hV B hB.smooth hp N hN (fun e => genSec (t e) (tg e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (compat e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have := hB.proper
  have top : nonzeroLocus s = ⊤ := eq_top_of_closed_fibre B.hom _ fun x hx => by
    have hm : x ∈ Set.range (pullback.fst B.hom (thick V I 0)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact closedPoint_mem_range 0
    obtain ⟨z, rfl⟩ := hm
    choose J hJ using fun ψ : ((Over.map (thick V I 0)).obj (thickObj V I 0 B)).left ⟶ B.left =>
      exists_chart hN (ψ z)
    refine (TwistZero.mem_nonzeroLocus_iff s (fstG I 0 B).left z hJ).2 ?_
    rw [hs 0 z J hJ, sval_genSec _ _ _ z hJ]
    exact Units.isUnit _
  refine triv_of_pull_id (TwistZero.triv_of_sec hN s fun y J hJ => ?_)
  exact (TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)

end GlobalTheory.AbTriv
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TrivSubscheme

theorem exists_idealSheaf {T : Scheme.{0}} (P : ∀ Y : Scheme.{0}, (Y ⟶ T) → Prop)
    (hcomp : ∀ (Y Z : Scheme.{0}) (x : Y ⟶ T) (h : Z ⟶ Y), P Y x → P Z (h ≫ x))
    (hloc : ∀ (Y : Scheme.{0}) (x : Y ⟶ T),
      (∀ y : Y, ∃ V : Y.affineOpens, y ∈ V.1 ∧ P _ (V.2.fromSpec ≫ x)) → P Y x)
    (haff : ∀ U : T.affineOpens, ∃ I : Ideal Γ(T, U), ∀ (S : CommRingCat.{0}) (g : Γ(T, U) ⟶ S),
      P _ (Spec.map g ≫ U.2.fromSpec) ↔ I ≤ RingHom.ker g.hom) :
    ∃ I : T.IdealSheafData, ∀ (Y : Scheme.{0}) (x : Y ⟶ T), P Y x ↔ I ≤ x.ker := by
  choose J hJ using haff
  have hmap : ∀ (U V : T.affineOpens) (h : V.1 ≤ U.1),
      (J U).map (T.presheaf.map (homOfLE h).op).hom = J V := by
    intro U V h
    have key : ∀ K : Ideal Γ(T, V), (J U).map (T.presheaf.map (homOfLE h).op).hom ≤ K ↔ J V ≤ K := by
      intro K
      have h₁ := hJ V _ (CommRingCat.ofHom (Ideal.Quotient.mk K))
      have h₂ := hJ U _ (T.presheaf.map (homOfLE h).op ≫ CommRingCat.ofHom (Ideal.Quotient.mk K))
      rw [Spec.map_comp, Category.assoc, IsAffineOpen.map_fromSpec U.2 V.2, h₁, CommRingCat.hom_comp,
        ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker] at h₂
      rw [Ideal.map_le_iff_le_comap, h₂]
    exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)
  refine ⟨⟨J, fun U f => hmap U (T.affineBasicOpen f) _, _, rfl⟩, fun Y x => ?_⟩
  have hV : ∀ (U : T.affineOpens) (V : Y.affineOpens) (e : V.1 ≤ x ⁻¹ᵁ U.1),
      P _ (V.2.fromSpec ≫ x) ↔ J U ≤ RingHom.ker (x.appLE U.1 V.1 e).hom := fun U V e => by
    rw [← hJ, IsAffineOpen.SpecMap_appLE_fromSpec x U.2 V.2 e]
  have hex : ∀ (W : Y.Opens) (y : Y), y ∈ W → ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ W := fun W y hy => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
    exact ⟨⟨V, hV⟩, hyV, hle⟩
  constructor
  · intro hx
    refine Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_
    refine Y.IsSheaf.section_ext fun y hy => ?_
    obtain ⟨V, hyV, hle⟩ := hex _ y hy
    refine ⟨V.1, hle, hyV, ?_⟩
    exact ((hV U V hle).1 (hcomp _ _ _ _ hx) ha).trans (map_zero _).symm
  · intro hx
    refine hloc Y x fun y => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x y)) isOpen_univ
    obtain ⟨V, hyV, hle⟩ := hex (x ⁻¹ᵁ U) y hyU
    refine ⟨V, hyV, (hV ⟨U, hU⟩ V hle).2 fun a ha => ?_⟩
    have h₁ : (x.app U).hom a = 0 := x.ideal_ker_le ⟨U, hU⟩ (hx ⟨U, hU⟩ ha)
    rw [RingHom.mem_ker, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (congrArg _ h₁).trans (map_zero _)

theorem triv_pull_iff {X Y Z : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (h : Z ⟶ Y) :
    Triv ((M.pull f).pull h) ↔ Triv (M.pull (h ≫ f)) :=
  ⟨fun ⟨t, ht⟩ => exists_isGen_linComb_of_pull M _ _ _ t ht, CubeOpen.triv_pull_pull f h⟩

variable {X T : Scheme.{0}} (p : X ⟶ T) (F : LB X)

def TrivOver {Y : Scheme.{0}} (x : Y ⟶ T) : Prop := Triv (F.pull (pullback.fst p x))

def LocTrivOver (Y : Scheme.{0}) (x : Y ⟶ T) : Prop :=
  ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ TrivOver p F (U.ι ≫ x)

variable {p F}

theorem TrivOver.triv {Y Z : Scheme.{0}} {x : Y ⟶ T} (H : TrivOver p F x) (k : Z ⟶ X) (z : Z ⟶ Y)
    (e : k ≫ p = z ≫ x) : Triv (F.pull k) :=
  CubeOpen.triv_comp (pullback.lift k z e) (pullback.lift_fst _ _ _) H

theorem TrivOver.comp {Y Z : Scheme.{0}} {x : Y ⟶ T} (H : TrivOver p F x) (h : Z ⟶ Y) {w : Z ⟶ T}
    (e : h ≫ x = w) : TrivOver p F w :=
  H.triv _ (pullback.snd _ _ ≫ h) (by rw [pullback.condition, Category.assoc, e])

theorem LocTrivOver.comp (Y Z : Scheme.{0}) (x : Y ⟶ T) (h : Z ⟶ Y) (H : LocTrivOver p F Y x) :
    LocTrivOver p F Z (h ≫ x) := fun z => by
  obtain ⟨U, hU, ht⟩ := H (h z)
  exact ⟨h ⁻¹ᵁ U, hU, ht.comp (h ∣_ U) (by rw [morphismRestrict_ι_assoc])⟩

theorem locTrivOver_of_affine (Y : Scheme.{0}) (x : Y ⟶ T)
    (H : ∀ y : Y, ∃ V : Y.affineOpens, y ∈ V.1 ∧ LocTrivOver p F _ (V.2.fromSpec ≫ x)) :
    LocTrivOver p F Y x := fun y => by
  obtain ⟨V, hy, hV⟩ := H y
  obtain ⟨q, rfl⟩ := V.2.range_fromSpec.ge hy
  obtain ⟨U, hU, ht⟩ := hV q
  haveI : IsOpenImmersion V.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec (U := V.1) V.2
  have hr : Set.range (V.2.fromSpec ''ᵁ U).ι ⊆ Set.range (U.ι ≫ V.2.fromSpec) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨V.2.fromSpec ''ᵁ U, ⟨q, hU, rfl⟩, ht.comp (IsOpenImmersion.lift _ _ hr) ?_⟩
  rw [← Category.assoc U.ι, IsOpenImmersion.lift_fac_assoc]

theorem locTrivOver_iff {Y X' : Scheme.{0}} {x : Y ⟶ T} {π : X' ⟶ X} {f' : X' ⟶ Y} (h : IsPullback π f' p x) :
    LocTrivOver p F Y x ↔ ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ Triv (F.pull ((f' ⁻¹ᵁ U).ι ≫ π)) := by
  refine forall_congr' fun y => exists_congr fun U => and_congr_right fun _ => ⟨fun ht => ?_, fun ht => ?_⟩
  · exact ht.triv _ (f' ∣_ U) (by rw [morphismRestrict_ι_assoc, Category.assoc, h.w])
  · have hp := (isPullback_morphismRestrict f' U).flip.paste_horiz h
    exact CubeOpen.triv_comp (hp.lift _ _ pullback.condition) (hp.lift_fst _ _ _) ht

theorem exists_closed_locTriv : GlobalFnsSt → ∀ (R : Type) [CommRing R] (T B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB (T ⊗ B).left, F.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ T), IsClosedImmersion j.left ∧ ∀ (T' : Over (Spec (CommRingCat.of R))) (x : T' ⟶ T), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (x ▷ B).left).pull ((fst T' B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  intro hG R _ T B _ hB hproj F hF
  have h₀ : IsPullback (pullback.snd T.hom B.hom) (fst T B).left B.hom T.hom :=
    (IsPullback.of_hasPullback T.hom B.hom).flip
  obtain ⟨I, hI⟩ := exists_idealSheaf (LocTrivOver (fst T B).left F) LocTrivOver.comp locTrivOver_of_affine
    (fun U => by
      let t : Spec (CommRingCat.of Γ(T.left, U)) ⟶ Spec (CommRingCat.of R) := U.2.fromSpec ≫ T.hom
      have h₁ : IsPullback (pullback.fst B.hom t) (pullback.snd B.hom t) B.hom (U.2.fromSpec ≫ T.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd B.hom t) (fst T B).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      letI : (Over.pullback t).Monoidal := (Over.instBraidedPullback (f := t)).toMonoidal
      letI : GrpObj ((Over.pullback t).obj B) := Functor.grpObjObj (F := Over.pullback t)
      obtain ⟨I, hI⟩ := TrivRep.exists_ideal_locTriv hG Γ(T.left, U) ((Over.pullback t).obj B)
        (CubeGen.isAb_baseChange hB t) (CubeProj.isProjBy_baseChange hproj h₁) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun S g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd B.hom t) (Spec.map g)
      rw [← hI S g.hom _ _ _ h₃, locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((triv_pull_iff _ _ _).trans (triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ T.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩
  have h₄ : IsPullback (x ▷ B).left (fst T' B).left (fst T B).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerRight_left_fst x) h₀
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom B.hom).flip
  simp only [triv_pull_iff]
  rw [← locTrivOver_iff h₄, hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ x.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨y, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)

end GlobalTheory.TrivSubscheme
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.TorsionCount

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) : LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem pw_pw {X : Scheme.{0}} (H : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw H a) b = AbLaw.pw H (a * b) := by
  unfold AbLaw.pw
  congr 1
  funext i j
  exact (zpow_mul _ _ _).symm

def chartPullPw {X Y : Scheme.{0}} (H : LB X) (φ : Y ⟶ X) (t : ℤ) :
    ChartPull ((AbLaw.pw H t).pull φ) (AbLaw.pw (H.pull φ) t) (𝟙 Y) where
  idx j := j
  le _ _ hy := hy
  g y i j hi hj :=
    (gm_pull_g (AbLaw.pw H t) φ (𝟙 Y) y i j hi hj).trans ((map_zpow _ _ t).trans
      ((congrArg (· ^ t) (gm_pull_g H φ (𝟙 Y) y i j hi hj).symm).trans (map_zpow _ _ t).symm))

theorem nonempty_secEquiv {K : Type} [CommRing K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ X)
    (hφ : φ ≫ f = f) {H : LB X} (hH : H.IsLB) (q : ℕ) (h : LBIso (AbLaw.pw H q) (H.pull φ)) (t : ℕ) :
    Nonempty (SecOnR f (AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ ≃ₗ[K] SecOnR (φ ≫ f) ((AbLaw.pw H t).pull φ) ⊤) := by
  have h₁ := (lbIso_pw h t).chartPull (chartPullId _) (chartPullPw H φ t)
  rw [pw_pw, ← Nat.cast_mul] at h₁
  obtain ⟨w, hw⟩ := h₁
  rw [hφ]
  exact ⟨SecOnR.linEquiv f (SecOn.congr (isLB_pw hH _) (pull_isLB (isLB_pw hH _) φ) w hw ⊤)⟩

theorem card_torsion_points : GlobalFnsSt → RigiditySt → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) := by
  intro hG _ k _ _ B _ g n hB hg hn
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hq : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hn0)
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec B)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB).1 ⟨H, r, hH, hr⟩ (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH) hsym
  have hiso : LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (𝟙 B ^ n).left) := by
    have h := GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing k B M n
    rw [hM] at h
    rw [Nat.cast_pow]
    exact h
  have hφ : (𝟙 B ^ n).left ≫ B.hom = B.hom := Over.w _
  haveI : IsFinite (𝟙 B ^ n).left :=
    GlobalTheory.T.isFinite_of_pull_veryAmple_iso_pow k _ _ B.hom _ H H m s (n ^ 2) hH hH inferInstance (by rw [hφ]; exact hs) hq hiso
  haveI : Etale (𝟙 B ^ n).left := GrpTangent.etale_id_pow B (by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  have hcard := GlobalTheory.finrank_eq_card_kernel_points_of_etale k B hB (𝟙 B ^ n)
  have hc : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} =
      Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ B // y ≫ (𝟙 B ^ n) = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by rw [MonObj.comp_pow, Category.comp_id])
  rw [hc]
  obtain ⟨hfin, hmono, c, C, hc1, hgrow⟩ := GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k B.left B.hom g hg H m s hH hs
  have e := nonempty_secEquiv B.hom _ hφ hH (n ^ 2) hiso
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_shift_finrank_sec_pull_bounds k B.left B.left B.hom (𝟙 B ^ n).left H m s hH hs _ hcard hfin fun t => by
    obtain ⟨e⟩ := e t
    haveI := hfin (n ^ 2 * t)
    exact Module.Finite.equiv e
  rw [pow_mul]
  refine GlobalTheory.UU.degree_eq_pow_of_growth (fun t : ℕ => Module.finrank k (SecOnR B.hom (AbLaw.pw H t) ⊤)) g c C a _ (n ^ 2) hc1 hq
    hmono hgrow fun t => ?_
  obtain ⟨e₁⟩ := e (t + a)
  obtain ⟨e₂⟩ := e t
  exact ⟨(ha t).1.trans e₁.finrank_eq.ge, e₂.finrank_eq.le.trans (ha t).2⟩

end GlobalTheory.UU.TorsionCount
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU

theorem exists_addG : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  intro V _ _ _ _ D A G _ _ U θ
  have := U.semi.smooth
  have := U.semi.separated
  have := U.semi.quasiCompact
  obtain ⟨v, hv⟩ := exists_addSec _ G U.P (𝟙_ _) θ (toUnit _)
  obtain ⟨v', hv'⟩ := exists_sec U.P.L.isLB (K' := Fin 1 ⊕ Fin 1)
    (φ' := Sum.elim (fun _ => (fst G G).left ≫ 𝟙 G.left) (fun _ => (snd G G).left ≫ 𝟙 G.left))
    (ε' := Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ)))
    (fun U _ h => by simp only [Category.comp_id]) v
  obtain ⟨r, hr, n, a, b, hab⟩ := GlobalTheory.exists_smul_eq_sum_mul_of_isDomain V G.left U.P.L.L U.P.L.isLB G G (Fin 1) (Fin 1)
    (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ)) (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ)) v'
  have mv : ∀ s : LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((2 : ℕ) : ℤ))),
      ∃ σ : U.SecGT (𝟙_ _) 2, ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ G) (z : T.left) (J), Good U.P.L.L z J →
        sval σ (lift (toUnit T) x).left z J = sval s x.left z J := fun s => by
    obtain ⟨σ, hσ⟩ := exists_sec U.P.L.isLB (K' := Fin 1) (φ' := fun _ => (snd (𝟙_ _) G).left)
      (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun U _ h => by simp only [Category.comp_id])
      (H1.SectionArithmetic.pullSec s (snd (𝟙_ _) G).left)
    refine ⟨σ, fun T x z J hJ => (hσ _ _ z J hJ).trans ?_⟩
    rw [H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, ← Over.comp_left, lift_snd]
  choose mv hmv using mv
  refine ⟨r, n, fun i => mv (a i), fun i => mv (b i), hr, fun T x y z J hJ => ?_⟩
  have e := hab T.left (lift x y).left z J hJ
  rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd, hv' _ _ z J hJ, hv T x y z J hJ,
    toUnit_unique (lift x y ≫ toUnit _) (toUnit T)] at e
  have g : gs (lift x y).left z ⊤ (scal (G ⊗ G).hom r) = gs (𝟙 _) z ⊤ (scal T.hom r) := by
    have p : ∀ {Z Y : Scheme.{0}} (f : Z ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of V)) (w : Z),
        gs f w ⊤ (scal q r) = gs (f ≫ q) w ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) :=
      fun f q w => gs_pull f q w ⊤ trivial _
    rw [p, p, Over.w, Category.id_comp]
  simp only [hmv _ T _ z J hJ]
  rw [e, g, _root_.mul_assoc]

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.fourierJacobiExpansion_overField_injective : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → (t = t' ↔ s = s')) := by
  first | exact @GlobalTheory.UU.ExpFUniq.main | exact GlobalTheory.UU.ExpFUniq.main | (intros; apply GlobalTheory.UU.ExpFUniq.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.finite_not_psiIn_maximalIdeal_pow : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  first | exact @GlobalTheory.psi_tendsto_zero | exact GlobalTheory.psi_tendsto_zero | (intros; apply GlobalTheory.psi_tendsto_zero <;> assumption)
end
