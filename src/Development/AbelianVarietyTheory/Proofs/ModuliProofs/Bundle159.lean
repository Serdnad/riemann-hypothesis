module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle158
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle073
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.AmpleStabTorsion

theorem finite_sections {k : Type} [Field k] [IsAlgClosed k] (H : Over (Sp k)) [IsFinite H.hom] :
    Finite (Out.baseOver (Sp k) ⟶ H) := by
  have hfin : (Set.univ : Set H.left).Finite :=
    (H.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  have : Finite H.left := Set.finite_univ_iff.1 hfin
  refine Finite.of_injective
    (fun y : Out.baseOver (Sp k) ⟶ H => (y.left : Sp k ⟶ H.left) (IsLocalRing.closedPoint k)) fun y y' h => ?_
  exact Over.OverMorphism.ext (ext_of_apply_closedPoint_eq H.hom (Over.w y) (Over.w y') h)


theorem exists_pow_eq_one : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ x : Out.baseOver (Sp k) ⟶ A, Triv (Out.translDiff A M x) → ∃ m : ℕ, 1 ≤ m ∧ x ^ m = 1 := by
  intro hL k _ _ A _ _ hA M hM hamp x hx
  set_option backward.isDefEq.respectTransparency false in
  have isLB_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) : (AbLaw.pw H t).IsLB := by
    refine { cover := hH.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simpa only [AbLaw.pw, one_zpow, ← map_zpow] using h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simpa only [AbLaw.pw, mul_zpow, ← map_zpow] using h
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy k A M hM).1 hamp
  obtain ⟨h0, -, htw⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns k A hA ⟨_, isLB_pw hM d, n, s, hs⟩ M _ hM h0
  have := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns k A hA M _ hM h0 hamp H j hj hH
  have := finite_sections H
  have hxK : x ∈ GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)) := by
    obtain ⟨c, hc⟩ := hx
    exact fun p => ⟨⊤, trivial, _, LB.isGen_genPull _ c hc _⟩
  have hfin : ((GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)) : Set (Out.baseOver (Sp k) ⟶ A))).Finite :=
    (Set.finite_range fun y : Out.baseOver (Sp k) ⟶ H => y ≫ j).subset fun z hz =>
      (hH _ z).1 ((htw _ rfl _ z).1 hz)
  have : Finite (GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k))) := hfin
  obtain ⟨m, hm, e⟩ := (isOfFinOrder_of_finite (⟨x, hxK⟩ : GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)))).exists_pow_eq_one
  exact ⟨m, hm, congrArg Subtype.val e⟩

end GlobalTheory.AmpleStabTorsion
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing : GlobalTheory.LN.HomExtSt := by
  first | exact @GlobalTheory.homExtension_semiAbelian_dvr | exact GlobalTheory.homExtension_semiAbelian_dvr | (intros; apply GlobalTheory.homExtension_semiAbelian_dvr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

section Point

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U}

def pointCpt (hc : IsIso c) (ht : IsIso t₀.G.hom) (β : O →+* F) (hn : Geo.Tor.IsNormalScheme (Sp O)) :
    Cpt c t₀ β where
  X := Sp O
  s := 𝟙 _
  normal := hn
  proj := Inhab.isProjOver_id O
  flat := inferInstance
  jQ := c ≫ inv (pullback.snd _ _)
  jQ_over := by simp
  jQ_open := inferInstance
  jQ_dense := by
    rw [Set.range_eq_univ.2 (c ≫ inv (pullback.snd (𝟙 _) (spMap β))).surjective]
    exact dense_univ
  t := Inhab.zeroTriple H _
  m := (nonempty_sabMap ht (isIso_zeroTriple _) _).some
  ab_gen := by
    rw [Set.range_eq_univ.2 (c ≫ inv (pullback.snd (𝟙 _) (spMap β))).surjective,
      Inhab.abLocus_eq_univ _ (Inhab.isProper_zeroTriple _), Set.preimage_univ]

end Point

theorem zeta_one : zeta 1 = 1 := (pow_one _).symm.trans (BaseRing.zeta_pow_self one_pos)

theorem KA_le_of_eq_one {l₀ : Level H} (h : l₀.A = 1) (l : Level H) : KA l₀ ≤ KA l := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [h, zeta_one]; exact one_mem _

end GlobalTheory.Models.RankZero

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.EmbedLocal

theorem exists_emb_projRep :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ :=
  of_parts GlobalTheory.exists_emb_locally GlobalTheory.T.thetaEmbeddingSections_baseChange_affine GlobalTheory.T.embedding_sections_span_geometric_fibre GlobalTheory.T.projCoordRepresentation_geometric_fibre_spanning GlobalTheory.FibreEmbed.projRep_of_fibres

end GlobalTheory.ZM.EmbedLocal
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ExtAmple

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem relAmple_pullback_of_fac {S S₀ T : Scheme.{0}} [IsAffine S₀] {B : Over S} {A : Over S₀} {L : LB B.left}
    {L₀ : LB A.left} (hL : L.IsLB) (hL₀ : L₀.IsLB) {g : S₀ ⟶ S} {φ : A.left ⟶ B.left}
    (h : IsPullback φ A.hom B.hom g) (e : LBIso L₀ (L.pull φ)) (hA : RelAmple A L₀) (y : T ⟶ S₀) :
    RelAmple ((Over.pullback (y ≫ g)).obj B) (L.pull (pullback.fst B.hom (y ≫ g))) := by
  let ψ : pullback B.hom (y ≫ g) ⟶ A.left :=
    h.lift (pullback.fst B.hom (y ≫ g)) (pullback.snd B.hom (y ≫ g) ≫ y) (by rw [Category.assoc]; exact pullback.condition)
  have hψ : ψ ≫ φ = pullback.fst B.hom (y ≫ g) := h.lift_fst _ _ _
  have H : IsPullback ψ (pullback.snd B.hom (y ≫ g)) A.hom y := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hψ]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨w, hw⟩ : LBIso (L.pull (pullback.fst B.hom (y ≫ g))) (L₀.pull ψ) :=
    LBIso.chartPull
      (chartPullSame L (fun _ : PUnit => pullback.fst B.hom (y ≫ g)) (fun _ => φ) (fun _ => 1) ψ fun _ => hψ.symm)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L₀ _ _ rfl) (LBIso.symm e)
  exact relAmple_pull (A' := (Over.pullback (y ≫ g)).obj B) H hL₀ (pull_isLB hL _)
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA

theorem fac_or_fac (V K k : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [Field k] (f : V →+* k) :
    (∃ g : K →+* k, f = g.comp (algebraMap V K)) ∨
      ∃ g : IsLocalRing.ResidueField V →+* k, f = g.comp (IsLocalRing.residue V) := by
  by_cases hf : RingHom.ker f = ⊥
  · have hi : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f).2 hf
    exact Or.inl ⟨IsFractionRing.lift hi, RingHom.ext fun x => (IsFractionRing.lift_algebraMap hi x).symm⟩
  · have hm : (RingHom.ker f).IsMaximal := (RingHom.ker_isPrime f).isMaximal hf
    have he := IsLocalRing.eq_maximalIdeal hm
    exact Or.inr ⟨Ideal.Quotient.lift _ f (fun a ha => by rw [← he] at ha; exact ha), RingHom.ext fun x => rfl⟩

theorem relAmple_extension : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple B M.L.L := by
  intro h₁ h₂ V K _ _ _ _ _ _ P B _ _ M φ hB hφ e hc
  refine GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres h₁ h₂ V hc B hB M fun k _ x => ?_
  obtain ⟨f, rfl⟩ := Spec.map_surjective x
  rcases fac_or_fac V K k f.hom with ⟨g, hg⟩ | ⟨g, hg⟩
  · have hx : Spec.map f = spMap g ≫ spMap (algebraMap V K) := by
      rw [← Spec.map_comp]; congr 1; exact CommRingCat.hom_ext hg
    rw [hx]
    exact relAmple_pullback_of_fac M.L.isLB P.isLB hφ.1 e P.ample _
  · have hx : Spec.map f = spMap g ≫ spMap (IsLocalRing.residue V) := by
      rw [← Spec.map_comp]; congr 1; exact CommRingCat.hom_ext hg
    rw [hx]
    exact relAmple_pullback_of_fac (A := (Over.pullback (spMap (IsLocalRing.residue V))).obj B) M.L.isLB
      (pull_isLB M.L.isLB _) (IsPullback.of_hasPullback _ _) (lbIso_self (pull_isLB M.L.isLB _))
      (GlobalTheory.T.relAmple_specialFibre_extended_principalPolarisation h₁ h₂ V K P B M φ hB hφ e hc) _

end GlobalTheory.ExtAmple
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

theorem lbIso_of_compat : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [IsReduced R] (s : Sp R ⟶ Sp o) (t t' : TObj g k J b s) (Sg : Set (Sp R)) (φ : t.A.left ⟶ t'.A.left), Dense Sg → GeoGood t t' Sg → Compat t t' (𝟙 _) φ → IsGrpPullback t.A t'.A (𝟙 _) φ → LBIso t.L (t'.L.pull φ) := by
  intro o _ g k J b R _ _ s t t' Sg φ hd hg hc hφ
  have hp := pull_isLB t'.isLB φ
  have hN := LB.isLB_div hp t.isLB
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ t.A.left),
      CechPic.pull (f ≫ φ) (CechPic.cls _ t'.isLB) = CechPic.pull f (CechPic.cls _ t.isLB) →
      ∃ w : ((LB.div (t'.L.pull φ) t.L).pull f).Gen, w.IsGen := fun f e => by
    refine (CechPic.cls_eq_zero_iff (pull_isLB hN f)).1 ?_
    rw [CechPic.cls_pull hN, CechPic.cls_div hp t.isLB, map_sub, CechPic.cls_pull t'.isLB, ← CechPic.pull_comp, e, sub_self]
  refine GlobalTheory.T.seesaw_rigidified_lineBundle_dense_fibres R t.A t.L _ Sg t.ab t.isLB t.ample hN hd (key _ ?_) fun p hpS => ?_
  · have e : eSec t.A ≫ φ = eSec t'.A := (PolBaseChange.eSec_comm hφ).trans (Category.id_comp _)
    have e₁ := (CechPic.cls_eq_zero_iff (pull_isLB t.isLB _)).2 t.rigid
    have e₂ := (CechPic.cls_eq_zero_iff (pull_isLB t'.isLB _)).2 t'.rigid
    rw [e]
    exact e₂.trans e₁.symm
  · obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := hg ((Sp R).residueField p) ((Sp R).fromSpecResidueField p) (by
      rw [Scheme.range_fromSpecResidueField]; exact Set.singleton_subset_iff.2 hpS)
    refine ⟨Ω, inferInstance, _, _, ψ, _, ⟨(default : PrimeSpectrum Ω), ?_⟩, h₁.1.1, key ψ ?_⟩
    · exact Scheme.fromSpecResidueField_apply p _
    · rw [hc.fibre h₁ h₂]
      exact ((CechPic.cls_eq_iff u.isLB (pull_isLB t'.isLB _)).2 h₂.2.1).symm.trans
        ((CechPic.cls_eq_iff u.isLB (pull_isLB t.isLB _)).2 h₁.2.1)

end GlobalTheory.TUniq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.exists_torsion_cubeLB_iso_polarisation_translate : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → (k : K) ≠ 0 → x ^ k = 1 → ∃ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 ∧ LBIso (cubeLB P.A ![toUnit P.A ≫ x, 𝟙 P.A] M) (cubeLB P.A ![toUnit P.A ≫ y, 𝟙 P.A] P.L) := by
  first | exact @GlobalTheory.exists_torsion_lbIso_cubeLB | exact GlobalTheory.exists_torsion_lbIso_cubeLB | (intros; apply GlobalTheory.exists_torsion_lbIso_cubeLB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u v : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsMonHom u → IsMonHom v → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' v' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ v'.left ≫ φ = φ ≫ v.left ∧ LBIso (cubeLB G ![fst G G ≫ u', snd G G] L') (cubeLB G ![fst G G, snd G G ≫ v'] L')} → LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  first | exact @GlobalTheory.adjoint_cubeLB_of_dense_fibres | exact GlobalTheory.adjoint_cubeLB_of_dense_fibres | (intros; apply GlobalTheory.adjoint_cubeLB_of_dense_fibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.lbIso_cube_graph_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.Rigidified A L → IsMonHom u → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ LBIso L' (cubeLB G ![𝟙 G, u'] L')} → LBIso L (cubeLB A ![𝟙 A, u] L) := by
  first | exact @GlobalTheory.lbIso_cube_of_dense | exact GlobalTheory.lbIso_cube_of_dense | (intros; apply GlobalTheory.lbIso_cube_of_dense <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_basicOpen_kTriv_of_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] (x : R →+* K) (A₀ : Over (Sp K)) [GrpObj A₀] (φ₀ : A₀.left ⟶ A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsGrpPullback A₀ A (spMap x) φ₀ → Out.KTriv A₀ (L.pull φ₀) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (A' : Over (Sp R')) [GrpObj A'] (π : A'.left ⟶ A.left), IsUnit (φ f) → IsGrpPullback A' A (spMap φ) π → Out.KTriv A' (L.pull π) := by
  first | exact @GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit | exact GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit | (intros; apply GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian : Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (N : LB (A ⊗ B).left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → (∃ t : (N.pull (lift (1 : B ⟶ A) (𝟙 B)).left).Gen, t.IsGen) → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ A | ∃ t : (N.pull (lift (toUnit B ≫ x) (𝟙 B)).left).Gen, t.IsGen}, Set.range x.left) → (∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ B)).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian | exact GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian | (intros; apply GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_clopen_weilIs_iff : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), 0 < n → IsUnit (n : Γ(T.left, ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 → ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T), Out.WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U :=
  fun hL => PairingLocus.exists_clopen_of_lift hL.globalFns
    (kerPow_of_square (AbSquare.square_of_cube T.cube_theorem_and_sections_finite_growth_abelianVariety.1).1).2.2

end GlobalTheory
end
