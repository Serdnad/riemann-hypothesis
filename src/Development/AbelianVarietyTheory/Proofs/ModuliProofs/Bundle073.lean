module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigid
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionFinite

theorem finite_torsion_semiAbelian_of_abelian :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ n : ℕ, 0 < n → Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1} := by
  intro hB k _ _ G _ hG n hn
  haveI := hG.comm
  let t : Sp k ⟶ Sp k := 𝟙 _
  have h := (semiAbelian_torsion_finite_and_closedPoint_finiteOrder hB).1 k
    ((Over.pullback t).obj G) (hG.fibres k t) n hn
  have hp := isGrpPullback_pullback G t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst G.hom t = y.left ≫ pullback.fst G.hom t :=
        congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y))
        (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Finite {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ G // x ^ n = 1} := by
    refine Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun x => x ^ n = 1) fun x => ?_)
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

end GlobalTheory.TorsionFinite
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.BundleNormalise

open GlobalTheory.RigidTriv

variable {X Y : Scheme.{0}}

private theorem gm_res_eq_gm (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V) (u : Γ(X, U)ˣ) :
    gm f y V (res h u) = gm f y U u := by
  rw [← gm_id_pull f y V hy, pullU_res₂ f h u]
  exact gm_rp₁ f y U (f ⁻¹ᵁ V) (f.preimage_mono h) hy u

theorem gm_div {M M' : LB X} (f : Y ⟶ X) (y : Y) (a a' : M.ι) (b b' : M'.ι)
    (hm : f y ∈ M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) :
    gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) ((LB.div M M').g (a, b) (a', b')) =
      gm f y _ (M.g a a') * (gm f y _ (M'.g b b'))⁻¹ := by
  simp only [LB.div]
  rw [map_mul, map_inv]
  erw [gm_res_eq_gm f y _ hm, gm_res_eq_gm f y _ hm]

theorem gm_iso {M M' : LB X} {w : LB.Iso M' M} (hw : w.IsGen) (f : Y ⟶ X) (y : Y) (a a' : M.ι) (b b' : M'.ι)
    (hm : f y ∈ M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) :
    gm f y (M.U a ⊓ M'.U b) (w.s (a, b)) =
      gm f y _ (M.g a a') * (gm f y _ (M'.g b b'))⁻¹ * gm f y (M.U a' ⊓ M'.U b') (w.s (a', b')) := by
  have hl : M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b') ≤ M.U a ⊓ M'.U b := inf_le_left
  have hr : M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b') ≤ M.U a' ⊓ M'.U b' := inf_le_right
  refine (gm_res_eq_gm f y hl hm (w.s (a, b))).symm.trans ?_
  refine (congrArg (gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b'))) (hw (a, b) (a', b'))).trans ?_
  refine (map_mul (gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b'))) _ _).trans ?_
  exact congrArg₂ (· * ·) (gm_div f y a a' b b' hm) (gm_res_eq_gm f y hr hm (w.s (a', b')))

private theorem units_ext_of_gm_id_eq {Z : Scheme.{0}} {W : Z.Opens} (u v : Γ(Z, W)ˣ)
    (h : ∀ x ∈ W, gm (𝟙 Z) x W u = gm (𝟙 Z) x W v) : u = v := by
  have key : (Scheme.Hom.app (𝟙 Z) W).hom u.val = (Scheme.Hom.app (𝟙 Z) W).hom v.val := by
    apply TopCat.Presheaf.section_ext Z.sheaf
    intro x hx
    have hx' : (𝟙 Z) x ∈ W := hx
    have e := congrArg Units.val (h x hx)
    simp only [gm, pullU, dif_pos hx', MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at e
    exact e
  ext1
  exact (ConcreteCategory.bijective_of_isIso (Scheme.Hom.app (𝟙 Z) W)).1 key

private theorem res_res_units' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    res h2 (res h1 u) = res (h2.trans h1) u := by
  ext1
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

private theorem mem_pull_U_of_mem {X S : Scheme.{0}} (M : LB X) (e : S ⟶ X) (x : S) (a : M.ι) (h : e x ∈ M.U a) :
    x ∈ (M.pull e).U (fun _ => a) :=
  Set.mem_iInter.2 fun _ => h

private theorem comm_mul_mul_inv_mul_mul_inv_inv_eq {G : Type*} [CommGroup G] (g g' a a' w : G) :
    g * a * (g' * a')⁻¹ * (g * g'⁻¹ * w)⁻¹ = a * a'⁻¹ * w⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem eq_mul_mul_inv_mul_inv_mul {G : Type*} [CommGroup G] (a b w : G) : a = w * (a * b⁻¹ * w⁻¹) * b := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_iso_normalised : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V V' : S.Opens) (M M' : LB X) (r : (M.pull e).Gen) (r' : (M'.pull e).Gen), e ≫ p = 𝟙 S → ⨆ a, M.U a = p ⁻¹ᵁ V → ⨆ a, M'.U a = p ⁻¹ᵁ V' → r.IsGen → r'.IsGen → LBIso M' M → ∃ w : LB.Iso M' M, w.IsGen ∧ ∀ (x : S) (a : M.ι) (b : M'.ι), e x ∈ M.U a → e x ∈ M'.U b → gm (𝟙 S) x ((M.pull e).U fun _ => a) (r.s fun _ => a) = gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x ((M'.pull e).U fun _ => b) (r'.s fun _ => b) := by
  intro X S p e V V' M M' r r' he hV hV' hr hr' hw
  obtain ⟨w, hw⟩ := hw
  let O : M.ι × M'.ι → S.Opens := fun k =>
    (M.pull e).U (fun _ => k.1) ⊓ (M'.pull e).U (fun _ => k.2) ⊓ e ⁻¹ᵁ (M.U k.1 ⊓ M'.U k.2)
  let c : ∀ k, Γ(S, O k)ˣ := fun k =>
    res (inf_le_left.trans inf_le_left : O k ≤ _) (r.s fun _ => k.1) *
      (res (inf_le_left.trans inf_le_right : O k ≤ _) (r'.s fun _ => k.2))⁻¹ *
      (res (inf_le_right : O k ≤ _) (pullU e (M.U k.1 ⊓ M'.U k.2) (w.s k)))⁻¹

  have hc : ∀ a b x, x ∈ O (a, b) → gm (𝟙 S) x (O (a, b)) (c (a, b)) =
      gm (𝟙 S) x _ (r.s fun _ => a) * (gm (𝟙 S) x _ (r'.s fun _ => b))⁻¹ *
        (gm e x (M.U a ⊓ M'.U b) (w.s (a, b)))⁻¹ := by
    intro a b x hx
    simp only [c]
    rw [map_mul, map_mul, map_inv, map_inv, gm_res_eq_gm (𝟙 S) x _ hx, gm_res_eq_gm (𝟙 S) x _ hx,
      gm_res_eq_gm (𝟙 S) x _ hx]
    refine congrArg (HMul.hMul _) (congrArg Inv.inv ?_)
    exact gm_id_pull e x _ hx.2 _

  have hcomp : ∀ k l, res (inf_le_left : O k ⊓ O l ≤ O k) (c k) = res (inf_le_right : O k ⊓ O l ≤ O l) (c l) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩
    apply units_ext_of_gm_id_eq
    intro x hx
    have hk := hx.1
    have hl := hx.2
    rw [gm_res_eq_gm (𝟙 S) x _ hx, gm_res_eq_gm (𝟙 S) x _ hx, hc a b x hk, hc a' b' x hl,
      pull_gen hr x a a' hk.2.1 hl.2.1, pull_gen hr' x b b' hk.2.2 hl.2.2,
      gm_iso hw e x a a' b b' ⟨hk.2, hl.2⟩]
    exact comm_mul_mul_inv_mul_mul_inv_inv_eq _ _ _ _ _

  obtain ⟨s0, hs0, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf O (⨆ k, O k)
    (fun i => homOfLE (le_iSup O i)) le_rfl (fun i => (c i).val)
    (fun i j => congrArg Units.val (hcomp i j))
  obtain ⟨t0, ht0, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf O (⨆ k, O k)
    (fun i => homOfLE (le_iSup O i)) le_rfl (fun i => (c i).inv)
    (fun i j => congrArg Units.inv (hcomp i j))
  have hst : s0 * t0 = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' S.sheaf O (⨆ k, O k) (fun i => homOfLE (le_iSup O i)) le_rfl
    intro i
    rw [map_mul, map_one, hs0 i, ht0 i]
    exact (c i).val_inv
  have hts : t0 * s0 = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' S.sheaf O (⨆ k, O k) (fun i => homOfLE (le_iSup O i)) le_rfl
    intro i
    rw [map_mul, map_one, hs0 i, ht0 i]
    exact (c i).inv_val
  let c0 : Γ(S, ⨆ k, O k)ˣ := ⟨s0, t0, hst, hts⟩
  have hc0 : ∀ k, res (le_iSup O k) c0 = c k := fun k => Units.ext (hs0 k)

  have hpe : ∀ x, p (e x) = x := fun x => by
    have := congrArg (fun f => f.base x) he
    simpa using this
  have hk : ∀ k : M.ι × M'.ι, (LB.div M M').U k ≤ p ⁻¹ᵁ (⨆ k, O k) := by
    rintro ⟨a, b⟩ y hy
    have h1 : y ∈ ⨆ a, M.U a := TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy.1⟩
    have h2 : y ∈ ⨆ b, M'.U b := TopologicalSpace.Opens.mem_iSup.2 ⟨b, hy.2⟩
    rw [hV] at h1
    rw [hV'] at h2
    have h3 : e (p y) ∈ p ⁻¹ᵁ V := by
      show p (e (p y)) ∈ V
      rw [hpe]
      exact h1
    have h4 : e (p y) ∈ p ⁻¹ᵁ V' := by
      show p (e (p y)) ∈ V'
      rw [hpe]
      exact h2
    rw [← hV] at h3
    rw [← hV'] at h4
    obtain ⟨a', ha'⟩ := TopologicalSpace.Opens.mem_iSup.1 h3
    obtain ⟨b', hb'⟩ := TopologicalSpace.Opens.mem_iSup.1 h4
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨(a', b'), ⟨⟨mem_pull_U_of_mem M e _ a' ha', mem_pull_U_of_mem M' e _ b' hb'⟩, ⟨ha', hb'⟩⟩⟩
  refine ⟨⟨fun k => w.s k * res (hk k) (pullU p _ c0)⟩, ?_, ?_⟩
  · intro i j
    dsimp only
    rw [map_mul, map_mul, hw i j, res_res_units', res_res_units', _root_.mul_assoc]
  · intro x a b hxa hxb
    have hx : x ∈ O (a, b) := ⟨⟨mem_pull_U_of_mem M e x a hxa, mem_pull_U_of_mem M' e x b hxb⟩, ⟨hxa, hxb⟩⟩
    have hxab : e x ∈ M.U a ⊓ M'.U b := ⟨hxa, hxb⟩
    have hx0 : x ∈ ⨆ k, O k := le_iSup O (a, b) hx
    have hz : x ∈ e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k)) := by
      show p (e x) ∈ ⨆ k, O k
      rw [hpe]
      exact hx0
    have hP : gm e x (M.U a ⊓ M'.U b) (res (hk (a, b)) (pullU p _ c0)) = gm (𝟙 S) x (O (a, b)) (c (a, b)) := by
      calc gm e x (M.U a ⊓ M'.U b) (res (hk (a, b)) (pullU p _ c0))
          = gm e x (p ⁻¹ᵁ (⨆ k, O k)) (pullU p _ c0) := gm_res_eq_gm e x (hk (a, b)) hxab _
        _ = gm (𝟙 S) x (e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k))) (pullU e _ (pullU p _ c0)) := (gm_id_pull e x _ hz _).symm
        _ = gm (𝟙 S) x (e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k))) (res le_rfl (pullU e _ (pullU p _ c0))) :=
          (gm_res_eq_gm (𝟙 S) x le_rfl hz _).symm
        _ = gm (e ≫ p) x (⨆ k, O k) c0 := gm_rp₂ e p x _ _ le_rfl hz c0
        _ = gm (𝟙 S) x (⨆ k, O k) c0 := by rw [he]
        _ = gm (𝟙 S) x (O (a, b)) (res (le_iSup O (a, b)) c0) := (gm_res_eq_gm (𝟙 S) x _ hx c0).symm
        _ = gm (𝟙 S) x (O (a, b)) (c (a, b)) := congrArg _ (hc0 (a, b))
    have hw' : gm e x (M.U a ⊓ M'.U b) (w.s (a, b) * res (hk (a, b)) (pullU p _ c0)) =
        gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x (O (a, b)) (c (a, b)) :=
      (map_mul _ _ _).trans (congrArg _ hP)
    refine Eq.trans ?_ (congrArg (· * gm (𝟙 S) x _ (r'.s fun _ => b)) hw'.symm)
    rw [hc a b x hx]
    exact eq_mul_mul_inv_mul_inv_mul _ _ _

end GlobalTheory.BundleNormalise
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem good_pullback : Out.GtBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (_ : SABMap t' t f), Good t → Good t' := by
  intro hB E _ _ _ H X X' t t' f m hg
  obtain ⟨hA, hS, hT⟩ := hg
  obtain ⟨cm, cart, base, act, lin⟩ := m
  have hpb := GlobalTheory.AbLocusPull.abLocus_sections_pull X X' f t.G t'.G cm.F t.semi cart
  refine ⟨hpb.1 hA, GlobalTheory.splitFibres_of_isGrpPullback hB X X' f t.G t'.G cm.F cart hS,
    hpb.2 t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ?_ hT⟩
  obtain ⟨w, hw, -⟩ := lin
  exact ⟨w, hw⟩

end GlobalTheory.Models
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLocus

theorem exists_idempotent {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : u ^ n = 1) :
    ∃ e : R, IsIdempotentElem e ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), φ u = 1 ↔ φ e = 1 := by
  obtain ⟨m, hm⟩ := hn.exists_left_inv
  have h₀ : (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hu, sub_self]
  have h₁ : u * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    linear_combination m * h₀
  have h₂ : ∀ i : ℕ, u ^ i * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    intro i
    induction i with
    | zero => rw [pow_zero, _root_.one_mul]
    | succ i ih => rw [pow_succ, _root_.mul_assoc, h₁, ih]
  refine ⟨m * ∑ i ∈ Finset.range n, u ^ i, ?_, fun R' _ φ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · show _ * _ = _
    rw [_root_.mul_assoc, Finset.sum_mul, Finset.sum_congr rfl fun i _ => h₂ i, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← _root_.mul_assoc, hm, _root_.one_mul]
  · have := congrArg φ hm

    simp only [map_mul, map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    _root_.mul_one, map_natCast, map_one] at this ⊢
    exact this
  · have := congrArg φ h₁
    rwa [map_mul, h, _root_.mul_one] at this

theorem isClosed_basicOpen {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (X.basicOpen e : Set X) := by
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ X.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (X.mem_basicOpen e x trivial).2 h'
      · exact absurd ((X.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

theorem appTop_eq_one_iff {X Y : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) (h : Y ⟶ X) :
    h.appTop.hom e = 1 ↔ Set.range h ⊆ X.basicOpen e := by
  have p : h ⁻¹ᵁ X.basicOpen e = Y.basicOpen (h.appTop.hom e) := Scheme.preimage_basicOpen h e
  constructor
  · rintro H _ ⟨y, rfl⟩
    have : y ∈ h ⁻¹ᵁ X.basicOpen e := by
      rw [p, H, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    exact this
  · intro H
    have hu : IsUnit (h.appTop.hom e) := by
      refine RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace ⊤ _ fun y hy => ?_
      have : y ∈ Y.basicOpen (h.appTop.hom e) := by rw [← p]; exact H ⟨y, rfl⟩
      exact (Y.mem_basicOpen _ y hy).1 this
    exact hu.mul_left_cancel ((he.map h.appTop.hom).eq.trans (_root_.mul_one _).symm)

theorem exists_clopen_eq {X : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤))) {c c₀ : Γ(X, ⊤)ˣ}
    (hc : c ^ n = 1) (hc₀ : c₀ ^ n = 1) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ X),
      Units.map h.appTop.hom.toMonoidHom c = Units.map h.appTop.hom.toMonoidHom c₀ ↔ Set.range h ⊆ U := by
  have hu : (c * c₀⁻¹).val ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hc, hc₀, inv_one, _root_.mul_one, Units.val_one]
  obtain ⟨e, he, H⟩ := exists_idempotent hn hu
  refine ⟨X.basicOpen e, isClosed_basicOpen he, fun Y h => ?_⟩
  rw [← appTop_eq_one_iff he, ← H, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← Units.val_eq_one]
  rfl

theorem pow_eq_one (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A}
    (hx : x ^ k = 1) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ j : ℕ, WeilIs P.A P.L k (x ^ (j + 1)) y (c ^ (j + 1)) := by
    intro j
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c]; exact weilIs_mul_left hG S P k T _ _ _ _ _ ih hc
  have h := hpow k
  rw [pow_succ, hx, _root_.one_mul] at h
  have := CommutatorPairing.weilIs_unique hG P.isAb P.isLB h hc
  rwa [pow_succ, mul_eq_right] at this

theorem exists_clopen_of_weilIs (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) {T : Over S}
    {x y : T ⟶ P.A} {c c₀ : Γ(T.left, ⊤)ˣ} (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1) (hc : c ^ n = 1)
    (h₀ : WeilIs P.A P.L n x y c₀) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by
  obtain ⟨U, hU, H⟩ := exists_clopen_eq hn hc (pow_eq_one hG P n hx h₀)
  refine ⟨U, hU, fun T' h => ?_⟩
  have h₁ := CommPairing.weilIs_pull hG P.isAb P.isLB h h₀
  rw [← H]
  exact ⟨fun h₂ => CommutatorPairing.weilIs_unique hG P.isAb P.isLB h₂ h₁, fun e => e ▸ h₁⟩

theorem exists_clopen_of_lift : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A),
    x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) →
    ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), 0 < n →
      IsUnit (n : Γ(T.left, ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 →
      ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
        WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔
          Set.range h.left ⊆ U := by
  intro hG hl S P n T x y c _ hn hx hy hc
  obtain ⟨c₀, h₀, -⟩ := CommutatorPairing.existsUnique_weilIs hG hl S P n T x y hx hy
  exact exists_clopen_of_weilIs hG P n hn hx hc h₀

theorem exists_clopen_of_isLocallyNoetherian (hL : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ) (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hc : c ^ n = 1) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by
  obtain ⟨c₀, h₀, -⟩ := (hL.weil S P n T).1 x y hx hy
  exact exists_clopen_of_weilIs hL.globalFns P n hn hx hc h₀

end GlobalTheory.PairingLocus
end
