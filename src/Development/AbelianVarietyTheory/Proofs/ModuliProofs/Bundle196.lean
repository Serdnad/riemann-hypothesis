module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle057
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle195
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectNearGoodPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodReductionOfThetaPointUnits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem LN.ega_holds : GlobalTheory.LN.Ega :=
  GlobalTheory.T.extension_of_abelian_schemes GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type}
    (x : I → (T ⟶ P.A)) (v : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

theorem TObj.HasTh.unit_smul {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (H : t.HasTh x v) {c : R} (hc : IsUnit c) :
    t.HasTh x (c • v) := by
  have h := isThetaPt_unit_mul t.pol N' (T := Over.mk x) _ _ _
    (hc.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) H
  unfold TObj.HasTh
  convert h using 2 with a
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem tmap_of_hasTh_complex : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (t t' : TObj g ((n ^ j) ^ 2) J b (spMap em)) (v : Ix g ((n ^ j) ^ 2) → ℂ) (c : ℂ), c ≠ 0 → t.Shape Mat κ → t'.Shape Mat κ → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) (c • v) → TMap t' t (𝟙 _) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, H⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b em t t' v c hc hs hs' hv hv' => ?_⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id (CommRingCat.of ℂ)
  have hv'' : t'.HasTh (𝟙 _) v := by
    have h := hv'.unit_smul (IsUnit.mk0 c⁻¹ (inv_ne_zero hc))
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  have key : ∀ s : Sp ℂ ⟶ Sp o, s = spMap (RingHom.id ℂ) ≫ spMap em →
      ∀ t t' : TObj g ((n ^ j) ^ 2) J b s, t.Shape Mat κ → t'.Shape Mat κ →
        t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) v → TMap t' t (𝟙 _) := by
    intro s hs t t' h1 h1' h2 h2'
    subst hs
    have hvd : VeryDense (objPrimes b Mat κ em v) := by
      intro q f hq hf
      have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
      subst hq0
      refine ⟨⊥, ⟨ℂ, inferInstance, inferInstance, RingHom.id ℂ, t, ?_, h1, h2⟩, hq, le_rfl, hf⟩
      exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.id ℂ).injective
    obtain ⟨t₀, -, h₀⟩ := H j hj o b ℂ em v hvd
    have m := h₀ ℂ (RingHom.id ℂ) t h1 h2
    have m' := h₀ ℂ (RingHom.id ℂ) t' h1' h2'
    refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t₀ t t').2 _ (𝟙 _) m).2 ?_
    rwa [Category.id_comp]
  exact key _ (by rw [hid, Category.id_comp]) t t' hs hs' hv hv''

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem descend_to_theta_field : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K₀ K : Type) [Field K₀] [Field K] [IsAlgClosed K] (β : o →+* K₀) (e : K₀ →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K₀), s = spMap e ≫ spMap β → t.Shape Mat κ → t.Prim w w' → t.HasTh (𝟙 _) (fun a => e (v a)) → ∃ t₀ : TObj g ((n ^ j) ^ 2) J b (spMap β), TMap t t₀ (spMap e) ∧ t₀.Shape Mat κ ∧ t₀.Prim w w' ∧ t₀.HasTh (𝟙 _) v := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b K₀ K _ _ _ β e s t v hs hsh hpr hth => ?_⟩
  subst hs

  have hdense : VeryDense (objPrimes b Mat κ β v) := by
    intro q f hq hf
    have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
    have hker : RingHom.ker e = q := by
      rw [hq0]; exact (RingHom.injective_iff_ker_eq_bot e).mp e.injective
    exact ⟨q, ⟨K, inferInstance, inferInstance, e, t, hker, hsh, hth⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, hth₀, hu⟩ := hj₀ j hj o b K₀ β v hdense

  have hmap : TMap t t₀ (spMap e) := hu K e t hsh hth
  obtain ⟨-, -, hdesc⟩ := GlobalTheory.shape_prim_pull_and_descend o g ((n ^ j) ^ 2) J b Mat κ w w' _ _ _ _ _ t₀ t hmap
  obtain ⟨hS, hP⟩ := hdesc K₀ rfl inferInstance inferInstance
  exact ⟨t₀, hmap, hS hsh, hP inferInstance hpr, hth₀⟩

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkIso

open PrimCocycle

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

theorem exists_gen_axis {M M' : LB B.left} (hM : M.IsLB) (hM' : M'.IsLB) {T : Over S} (x y : T ⟶ B)
    (h : x = 1 ∨ y = 1) : ∃ t : ((LB.div (abelian₂ B M') (abelian₂ B M)).pull (lift x y).left).Gen, t.IsGen := by
  have key : ∀ {N : LB B.left}, N.IsLB →
      ∃ u : LB.Gen (LB.LinComb N (fun I => (lift x y).left ≫ lamφ B I) lamε), u.IsGen := fun {N} hN => by
    obtain ⟨u, hu, -⟩ := exists_gen hN (φ := PEmpty.elim) (ε := PEmpty.elim)
      (φ' := fun I => (lift x y).left ≫ lamφ B I) (ε' := lamε) (fun U _ g => by
        refine (Fintype.prod_empty _).trans (Eq.symm ((prod_lam x y g).trans ?_))
        rcases h with rfl | rfl
        · rw [_root_.one_mul, mul_right_comm (g y.left), mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
        · rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]) (LB.oneGen N)
      (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)).symm)
    exact ⟨u, hu⟩
  obtain ⟨u, hu⟩ := key hM
  obtain ⟨u', hu'⟩ := key hM'
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullOut M (lamφ B) lamε _ _ fun _ => rfl)
    (chartPullOut M' (lamφ B) lamε _ _ fun _ => rfl) (IsoDescent.lbIso_of_gens hM hM' _ _ _ _ u hu u' hu')
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ _) w hw

theorem exists_gen_tensor {L : LB A.left} {M M' : LB B.left} (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (ψ : A ⟶ B)
    [IsMonHom ψ] (h : LBIso L (M.pull ψ.left)) (h' : LBIso L (M'.pull ψ.left)) :
    ∃ t : ((LB.div (abelian₂ B M') (abelian₂ B M)).pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen := by
  have e : ∀ I, lamφ A I ≫ ψ.left = (ψ ⊗ₘ ψ).left ≫ lamφ B I := fun I =>
    congrArg (fun q => q.left)
      ((psum_hom (MonoidHom.mk' (fun z : A ⊗ A ⟶ A => z ≫ ψ) fun a b => MonObj.mul_comp a b ψ) (x2 A) I.down).trans
        ((congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])).trans
          (psum_hom (preHom (ψ ⊗ₘ ψ)) (x2 B) I.down).symm))
  obtain ⟨v, hv⟩ := h
  obtain ⟨v', hv'⟩ := h'
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullOut M (lamφ B) lamε _ _ e) (chartPullOut M' (lamφ B) lamε _ _ e)
    (LBIso.trans (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hM' _ _)
      (iso_linComb ((isGen_iff v).1 hv) (lamφ A) lamε).symm (iso_linComb ((isGen_iff v').1 hv') (lamφ A) lamε))
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ _) w hw

end GlobalTheory.HkIso

namespace GlobalTheory

open HkIso HeckePoint

theorem exists_objMap_of_isIsog_of_kerSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left), p.Prime → ¬ p ∣ l.M' → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), Set.range z.left ⊆ K → z ^ p ^ 2 = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  intro E _ _ _ H D l p S _ s o o₁ o₂ ψ₁ ψ₂ K hp hpM ⟨⟨hom₁, fin₁, et₁, sur₁, lin₁, bun₁⟩, lev₁⟩
    ⟨⟨hom₂, fin₂, et₂, sur₂, lin₂, bun₂⟩, lev₂⟩ ker₁ ker₂ hK
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab₁ := isAbelianScheme_of_proper o₁.t o₁.proper
  have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, homα, hα, uα⟩ := GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S _ _ _ ψ₁ ψ₂ hab hab₁ inferInstance hom₁ fin₁ et₁ sur₁ hom₂
    fun k _ _ t x hx => (ker₂ k t x).2 ((ker₁ k t x).1 hx)
  obtain ⟨β, -, hβ, -⟩ := GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S _ _ _ ψ₂ ψ₁ hab hab₂ inferInstance hom₂ fin₂ et₂ sur₂ hom₁
    fun k _ _ t x hx => (ker₁ k t x).2 ((ker₂ k t x).1 hx)
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have : Epi ψ₂.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₂ := Over.epi_of_epi_left ψ₂
  have : IsIso α := ⟨β, by rw [← cancel_epi ψ₁, reassoc_of% hα, hβ, Category.comp_id],
    by rw [← cancel_epi ψ₂, reassoc_of% hβ, hα, Category.comp_id]⟩
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have := ((baseKA l).unit (p ^ 2) (pow_pos hp.pos 2)).map
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom)
    rwa [map_natCast] at this
  have i₀ : (lbPow o.t.PP.L (p ^ 2)).IsLB := DVR.linComb_isLB _ o.t.PP.isLB _ _
  have i₁ := pull_isLB o₁.t.PP.isLB (𝟙 _)
  have i₂ := pull_isLB o₂.t.PP.isLB α.left
  have hlam : LBIso (abelian₂ o₁.t.G (o₁.t.PP.L.pull (𝟙 _))) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny S _ _ ψ₁ o₁.t.PP.L _ (p ^ 2) hab hab₁ o₁.t.PP.isLB o₁.ample
      (LB.isLB_div (DVR.linComb_isLB _ i₂ _ _) (DVR.linComb_isLB _ i₁ _ _)) hom₁ fin₁ et₁ sur₁ (pow_pos hp.pos 2) hunit
      (fun k _ _ t x hx => hK k t x ((ker₁ k t x).1 hx))
      (exists_gen_axis i₁ i₂ _ _ (Or.inl rfl)) (exists_gen_axis i₁ i₂ _ _ (Or.inr rfl))
      (exists_gen_tensor i₀ i₁ i₂ ψ₁
        (LBIso.chartPull (chartPullId _) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun _ => by simp) bun₁)
        (LBIso.chartPull (chartPullId _) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun _ => by
          rw [Category.id_comp, ← Over.comp_left, hα]) bun₂))
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso globalFns_holds hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }, congrArg (fun q => q.left) hα⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open GlobalTheory.CechPic

theorem pow_eq_of_map_add {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q)
    (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ) (a : A) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_nsmul, left_eq_mul.1 h]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, hf]

theorem exists_dual_isogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o' : Ob D l s) (ψ : o.t.G ⟶ o'.t.G), p.Prime → ¬ p ∣ l.M' → IsIsog o o' p ψ → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), z ≫ ψ = 1 → z ^ p ^ 2 = 1) → ∃ ψ' : o'.t.G ⟶ o.t.G, ψ ≫ ψ' = 𝟙 o.t.G ^ p ^ 2 ∧ ψ' ≫ ψ = 𝟙 o'.t.G ^ p ^ 2 ∧ IsIsog o' o p ψ' := by
  intro E _ _ _ H D l p S _ s o o' ψ hp _ ⟨⟨hψ, hf, he, hs, hact, hiso⟩, hlev⟩ hker
  have hA : IsAbelianScheme o.t.G := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  have hB : IsAbelianScheme o'.t.G := ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hn : 0 < p ^ 2 := pow_pos hp.pos 2
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((p ^ 2 : ℕ) : Γ(Sp (KA l), ⊤)) := by
      have := ((baseKA l).unit _ hn).map (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom
      rwa [map_natCast] at this
    have := h0.map s.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨m1, m2, m3, m4⟩ := abelianScheme_id_pow_finite_etale_surjective S o.t.G (p ^ 2) hA hu
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨π, hπ, hψπ, -⟩ := GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S o.t.G o'.t.G o.t.G ψ (𝟙 o.t.G ^ p ^ 2) hA hB inferInstance hψ hf he hs m1
    fun k _ _ x z hz => by rw [MonObj.comp_pow, Category.comp_id, hker k x z hz]
  have hepi : Epi ψ.left := Flat.epi_of_flat_of_surjective _
  have canc : ∀ (Y : Over S) (f f' : o'.t.G ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f' := fun Y f f' h =>
    Over.OverMorphism.ext ((cancel_epi ψ.left).1 (congrArg (·.left) h))
  have hπψ : π ≫ ψ = 𝟙 o'.t.G ^ p ^ 2 := canc _ _ _ (by
    rw [← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])
  have hl : ψ.left ≫ π.left = (𝟙 o.t.G ^ p ^ 2).left := congrArg (·.left) hψπ
  have hw : π.left ≫ o.t.G.hom = o'.t.G.hom := Over.w π
  have hsep : IsSeparated π.left := by
    have : IsSeparated (π.left ≫ o.t.G.hom) := by rw [hw]; infer_instance
    exact IsSeparated.of_comp _ o.t.G.hom
  have hlfp : LocallyOfFinitePresentation π.left := by
    have : LocallyOfFinitePresentation (π.left ≫ o.t.G.hom) := by rw [hw]; infer_instance
    exact TangentCrit.locallyOfFinitePresentation_of_comp _ o.t.G.hom
  obtain ⟨hf', he'⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover _ _ _ ψ.left π.left hf he hs
    (hl ▸ m2) (hl ▸ m3) hsep hlfp
  have hs' : Surjective π.left := by
    have : Surjective (ψ.left ≫ π.left) := hl ▸ m4
    exact Surjective.of_comp ψ.left π.left
  have hact' : ∀ a, o'.t.act.act a ≫ π = π ≫ o.t.act.act a := fun a => canc _ _ _ (by
    have := o.t.act.hom a
    rw [← Category.assoc, ← hact, Category.assoc, hψπ, ← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow,
      Category.id_comp, Category.comp_id])
  refine ⟨π, hψπ, hπψ, ⟨hπ, hf', he', hs', hact', ?_⟩, fun p' hp' a => ?_⟩
  · have hL := o.t.PP.isLB
    have hM := o'.t.PP.isLB
    have hΘ : ∃ t : LB.Gen (Theta o.t.G o.t.PP.L), t.IsGen := ⟨o.t.cub.t, o.t.cub.isGen⟩
    have hn' : (lbPow o'.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hM _ _
    have hψm : pull ψ.left (cls _ hM) = (p ^ 2) • cls _ hL := by
      rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
      exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
    have h₁ : (cubeLB o.t.G ![fst o'.t.G o'.t.G ≫ π, snd o'.t.G o'.t.G ≫ π] o.t.PP.L).IsLB :=
      LB.isLB_linComb hL _ _
    have h₂ : (cubeLB o'.t.G ![fst o'.t.G o'.t.G, snd o'.t.G o'.t.G] (lbPow o'.t.PP.L (p ^ 2))).IsLB :=
      LB.isLB_linComb hn' _ _
    have hN := LB.isLB_div h₁ h₂
    have val : ∀ {T : Over S} (x y : T ⟶ o'.t.G), pull (lift x y).left (cls _ hN) =
        lam (cls _ hL) (x ≫ π) (y ≫ π) - (p ^ 2) • lam (cls _ hM) x y := by
      intro T x y
      rw [cls_div h₁ h₂, cls_cube_two hL, cls_cube_two hn', map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, cls_lbPow hM, lam_nsmul]
    have hN0 : cls _ hN = 0 := by
      refine (cls_eq_zero_iff hN).2 (GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny S o.t.G o'.t.G ψ o'.t.PP.L _ (p ^ 2) hA hB hM o'.ample hN hψ hf he hs
        hn hu hker ?_ ?_ ?_)
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        rw [cls_pull hN, val, MonObj.one_comp, lam_one_left, lam_one_left, nsmul_zero, sub_self]
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        rw [cls_pull hN, val, MonObj.one_comp, lam_one_right, lam_one_right, nsmul_zero, sub_self]
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        have e : ψ ⊗ₘ ψ = lift (fst _ _ ≫ ψ) (snd _ _ ≫ ψ) := by ext1 <;> simp
        rw [cls_pull hN, e, val, Category.assoc, Category.assoc, hψπ, MonObj.comp_pow, MonObj.comp_pow,
          Category.comp_id, Category.comp_id, lam_pow_left hL hΘ, lam_pow_right hL hΘ, ← lam_pull, hψm,
          lam_nsmul, sub_self]
    have e : cls _ hL = lam (cls _ hL) (𝟙 _) (o.t.act.act H.w0) :=
      ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 o.t.prim).trans (cls_cube_two hL _ _ _)
    have e' : cls _ hM = lam (cls _ hM) (𝟙 _) (o'.t.act.act H.w0) :=
      ((cls_eq_iff hM (LB.isLB_linComb hM _ _)).2 o'.t.prim).trans (cls_cube_two hM _ _ _)
    have key := val (𝟙 _) (o'.t.act.act H.w0)
    rw [hN0, map_zero, ← e', hact', Category.id_comp, eq_comm, sub_eq_zero] at key
    rw [← cls_eq_iff hn' (pull_isLB hL _), cls_lbPow hM, cls_pull hL, ← key]
    conv_rhs => rw [e, pull_lam, Category.comp_id]
  · have hM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul (HeckePoint.natCast_M_mem l) Submodule.mem_top)
    have h2 : p ^ 2 * (p' * p') ≡ 1 [MOD l.M'] := by
      have := hp'.mul hp'
      rwa [show p * p' * (p * p') = p ^ 2 * (p' * p') by ring] at this
    rw [← (hlev p' hp' (p' • a)).1, ← (hlev p' hp' (p' • a)).2, Category.assoc, Category.assoc, hψπ,
      MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, pow_eq_of_map_add _ o.eta_add,
      pow_eq_of_map_add _ o.etaA_add, smul_smul, smul_smul, _root_.mul_assoc,
      HeckePoint.eq_of_modEq _ o.eta_add hM (h2.of_dvd (Nat.dvd_lcm_left _ _)),
      HeckePoint.eq_of_modEq _ o.etaA_add o.etaA_ker (h2.of_dvd (Nat.dvd_lcm_right _ _)), one_nsmul]
    exact ⟨rfl, rfl⟩

end GlobalTheory.HkFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_thetaObject_near_good_prime : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), DenseP (objPrimes b Mat κ β v) → ∀ q₀ ∈ objPrimes b Mat κ β v, ∃ (f : R) (t : TObj g ((n ^ j) ^ 2) J b (spMap ((algebraMap R (Localization.Away f)).comp β))), f ∉ q₀ ∧ t.HasTh (𝟙 _) (fun a => (algebraMap R (Localization.Away f)) (v a)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : (Localization.Away f) →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap ((algebraMap R (Localization.Away f)).comp β))), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x ((algebraMap R (Localization.Away f)) (v a))) → TMap t' t (spMap x) := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_tObj_near | exact GlobalTheory.ZM.NearBuild.exists_tObj_near | (intros; apply GlobalTheory.ZM.NearBuild.exists_tObj_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.goodReduction_of_thetaPoint_units : Out.Laws → Out.Laws2 → GlobalTheory.SS.SemistablePol → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → ∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a)) := by
  first | exact @GlobalTheory.ThetaCrit.good_reduction_of_theta_point | exact GlobalTheory.ThetaCrit.good_reduction_of_theta_point | (intros; apply GlobalTheory.ThetaCrit.good_reduction_of_theta_point <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.descend_to_thetaConstant_field : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K₀ K : Type) [Field K₀] [Field K] [IsAlgClosed K] (β : o →+* K₀) (e : K₀ →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K₀), s = spMap e ≫ spMap β → t.Shape Mat κ → t.Prim w w' → t.HasTh (𝟙 _) (fun a => e (v a)) → ∃ t₀ : TObj g ((n ^ j) ^ 2) J b (spMap β), TMap t t₀ (spMap e) ∧ t₀.Shape Mat κ ∧ t₀.Prim w w' ∧ t₀.HasTh (𝟙 _) v := by
  first | exact @GlobalTheory.ZM.descend_to_theta_field | exact GlobalTheory.ZM.descend_to_theta_field | (intros; apply GlobalTheory.ZM.descend_to_theta_field <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaPoint_determines_shape_complex : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (t t' : TObj g ((n ^ j) ^ 2) J b (spMap em)) (v : Ix g ((n ^ j) ^ 2) → ℂ) (c : ℂ), c ≠ 0 → t.Shape Mat κ → t'.Shape Mat κ → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) (c • v) → TMap t' t (𝟙 _) := by
  first | exact @GlobalTheory.ZM.tmap_of_hasTh_complex | exact GlobalTheory.ZM.tmap_of_hasTh_complex | (intros; apply GlobalTheory.ZM.tmap_of_hasTh_complex <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left), p.Prime → ¬ p ∣ l.M' → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), Set.range z.left ⊆ K → z ^ p ^ 2 = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  first | exact @GlobalTheory.exists_objMap_of_isIsog_of_kerSet | exact GlobalTheory.exists_objMap_of_isIsog_of_kerSet | (intros; apply GlobalTheory.exists_objMap_of_isIsog_of_kerSet <;> assumption)

end
end
