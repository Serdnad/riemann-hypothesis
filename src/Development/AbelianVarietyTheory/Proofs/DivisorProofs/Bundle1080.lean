module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle107
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle099
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle061
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
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
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle004
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPic

open TopologicalSpace

theorem exists_unit_lift_of_surj_closedImm {X X₀ : Scheme.{0}} (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i]
    (W : X.Opens) (hW : IsAffineOpen W) (u : Γ(X₀, i ⁻¹ᵁ W)ˣ) : ∃ s : Γ(X, W)ˣ, pullU i W s = u := by
  obtain ⟨v, hv⟩ := i.app_surjective W hW u.val
  have hunit : IsUnit v := X.toRingedSpace.isUnit_of_isUnit_germ W v fun x hx => by
    obtain ⟨y, rfl⟩ := Surjective.surj (f := i) x
    have h1 : IsUnit ((i.stalkMap y).hom ((X.presheaf.germ W (i y) hx).hom v)) := by
      rw [Scheme.Hom.germ_stalkMap_apply, hv]; exact u.isUnit.map _
    exact isUnit_of_map_unit _ _ h1
  exact ⟨hunit.unit, Units.ext hv⟩

theorem mul_twist_eq_of_cocycle {G : Type*} [CommGroup G] (A B C E F S T : G) (h1 : A * B = F) (h2 : C * E = F) :
    A * S = C * (S⁻¹ * B * T)⁻¹ * (E * T) := by
  rw [eq_mul_inv_of_mul_eq h1, eq_mul_inv_of_mul_eq h2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_cocycle_one_on_thickening : ∀ (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i]
    (c : Pic X), GlobalTheory.CechPic.pull i c = 0 →
    ∃ (D : LB X) (hD : D.IsLB), cls D hD = c ∧ ∀ a b, pullU i _ (D.g a b) = 1 := by
  intro X X₀ i _ _ c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  rw [← cls_pull hL i (pull_isLB hL i)] at hc
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hc
  let ι' := {q : X.affineOpens × L.ι // (q.1 : X.Opens) ≤ L.U q.2}
  let W : ι' → X.Opens := fun q => q.1.1
  let J : ι' → L.ι := fun q => q.1.2
  have hle : ∀ q : ι', i ⁻¹ᵁ W q ≤ (L.pull i).U (fun _ => J q) := fun q y hy => mem_pull.2 (q.2 hy)
  choose s hs using fun q : ι' =>
    exists_unit_lift_of_surj_closedImm i (W q) q.1.1.2 (res (hle q) (t.s (fun _ => J q)))
  have l1 : ∀ q q' : ι', W q ⊓ W q' ≤ L.U (J q) ⊓ L.U (J q') := fun q q' => inf_le_inf q.2 q'.2
  let gg : ∀ q q' : ι', Γ(X, W q ⊓ W q')ˣ := fun q q' =>
    (res inf_le_left (s q))⁻¹ * res (l1 q q') (L.g (J q) (J q')) * res inf_le_right (s q')
  let D : LB X := ⟨ι', W, gg⟩
  have gD : ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (q q' : ι'), f y ∈ W q → f y ∈ W q' →
      gm f y (W q ⊓ W q') (D.g q q') =
        (gm f y (W q) (s q))⁻¹ * gm f y (L.U (J q) ⊓ L.U (J q')) (L.g (J q) (J q')) * gm f y (W q') (s q') := by
    intro Y f y q q' h h'
    have hm : f y ∈ W q ⊓ W q' := ⟨h, h'⟩
    show gm f y _ ((res _ (s q))⁻¹ * res _ (L.g (J q) (J q')) * res _ (s q')) = _
    rw [map_mul, map_mul, map_inv, gm_res f y _ hm, gm_res f y _ hm, gm_res f y _ hm]
  have hD : D.IsLB := {
    cover := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨j, hj⟩ := exists_chart hL x
      obtain ⟨V, hV, hxV, hVle⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hj
      exact Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, j), hVle⟩, hxV⟩
    g_self := fun q => unit_ext fun y hy => by
      rw [gm_res _ y _ hy, gD X (𝟙 X) y q q hy hy, gm_self hL (𝟙 X) y (q.2 hy), map_one]
      group
    cocycle := fun a b c => unit_ext fun y hy => by
      have ha : y ∈ W a := hy.1.1
      have hb : y ∈ W b := hy.1.2
      have hc : y ∈ W c := hy.2
      rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gD X (𝟙 X) y a b ha hb,
        gD X (𝟙 X) y b c hb hc, gD X (𝟙 X) y a c ha hc,
        ← gm_cocycle hL (𝟙 X) y (a.2 ha) (b.2 hb) (c.2 hc)]
      group
      rfl }
  refine ⟨D, hD, ?_, fun a b => ?_⟩
  · refine (cls_eq_iff hD hL).2 ⟨⟨fun p => res (le_inf inf_le_left (inf_le_right.trans p.2.2) :
        L.U p.1 ⊓ W p.2 ≤ L.U p.1 ⊓ L.U (J p.2)) (L.g p.1 (J p.2)) * res inf_le_right (s p.2)⟩, ?_⟩
    refine (isGen_iff_germ _).2 fun y p p' hp hp' => ?_
    have val : ∀ p : L.ι × ι', y ∈ L.U p.1 ⊓ W p.2 → gm (𝟙 X) y (L.U p.1 ⊓ W p.2)
        (res (le_inf inf_le_left (inf_le_right.trans p.2.2) : L.U p.1 ⊓ W p.2 ≤ L.U p.1 ⊓ L.U (J p.2))
          (L.g p.1 (J p.2)) * res inf_le_right (s p.2)) =
        gm (𝟙 X) y _ (L.g p.1 (J p.2)) * gm (𝟙 X) y (W p.2) (s p.2) := fun p h => by
      rw [map_mul, gm_res _ y _ h, gm_res _ y _ h]
    show gm (𝟙 X) y (L.U p.1 ⊓ W p.2) _ = gm (𝟙 X) y (L.U p.1 ⊓ W p.2 ⊓ (L.U p'.1 ⊓ W p'.2)) ((LB.div L D).g p p') *
      gm (𝟙 X) y (L.U p'.1 ⊓ W p'.2) _
    dsimp only
    erw [val p hp, val p' hp', gm_div D L (𝟙 X) y p p' ⟨hp, hp'⟩, gD X (𝟙 X) y p.2 p'.2 hp.2 hp'.2]
    exact mul_twist_eq_of_cocycle _ _ _ _ _ _ _ (gm_cocycle hL (𝟙 X) y hp.1 (p.2.2 hp.2) (p'.2.2 hp'.2))
      (gm_cocycle hL (𝟙 X) y hp.1 hp'.1 (p'.2.2 hp'.2))
  · apply unit_ext
    intro y hy
    have hsa : ∀ q : ι', i y ∈ W q → gm i y (W q) (s q) = gm (𝟙 X₀) y _ (t.s (fun _ => J q)) := fun q h => by
      have e := gm_pull (𝟙 X₀) i y (W q) h (s q)
      rw [Category.id_comp] at e
      rw [← e, hs q, gm_res (𝟙 X₀) y (hle q) h]
    have ha : i y ∈ W a := hy.1
    have hb : i y ∈ W b := hy.2
    have eg := gm_pull_g L i (𝟙 X₀) y (fun _ => J a) (fun _ => J b) (hle a ha) (hle b hb)
    rw [Category.id_comp] at eg
    have e := gm_pull (𝟙 X₀) i y (W a ⊓ W b) hy (D.g a b)
    rw [Category.id_comp] at e
    rw [e, gD X₀ i y a b ha hb, map_one, hsa a ha, hsa b hb, ← eg,
      (isGen_iff_germ t).1 ht y _ _ (hle a ha) (hle b hb)]
    group

end GlobalTheory.CechPic
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ d : Pic Y, (∀ i, GlobalTheory.CechPic.pull (f i) d = 0) → d = 0 := by
  first | exact @GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero | exact GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero | (intros; apply GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_appLE_ι {Z : Scheme.{0}} (O W : Z.Opens) (hW : W ≤ O) (W' : O.toScheme.Opens)
    (h : W' = O.ι ⁻¹ᵁ W) : Function.Bijective (O.ι.appLE W W' h.le) := by
  subst h
  have : IsIso (O.ι.app W) := Scheme.Hom.isIso_app _ _ (by simpa using hW)
  rw [← Scheme.Hom.app_eq_appLE]
  exact ConcreteCategory.bijective_of_isIso _

theorem eq_zero_of_pull_eq_zero : ∀ (T Z : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : Z ⟶ T) (O : Z.Opens) (e : T ⟶ O.toScheme), Smooth (O.ι ≫ p) → GeometricallyIntegral (O.ι ≫ p) → e ≫ O.ι ≫ p = 𝟙 _ → O ⊔ p ⁻¹ᵁ U = ⊤ → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull (p ⁻¹ᵁ U).ι c = 0 → c = 0 := by
  intro T Z _ _ hT U hU p O e hs hg he hcov
  refine GlobalTheory.T.cechPicard_eq_zero_of_twoOpen_cover_units_split Z O (p ⁻¹ᵁ U) hcov fun F => ?_
  have h1 : (O.ι ≫ p) ⁻¹ᵁ U = O.ι ⁻¹ᵁ (O ⊓ p ⁻¹ᵁ U) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq, Scheme.Hom.comp_preimage]
  have h2 : (⊤ : O.toScheme.Opens) = O.ι ⁻¹ᵁ O := by simp
  have b1 := bijective_appLE_ι O (O ⊓ p ⁻¹ᵁ U) inf_le_left _ h1
  have b2 := bijective_appLE_ι O O le_rfl _ h2
  obtain ⟨G, w, hGw⟩ := GlobalTheory.T.unit_above_dense_open_eq_global_mul_pullback T O hT U hU (O.ι ≫ p) e hs hg he
    (Units.map (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom.toMonoidHom F)
  let ε := RingEquiv.ofBijective (O.ι.appLE O ⊤ h2.le).hom b2
  refine ⟨Units.map ε.symm.toMonoidHom G, pullU p U w, ?_⟩
  apply Units.ext
  apply b1.1
  have hv := congrArg Units.val hGw
  have hG : (O.ι.appLE O ⊤ h2.le).hom (ε.symm G) = G := ε.apply_symm_apply _
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F =
    O.toScheme.presheaf.map (homOfLE le_top).op (G : Γ(O, ⊤)) * (O.ι ≫ p).app U (w : Γ(T, U)) at hv
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F = (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom
    (Z.presheaf.map (homOfLE inf_le_left).op (ε.symm G) *
      Z.presheaf.map (homOfLE inf_le_right).op (p.app U (w : Γ(T, U))))
  rw [hv, map_mul, ← hG]
  congr 1
  · rw [hG]
    conv_lhs => rw [← hG]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.PicGlue
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandOfCapelli

open Finset Polynomial
open GlobalTheory.Dec (gelfVal)

theorem main_succ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (F : Fin (m+1) → Fin (m+1) → A)
    (χ : Fin (m+1) → ℂ) (hF : GlRel F)
    (hq : ∀ w : ℂ, qdet F w = algebraMap ℂ A ((GlobalTheory.CapelliNewton.capQ m χ).eval w)) (N : ℕ) :
    etr F N = algebraMap ℂ A (gelfVal χ N) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  set Q := GlobalTheory.CapelliNewton.capQ m χ with hQ
  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
      qminor F (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m F (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow F (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
      qminor F (Fin.succAbove j) (Fin.succAbove i) w * epow F (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  let Rp : ℂ[X] := ∑ d ∈ range (m + 1), C (φ (Rc d)) * X ^ d
  have hRp : ∀ w : ℂ, φ (∑ d ∈ range (m + 1), w ^ d • Rc d) = Rp.eval w := by
    intro w

    simp only [Rp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_smul, smul_eq_mul]
    exact sum_congr rfl fun d _ => mul_comm _ _
  have hRpdeg : Rp.natDegree ≤ m := natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hφa : ∀ c : ℂ, φ (algebraMap ℂ A c) = c * φ 1 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (Q.eval (w + 1) - Q.eval w) * φ 1 + (-1) ^ N * Rp.eval w
      = Q.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k) := by
    intro w
    have h1 := congrArg φ (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m F hF w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    simp only [hq, ← Algebra.smul_def, map_add (f := _), map_smul, smul_eq_mul, hRp] at h1

    simp only [mul_sum, map_sum, map_smul, map_sub, smul_eq_mul, hφa] at h1
    rw [mul_sum]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m N χ
  let S : ℂ[X] := ∑ k ∈ range (N + 1),
    C ((-1) ^ k * (φ (etr F k) - gelfVal χ k * φ 1)) * (X - C (m : ℂ)) ^ (N - k)
  have hSe : ∀ w : ℂ, S.eval w = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * φ (etr F k))
      - φ 1 * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k := by
    intro w
    simp only [S, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hQS : Q * S = C ((-1) ^ N) * Rp + C (φ 1) * rs := by
    refine Polynomial.funext fun w => ?_
    have h2 := hrsE w
    rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (w + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ w, ← hQ] at h2
    simp only [eval_mul, eval_add, eval_C, hSe]
    linear_combination -hrec w + φ 1 * h2
  have hS0 : S = 0 := by
    by_contra hne
    have hd := (GlobalTheory.CapelliNewton.capQ_monic m χ).natDegree_mul' hne
    rw [← hQ, hQS, GlobalTheory.CapelliNewton.capQ_natDegree] at hd
    have hle : (C ((-1 : ℂ) ^ N) * Rp + C (φ 1) * rs).natDegree ≤ m :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hRpdeg)
        ((natDegree_C_mul_le _ _).trans hrs))
    omega
  have h0 := congrArg (eval (m : ℂ)) hS0
  simp only [S, eval_zero, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self] at h0
  rw [sum_eq_single N (fun b hb hbN => by
      rw [zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hb)) hbN)), mul_zero])
    (fun h => absurd (self_mem_range_succ N) h)] at h0
  rw [Nat.sub_self, pow_zero, mul_one] at h0
  have hne : ((-1 : ℂ)) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [map_sub, hφa]
  exact mul_left_cancel₀ hne (by linear_combination h0)

theorem gelfand_of_capelli : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (F : Fin n → Fin n → A) (χ : Fin n → ℂ),
    GlRel F → (∀ u : ℂ, qdet F (u + ((n : ℂ) - 1) / 2) = algebraMap ℂ A (∏ s, (u + χ s))) →
    ∀ k : ℕ, etr F (k + 1) = algebraMap ℂ A (GlobalTheory.Dec.gelfVal χ (k + 1)) := by
  intro A _ _ n F χ hF hq k
  cases n with
  | zero => simp [etr, gelfVal]
  | succ m =>
    refine main_succ A m F χ hF (fun w => ?_) (k + 1)
    calc qdet F w = qdet F ((w - (m : ℂ) / 2) + (((m + 1 : ℕ) : ℂ) - 1) / 2) := by congr 1; push_cast; ring
      _ = algebraMap ℂ A (∏ s, ((w - (m : ℂ) / 2) + χ s)) := hq _
      _ = _ := by rw [GlobalTheory.CapelliNewton.capQ_eval]

end GlobalTheory.GelfandOfCapelli
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandInj

open Finset Polynomial

theorem capQ_eq_prod (m : ℕ) (χ : Fin (m+1) → ℂ) :
    GlobalTheory.CapelliNewton.capQ m χ
      = (((Multiset.map χ Finset.univ.val).map (fun a => ((m : ℂ) / 2 - a))).map (fun a => X - C a)).prod := by
  unfold GlobalTheory.CapelliNewton.capQ
  rw [Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, map_sub]
  ring

theorem capQ_roots (m : ℕ) (χ : Fin (m+1) → ℂ) :
    (GlobalTheory.CapelliNewton.capQ m χ).roots = (Multiset.map χ Finset.univ.val).map (fun a => ((m : ℂ) / 2 - a)) := by
  rw [capQ_eq_prod, Polynomial.roots_multiset_prod_X_sub_C]

theorem gelfVal_multiset_eq : ∀ (n : ℕ) (χ χ' : Fin n → ℂ), (∀ k : ℕ, GlobalTheory.Dec.gelfVal χ (k + 1) = GlobalTheory.Dec.gelfVal χ' (k + 1)) → Multiset.map χ Finset.univ.val = Multiset.map χ' Finset.univ.val := by
  intro n χ χ' h
  cases n with
  | zero => simp
  | succ m =>
    have hall : ∀ k, GlobalTheory.Dec.gelfVal χ k = GlobalTheory.Dec.gelfVal χ' k := by
      intro k
      cases k with
      | zero => rw [GlobalTheory.CapelliNewton.gelfVal_zero, GlobalTheory.CapelliNewton.gelfVal_zero]
      | succ k => exact h k
    have hgv : GlobalTheory.Dec.gelfVal χ = GlobalTheory.Dec.gelfVal χ' := funext hall
    obtain ⟨r, hr, hrE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m (m + 1) χ
    obtain ⟨r', hr', hrE'⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m (m + 1) χ'
    have hf := GlobalTheory.T.poly_eq_zero_of_newton_recursion m (m + 1) (GlobalTheory.Dec.gelfVal χ)
      (GlobalTheory.CapelliNewton.capQ m χ - GlobalTheory.CapelliNewton.capQ m χ') (r - r')
      (Nat.lt_succ_self m) (GlobalTheory.CapelliNewton.gelfVal_zero m χ) ?_ ?_ ?_
    · have hQ : GlobalTheory.CapelliNewton.capQ m χ = GlobalTheory.CapelliNewton.capQ m χ' := sub_eq_zero.mp hf
      have hroots := congrArg Polynomial.roots hQ
      rw [capQ_roots, capQ_roots] at hroots
      exact Multiset.map_injective (fun a b hab => by simpa using hab) hroots
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_sub]
      rcases Nat.lt_or_ge (m + 1) k with hlt | hge
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [GlobalTheory.CapelliNewton.capQ_natDegree]; exact hlt),
          coeff_eq_zero_of_natDegree_lt (by rw [GlobalTheory.CapelliNewton.capQ_natDegree]; exact hlt), sub_zero]
      · have hk' : k = m + 1 := le_antisymm hge hk
        subst hk'
        have h1 := (GlobalTheory.CapelliNewton.capQ_monic m χ).coeff_natDegree
        have h2 := (GlobalTheory.CapelliNewton.capQ_monic m χ').coeff_natDegree
        rw [GlobalTheory.CapelliNewton.capQ_natDegree] at h1 h2
        rw [h1, h2, sub_self]
    · exact (natDegree_sub_le _ _).trans (max_le hr hr')
    · intro u
      have h1 := hrE u
      have h2 := hrE' u
      rw [← hgv] at h2
      rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (u + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ u] at h1
      rw [← GlobalTheory.CapelliNewton.capQ_eval m χ' (u + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ' u] at h2
      simp only [eval_sub]
      linear_combination h1 - h2

end GlobalTheory.GelfandInj
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPrim

variable {R : Type} [CommRing R]

theorem pullOver_one_eq_zero {Y A : Over (Sp R)} [GrpObj A] (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (1 : Y ⟶ A) c = 0 := by
  haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
  rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]

theorem pullOver_id_apply {A : Over (Sp R)} (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := IsMor.pullCohomologyOne_id _ _

theorem allPrim_of_free (H : GlobalTheory.Published.AbelianDeRhamFree) {A : Over (Sp R)} [GrpObj A] {g : ℕ}
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  obtain ⟨f1, p1, r1, -⟩ := H R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := H R (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (GlobalTheory.AbDual.smooth_prod hg hg)
  let r : FirstDeRham ((A ⊗ A).hom ≫ 𝟙 _) →ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) × FirstDeRham (A.hom ≫ 𝟙 _) :=
    (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1)).prod (pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)))
  have hv : ∀ x, r x =
      (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1) x, pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)) x) :=
    fun _ ↦ rfl
  have hr : ∀ a b,
      r (pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b) = (a, b) := by
    intro a b
    rw [hv]
    simp only [map_add (f := _), pullOver_pullOver, lift_fst, lift_snd, pullOver_one_eq_zero,
      pullOver_id_apply, add_zero, zero_add]
  have hs : Function.Surjective r := fun x ↦ ⟨_, hr x.1 x.2⟩
  have hb : Function.Bijective r :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hs fun m _ ↦ by
      rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring
  refine eq_top_iff.2 fun c _ ↦ (mem_prim_iff _ _ A c).2 (hb.1 ?_)
  rw [hr, hv]
  simp only [pullOver_pullOver, ← Hom.mul_def, _root_.mul_one, _root_.one_mul, pullOver_id_apply]

theorem abelianDeRham_free (H : GlobalTheory.Published.AbelianDeRhamFree) : GlobalTheory.Published.AbelianDeRham.Free :=
  fun R _ A _ g hA hg ↦ ⟨allPrim_of_free H hA hg, H R A g hA hg⟩

end GlobalTheory.AbelianPrim
end
end

section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

theorem _root_.GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n), (∀ m ∈ (ten fun τ => extremal K n (lam τ) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) ∧ ∀ G ∈ VV K lam, (∀ m ∈ G.support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∃ c : K, G = c • ten fun τ => extremal K n (lam τ) := by
  first | exact @GlobalTheory.CoefWtLine.weight_line | exact GlobalTheory.CoefWtLine.weight_line | (intros; apply GlobalTheory.CoefWtLine.weight_line <;> assumption)
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.derivAtZero_reindex_eq_taylor_coefficient : ∀ (D : D7) (ι : Type) [Fintype ι] (e : ι ≃ D.what₂.Tau) (a b : ℕ) (F : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ F → ∀ m : DVar ι a b →₀ ℕ, derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D F (Finsupp.equivMapDomain (e.prodCongr (Equiv.refl (Fin b × Fin a))) m) := by
  first | exact @GlobalTheory.DerivReindex.derivAt0_reindex | exact GlobalTheory.DerivReindex.derivAt0_reindex | (intros; apply GlobalTheory.DerivReindex.derivAt0_reindex <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.jet_finset_linear_combination : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → VCx ι a b → ℂ), (∀ x ∈ R, Differentiable ℂ (F x)) → ∀ m, jetC cD (fun z => ∑ x ∈ R, c x * F x z) m = ∑ x ∈ R, c x * jetC cD (F x) m := by
  first | exact @GlobalTheory.ColNorms.jetC_sum_mul | exact GlobalTheory.ColNorms.jetC_sum_mul | (intros; apply GlobalTheory.ColNorms.jetC_sum_mul <;> assumption)
end
