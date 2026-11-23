module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFamGlue

section General

variable {X₁ X₂ Y T : Scheme.{0}} {L : LB X₁} {M : LB X₂} {a : Y ⟶ X₁} {b : Y ⟶ X₂} {K : Type} [Fintype K]

def isoGerm (w : LB.Iso (L.pull a) (M.pull b)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : M.ι) (q : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((M.pull b).U (fun _ => p) ⊓ (L.pull a).U (fun _ => q)) (w.s (fun _ => p, fun _ => q))

theorem isoGerm_trans {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {p p' : M.ι} {q q' : L.ι}
    (hp : b (r z) ∈ M.U p) (hp' : b (r z) ∈ M.U p') (hq : a (r z) ∈ L.U q) (hq' : a (r z) ∈ L.U q') :
    isoGerm w r z p q = gm (r ≫ b) z _ (M.g p p') * (gm (r ≫ a) z _ (L.g q q'))⁻¹ * isoGerm w r z p' q' := by
  have hm : r z ∈ (M.pull b).U (fun _ => p) ⊓ (L.pull a).U (fun _ => q) ⊓
      ((M.pull b).U (fun _ => p') ⊓ (L.pull a).U (fun _ => q')) :=
    ⟨⟨mem_pull.2 hp, mem_pull.2 hq⟩, mem_pull.2 hp', mem_pull.2 hq'⟩
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _)
    (hw (fun _ => p, fun _ => q) (fun _ => p', fun _ => q'))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((gm_div (L.pull a) (M.pull b) r z (fun _ => p, fun _ => q) (fun _ => p', fun _ => q') hm).trans ?_)
      (gm_res r z _ hm _))))
  exact congrArg₂ (· * ·) (gm_pull_g M b r z _ _ hm.1.1 hm.2.1) (congrArg (·⁻¹) (gm_pull_g L a r z _ _ hm.1.2 hm.2.2))

theorem prod_trans {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) (ψ : K → (T ⟶ Y)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {p p' : K → M.ι} {q q' : K → L.ι}
    (hp : r z ∈ LB.wchart M (fun k => ψ k ≫ b) p) (hp' : r z ∈ LB.wchart M (fun k => ψ k ≫ b) p')
    (hq : r z ∈ LB.wchart L (fun k => ψ k ≫ a) q) (hq' : r z ∈ LB.wchart L (fun k => ψ k ≫ a) q') :
    ∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k = trF (fun k => ψ k ≫ b) ε r z p p' *
      (trF (fun k => ψ k ≫ a) ε r z q q')⁻¹ * ∏ k, isoGerm w (r ≫ ψ k) z (p' k) (q' k) ^ ε k := by
  rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [isoGerm_trans hw (r ≫ ψ k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), mul_zpow, mul_zpow, inv_zpow]
  simp only [Category.assoc]

theorem exists_down (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) (ψ : K → (T ⟶ Y))
    (ε : K → ℤ) (σ : LB.Sec (LB.LinComb M (fun k => ψ k ≫ b) ε)) :
    ∃ τ : LB.Sec (LB.LinComb L (fun k => ψ k ≫ a) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (p : K → M.ι) (q : K → L.ι),
      r z ∈ LB.wchart M (fun k => ψ k ≫ b) p → r z ∈ LB.wchart L (fun k => ψ k ≫ a) q →
      (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L (fun k => ψ k ≫ a) q) (τ.f q) =
        gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) := by
  have cov : ∀ y : T, ∃ p, y ∈ LB.wchart M (fun k => ψ k ≫ b) p := fun y => by
    choose I hI using fun k => exists_chart hM ((ψ k ≫ b) y)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  have glue : ∀ q : K → L.ι, ∃ c : Γ(T, LB.wchart L (fun k => ψ k ≫ a) q), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z)
      (p : K → M.ι), r z ∈ LB.wchart M (fun k => ψ k ≫ b) p → r z ∈ LB.wchart L (fun k => ψ k ≫ a) q →
      gs r z _ c = (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k)⁻¹.val *
        gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) := by
    intro q
    let V : (K → M.ι) → T.Opens := fun p => LB.wchart M (fun k => ψ k ≫ b) p ⊓ LB.wchart L (fun k => ψ k ≫ a) q
    have h₃ : ∀ p k, V p ≤ ψ k ⁻¹ᵁ ((M.pull b).U (fun _ => p k) ⊓ (L.pull a).U (fun _ => q k)) := fun p k y hy =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 k), mem_pull.2 (Set.mem_iInter.1 hy.2 k)⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(T, V p), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p, r z ∈ V p →
        gs r z (V p) (u p) = (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k)⁻¹.val *
          gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) :=
      ⟨fun p => (∏ k, res (h₃ p k) (pullU (ψ k) _ (w.s (fun _ => p k, fun _ => q k))) ^ ε k)⁻¹.val *
          (T.presheaf.map (homOfLE (inf_le_left : V p ≤ LB.wchart M (fun k => ψ k ≫ b) p)).op).hom (σ.f p),
        fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) ((map_prod _ _ _).trans
            (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
              ((gm_res r z (h₃ p k) hz _).trans (gm_pull r (ψ k) z _ (h₃ p k hz) _))))))))) (gs_res r z _ hz _))⟩
    obtain ⟨c, hc, -⟩ := T.sheaf.existsUnique_gluing' V (LB.wchart L (fun k => ψ k ≫ a) q)
      (fun p => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨p, hp⟩ := cov y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hp, hy⟩) u
      (fun p p' => fn_ext (V := V p ⊓ V p') fun y hy => by
        refine (gs_res (𝟙 T) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 T) y inf_le_right hy _).symm)
        rw [hu _ _ y p hy.1, hu _ _ y p' hy.2, sec_trans σ (𝟙 T) y hy.1.1 hy.2.1,
          prod_trans hw ψ ε (𝟙 T) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          mul_eq_left.1 (trF_trans hL _ ε (𝟙 T) y hy.1.2 hy.1.2 hy.1.2), ← _root_.mul_assoc, ← Units.val_mul]
        congr 2
        rw [inv_one, _root_.mul_one, mul_inv_rev, inv_mul_cancel_right])
    refine ⟨c, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ V p := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz c).symm.trans ((congrArg (gs r z (V p)) (hc p)).trans (hu Z r z p hz))
  choose c hc using glue
  refine ⟨⟨c, fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z p q hp hq => ?_⟩
  · obtain ⟨p, hp⟩ := cov y
    refine (gs_res (𝟙 T) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 T) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 T) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 T) y q q' hy.1 hy.2)))
      (gs_res (𝟙 T) y _ hy _))).symm)
    refine (hc q _ (𝟙 T) y p hp hy.1).trans (Eq.trans ?_ (congrArg _ (hc q' _ (𝟙 T) y p hp hy.2)).symm)
    rw [prod_trans hw ψ ε (𝟙 T) y hp hp hy.1 hy.2, mul_eq_left.1 (trF_trans hM _ ε (𝟙 T) y hp hp hp),
      ← _root_.mul_assoc, ← Units.val_mul, _root_.one_mul, mul_inv_rev, inv_inv, _root_.mul_comm _⁻¹]
    rfl
  · exact (congrArg _ (hc q Z r z p hp hq)).trans (Units.mul_inv_cancel_left _ _)

def sumSec {N : LB Y} {A : Type} (S : Finset A) (s : A → N.Sec) : N.Sec where
  f i := ∑ x ∈ S, (s x).f i
  compat i j := by

    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (s x).compat i j

theorem sval_sumSec {φ : K → (Y ⟶ X₁)} {ε : K → ℤ} {A : Type} (S : Finset A) (s : A → (LB.LinComb L φ ε).Sec)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (sumSec S s) r z J = ∑ x ∈ S, sval (s x) r z J := DVR.gs_fsum r z _ (hJ.mem φ r) S _

end General

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

theorem formEq_term (a : D.toPre.P.A ⟶ D.toPre.P.A) (b : thickObj R I e G ⟶ thickObj R I e G)
    (hb : b.left ≫ DVR.pGl U e = DVR.pGl U e ≫ a.left) (n j : ℤ) (β : D.toPre.X) :
    FormEq (Sum.elim (fun k => DVR.pGl U e ≫ tφ D.toPre a β k) (DVR.Oφl U e β)) (Sum.elim (tε n j) Oinvε)
      (fun k => (![𝟙 _, b.left] : Fin 2 → _) k ≫ DVR.pGl U e) ![n, j] := by
  intro V _ h
  have a₀ : DVR.pGl U e ≫ tφ D.toPre a β 0 = DVR.pGl U e := Category.comp_id _
  have a₁ : DVR.pGl U e ≫ tφ D.toPre a β 1 = DVR.Oφl U e β 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (DVR.cP D.toPre _ β)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (DVR.comp_cP D.toPre _ β)))
  have a₂ : DVR.pGl U e ≫ tφ D.toPre a β 2 = DVR.Oφl U e β 1 :=
    congrArg (fun z => z.left) (DVR.comp_cP D.toPre (U.gt e).pG β)
  have a₃ : DVR.pGl U e ≫ tφ D.toPre a β 3 = DVR.Oφl U e β 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : DVR.Oφl U e β 2 = DVR.pGl U e := rfl
  have a₅ : DVR.pGl U e ≫ tφ D.toPre a β 4 = b.left ≫ DVR.pGl U e := hb.symm
  have a₆ : (![𝟙 _, b.left] : Fin 2 → _) 0 ≫ DVR.pGl U e = DVR.pGl U e := Category.id_comp _
  have a₇ : (![𝟙 _, b.left] : Fin 2 → _) 1 ≫ DVR.pGl U e = b.left ≫ DVR.pGl U e := rfl
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_four, Fin.prod_univ_two]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, tε, Oinvε, Matrix.cons_val]
  module

theorem exists_texp (a : D.toPre.P.A ⟶ D.toPre.P.A) (b : thickObj R I e G ⟶ thickObj R I e G)
    (hb : b ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) (n j : ℤ) {Ix : Type}
    {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (hs : Small I s) :
    ∃ τ : SecE U b n j, TExp U τ s := by
  classical
  have hb' : b.left ≫ DVR.pGl U e = DVR.pGl U e ≫ a.left := by
    have h₁ : b.left ≫ (U.gt e).q.left = (U.gt e).q.left ≫ ((Over.pullback (thick R I e)).map a).left :=
      congrArg (fun f => f.left) hb
    have h₂ : ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
        pullback.fst D.toPre.P.A.hom (thick R I e) ≫ a.left := pullback.lift_fst _ _ _
    show b.left ≫ (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
      ((U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e)) ≫ a.left
    rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]
  choose σ hσ using fun i => exists_sec D.toPre.P.isLB (formEq_term U e a b hb' n j (w i))
    (pullMulSec (s i) (DVR.pGl U e) (DVR.tG U e (w i)) ((U.gt e).t_gen (w i)))
  obtain ⟨τ₀, h₀⟩ := exists_down U.LG.isLB D.toPre.P.isLB (U.w_gen e) (![𝟙 _, b.left] : Fin 2 → _) ![n, j]
    (sumSec (hs e).toFinset σ)
  obtain ⟨τ, hτ⟩ := exists_sec U.LG.isLB (φ' := ![(fstG I e G).left, b.left ≫ (fstG I e G).left]) (ε' := ![n, j])
    (fun V _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      exact congrArg (fun f => h f ^ n * _) (Category.id_comp _)) τ₀
  refine ⟨τ, fun S hS Z x z J J' hJ hJ' => ?_⟩
  have H := h₀ Z x z _ _ (hJ.mem _ x) (hJ'.mem _ x)
  have van : ∀ i, Van I (s i) e → sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val = 0 :=
    fun i hi => by
      have := hi Z (x ≫ (U.gt e).q.left) z J hJ
      rw [Category.assoc] at this
      exact (congrArg (· * _) this).trans (zero_mul _)
  have H₂ : sval (sumSec (hs e).toFinset σ) x z J =
      ∑ i ∈ S, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val := by
    rw [sval_sumSec _ _ x z hJ]
    refine (Finset.sum_congr rfl fun i _ => (hσ i Z x z J hJ).trans (sval_pullMulSec _ _ _ _ x z hJ)).trans ?_
    refine Finset.sum_subset (fun i hi => by_contra fun h => (hs e).mem_toFinset.1 hi (hS i h)) fun i _ hi => ?_
    exact van i (by_contra fun h => hi ((hs e).mem_toFinset.2 h))
  refine Eq.trans ?_ (H.trans H₂)
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) (hτ Z x z J' hJ')
  rw [Fin.prod_univ_two]
  show _ = DVR.wv U e (x ≫ 𝟙 _) z (J (x ≫ 𝟙 _ ≫ _)) (J' (x ≫ 𝟙 _ ≫ _)) ^ n * _
  rw [Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

end Main

theorem glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), b ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map a → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ τ : SecE U.toUnifPre b n j, TExp U.toUnifPre τ s :=
  fun _ _ _ _ _ _ a _ _ _ _ _ U e b hb n j _ _ s hs => exists_texp U.toUnifPre e a b hb n j s hs

end GlobalTheory.TwFamGlue
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem prod_tφ_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X)
    {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, h (tφ D a β k) ^ tε n j k =
      h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * h ((toUnit D.P.A ≫ D.c β) * 𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (h (toUnit D.P.A ≫ D.c β).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left * h a.left ^ j := by
  rw [Fin.prod_univ_five, _root_.mul_comm (toUnit D.P.A ≫ D.c β)]
  simp only [← zpow_neg_one]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (zpow_one _)) rfl)
    (zpow_one _)) rfl

theorem exists_isProdT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j n' j' : ℤ)
    (β β' : D.X) (f : SecT D a n j β) (g : SecT D a n' j' β') :
    ∃ p : SecT D a (n + n') (j + j') (β + β'), IsProdT f g p := by
  have hadd : toUnit D.P.A ≫ D.c (β + β') = (toUnit D.P.A ≫ D.c β) * (toUnit D.P.A ≫ D.c β') := by
    rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have hu := DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen
    (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := tφ D a (β + β')) (ε' := tε (n + n') (j + j')) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (prod_tφ_eq D a n j β h) (prod_tφ_eq D a n' j' β' h)))
        (prod_cub (toUnit D.P.A ≫ D.c β) (toUnit D.P.A ≫ D.c β') (𝟙 D.P.A) h))).trans ?_
      rw [prod_tφ_eq, hadd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec _ hu))
  refine ⟨p, fun Z x z J hJ => (hp Z x z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val (val_pull hJ _ _ _)))))⟩

theorem exists_prodT_van : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (β β' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β'), ∃ p : SecT D.toPre a n'' j'' (β + β'), IsProdT f g p ∧ ∀ e, (Van (maximalIdeal R) f e ∨ Van (maximalIdeal R) g e) → Van (maximalIdeal R) p e := by
  intro R _ _ _ _ D a n j n' j' n'' j'' hn hj β β' f g
  subst hn hj
  obtain ⟨p, hp⟩ := exists_isProdT D.toPre a n j n' j' β β' f g
  refine ⟨p, hp, fun e he Z x z J hJ => ?_⟩
  rw [hp Z _ z J hJ]
  rcases he with he | he
  · rw [he Z x z J hJ, zero_mul, zero_mul]
  · rw [he Z x z J hJ, mul_zero, zero_mul]

end GlobalTheory.TwFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_mul_of_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β) (p : ∀ q : D.toPre.X × D.toPre.X, SecT D.toPre a n'' j'' (q.1 + q.2)) (τ : SecE U.toUnifPre b n j) (τ' : SecE U.toUnifPre b n' j') (τ'' : SecE U.toUnifPre b n'' j''), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → (∀ q : D.toPre.X × D.toPre.X, IsProdT (f q.1) (g q.2) (p q)) → TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') → TExp U.toUnifPre τ'' (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
  intro R _ _ _ _ D a A G _ _ _ U e b n j n' j' n'' j'' hn hj f g p τ τ' τ'' hf hg hp hτ hτ' hτ''
  classical
  subst hn hj
  intro S hS Z x z J J' hJ hJ'
  have hy : x ≫ (U.gt e).pG.left = (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := by
    simp [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left]
  have vanAt : ∀ {n j : ℤ} {β : D.toPre.X} (s : SecT D.toPre a n j β), Van (maximalIdeal R) s e →
      sval s (x ≫ (U.gt e).pG.left) z J = 0 := fun s hs => by rw [hy]; exact hs Z _ z J hJ
  have h1 : evalE U.toUnifPre τ'' x z J J' = evalE U.toUnifPre τ x z J J' * evalE U.toUnifPre τ' x z J J' := by
    simp only [evalE, zpow_add, Units.val_mul]; rw [hτ'' Z x z J' hJ']; ring
  have hL : ∀ χ χ' : D.toPre.X, x ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (U.gt e).pG)).left =
      (x ≫ (U.gt e).pG.left) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 D.toPre.P.A)) :
        D.toPre.P.A ⟶ G3 D.toPre.P.A).left := by
    intro χ χ'
    rw [Category.assoc, ← Over.comp_left]
    congr 2
    simp [comp_lift]
  have hT : ∀ χ χ' : D.toPre.X, (val ((U.gt e).t (χ + χ')) x z J).val *
      (val D.toPre.cub.t ((x ≫ (U.gt e).pG.left) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 D.toPre.P.A)) :
        D.toPre.P.A ⟶ G3 D.toPre.P.A).left) z J).val =
      (val ((U.gt e).t χ) x z J).val * (val ((U.gt e).t χ') x z J).val := by
    intro χ χ'
    have h := (val_mul hJ _ _ x).symm.trans ((val_corr hJ ((U.gt e).t_mul χ χ') x).trans (val_mul hJ _ _ x))
    have h' := (congrArg (val ((U.gt e).t (χ + χ')) x z J * ·) (val_pull hJ _ _ x)).symm.trans h
    rw [← hL χ χ']
    exact (Units.val_mul _ _).symm.trans ((congrArg Units.val h').trans (Units.val_mul _ _))
  have hSf : ∀ i ∉ (hf e).toFinset, Van (maximalIdeal R) (f i) e := fun i hi =>
    by_contra fun hc => hi ((hf e).mem_toFinset.2 hc)
  have hSg : ∀ i ∉ (hg e).toFinset, Van (maximalIdeal R) (g i) e := fun i hi =>
    by_contra fun hc => hi ((hg e).mem_toFinset.2 hc)
  have ef : evalE U.toUnifPre τ x z J J' = ∑ i ∈ (hf e).toFinset,
      sval (f i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t i) x z J).val := hτ _ hSf Z x z J J' hJ hJ'
  have eg : evalE U.toUnifPre τ' x z J J' = ∑ i ∈ (hg e).toFinset,
      sval (g i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t i) x z J).val := hτ' _ hSg Z x z J J' hJ hJ'
  have hP := fun q => hp q Z (x ≫ (U.gt e).pG.left) z J hJ
  have z₁ : ∀ q ∉ S, sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val = 0 :=
    fun q hq => by rw [vanAt _ (hS q hq), zero_mul]
  have z₂ : ∀ q ∉ (hf e).toFinset ×ˢ (hg e).toFinset,
      sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val = 0 := by
    intro q hq
    rw [Finset.mem_product, not_and_or] at hq
    rw [hP q]
    rcases hq with h | h
    · rw [vanAt _ (hSf _ h), zero_mul, zero_mul, zero_mul]
    · rw [vanAt _ (hSg _ h), mul_zero, zero_mul, zero_mul]
  show _ = ∑ q ∈ S, sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val
  rw [h1, ef, eg, Finset.sum_mul_sum, ← Finset.sum_product',
    Finset.sum_subset (Finset.subset_union_right (s₁ := (hf e).toFinset ×ˢ (hg e).toFinset)) (fun q _ hq => z₁ q hq),
    ← Finset.sum_subset (Finset.subset_union_left (s₂ := S)) (fun q _ hq => z₂ q hq)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hP q]
  linear_combination (-(sval (f q.1) (x ≫ (U.gt e).pG.left) z J * sval (g q.2) (x ≫ (U.gt e).pG.left) z J)) * hT q.1 q.2

end GlobalTheory.TwFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_of_isSum {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β)
    (hs : Small I s) (hF : IsSum I s F) (hτ : TExp U τ s) : TExp U τ (w := id) F := by
  classical
  intro S hS Z x z J J' hJ hJ'
  have h0 : ∀ i ∉ (hs e).toFinset, Van I (s i) e := fun i hi => by
    by_contra h
    exact hi ((hs e).mem_toFinset.2 h)
  have hx : x ≫ (U.gt e).pG.left =
      (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R I e) := (Category.assoc _ _ _).symm
  rw [hτ _ h0 Z x z J J' hJ hJ']
  have hsum : ∀ δ, sval (F δ) (x ≫ (U.gt e).pG.left) z J =
      ∑ i ∈ (hs e).toFinset.filter (fun i => w i = δ), sval (s i) (x ≫ (U.gt e).pG.left) z J := fun δ => by
    rw [hx]
    convert hF e _ h0 δ Z (x ≫ (U.gt e).q.left) z J hJ
  have hvan : ∀ δ ∉ S, sval (F δ) (x ≫ (U.gt e).pG.left) z J = 0 := fun δ hδ => by
    rw [hx]
    exact hS δ hδ Z (x ≫ (U.gt e).q.left) z J hJ
  have key : ∀ T : Finset D.toPre.X, (hs e).toFinset.image w ⊆ T →
      ∑ i ∈ (hs e).toFinset, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val =
      ∑ δ ∈ T, sval (F δ) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t δ) x z J).val := fun T hT => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := T) (fun i hi => hT (Finset.mem_image_of_mem w hi))]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain rfl := (Finset.mem_filter.1 hi).2
    rfl
  rw [key _ (Finset.subset_union_left (s₂ := S))]
  refine (Finset.sum_subset Finset.subset_union_right fun δ _ hδ => ?_).symm
  exact (congrArg (· * _) (hvan δ hδ)).trans (zero_mul _)

theorem texp_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U _ _ _ _ τ _ _ s F hs hF hτ => texp_of_isSum U.toUnifPre τ s F hs hF hτ

end GlobalTheory.TwFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem coord_of_formalEnd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  intro R _ _ _ _ D a a' h h' hE A G _ _ _ U b ⟨hb, _, hq, ht⟩ α u ⟨hu, hu1⟩ e Z x z J hJ
  obtain ⟨t, ht, hi⟩ := ht e
  have := hb e
  have := (U.gt e).q_hom
  obtain ⟨v, hv, vv⟩ := GlobalTheory.gtCoord_end_ratio_descends R (maximalIdeal R) D.toPre e G (U.gt e) (b e) a h' t
    (hb e) ht hi (hq e) α
  have hA : IsAbelianScheme (thickObj R (maximalIdeal R) e D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have key := gen_unique D.toPre.P.isLB (thickObj R (maximalIdeal R) e D.toPre.P.A).hom
    (η[thickObj R (maximalIdeal R) e D.toPre.P.A]).left (Over.w _) (GlobalTheory.globalFns_holds _ _ hA).2 hv
    (DVR.pullGen_isGen _ _ _ _ hu (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)))
    (fun y J hJ => by
      have k := vv _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
          thickObj R (maximalIdeal R) e D.toPre.P.A) = η[thickObj R (maximalIdeal R) e D.toPre.P.A] := by
        simp [Hom.one_def]
      rw [o] at k
      exact k.symm.trans ((hu1 _ (thick R (maximalIdeal R) e) y J hJ).symm.trans
        ((congrArg (fun p => val u p y J)
          (UnitValue.eSec_pullback_fst (thick R (maximalIdeal R) e) D.toPre.P.A).symm).trans
          (val_pull hJ _ _ _).symm)))
  refine (vv Z x z J hJ).trans (congrArg (_ * ·) ((key Z _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)))
  exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.TwFam
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefFibTens

theorem nefFib_pow_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → NefFib A → NefFib ((L.pow n).tens A) := by
  intro k _ X _ p D hX L A n hL hA Z i _ _ κ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp ((L.pow n).tens A).isLB (L.pow n).isLB A.isLB
    (cls_tens (L.pow n).isLB A.isLB _) Z i κ hd, NefHodgeTateAt.topSelf_pow hp L n Z i κ hd]
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)) (hA Z i κ hd)

end GlobalTheory.NefFibTens
end
end
