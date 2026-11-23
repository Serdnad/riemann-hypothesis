module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem isDiagEnd_pullback : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (ψ : P'.A.left ⟶ P.A.left)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P u ε → IsGrpPullback P'.A P.A f ψ →
    LBIso P'.L (P.L.pull ψ) → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A),
      IsDiagEnd F W P' (f ≫ u) ε' ∧ ∀ E, (ε' E).left ≫ ψ = ψ ≫ (ε E).left := by
  intro g n F W T T' P P' u f φ ε hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩ := hS
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n _ (zetaAway n) T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c
    (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  have hbun' : LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)) := by
    let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
    let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
    let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
    have l0 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
    have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε
    have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε).IsLB :=
      ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε
    have l3 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
    have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
    have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
    have i3 : LBIso ((LB.LinComb c.P q ε).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      LBIso.chartPull (chartPullOut c.P q ε φ _ fun _ => rfl) (chartPullId _) refl1
    have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb (c.P.pull ψ₂) q' ε) :=
      LBIso.chartPull (chartPullId _)
        (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
    have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε) (LB.LinComb c'.P q' ε) :=
      GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε
    have h1 := pull_isLB P.isLB φ
    have h2 := pull_isLB l0 φ
    exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))

  have wε : ∀ E, (φ ≫ (ε E).left) ≫ P.A.hom = P'.A.hom ≫ f := fun E => by
    rw [Category.assoc, Over.w, hφp.w]
  let ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A) := fun E =>
    Over.homMk (hφp.lift (φ ≫ (ε E).left) P'.A.hom (wε E)) (hφp.lift_snd _ _ _)
  have hε'φ : ∀ E, (ε' E).left ≫ φ = φ ≫ (ε E).left := fun E => hφp.lift_fst _ _ _
  let U : Over.mk (P'.A.hom ≫ f) ⟶ P.A := pushPt hφ.1.w (𝟙 P'.A)
  have hUl : U.left = φ := by
    simp [U, pushPt]
  have hpushε : ∀ E, pushPt hφ.1.w (ε' E) = U ≫ ε E := fun E => Over.OverMorphism.ext (by
    show (ε' E).left ≫ φ = U.left ≫ (ε E).left
    rw [hUl, hε'φ])
  have hpushpr : ∀ b, pushPt hψ.1.w (pr' b) = U ≫ pr b := fun b => by
    rw [← push_comp]; simp
  refine ⟨ε', ⟨c', hc'u, pr', hmon, huniv', hbun', fun E a => injψ ?_⟩, hε'φ⟩
  rw [push_comp, hpushε, Category.assoc, hdiag E a]
  change preHom (G := c.A) U _ = pushHom hψ P'.A _
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply, map_zpow]
  congr 1
  exact (hpushpr b).symm

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.TensGen

theorem exists_flat {X X' Y : Scheme.{0}} (M : LB X) {I K : Type} [Fintype I] [Fintype K] (F : I → (X' ⟶ X))
    (e : I → ℤ) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => ε p.1 * e p.2))) (ht : t.IsGen) :
    ∃ t₂ : LB.Gen (LB.LinComb (LB.LinComb M F e) φ' ε), t₂.IsGen ∧
      ∀ (jj : K → I → M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart (LB.LinComb M F e) φ' jj →
        gm r z _ (t₂.s jj) = gm r z (LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2))
          (t.s (fun p => jj p.1 p.2)) := by
  have le : ∀ jj : K → I → M.ι, LB.wchart (LB.LinComb M F e) φ' jj ≤
      LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2) := fun jj y hy =>
    Set.mem_iInter.2 fun p => by
      have h₁ : (F p.2) ((φ' p.1) y) ∈ M.U (jj p.1 p.2) := Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
      exact h₁
  have v : ∀ (jj : K → I → M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart (LB.LinComb M F e) φ' jj →
      gm r z _ (res (le jj) (t.s (fun p => jj p.1 p.2))) =
        gm r z (LB.wchart M (fun p : K × I => φ' p.1 ≫ F p.2) (fun p => jj p.1 p.2)) (t.s (fun p => jj p.1 p.2)) :=
    fun jj Z r z hz => gm_res r z _ hz _
  refine ⟨⟨fun jj => res (le jj) (t.s (fun p => jj p.1 p.2))⟩, fun i j => unit_ext fun y hy => ?_, v⟩
  rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
  change gm (𝟙 Y) y _ (res (le i) _) = _ * gm (𝟙 Y) y _ (res (le j) _)
  rw [v i _ (𝟙 Y) y hy.1, v j _ (𝟙 Y) y hy.2, gen_trans ht (𝟙 Y) y (le i hy.1) (le j hy.2)]
  congr 1
  refine Eq.trans ?_ (gm_linComb (LB.LinComb M F e) φ' ε (𝟙 Y) y i j hy.1 hy.2).symm
  have b : ∀ a, gm (𝟙 Y ≫ φ' a) y ((LB.LinComb M F e).U (i a) ⊓ (LB.LinComb M F e).U (j a))
      ((LB.LinComb M F e).g (i a) (j a)) = ∏ k, gm ((𝟙 Y ≫ φ' a) ≫ F k) y (M.U (i a k) ⊓ M.U (j a k)) (M.g (i a k) (j a k)) ^ e k :=
    fun a => gm_linComb M F e (𝟙 Y ≫ φ' a) y (i a) (j a) (Set.mem_iInter.1 hy.1 a) (Set.mem_iInter.1 hy.2 a)
  simp only [b, trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem exists_gen_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) {Y : Scheme.{0}} {K : Type} [Fintype K] (φ' : K → (Y ⟶ D'.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L (fun p : K × ((Fin r × Fin r) × Fin 4) => φ' p.1 ≫ tensφ T.pr p.2) (fun p => ε p.1 * tensε W p.2))), t.IsGen → ∃ t' : LB.Gen (LB.LinComb D'.P.L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → (∏ a, gm (q ≫ φ' a) z _ (T.w.s (fun k => J ((q ≫ φ' a) ≫ tensφ T.pr k), J' (q ≫ φ' a))) ^ ε a) * val t' q z J' = val t q z J := by
  intro R _ _ D D' r W T Y K _ φ' ε t ht
  obtain ⟨t₂, ht₂, h₂⟩ := exists_flat D.P.L (tensφ T.pr) (tensε W) φ' ε t ht
  have hA : (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).IsLB :=
    LB.isLB_linComb (LB.isLB_linComb D.P.isLB _ _) _ _
  have hB : (LB.LinComb D'.P.L φ' ε).IsLB := LB.isLB_linComb D'.P.isLB _ _
  obtain ⟨t', ht', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso hA hB (isoInv (LB.linCombIso T.w φ' ε))
    (isoInv_isGen (DVR.linCombIso_isGen T.w T.w_gen φ' ε)) t₂ ht₂
  refine ⟨t', ht', fun Z q z J J' hJ hJ' => ?_⟩
  let i : K → (Fin r × Fin r) × Fin 4 → D.P.L.ι := fun a k => J ((q ≫ φ' a) ≫ tensφ T.pr k)
  let j : K → D'.P.L.ι := fun a => J' (q ≫ φ' a)
  have hi : q z ∈ LB.wchart (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' i :=
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun k => hJ ((q ≫ φ' a) ≫ tensφ T.pr k)
  have hj : q z ∈ LB.wchart D'.P.L φ' j := hJ'.mem φ' q
  have e1 := hv Z q z j i hj hi
  have hm : q z ∈ (LB.LinComb D'.P.L φ' ε).U j ⊓ (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).U i :=
    ⟨hj, hi⟩
  have hm' : q z ∈ (LB.div (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε) (LB.LinComb D'.P.L φ' ε)).U (i, j) :=
    ⟨hi, hj⟩
  have e2 : gm q z ((LB.LinComb D'.P.L φ' ε).U j ⊓ (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) φ' ε).U i)
      ((isoInv (LB.linCombIso T.w φ' ε)).s (j, i)) =
      (∏ a, gm (q ≫ φ' a) z _ (T.w.s (i a, j a)) ^ ε a)⁻¹ :=
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res q z _ hm _).trans
      (GlobalTheory.WtTower.gm_linCombIso T.w φ' ε (i, j) q z hm')))
  have e3 : gm q z _ (t₂.s i) = val t q z J :=
    (h₂ i Z q z hi).trans (val_of t q z J _ fun p => by simp only [i, Category.assoc]).symm
  change _ * gm q z _ (t'.s j) = _
  rw [e1, e2, e3]
  exact mul_inv_cancel_left _ _

end GlobalTheory.TensGen
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_le_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) :
    α ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hW hy

theorem locInt_le_gen {S G Y T : Scheme.{0}} (g : G ⟶ S) (α : Y ⟶ G) (t : Y ⟶ T) (e : T ⟶ S)
    (hpb : α ≫ g = t ≫ e) (W : G.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) :
    α ⁻¹ᵁ W ≤ t ⁻¹ᵁ (e ⁻¹ᵁ U) := by
  intro y hy
  have h1 : g (α y) ∈ U := hWU hy
  have h2 : (α ≫ g) y = (t ≫ e) y := by rw [hpb]
  show e (t y) ∈ U
  rw [← Scheme.Hom.comp_apply, ← h2]
  exact h1

def LocInt {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (L : LB G.left) {Y : Scheme.{0}}
    (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : α ≫ G.hom = t ≫ M.gp) {k : ℕ} (s : SecK L α k) : Prop :=
  ∀ (j : L.ι) (W : G.left.Opens) (U : M.S.Opens) (hW : W ≤ L.U j) (hWU : W ≤ G.hom ⁻¹ᵁ U),
    IsAffineOpen W → IsAffineOpen U →
    ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)),
      (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧
      (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op).hom (s.f (fun _ => j)) =
        ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb W U hWU)).hom (b m)

theorem le_preimage_of_comp_eq {X X' S : Scheme.{0}} (g : X ⟶ S) (g' : X ⟶ X') (h : X' ⟶ S) (e : g' ≫ h = g)
    (U : S.Opens) : g ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (h ⁻¹ᵁ U) := by
  intro x hx
  show h (g' x) ∈ U
  rw [← Scheme.Hom.comp_apply, e]
  exact hx

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

abbrev SymUnit (r : ℕ) : Type :=
  {b : (Matrix (Fin r) (Fin r) ℤ)ˣ // (b : Matrix (Fin r) (Fin r) ℤ).transpose = b}

def TensO {r : ℕ} (_ : SymUnit r) : Type := Matrix (Fin r) (Fin r) ℤ

namespace TensO

variable {r : ℕ} (s : SymUnit r)

instance : Ring (TensO s) := inferInstanceAs (Ring (Matrix (Fin r) (Fin r) ℤ))

def mat (a : TensO s) : Matrix (Fin r) (Fin r) ℤ := a

def ofMat (a : Matrix (Fin r) (Fin r) ℤ) : TensO s := a

theorem inv_transpose : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose =
    ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) := by
  have h1 : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ) = 1 :=
    Units.inv_mul s.1
  have h2 : (s.1 : Matrix (Fin r) (Fin r) ℤ) * ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = 1 :=
    Units.mul_inv s.1
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, s.2, Matrix.transpose_one] at h3
  calc _ = (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ)) *
        ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose := by rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h3, Matrix.mul_one]

instance : StarRing (TensO s) where
  star a := ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
    (s.1 : Matrix (Fin r) (Fin r) ℤ)
  star_involutive a := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ)).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) = a
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, s.2, inv_transpose]
    have h1 : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ) = 1 :=
      Units.inv_mul s.1
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rfl
  star_mul a b := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a * mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) =
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ)) *
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ))
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.one_mul]
  star_add a b := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a + mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) = _
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
    rfl

theorem star_def (a : TensO s) : star a = ofMat s (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (mat s a).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ)) := rfl

@[simp] theorem mat_one : mat s (1 : TensO s) = 1 := rfl

end TensO

def symUnitOf {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det) : SymUnit r :=
  ⟨((Matrix.isUnit_iff_isUnit_det _).2 h).unit, by
    show (W + W.transpose).transpose = W + W.transpose
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]⟩

end GlobalTheory.Mum

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def Tens.smulF (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) : D'.X :=
  T.xe.symm (fun i => ∑ j, TensO.mat s a i j • T.xe z j)

theorem Tens.xe_smulF (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) (i : Fin r) :
    T.xe (T.smulF s a z) i = ∑ j, TensO.mat s a i j • T.xe z j := by
  simp [Tens.smulF]

def Tens.mod (T : Tens D D' W) (s : SymUnit r) : Module (TensO s) D'.X where
  smul := T.smulF s
  one_smul z := by
    show T.smulF s 1 z = z
    apply T.xe.injective
    funext i
    rw [Tens.xe_smulF]
    simp [TensO.mat_one, Matrix.one_apply, ite_smul]
  mul_smul a b z := by
    show T.smulF s (a * b) z = T.smulF s a (T.smulF s b z)
    apply T.xe.injective
    funext i
    have hmat : TensO.mat s (a * b) = TensO.mat s a * TensO.mat s b := rfl
    simp only [Tens.xe_smulF, hmat, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  smul_zero a := by
    show T.smulF s a 0 = 0
    apply T.xe.injective
    funext i
    simp [Tens.xe_smulF]
  smul_add a z z' := by
    show T.smulF s a (z + z') = T.smulF s a z + T.smulF s a z'
    apply T.xe.injective
    funext i
    simp [Tens.xe_smulF, smul_add, Finset.sum_add_distrib]
  add_smul a b z := by
    show T.smulF s (a + b) z = T.smulF s a z + T.smulF s b z
    apply T.xe.injective
    funext i
    have hmat : TensO.mat s (a + b) = TensO.mat s a + TensO.mat s b := rfl
    simp [Tens.xe_smulF, hmat, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  zero_smul z := by
    show T.smulF s 0 z = 0
    apply T.xe.injective
    funext i
    rw [Tens.xe_smulF, map_zero]
    exact Finset.sum_eq_zero fun j _ => by
      show (0 : Matrix (Fin r) (Fin r) ℤ) i j • T.xe z j = 0
      simp

theorem Tens.xe_smul (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) (i : Fin r) :
    letI := T.mod s
    T.xe (a • z) i = ∑ j, TensO.mat s a i j • T.xe z j :=
  T.xe_smulF s a z i

def Tens.act (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) : D'.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D'.P.A fun i => ∏ j, T.pr j ^ a i j)

theorem Tens.act_pr (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    T.act a ≫ T.pr i = ∏ j, T.pr j ^ a i j :=
  T.lim.fac _ ⟨i⟩

def Tens.inc (T : Tens D D' W) (i₀ : Fin r) : D.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D.P.A fun i => if i = i₀ then 𝟙 _ else 1)

theorem Tens.inc_pr' (T : Tens D D' W) (i₀ i : Fin r) :
    T.inc i₀ ≫ T.pr i = if i = i₀ then 𝟙 _ else 1 :=
  T.lim.fac _ ⟨i⟩

def Tens.xi (T : Tens D D' W) (i₀ : Fin r) : D.X →+ D'.X :=
  T.xe.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ => D.X) i₀)

def Tens.xp (T : Tens D D' W) (i₀ : Fin r) : D'.X →+ D.X :=
  (Pi.evalAddMonoidHom (fun _ => D.X) i₀).comp T.xe.toAddMonoidHom

end

def TensO.idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) : TensO s := TensO.ofMat s (Matrix.single i₀ i₀ 1)

theorem TensO.idem_mul_idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) : TensO.idem s i₀ * TensO.idem s i₀ = TensO.idem s i₀ := by
  have h : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    simp
  exact h

def TensO.binv {r : ℕ} (s : SymUnit r) : TensO s := TensO.ofMat s ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secK_pullMul_gen : ∀ {X Y : Scheme.{0}} (L : LB X), L.IsLB → ∀ (β : Y ⟶ X) (g : Y ⟶ Y) (h : X ⟶ X), g ≫ β = β ≫ h →
    ∀ (k k' : ℕ) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, h] ![(k' : ℤ), -(k : ℤ)])), u.IsGen → ∀ (σ : SecK L β k),
    ∃ σ₂ : SecK L β k', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval σ₂ r z J = (val u (r ≫ β) z J).val * sval σ (r ≫ g) z J := by
  intro X Y L hL β g h hc k k' u hu σ
  have hu' := DVR.pullGen_isGen L _ _ u hu β
  have hF : FormEq (Sum.elim (fun i => g ≫ (fun _ : Fin 1 => β) i) (fun i => β ≫ (![𝟙 X, h] : Fin 2 → (X ⟶ X)) i))
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![(k' : ℤ), -(k : ℤ)]) (fun _ : Fin 1 => β) (fun _ => (k' : ℤ)) := by
    intro U _ f
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, hc, zpow_neg]
    rw [mul_comm (f β ^ _)]
    exact mul_inv_cancel_left _ _
  obtain ⟨σ₂, hσ₂⟩ := exists_sec hL hF (pullMulSec σ g (LB.pullGen L _ _ u β) hu')
  refine ⟨σ₂, fun Z r z J hJ => ?_⟩
  rw [hσ₂ Z r z J hJ, sval_pullMulSec σ g _ hu' r z hJ, val_pull hJ u β r, mul_comm]

end GlobalTheory.Mum
end
