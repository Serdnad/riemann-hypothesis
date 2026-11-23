module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle116
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
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautTau

section Core

variable {X X' P P' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem exists_gen_across (hL : L.IsLB) (hL' : L'.IsLB) (ψ : K → (P ⟶ X)) (ψ' : K → (P' ⟶ X')) (ε : K → ℤ)
    (β₂ : P' ⟶ P) (w : LB.Iso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull β₂)) (hw : w.IsGen) (p : Y ⟶ P')
    (b : LB.Gen (LB.LinComb L (fun k => p ≫ β₂ ≫ ψ k) (fun k => -ε k))) (hb : b.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L' (fun k => p ≫ ψ' k) (fun k => -ε k)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        val u r z J' = gm (r ≫ p) z _ (w.s (fun _ k => J ((r ≫ p) ≫ β₂ ≫ ψ k), fun k => J' ((r ≫ p) ≫ ψ' k))) *
          val b r z J := by
  have hC : (LB.LinComb L ψ ε).IsLB := DVR.linComb_isLB _ hL _ _
  have hC' : (LB.LinComb L' ψ' ε).IsLB := DVR.linComb_isLB _ hL' _ _
  have pw := (isGen_iff w).1 hw

  have wchg : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j j₂ : K → L.ι) (q q₂ : K → L'.ι),
      (∀ k, (f ≫ p ≫ β₂ ≫ ψ k) z ∈ L.U (j k)) → (∀ k, (f ≫ p ≫ β₂ ≫ ψ k) z ∈ L.U (j₂ k)) →
      (∀ k, (f ≫ p ≫ ψ' k) z ∈ L'.U (q k)) → (∀ k, (f ≫ p ≫ ψ' k) z ∈ L'.U (q₂ k)) →
      gw w (f ≫ p) z j q = (∏ k, gm (f ≫ p ≫ β₂ ≫ ψ k) z _ (L.g (j k) (j₂ k)) ^ ε k) *
        (∏ k, gm (f ≫ p ≫ ψ' k) z _ (L'.g (q k) (q₂ k)) ^ ε k)⁻¹ * gw w (f ≫ p) z j₂ q₂ := by
    intro Z f z j j₂ q q₂ hj hj₂ hq hq₂
    have m₁ : β₂ ((f ≫ p) z) ∈ (LB.LinComb L ψ ε).U j := Set.mem_iInter.2 fun k => hj k
    have m₂ : β₂ ((f ≫ p) z) ∈ (LB.LinComb L ψ ε).U j₂ := Set.mem_iInter.2 fun k => hj₂ k
    have m₃ : (f ≫ p) z ∈ (LB.LinComb L' ψ' ε).U q := Set.mem_iInter.2 fun k => hq k
    have m₄ : (f ≫ p) z ∈ (LB.LinComb L' ψ' ε).U q₂ := Set.mem_iInter.2 fun k => hq₂ k
    rw [pw Z (f ≫ p) z j j₂ q q₂ m₁ m₂ m₃ m₄]
    erw [gm_linComb L ψ ε ((f ≫ p) ≫ β₂) z j j₂ m₁ m₂, gm_linComb L' ψ' ε (f ≫ p) z q q₂ m₃ m₄]
    simp only [Category.assoc]
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' (fun k => p ≫ ψ' k) q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : K → L.ι),
        f z ∈ LB.wchart L' (fun k => p ≫ ψ' k) q → f z ∈ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j →
        gm f z _ s = gw w (f ≫ p) z j q * gm f z _ (b.s j) := by
    intro q
    let W : (K → L.ι) → Y.Opens := fun j =>
      LB.wchart L' (fun k => p ≫ ψ' k) q ⊓ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j
    have l₀ : ∀ j, W j ≤ LB.wchart L' (fun k => p ≫ ψ' k) q := fun j => inf_le_left
    have l₁ : ∀ j, W j ≤ p ⁻¹ᵁ (((LB.LinComb L ψ ε).pull β₂).U (fun _ => j) ⊓ (LB.LinComb L' ψ' ε).U q) :=
      fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 k),
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 k⟩
    have l₂ : ∀ j, W j ≤ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j := fun j => inf_le_right
    obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Y, W j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : K → L.ι), f z ∈ W j →
        gm f z (W j) (u j) = gw w (f ≫ p) z j q * gm f z _ (b.s j) :=
      ⟨fun j => res (l₁ j) (pullU p _ (w.s (fun _ => j, q))) * res (l₂ j) (b.s j), fun Z f z j hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f z (l₁ j) hz _).trans (gm_pull f p z _ (l₁ j hz) _)) (gm_res f z (l₂ j) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose j hj using fun k => exists_chart hL ((p ≫ β₂ ≫ ψ k) x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hx, Set.mem_iInter.2 hj⟩) u (fun j j₂ x hx => by
        rw [hu _ (𝟙 Y) x j hx.1, hu _ (𝟙 Y) x j₂ hx.2]
        have a := wchg Y (𝟙 Y) x j j₂ q q (fun k => Set.mem_iInter.1 hx.1.2 k) (fun k => Set.mem_iInter.1 hx.2.2 k)
          (fun k => Set.mem_iInter.1 hx.1.1 k) (fun k => Set.mem_iInter.1 hx.1.1 k)
        have c := gen_trans hb (𝟙 Y) x hx.1.2 hx.2.2
        have one : (∏ k, gm (𝟙 Y ≫ p ≫ ψ' k) x _ (L'.g (q k) (q k)) ^ ε k) = 1 :=
          Finset.prod_eq_one fun k _ => by
            rw [gm_self hL' (𝟙 Y ≫ p ≫ ψ' k) x (show (𝟙 Y ≫ p ≫ ψ' k) x ∈ L'.U (q k) from Set.mem_iInter.1 hx.1.1 k),
              one_zpow]
        have hA : (∏ k, gm (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x _ (L.g (j k) (j₂ k)) ^ ε k) *
            trF (L := L) (fun k => p ≫ β₂ ≫ ψ k) (fun k => -ε k) (𝟙 Y) x j j₂ = 1 := by
          rw [trF, ← Finset.prod_mul_distrib]
          exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, _root_.mul_inv_cancel]
        rw [a, one, inv_one, _root_.mul_one]
        erw [c]
        rw [_root_.mul_mul_mul_comm, hA, _root_.one_mul]
        rfl)
    exact ⟨s, fun Z f z j hq hj => (gm_res f z (l₀ j) ⟨hq, hj⟩ s).symm.trans
      ((congrArg (gm f z (W j)) (hs j)).trans (hu Z f z j ⟨hq, hj⟩))⟩
  choose s hs using glue
  refine ⟨⟨s⟩, fun q q₂ => unit_ext fun x hx => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  swap
  · refine (hs (fun k => J' (r ≫ p ≫ ψ' k)) Z r z (fun k => J (r ≫ p ≫ β₂ ≫ ψ k)) (hJ'.mem (fun k => p ≫ ψ' k) r)
      (hJ.mem (fun k => p ≫ β₂ ≫ ψ k) r)).trans ?_
    congr 1
  choose j hj using fun k => exists_chart hL ((p ≫ β₂ ≫ ψ k) x)
  have mj : (𝟙 Y) x ∈ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j := Set.mem_iInter.2 hj
  have e₁ := hs q Y (𝟙 Y) x j hx.1 mj
  have e₂ := hs q₂ Y (𝟙 Y) x j hx.2 mj
  have c := wchg Y (𝟙 Y) x j j q q₂ hj hj (fun k => Set.mem_iInter.1 hx.1 k) (fun k => Set.mem_iInter.1 hx.2 k)
  have one : (∏ k, gm (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x _ (L.g (j k) (j k)) ^ ε k) = 1 :=
    Finset.prod_eq_one fun k _ => by
      rw [gm_self hL (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x (show (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x ∈ L.U (j k) from hj k), one_zpow]
  rw [one, _root_.one_mul] at c
  have g := gm_linComb L' (fun k => p ≫ ψ' k) (fun k => -ε k) (𝟙 Y) x q q₂ hx.1 hx.2
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx]
  erw [g, e₁, e₂, c]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rw [_root_.mul_assoc]

end Core

section Main

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]

theorem toUnit_left' {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem ag_four {G : Type} [CommGroup G] (a b c d : G) :
    a⁻¹ * b * c * d⁻¹ = (a * b⁻¹ * c⁻¹ * d)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tauCoord_of_dataFrom (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ))
    (hD : DataFrom T iw s ε n Q e) (a b : Q.X) :
    ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      Q.TauCoord a b k := by
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, hτ⟩ := hD
  obtain ⟨k, hk, hval⟩ := hτ a b
  refine ⟨k, hk, ?_⟩
  let h : (𝟙_ (Over (Sp V))).left ⟶ (𝟙_ (Over (Sp W))).left := spMap iw
  let p : (𝟙_ (Over (Sp V))).left ⟶ (G2 Q.B).left := (lift (Q.c a) (Q.c b)).left
  have c0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have t0 : T.c₀ 0 = 1 := mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))
  have hF1 : p ≫ β₂ = (lift (pushPt hpb.1.w (Q.c a)) (pushPt hpb.1.w (Q.c b))).left := by
    apply pullback.hom_ext
    · show _ ≫ (fst T.B T.B).left = _ ≫ (fst T.B T.B).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      rfl
    · show _ ≫ (snd T.B T.B).left = _ ≫ (snd T.B T.B).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      rfl
  have px : (pushPt hpb.1.w (Q.c a)).left = h ≫ (T.c₀ ((n : ℤ) • e a)).left := hc a
  have py : (pushPt hpb.1.w (Q.c b)).left = h ≫ (T.c₀ ((n : ℤ) • e b)).left := hc b
  have pxy : (pushPt hpb.1.w (Q.c a) * pushPt hpb.1.w (Q.c b)).left =
      h ≫ (T.c₀ ((n : ℤ) • e a) * T.c₀ ((n : ℤ) • e b)).left := by
    have m := congrArg (fun q => q.left) (map_mul (pushHom hpb (𝟙_ (Over (Sp V)))) (Q.c a) (Q.c b))
    refine m.symm.trans ?_
    show (Q.c a * Q.c b).left ≫ β = _
    rw [← Q.c_add, hc, ← T.c₀_add, ← smul_add, ← map_add (f := _)]
  have p1 : (1 : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ spMap iw) ⟶ T.B).left = h ≫ (1 : 𝟙_ (Over (Sp W)) ⟶ T.B).left := by
    have m := congrArg (fun q => q.left) (map_one (pushHom hpb (𝟙_ (Over (Sp V)))))
    refine m.symm.trans ?_
    show (1 : 𝟙_ (Over (Sp V)) ⟶ Q.B).left ≫ β = _
    have := hc 0
    rw [c0, map_zero, smul_zero, t0] at this
    exact this
  have hFT : FormEq (fun k => h ≫ lamPts (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b)) k) negε
      (fun I => p ≫ β₂ ≫ GlobalTheory.PrimCocycle.lamφ T.B I) (fun I => -GlobalTheory.PrimCocycle.lamε I) := by
    intro U _ H
    have r₁ : ∀ I, p ≫ β₂ ≫ GlobalTheory.PrimCocycle.lamφ T.B I =
        (lift (pushPt hpb.1.w (Q.c a)) (pushPt hpb.1.w (Q.c b))).left ≫ GlobalTheory.PrimCocycle.lamφ T.B I := fun I => by
      rw [← Category.assoc, hF1]
    simp only [r₁, zpow_neg, Finset.prod_inv_distrib]
    rw [GlobalTheory.PrimCocycle.prod_lam, pxy, px, py, p1, Fin.prod_univ_four]
    simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    exact ag_four _ _ _ _
  have hFQ : FormEq (fun I => p ≫ GlobalTheory.PrimCocycle.lamφ Q.B I) (fun I => -GlobalTheory.PrimCocycle.lamε I)
      (lamPts (Q.c a) (Q.c b)) negε := by
    intro U _ H
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rw [GlobalTheory.PrimCocycle.prod_lam, Fin.prod_univ_four]
    simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    exact (ag_four _ _ _ _).symm
  obtain ⟨b₁, hb₁, hv₁⟩ := exists_gen T.M.isLB hFT
    (LB.pullGen T.M.L (lamPts (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b))) negε (T.τ₀ _ _) h)
    (DVR.pullGen_isGen _ _ _ _ (T.τ₀_gen _ _) h)
  obtain ⟨u₁, hu₁, hvu⟩ := exists_gen_across T.M.isLB Q.M.isLB (GlobalTheory.PrimCocycle.lamφ T.B)
    (GlobalTheory.PrimCocycle.lamφ Q.B) GlobalTheory.PrimCocycle.lamε β₂ w hw p b₁ hb₁
  obtain ⟨u, hu, hvq⟩ := exists_gen Q.M.isLB hFQ u₁ hu₁
  refine ⟨u, hu, fun z J' hJ' => ?_⟩
  choose J hJ using fun χ : (TK V).left ⟶ T.B.left => exists_chart T.M.isLB (χ z)
  have hJg : Good T.M.L z J := hJ
  rw [hval z J J' hJg hJ']
  congr 1
  rw [hvq _ _ z J' hJ', hvu _ _ z J J' hJg hJ', hv₁ _ _ z J hJg, val_pull hJg]
  have hr : (toUnit (TK V)).left ≫ p = (lift (toUnit (TK V) ≫ Q.c a) (toUnit (TK V) ≫ Q.c b)).left := by
    rw [← Over.comp_left, comp_lift]
  have hh : (toUnit (TK V)).left ≫ h = (TK V).hom ≫ spMap iw := by
    rw [toUnit_left']
  rw [hh, ← hr]
  rfl

end Main

end GlobalTheory.TautTau
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.TChart

theorem cotangent_indep_of_isComplAt : ∀ (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (I : Type) [Fintype I] (R : Type) [CommRing R] [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ (m : ℕ) (ι₀ : Fin m ↪ I), (∀ k, ψ (MvPolynomial.X (ι₀ k)) ∈ maximalIdeal R) → ∀ c : Fin m → R, ∑ k, c k * ψ (MvPolynomial.X (ι₀ k)) ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal W).map (ψ.comp MvPolynomial.C) → ∀ k, c k ∈ maximalIdeal R := by
  intro W _ _ _ I _ R _ _ ψ hψ hloc m ι₀ hX c hc k
  classical
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  haveI hflat : Module.Flat (MvPolynomial I W) R := hψ.2.2.1
  haveI := hloc
  have hsmul : ∀ (a : MvPolynomial I W) (r : R), a • r = ψ a * r := fun a r => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  let P : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ
  have hPm : P.map ψ = maximalIdeal R := hψ.2.2.2.1
  let δ : MvPolynomial I W → ResidueField R := fun f => residue R (ψ (MvPolynomial.pderiv (ι₀ k) f))
  have hπP : ∀ p ∈ P, residue R (ψ p) = 0 := fun p hp => (residue_eq_zero_iff _).2 hp
  have hδmul : ∀ a b, δ (a * b) = residue R (ψ a) * δ b + residue R (ψ b) * δ a := by
    intro a b; simp only [δ, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by intro a b; simp [δ]
  let K : Ideal (MvPolynomial I W) :=
    { carrier := {x | x ∈ P ∧ δ x = 0}
      add_mem' := fun {a b} ha hb => ⟨P.add_mem ha.1 hb.1, by rw [hδadd, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨P.zero_mem, by simp [δ]⟩
      smul_mem' := fun a x hx => ⟨P.mul_mem_left a hx.1, by
        rw [smul_eq_mul, hδmul, hx.2, hπP x hx.1, mul_zero, zero_mul, add_zero]⟩ }
  have hCW : (maximalIdeal W).map (MvPolynomial.C : W →+* MvPolynomial I W) ≤ K := by
    refine Ideal.map_le_iff_le_comap.2 fun w hw => ⟨?_, by simp [δ]⟩
    show ψ (MvPolynomial.C w) ∈ maximalIdeal R
    exact map_nonunit (ψ.comp MvPolynomial.C) w hw
  have hP2 : P ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun p hp q hq => ⟨P.mul_mem_left p hq, ?_⟩
    show δ (p * q) = 0
    rw [hδmul, hπP p hp, hπP q hq]; simp
  have hJ : maximalIdeal R ^ 2 ⊔ (maximalIdeal W).map (ψ.comp MvPolynomial.C) ≤ K.map ψ := by
    rw [← hPm, ← Ideal.map_pow, ← Ideal.map_map, ← Ideal.map_sup]
    exact Ideal.map_mono (sup_le hP2 hCW)
  let muT : TensorProduct (MvPolynomial I W) R P →ₗ[MvPolynomial I W] R :=
    (TensorProduct.rid (MvPolynomial I W) R).toLinearMap ∘ₗ (Submodule.subtype P).lTensor R
  have hmu : Function.Injective muT :=
    (TensorProduct.rid (MvPolynomial I W) R).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hmut : ∀ (r : R) (p : P), muT (r ⊗ₜ p) = ψ p * r := fun r p => by
    simp [muT, hsmul]
  let f : R →+ P →+ ResidueField R := AddMonoidHom.mk'
    (fun r => AddMonoidHom.mk' (fun p : P => residue R r * δ p) (by intro a b; simp [hδadd, mul_add]))
    (by intro a b; ext p; simp [add_mul])
  have hf : ∀ (a : MvPolynomial I W) (r : R) (p : P), f (a • r) p = f r (a • p) := by
    intro a r p
    simp only [f, AddMonoidHom.mk'_apply, hsmul, Submodule.coe_smul, smul_eq_mul, hδmul, hπP p p.2, map_mul]
    ring
  let L : TensorProduct (MvPolynomial I W) R P →+ ResidueField R := TensorProduct.liftAddHom f hf
  have hLt : ∀ (r : R) (p : P), L (r ⊗ₜ p) = residue R r * δ p := fun r p => by
    simp [L, f]
  have hspan : ∀ y ∈ K.map ψ, ∀ r : R, ∃ t, muT t = r * y ∧ L t = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      exact ⟨r ⊗ₜ ⟨j, hj.1⟩, by rw [hmut]; ring, by rw [hLt]; simp [hj.2]⟩
    | zero => intro r; exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨t₁, h₁, h₁'⟩ := hx r
      obtain ⟨t₂, h₂, h₂'⟩ := hy r
      exact ⟨t₁ + t₂, by rw [map_add (f := _), h₁, h₂]; ring, by rw [map_add (f := _), h₁', h₂', add_zero]⟩
    | smul a x _ hx =>
      intro r
      obtain ⟨t, h₁, h₂⟩ := hx (r * a)
      exact ⟨t, by rw [h₁, smul_eq_mul]; ring, h₂⟩
  have hX' : ∀ j, MvPolynomial.X (ι₀ j) ∈ P := hX
  let t₀ : TensorProduct (MvPolynomial I W) R P := ∑ j, c j ⊗ₜ ⟨MvPolynomial.X (ι₀ j), hX' j⟩
  have hmu0 : muT t₀ = ∑ j, c j * ψ (MvPolynomial.X (ι₀ j)) := by

    simp only [t₀, map_sum, hmut]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hL₀ : L t₀ = residue R (c k) := by

    simp only [t₀, map_sum, hLt, δ, MvPolynomial.pderiv_X, Pi.single_apply, ι₀.injective.eq_iff]
    simp
  obtain ⟨t, ht₁, ht₂⟩ := hspan _ (hJ hc) 1
  have : t = t₀ := hmu (by rw [ht₁, _root_.one_mul, hmu0])
  rw [this, hL₀] at ht₂
  exact (residue_eq_zero_iff _).1 ht₂

end GlobalTheory.TChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.CUniq

theorem map_max {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (θ : R →+* V) [IsLocalHom θ]
    {x : R} (hx : x ∈ maximalIdeal R) : θ x ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun h => hx (isUnit_of_map_unit θ x h)

theorem diff_pow {A R V : Type} [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ψ : A →+* R) (hψ : IsComplAt ψ) (θ₁ θ₂ : R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (h : θ₁.comp ψ = θ₂.comp ψ) (k : ℕ) : ∀ r : R, θ₁ r - θ₂ r ∈ maximalIdeal V ^ k := by
  have hc : ∀ a, θ₁ (ψ a) = θ₂ (ψ a) := fun a => congrArg (fun f => f a) h
  induction k with
  | zero => intro r; simp
  | succ k ih =>
    have hm : ∀ x ∈ maximalIdeal R, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 1) := by
      intro x hx
      rw [← hψ.2.2.2.1] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, -, rfl⟩ := hy
        simp [hc]
      | zero => simp
      | add y z _ _ hy hz =>
        have := add_mem hy hz
        simpa [map_add (f := _), sub_add_sub_comm] using this
      | smul a y hy' hy =>
        have hyM : y ∈ maximalIdeal R := hψ.2.2.2.1 ▸ hy'
        have e : θ₁ (a • y) - θ₂ (a • y) = θ₁ a * (θ₁ y - θ₂ y) + (θ₁ a - θ₂ a) * θ₂ y := by
          simp only [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ hy) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih a) (map_max θ₂ hyM)
    intro r
    obtain ⟨a, b, hb, hx⟩ := hψ.2.2.2.2 r
    have e := hm _ hx
    have hu : IsUnit (θ₁ (ψ b)) := hb.map θ₁
    have e2 : θ₁ (r * ψ b - ψ a) - θ₂ (r * ψ b - ψ a) = (θ₁ r - θ₂ r) * θ₁ (ψ b) := by
      simp only [map_sub, map_mul, hc]; ring
    rw [e2] at e
    obtain ⟨u, hu'⟩ := hu
    have : θ₁ r - θ₂ r = (θ₁ r - θ₂ r) * θ₁ (ψ b) * ↑u⁻¹ := by
      rw [← hu', _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ e

end GlobalTheory.TChart.CUniq

theorem GlobalTheory.TChart.cuniq : ∀ (A R V : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (ψ : A →+* R), IsComplAt ψ → ∀ θ₁ θ₂ : R →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp ψ = θ₂.comp ψ → θ₁ = θ₂ := by
  intro A R V _ _ _ _ _ _ ψ hψ θ₁ θ₂ h₁ h₂ h
  ext r
  have hk := fun k => GlobalTheory.TChart.CUniq.diff_pow ψ hψ θ₁ θ₂ h k r
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top
  have : θ₁ r - θ₂ r ∈ ⨅ k : ℕ, maximalIdeal V ^ k := Ideal.mem_iInf.mpr hk
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at this
  exact this
end

section

open IsLocalRing NumberField

namespace GlobalTheory.PointAlg

theorem trdeg_le_of_hom_algClosure (X Y Z : Type) [Field X] [Field Y] [Field Z] [Algebra ℚ X] [Algebra ℚ Y]
    (f : X →+* AlgebraicClosure Z) (e : Y →+* Z) (he : Function.Surjective e) :
    Algebra.trdeg ℚ X ≤ Algebra.trdeg ℚ Y := by
  letI : Algebra ℚ Z := (e.comp (algebraMap ℚ Y)).toAlgebra
  have h1 : Algebra.trdeg ℚ X ≤ Algebra.trdeg ℚ (AlgebraicClosure Z) :=
    trdeg_le_of_injective f.toRatAlgHom f.injective
  have h2 : Algebra.trdeg ℚ Z ≤ Algebra.trdeg ℚ Y :=
    trdeg_le_of_surjective e.toRatAlgHom he
  have h3 := trdeg_add_eq ℚ Z (A := AlgebraicClosure Z)
  rw [trdeg_eq_zero (R := Z) (A := AlgebraicClosure Z), add_zero] at h3
  exact h1.trans (h3.ge.trans h2)

theorem closed_point_of_values (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R]
    [IsLocalRing R] [Field K] (b : F →+* A) (hb : b.EssFiniteType) (ψ : A →+* R) (hψ : GlobalTheory.TChart.IsComplAt ψ)
    (ev : R →+* K) (k₀ : Subfield K) (hk : Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)))
    (hev : ∀ a, ev (ψ a) ∈ k₀) : (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  obtain ⟨j⟩ := hk
  obtain ⟨-, -, -, hmap, hres⟩ := hψ
  set q : Ideal A := (maximalIdeal R).comap ψ with hq
  haveI hqp : q.IsPrime := Ideal.comap_isPrime ψ _
  let L := Localization.AtPrime q
  have hu : ∀ y : q.primeCompl, IsUnit (ψ y) := fun y => by
    by_contra h
    exact y.2 ((mem_maximalIdeal _).mpr h)
  let Φ : L →+* R := IsLocalization.lift (M := q.primeCompl) hu
  have hΦ : ∀ a, Φ (algebraMap A L a) = ψ a := fun a => IsLocalization.lift_eq hu a
  have hne : ∀ a, IsUnit (ψ a) → ev (ψ a) ≠ 0 := fun a h => (h.map ev).ne_zero
  have hΦk : ∀ x, ev (Φ x) ∈ k₀ := by
    intro x
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.primeCompl x
    have h2 := congrArg (fun t => ev (Φ t)) h
    simp only [map_mul, hΦ] at h2
    rw [eq_div_of_mul_eq (hne _ (hu s)) h2]
    exact k₀.div_mem (hev _) (hev _)
  haveI : IsLocalHom Φ := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.primeCompl x
    have h2 := congrArg Φ h
    simp only [map_mul, hΦ] at h2
    have ha : IsUnit (ψ a) := h2 ▸ hx.mul (hu s)
    have ha' : a ∈ q.primeCompl := fun h => (mem_maximalIdeal _).mp h ha
    have := IsLocalization.map_units L ⟨a, ha'⟩
    simp only at h
    exact isUnit_of_mul_isUnit_left (h ▸ this)
  have hsurj : Function.Surjective (ResidueField.map Φ) := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    obtain ⟨a, s, hs, h⟩ := hres r
    rw [← residue_eq_zero_iff, map_sub, map_mul, sub_eq_zero] at h
    refine ⟨residue L (algebraMap A L a) / residue L (algebraMap A L s), ?_⟩
    rw [map_div₀, ResidueField.map_residue, ResidueField.map_residue, hΦ, hΦ, ← h]
    exact mul_div_cancel_right₀ _ (hs.map (residue R)).ne_zero
  let g : L →+* AlgebraicClosure (ResidueField R) := j.comp ((ev.comp Φ).codRestrict k₀ hΦk)
  haveI hP : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  have hE : ((algebraMap A L).comp (b.comp (algebraMap ℚ F))).EssFiniteType := by
    refine RingHom.EssFiniteType.comp (RingHom.EssFiniteType.comp ?_ hb) ?_
    · exact RingHom.essFiniteType_algebraMap.mpr inferInstance
    · exact RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization L q.primeCompl)
  letI : Algebra ℚ L := ((algebraMap A L).comp (b.comp (algebraMap ℚ F))).toAlgebra
  have hmax : RingHom.ker g = maximalIdeal L :=
    GlobalTheory.eq_maximalIdeal_of_trdeg_le ℚ L hE _ hP
      (trdeg_le_of_hom_algClosure _ _ _
        (IsFractionRing.lift (K := FractionRing (L ⧸ RingHom.ker g)) (RingHom.kerLift_injective g))
        (ResidueField.map Φ) hsurj)
  have h0 : ∀ r ∈ maximalIdeal R, ev r = 0 := by
    have : maximalIdeal R ≤ RingHom.ker ev := by
      rw [← hmap, Ideal.map_le_iff_le_comap]
      intro a ha
      have h1 : algebraMap A L a ∈ RingHom.ker g := by
        rw [hmax]
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L q a).mpr ha
      rw [RingHom.mem_ker] at h1
      have h2 := congrArg Subtype.val (j.injective (h1.trans (map_zero j).symm))
      change ev (Φ (algebraMap A L a)) = 0 at h2
      rw [hΦ] at h2
      exact h2
    exact fun r hr => this hr
  refine ⟨h0, fun r => ?_⟩
  obtain ⟨a, s, hs, h⟩ := hres r
  have h2 := h0 _ h
  rw [map_sub, map_mul, sub_eq_zero] at h2
  rw [eq_div_of_mul_eq (hne _ hs) h2]
  exact k₀.div_mem (hev _) (hev _)

end GlobalTheory.PointAlg
end
