module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateL
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle035
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

section TransportLinComb

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I]

theorem transChart_le (ψ : K → (X' ⟶ X)) (σ : I → (Y ⟶ X')) (jN : I × K → L.ι) (jM : I → L'.ι) (i : I) :
    LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) jN ⊓ LB.wchart L' σ jM ≤
      σ i ⁻¹ᵁ (LB.wchart L ψ (fun k => jN (i, k)) ⊓ L'.U (jM i)) :=
  fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k), Set.mem_iInter.1 hy.2 i⟩

def transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)) (σ : I → (Y ⟶ X')) (e : I → ℤ) :
    LB.Iso (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)) where
  s P := ∏ i, res (transChart_le ψ σ P.1 P.2 i) (pullU (σ i) _ (w.s (fun k => P.1 (i, k), P.2 i))) ^ e i

theorem gm_transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) (r : Z ⟶ Y) (z : Z) (P : (I × K → L.ι) × (I → L'.ι))
    (hP : r z ∈ LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) P.1 ⊓ LB.wchart L' σ P.2) :
    gm r z _ ((transIso ψ δ w σ e).s P) = ∏ i, gm (r ≫ σ i) z _ (w.s (fun k => P.1 (i, k), P.2 i)) ^ e i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ e i) ?_))
  exact (gm_res r z _ hP _).trans (gm_pull r (σ i) z _ (transChart_le ψ σ P.1 P.2 i hP) _)

theorem isGen_iff_gm' {M : LB Y} (t : LB.Gen M) :
    t.IsGen ↔ ∀ i j y, y ∈ M.U i ⊓ M.U j →
      gm (𝟙 Y) y (M.U i) (t.s i) = gm (𝟙 Y) y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y) y (M.U j) (t.s j) := by
  constructor
  · intro h i j y hy
    exact (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (h i j)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
  · intro h i j
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y _ hy _).trans ((h i j y hy).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))).symm)

theorem gm_of_isGen (ψ : K → (X' ⟶ X)) (δ : K → ℤ) {w : LB.Iso L' (LB.LinComb L ψ δ)} (hw : w.IsGen)
    (r : Z ⟶ X') (z : Z) (P Q : (K → L.ι) × L'.ι)
    (hm : r z ∈ LB.wchart L ψ P.1 ⊓ L'.U P.2 ⊓ (LB.wchart L ψ Q.1 ⊓ L'.U Q.2)) :
    gm r z _ (w.s P) = ((∏ k, gm (r ≫ ψ k) z (L.U (P.1 k) ⊓ L.U (Q.1 k)) (L.g (P.1 k) (Q.1 k)) ^ δ k) *
      (gm r z _ (L'.g P.2 Q.2))⁻¹) * gm r z _ (w.s Q) := by
  have h := congrArg (gm r z _) (hw P Q)
  exact (gm_res r z _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div L' (LB.LinComb L ψ δ) r z P Q hm).trans (congrArg (· * _) (gm_linComb L ψ δ r z _ _ hm.1.1 hm.2.1)))
    (gm_res r z _ hm _))))

theorem isGen_transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) {w : LB.Iso L' (LB.LinComb L ψ δ)} (hw : w.IsGen)
    (σ : I → (Y ⟶ X')) (e : I → ℤ) : (transIso ψ δ w σ e).IsGen := by
  refine (isGen_iff_gm' _).2 fun P Q y hy => ?_
  have hd : gm (𝟙 Y) y ((LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).U P ⊓ (LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).U Q) ((LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).g P Q) = _ :=
    gm_div (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)) (𝟙 Y) y P Q hy
  rw [gm_transIso ψ δ w σ e (𝟙 Y) y P hy.1, gm_transIso ψ δ w σ e (𝟙 Y) y Q hy.2,
    hd]
  erw [gm_linComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2) (𝟙 Y) y P.1 Q.1 hy.1.1 hy.2.1,
    gm_linComb L' σ e (𝟙 Y) y P.2 Q.2 hy.1.2 hy.2.2,
    Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) (gm_of_isGen ψ δ hw (𝟙 Y ≫ σ i) y
      (fun k => P.1 (i, k), P.2 i) (fun k => Q.1 (i, k), Q.2 i)
      ⟨transChart_le ψ σ P.1 P.2 i hy.1, transChart_le ψ σ Q.1 Q.2 i hy.2⟩)]
  rw [Fintype.prod_prod_type]
  simp only [Category.assoc, mul_zpow, Finset.prod_mul_distrib, ← Finset.prod_zpow, ← zpow_mul, inv_zpow',
    Finset.prod_inv_distrib]
  simp only [mul_comm (δ _) (e _)]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rfl

end TransportLinComb

theorem exists_transIso_linComb : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I]
    (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)), w.IsGen → L.IsLB → L'.IsLB →
    ∀ (σ : I → (Y ⟶ X')) (e : I → ℤ), ∃ v : LB.Iso (LB.LinComb L' σ e)
      (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        gm q z _ (v.s (fun p => J (q ≫ σ p.1 ≫ ψ p.2), fun i => J' (q ≫ σ i))) =
          ∏ i, gm (q ≫ σ i) z _ (w.s (fun k => J (q ≫ σ i ≫ ψ k), J' (q ≫ σ i))) ^ e i := by
  intro X X' Y L L' K I _ _ ψ δ w hw _ _ σ e
  refine ⟨transIso ψ δ w σ e, isGen_transIso ψ δ hw σ e, fun Z q z J J' hJ hJ' => ?_⟩
  exact gm_transIso ψ δ w σ e q z _ ⟨hJ.mem (fun p : I × K => σ p.1 ≫ ψ p.2) q, hJ'.mem σ q⟩

end GlobalTheory.Mum
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaSymTransport

theorem val_symGen_eq : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (ν : LB.Gen (negLB A L k T)) (ν' : LB.Gen (negLB A' L' k T')) (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt⁻¹).left = (translT A' θ'.pt⁻¹).left ≫ f) (hneg : f ≫ (negT A T).left = (negT A' T').left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Hν : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (snd T' A' ≫ (GrpObj.inv : A' ⟶ A')).left]) (ε := ![k, -k]) ν' q z J' * (Ψ (q ≫ (negT A' T').left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (symGen A L k θ ν) (q ≫ f) z J = val (symGen A' L' k θ' ν') q z J' := by
  intro S S' A A' _ _ _ L L' T T' f k θ θ' ν ν' Ψ hT hneg H Hν Z q z J J' hJ hJ'
  have c₁ : (translT A' θ'.pt⁻¹).left ≫ (translT A' θ'.pt).left = 𝟙 _ := by
    rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  have c₂ : (negT A' T').left ≫ (translT A' θ'.pt).left = (translT A' θ'.pt⁻¹).left ≫ (negT A' T').left := by
    rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.PullMove.negT_translT]
  have e₁ := H Z (q ≫ (translT A' θ'.pt⁻¹).left) z J J' hJ hJ'
  have e₂ := H Z (q ≫ (negT A' T').left) z J J' hJ hJ'
  have e₃ := Hν Z q z J J' hJ hJ'
  have e₄ := Hν Z (q ≫ (translT A' θ'.pt⁻¹).left) z J J' hJ hJ'
  simp only [Category.assoc, c₁, c₂, Category.comp_id, ← hT, ← hneg] at e₁ e₂ e₄
  rw [GlobalTheory.ConjPull.val_thetaSym _ _ _ _ hJ, GlobalTheory.ConjPull.val_thetaSym _ _ _ _ hJ']
  simp only [Category.assoc]
  rw [e₁, e₂, e₃, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end GlobalTheory.ThetaSymTransport
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaPowConj

theorem prod_telescope {U : Type} [CommGroup U] (F G : ℕ → U) (n : ℕ) :
    ∏ i ∈ Finset.range n, (F i * G i * (F (i + 1))⁻¹) = F 0 * (∏ i ∈ Finset.range n, G i) * (F n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    group

theorem val_powGen_transport : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  intro S S' A A' _ _ L L' T T' f k N θ θ' Ψ hT hN H Z q z J J' hJ hJ'
  rw [GlobalTheory.ConjPull.val_thetaPow θ N (q ≫ f) z hJ, GlobalTheory.ConjPull.val_thetaPow θ' N q z hJ']
  have step : ∀ i ∈ Finset.range N,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        ((q ≫ f) ≫ (translT A (θ.pt ^ i)).left) z J =
      Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k *
        val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J' *
        (Ψ (q ≫ (translT A' (θ'.pt ^ (i + 1))).left) z J J' ^ k)⁻¹ := by
    intro i _
    have e1 : (q ≫ f) ≫ (translT A (θ.pt ^ i)).left = (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ f := by
      rw [Category.assoc, hT i, Category.assoc]
    have e2 : (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ (translT A' θ'.pt).left =
        q ≫ (translT A' (θ'.pt ^ (i + 1))).left := by
      rw [Category.assoc, ← Over.comp_left, GlobalTheory.PullMove.translT_mul, pow_succ']
    rw [e1, H Z _ z J J' hJ hJ', e2]
  rw [Finset.prod_congr rfl step,
    prod_telescope (fun i => Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k)
      (fun i => val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J')]
  simp only [hN, pow_zero]
  rw [mul_comm, ← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.ThetaPowConj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem isActOf_of_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  intro S S' A A' _ _ L L' hL hL' T T' f _ k θ θ' Ψ hT H σ σ' τ τ' hσ hσ' hact
  refine GlobalTheory.ThetaNu.isActOf_of_sval hL fun y J hJ => ?_
  choose J' hJ' using fun χ : (T ⊗ A).left ⟶ A'.left => exists_chart hL' (χ y)
  have gJ' : Good L' y J' := hJ'
  have e1 := hσ' _ (inv f) y J J' hJ gJ'
  have e2 := twist_val hact (inv f) y gJ'
  have e3 := H _ (inv f) y J J' hJ gJ'
  have e4 := hσ _ (inv f ≫ (translT A' θ'.pt).left) y J J' hJ gJ'
  have c : (inv f ≫ (translT A' θ'.pt).left) ≫ f = 𝟙 _ ≫ (translT A θ.pt).left := by
    rw [Category.assoc, ← hT, ← Category.assoc, IsIso.inv_hom_id]
  rw [IsIso.inv_hom_id] at e1 e3
  rw [c] at e4
  rw [e1, e2, e4, e3]
  generalize Ψ (inv f ≫ (translT A' θ'.pt).left) y J J' ^ k = a
  generalize Ψ (inv f) y J J' ^ k = b
  generalize val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ (inv f) y J' = v
  generalize sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ
    (inv f ≫ (translT A' θ'.pt).left) y J' = w
  rw [Units.val_mul, Units.val_mul]
  linear_combination (-(b.val * v.val * w)) * a.mul_inv

end GlobalTheory.ThetaMove
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RosZeroLeft

theorem val_lift_one_left : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB →
    IsAbelianScheme A → ∀ (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ (T : Over S) (y : T ⟶ A) (z : T.left) (J : (T.left ⟶ A.left) → L.ι), Good L z J →
      val u (lift (1 : T ⟶ A) y).left z J = 1 := by
  intro S A _ _ L hL hA f g _ _ u hu h₀ T y z J hJ
  have one_isGen : (LB.oneGen L (Y := A.left)).IsGen :=
    isGen_of_gm _ fun _ _ _ _ _ =>
      (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)))
  have key := gen_unique' hL (u := LB.pullGen L _ _ u (lift (1 : A ⟶ A) (𝟙 A)).left)
    (u' := LB.oneGen L) (fun U _ h => by
      refine (Fintype.prod_empty _).trans (Eq.symm ((prod_ros f g 1 (𝟙 A) h).trans ?_))
      rw [MonObj.one_comp, _root_.one_mul, _root_.one_mul, Category.id_comp]
      simp)
    A.hom η[A].left (Over.w η[A]) (GlobalTheory.globalFns_holds _ _ hA).2 (DVR.pullGen_isGen _ _ _ _ hu _)
    one_isGen (fun y I hI => by
      have := val_corr hI h₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at this
      rw [val_pull hI, val_one, ← Over.comp_left]
      have e : η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) = lift η[A] η[A] := by simp [Hom.one_def]
      rw [e]; exact this) _ y.left z J hJ
  rw [val_pull hJ, val_one, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] at key
  exact key

end GlobalTheory.RosZeroLeft
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwoTorsTr

theorem tr_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G)
    (ha : a ^ 2 = 1) : ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (((toUnit G ≫ a) * 𝟙 G) ≫ toUnit G) (toUnit G),
    Category.comp_id, ← _root_.mul_assoc, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one, _root_.one_mul]

end GlobalTheory.TwoTorsTr

namespace GlobalTheory.TwoTorsTr

theorem secPull_invol {X : Scheme.{0}} (L L₂ : LB X) (hL : L.IsLB) (hL₂ : L₂.IsLB) (τ : X ⟶ X) (ττ : τ ≫ τ = 𝟙 X)
    (wL : LB.Iso L₂ (L.pull τ)) (hw : wL.IsGen) (σ : H0 L 1) : ∃ σ₂ : H0 L₂ 1,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧
    ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  have hc : ∀ κ : Fin 1, (fun _ : Fin 1 => 𝟙 X) κ ≫ τ = τ ≫ (fun _ : Fin 1 => 𝟙 X) κ := fun _ => by
    simp only [Category.id_comp, Category.comp_id]
  obtain ⟨σ₂, hσ₂, -⟩ := SecPull.existsUnique_secPull _ _ _ _ L L₂ τ hL hL₂ wL hw (Fin 1)
    (fun _ => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N' := by
    intro Z r z N N' hN hN'
    have := ExpTrans.sec_val wL (fun _ : Fin 1 => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ σ₂
      r z (hσ₂ Z r z) hN hN'
    rw [this, Fin.prod_univ_one, zpow_natCast, pow_one, ExpTrans.om, Category.comp_id]
  refine ⟨σ₂, key, fun h0 j => ?_⟩
  refine ThetaScalar.eq_zero_of_sval hL σ (fun y J hJ => ?_) j
  choose J' hJ' using fun ψ : X ⟶ X => exists_chart hL₂ (ψ y)
  have e := key X τ y J J' hJ hJ'
  rw [ττ, ThetaScalar.sval_eq_zero σ₂ h0 τ y hJ', MulZeroClass.mul_zero] at e
  exact e

end GlobalTheory.TwoTorsTr

namespace GlobalTheory

theorem twoTors_secPull : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  intro R _ G _ _ L L₂ hL hL₂ a ha wL hw σ
  exact TwoTorsTr.secPull_invol L L₂ hL hL₂ _
    (by rw [← Over.comp_left, TwoTorsTr.tr_tr G a ha, Over.id_left]) wL hw σ

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.UU.expT_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  intro R _ _ I D A G _ _ U k q σ τ f g hσ hf hE e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hB => ?_⟩
  obtain ⟨H1, H2⟩ := hs Z x rG rB h1 h2 h3 z JG J hG hB
  have hc : cst (rB ≫ (𝟙_ _ ⊗ D.P.A).hom) z q = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q := by
    rw [← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A), ← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G),
      ← Category.assoc, ← Category.assoc, h3]
  have hF : ∀ α, sval (f α) rB z J = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval (g α) rB z J := fun α => by
    rw [← hc]
    exact GlobalTheory.secIsMul_gs (hf α) rB z _ (hB.mem _ _)
  have hS : sval σ rG z JG = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval τ rG z JG :=
    GlobalTheory.secIsMul_gs hσ rG z _ (hG.mem _ _)
  refine ⟨fun α hα => by rw [hF, H1 α hα, mul_zero], ?_⟩
  rw [hS, mul_left_comm, H2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [hF, _root_.mul_assoc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secIsMul_of_germ_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  intro R _ _ X p hp L s q hq h
  haveI : Flat (X := X) (Y := Sp R) p := hp
  have loc : ∀ j, ∃ g : Γ(X, L.U j), s.f j = constFn p (L.U j) q * g := fun j =>
    exists_div p hq (L.U j) (s.f j) (fun x hx => h x j hx)
  choose t ht using loc
  have hg : ∀ j (x : X), x ∈ L.U j → gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * gs (𝟙 X) x (L.U j) (t j) := by
    intro j x hx
    rw [ht j, gs_mul _ _ _ hx, gs_constFn p (L.U j) (𝟙 X) x hx, Category.id_comp]
  refine ⟨⟨t, fun i j => ?_⟩, fun j => ?_⟩
  · refine fn_ext fun x hx => ?_
    have e := congrArg (gs (𝟙 X) x (L.U i ⊓ L.U j)) (s.compat i j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e ⊢
    rw [hg i x hx.1, hg j x hx.2, mul_left_comm] at e
    exact cst_regular p x hq e
  · exact ht j

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.QkMul

open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qk_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k d : ℕ) (p : QkPt D.toPre F k), ∃ q : QkPt D.toPre F (k * d), q.y = d • p.y ∧ q.g = p.g := by
  intro R _ _ _ D F _ _ k d p
  refine ⟨qkMk D.tau_bimult (d • p.y) p.g ?_, rfl, rfl⟩
  rw [mul_nsmul, qk_nsmul D.tau_bimult, map_nsmul]

end GlobalTheory.Mum.QkMul
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

def mixφ {R : Type} [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X) :
    PUnit.{1} ⊕ Fin 4 → (D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) :=
  Sum.elim (fun _ => b.left ≫ coprod.inr) (fun k => D₁.famφB α k ≫ coprod.inl)

end GlobalTheory.Mum.Two.Mix
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.morphism_eq_of_eq_on_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  first | exact @GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | exact GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | (intros; apply GlobalTheory.FormalAlg.hom_eq_of_reductions_eq <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_baseMul_section_of_germ_dvd_flat_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  first | exact @GlobalTheory.Mum.exists_secIsMul_of_germ_dvd | exact GlobalTheory.Mum.exists_secIsMul_of_germ_dvd | (intros; apply GlobalTheory.Mum.exists_secIsMul_of_germ_dvd <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_levelPoint_mul_level : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k d : ℕ) (p : QkPt D.toPre F k), ∃ q : QkPt D.toPre F (k * d), q.y = d • p.y ∧ q.g = p.g := by
  first | exact @GlobalTheory.Mum.QkMul.exists_qk_mul | exact GlobalTheory.Mum.QkMul.exists_qk_mul | (intros; apply GlobalTheory.Mum.QkMul.exists_qk_mul <;> assumption)

end
end
