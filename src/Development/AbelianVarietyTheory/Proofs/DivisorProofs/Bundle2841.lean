module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_ratio_gen {X A : Scheme.{0}} {M : LB X} {L₀ : LB A} (hM : M.IsLB) (hL₀ : L₀.IsLB)
    {K : Type} [Fintype K] (φ : K → (A ⟶ X)) (ε : K → ℤ) (F : A ⟶ X)
    (w : LB.Iso L₀ (LB.LinComb M φ ε)) (hw : w.IsGen) (W : LB.Iso L₀ (M.pull F)) (hW : W.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb M (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1))), τ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (J : (Z ⟶ X) → M.ι) (j' : L₀.ι), Good M z J → r z ∈ L₀.U j' →
        val τ r z J = gv w r z (fun k => J (r ≫ φ k)) j' * (gw W r z (J (r ≫ F)) j')⁻¹ := by
  classical
  have pW := (isGen_iff W).1 hW
  have l1 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (LB.LinComb M φ ε).U (j ∘ Sum.inl) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy.1 (Sum.inl i), hy.2⟩
  have l2 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (M.pull F).U (fun _ => j (Sum.inr PUnit.unit)) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 (Sum.inr PUnit.unit), hy.2⟩
  let u : ∀ (j : K ⊕ PUnit → M.ι) k, Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k)ˣ := fun j k =>
    res (l1 j k) (w.s (j ∘ Sum.inl, k)) * (res (l2 j k) (W.s (fun _ => j (Sum.inr PUnit.unit), k)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k →
      gm r z _ (u j k) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg _ (gm_res r z _ hz _))))
  have rel : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (j j' : K ⊕ PUnit → M.ι) (k k' : L₀.ι),
      r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j → r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j' →
      r z ∈ L₀.U k → r z ∈ L₀.U k' →
      gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ =
        trF (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1)) r z j j' *
          (gv w r z (j' ∘ Sum.inl) k' * (gw W r z (j' (Sum.inr PUnit.unit)) k')⁻¹) := by
    intro Z r z j j' k k' hj hj' hk hk'
    have key : ∀ {G : Type} [CommGroup G] (a c d x y : G), a * c⁻¹ * x * (d * c⁻¹ * y)⁻¹ = a * d⁻¹ * (x * y⁻¹) :=
      fun a c d x y => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    have a₁ : r z ∈ (LB.LinComb M φ ε).U (j ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj (Sum.inl i)
    have a₂ : r z ∈ (LB.LinComb M φ ε).U (j' ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj' (Sum.inl i)
    have b₁ : F (r z) ∈ M.U (j (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj (Sum.inr PUnit.unit)
    have b₂ : F (r z) ∈ M.U (j' (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj' (Sum.inr PUnit.unit)
    have e := gm_linComb M φ ε r z _ _ a₁ a₂
    rw [gm_isGen hw r z _ _ k k' a₁ a₂ hk hk', pW Z r z _ _ k k' b₁ b₂ hk hk']
    erw [e]
    rw [trF, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, zpow_neg, zpow_one]
    exact key _ _ _ _ _
  have glue : ∀ j : K ⊕ PUnit → M.ι, ∃ s : Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j)ˣ,
      ∀ k, res (inf_le_left : LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤ _) s = u j k := fun j =>
    glue_unit _ (fun k => LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL₀ y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) (u j)
      (fun k k' y hy => by
        rw [hu _ _ y j k hy.1, hu _ _ y j k' hy.2, rel _ (𝟙 A) y j j k k' hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hM _ _ (𝟙 A) y hy.1.1, _root_.one_mul])
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j →
      r z ∈ L₀.U k → gm r z _ (s j) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hj hk => (gm_res r z _ (show r z ∈ _ ⊓ L₀.U k from ⟨hj, hk⟩) (s j)).symm.trans
      ((congrArg (gm r z _) (hs j k)).trans (hu Z r z j k ⟨hj, hk⟩))
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z J j' hJ hj' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL₀ y
    exact (hv _ (𝟙 A) y j k hj hk).trans ((rel _ (𝟙 A) y j j' k k hj hj' hk hk).trans
      (congrArg _ (hv _ (𝟙 A) y j' k hj' hk).symm))
  · exact hv Z r z _ j' (hJ.mem _ r) hj'

end GlobalTheory.MumCmp.TwRatio

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_twist_ratio : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε)) (hw : w.IsGen)
    (W : LB.Iso D₀.P.L (D.P.L.pull (GlobalTheory.MumCmp.twφ D₀ D β b 0))) (hW : W.IsGen),
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D₀.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (j' : D₀.P.L.ι),
        Geo.Tor.Good D.P.L z J → r z ∈ D₀.P.L.U j' →
        Geo.Tor.gv w r z (fun i => J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b i)) j' =
          Geo.Tor.gw W r z (J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b 0)) j' * Geo.Tor.val ν (r ≫ D₀.P.A.hom) z J := by
  intro R _ _ _ D₀ D β b w hw W hW
  classical
  obtain ⟨τ, hτ, vτ⟩ := exists_ratio_gen D.P.isLB D₀.P.isLB (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε
    (GlobalTheory.MumCmp.twφ D₀ D β b 0) w hw W hW
  obtain ⟨t₀, ht₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]
  have hF : FormEq (Sum.elim (GlobalTheory.MumCmp.twφ D₀ D β b) (fun _ : PUnit => GlobalTheory.MumCmp.twφ D₀ D β b 0))
      (Sum.elim GlobalTheory.MumCmp.twε (fun _ => -1))
      (fun k => D₀.P.A.hom ≫ (![b.left, η[D.P.A].left] : Fin 2 → ((𝟙_ (Over (Sp R))).left ⟶ D.P.A.left)) k)
      ![-1, 1] := by
    intro U _ h
    have e1 : GlobalTheory.MumCmp.twφ D₀ D β b 1 = D₀.P.A.hom ≫ b.left := rfl
    have e2 : GlobalTheory.MumCmp.twφ D₀ D β b 2 = D₀.P.A.hom ≫ η[D.P.A].left := rfl
    rw [Fintype.prod_sum_type, Fin.prod_univ_three, Fin.prod_univ_two]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, e1, e2, GlobalTheory.MumCmp.twε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen D.P.isLB hF τ hτ
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio D.P.isLB hτ' (DVR.pullGen_isGen _ _ _ t₀ ht₀ D₀.P.A.hom)
  have hG := GlobalTheory.globalFns_holds _ D₀.P.A D₀.P.isAb
  obtain ⟨c, hc⟩ := hG.2 a.val
  obtain ⟨c', hc'⟩ := hG.2 (a⁻¹).val
  have hcc : c * c' = 1 := hG.1 (by rw [map_mul, hc, hc', Units.mul_inv, map_one])
  let cu : Γ(Sp R, ⊤)ˣ := ⟨c, c', hcc, (mul_comm c' c).trans hcc⟩
  have hcu : pullU D₀.P.A.hom ⊤ cu = a := Units.ext hc
  obtain ⟨ν, hν, vν⟩ := GlobalTheory.TorsionTranslate.exists_scale t₀ ht₀ cu
  refine ⟨ν, hν, fun Z r z J j' hJ hj' => ?_⟩
  have e1 := vτ Z r z J j' hJ hj'
  have e2 := vτ' Z r z J hJ
  have e3 := ha Z r z J hJ
  have e4 := val_pull hJ t₀ D₀.P.A.hom r
  have e5 := vν Z (r ≫ D₀.P.A.hom) z J hJ
  have e6 : gm r z ⊤ a = gm (r ≫ D₀.P.A.hom) z ⊤ cu := by
    rw [← hcu]; exact gm_pull r D₀.P.A.hom z ⊤ trivial cu
  rw [e5, ← e6, ← e4, ← e3, e2, e1, mul_left_comm, mul_inv_cancel, _root_.mul_one]

end GlobalTheory.MumCmp.TwRatio
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ExpandNonzero

open ReciprocityTheory.ChartRestriction.G.Semi

theorem mem_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (y : Y) : y ∈ LB.wchart L φ j ↔ ∀ k, (φ k).base y ∈ L.U (j k) := by
  show y ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X) ↔ _
  exact Set.mem_iInter

theorem sec_mem_basicOpen {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) (i j : L.ι) {x : X}
    (hx : x ∈ X.basicOpen (s.f j)) (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  have hxj : x ∈ L.U j := X.basicOpen_le _ hx
  have h := congrArg X.basicOpen (s.compat i j)
  simp only [Scheme.basicOpen_res, Scheme.basicOpen_mul,
    Scheme.basicOpen_of_isUnit _ (L.g i j).isUnit] at h
  have hm : x ∈ (L.U i ⊓ L.U j) ⊓ ((L.U i ⊓ L.U j) ⊓ X.basicOpen (s.f j)) :=
    ⟨⟨hi, hxj⟩, ⟨hi, hxj⟩, hx⟩
  rw [← h] at hm
  exact hm.2

theorem nonzero_of_expandsAt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (k : ℕ) (s : H0 U.LG.L k)
      (f : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt 0 k s f →
      (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) →
      ∀ y : (thickObj R (maximalIdeal R) 0 G).left,
      (∃ j : Fin 4 → D.toPre.P.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((U.gt 0).pG.left.app _).hom ((f 0).f j))) →
      ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  intro R _ _ _ D A G _ _ U k s f hexp hzero y hy
  classical
  obtain ⟨j, hj⟩ := hy
  obtain ⟨S, hS, hE⟩ := hexp
  have hcovM : ∀ ψ : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left,
      ∃ i, ψ.base y ∈ D.toPre.P.L.U i := fun ψ => by
    have : ψ.base y ∈ ⨆ i, D.toPre.P.L.U i := by rw [D.toPre.P.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨iL, hiL⟩ : ∃ i, (fstG (maximalIdeal R) 0 G).left.base y ∈ U.LG.L.U i := by
    have : (fstG (maximalIdeal R) 0 G).left.base y ∈ ⨆ i, U.LG.L.U i := by
      rw [U.LG.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  let idx : ((thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι :=
    fun ψ => (hcovM ψ).choose
  have hidx : ∀ ψ, ψ.base y ∈ D.toPre.P.L.U (idx ψ) := fun ψ => (hcovM ψ).choose_spec
  refine ⟨fun _ => iL, ?_⟩
  have h0S : (0 : D.toPre.X) ∈ S := by
    by_contra h
    have h' := hS 0 h j
    rw [h', Scheme.basicOpen_zero] at hj
    exact hj
  have key := hE (fun _ => idx (U.gt 0).pG.left, fun _ => iL) (fun _ => iL)
    (fun α i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB α i))
    (fun α i => idx (D.toPre.Oφ (U.gt 0).pG α i)) rfl (by
      intro a b hab
      rcases a with _ | (a | a) <;> rcases b with _ | (b | b) <;> exact congrArg idx hab)

  have hyW : y ∈ U.expW 0 (fun _ => idx (U.gt 0).pG.left, fun _ => iL) (fun _ => iL) S
      (fun α i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB α i))
      (fun α i => idx (D.toPre.Oφ (U.gt 0).pG α i)) := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact (mem_wchart _ _ _ y).2 fun _ => hidx _
    · exact (mem_wchart _ _ _ y).2 fun _ => hiL
    · show (fstG (maximalIdeal R) 0 G).left.base y ∈ LB.wchart _ _ _
      exact (mem_wchart _ _ _ _).2 fun _ => hiL
    · refine Finset.inf_induction
        (p := fun V : (thickObj R (maximalIdeal R) 0 G).left.Opens => y ∈ V)
        (show y ∈ (⊤ : (thickObj R (maximalIdeal R) 0 G).left.Opens) from trivial)
        (fun a ha b hb => TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩) fun α _ =>
          TopologicalSpace.Opens.mem_inf.2 ⟨?_, ?_⟩
      · show (U.gt 0).pG.left.base y ∈ LB.wchart _ _ _
        exact (mem_wchart _ _ _ _).2 fun i => hidx ((U.gt 0).pG.left ≫ D.toPre.famφB α i)
      · exact (mem_wchart _ _ _ y).2 fun i => hidx _

  have hf0 : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
      (((U.gt 0).pG.left.app _).hom
        ((f 0).f (fun i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB 0 i)))) := by
    rw [← Scheme.preimage_basicOpen] at hj ⊢
    exact sec_mem_basicOpen (f 0) _ j hj
      ((mem_wchart _ _ _ _).2 fun i => hidx ((U.gt 0).pG.left ≫ D.toPre.famφB 0 i))
  rw [Finset.sum_eq_single ⟨0, h0S⟩ (fun b _ hb => by
      have hb' : b.1 ≠ 0 := fun h => hb (Subtype.ext h)
      refine mul_eq_zero_of_left ?_ _
      exact (congrArg _ (hzero b.1 hb' _)).trans (map_zero _))
    (fun h => absurd (Finset.mem_attach _ _) h)] at key
  have hL := (congrArg (fun a => y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen a) key).mpr (by
    simp only [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _),
      Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf]
    exact ⟨⟨hyW, hf0⟩, hyW⟩)
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((Units.isUnit _).pow k),
    Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf] at hL
  exact hL.2.2

end GlobalTheory.Mum.ExpandNonzero
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_gen_up : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) [IsIso f] (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k])) (hu' : u'.IsGen), ∃ u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  intro XA XP XG XT Y Y' LA LP LG LT hA hP hG hT α β c wA hwA ℓ hℓ w hw f _ sA mA sT mT e' h₁ h₂ h₃ k u' hu'
  obtain ⟨t1, ht1, v1⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff w).1 hw) hG hT (φ' := ![sT, mT])
    (ε := ![k, -k]) u' hu'
  obtain ⟨t2, ht2, v2⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff ℓ).1 hℓ) hP hG
    (φ' := fun i => ![sT, mT] i ≫ c) (ε := ![k, -k]) t1 ht1
  have ht3 := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen LP _ _ t2 ht2 (inv f)
  have hfe : ∀ i, inv f ≫ (![sT, mT] i ≫ c) ≫ β = ![sA, mA] i ≫ α := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Category.assoc, ← h₁, IsIso.inv_hom_id_assoc]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc]
      rw [← h₂, Category.assoc, ← h₁, reassoc_of% h₃, IsIso.inv_hom_id_assoc]
  obtain ⟨t4, ht4, v4⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hP (φ' := fun i => ![sA, mA] i ≫ α) (ε' := ![k, -k])
    (fun U _ h => by simp only [hfe]) _ ht3
  obtain ⟨u, hu, v5⟩ := GlobalTheory.ArcPull.exists_down_om hwA hP hA (φ' := ![sA, mA]) (φ := fun i => ![sA, mA] i ≫ α)
    (𝟙 Y) (fun i => (Category.id_comp _).symm) t4 ht4
  refine ⟨u, hu, fun Z q z JP JA JG Jt gP gA gG gT => ?_⟩
  have e5 := v5 Z (q ≫ f) z JP JA gP gA
  have e4 := v4 Z ((q ≫ f) ≫ 𝟙 Y) z JP gP
  have e3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull gP t2 (inv f) ((q ≫ f) ≫ 𝟙 Y)
  have hq : ((q ≫ f) ≫ 𝟙 Y) ≫ inv f = q := by simp
  rw [hq] at e3
  have e2 : val t2 q z JP = pw ℓ (fun i => ![sT, mT] i ≫ c) ![k, -k] q z _ _ * val t1 q z JG :=
    v2 Z q z _ _ (gP.mem _ q) (gG.mem _ q)
  have e1 : val t1 q z JG = pw w ![sT, mT] ![k, -k] q z _ _ * val u' q z Jt := v1 Z q z _ _ (gG.mem _ q) (gT.mem _ q)
  have h₄ : f ≫ mA ≫ α = mT ≫ c ≫ β := by rw [← reassoc_of% h₃, h₁, reassoc_of% h₂]
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, GlobalTheory.ArcPull.om, tf, Category.assoc, Category.comp_id] at e1 e2 e3 e4 e5 ⊢
  have p₁ : q ≫ f ≫ sA ≫ α = q ≫ sT ≫ c ≫ β := by rw [h₁]
  have p₄ : q ≫ f ≫ mA ≫ α = q ≫ mT ≫ c ≫ β := by rw [h₄]
  have p₃ : q ≫ e' ≫ f ≫ sA = q ≫ f ≫ mA := by rw [h₃]
  have p₂ : q ≫ e' ≫ sT = q ≫ mT := by rw [h₂]
  have p₂' : q ≫ e' ≫ sT ≫ c = q ≫ mT ≫ c := by rw [reassoc_of% h₂]
  have p₂'' : q ≫ e' ≫ sT ≫ c ≫ β = q ≫ mT ≫ c ≫ β := by rw [reassoc_of% h₂]
  rw [e4, e3, e2, e1, p₁, p₄] at e5
  rw [p₃, p₂'', p₂', p₂]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e5
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FieldVA

variable {X : Scheme.{0}}

theorem nonzeroLocus_pullPow (L : LB X) (N : ℕ) (t : (lbPow L N).Sec) :
    nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 X) t) = nonzeroLocus t := by
  apply le_antisymm
  · refine iSup_le fun j y hy => ?_
    have hy' : y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _ (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) j)).hom
        (t.f (fun _ => j 0))) := hy
    rw [Scheme.basicOpen_appLE] at hy'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hy'.2⟩
  · refine iSup_le fun j y hy => ?_
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j PUnit.unit, ?_⟩
    have hc : y ∈ (lbPow L N).U j := X.basicOpen_le (t.f j) hy
    show y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _
      (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) (fun _ => j PUnit.unit))).hom (t.f (fun _ => j PUnit.unit)))
    rw [Scheme.basicOpen_appLE]
    exact ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc PUnit.unit, hy⟩

end GlobalTheory.Mum.FieldVA

namespace GlobalTheory.Mum


open GlobalTheory.Mum.FieldVA in
theorem veryAmpleAlong_field (hA : AmpleSt) (K : Type) [Field K] (P : PolAV (Sp K)) :
    ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  obtain ⟨m, t, hcov, hs⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow hA K P 4 le_rfl
  have hb : ∀ i, nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) :=
    fun i => nonzeroLocus_pullPow P.L 4 (t i)
  refine ⟨m, fun i => GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i), ?_, fun i => ?_⟩
  · refine _root_.top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y ∈ ⨆ i ∈ Set.univ, nonzeroLocus (t i) by rw [hcov]; trivial)
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, show y ∈ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) by
      rw [hb]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i (Set.mem_univ i)
  have hW : (𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) := by
    rw [← hb i]; exact le_antisymm (fun y hy => hy) (fun y hy => hy)
  have le1 := hW.le
  have le2 := hW.ge
  have hconst : ∀ a, resG P.A.left le1 (constFn P.A.hom (nonzeroLocus (t i)) a) =
      AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := by
    intro a
    have h2 : constFn P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a =
        AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := rfl
    refine (fn_ext fun x hx => ?_).trans h2
    rw [gs_res _ x le1 hx, gs_constFn _ _ _ _ (le1 hx), gs_constFn _ _ _ _ hx]
  refine ⟨by rw [hW]; exact haff, fun j => resG P.A.left le1 (r j), fun j c a ha hc => ?_, ?_⟩
  · have hc' : a ∈ (lbPow P.L 4).U (fun _ => c 0) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc 0
    have key : ∀ s : (lbPow P.L 4).Sec, secGerm (𝟙 P.A.left) a (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) s) c =
        gs (𝟙 P.A.left) a ((lbPow P.L 4).U (fun _ => c 0)) (s.f (fun _ => c 0)) := fun s =>
      (gs_appLE (𝟙 P.A.left) _ _ _ (𝟙 P.A.left) a hc _).trans
        (congrArg (fun q => gs q a _ (s.f (fun _ => c 0))) (Category.id_comp _))
    have hm : (𝟙 P.A.left) a ∈ nonzeroLocus (t i) ⊓ (lbPow P.L 4).U (fun _ => c 0) := ⟨le1 ha, hc'⟩
    have e := congrArg (gs (𝟙 P.A.left) a _) (hr j (fun _ => c 0))
    rw [gs_res _ a _ hm, gs_mul _ a _ hm, gs_res _ a _ hm, gs_res _ a _ hm] at e
    rw [key, key, gs_res _ a le1 ha]
    exact e
  · have hρ : ∀ f, resG P.A.left le1 (resG P.A.left le2 f) = f := fun f => fn_ext fun x hx => by
      rw [gs_res _ x le1 hx, gs_res _ x le2 (le1 hx)]
    have hcl : Subring.closure (Set.range (constFn P.A.hom (nonzeroLocus (t i))) ∪ Set.range r) ≤
        (MvPolynomial.eval₂Hom (AbLaw.cst P.A.hom
          ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))))
          (fun j => resG P.A.left le1 (r j))).range.comap (resG P.A.left le1) := by
      refine Subring.closure_le.2 ?_
      rintro g (⟨a, rfl⟩ | ⟨j, rfl⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.C a, by
          rw [MvPolynomial.eval₂Hom_C]; exact (hconst a).symm⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.X j, by rw [MvPolynomial.eval₂Hom_X']⟩)
    intro f
    obtain ⟨p, hp⟩ := RingHom.mem_range.1 (Subring.mem_comap.1
      (hcl (hsurj ▸ Subring.mem_top (resG P.A.left le2 f))))
    exact ⟨p, hp.trans (hρ f)⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum

theorem sections_move_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k m : ℕ}, 1 ≤ k → ∀ (b : Fin (m + 1) → H0 A.L k), ∃ (σ : Fin (m + 1) → H0 U.LG.L k) (c : Fin (m + 1) → (FractionRing R)ˣ), ∀ (y : ↥(pullback G.hom (jK R))) (j : Fin 1 → U.LG.L.ι) (jA : Fin 1 → A.L.ι), pullback.fst G.hom (jK R) y ∈ U.LG.L.U (j 0) → U.gen.hom.left y ∈ A.L.U (jA 0) → ∃ u : ((pullback G.hom (jK R)).presheaf.stalk y)ˣ, ∀ i, secGerm (pullback.fst G.hom (jK R)) y (σ i) j = u.val * gs (pullback.snd G.hom (jK R)) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i : FractionRing R)) * secGerm (show pullback G.hom (jK R) ⟶ A.A.left from U.gen.hom.left) y (b i) jA := by
  intro R _ _ I D A G _ _ U k m hk b
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨w', hw', -⟩ := GlobalTheory.Algebraise.exists_swap _ _ w hw (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
  choose s hs using fun i => GlobalTheory.Algebraise.exists_down A.isLB U.LG.isLB U.gen.hom.left
    (pullback.fst G.hom (jK R)) w' hw' (b i)
  choose c' σ hc' hσ using fun i => GlobalTheory.FormalGeneric.exists_integral U hk (s i)
  refine ⟨σ, fun i => Units.mk0 (algebraMap R (FractionRing R) (c' i))
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hc' i)), fun y j jA hj hjA => ?_⟩
  refine ⟨(gw w' (𝟙 _) y (jA 0) (fun _ => j 0) ^ k)⁻¹, fun i => ?_⟩
  have e₁ := hs i _ (𝟙 _) y (jA 0) (j 0) hjA hj
  have e₂ := hσ i _ (𝟙 _) y (j 0) hj
  have hc : cst (pullback.snd G.hom (jK R) ≫ jK R) y (c' i) = gs (pullback.snd G.hom (jK R)) y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) (c' i))) :=
    (gs_pull _ (jK R) y ⊤ trivial _).symm.trans
      (congrArg (gs _ y ⊤) (GlobalTheory.FormalGeneric.appTop_spec (algebraMap R (FractionRing R)) (c' i)))
  rw [Category.id_comp] at e₁ e₂
  rw [Category.id_comp, hc] at e₂
  rw [GlobalTheory.Algebraise.fin_one_const j, GlobalTheory.Algebraise.fin_one_const jA]
  change GlobalTheory.SectionRingIso.vl (σ i) _ y _ = _ * _ * GlobalTheory.SectionRingIso.vl (b i) _ y _
  rw [e₂, e₁, Units.val_mk0, ← Units.val_pow_eq_pow_val]
  generalize gw w' (𝟙 _) y (jA 0) (fun _ => j 0) ^ k = v
  rw [_root_.mul_assoc, mul_left_comm _ v.val, Units.inv_mul_cancel_left]
  rfl

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.isogeny_representable_finite_etale : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (B : Over Y.left) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧ IsQuasiInv k ψ ψ' ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsQuasiInv k ψ₁ ψ₁' → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (θ : A₁.left ⟶ A₀.left) (θ' : B₁.left ⟶ B.left), θ ≫ φ₀ = φ₁ ∧ IsGrpPullback A₁ A₀ y θ ∧ IsGrpPullback B₁ B y θ' ∧ θ ≫ ψ.left = ψ₁.left ≫ θ' := by
  first | exact @GlobalTheory.UPel.HT.ES.IsogRep.isogeny_rep | exact GlobalTheory.UPel.HT.ES.IsogRep.isogeny_rep | exact @GlobalTheory.UPel.HT.ES.IsogRep.ker_iff_of_pullbacks | exact GlobalTheory.UPel.HT.ES.IsogRep.ker_iff_of_pullbacks | exact @GlobalTheory.UPel.HT.ES.IsogRep.exists_quot_quasiInv | exact GlobalTheory.UPel.HT.ES.IsogRep.exists_quot_quasiInv
end
