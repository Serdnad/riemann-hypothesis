module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {X X' Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem sec_of_units {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X')}
    {ε' : K' → ℤ} (u : ∀ p q, Γ(Y, LB.wchart M φ p ⊓ LB.wchart M' φ' q)ˣ)
    (hu : ∀ (y : Y) p p' q q', y ∈ LB.wchart M φ p → y ∈ LB.wchart M φ p' → y ∈ LB.wchart M' φ' q → y ∈ LB.wchart M' φ' q' →
      gm (𝟙 Y) y _ (u p q) * trF φ ε (𝟙 Y) y p p' = trF φ' ε' (𝟙 Y) y q q' * gm (𝟙 Y) y _ (u p' q'))
    (s : LB.Sec (LB.LinComb M φ ε)) : ∃ s' : LB.Sec (LB.LinComb M' φ' ε'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q,
      r z ∈ LB.wchart M φ p → r z ∈ LB.wchart M' φ' q →
      gs r z (LB.wchart M' φ' q) (s'.f q) = (gm r z _ (u p q)).val * gs r z (LB.wchart M φ p) (s.f p) := by
  have ch : ∀ y : Y, ∃ p, y ∈ LB.wchart M φ p := fun y => by
    choose p hp using fun k => exists_chart hM (φ k y)
    exact ⟨p, Set.mem_iInter.2 hp⟩
  let sp : ∀ p q, Γ(Y, LB.wchart M φ p ⊓ LB.wchart M' φ' q) := fun p q =>
    (u p q).val * (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart M φ p ⊓ LB.wchart M' φ' q ≤ LB.wchart M φ p)).op).hom (s.f p)
  have hv : ∀ {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) p q (h : r z ∈ LB.wchart M φ p ⊓ LB.wchart M' φ' q),
      gs r z _ (sp p q) =
        (gm r z _ (u p q)).val * gs r z (LB.wchart M φ p) (s.f p) := fun r z p q h =>
    (gs_mul r z _ h _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ h _) (gs_res r z _ h _))
  have tr : ∀ (y : Y) p p' q q', y ∈ LB.wchart M φ p → y ∈ LB.wchart M φ p' → y ∈ LB.wchart M' φ' q → y ∈ LB.wchart M' φ' q' →
      (gm (𝟙 Y) y _ (u p q)).val * gs (𝟙 Y) y (LB.wchart M φ p) (s.f p) =
        (trF φ' ε' (𝟙 Y) y q q').val * ((gm (𝟙 Y) y _ (u p' q')).val * gs (𝟙 Y) y (LB.wchart M φ p') (s.f p')) :=
    fun y p p' q q' a b c d => by
      rw [sec_trans s (𝟙 Y) y a b, ← _root_.mul_assoc, ← Units.val_mul, hu y p p' q q' a b c d, Units.val_mul, _root_.mul_assoc]
  have glue : ∀ q, ∃ f : Γ(Y, LB.wchart M' φ' q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p, r z ∈ LB.wchart M φ p →
      r z ∈ LB.wchart M' φ' q → gs r z _ f = (gm r z _ (u p q)).val * gs r z (LB.wchart M φ p) (s.f p) := fun q => by
    obtain ⟨f, hf, -⟩ := Y.sheaf.existsUnique_gluing' (fun p => LB.wchart M φ p ⊓ LB.wchart M' φ' q) (LB.wchart M' φ' q)
      (fun _ => homOfLE inf_le_right) (fun y hy => let ⟨p, hp⟩ := ch y; TopologicalSpace.Opens.mem_iSup.2 ⟨p, hp, hy⟩)
      (fun p => sp p q) fun p p' => fn_ext fun y hy =>
        ((gs_res _ y inf_le_left hy _).trans ((hv _ y p q hy.1).trans ((tr y p p' q q hy.1.1 hy.2.1 hy.1.2 hy.1.2).trans (by
          rw [trF_self hM' _ _ (𝟙 Y) y hy.1.2, Units.val_one, _root_.one_mul])))).trans
          ((gs_res _ y inf_le_right hy _).trans (hv _ y p' q hy.2)).symm
    exact ⟨f, fun Z r z p a b => (gs_res r z inf_le_right (show r z ∈ LB.wchart M φ p ⊓ LB.wchart M' φ' q from ⟨a, b⟩) f).symm.trans
      ((congrArg _ (hf p)).trans (hv r z p q ⟨a, b⟩))⟩
  choose f hf using glue
  refine ⟨⟨f, fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hf q Z r z p⟩
  obtain ⟨p, hp⟩ := ch y
  exact ((gs_res _ y _ hy _).trans ((hf q _ (𝟙 Y) y p hp hy.1).trans (tr y p p q q' hp hp hy.1 hy.2))).trans ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_linComb M' φ' ε' (𝟙 Y) y q q' hy.1 hy.2)))
      ((gs_res _ y _ hy _).trans (hf q' _ (𝟙 Y) y p hp hy.2)))).symm

variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
  {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
include hw hL hL'

theorem sec_upK (s : LB.Sec (LB.LinComb L' φ' ε)) : ∃ s' : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' → sval s' r z J =
      (pw w φ' ε r z (fun k => J (r ≫ φ' k ≫ F)) fun k => J' (r ≫ φ' k)).val * sval s r z J' := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have e : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q, r z ∈ LB.wchart L' φ' q ⊓ LB.wchart L (fun k => φ' k ≫ F) p →
      gm r z _ (res (inf_comm _ _).le (u p q)) = pw w φ' ε r z p q := fun Z r z p q h =>
    (gm_res r z _ h _).trans (hu p q Z r z ⟨h.2, h.1⟩)
  obtain ⟨s', hs⟩ := sec_of_units hL' hL (ε' := ε) (fun q p => res (inf_comm _ _).le (u p q)) (fun y q q' p p' a b c d => by
    rw [e _ _ y p q ⟨a, c⟩, e _ _ y p' q' ⟨b, d⟩, pw_trans hw φ' ε (𝟙 Y) y c d a b, _root_.mul_assoc, _root_.mul_assoc,
      mul_left_comm (trF φ' ε (𝟙 Y) y q q')⁻¹, inv_mul_cancel, _root_.mul_one]) s
  exact ⟨s', fun Z r z J J' hJ hJ' => (hs Z r z _ _ (hJ'.mem _ r) (hJ.mem _ r)).trans
    (congrArg (·.val * _) (e Z r z _ _ ⟨hJ'.mem _ r, hJ.mem _ r⟩))⟩

omit hw

variable {Y₀ : Scheme.{0}} {f₁ : Y₀ ⟶ X'} {f₂ : Y₀ ⟶ X} {W : LB.Iso (L'.pull f₁) (L.pull f₂)} (hW : W.IsGen)
  (m : K → (Y ⟶ Y₀)) {ψ : K → (Y ⟶ X')} (e : ∀ k, m k ≫ f₁ = ψ k)
include hW e

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

def SecBDvdSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
    ValOver ϖ (FractionRing V) vK →
    ∀ (k : ℕ) (α : D.toPre.X)
      (E : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))),
      VGe D (FractionRing V) vK k α E 0 → ∀ (r : V), r ≠ 0 → ∀ (f : D.toPre.SecB k α),
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) E (D.toPre.famφB α)
        (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left
        (scal (DegPre.BF D.toPre (FractionRing V)).hom r) →
      ∀ j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
        f.f j = constFn D.toPre.P.A.hom _ r * g

theorem gs_fsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ S, a i) = ∑ i ∈ S, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs, dif_pos h, map_sum]

theorem isUnit_gs_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (u : Γ(X, U)ˣ) (k : ℕ) :
    IsUnit (gs f y U (u.val ^ k)) := by
  simp only [gs, dif_pos h]
  exact ((u.isUnit.pow k).map _).map _

theorem dvd_of_eq_sum {P : Scheme.{0}} {x : P} {W : P.Opens} (hmem : x ∈ W) {κ : Type} {S : Finset κ}
    {a b : κ → Γ(P, W)} {L : Γ(P, W)} (c : P.presheaf.stalk x) (heq : L = ∑ i ∈ S, a i * b i)
    (h : ∀ i ∈ S, c ∣ gs (𝟙 P) x W (a i)) : c ∣ gs (𝟙 P) x W L := by
  have hx : (𝟙 P) x ∈ W := by first | exact hmem | simpa using hmem
  subst heq
  rw [gs_fsum (𝟙 P) x W hx]
  refine Finset.dvd_sum fun i hi => ?_
  have hm : gs (𝟙 P) x W (a i * b i) = gs (𝟙 P) x W (a i) * gs (𝟙 P) x W (b i) := by
    simp only [gs, dif_pos hx, map_mul]
  rw [hm]
  exact (h i hi).mul_right _

theorem nuExt_of (hB : SecBDvdSt) : NuExtSt := by
  intro V _ _ _ ϖ hϖ D Q hQ vK hv A G _ _ _ _ _ U k hk s E hexp hnu
  obtain ⟨r, hr0, σ, f, hsσ, hEf, hexpAt⟩ := hexp
  have hvge : ∀ α, VGe D (FractionRing V) vK k α (E.s α) 0 :=
    n1e V ϖ hϖ D Q hQ (FractionRing V) vK k E hnu
  have hfd : ∀ α j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
      (f α).f j = constFn D.toPre.P.A.hom _ r * g :=
    fun α => hB V ϖ hϖ D vK hv k α (E.s α) (hvge α) r hr0 (f α) (hEf α)
  choose g hg using hfd
  obtain ⟨n, hn⟩ := exists_pow_le_span hϖ hr0
  have hpw : (U.gt n).pG.left ≫ D.toPre.P.A.hom =
      pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom :=
    (Over.w (U.gt n).pG).trans pullback.condition.symm
  have hpt : ∀ (j : Fin 1 → U.LG.L.ι) (x' : ↑(pullback G.hom (thick V (maximalIdeal V) n))),
      pullback.fst G.hom (thick V (maximalIdeal V) n) x' ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j →
      cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r ∣
        gs (pullback.fst G.hom (thick V (maximalIdeal V) n)) x' (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)
          (σ.f j) := by
    intro j x' hx'
    obtain ⟨S, -, hS⟩ := hexpAt n
    obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB x' (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    let pp : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
      (fun _ => J (U.gt n).pG.left, fun _ => j 0)
    let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α i => J ((U.gt n).pG.left ≫ D.toPre.famφB α i)
    let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α i => J (D.toPre.Oφ (U.gt n).pG α i)
    have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt n).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt n).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt n).pG a.1.1 a.2)))
        (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
      rintro (a | a | a) (b | b | b) h <;> exact congrArg J h
    have hj0 : pullback.fst G.hom (thick V (maximalIdeal V) n) x' ∈ U.LG.L.U (j 0) := Set.mem_iInter.1 hx' 0
    have hmem : x' ∈ U.expW n pp j S jf jt := by
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => hJ _, Set.mem_iInter.2 fun _ => hj0⟩, hx'⟩, ?_⟩
      refine Finset.inf_induction (p := fun O : (thickObj V (maximalIdeal V) n G).left.Opens => x' ∈ O) trivial
        (fun a ha b hb => ⟨ha, hb⟩) (fun α _ => ⟨Set.mem_iInter.2 fun i => hJ _, Set.mem_iInter.2 fun i => hJ _⟩)
    have heq := hS pp j jf jt rfl hcoh

    have hterm : ∀ α ∈ S, ∀ (h : U.expW n pp j S jf jt ≤ (U.gt n).pG.left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)),
        gs (𝟙 _) x' (U.expW n pp j S jf jt) (((thickObj V (maximalIdeal V) n G).left.presheaf.map
          (homOfLE h).op).hom (((U.gt n).pG.left.app _).hom ((f α).f (jf α)))) =
        cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r *
          (show (pullback G.hom (thick V (maximalIdeal V) n)).presheaf.stalk x' from
            gs (U.gt n).pG.left x' _ (g α (jf α))) := by
      intro α _ h
      have hxα : (U.gt n).pG.left x' ∈ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) := h hmem
      exact (gs_res (𝟙 _) x' h hmem _).trans ((gs_pull (𝟙 _) (U.gt n).pG.left x' _ hxα _).trans
        ((congrArg (fun q => gs q x' _ ((f α).f (jf α))) (Category.id_comp _)).trans
          ((congrArg (gs (U.gt n).pG.left x' _) (hg α (jf α))).trans ((gs_mul _ x' _ hxα _ _).trans
            (congrArg (· * _) ((gs_constFn D.toPre.P.A.hom _ _ x' hxα r).trans
              (congrArg (fun q => cst q x' r) hpw)))))))
    have hdv := dvd_of_eq_sum hmem (cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r) heq
      (fun α _ => (dvd_mul_right _ _).trans (dvd_of_eq (hterm α.1 α.2 _).symm))
    have hdv2 := hdv.trans (dvd_of_eq (gs_mul (𝟙 _) x' _ hmem _ _))
    have hdv3 := (IsUnit.dvd_mul_left (isUnit_gs_pow (𝟙 _) x' _ hmem _ k)).1 hdv2
    exact hdv3.trans (dvd_of_eq ((gs_res (𝟙 _) x' _ hmem _).trans ((gs_pull (𝟙 _) _ x' _ hx' _).trans
      (congrArg (fun q => gs q x' _ (σ.f j)) (Category.id_comp _)))))
  obtain ⟨σ', hσ'⟩ := exists_div_sec_of_thick G.hom (maximalIdeal V ^ (n + 1)) hr0 hn σ hpt
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have h1 := secScal_sval_c hsσ (𝟙 _) y hJ
  have hm := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ pullback.fst G.hom (jK V))
  have h2 : sval σ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom) y r * sval σ' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J :=
    (congrArg (gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y _) (hσ' _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg (· * _) (gs_constFn G.hom _ _ y hm r)))
  have hjK : ∀ a : V, (jK V).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) a) :=
    fun a => (congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))).symm
  have hcu : IsUnit (scal (pullback.snd G.hom (jK V) ≫ jK V) r) := by
    show IsUnit ((pullback.snd G.hom (jK V)).appTop.hom ((jK V).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)))
    rw [hjK]
    have hne : algebraMap V (FractionRing V) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hr0
    exact ((isUnit_iff_ne_zero.2 hne).map _).map _
  have hceq : gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) r) =
      cst ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom) y r :=
    (gs_pull (𝟙 _) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans
      (congrArg (fun q => gs q y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r))
        (by rw [Category.id_comp, Category.id_comp, pullback.condition]))
  have hgu : IsUnit (gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) r)) := by
    rw [gs_eq (𝟙 _) y ⊤ trivial]
    exact (hcu.map _).map _
  rw [hceq] at hgu
  have h3 := h2.symm.trans (h1.trans (congrArg (· * _) hceq))
  exact hgu.mul_left_cancel h3

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

section FE

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem trF_fst (mu : D.toPre.X) :
    (DegPre.trF D.toPre F mu).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left := by
  rw [← Over.comp_left]
  simp [DegPre.trF]

theorem trF_prB (mu : D.toPre.X) :
    (DegPre.trF D.toPre F mu).left ≫ (DegPre.prB D.toPre F).left =
      (DegPre.prB D.toPre F).left ≫ (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  simp only [DegPre.trF, CartesianMonoidalCategory.lift_snd, padd, CategoryTheory.Hom.mul_def, cQ,
    CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id, SemiCartesianMonoidalCategory.comp_toUnit_assoc]

theorem gs_gF_zF (y : (TF (R := V) F).left) (ζ : F) :
    gs (DegPre.zF D.toPre F).left y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have h := gs_pull (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ)
  have e : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left]
    simp [DegPre.zF]
  rw [e] at h
  rw [← h]
  rfl

theorem gs_scal_jFK (y : (TF (R := V) F).left) (c : FractionRing V) :
    gs (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y ⊤ (scal (𝟙 _) c) =
      gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (algebraMap (FractionRing V) F c)) := by
  have key : ((jFK (R := V) F).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (algebraMap (FractionRing V) F c) := by
    have := congrArg (fun φ => φ.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing V) F)))
    exact this.symm
  have h := gs_pull (𝟙 (TF (R := V) F).left) (jFK (R := V) F) y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c)
  have hs : scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c := by
    simp [scal]
  erw [hs, ← h]
  exact congrArg (gs (𝟙 (TF (R := V) F).left) y ⊤) key

theorem fe_move (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) (k : ℕ)
    (mu α : D.toPre.X) (s : Fam D.toPre F k) {r : ℚ} (hs : VGe D F v k α (s.s α) r) :
    VGe D F v k (α + k • mu) (s.s (α + k • mu)) (r + ((k * Q mu + bOf D.toPre Q mu α : ℤ) : ℚ)) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, hc₀, hval⟩ := famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := exists_eB D.toPre k α mu e' he' hC
  have hc0 : c₀ ≠ 0 := ne_zero_of_hasVal hϖ hc₀
  set c : F := algebraMap (FractionRing V) F c₀ with hc
  have hcne : c ≠ 0 := (map_ne_zero _).2 hc0
  let cU : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ :=
    ⟨gF D.toPre F c, gF D.toPre F c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hcne, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hcne, map_one]⟩
  let g0 : LB.Gen (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top cU⟩
  have hg0 : g0.IsGen := fun i j => by
    have hg : (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
      simp [LB.LinComb]; rfl
    calc res _ (g0.s i) = res _ (g0.s j) := (res_res' _ _ cU).trans (res_res' _ _ cU).symm
      _ = _ := by rw [hg, _root_.one_mul]
  have hformU : FormEq (Sum.elim (fun i => (DegPre.prB D.toPre F).left ≫ Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i) i) PEmpty.elim)
      (Sum.elim (DegPre.deltaε k) PEmpty.elim) (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k) := fun U _ h => by
    have e0 : ∀ f : PEmpty → U, ∏ i, f i = 1 := fun f => Fintype.prod_empty f
    rw [Fintype.prod_sum_type, e0, _root_.mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl, DegPre.deltaφ, GC.famφ_eq]
    · simp only [Sum.elim_inr, DegPre.deltaφ, GC.famφ_eq]
      rw [← Category.assoc, trF_prB, Category.assoc]
      rfl
  obtain ⟨u, hu, vu⟩ := exists_gen hL hformU
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ eB (DegPre.prB D.toPre F).left) g0)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ heB _) hg0)
  have hval_u : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J →
      (val u ρ z J).val = (val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val * gs ρ z ⊤ (gF D.toPre F c) := by
    intro Z ρ z J hJ
    rw [vu Z ρ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul]
    congr 1
    have hmem : ρ z ∈ LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim (fun k => J (ρ ≫ PEmpty.elim k)) :=
      Set.mem_iInter.2 fun k => k.elim
    exact (congrArg Units.val (gm_res ρ z le_top hmem cU)).trans (gs_unit ρ z ⊤ (by trivial) cU).symm
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hcorr : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F k mu α) := corr_of_val hL fun y J hJ => Units.ext (by
    have C : IsCub (cubV D.toPre.cub (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
    have E2 : val eB ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) y J =
        val e' (DegPre.jFR (R := V) F) y J := by
      have E1 := veB (TF (R := V) F) (DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F) y J hJ
      rw [z₂, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul] at E1
      have e3 : (1 : TF (R := V) F ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom = DegPre.jFR (R := V) F := Over.w _
      rw [e3] at E1
      have e4 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, z₂]
      rw [e4]; exact E1
    rw [val_pull hJ, Category.id_comp, hval_u _ _ y J hJ, hval F (TF (R := V) F).left (𝟙 (TF (R := V) F).left) y J hJ, E2, gs_gF_zF, gs_scal_jFK,
      Category.id_comp, ← hc]
    exact mul_comm _ _)
  have hrel := s.fe mu α u hu hcorr
  have hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)
      (Sum.elim (D.toPre.famφB (α + k • mu)) (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.toPre.famφB (α + k • mu)) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  refine vge_move (trF_fst mu) (trF_prB mu) u hrel eB heB hformB c (fun y J hJ => ?_) ?_ hs
  · rw [hval_u _ _ y J hJ, Category.id_comp]; exact mul_comm _ _
  · exact le_of_eq (hv c₀ _ hc₀).symm

end FE

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end
