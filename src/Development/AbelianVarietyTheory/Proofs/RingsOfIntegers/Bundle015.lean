module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)


omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem thickMap_comp_fGl (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ fGl I G (e + 1) = fGl I G e := by
  unfold thickMap fGl fstG
  simp only [Over.homMk_left, pullback.map, pullback.lift_fst, Category.comp_id]

private lemma mem_pull_U_of_mem_U {X Y : Scheme.{0}} {M : LB X} (f : Y ⟶ X) (j : PUnit → M.ι) (y : Y)
    (h : f y ∈ M.U (j ⟨⟩)) : y ∈ (M.pull f).U j := by
  unfold LB.pull LB.LinComb
  simp only [LB.wchart]
  simpa using fun i : PUnit => (show i = ⟨⟩ from rfl) ▸ h

private lemma gm_res_eq_gm {Z : Scheme.{0}} (z : Z) {V W : Z.Opens} (h : V ≤ W) (hz : z ∈ V) (x : Γ(Z, W)ˣ) :
    gm (𝟙 Z) z V (res h x) = gm (𝟙 Z) z W x := by
  rw [← gm_rp₁ (𝟙 Z) z W V h hz x]
  unfold pullU
  congr 2

theorem wv_thickMap (e : ℕ) (y : (thickObj R I e G).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : pGl U e y ∈ D.toPre.P.L.U jM) (hL : fGl I G e y ∈ U.LG.L.U jL) :
    wv U (e + 1) (thickMap R I e G) y jM jL = wv U e (𝟙 _) y jM jL := by
  have hq := U.gt_q e
  have hf := thickMap_comp_fGl I e G
  have h3 : (pGl U (e + 1)) ((thickMap R I e G) y) = (pGl U e) y := congrArg (fun g => g.base y) hq
  have h4 : (fGl I G (e + 1)) ((thickMap R I e G) y) = (fGl I G e) y := congrArg (fun g => g.base y) hf
  have hy : y ∈ ((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL :=
    ⟨mem_pull_U_of_mem_U _ _ _ hM, mem_pull_U_of_mem_U _ _ _ hL⟩
  have hy' : y ∈ thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) :=
    ⟨mem_pull_U_of_mem_U _ _ _ (h3 ▸ hM), mem_pull_U_of_mem_U _ _ _ (h4 ▸ hL)⟩
  have hle : thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) ≤
      thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) := inf_le_left
  have hV : y ∈ (thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL)) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) := ⟨hy', hy⟩
  unfold wv
  refine (gm_rp₁ (thickMap R I e G) y _ _ hle hV ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))).symm.trans ?_
  exact (congrArg (gm (𝟙 _) y _) (U.w_compat e (fun _ => jM, fun _ => jL) _ hle inf_le_right)).trans
    (gm_res_eq_gm y (inf_le_right : (thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL)) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) ≤ (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL)) hV _)

end

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowerThickIso

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull gm_div gm_linComb gm_pull_g gm_self mem_pull PGen isGen_iff glue_unit
  exists_chart)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'}
  {h : Fin j → (Ge' ⟶ Ge)}

theorem gm_box_g {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z) (a b : Fin j → M.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i))
    (hb : ∀ i, pr i (ψ z) ∈ M.U (b i)) :
    gm ψ z (LB.wchart M pr a ⊓ LB.wchart M pr b) ((LB.LinComb M pr (fun _ => 1)).g a b) =
      ∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i)) :=
  (gm_linComb M pr (fun _ => 1) ψ z a b (Set.mem_iInter.2 ha) (Set.mem_iInter.2 hb)).trans
    (Finset.prod_congr rfl fun _ _ => zpow_one _)

theorem bw_change {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z)
    (a b : Fin j → M.ι) (k k' : M'.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i)) (hb : ∀ i, pr i (ψ z) ∈ M.U (b i))
    (hk : ψ z ∈ M'.U k) (hk' : ψ z ∈ M'.U k') :
    bw w ψ z a k = (∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i))) *
      (gm ψ z _ (M'.g k k'))⁻¹ * bw w ψ z b k' := by
  have hm : ψ z ∈ LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k') :=
    ⟨⟨Set.mem_iInter.2 ha, hk⟩, Set.mem_iInter.2 hb, hk'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k'))) (hw (a, k) (b, k'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (a, k) (b, k') hm) (gm_res ψ z _ hm _))))
  rw [← gm_box_g ψ z a b ha hb]
  exact e'

def germ (pG' : Ge' ⟶ B') (h : Fin j → (Ge' ⟶ Ge)) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι)
    (jL : Fin j → L.ι) : (Z.presheaf.stalk z)ˣ :=
  (bw w (r ≫ pG') z jM jM')⁻¹ * ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i)

theorem germ_change (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : Fin j → M.ι) (jM' kM' : M'.ι) (jL kL : Fin j → L.ι)
    (a₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (jL i))
    (b₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (kM i)) (b₂ : pG' (r z) ∈ M'.U kM') (b₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (kL i)) :
    germ pG' h w we r z jM jM' jL =
      gm (r ≫ pG') z _ (M'.g jM' kM') *
        (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        germ pG' h w we r z kM kM' kL := by
  have p₁ : ∀ i, pG (h i (r z)) = pr i (pG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₁ i).symm
  have p₂ : ∀ i, fG (h i (r z)) = prG i (fG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₂ i)
  have a := bw_change hw (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have c : ∀ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) =
      gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i)) *
        (gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i) := fun i => by
    have c₃ : fG (h i (r z)) ∈ L.U (jL i) := p₂ i ▸ a₃ i
    have d₃ : fG (h i (r z)) ∈ L.U (kL i) := p₂ i ▸ b₃ i
    have c₁ : pG (h i (r z)) ∈ M.U (jM i) := p₁ i ▸ a₁ i
    have d₁ : pG (h i (r z)) ∈ M.U (kM i) := p₁ i ▸ b₁ i
    have c := hwe Z (r ≫ h i) z (jM i) (kM i) (fun _ => jL i) (fun _ => kL i) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
    rw [gm_pull_g L fG (r ≫ h i) z (fun _ => jL i) (fun _ => kL i) (mem_pull.2 c₃) (mem_pull.2 d₃),
      Category.assoc, Category.assoc, ← e₁, e₂] at c
    rw [Category.assoc, Category.assoc]
    exact c
  unfold germ
  rw [a, Finset.prod_congr rfl fun i _ => c i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  generalize (∏ i, gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i))) = A
  generalize (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i))) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize bw w (r ≫ pG') z kM kM' = P
  generalize (∏ i, Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i)) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    (jM' : M'.ι) (jL : Fin j → L.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι), (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) →
        pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        gm r z _ s = germ pG' h w we r z jM jM' jL := by
  have p₁ : ∀ i x, pG (h i x) = pr i (pG' x) := fun i x => congrArg (fun g => g x) (e₁ i).symm
  have p₂ : ∀ i x, fG (h i x) = prG i (fG' x) := fun i x => congrArg (fun g => g x) (e₂ i)
  obtain ⟨W, hW⟩ : ∃ W : (Fin j → M.ι) → Ge'.Opens, ∀ a x, x ∈ W a ↔
      (∀ i, pr i (pG' x) ∈ M.U (a i)) ∧ pG' x ∈ M'.U jM' ∧ ∀ i, prG i (fG' x) ∈ L.U (jL i) :=
    ⟨fun a => pG' ⁻¹ᵁ LB.wchart M pr a ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ fG' ⁻¹ᵁ LB.wchart L prG jL),
      fun _ _ => and_congr Set.mem_iInter (and_congr Iff.rfl Set.mem_iInter)⟩
  have l₀ : ∀ a, W a ≤ (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL) :=
    fun a x hx => ⟨mem_pull.2 ((hW a x).1 hx).2.1, mem_pull.2 (Set.mem_iInter.2 ((hW a x).1 hx).2.2)⟩
  have l₁ : ∀ a, W a ≤ pG' ⁻¹ᵁ (LB.wchart M pr a ⊓ M'.U jM') := fun a x hx =>
    ⟨Set.mem_iInter.2 ((hW a x).1 hx).1, ((hW a x).1 hx).2.1⟩
  have l₂ : ∀ a i, W a ≤ h i ⁻¹ᵁ ((M.pull pG).U (fun _ => a i) ⊓ (L.pull fG).U (fun _ => jL i)) := fun a i x hx =>
    ⟨mem_pull.2 ((p₁ i x).symm ▸ ((hW a x).1 hx).1 i), mem_pull.2 ((p₂ i x).symm ▸ ((hW a x).1 hx).2.2 i)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(Ge', W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (a : Fin j → M.ι), r z ∈ W a →
      gm r z (W a) (u a) = germ pG' h w we r z a jM' jL :=
    ⟨fun a => (res (l₁ a) (pullU pG' _ (w.s (a, jM'))))⁻¹ *
        ∏ i, res (l₂ a i) (pullU (h i) _ (we.s (fun _ => a i, fun _ => jL i))),
      fun Z r z a hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ a) hz _).trans (gm_pull r pG' z _ (l₁ a hz) _)))) ((map_prod _ _ _).trans
          (Finset.prod_congr rfl fun i _ =>
            (gm_res r z (l₂ a i) hz _).trans (gm_pull r (h i) z _ (l₂ a i hz) _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      choose a ha using fun i => exists_chart hM (pr i (pG' x))
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨a, (hW a x).2 ⟨ha, mem_pull.1 hx.1, Set.mem_iInter.1 (mem_pull.1 hx.2)⟩⟩) u
    (fun a a' x hx => by
      have h₁ := (hW a x).1 hx.1
      have h₂ := (hW a' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwe (𝟙 Ge') x a a' jM' jM' jL jL h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, Finset.prod_eq_one fun i _ =>
        gm_self hL ((𝟙 Ge' ≫ fG') ≫ prG i) x (h₁.2.2 i), inv_one, _root_.one_mul, _root_.one_mul] at k
      exact (hu _ (𝟙 Ge') x a hx.1).trans (k.trans (hu _ (𝟙 Ge') x a' hx.2).symm))
  refine ⟨s, fun Z r z jM a₁ a₂ a₃ => ?_⟩
  have hz := (hW jM (r z)).2 ⟨a₁, a₂, a₃⟩
  exact (gm_res r z (l₀ jM) hz s).symm.trans ((congrArg (gm r z (W jM)) (hs jM)).trans (hu Z r z jM hz))

theorem exists_box_iso (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen)
    (hwe : we.IsGen) :
    ∃ we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι) (jL : Fin j → L.ι),
        (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) → pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        bw w (r ≫ pG') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL) =
          ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) := by
  rw [isGen_iff] at hwe
  choose s hs using exists_unit hM hM' hL e₁ e₂ hw hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL a₁ a₂ a₃ => ?_⟩
  · intro Z r z l l' k k' a₂ b₂ a₄ b₄
    choose a ha using fun i => exists_chart hM (pr i (pG' (r z)))
    have a₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 a₄)
    have b₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k' PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 b₄)
    have c := germ_change e₁ e₂ hw hwe r z a a l l' _ _ ha a₂ a₄' ha b₂ b₄'
    rw [← hs l _ Z r z a ha a₂ a₄', ← hs l' _ Z r z a ha b₂ b₄', ← gm_box_g (r ≫ fG') z _ _ a₄' b₄'] at c
    rw [gm_pull_g (LB.LinComb L prG (fun _ => 1)) fG' r z k k' a₄ b₄]
    exact c
  · exact (congrArg (bw w (r ≫ pG') z jM jM' * ·) (hs jM' jL Z r z jM a₁ a₂ a₃)).trans
      (mul_inv_cancel_left _ _)

end General

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (e : ℕ) (g : GtCoord I D.toPre e G) (g' : GtCoord I D'.toPre e G'), (∀ i, g'.pG.left ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ g.pG.left) → ∀ (L : LB G.left), L.IsLB → ∀ w : LB.Iso (L.pull (fstG I e G).left) (D.toPre.P.L.pull g.pG.left), w.IsGen → ∃ w' : LB.Iso ((boxLB L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : Fin j → L.ι), (∀ i, (pD.pw.pr i).left (g'.pG.left (r z)) ∈ D.toPre.P.L.U (jM i)) → g'.pG.left (r z) ∈ D'.toPre.P.L.U jM' → (∀ i, (pG.pr i).left ((fstG I e G').left (r z)) ∈ L.U (jL i)) → bw pD.w (r ≫ g'.pG.left) z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL) = ∏ i, Geo.Tor.gw w (r ≫ ((Over.pullback (thick R I e)).map (pG.pr i)).left) z (jM i) (fun _ => jL i) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG e g g' hq L hL w hw
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  exact exists_box_iso (Ge := (thickObj R I e G).left) (Ge' := (thickObj R I e G').left) (h := rhoE I pG e)
    (pG := g.pG.left) (pG' := g'.pG.left) (fG := fGl I G e) (fG' := fGl I G' e)
    D.toPre.P.isLB D'.toPre.P.isLB hL hq hρ pD.w w pD.w_gen hw

end GlobalTheory.PowerThickIso
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.BoxExpPre

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pG : IsPowGrp G' G j}
  {U' : UnifPre I D' A' G'} {U : UnifPre I D A G} {wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)}


variable (pD pG U' U) in
def TPr : Prop := (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i)))))


variable (pD pG U' U wL) in
def WPr : Prop := (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL'))))

theorem prebox_q (PT : TPr pD pG U' U) (e : ℕ) (i : Fin j) :
    pGl U' e ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ pGl U e := (PT e 0).choose i 2


theorem prebox_F (PT : TPr pD pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {k : ℕ} {f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α}
    {f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α'} (hf' : IsBoxFamB pD k f' f) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U' e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a).val * sval (f' α') (pGl U' e) y J' =
      ∏ i, sval (f i (pD.xe α' i)) (rhoE I pG e i ≫ (pGl U e)) y J := by
  obtain ⟨hφ, H⟩ := hf' α'
  have := box_sec_val pD.w hφ (f' α') (fun i => f i (pD.xe α' i)) _ H (pGl U' e) y hJ hJ'
  simp only [prebox_q PT] at this
  exact this


theorem prebox_expansion_torus (PT : TPr pD pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' (Oφl U' e α' a) ^ Oinvε a) * val (tG U' e α') (𝟙 _) y J' =
      ∏ i, val (tG U e (pD.xe α' i)) (rhoE I pG e i) y J := by
  obtain ⟨hψ, H⟩ := PT e α'
  exact box_gen_val pD.w hψ _ (fun i => tG U e (pD.xe α' i)) H y hJ hJ'

theorem prebox_om {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι} (k : ℕ) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U' e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a) * ∏ a, omB pD y J J' (Oφl U' e α' a) ^ Oinvε a =
      omB pD y J J' (pGl U' e) ^ k := by
  have a₀ : (pGl U' e) ≫ D'.toPre.famφB α' 0 = (pGl U' e) := Category.comp_id _
  have a₁ : (pGl U' e) ≫ D'.toPre.famφB α' 1 = Oφl U' e α' 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U'.gt e).pG (𝟙 _) (cP D'.toPre _ α')).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D'.toPre _ α')))
  have a₂ : (pGl U' e) ≫ D'.toPre.famφB α' 2 = Oφl U' e α' 1 :=
    congrArg (fun z => z.left) (comp_cP D'.toPre (U'.gt e).pG α')
  have a₃ : (pGl U' e) ≫ D'.toPre.famφB α' 3 = Oφl U' e α' 3 :=
    congrArg (fun z : _ ⟶ D'.toPre.P.A => z.left) (MonObj.comp_one (M := D'.toPre.P.A) (U'.gt e).pG)
  have a₄ : Oφl U' e α' 2 = (pGl U' e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module


theorem prebox_expansion_weight (PT : TPr pD pG U' U) (PW : WPr pD pG U' U wL) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    omB pD y J J' (pGl U' e) * wv U' e (𝟙 _) y (J' (pGl U' e)) jL' =
        (∏ i, wv U e (rhoE I pG e i) y (J ((pGl U' e) ≫ (pD.pw.pr i).left)) (jL i)) *
          gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (wL.s (jL, jL')) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have hq := prebox_q PT e
  have mM : (pGl U' e) y ∈ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left), J' (pGl U' e)) :=
    ⟨Set.mem_iInter.2 fun i => hJ ((pGl U' e) ≫ (pD.pw.pr i).left), hJ' (pGl U' e)⟩
  have mW : ∀ i, rhoE I pG e i y ∈ (D.toPre.P.L.pull (pGl U e)).U (fun _ => J ((pGl U' e) ≫ (pD.pw.pr i).left)) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL i) := fun i =>
    ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U (J ((pGl U' e) ≫ (pD.pw.pr i).left))) (hq i)).mp (hJ _)),
      mem_pull.2 (hL₁ i)⟩
  have hm : (𝟙 _ : (thickObj R I e G').left ⟶ _) y ∈ (pGl U' e) ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U
      (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left), J' (pGl U' e)) ⊓
      (LB.div (D'.toPre.P.L.pull (pGl U' e)) (U'.LG.L.pull (fGl I G' e))).U (fun _ => J' (pGl U' e), fun _ => jL') ⊓
      (⨅ i, rhoE I pG e i ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (pGl U e)) (U.LG.L.pull (fGl I G e))).U
        (fun _ => J ((pGl U' e) ≫ (pD.pw.pr i).left), fun _ => jL i)) ⊓
      (fGl I G' e) ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') :=
    ⟨⟨⟨mM, mem_pull.2 (hJ' (pGl U' e)), mem_pull.2 hL'⟩, by
      rw [← Finset.inf_univ_eq_iInf]; exact mem_finf _ _ _ fun i _ => mW i⟩, mL⟩
  have W := congrArg (gm (𝟙 _) y _) (PW e (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left)) (J' (pGl U' e)) jL' jL)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ (pGl U' e) y _ _ _ hm _) (gm_res (𝟙 _) y _ hm _))).symm.trans (W.trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
          gm_rp₁ (rhoE I pG e i) y _ _ _ hm _)) (gm_rp₁ (fGl I G' e) y _ _ _ hm _))))


theorem prebox_S {e k : ℕ} {y : (thickObj R I e G').left} {σ : Fin j → H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    (hσ' : IsBoxSecG pG wL k σ' σ) {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    (gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (wL.s (jL, jL')) ^ k).val *
        sv U' k σ' (fGl I G' e) y jL' = ∏ i, sv U k (σ i) (rhoE I pG e i ≫ fGl I G e) y (jL i) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have Sg := congrArg (gs (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL'))) (hσ' jL jL')
  rw [gs_mul _ y _ mL, gs_unit _ y _ mL, map_pow] at Sg
  refine (congrArg₂ (· * ·) rfl (gs_res (fGl I G' e) y (boxG_le_b pG jL jL') mL _).symm).trans
    (Sg.trans ((gs_prod _ y _ mL _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]
  exact (gs_res (fGl I G' e) y (boxG_le_c pG jL jL' i) mL _).trans
    (gs_pull (fGl I G' e) (pG.pr i).left y _ (boxG_le_c pG jL jL' i mL) _)

theorem expandsAt_prebox (PT : TPr pD pG U' U) (PW : WPr pD pG U' U wL) (k e : ℕ) (σ : Fin j → H0 U.LG.L k)
    (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ i, U.ExpandsAt e k (σ i) (f i))
    (σ' : H0 U'.LG.L k) (f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α')
    (hσ' : IsBoxSecG pG wL k σ' σ) (hf' : IsBoxFamB pD k f' f) :
    U'.ExpandsAt e k σ' f' := by
  classical
  choose S hS using fun i => expandsAt_val U e k (σ i) (f i) (hE i)
  refine expandsAt_of_val U' e k σ' f' ((Fintype.piFinset S).map pD.xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G').left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hF := prebox_F PT hJ hJ' hf'
  have hT := prebox_expansion_torus PT hJ hJ'
  have hω := prebox_om (pD := pD) (U' := U') (y := y) (J := J) (J' := J') k
  have hq := prebox_q PT e
  refine ⟨fun α' hα => ?_, fun jL' hL' => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, pD.xe α' i ∉ S i := by
      by_contra hc
      exact hα (Finset.mem_map.2 ⟨pD.xe α', Fintype.mem_piFinset.2 fun i => by_contra fun h => hc ⟨i, h⟩,
        pD.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').trans (Finset.prod_eq_zero (Finset.mem_univ i)
      ((hS i _ (rhoE I pG e i) y J hJ).1 _ hi)))
  · choose jL hL using fun i => exists_chart U.LG.isLB ((pG.pr i).left ((fGl I G' e) y))
    have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
      (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (pullback.lift_fst _ _ _ :
        rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left)).mpr (hL i)
    have W' := prebox_expansion_weight PT PW hJ hJ' hL hL'
    have Sg' := prebox_S hσ' hL hL'
    refine (omB pD y J J' (pGl U' e) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, W', mul_pow, Units.val_mul, _root_.mul_assoc, Sg', ← Finset.prod_pow,
      Units.coe_prod, ← Finset.prod_mul_distrib, Finset.sum_map, Finset.mul_sum]
    refine (Finset.prod_congr rfl fun i _ => ?_).trans ((Finset.prod_univ_sum S fun i α =>
      sval (f i α) (rhoE I pG e i ≫ (pGl U e)) y J * (val (tG U e α) (rhoE I pG e i) y J).val).trans
      (Finset.sum_congr rfl fun x _ => ?_))
    · rw [hq]; exact (hS i _ (rhoE I pG e i) y J hJ).2 (jL i) (hL₁ i)
    · obtain ⟨α', rfl⟩ := pD.xe.surjective x
      have e₀ : pD.xe.symm.toEquiv.toEmbedding (pD.xe α') = α' := pD.xe.symm_apply_apply α'
      rw [e₀, Finset.prod_mul_distrib, ← hF α', ← Units.coe_prod, ← hT α', ← hω α', Units.val_mul, Units.val_mul,
        _root_.mul_mul_mul_comm]

theorem expandsAt_box_unifPre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) → ∀ (k e : ℕ) (σ : Fin j → H0 U.LG.L k) (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ i, U.ExpandsAt e k (σ i) (f i)) → ∀ (σ' : H0 U'.LG.L k) (f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α'), IsBoxSecG pG wL k σ' σ → IsBoxFamB pD k f' f → U'.ExpandsAt e k σ' f' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U wL h k e σ f hE σ' f' hσ hf
  exact expandsAt_prebox h.2.2.2.2.1 h.2.2.2.2.2 k e σ f hE σ' f' hσ hf

end GlobalTheory.BoxExpPre
end
end
