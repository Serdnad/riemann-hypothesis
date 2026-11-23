module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CubBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

section Box

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem bw_trans {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : Fin j → M.ι} {k k' : M'.ι} (h₁ : ψ z ∈ LB.wchart M pr jN) (h₁' : ψ z ∈ LB.wchart M pr jN')
    (h₂ : ψ z ∈ M'.U k) (h₂' : ψ z ∈ M'.U k') :
    bw w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i))) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bw w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  have d := gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (jN, k) (jN', k') hm
  have l := gm_linComb M pr (fun _ => 1) ψ z jN jN' h₁ h₁'
  simp only [zpow_one] at l
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res ψ z _ hm _))))

variable {K : Type} [Fintype K]

def ratio (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (ρ : Fin j → (Y ⟶ Y₀)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bw w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)))⁻¹

theorem chart_le {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a) (jN : K → Fin j → M.ι) (i : Fin j) :
    LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ≤ ρ i ⁻¹ᵁ LB.wchart M φ (fun a => jN a i) := fun y hy =>
  Set.mem_iInter.2 fun a => (congrArg (fun g : Y ⟶ X => g y ∈ M.U (jN a i)) (hψ i a)).mp
    (Set.mem_iInter.1 (Set.mem_iInter.1 hy a) i)

theorem ratio_trans (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {jN jN' : K → Fin j → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)
    (h' : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN' ⊓ LB.wchart M' φ' jM') :
    ratio w ρ t' t r z jN jM = ratio w ρ t' t r z jN' jM' := by
  have e₁ : ∀ a, bw w (r ≫ φ' a) z (jN a) (jM a) = _ := fun a => bw_trans w hw (r ≫ φ' a) z (jN' := jN' a) (k' := jM' a)
    (Set.mem_iInter.1 h.1 a) (Set.mem_iInter.1 h'.1 a) (Set.mem_iInter.1 h.2 a) (Set.mem_iInter.1 h'.2 a)
  have e₂ := gen_trans ht' r z h.2 h'.2
  have e₃ : ∀ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) = _ := fun i =>
    gen_trans ht (r ≫ ρ i) z (j' := fun a => jN' a i) (chart_le hψ jN i h.1) (chart_le hψ jN' i h'.1)
  have e₄ : ∏ i, trF (L := M) φ ε (r ≫ ρ i) z (fun a => jN a i) (fun a => jN' a i) =
      ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (jN a i) ⊓ M.U (jN' a i)) (M.g (jN a i) (jN' a i))) ^ ε a := by
    unfold trF
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Category.assoc, Category.assoc, hψ]
  unfold ratio
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂, Finset.prod_congr rfl fun i _ => e₃ i,
    Finset.prod_mul_distrib, e₄]
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε)) (jN : K → Fin j → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
        r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM →
        gm r z _ u = ratio w ρ t' t r z jN jM := by
  refine ⟨@id (Γ(Y, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
      ((LB.linCombIso w φ' ε).s (jN, jM)) * res inf_le_right (t'.s jM) *
      (∏ i, res (inf_le_left.trans (chart_le hψ jN i)) (pullU (ρ i) _ (t.s (fun a => jN a i))))⁻¹,
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linCombIso w φ' ε r z jN jM hz) (gm_res r z _ hz _))) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))))
  exact (gm_res r z _ hz _).trans (gm_pull r (ρ i) z _ (chart_le hψ jN i hz.1) _)

theorem box_unique {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bw w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ i, val t (e ≫ ρ i) y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ i, val t (r ≫ ρ i) z J := by
  choose u hu using fun q : (K → Fin j → M.ι) × (K → M'.ι) => exists_ratio w hψ t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens)
    (fun q : (K → Fin j → M.ι) × (K → M'.ι) =>
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' q.1 ⊓ LB.wchart M' φ' q.2) (fun _ => le_top)
    (fun y _ => by
      choose a ha using fun k i => exists_chart hM (pr i (φ' k y))
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(a, b), Set.mem_iInter.2 fun k => Set.mem_iInter.2 (ha k), Set.mem_iInter.2 hb⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratio_trans w hw hψ ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ i, val t (r ≫ ρ i) z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
      ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩
    have v : ∏ i, val t (r ≫ ρ i) z J = ∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => J ((r ≫ φ' a) ≫ pr i)))
        (t.s (fun a => J ((r ≫ φ' a) ≫ pr i))) := Finset.prod_congr rfl fun i _ =>
      val_of t _ z J _ (fun a => by rw [Category.assoc, Category.assoc, hψ])
    rw [v]
    have w₁ := (hu (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Box

theorem cubV_box : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J J'), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D'.P.L z J' → ∀ x x' y : T ⟶ D'.P.A, (let om := fun p : T ⟶ D'.P.A => bw pD.w p.left z (fun i => J (p.left ≫ (pD.pw.pr i).left)) (J' p.left); Geo.Tor.cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ i, Geo.Tor.cubV D.cub z J (x ≫ pD.pw.pr i) (x' ≫ pD.pw.pr i) (y ≫ pD.pw.pr i)) := by
  intro hG R _ _ j D D' pD T z J J' hJ hJ' x x' y om
  let ρ : Fin j → ((G3 D'.P.A).left ⟶ (G3 D.P.A).left) := fun i => (pD.pw.pr i ⊗ₘ pD.pw.pr i ⊗ₘ pD.pw.pr i).left
  have hψ : ∀ i a, thφ D'.P.A (x3 D'.P.A) a ≫ (pD.pw.pr i).left = ρ i ≫ thφ D.P.A (x3 D.P.A) a := fun i a =>
    letI := pD.pw.hom i
    (CubeMap.ofHom (pD.pw.pr i)).psum_comm a.down
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (a b c : T ⟶ D'.P.A) i, (lift a (lift b c)).left ≫ ρ i =
      (lift (a ≫ pD.pw.pr i) (lift (b ≫ pD.pw.pr i) (c ≫ pD.pw.pr i))).left := fun a b c i => by
    show (lift a (lift b c) ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i ⊗ₘ pD.pw.pr i)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen (ε := thε) hψ
    D'.cub.isGen D.cub.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV D'.cub s I') := isCub_cubV D'.cub hI'
      have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I) := isCub_cubV D.cub hI
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
        (fun q => bw pD.w q s (fun i => I (q ≫ (pD.pw.pr i).left)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun i _ => ?_).symm)
      have := pD.pw.hom i
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ pD.pw.pr i = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ i = _ from hρ 1 1 1 i, o]
      exact C.face 1 1) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bw pD.w q z (fun i => J (q ≫ (pD.pw.pr i).left)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]; rfl

end GlobalTheory.CubBox
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

lemma krull_ext {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (W : (Spec (CommRingCat.of V)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of V), W))
    (h : ∀ (e : ℕ) (z), gs (thick V (maximalIdeal V) e) z W a = gs (thick V (maximalIdeal V) e) z W b) :
    a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick V (maximalIdeal V) e).app ⊤).hom a = ((thick V (maximalIdeal V) e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

lemma trF_unique {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (φ : Y ⟶ X) (n : ℤ) (r : Z ⟶ Y)
    (z : Z) (J : (Z ⟶ X) → L.ι) (j : L.ι) (q : Z ⟶ X) (hq : r ≫ φ = q) :
    trF (L := L) (fun _ : K => φ) (fun _ => n) r z (fun _ => J (r ≫ φ)) (fun _ => j) =
      gm q z (L.U (J q) ⊓ L.U j) (L.g (J q) j) ^ n := by
  subst hq
  exact Fintype.prod_unique _

def thU (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
  thick R I e

section Thick

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

lemma eSec_fGl : eSec (thickObj R I e G) ≫ fGl I G e = thU R I e ≫ eSec G :=
  eSec_pullback_fst _ _

lemma eSec_pGl : eSec (thickObj R I e G) ≫ pGl U e = thU R I e ≫ eSec D.toPre.P.A := by
  have := (U.gt e).q_hom
  have h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.toPre.P.A) :=
    congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_pullback_fst (thick R I e) _)
  rw [← h2, Category.assoc]
  rfl

lemma eSec_map (f : G ⟶ G) [IsMonHom f] :
    eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map f).left = eSec (thickObj R I e G) :=
  congrArg Over.Hom.left (IsMonHom.one_hom ((Over.pullback (thick R I e)).map f))

lemma wv_rig (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (thU R I e ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U jM) (hL : (thU R I e ≫ eSec G) z ∈ U.LG.L.U jL) :
    wv U e (eSec (thickObj R I e G)) z jM jL *
      gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => jL)) (U.LG.rig.s (fun _ => jL)) =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM)) (D.toPre.rig.s (fun _ => jM)) := by
  have m₁ : z ∈ eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL)) :=
    ⟨mem_pull.2 ((congrArg (fun g => g z ∈ D.toPre.P.L.U jM) (eSec_pGl U e)).mpr hM),
      mem_pull.2 ((congrArg (fun g => g z ∈ U.LG.L.U jL) (eSec_fGl (G := G) e)).mpr hL)⟩
  have m₂ : z ∈ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) := mem_pull.2 hL
  have m₃ : z ∈ thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := mem_pull.2 hM
  have hz : z ∈ (eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL))) ⊓ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) ⊓
      thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := ⟨⟨m₁, m₂⟩, m₃⟩
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => jM, fun _ => jL) _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ hz _) (gm_rp₁ _ z _ _ _ hz _))).symm.trans
    (W.trans (gm_rp₁ _ z _ _ _ hz _))

lemma unit_value_thick (f : G ⟶ G) [IsMonHom f] {g : D.toPre.P.A.left ⟶ D.toPre.P.A.left} {N : ℕ} (hN : 0 < N)
    {ε : Fin 2 → ℤ} (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, g] ε))
    (hX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N - 1))))
    (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J → ∀ jL jL',
      (r ≫ fGl I G e) z ∈ U.LG.L.U jL →
      ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z ∈ U.LG.L.U jL' →
      (wv U e r z (J (r ≫ pGl U e)) jL ^ (k * N)).val * sv U (k * N) σ'' (r ≫ fGl I G e) z jL =
        (val X (r ≫ pGl U e) z J ^ k).val *
          ((wv U e (r ≫ ((Over.pullback (thick R I e)).map f).left) z
            (J ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ pGl U e)) jL' ^ k).val *
            sv U k τ ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z jL'))
    (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (j : U.LG.L.ι)
    (hj : (thU R I e ≫ eSec G) z ∈ U.LG.L.U j) :
    sv U (k * N) σ'' (thU R I e ≫ eSec G) z j =
      (gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        sv U k τ (thU R I e ≫ eSec G) z j := by
  choose J hJ using fun ψ : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have E := H _ (eSec (thickObj R I e G)) z J hJ j j (by rw [eSec_fGl]; exact hj)
    (by rw [eSec_map, eSec_fGl]; exact hj)
  rw [eSec_map, eSec_fGl, eSec_pGl] at E
  have hw := wv_rig U e z _ j (hJ (thU R I e ≫ eSec D.toPre.P.A)) hj
  have hx : val X (thU R I e ≫ eSec D.toPre.P.A) z J =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => J (thU R I e ≫ eSec D.toPre.P.A)))
        (D.toPre.rig.s (fun _ => J (thU R I e ≫ eSec D.toPre.P.A))) ^ (1 * (N - 1)) :=
    (val_pull hJ X _ _).symm.trans ((val_corr hJ hX _).trans (map_pow _ _ _))
  rw [hx, ← hw] at E
  generalize wv U e (eSec (thickObj R I e G)) z (J (thU R I e ≫ eSec D.toPre.P.A)) j = w at E
  generalize gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) = u at E ⊢
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  refine (w ^ (k * (n + 1))).mul_right_inj.1 (E.trans ?_)
  simp only [Nat.add_sub_cancel, Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end Thick

theorem unit_value {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] [IsLocalRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    (U : UnifPre (maximalIdeal V) D A G) {N : ℕ} (hN : 0 < N) (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (e : ℕ) (z) (j : U.LG.L.ι), (thU V (maximalIdeal V) e ≫ eSec G) z ∈ U.LG.L.U j →
      sv U (k * N) σ'' (thU V (maximalIdeal V) e ≫ eSec G) z j =
      (gm (thU V (maximalIdeal V) e) z ((U.LG.L.pull (eSec G)).U (fun _ => j))
        (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (thU V (maximalIdeal V) e ≫ eSec G) z j)
    (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J) (hJ : Good U.LG.L y J) :
    sval σ'' (r ≫ eSec G) y J =
      (val (L := U.LG.L) U.LG.rig r y J ^ (k * (N - 1))).val * sval τ (r ≫ eSec G) y J := by
  obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (eSec G (IsLocalRing.closedPoint V))
  have hj' : ∀ x, eSec G x ∈ U.LG.L.U j := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := V) x).map (eSec G).continuous).mem_open (U.LG.L.U j).isOpen hj
  let W₁ : G.left.Opens := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)
  have m₁ : ∀ x, eSec G x ∈ W₁ := fun x => Set.mem_iInter.2 fun _ => hj' x
  let W : (𝟙_ (Over (Spec (CommRingCat.of V)))).left.Opens := (U.LG.L.pull (eSec G)).U (fun _ => j)
  have m : ∀ x, x ∈ W := fun x => mem_pull.2 (hj' x)
  have hle : W ≤ eSec G ⁻¹ᵁ W₁ := fun x _ => m₁ x
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (s : Γ(G.left, W₁)),
      gs r y W (rs hle (((eSec G).app W₁).hom s)) = gs (r ≫ eSec G) y W₁ s := fun Z r y s =>
    (gs_res r y hle (m _) _).trans (gs_pull r (eSec G) y W₁ (m₁ _) s)
  have ev' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z),
      gs r y W ((@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j)))) =
      (gm r y W (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (r ≫ eSec G) y j := fun Z r y =>
    (gs_mul r y W (m _) _ _).trans (congrArg₂ (· * ·) ((gs_unit r y W (m _) _).trans
      (congrArg Units.val (map_pow _ _ _))) (ev Z r y _))
  have key : rs hle (((eSec G).app W₁).hom (σ''.f (fun _ => j))) =
      (@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j))) :=
    krull_ext W (eq_top_iff.2 fun x _ => m x) _ _ fun e z =>
      (ev _ (thU V (maximalIdeal V) e) z _).trans ((H e z j (hj' _)).trans (ev' _ (thU V (maximalIdeal V) e) z).symm)
  have E := (ev Z r y _).symm.trans ((congrArg (gs r y W) key).trans (ev' Z r y))
  have a₁ : sval σ'' (r ≫ eSec G) y J = _ :=
    sec_trans σ'' (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₂ : sval τ (r ≫ eSec G) y J = _ :=
    sec_trans τ (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₃ : val (L := U.LG.L) U.LG.rig r y J = _ :=
    gen_trans (L := U.LG.L) U.LG.rigGen r y (hJ.mem _ r) (j' := fun _ => j) (m _)
  rw [a₁, a₂, a₃]
  refine (congrArg _ E).trans ?_
  rw [trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _), trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _),
    trF_unique _ _ _ _ J j (r ≫ eSec G) rfl]
  simp only [zpow_natCast, zpow_one]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have alg : ∀ (c u : (Z.presheaf.stalk y)ˣ) (s : Z.presheaf.stalk y), (c ^ (k * (n + 1))).val * ((u ^ (k * n)).val * s) =
      ((c * u) ^ (k * n)).val * ((c ^ k).val * s) := fun c u s => by
    simp only [Units.val_pow_eq_pow_val, Units.val_mul]
    ring
  exact alg _ _ _

theorem value_at_unit_section : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ (k : ℕ) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ'' (r ≫ eSec t.G) y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig r y J ^ (k * (N - 1))).val * Geo.Tor.sval τ (r ≫ eSec t.G) y J := by
  intro V _ _ _ E _ _ _ H t P a N _ hN X _ hX k σ'' τ h
  have := t.act.hom a
  exact unit_value P.U.toUnifPre hN k σ'' τ fun e => unit_value_thick P.U.toUnifPre e (t.act.act a) hN X hX k σ'' τ (h e)

end GlobalTheory.UnitValue
end
end
