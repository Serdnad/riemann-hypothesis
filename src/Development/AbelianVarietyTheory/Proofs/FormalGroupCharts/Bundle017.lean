module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

section

noncomputable section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.JetSer

theorem valSer_germ_fnVal {A : Type} [CommRing A] {Y : Scheme.{0}} (r : Spec (CommRingCat.of A) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Spec (CommRingCat.of A)) (f : Γ(Y, U)) :
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (fnVal r U f)) = gs r z U f := by
  have hz : r z ∈ U := h (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial)
  rw [gs_eq r z U hz, fnVal, dite_eq_left h]
  have e : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) = a :=
    fun a => (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id_apply a
  rw [e]
  exact TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of A)).presheaf (homOfLE h) z trivial _

theorem valSer : ValSerSt := by
  intro A _ X L hL j z Ψ _ hΨ
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Ψ) (fun ψ => ψ.1) (fun _ => j) (fun _ _ _ => rfl)
    (fun ψ => hΨ ψ.1 ψ.2 (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial))
  refine ⟨J, hJ, fun Y K _ φ ε t r hr => ?_⟩
  have hU : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j) := fun y hy => Set.mem_iInter.2 fun k => hΨ _ (hr k) hy
  rw [val_of t r z J (fun _ => j) (fun k => e ⟨_, hr k⟩)]
  exact (gs_unit r z _ (hU (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial)) _).symm.trans
    (valSer_germ_fnVal r _ hU z _).symm

end GlobalTheory.JetSer
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

theorem IsFPt.mul {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type}
    {y z : Fam G κ} (hy : IsFPt y) (hz : IsFPt z) : IsFPt (fun m => y m * z m : Fam G κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show _ ≫ (y (m + 1) * z (m + 1)) = y m * z m
    rw [MonObj.comp_mul, hy.1 m, hz.1 m]
  · show _ ≫ (y m * z m) = 1
    rw [MonObj.comp_mul, hy.2 m, hz.2 m, _root_.mul_one]

theorem addOf_pt_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  have h : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  unfold addOf
  rw [h]
  unfold ev
  exact congrFun MvPowerSeries.subst_self _

theorem lawSt_of (hJ : JetAlgSt) (hR : RepSt) : LawSt := by
  intro R _ G _ _ d x hx
  have uC : ∀ {n : ℕ} {a a' : Pt R n d} {y : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a' y → a = a' :=
    fun {n a a' y} h h' =>
      ((hR R G d x hx (Fin n × Fin d)).2.1 y ((hR R G d x hx (Fin n × Fin d)).2.2.1 a y h)).unique h h'
  have uP : ∀ {n : ℕ} {a : Pt R n d} {y y' : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a y' → y = y' :=
    fun {n a y y'} h h' => ((hR R G d x hx (Fin n × Fin d)).1 a h.1).unique h h'
  have gen : ∀ (n : ℕ) (j : Fin n), ∃ y : Fam G (Fin n × Fin d), Rep x (pt R d j) y :=
    fun n j => ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists
  choose Y hY using gen
  refine ⟨?_, fun F F' hF hF' => ?_⟩
  swap
  · rw [← addOf_pt_pt F, ← addOf_pt_pt F']
    exact uC (hF.2 2 _ _ _ _ (hY 2 0) (hY 2 1)) (hF'.2 2 _ _ _ _ (hY 2 0) (hY 2 1))
  have H2 := hR R G d x hx (Fin 2 × Fin d)
  obtain ⟨F, hF⟩ := (H2.2.1 _ (IsFPt.mul (H2.2.2.1 _ _ (hY 2 0)) (H2.2.2.1 _ _ (hY 2 1)))).exists
  have law : IsLawOf x F := by
    refine ⟨hF.1, fun n a b y z ha hb => ?_⟩
    let c : Fin 2 × Fin d → PS R n d := fun p => (![a, b] : Fin 2 → Pt R n d) p.1 p.2
    have hc : ∀ p, constantCoeff (c p) = 0 := fun p => pair_points_zero_constant ha.1 hb.1 p.1 p.2
    have hex : ∀ m, ∃ ψ : JetR R (Fin 2 × Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m,
        ∀ j, ψ (zR m j) = toJet m (c j) :=
      fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d) c hc m).1
    choose ψ hψ using hex
    have sub := H2.2.2.2.2 (Fin n × Fin d) c ψ hc hψ
    have hs : ∀ j : Fin 2, (fun i => MvPowerSeries.subst c (pt R (n := 2) d j i)) = (![a, b] : Fin 2 → Pt R n d) j :=
      fun j => funext fun i => gt_ev_X _ (pair_points_zero_constant ha.1 hb.1) j i
    have e0 : (fun m => spMap (ψ m) ≫ Y 2 0 m) = y := by
      have := sub _ _ (hY 2 0)
      rw [hs 0] at this
      exact uP this ha
    have e1 : (fun m => spMap (ψ m) ≫ Y 2 1 m) = z := by
      have := sub _ _ (hY 2 1)
      rw [hs 1] at this
      exact uP this hb
    have key := sub _ _ hF
    have e : (fun m => spMap (ψ m) ≫ (Y 2 0 m * Y 2 1 m)) = fun m => y m * z m := by
      funext m
      rw [MonObj.comp_mul, ← e0, ← e1]
    rw [← e]
    exact key
  refine ⟨⟨F, hF.1, fun i => ?_, fun i => ?_, fun i => ?_⟩, law⟩
  · have h := law.2 1 _ _ _ _ (hR R G d x hx (Fin 1 × Fin d)).2.2.2.1 (hY 1 0)
    simp only [_root_.one_mul] at h
    exact congrFun (uC h (hY 1 0)) i
  · have h := law.2 2 _ _ _ _ (hY 2 1) (hY 2 0)
    have e : (fun m => Y 2 1 m * Y 2 0 m) = fun m => Y 2 0 m * Y 2 1 m :=
      funext fun m => _root_.mul_comm _ _
    rw [e] at h
    exact congrFun (uC h hF) i
  · have h := law.2 3 _ _ _ _ (law.2 3 _ _ _ _ (hY 3 0) (hY 3 1)) (hY 3 2)
    have h' := law.2 3 _ _ _ _ (hY 3 0) (law.2 3 _ _ _ _ (hY 3 1) (hY 3 2))
    simp only [_root_.mul_assoc] at h
    exact congrFun (uC h h') i

end GlobalTheory.JetSer
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NormRos

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_lbIso {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))), t.IsGen := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  refine ⟨⟨fun j => res (le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩,
    fun (p q : K' ⊕ K → L.ι) => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 Y) y (LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr))))
    (hw (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr))
  have e' := (gm_res (𝟙 Y) y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr) hm)
    (gm_res (𝟙 Y) y _ hm _))))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.2 _)))
  refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1).symm ?_)
  refine Eq.trans ?_ (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2).symm)
  simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp_apply]

theorem gen_s_ext {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good L y J → val u (𝟙 Y) y J = val u' (𝟙 Y) y J) : u.s = u'.s :=
  funext fun j => Units.ext (sec_ext_val hL (s := genSec u hu) (s' := genSec u' hu') (fun y J hJ => by
    rw [sval_genSec u hu _ y hJ, sval_genSec u' hu' _ y hJ, h y J hJ]) j)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem prod_square {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem exists_gen_rosati {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L)) :
    ∃ t : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε), t.IsGen := by
  obtain ⟨t, ht⟩ := exists_gen_of_lbIso H
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := rosatiφ G f g) (ε' := rosatiε) (fun V _ k => by
      have p := prod_ros f g (fst G G) (snd G G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      refine (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2)))
        (U := V) _ (prod_square (fst G G) (snd G G ≫ g) k)
        (DVR.prod_neg _ _ (prod_square (fst G G ≫ f) (snd G G) k)))).trans ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
  exact ⟨u, hu⟩

theorem exists_isNormRos {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G) [IsMonHom f] [IsMonHom g]
    (t : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε)) (ht : t.IsGen) : ∃ u, IsNormRos L f g u := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := rosatiφ G f g) (ε' := rosatiε)
    (fun V _ k => by
      have p := prod_ros f g (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G) k
      rw [MonObj.one_comp, MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (c := ∏ i, k (rosatiφ G f g i) ^ rosatiε i) rfl (DVR.prod_neg _ _ p)) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (lift (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
  have e : zero2 G ≫ (lift (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G)).left = zero2 G := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
    congr 1
  rw [val_one, val_pull hJ, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]


omit [IsCommMonObj G] in
theorem isNormRos_unique {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (hs : Function.Surjective (G ⊗ G).hom.appTop.hom) {u u' : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε)}
    (h : IsNormRos L f g u) (h' : IsNormRos L f g u') : u.s = u'.s := by
  have z2 : zero2 G ≫ (G ⊗ G).hom = 𝟙 S := Over.w (lift η[G] η[G])
  refine gen_s_ext hL h.1 h'.1 fun y J hJ =>
    gen_unique hL (S₀ := S) (G ⊗ G).hom (zero2 G) z2 hs h.1 h'.1 (fun s I hI => ?_) _ _ y J hJ
  have a := val_corr hI h.2 (𝟙 _)
  have b := val_corr hI h'.2 (𝟙 _)
  rw [val_pull hI, Category.id_comp, val_one] at a b
  exact a.trans b.symm

theorem normRos_of_lbIso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB →
    ∀ (f g : G ⟶ G) [IsMonHom f] [IsMonHom g],
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) →
    (∃ u, IsNormRos L f g u) ∧ (Function.Surjective (G ⊗ G).hom.appTop.hom →
      ∀ u u', IsNormRos L f g u → IsNormRos L f g u' → u.s = u'.s) := by
  intro S G _ _ L hL f g _ _ H
  obtain ⟨t, ht⟩ := exists_gen_rosati hL f g H
  exact ⟨exists_isNormRos hL f g t ht, fun hs u u' h h' => isNormRos_unique hL f g hs h h'⟩

end GlobalTheory.NormRos
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartAction

theorem rep_unique (hR : RepSt) {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ}
    {x : Fam G (Fin d)} (hx : IsUnivChart G d x) {κ : Type} [Finite κ] {a b : Fin d → MvPowerSeries κ R}
    {y z : Fam G κ} (ha : Rep x a y) (hb : Rep x b z) (h : y = z) : a = b := by
  subst h
  obtain ⟨-, h2, h3, -⟩ := hR R G d x hx κ
  exact (h2 y (h3 a y ha)).unique ha hb

theorem actSt_of (_ : JetAlgSt) (hR : RepSt) (hM : MapSt) : ActSt := by
  intro R _ G _ _ d x hx O _ act Gl hF
  have hex : ∀ a, ∃ φ, IsMapOf x x (act.act a) φ := fun a => by
    haveI := act.hom a
    exact (hM R G G d x x hx hx (act.act a) (IsMonHom.one_hom _)).exists
  choose φ hφ using hex
  have hpt : ∀ (n : ℕ) (j : Fin n), ∃ y, Rep x (pt R (n := n) d j) y := fun n j =>
    ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists
  choose y hy using hpt
  have h1 : ∀ a, Rep x (φ a) (fun m => y 1 0 m ≫ act.act a) := fun a => by
    have := (hφ a).2 1 _ _ (hy 1 0)
    rwa [gt_comp1_pt_right] at this
  refine ⟨⟨φ, fun a => (hφ a).1, fun a => ?_, fun a b => ?_, fun a b => ?_, ?_⟩, hφ⟩
  · haveI := act.hom a
    refine rep_unique hR hx ((hφ a).2 2 _ _ (hF.2 2 _ _ _ _ (hy 2 0) (hy 2 1)))
      (hF.2 2 _ _ _ _ ((hφ a).2 2 _ _ (hy 2 0)) ((hφ a).2 2 _ _ (hy 2 1))) ?_
    funext m
    exact MonObj.mul_comp _ _ _
  · refine rep_unique hR hx (h1 (a + b)) (hF.2 1 _ _ _ _ (h1 a) (h1 b)) ?_
    funext m
    rw [act.add]
    exact MonObj.comp_mul _ _ _
  · refine rep_unique hR hx (h1 (a * b)) ((hφ a).2 1 _ _ (h1 b)) ?_
    funext m
    rw [mul_comm, act.mul, Category.assoc]
  · refine rep_unique hR hx (h1 1) (hy 1 0) ?_
    funext m
    rw [act.one, Category.comp_id]

end GlobalTheory.ChartAction
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer
variable {R : Type} [CommRing R]

theorem rep_jetAug_comp_trunc (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
  jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm

theorem rep_jetAug_comp_zero (κ : Type) (m : ℕ) :
    (jetAug R κ 0).comp (jetZeroR R κ m) = jetAug R κ m :=
  jet_ext fun j => (jetAug_zR 0 j).trans (jetAug_zR m j).symm

theorem isFPt_of_isUnivChart {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)}
    (hx : IsUnivChart G d x) : IsFPt x := by
  refine ⟨hx.1, fun m => ?_⟩
  rw [← rep_jetAug_comp_zero, ← spMap_comp, Category.assoc, hx.2.1 m]
  exact MonObj.comp_one _

theorem repSt_of_jetAlgSt (hJ : JetAlgSt) : RepSt := by
  intro R _ G _ d x hx κ _
  obtain ⟨hτ, htr, hinj, hsur, hsub⟩ := hJ R κ
  have hxa := (isFPt_of_isUnivChart hx).2
  have haug : ∀ (a : Fin d → MvPowerSeries κ R), (∀ j, constantCoeff (a j) = 0) → ∀ m
      (ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m), (∀ j, ψ (zR m j) = toJet m (a j)) →
      (jetAug R κ m).comp ψ = jetAug R (Fin d) m := by
    intro a ha m ψ hψ
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, hψ, (htr m _).2, ha, jetAug_zR]
  have hfp : ∀ a (y : Fam G κ), Rep x a y → IsFPt y := by
    rintro a y ⟨ha, hy⟩
    choose ψ hψ hy using hy
    refine ⟨fun m => ?_, fun m => ?_⟩
    · have e : (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
        refine jet_ext fun j => ?_
        rw [AlgHom.comp_apply, hψ, (htr m _).1]
        exact (hψ m j).symm
      rw [hy, hy, ← Category.assoc, spMap_comp, e, ← spMap_comp, Category.assoc, hx.1]
    · rw [hy, ← Category.assoc, spMap_comp, haug a ha m _ (hψ m), hxa]
  refine ⟨fun a ha => ?_, fun y hy => ?_, hfp, ⟨fun j => by simp, fun m => ?_⟩, ?_⟩
  · choose ψ hψ using fun m => (hsub (Fin d) a ha m).1
    refine ⟨fun m => spMap (ψ m) ≫ x m, ⟨ha, fun m => ⟨ψ m, hψ m, rfl⟩⟩, ?_⟩
    rintro y ⟨-, hy⟩
    funext m
    obtain ⟨ψ', h1, h2⟩ := hy m
    have : ψ' = ψ m := jet_ext fun j => (h1 j).trans (hψ m j).symm
    rw [h2, this]
  · have hU := fun m => hx.2.2 (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) (y m) (hy.2 m)
    choose ψ hψ hu using hU
    have hc : ∀ m, (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
      intro m
      have hk : RingHom.ker (jetAug R κ m) ^ (m + 1 + 1) = ⊥ := by
        rw [pow_succ (RingHom.ker (jetAug R κ m)) (m + 1), ker_jetAug_pow, Ideal.bot_mul]
      refine (hx.2.2 (JetR R κ m) (jetAug R κ m) (m + 1) hk (y m) (hy.2 m)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [← AlgHom.comp_assoc, rep_jetAug_comp_trunc, (hψ (m + 1)).1]
      · rw [← spMap_comp, Category.assoc, ← (hψ (m + 1)).2, hy.1 m]
      · rw [← AlgHom.comp_assoc, (hψ m).1, rep_jetAug_comp_trunc]
      · rw [← spMap_comp, Category.assoc, hx.1 m, ← (hψ m).2]
    have hex : ∀ j, ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = ψ m (zR m j) := fun j =>
      hsur (fun m => ψ m (zR m j)) (fun m => AlgHom.congr_fun (hc m) (zR (m + 1) j))
    choose a ha using hex
    refine ⟨a, ⟨fun j => ?_, fun m => ⟨ψ m, fun j => (ha j m).symm, (hψ m).2⟩⟩, ?_⟩
    · rw [← (htr 0 _).2, ha, ← jetAug_zR (R := R) 0 j]
      exact AlgHom.congr_fun (hψ 0).1 _
    · rintro a' ⟨ha', hy'⟩
      funext j
      refine hinj _ _ fun m => ?_
      obtain ⟨ψ', h1, h2⟩ := hy' m
      rw [ha, ← h1, hu m ψ' ⟨haug a' ha' m ψ' h1, h2⟩]
  · refine ⟨(Algebra.ofId R _).comp (jetAug R (Fin d) m), fun j => ?_, ?_⟩
    · obtain ⟨τ, h, -⟩ := hτ m
      rw [AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, ← h, map_zero]
    · rw [← spMap_comp, Category.assoc, hxa]
      exact (MonObj.comp_one _).symm
  · rintro κ' _ b ψ hb hψ a y ⟨ha, hy⟩
    obtain ⟨-, htr', -, -, hsub'⟩ := hJ R κ'
    have hs := fun m => (hsub' κ b hb m).2 (ψ m) (hψ m)
    refine ⟨fun j => ?_, fun m => ?_⟩
    · have e : (jetAug R κ' 0).comp (ψ 0) = jetAug R κ 0 := by
        refine jet_ext fun i => ?_
        rw [AlgHom.comp_apply, hψ, (htr' 0 _).2, hb, jetAug_zR]
      rw [← (htr' 0 _).2, ← hs, ← ha j, ← (htr 0 _).2]
      exact AlgHom.congr_fun e _
    · obtain ⟨φ, h1, h2⟩ := hy m
      refine ⟨(ψ m).comp φ, fun j => ?_, ?_⟩
      · rw [AlgHom.comp_apply, h1, hs]
      · show spMap (ψ m) ≫ y m = _
        rw [h2, ← Category.assoc, spMap_comp]

end GlobalTheory.JetSer
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

theorem IsMapOf.twoChart_rep_of_id {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} {d : ℕ}
    {x x' : Fam G (Fin d)} {φ : Pt R 1 d} (h : IsMapOf x x' (𝟙 G) φ) {n : ℕ} {a : Pt R n d}
    {y : Fam G (Fin n × Fin d)} (hy : Rep x a y) : Rep x' (comp1 φ a) y := by
  simpa only [Category.comp_id] using h.2 n a y hy

theorem twoChart_addOf_pt_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext l
  have : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  unfold addOf
  rw [this]
  unfold ev
  exact congrFun MvPowerSeries.subst_self (F l)

theorem twoChart_of_rep_map : JetAlgSt → RepSt → MapSt → TwoChartSt := by
  intro _ hR hM R _ G _ d x x' hx hx'
  obtain ⟨φ, hφ, -⟩ := hM R G G d x' x hx' hx (𝟙 G) (Category.comp_id _)
  obtain ⟨φi, hφi, -⟩ := hM R G G d x x' hx hx' (𝟙 G) (Category.comp_id _)
  have uniq : ∀ {z : Fam G (Fin d)}, IsUnivChart G d z → ∀ {n : ℕ} {a b : Pt R n d}
      {y : Fam G (Fin n × Fin d)}, Rep z a y → Rep z b y → a = b := fun {z} hz {n a b y} ha hb =>
    ((hR R G d z hz (Fin n × Fin d)).2.1 y ((hR R G d z hz (Fin n × Fin d)).2.2.1 a y ha)).unique ha hb
  have ex : ∀ {z : Fam G (Fin d)}, IsUnivChart G d z → ∀ {n : ℕ} (j : Fin n),
      ∃ y : Fam G (Fin n × Fin d), Rep z (pt R d j) y := fun {z} hz {n} j =>
    ((hR R G d z hz (Fin n × Fin d)).1 (pt R d j) (gp_pt j)).exists
  refine ⟨φ, φi, ⟨hφ.1, hφi.1, ?_, ?_⟩, hφ, hφi, fun F F' hF hF' i => ?_, fun f α α' hα hα' => ?_⟩
  · obtain ⟨y, hy⟩ := ex hx (0 : Fin 1)
    have h := hφ.twoChart_rep_of_id (hφi.twoChart_rep_of_id hy)
    rw [gt_comp1_pt_right] at h
    exact uniq hx h hy
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 1)
    have h := hφi.twoChart_rep_of_id (hφ.twoChart_rep_of_id hy)
    rw [gt_comp1_pt_right] at h
    exact uniq hx' h hy
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 2)
    obtain ⟨z, hz⟩ := ex hx' (1 : Fin 2)
    have h₁ := hF'.2 2 _ _ y z hy hz
    rw [twoChart_addOf_pt_pt] at h₁
    have h₂ := hφi.twoChart_rep_of_id (hF.2 2 _ _ y z (hφ.twoChart_rep_of_id hy) (hφ.twoChart_rep_of_id hz))
    exact congrFun (uniq hx' h₁ h₂) i
  · obtain ⟨y, hy⟩ := ex hx' (0 : Fin 1)
    have h₁ := hα'.2 1 _ y hy
    have h₂ := hφi.twoChart_rep_of_id (hα.2 1 _ y (hφ.twoChart_rep_of_id hy))
    rw [gt_comp1_pt_right] at h₁ h₂
    exact uniq hx' h₁ h₂

end GlobalTheory.JetSer
end
end
