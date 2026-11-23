module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecTransport

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {β : Y ⟶ X}

lemma le_pull (j : Fin 1 → L.ι) (i : M.ι) :
    LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i ≤ (L.pull β).U (fun _ => j 0) ⊓ M.U i :=
  fun _ hy => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 0, hy.2⟩

lemma le_one (j : Fin 1 → L.ι) (i : M.ι) :
    LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i ≤ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def piece (ℓ : LB.Iso M (L.pull β)) (c : Γ(Y, ⊤)) (k : ℕ) (σ' : H0 M k) (j : Fin 1 → L.ι) (i : M.ι) :
    Γ(Y, LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i) :=
  (Y.presheaf.map (homOfLE le_top).op).hom c * ((res (le_pull j i) (ℓ.s (fun _ => j 0, i))) ^ k).val *
    (Y.presheaf.map (homOfLE (le_one j i)).op).hom (σ'.f (fun _ => i))

theorem gs_piece (ℓ : LB.Iso M (L.pull β)) (c : Γ(Y, ⊤)) (k : ℕ) (σ' : H0 M k) (j : Fin 1 → L.ι) (i : M.ι)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i) :
    gs r z _ (piece ℓ c k σ' j i) = gs r z ⊤ c * (gw ℓ r z (j 0) i ^ k).val *
      gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) := by
  exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
    (gs_res r z le_top hz c) ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_pow _ _ _).trans
      (congrArg (· ^ k) (gm_res r z (le_pull j i) hz _)))))))
    (gs_res r z (le_one j i) hz _))

theorem indep (hL : L.IsLB) (ℓ : LB.Iso M (L.pull β)) (hℓ : PGen ℓ) (k : ℕ) (σ' : H0 M k) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (j₀ : L.ι) (i i' : M.ι) (hj : β (r z) ∈ L.U j₀) (hi : r z ∈ M.U i) (hi' : r z ∈ M.U i') :
    (gw ℓ r z j₀ i ^ k).val * gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) =
      (gw ℓ r z j₀ i' ^ k).val * gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i')) (σ'.f (fun _ => i')) := by
  have e1 := hℓ Z r z j₀ j₀ i i' hj hj hi hi'
  rw [gm_self hL (r ≫ β) z hj, _root_.one_mul] at e1
  have hm : r z ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have hm' : r z ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have e2 := sec_trans σ' r z hm hm'
  have e3 : trF (L := M) (fun _ : Fin 1 => 𝟙 Y) (fun _ => (k : ℤ)) r z (fun _ => i) (fun _ => i') =
      gm r z _ (M.g i i') ^ k := by
    simp only [trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast]
  rw [e2, e3, ← _root_.mul_assoc, ← Units.val_mul, e1, mul_pow, inv_pow,
    _root_.mul_comm ((gm r z _ (M.g i i') ^ k)⁻¹), _root_.mul_assoc, _root_.inv_mul_cancel, _root_.mul_one]

theorem exists_transport (hL : L.IsLB) (hM : M.IsLB) (ℓ : LB.Iso M (L.pull β)) (hℓ : ℓ.IsGen) (c : Γ(Y, ⊤))
    (k : ℕ) (σ' : H0 M k) : ∃ σ : SecK L β k, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good M z J' →
      sval σ r z J = gs r z ⊤ c * (gw ℓ r z (J (r ≫ β)) (J' r) ^ k).val * sval σ' r z J' := by
  have hP := (isGen_iff ℓ).1 hℓ
  have glue : ∀ j : Fin 1 → L.ι, ∃ a : Γ(Y, LB.wchart L (fun _ : Fin 1 => β) j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (i : M.ι), r z ∈ LB.wchart L (fun _ : Fin 1 => β) j → r z ∈ M.U i →
      gs r z _ a = gs r z ⊤ c * (gw ℓ r z (j 0) i ^ k).val *
        gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) := by
    intro j
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (fun i : M.ι => LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i)
      (LB.wchart L (fun _ : Fin 1 => β) j) (fun i => homOfLE inf_le_left)
      (fun y hy => Opens.mem_iSup.2 ⟨(exists_chart hM y).choose, hy, (exists_chart hM y).choose_spec⟩)
      (fun i => piece ℓ c k σ' j i) (fun i i' => fn_ext fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [gs_piece ℓ c k σ' j i (𝟙 Y) y hy.1, gs_piece ℓ c k σ' j i' (𝟙 Y) y hy.2, _root_.mul_assoc, _root_.mul_assoc]
        exact congrArg _ (indep hL ℓ hP k σ' (𝟙 Y) y (j 0) i i' (Set.mem_iInter.1 hy.1.1 0) hy.1.2 hy.2.2))
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha i)).trans (gs_piece ℓ c k σ' j i r z hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    change gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => β) j) (a j) =
      _ * gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => β) j') (a j')
    rw [ha j _ (𝟙 Y) y i hy.1 hi, ha j' _ (𝟙 Y) y i hy.2 hi]
    have e1 := hP Y (𝟙 Y) y (j 0) (j' 0) i i (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0) hi hi
    rw [gm_self hM (𝟙 Y) y hi, inv_one, _root_.mul_one] at e1
    rw [e1]
    simp only [Fin.prod_univ_one, zpow_natCast, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  · rw [sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
    exact ha _ Z r z (J' r) (hJ.mem (fun _ : Fin 1 => β) r) (hJ' r)

end GlobalTheory.Mum.SecTransport

namespace GlobalTheory.Mum

theorem Trait.exists_carries : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W)
    (σ' : H0 T.U.LG.L k), ∃ σ'' : SecK C.P.L.L T.β k, T.Carries u σ' σ'' := by
  intro R _ _ _ D C W _ _ _ T k u σ'
  exact SecTransport.exists_transport C.P.L.isLB T.U.LG.isLB T.ℓ T.ℓ_gen (scal T.G.hom u) k σ'

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

theorem unit_nonfield : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ¬ IsField R → ∀ b : W, b ≠ 0 → ∀ z : Z, IsUnit (gs p z ⊤ (scal T.G.hom b)) := by
  intro R _ _ _ D C W _ _ _ T Z p p' hpp hR b hb z

  have hw : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ jK R := by
    rw [← T.ξ_π, ← C.gp_π, ← Category.assoc T.G.hom, ← T.cart.1.w, ← Category.assoc C.A.A.hom, ← C.α_cart.1.w]
    simp only [← Category.assoc]; rw [hpp]
  have hpt := congrArg (fun g => (g z).asIdeal) hw
  simp only [Scheme.Hom.comp_apply] at hpt
  set P := ((p ≫ T.G.hom) z) with hP
  have hc : P.asIdeal.comap T.φ = ⊥ := by
    have e1 : (spMap T.φ ((T.G.hom) (p z))).asIdeal = P.asIdeal.comap T.φ := by
      rw [hP, Scheme.Hom.comp_apply]; rfl
    rw [← e1, hpt]
    have e2 : ((jK R) ((C.A.A.hom) (p' z))).asIdeal = ((C.A.A.hom) (p' z)).asIdeal.comap (algebraMap R (FractionRing R)) := rfl
    rw [e2]
    have hbot : ((C.A.A.hom) (p' z)).asIdeal = ⊥ := by
      have := ((C.A.A.hom) (p' z)).isPrime
      exact Ideal.eq_bot_of_prime _
    rw [hbot]
    exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
  have hdvr : IsDiscreteValuationRing W := T.cdvr.1
  have hPbot : P.asIdeal = ⊥ := by
    by_contra hne
    have hmax : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.isPrime hne
    have hm : P.asIdeal = maximalIdeal W := IsLocalRing.eq_maximalIdeal hmax
    have hRm : maximalIdeal R ≠ ⊥ := fun h => hR ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRm
    have hl := T.loc
    have hφr : T.φ r ∈ P.asIdeal := by
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 hr (isUnit_of_map_unit T.φ r hu)
    have : r ∈ P.asIdeal.comap T.φ := hφr
    rw [hc] at this
    exact hr0 ((Submodule.mem_bot R).1 this)
  have hmem : (p ≫ T.G.hom) z ∈ (Sp W).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) := by
    rw [basicOpen_eq_of_affine]
    show b ∉ ((p ≫ T.G.hom) z).asIdeal
    rw [← hP, hPbot]; exact fun h => hb ((Submodule.mem_bot W).1 h)
  have hpull : gs p z ⊤ (scal T.G.hom b) = gs (p ≫ T.G.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) :=
    gs_pull p T.G.hom z ⊤ trivial _
  rw [hpull, gs_eq _ z ⊤ trivial]
  have hz : z ∈ Z.basicOpen (((p ≫ T.G.hom).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hmem
  exact (Scheme.mem_basicOpen Z _ z (by trivial)).1 hz

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibreVal

variable {X Y Z : Scheme.{0}}

theorem gs_pow (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by simp only [gs_eq f y U h, map_pow]

theorem gs_sum (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ) (a : κ → Γ(X, U)) :
    gs f y U (S.sum a) = S.sum (fun i => gs f y U (a i)) := by simp only [gs_eq f y U h, map_sum]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem mem_finset_inf {κ : Type} (S : Finset κ) (V : κ → X.Opens) (x : X) (h : ∀ i ∈ S, x ∈ V i) : x ∈ S.inf V :=
  Finset.inf_induction (p := fun W : X.Opens => x ∈ W) trivial (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) h

end GlobalTheory.Mum.FibreVal

theorem GlobalTheory.Mum.FibreVal.pG_app_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {V : D.P.A.left.Opens} (x : Γ(D.P.A.left, V))
    (h : ((pullback.fst D.P.A.hom (thick R I e)).app V).hom x = 0) : (g.pG.left.app V).hom x = 0 := by
  have h' := congrArg (g.q.left.app (pullback.fst D.P.A.hom (thick R I e) ⁻¹ᵁ V)).hom h
  rw [map_zero] at h'
  exact h'

theorem GlobalTheory.Mum.FibreVal.sval_comp_eq_zero {X W Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (g : Z ⟶ W) (p : W ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    (h : (p.app (LB.wchart L φ (fun k => J ((g ≫ p) ≫ φ k)))).hom (s.f (fun k => J ((g ≫ p) ≫ φ k))) = 0) :
    sval s (g ≫ p) z J = 0 := by
  have e1 := gs_pull g p z (LB.wchart L φ (fun k => J ((g ≫ p) ≫ φ k))) (hJ.mem φ (g ≫ p)) (s.f (fun k => J ((g ≫ p) ≫ φ k)))
  rw [h, gs_zero] at e1
  exact e1.symm



open GlobalTheory.Mum.FibreVal in
theorem GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  intro R _ _ _ D A G _ _ U Y T g y hP k z J J' hJ hJ'
  let pp : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) := (fun _ => J' (g ≫ (U.gt 0).pG.left), fun _ => J (g ≫ (fstG (maximalIdeal R) 0 G).left))
  have hpp : g z ∈ (LB.div (D.toPre.P.L.pull (U.gt 0).pG.left) (U.LG.L.pull (fstG (maximalIdeal R) 0 G).left)).U pp :=
    ⟨Set.mem_iInter.2 fun _ => hJ' (g ≫ (U.gt 0).pG.left), Set.mem_iInter.2 fun _ => hJ (g ≫ (fstG (maximalIdeal R) 0 G).left)⟩
  refine ⟨(gm g z _ ((U.w 0).s pp) ^ k)⁻¹, ?_⟩
  intro α b τ F s hT hL hE
  obtain ⟨S, h0, hS⟩ := hE
  let j₁ : Fin 1 → U.LG.L.ι := fun _ => J (g ≫ (fstG (maximalIdeal R) 0 G).left)
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β i => J' ((g ≫ (U.gt 0).pG.left) ≫ D.toPre.famφB β i)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β i => J' (g ≫ D.toPre.Oφ (U.gt 0).pG β i)
  have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2)))
        (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    have key : ∀ c, (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) c =
        J' (g ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2))) c) := by
      rintro (a | a | a) <;> simp [jf, jt, pp]
    intro a c e
    rw [key, key, e]
  have e := hS pp j₁ jf jt rfl hcoh
  have hz : g z ∈ U.expW 0 pp j₁ S jf jt :=
    ⟨⟨hpp, hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (g ≫ (fstG (maximalIdeal R) 0 G).left)⟩, mem_finset_inf _ _ _ fun β _ =>
      ⟨hJ'.mem (D.toPre.famφB β) (g ≫ (U.gt 0).pG.left), hJ'.mem (D.toPre.Oφ (U.gt 0).pG β) g⟩⟩
  have e' := congrArg (gs g z (U.expW 0 pp j₁ S jf jt)) e
  rw [gs_mul g z _ hz, gs_pow g z _ hz, gs_unit g z _ hz, gm_res g z _ hz, gs_res g z _ hz] at e'
  erw [gs_pull g (fstG (maximalIdeal R) 0 G).left z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁) (Set.mem_iInter.2 fun _ => hJ (g ≫ (fstG (maximalIdeal R) 0 G).left))] at e'
  rw [gs_sum g z _ hz] at e'
  have hterm : ∀ (β : D.toPre.X) (hβ : β ∈ S),
      gs g z (U.expW 0 pp j₁ S jf jt)
        (((thickObj R (maximalIdeal R) 0 G).left.presheaf.map (homOfLE (U.expW_le_f 0 pp j₁ jf jt hβ)).op).hom
            (((U.gt 0).pG.left.app _).hom ((F.f β).f (jf β))) *
          (Semi.res (U.expWeight_le_chart_weight 0 pp j₁ jf jt hβ) (((U.gt 0).t β).s (jt β))).val) =
      sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val := by
    intro β hβ
    rw [gs_mul g z _ hz, gs_res g z _ hz, gs_unit g z _ hz]
    erw [gm_res g z _ hz]
    erw [gs_pull g (U.gt 0).pG.left z _ (hJ'.mem (D.toPre.famφB β) (g ≫ (U.gt 0).pG.left))]
    rfl
  replace e' := (e'.trans (Finset.sum_congr rfl fun (β : S) _ => hterm β.1 β.2)).trans
    (Finset.sum_attach S (fun β => sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val))
  have hsum : ∑ β ∈ S, sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val =
      sval (F.f α) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t α) g z J').val := by
    apply Finset.sum_eq_single α
    · intro β _ hne
      rw [sval_comp_eq_zero (F.f β) g (U.gt 0).pG.left z hJ' (pG_app_eq_zero (U.gt 0) _ (hL.2 β hne _)), zero_mul]
    · intro hα
      rw [sval_comp_eq_zero (F.f α) g (U.gt 0).pG.left z hJ' (h0 α hα _), zero_mul]
  rw [hsum] at e'
  have hq : (y ≫ Y.q).left = g ≫ (U.gt 0).pG.left := by
    have h1 := (Y.rep.1 T Y.H y (𝟙 Y.H)).1
    rw [Category.comp_id] at h1
    rw [Over.comp_left]
    exact h1.symm.trans hP.1
  have ht : val ((Y.Φ T y).s α) (𝟙 _) z J' = val ((U.gt 0).t α) g z J' :=
    (val_corr hJ' (hP.2 α) (𝟙 _)).trans ((val_pull hJ' _ g (𝟙 _)).trans (by rw [Category.id_comp]))
  rw [hT T y z J' hJ', hq, ht, ← hL.1, ← e',
    sval_of s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J j₁ (fun _ => by rw [Category.comp_id]),
    ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
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

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

namespace Ext

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre

theorem exists_torusPt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) D.X) : ∃ g : GtPt D T, g.b = 1 ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      (val (g.s χ) r y J).val = gs r y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  let u : Multiplicative D.X →* Γ(T.left, ⊤) :=
    { toFun := fun χ => (coord x).hom (AddMonoidAlgebra.single χ.toAdd 1)
      map_one' := Diag.coord_single_zero x
      map_mul' := fun a b => Diag.coord_single_add x _ _ }
  let v : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) := fun χ =>
    ⟨fun _ => res le_top (u.toHomUnits (Multiplicative.ofAdd χ))⟩
  have hv : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (v χ) r y J = gm r y ⊤ (u.toHomUnits (Multiplicative.ofAdd χ)) := fun χ Z r y J hJ =>
    gm_res r y _ (hJ.mem PEmpty.elim r) _
  obtain ⟨g, hb, hg⟩ := exists_pt (1 : T ⟶ D.P.A) v (fun χ i j => by
      obtain rfl : i = j := funext fun k => k.elim
      have e : (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
        dsimp only [LB.LinComb]
        erw [Fintype.prod_empty]
        rfl
      rw [e, _root_.one_mul])
    (fun χ U _ h => by
      rw [prod_pt, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel])
    (fun y J hJ => by rw [hv _ _ _ _ _ hJ, ofAdd_zero, map_one, map_one])
    (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, _root_.mul_one, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, ofAdd_add, map_mul, map_mul])
  exact ⟨g, hb, fun χ Z r y J hJ => by
    rw [hg _ _ _ _ _ hJ, hv _ _ _ _ _ hJ]; exact (gs_unit r y ⊤ trivial _).symm⟩

variable (Y : Ext D)

theorem pt_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

def torI : splitTorus (Sp R) D.X ⟶ Y.H :=
  (Y.Φ _).symm (exists_torusPt (D := D) (𝟙 _)).choose

theorem torI_pt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) D.X) : (Y.Φ T (x ≫ Y.torI)).b = 1 ∧
    ∀ (χ : D.X) y J, Good D.P.L y J →
      (cv (Y.Φ T (x ≫ Y.torI)) χ y J).val = gs (𝟙 _) y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  obtain ⟨h₁, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T _ x Y.torI)
  obtain ⟨e₁, e₂⟩ := (exists_torusPt (D := D) (𝟙 _)).choose_spec
  have e : Y.Φ _ Y.torI = (exists_torusPt (D := D) (𝟙 _)).choose := Equiv.apply_symm_apply _ _
  rw [e] at h₁ h₂
  refine ⟨by rw [h₁, e₁, MonObj.comp_one], fun χ y J hJ => ?_⟩
  rw [h₂ χ y J hJ, e₂ χ _ _ y J hJ]
  conv_rhs => rw [← Category.comp_id x, coord_comp]
  exact (gs_eq x.left y ⊤ trivial _).trans (gs_eq (𝟙 _) y ⊤ trivial _).symm

theorem torI_q : Y.torI ≫ Y.q = 1 := by
  have h := (Y.torI_pt (𝟙 _)).1
  rwa [pt_b, Category.id_comp] at h

theorem isMonHom_torI : IsMonHom Y.torI :=
  isMonHom_of_mul _ fun T x x' => (Y.Φ T).injective <| by
    refine isAdd_unique ((TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => Units.ext ?_⟩) (Y.rep.2 T _ _)
    · rw [(Y.torI_pt _).1, (Y.torI_pt _).1, (Y.torI_pt _).1, _root_.mul_one]
    · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [(Y.torI_pt x').1, C.face₃, _root_.mul_one, Units.val_mul, (Y.torI_pt _).2 χ y J hJ, (Y.torI_pt _).2 χ y J hJ,
        (Y.torI_pt _).2 χ y J hJ]
      exact (congrArg (gs _ y ⊤) (Diag.coord_mul x x' χ)).trans (gs_mul (𝟙 _) y ⊤ trivial _ _)

theorem isKernel_torI : IsPullback Y.torI (toUnit _) Y.q η[D.P.A] := by
  have ex : ∀ {T : Over (Sp R)} y, ∃ J, Good D.P.L (Z := T.left) y J := fun y => by
    choose I hI using fun χ => exists_chart D.P.isLB ((χ : _ ⟶ D.P.A.left) y)
    exact ⟨I, hI⟩
  refine Diag.isPullback_toUnit_of_lift _ Y.torI_q (fun {T} a b h => Diag.hom_ext fun χ => fn_ext fun y _ => ?_)
    fun {T} x hx => ?_
  · obtain ⟨J, hJ⟩ := ex y
    exact ((Y.torI_pt a).2 χ y J hJ).symm.trans (h ▸ (Y.torI_pt b).2 χ y J hJ)
  · have hb : (Y.Φ T x).b = 1 := (Y.pt_b x).trans hx
    have hF : ∀ χ, FormEq (DegPre.gtφT D T (Y.Φ T x).b χ) DegPre.gtε (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun χ U _ h => by
        rw [prod_pt, hb, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
    choose s _ vs using fun χ => exists_gen D.P.isLB (hF χ) _ ((Y.Φ T x).isGen χ)
    have le : (⊤ : T.left.Opens) ≤ LB.wchart D.P.L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun _ _ => Set.mem_iInter.2 fun k => k.elim
    let u : D.X → Γ(T.left, ⊤)ˣ := fun χ => res le ((s χ).s PEmpty.elim)
    have hu : ∀ χ y J, Good D.P.L y J → gs (𝟙 _) y ⊤ (u χ).val = (cv (Y.Φ T x) χ y J).val := fun χ y J hJ =>
      (gs_unit _ y ⊤ trivial _).trans (congrArg Units.val ((gm_res _ y le trivial _).trans
        ((val_of (s χ) _ y J PEmpty.elim fun k => k.elim).symm.trans (vs χ _ _ y J hJ))))
    let g : Multiplicative D.X →* Γ(T.left, ⊤) :=
      { toFun := fun χ => (u χ.toAdd).val
        map_one' := fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          refine (hu 0 y J hJ).trans ?_
          rw [cv_zero _ hJ, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
        map_mul' := fun a b => fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
          have e := cv_add (Y.Φ T x) hJ a.toAdd b.toAdd
          rw [hb, C.face₃, _root_.mul_one] at e
          refine (hu _ y J hJ).trans (Eq.trans ?_ (gs_mul _ y ⊤ trivial _ _).symm)
          exact (congrArg Units.val e).trans (congrArg₂ (· * ·) (hu _ y J hJ) (hu _ y J hJ)).symm }
    refine ⟨Diag.ofChar T g, (Y.Φ T).injective (pt_ext ((Y.torI_pt _).1.trans hb.symm) fun χ y J hJ => Units.ext ?_)⟩
    exact ((Y.torI_pt _).2 χ y J hJ).trans ((congrArg (gs _ y ⊤) (Diag.coord_ofChar T g χ)).trans (hu χ y J hJ))

theorem cv_torI {Z : Over (Sp R)} (t : Z ⟶ splitTorus (Sp R) D.X) (χ : D.X) (z : Z.left) J (hJ : Good D.P.L z J) :
    cv (Y.Φ Z (t ≫ Y.torI)) χ z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) := by
  have hc : t.left.appTop.hom (charUnit (Sp R) D.X χ).val = (coord t).hom (AddMonoidAlgebra.single χ 1) := by
    rw [GlobalTheory.SplitTorus.charUnit_val]
    conv_rhs => rw [← Category.comp_id t, coord_comp]
    rfl
  refine Units.ext (((Y.torI_pt t).2 χ z J hJ).trans ?_)
  rw [← gs_unit t.left z ⊤ trivial, ← hc]
  exact (gs_eq (𝟙 _) z ⊤ trivial _).trans (gs_eq t.left z ⊤ trivial _).symm

theorem cv_torI_mul {Z : Over (Sp R)} (t : Z ⟶ splitTorus (Sp R) D.X) (g : Z ⟶ Y.H) (χ : D.X) (z : Z.left) J
    (hJ : Good D.P.L z J) :
    cv (Y.Φ Z ((t ≫ Y.torI) * g)) χ z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * cv (Y.Φ Z g) χ z J := by
  have h := ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 Z (t ≫ Y.torI) g)).2 χ z J hJ
  have C : IsCub (th D (T := Z) z J) := isCub_cubV D.cub hJ
  rw [(Y.torI_pt t).1, C.face₂, _root_.mul_one, Y.cv_torI t χ z J hJ] at h
  exact h

end Ext

theorem ext_torus : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D), ∃ i : splitTorus (Sp R) D.X ⟶ Y.H,
    IsMonHom i ∧ IsPullback i (toUnit _) Y.q η[D.P.A] ∧ ∀ (χ : D.X) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) D.X)
      (g : Z ⟶ Y.H) (z : Z.left) J, Good D.P.L z J →
        val ((Y.Φ Z ((t ≫ i) * g)).s χ) (𝟙 _) z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * val ((Y.Φ Z g).s χ) (𝟙 _) z J :=
  fun _ _ _ _ Y => ⟨Y.torI, Y.isMonHom_torI, Y.isKernel_torI, fun χ _ t g z J hJ => Y.cv_torI_mul t g χ z J hJ⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SecsDesc

theorem assemble (hE : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) (hN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F) (hT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), (∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) ∧ ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C
  obtain ⟨k₀, hk₀⟩ := hN R hR D C
  have hn : 1 < C.n := C.n_prime.one_lt
  have part1 : ∀ j ≥ k₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j),
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F := by
    intro j hj
    obtain ⟨Φ, hΦ⟩ := hE R hR D C j
    exact hk₀ (C.n ^ j) (hj.trans (Nat.lt_pow_self hn).le) Φ hΦ
  refine ⟨⟨k₀, part1⟩, fun F₁ => ?_⟩
  have key : ∀ k, k = C.n ^ (k₀ * 2) → ∃ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k,
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F := by
    rintro k rfl
    exact part1 _ (Nat.le_mul_of_pos_right _ (by norm_num))
  obtain ⟨Φ, hΦ⟩ := key ((C.n ^ k₀) ^ 2) (pow_mul _ _ _).symm
  exact hT R hR D C (C.n ^ k₀) (C.n_odd.pow) Φ hΦ F₁

end GlobalTheory.Mum.SecsDesc
end
