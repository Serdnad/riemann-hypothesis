module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle019
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem lbIso_pw_pull_of_hasGen {X : Scheme.{0}} {L : LB X} (F : X ⟶ X) (t : ℤ)
    (h : MulPull.HasGen L (K := Fin 2) ![F, 𝟙 X] ![1, -t]) : LBIso (pw L t) (L.pull F) := by
  obtain ⟨a, ha⟩ := h
  have mem : ∀ (x : X) (j k : L.ι), F x ∈ L.U j → x ∈ L.U k → x ∈ LB.wchart L ![F, 𝟙 X] ![j, k] :=
    fun x j k hj hk => Set.mem_iInter.2 fun i => by
      fin_cases i
      · exact hj
      · exact hk
  have le : ∀ p : (L.pull F).ι × L.ι,
      (L.pull F).U p.1 ⊓ L.U p.2 ≤ LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2] :=
    fun p x hx => mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso (pw L t) (L.pull F) := ⟨fun p => res (le p) (a.s _)⟩
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_⟩
  have e : ∀ j k, F (r y) ∈ L.U j → r y ∈ L.U k →
      gw w r y j k = gm r y (LB.wchart L ![F, 𝟙 X] ![j, k]) (a.s ![j, k]) := fun j k hj hk =>
    gm_res r y (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _
  rw [e j k hj hk, e j' k' hj' hk', gen_trans ha r y (mem _ _ _ hj hk) (mem _ _ _ hj' hk'), trF, Fin.prod_univ_two]
  congr 1
  show gm (r ≫ F) y _ (L.g j j') ^ (1 : ℤ) * gm (r ≫ 𝟙 X) y _ (L.g k k') ^ (-t) =
    gm (r ≫ F) y _ (L.g j j') * (gm r y (L.U k ⊓ L.U k') (L.g k k' ^ t))⁻¹
  rw [zpow_one, Category.comp_id, map_zpow, zpow_neg]

theorem CP.lbIso_pw_pull_pow {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ) :
    LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by
  have hL := M.L.isLB
  have hcube : MulPull.HasGen M.L.L (thφ B (x3 B)) thε := ⟨M.c.t, M.c.isGen⟩
  have hrig : MulPull.HasGen M.L.L (K := PUnit) (fun _ => eSec B) (fun _ => 1) := ⟨M.L.rig, M.L.rigGen⟩
  have hsym : MulPull.HasGen M.L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1] := ⟨M.sym, M.sym_gen⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 B) ((hrig.pull B.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one, one_left]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) n
  refine lbIso_pw_pull_of_hasGen _ _ (h.inv.of_formEq hL fun U _ h => ?_)
  rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
  rfl

theorem lbIso_pw_pull_pow_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ), LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) :=
  fun _ _ _ _ _ _ M n => M.lbIso_pw_pull_pow n

end GlobalTheory.UU
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.SymSec
open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem sec_gs {N : LB X} (s : LB.Sec N) (r : Y ⟶ X) (y : Y) {i j : N.ι} (hi : r y ∈ N.U i) (hj : r y ∈ N.U j) :
    gs r y (N.U i) (s.f i) = (gm r y (N.U i ⊓ N.U j) (N.g i j)).val * gs r y (N.U j) (s.f j) := by
  have hm : r y ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  exact (gs_res r y _ hm _).symm.trans ((congrArg (gs r y _) (s.compat i j)).trans ((gs_mul r y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r y _ hm _) (gs_res r y _ hm _))))

theorem glue {N : LB X} (hN : N.IsLB) {I : Type} (W : I → X.Opens) (c : I → N.ι) (hc : ∀ i, W i ≤ N.U (c i))
    (hW : ∀ x : X, ∃ i, x ∈ W i) (a : ∀ i, Γ(X, W i))
    (h : ∀ i i' x, x ∈ W i → x ∈ W i' → gs (𝟙 X) x (W i) (a i) =
      (gm (𝟙 X) x (N.U (c i) ⊓ N.U (c i')) (N.g (c i) (c i'))).val * gs (𝟙 X) x (W i') (a i')) :
    ∃ s : LB.Sec N, ∀ i x, x ∈ W i → gs (𝟙 X) x (N.U (c i)) (s.f (c i)) = gs (𝟙 X) x (W i) (a i) := by
  have gl : ∀ j : N.ι, ∃ b : Γ(X, N.U j), ∀ i x, x ∈ N.U j → x ∈ W i →
      gs (𝟙 X) x (N.U j) b = (gm (𝟙 X) x (N.U j ⊓ N.U (c i)) (N.g j (c i))).val * gs (𝟙 X) x (W i) (a i) := by
    intro j
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X, N.U j ⊓ W i), ∀ i x, x ∈ N.U j ⊓ W i →
        gs (𝟙 X) x _ (u i) = (gm (𝟙 X) x (N.U j ⊓ N.U (c i)) (N.g j (c i))).val * gs (𝟙 X) x (W i) (a i) :=
      ⟨fun i => (X.presheaf.map (homOfLE (inf_le_inf_left _ (hc i) : N.U j ⊓ W i ≤ N.U j ⊓ N.U (c i))).op).hom
          (N.g j (c i)).val * (X.presheaf.map (homOfLE (inf_le_right : N.U j ⊓ W i ≤ W i)).op).hom (a i),
        fun i x hx => (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_res _ x _ hx _).trans
          (gs_unit (𝟙 X) x (N.U j ⊓ N.U (c i)) ⟨hx.1, hc i hx.2⟩ _)) (gs_res _ x _ hx _))⟩
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun i => N.U j ⊓ W i) (N.U j)
      (fun i => homOfLE inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := hW x
        exact Opens.mem_iSup.2 ⟨i, hx, hi⟩) u
      (fun i i' => fn_ext (V := (N.U j ⊓ W i) ⊓ (N.U j ⊓ W i')) fun x hx => by
        refine (gs_res (𝟙 X) x inf_le_left hx _).trans (Eq.trans ?_ (gs_res (𝟙 X) x inf_le_right hx _).symm)
        rw [hu i x hx.1, hu i' x hx.2, h i i' x hx.1.2 hx.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hN (𝟙 X) x hx.1.1 (hc i hx.1.2) (hc i' hx.2.2)])
    refine ⟨b, fun i x h₁ h₂ => ?_⟩
    have hx : x ∈ N.U j ⊓ W i := ⟨h₁, h₂⟩
    exact (gs_res (𝟙 X) x inf_le_left hx b).symm.trans ((congrArg (gs (𝟙 X) x (N.U j ⊓ W i)) (hb i)).trans
      (hu i x hx))
  choose b hb using gl
  refine ⟨⟨b, fun j j' => fn_ext fun x hx => ?_⟩, fun i x hx => ?_⟩
  · obtain ⟨i, hi⟩ := hW x
    refine (gs_res (𝟙 X) x _ hx _).trans (Eq.trans ?_ ((gs_mul (𝟙 X) x _ hx _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)
    rw [hb j i x hx.1 hi, hb j' i x hx.2 hi, ← _root_.mul_assoc, ← Units.val_mul,
      gm_cocycle hN (𝟙 X) x hx.1 hx.2 (hc i hi)]
  · show gs (𝟙 X) x _ (b (c i)) = _
    rw [hb (c i) i x (hc i hx) hx, gm_self hN (𝟙 X) x (hc i hx), Units.val_one, _root_.one_mul]

theorem gs_ne [IsIntegral Y] (r : Y ⟶ X) [IsIso r] (y : Y) {U : X.Opens} (hy : r y ∈ U) {a : Γ(X, U)} (ha : a ≠ 0) :
    gs r y U a ≠ 0 := by
  rw [gs_eq r y U hy]
  have h₁ : Function.Injective (r.app U).hom := (ConcreteCategory.bijective_of_isIso (r.app U)).1
  intro h
  apply ha
  apply h₁
  apply germ_injective_of_isIntegral Y y (show y ∈ r ⁻¹ᵁ U from hy)
  rw [map_zero, map_zero]
  exact h

theorem sec_ne [IsIntegral X] {N : LB X} (s : LB.Sec N) (hs : ∃ j, s.f j ≠ 0) {i : N.ι} {x : X} (hx : x ∈ N.U i) :
    s.f i ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (N.U j : Set X).Nonempty := by
    by_contra hn
    exact hj (fn_ext fun y hy => (hn ⟨y, hy⟩).elim)
  obtain ⟨y, hy, hyi, hyj⟩ := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible _ _ (N.U i).isOpen
    (N.U j).isOpen ⟨x, trivial, hx⟩ (by simpa using hne)
  intro h0
  have e := sec_gs s (𝟙 X) y (i := j) (j := i) hyj hyi
  rw [h0, gs_eq (𝟙 X) y (N.U i) hyi, map_zero, map_zero, mul_zero] at e
  exact gs_ne (𝟙 X) y hyj hj e

theorem alg {R : Type} [CommRing R] (k : ℕ) {A B C D E F E' F' : Rˣ} {P Q P' Q' : R}
    (e₁ : P' = (A ^ k * C⁻¹).val * P) (e₂ : Q' = (B ^ k * D⁻¹).val * Q) (e₃ : E' = C * D * E)
    (e₄ : F' = B * A⁻¹ * F) :
    P' * Q' * (E' * (F' ^ k)⁻¹).val = (A ^ (2 * k)).val * (P * Q * (E * (F ^ k)⁻¹).val) := by
  subst e₁ e₂ e₃ e₄
  have : (A ^ k * C⁻¹) * (B ^ k * D⁻¹) * (C * D * E * ((B * A⁻¹ * F) ^ k)⁻¹) = A ^ (2 * k) * (E * (F ^ k)⁻¹) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  have := congrArg Units.val this
  simp only [Units.val_mul] at this ⊢
  linear_combination (P * Q) * this

theorem core [IsIntegral X] {L O : LB X} (hL : L.IsLB) (hO : O.IsLB) (σ z : X ⟶ X) [IsIso σ] (p₀ : O.ι)
    (hz : ∀ x, z x ∈ O.U p₀) (sy : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1])) (hsy : sy.IsGen)
    (t : LB.Gen (LB.LinComb O (K := Fin 3) ![𝟙 X, σ, z] ![1, 1, -2])) (ht : t.IsGen) (k : ℕ)
    (s : LB.Sec (LB.div (pw L k) O)) (hs : ∃ j, s.f j ≠ 0) :
    ∃ s : LB.Sec (pw L (2 * k : ℕ)), ∃ j, s.f j ≠ 0 := by
  let W : (L.ι × L.ι) × (O.ι × O.ι) → X.Opens := fun i =>
    (L.U i.1.1 ⊓ O.U i.2.1) ⊓ σ ⁻¹ᵁ (L.U i.1.2 ⊓ O.U i.2.2)
  have l₁ : ∀ i, W i ≤ LB.wchart L ![σ, 𝟙 X] ![i.1.2, i.1.1] := fun i x hx => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [hx.2.1, hx.1.1]
  have l₂ : ∀ i, W i ≤ LB.wchart O ![𝟙 X, σ, z] ![i.2.1, i.2.2, p₀] := fun i x hx => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [hx.1.2, hx.2.2, hz x]
  obtain ⟨a, ha⟩ : ∃ a : ∀ i, Γ(X, W i), ∀ i x, x ∈ W i → gs (𝟙 X) x (W i) (a i) =
      gs (𝟙 X) x (L.U i.1.1 ⊓ O.U i.2.1) (s.f (i.1.1, i.2.1)) * gs σ x (L.U i.1.2 ⊓ O.U i.2.2) (s.f (i.1.2, i.2.2)) *
        (gm (𝟙 X) x (LB.wchart O ![𝟙 X, σ, z] ![i.2.1, i.2.2, p₀]) (t.s ![i.2.1, i.2.2, p₀]) *
          ((gm (𝟙 X) x (LB.wchart L ![σ, 𝟙 X] ![i.1.2, i.1.1]) (sy.s ![i.1.2, i.1.1])) ^ k)⁻¹).val := by
    refine ⟨fun i => rs X (inf_le_left : W i ≤ L.U i.1.1 ⊓ O.U i.2.1) (s.f (i.1.1, i.2.1)) *
      rs X (inf_le_right : W i ≤ σ ⁻¹ᵁ (L.U i.1.2 ⊓ O.U i.2.2)) ((σ.app (L.U i.1.2 ⊓ O.U i.2.2)).hom (s.f (i.1.2, i.2.2))) *
      (res (l₂ i) (t.s ![i.2.1, i.2.2, p₀]) * ((res (l₁ i) (sy.s ![i.1.2, i.1.1])) ^ k)⁻¹).val, fun i x hx => ?_⟩
    refine (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·)
      (gs_res _ x _ hx _) ((gs_res _ x _ hx _).trans ((gs_pull (𝟙 X) σ x _ hx.2 _).trans (by rw [Category.id_comp])))))
      ((gs_unit _ x _ hx _).trans (congrArg Units.val ?_)))
    rw [map_mul, map_inv, map_pow]
    exact congrArg₂ (· * ·) (gm_res _ x _ hx _) (congrArg (fun q => (q ^ k)⁻¹) (gm_res _ x _ hx _))
  have cov : ∀ x : X, ∃ i, x ∈ W i := fun x => by
    obtain ⟨j, hj⟩ := exists_chart hL x
    obtain ⟨j', hj'⟩ := exists_chart hL (σ x)
    obtain ⟨p, hp⟩ := exists_chart hO x
    obtain ⟨q, hq⟩ := exists_chart hO (σ x)
    exact ⟨((j, j'), (p, q)), ⟨hj, hp⟩, ⟨hj', hq⟩⟩
  obtain ⟨s', hs'⟩ := glue (N := pw L (2 * k : ℕ)) (isLB_pw hL (2 * k : ℕ)) W (fun i => i.1.1) (fun i x hx => hx.1.1) cov a (by
    intro i i' x hx hx'
    have tr : ∀ (r : X ⟶ X) (p q : L.ι × O.ι), r x ∈ L.U p.1 ⊓ O.U p.2 → r x ∈ L.U q.1 ⊓ O.U q.2 →
        gs r x (L.U p.1 ⊓ O.U p.2) (s.f p) = (gm r x (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) ^ k *
          (gm r x (O.U p.2 ⊓ O.U q.2) (O.g p.2 q.2))⁻¹).val * gs r x (L.U q.1 ⊓ O.U q.2) (s.f q) := by
      intro r p q hp hq
      refine (sec_gs s r x (i := p) (j := q) hp hq).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
      refine (gm_div O (pw L k) r x p q ⟨hp, hq⟩).trans (congrArg₂ (· * ·) ?_ rfl)
      exact (map_zpow _ _ _).trans (zpow_natCast _ _)
    have e₁ := tr (𝟙 X) (i.1.1, i.2.1) (i'.1.1, i'.2.1) hx.1 hx'.1
    have e₂ := tr σ (i.1.2, i.2.2) (i'.1.2, i'.2.2) hx.2 hx'.2
    have e₃ := gen_trans ht (𝟙 X) x (l₂ i hx) (l₂ i' hx')
    have e₄ := gen_trans hsy (𝟙 X) x (l₁ i hx) (l₁ i' hx')
    have f₃ : trF (L := O) ![𝟙 X, σ, z] ![1, 1, -2] (𝟙 X) x ![i.2.1, i.2.2, p₀] ![i'.2.1, i'.2.2, p₀] =
        gm (𝟙 X) x (O.U i.2.1 ⊓ O.U i'.2.1) (O.g _ _) * gm σ x (O.U i.2.2 ⊓ O.U i'.2.2) (O.g _ _) := by
      rw [trF, Fin.prod_univ_three]
      show gm (𝟙 X ≫ 𝟙 X) x (O.U i.2.1 ⊓ O.U i'.2.1) (O.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ σ) x (O.U i.2.2 ⊓ O.U i'.2.2) (O.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ z) x (O.U p₀ ⊓ O.U p₀) (O.g _ _) ^ (-2 : ℤ) = _
      rw [gm_self hO (𝟙 X ≫ z) x (hz x), one_zpow, _root_.mul_one, zpow_one, zpow_one, Category.id_comp,
        Category.id_comp]
    have f₄ : trF (L := L) ![σ, 𝟙 X] ![1, -1] (𝟙 X) x ![i.1.2, i.1.1] ![i'.1.2, i'.1.1] =
        gm σ x (L.U i.1.2 ⊓ L.U i'.1.2) (L.g _ _) * (gm (𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _))⁻¹ := by
      rw [trF, Fin.prod_univ_two]
      show gm (𝟙 X ≫ σ) x (L.U i.1.2 ⊓ L.U i'.1.2) (L.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ 𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _) ^ (-1 : ℤ) = _
      rw [zpow_one, zpow_neg_one, Category.id_comp, Category.id_comp]
    have f₅ : gm (𝟙 X) x ((pw L (2 * k : ℕ)).U i.1.1 ⊓ (pw L (2 * k : ℕ)).U i'.1.1) ((pw L (2 * k : ℕ)).g i.1.1 i'.1.1) =
        gm (𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _) ^ (2 * k) :=
      (map_zpow _ _ _).trans (zpow_natCast _ _)
    rw [ha i x hx, ha i' x hx', f₅]
    exact alg k e₁ e₂ (e₃.trans (congrArg₂ (· * ·) f₃ rfl)) (e₄.trans (congrArg₂ (· * ·) f₄ rfl)))
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨i, hi⟩ := cov x
  refine ⟨s', i.1.1, fun h0 => ?_⟩
  have e := (hs' i x hi).trans (ha i x hi)
  rw [h0, gs_eq (𝟙 X) x ((pw L (2 * k : ℕ)).U i.1.1) hi.1.1, map_zero, map_zero] at e
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (Units.ne_zero _) e.symm
  · exact gs_ne (𝟙 X) x hi.1 (sec_ne s hs (i := (i.1.1, i.2.1)) hi.1)
  · exact gs_ne σ x hi.2 (sec_ne s hs (i := (i.1.2, i.2.2)) hi.2)

theorem exists_sec_sq : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] (M : CP B) (k : ℕ) (O : LB B.left), O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → (∃ s : LB.Sec (LB.div (pw M.L.L k) O), (∃ j, s.f j ≠ 0)) → ∃ s : LB.Sec (pw M.L.L (2 * k : ℕ)), (∃ j, s.f j ≠ 0) := by
  intro A _ _ B _ _ _ M k O hO ⟨u, hu⟩ ⟨s, hs⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, ∀ y : Spec (CommRingCat.of A), eSec B y ∈ O.U p₀ := by
    obtain ⟨i, hi⟩ := exists_chart hO (eSec B (IsLocalRing.closedPoint A))
    exact ⟨i, fun y => ((IsLocalRing.specializes_closedPoint y).map (eSec B).continuous).mem_open (O.U i).isOpen hi⟩
  have hι : (𝟙 B : B ⟶ B)⁻¹ = ι[B] := by rw [Hom.inv_def, Category.id_comp]
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (𝟙 B) ι[B]).left ≫ (psum B (x2 B) I.down).left =
      (psum B ![𝟙 B, ι[B]] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift (𝟙 B) ι[B])) (x2 B) I.down).trans
      (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  obtain ⟨t, ht, -⟩ := exists_gen hO (φ' := ![𝟙 B.left, (ι[B]).left, (1 : B ⟶ B).left]) (ε' := ![1, 1, -2])
    (fun V _ h => by
      have p := GlobalTheory.JetSer.prod_lam (𝟙 B) ι[B] h
      rw [← hι, mul_inv_cancel, hι] at p
      simp only [e, zpow_neg, Finset.prod_inv_distrib, p, Fin.prod_univ_three]
      show _ = h (𝟙 B.left) ^ (1 : ℤ) * h (ι[B]).left ^ (1 : ℤ) * h (1 : B ⟶ B).left ^ (-2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.id_left]
      module)
    (LB.invGen O _ _ (LB.pullGen O (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) u (lift (𝟙 B) ι[B]).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  haveI : IsIso (ι[B]).left := inferInstanceAs (IsIso ((Over.forget _).map ι[B]))
  exact core M.L.isLB hO (ι[B]).left (1 : B ⟶ B).left p₀ (fun x => hp₀ (B.hom x))
    M.sym M.sym_gen t ht k s hs

end GlobalTheory.UU.SymSec
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem cubN_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) (x y : A') (k : ℕ) :
    cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k =
      W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y := by
  induction k with
  | zero => simp only [cubN, Finset.range_zero, Finset.prod_empty, pow_zero, _root_.one_mul, _root_.mul_one]; exact mul_comm _ _
  | succ k ih =>
    have e₁ : cubN θ (k + 1) 1 (β x) (β y) = cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow]
    have e₂ : cubN θ' (k + 1) 1 x y = cubN θ' k 1 x y * θ' (x ^ k) x y := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have H := hθ (x ^ k) x y
    rw [← pow_succ] at H
    rw [e₁, e₂]
    apply mul_right_cancel (b := W (x ^ k) * W (x ^ k * y))
    calc cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W y *
            (W (x * y) * W 1) ^ (k + 1) * (W (x ^ k) * W (x ^ k * y))
          = (cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k) *
            (θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W (x ^ k * y) * W (x * y) * W 1) := by
          rw [pow_succ (W (x * y) * W 1) k]; ac_rfl
      _ = (W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y) *
            (W (x ^ (k + 1) * y) * W (x ^ k) * W x * W y * θ' (x ^ k) x y) := by rw [ih, H]
      _ = W (x ^ (k + 1) * y) * W 1 * (W x * W y) ^ (k + 1) * (cubN θ' k 1 x y * θ' (x ^ k) x y) *
            (W (x ^ k) * W (x ^ k * y)) := by
          rw [pow_succ (W x * W y) k]; ac_rfl

theorem cubN_ratio_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) {x y : A'} {N : ℕ} (hx : x ^ N = 1) (hy : y ^ N = 1) {e : U}
    (h : e * cubN θ' N 1 x y = cubN θ' N 1 y x) :
    e * cubN θ N 1 (β x) (β y) = cubN θ N 1 (β y) (β x) := by
  have h₁ := cubN_twist β W hθ x y N
  have h₂ := cubN_twist β W hθ y x N
  simp only [hx, _root_.one_mul] at h₁
  simp only [hy, _root_.one_mul] at h₂
  rw [mul_comm y x, mul_comm (W y) (W x)] at h₂
  have k₁ : cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 x y := by
    apply mul_right_cancel (b := W 1 * W y)
    calc cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N * (W 1 * W y)
          = cubN θ N 1 (β x) (β y) * W 1 * W y * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W y * W 1 * (W x * W y) ^ N * cubN θ' N 1 x y := h₁
      _ = (W x * W y) ^ N * cubN θ' N 1 x y * (W 1 * W y) := by ac_rfl
  have k₂ : cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 y x := by
    apply mul_right_cancel (b := W 1 * W x)
    calc cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N * (W 1 * W x)
          = cubN θ N 1 (β y) (β x) * W 1 * W x * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W x * W 1 * (W x * W y) ^ N * cubN θ' N 1 y x := h₂
      _ = (W x * W y) ^ N * cubN θ' N 1 y x * (W 1 * W x) := by ac_rfl
  apply mul_right_cancel (b := (W (x * y) * W 1) ^ N)
  calc e * cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N
        = e * (cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N) := mul_assoc _ _ _
    _ = (W x * W y) ^ N * (e * cubN θ' N 1 x y) := by rw [k₁]; ac_rfl
    _ = cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N := by rw [h, k₂]

theorem cubWeil_map : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (P : CP G) (P' : CP G') (F : G'.left ⟶ G.left) (hw) (w), IsCPMap P' P f F hw w → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil P'.c N x y ζ → CubWeil P.c N (toBase hw x) (toBase hw y) ζ) := by
  intro S S' f G _ _ G' _ _ P P' F hw w hP N T x y ζ hζ
  obtain ⟨hx, hy, hr⟩ := hζ
  let β := toBaseHom (hw := hw) hP.mul T
  have hβ : ∀ a : T ⟶ G', β a = toBase hw a := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hβ, ← map_pow, hx, map_one]
  · rw [← hβ, ← map_pow, hy, map_one]
  · intro z J hJ
    obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
    have hv := (hP.vals T z J' J hJ' hJ (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (fun _ => rfl)).2.2
    exact cubN_ratio_twist β (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (θ := cubV P.c (T := Over.mk (T.hom ≫ f)) z J) (θ' := cubV P'.c z J') hv hx hy (hr z J' hJ')

end GlobalTheory.UU
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

private theorem isCub_mul_swap_middle {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (a b c d y : A) :
    θ a b y * θ (a * b) (c * d) y * θ c d y = θ (a * c) (b * d) y * θ a c y * θ b d y := by
  have e1 : θ a b y * θ (a * b) (c * d) y = θ a (b * (c * d)) y * θ b (c * d) y := by
    rw [_root_.mul_comm]; exact h.coc a b (c * d) y
  have e2 : θ b (c * d) y * θ c d y = θ (b * c) d y * θ b c y := (h.coc b c d y).symm
  have e3 : θ (a * c) (b * d) y * θ a c y = θ a (c * (b * d)) y * θ c (b * d) y := h.coc a c (b * d) y
  have e4 : θ c (b * d) y * θ b d y = θ (c * b) d y * θ c b y := (h.coc c b d y).symm
  rw [e1, _root_.mul_assoc, e2, e3, _root_.mul_assoc, e4, _root_.mul_comm c b, h.s01 c b, mul_left_comm c b d]

private theorem v_sub_one_add_le_v_pow_l_sub_one {U : Type} [CommGroup U] {P B C D Px Px' D' E F : U} {k : ℕ}
    (ih : P * C ^ k = D * Px * Px') (e : D * B * C = D' * E * F) :
    P * B * C ^ (k + 1) = D' * (Px * E) * (Px' * F) := by
  calc P * B * C ^ (k + 1) = (P * C ^ k) * (B * C) := by rw [pow_succ]; ac_rfl
    _ = Px * Px' * (D * B * C) := by rw [ih]; ac_rfl
    _ = D' * (Px * E) * (Px' * F) := by rw [e]; ac_rfl

theorem cubN_mul_left {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ)
    (x x' y : A) :
    cubN θ k 1 (x * x') y * θ x x' y ^ k = θ (x ^ k) (x' ^ k) y * cubN θ k 1 x y * cubN θ k 1 x' y := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ x, pow_succ x', mul_pow x x' k]
    exact v_sub_one_add_le_v_pow_l_sub_one ih (isCub_mul_swap_middle h (x ^ k) (x' ^ k) x x' y)

private theorem gm_id_global_mul {X : Scheme.{0}} (z : X) (a b : Γ(X, ⊤)ˣ) :
    gm (𝟙 X) z ⊤ (a * b) = gm (𝟙 X) z ⊤ a * gm (𝟙 X) z ⊤ b :=
  map_mul _ a b

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x x' y : T ⟶ G}

theorem CubWeil.mul_left {ζ ζ' : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : CubWeil c N x' y ζ') :
    CubWeil c N (x * x') y (ζ * ζ') := by
  obtain ⟨hx, hy, hv⟩ := h
  obtain ⟨hx', -, hv'⟩ := h'
  refine ⟨by rw [mul_pow, hx, hx', _root_.one_mul], hy, fun z J hJ => ?_⟩
  have hc := isCub_cubV c hJ
  have e1 := cubN_mul_left hc N x x' y
  rw [hx, hx', hc.face, _root_.one_mul, hc.s12 x x' y, hc.s01 x y x'] at e1
  have e2 := hc.N_add N 1 y x x'
  simp only [hc.face, _root_.one_mul, _root_.mul_one, hy] at e2
  apply mul_right_cancel (b := cubV c z J y x x' ^ N)
  rw [gm_id_global_mul, _root_.mul_assoc, e1, e2, ← hv z J hJ, ← hv' z J hJ]
  exact mul_mul_mul_comm _ _ _ _

theorem cubWeil_one_left (c : CubicalStr G L) (hy : y ^ N = 1) : CubWeil c N 1 y 1 := by
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil (x := (1 : T ⟶ G)) c (one_pow N) hy
  have h2 := hζ.mul_left hζ
  rw [_root_.one_mul] at h2
  have e : ζ * ζ = ζ * 1 := by rw [_root_.mul_one]; exact h2.unique hζ
  rw [mul_left_cancel e] at hζ
  exact hζ

theorem CubWeil.pow_left {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (n : ℕ) : CubWeil c N (x ^ n) y (ζ ^ n) := by
  induction n with
  | zero => simpa using cubWeil_one_left c h.2.1
  | succ n ih => simpa [pow_succ] using ih.mul_left h

theorem CubWeil.pow_eq_one {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) : ζ ^ N = 1 := by
  have hp := h.pow_left N
  rw [h.1] at hp
  exact hp.unique (cubWeil_one_left c h.2.1)

end

theorem cubWeil_basic : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (N : ℕ) (T : Over S), (∀ x y : T ⟶ G, x ^ N = 1 → y ^ N = 1 → ∃! ζ, CubWeil c N x y ζ) ∧ (∀ (x x' y : T ⟶ G) ζ ζ', CubWeil c N x y ζ → CubWeil c N x' y ζ' → CubWeil c N (x * x') y (ζ * ζ')) ∧ (∀ (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N y x ζ⁻¹ ∧ ζ ^ N = 1) ∧ (∀ (T' : Over S) (ρ : T' ⟶ T) (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N (ρ ≫ x) (ρ ≫ y) (Units.map ρ.left.appTop.hom.toMonoidHom ζ)) ∧ ∀ (H : Over S) [GrpObj H] (i : H ⟶ G), IsMonHom i → Nonempty (BiTriv c i) → ∀ (t : T ⟶ H) (y : T ⟶ G), t ^ N = 1 → y ^ N = 1 → CubWeil c N (t ≫ i) y 1) := by
  intro S G _ _ L c N T
  refine ⟨fun x y hx hy => existsUnique_cubWeil c hx hy, fun x x' y ζ ζ' h h' => h.mul_left h',
    fun x y ζ h => ⟨h.symm, h.pow_eq_one⟩, fun T' ρ x y ζ h => h.comp ρ, ?_⟩
  intro H _ i hi hne t y ht hy
  obtain ⟨σ⟩ := hne
  exact σ.cubWeil ht hy

end GlobalTheory.UU
end
end
