module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem bijective_appLE_of_le_opensRange {Y Y' : Scheme.{0}} (e : Y' ⟶ Y) [IsOpenImmersion e]
    {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens} (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (e.appLE V V' h).hom := by
  obtain rfl : V' = e ⁻¹ᵁ V := le_antisymm h h'
  have := e.isIso_app V hV
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (e.app V)

theorem SecOn.pullLE_bijective_of_le_opensRange {Y Y' : Scheme.{0}} (M : LB Y) (e : Y' ⟶ Y)
    [IsOpenImmersion e] {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens}
    (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (SecOn.pullLE M e V V' h) := by
  have hb (i : M.ι) : Function.Bijective (e.appLE (V ⊓ M.U i) (V' ⊓ (M.pull e).U fun _ => i)
      ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))).hom :=
    bijective_appLE_of_le_opensRange e (inf_le_left.trans hV) _
      (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
  refine ⟨fun s t hst => GlobalTheory.LB.sec_ext fun i => (hb i).1 ?_, fun t => ?_⟩
  · exact (SecOn.coord_pullLE e h s fun _ => i).symm.trans
      ((congrArg (GlobalTheory.LB.coord · fun _ => i) hst).trans (SecOn.coord_pullLE e h t fun _ => i))
  · choose a ha using fun i => (hb i).2 (GlobalTheory.LB.coord t fun _ => i)
    refine ⟨GlobalTheory.LB.mkSec a fun i j => ?_, GlobalTheory.LB.sec_ext fun j =>
      (SecOn.coord_pullLE e h _ j).trans (ha (j PUnit.unit))⟩
    have e₁ : V' ⊓ (M.pull e).U (fun _ => i) ⊓ (M.pull e).U (fun _ => j) ≤
        e ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
      inf_le_inf ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))
        (GlobalTheory.LB.pull_U_le (L := M) e fun _ => j)
    refine (bijective_appLE_of_le_opensRange e (inf_le_left.trans (inf_le_left.trans hV)) e₁
      (inf_le_inf (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
        (GlobalTheory.LB.pull_U (L := M) e fun _ => j).ge)).1 ?_
    have := GlobalTheory.LB.coord_mem t (fun _ => i) (fun _ => j)
    rw [← ha i, ← ha j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    exact this.trans (congrArg (· * _) (GlobalTheory.LB.resG_pull_g (L := M) e (fun _ => i) (fun _ => j) _))

theorem cechLB_pull_iso_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (Y' : Scheme.{0}) (e : Y' ⟶ Y) [IsOpenImmersion e] (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → (∀ i, D i ≤ e.opensRange) → Nonempty (cechLB (e ≫ f) (M.pull e) (fun i => e ⁻¹ᵁ D i) ≅ cechLB f M D) := by
  intro R _ Y f M Y' e _ κ _ _ D _ hD
  have w : e ≫ f = (e ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  let φ : secCube f M D ⟶ secCube (e ≫ f) (M.pull e) fun i => e ⁻¹ᵁ D i :=
    GlobalTheory.Cube.homMk κ R (fun s => secCubePull M D w s) fun h x => secCubePull_res D w h x
  have : IsIso (cechComplexMap φ) := isIso_cechComplexMap φ fun s ⟨i, hi⟩ =>
    SecOn.pullLE_bijective_of_le_opensRange M e ((biInf_le D hi).trans (hD i))
      (preimage_biInf D e s).ge (preimage_biInf D e s).le
  exact ⟨(asIso (cechComplexMap φ)).symm⟩

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_nhds_pow_mul_twCoord_eq_zero {Y : Scheme.{0}} {H M : LB Y} {d : ℤ}
    (σ : LB.Sec (pw H d)) {t : ℤ} (hH : H.IsLB) (hM : M.IsLB) (a : SecOn (tw M H t) ⊤)
    (ha : SecOn.restrict _ (le_top : nonzeroLocus σ ≤ ⊤) a = 0) (x : Y) :
    ∃ (W : Y.Opens) (n : ℕ), x ∈ W ∧ ∀ (p : M.ι) (l : H.ι) (O : Y.Opens) (_ : O ≤ W)
      (h : O ≤ ⊤ ⊓ (M.U p ⊓ H.U l)),
      rs Y (h.trans (inf_le_right.trans inf_le_right) : O ≤ H.U l) (σ.f l) ^ n *
        rs Y h (SecOn.twCoord a p l) = 0 := by
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))
  have hx : x ∈ (⊤ ⊓ (M.U q ⊓ H.U k) : Y.Opens) := ⟨trivial, hq, hk⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (⊤ ⊓ (M.U q ⊓ H.U k) : Y.Opens).2
  have hWU' : W ≤ ⊤ ⊓ (M.U q ⊓ H.U k) := hWU
  have hWk : W ≤ H.U k := hWU'.trans (inf_le_right.trans inf_le_right)
  have hb : Y.basicOpen (rs Y hWk (σ.f k)) ≤ nonzeroLocus σ ⊓ (M.U q ⊓ H.U k) := by
    refine le_inf ?_ ((Y.basicOpen_le _).trans (hWU'.trans inf_le_right))
    refine le_trans ?_ (le_iSup (fun j => Y.basicOpen (σ.f j)) k)
    exact (Scheme.basicOpen_res Y (σ.f k) (homOfLE hWk).op).le.trans inf_le_right
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hW
    (rs Y hWU' (SecOn.twCoord a q k)) (rs Y hWk (σ.f k)) (by
      have e := congrArg (fun y => rs Y hb (SecOn.twCoord y q k)) ha
      simp only [SecOn.twCoord_restrict, rs_rs] at e
      exact (rs_rs _ (Y.basicOpen_le _) _).trans (e.trans (map_zero _)))
  refine ⟨W, n, hxW, fun p l O hO h => ?_⟩
  have e := congrArg (rs Y hO) hn
  rw [map_mul, map_pow, rs_rs, rs_rs (U := H.U k) hWk hO (σ.f k), map_zero] at e
  have hl : O ≤ H.U l := h.trans (inf_le_right.trans inf_le_right)
  have hp : O ≤ M.U p := h.trans (inf_le_right.trans inf_le_left)
  have hq' : O ≤ M.U q := hO.trans (hWU'.trans (inf_le_right.trans inf_le_left))
  have e₁ : rs Y hl (σ.f l) = rs Y (le_inf hl (hO.trans hWk)) ((pw H d).g l k).val *
      rs Y (hO.trans hWk) (σ.f k) :=
    GlobalTheory.LB.sec_rel σ l k hl (hO.trans hWk) (le_inf hl (hO.trans hWk))
  rw [SecOn.twCoord_compat a p q l k h (hO.trans hWU') (le_inf hp hq') (le_inf hl (hO.trans hWk)),
    e₁, mul_pow, mul_mul_mul_comm, e, mul_zero]

theorem exists_pow_mul_twCoord_eq_zero : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → ∀ a : SecOn (tw M H t) ⊤, SecOn.restrict _ (le_top : V ≤ ⊤) a = 0 → ∃ k : ℕ, ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_right.trans inf_le_right : ⊤ ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord a p l = 0 := by
  rintro Y H M d σ V t hH hM rfl hY a ha
  choose W n hxW hn using exists_nhds_pow_mul_twCoord_eq_zero σ hH hM a ha
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : Y => (W x : Set Y))
    (fun x => (W x).2) fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  refine ⟨s.sup n, fun p l => ?_⟩
  refine GlobalTheory.LB.fun_ext_of_cover (fun x : s => W x ⊓ (⊤ ⊓ (M.U p ⊓ H.U l)))
    (fun _ => inf_le_right) (fun y hy => ?_) fun x => ?_
  · obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy', hy⟩
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) x.2)
    have e := hn x p l _ inf_le_left inf_le_right
    change rs Y _ _ = rs Y _ _
    rw [map_mul, map_pow, rs_rs (U := H.U l) _ _ (σ.f l), map_zero, hm,
      pow_add, _root_.mul_assoc, e, mul_zero]

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw.TwExtend

variable {Y : Scheme.{0}}

theorem basicOpen_rs_eq {L : LB Y} (s : LB.Sec L) (k : L.ι) {W : Y.Opens} (h : W ≤ L.U k) :
    Y.basicOpen (rs Y h (s.f k)) = nonzeroLocus s ⊓ W := by
  apply le_antisymm
  · have hb : Y.basicOpen (rs Y h (s.f k)) = W ⊓ Y.basicOpen (s.f k) := Y.basicOpen_res _ _
    rw [hb]
    exact le_inf (inf_le_right.trans (le_iSup (fun k => Y.basicOpen (s.f k)) k)) inf_le_left
  · have hu := SecOn.isUnit_rs_of_le_nonzeroLocus s k
      (inf_le_right.trans h : nonzeroLocus s ⊓ W ≤ L.U k) inf_le_left
    rw [← rs_rs h inf_le_right] at hu
    have hb : Y.basicOpen (rs Y (inf_le_right : nonzeroLocus s ⊓ W ≤ W) (rs Y h (s.f k))) =
      (nonzeroLocus s ⊓ W) ⊓ Y.basicOpen (rs Y h (s.f k)) := Y.basicOpen_res _ _
    rw [Y.basicOpen_of_isUnit hu] at hb
    exact hb.le.trans inf_le_right

theorem fun_extend {W O : Y.Opens} (hW : IsAffineOpen W) (f : Γ(Y, W)) (hO : Y.basicOpen f = O)
    (h : O ≤ W) (z : Γ(Y, O)) : ∃ (n : ℕ) (x : Γ(Y, W)), rs Y h x = rs Y h f ^ n * z := by
  subst hO
  exact exists_eq_pow_mul_of_isAffineOpen Y W hW f z

theorem fun_kill {W O : Y.Opens} (hW : IsCompact (W : Set Y)) (f x : Γ(Y, W))
    (hO : Y.basicOpen f = O) (h : O ≤ W) (hx : rs Y h x = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  subst hO
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Y hW x f hx

theorem exists_fin_cover [CompactSpace Y] {M H : LB Y} (hM : M.IsLB) (hH : H.IsLB) :
    ∃ (κ : Type) (_ : Fintype κ) (W : κ → Y.Opens) (p : κ → M.ι) (l : κ → H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (p a) ⊓ H.U (l a)) ∧ ⊤ ≤ ⨆ a, W a := by
  have h : ∀ x : Y, ∃ (W : Y.Opens) (p : M.ι) (l : H.ι),
      IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U p ⊓ H.U l := by
    intro x
    obtain ⟨p, hp⟩ := LB.mem_of_cover hM x
    obtain ⟨l, hl⟩ := LB.mem_of_cover hH x
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ M.U p ⊓ H.U l from ⟨hp, hl⟩)
        (M.U p ⊓ H.U l).isOpen
    exact ⟨W, p, l, hW, hx, hle⟩
  choose W p l hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set Y))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => p a, fun a => l a, fun a => hW a,
    fun a => hle a, ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem unit_shift {R : Type} [CommRing R] (A B : Rˣ) (t d : ℤ) (k : ℕ) {u v : R}
    (h : u = (B ^ d).val * v) :
    (A * B ^ (t + k * d)).val * v ^ k = u ^ k * (A * B ^ t).val := by
  rw [h, zpow_add, mul_comm (k : ℤ) d, zpow_mul, zpow_natCast]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
  ring

theorem pw_rel {H : LB Y} {d : ℤ} (σ : LB.Sec (pw H d)) (u : ∀ l, Γ(Y, H.U l))
    (hu : ∀ l, u l = σ.f l) (l m : H.ι) {O : Y.Opens}
    (hl : O ≤ H.U l) (hm : O ≤ H.U m) (h : O ≤ H.U l ⊓ H.U m) :
    rs Y hl (u l) = (res h (H.g l m) ^ d).val * rs Y hm (u m) := by
  rw [← map_zpow, hu, hu]
  exact GlobalTheory.LB.sec_rel σ l m hl hm h

end GlobalTheory.AbLaw.TwExtend

namespace GlobalTheory.AbLaw

open TwExtend

theorem exists_tw_extend_pow_mul : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → QuasiSeparatedSpace Y → ∀ y : SecOn (tw M H t) V, ∃ (k : ℕ) (a : SecOn (tw M H (t + k * d)) ⊤), ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_inf_right _ le_top : V ⊓ (M.U p ⊓ H.U l) ≤ ⊤ ⊓ (M.U p ⊓ H.U l)) (SecOn.twCoord a p l) = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord y p l := by
  intro Y H M d σ V t hH hM hV _ _ y
  obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, H.U l), ∀ l, u l = σ.f l := ⟨σ.f, fun _ => rfl⟩
  have hb : ∀ l {W : Y.Opens} (h : W ≤ H.U l), Y.basicOpen (rs Y h (u l)) = V ⊓ W := by
    intro l W h
    rw [hu, hV]
    exact basicOpen_rs_eq σ l h
  have hrel := pw_rel σ u hu
  suffices key : ∃ (k : ℕ) (a : SecOn (tw M H (t + k * d)) ⊤), ∀ (p : M.ι) (l : H.ι),
      rs Y (inf_le_inf_right _ le_top : V ⊓ (M.U p ⊓ H.U l) ≤ ⊤ ⊓ (M.U p ⊓ H.U l))
        (SecOn.twCoord a p l) =
      rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (u l) ^ k *
        SecOn.twCoord y p l by
    simp only [hu] at key
    exact key
  clear hu hV σ
  obtain ⟨κ, _, W, p, l, hW, hWc, hc⟩ := exists_fin_cover hM hH
  have hWl : ∀ a, W a ≤ H.U (l a) := fun a => (hWc a).trans inf_le_right
  have hWp : ∀ a, W a ≤ M.U (p a) := fun a => (hWc a).trans inf_le_left
  choose n x hx using fun a => fun_extend (hW a) (rs Y (hWl a) (u (l a))) (hb _ _) inf_le_right
    (rs Y (inf_le_inf_left V (hWc a)) (SecOn.twCoord y (p a) (l a)))
  obtain ⟨N, hN⟩ : ∃ N, ∀ a, n a ≤ N :=
    ⟨Finset.univ.sup n, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ∀ a, Γ(Y, W a), ∀ a {O : Y.Opens} (hO : O ≤ W a) (hO' : O ≤ V),
      rs Y hO (x' a) = rs Y (hO.trans (hWl a)) (u (l a)) ^ N *
        rs Y (le_inf hO' (hO.trans (hWc a))) (SecOn.twCoord y (p a) (l a)) := by
    refine ⟨fun a => rs Y (hWl a) (u (l a)) ^ (N - n a) * x a, fun a O hO hO' => ?_⟩
    have := congrArg (rs Y (le_inf hO' hO)) (hx a)
    simp only [map_mul, map_pow, rs_rs] at this ⊢
    rw [this, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (hN a)]
  have hk : ∀ q : κ × κ, ∃ K : ℕ, rs Y (inf_le_left.trans (hWl q.1)) (u (l q.1)) ^ K *
      (rs Y (inf_le_left : W q.1 ⊓ W q.2 ≤ _) (x' q.1) -
        (res (inf_le_inf (hWp q.1) (hWp q.2)) (M.g (p q.1) (p q.2)) *
          res (inf_le_inf (hWl q.1) (hWl q.2)) (H.g (l q.1) (l q.2)) ^ (t + N * d)).val *
        rs Y inf_le_right (x' q.2)) = 0 := by
    rintro ⟨a, b⟩
    refine fun_kill (QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hW a).isCompact
      (W b).isOpen (hW b).isCompact) _ _ (hb _ _) inf_le_right ?_
    have hM' : V ⊓ (W a ⊓ W b) ≤ M.U (p a) ⊓ M.U (p b) :=
      inf_le_right.trans (inf_le_inf (hWp a) (hWp b))
    have hH' : V ⊓ (W a ⊓ W b) ≤ H.U (l a) ⊓ H.U (l b) :=
      inf_le_right.trans (inf_le_inf (hWl a) (hWl b))
    have e : rs Y (inf_le_right : V ⊓ (W a ⊓ W b) ≤ W a ⊓ W b)
        (res (inf_le_inf (hWp a) (hWp b)) (M.g (p a) (p b)) *
          res (inf_le_inf (hWl a) (hWl b)) (H.g (l a) (l b)) ^ (t + N * d)).val =
        (res hM' (M.g (p a) (p b)) * res hH' (H.g (l a) (l b)) ^ (t + N * d)).val := by
      refine (GlobalTheory.LB.val_res _ _).symm.trans (congrArg Units.val ?_)
      rw [map_mul, map_zpow, LB.res_res, LB.res_res]
    rw [map_sub, map_mul, e, rs_rs, rs_rs, hx' a _ inf_le_left, hx' b _ inf_le_left,
      SecOn.twCoord_compat y (p a) (p b) (l a) (l b) _
        (inf_le_inf_left V (inf_le_right.trans (hWc b))) hM' hH', ← _root_.mul_assoc,
      ← _root_.mul_assoc, unit_shift _ _ t d N (hrel (l a) (l b) (hH'.trans inf_le_left) _ hH'),
      sub_self]
  choose k hk using hk
  obtain ⟨K, hK⟩ : ∃ K, ∀ q, k q ≤ K :=
    ⟨Finset.univ.sup k, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  have hNK : t + ((N + K : ℕ) : ℤ) * d = t + N * d + K * d := by push_cast; ring
  obtain ⟨s, hs, -⟩ := SecOn.existsUnique_of_local (isLB_tw hM hH (t + ((N + K : ℕ) : ℤ) * d))
    (V := ⊤) W (fun _ => le_top) hc (fun a => (p a, l a)) hWc
    (fun a => rs Y (hWl a) (u (l a)) ^ K * x' a) (fun a b => by
      have e := congrArg Units.val (SecOn.res_tw_g (M := M) (H := H)
        (t + ((N + K : ℕ) : ℤ) * d) (p a) (p b) (l a) (l b) (inf_le_inf (hWc a) (hWc b))
        (inf_le_inf (hWp a) (hWp b)) (inf_le_inf (hWl a) (hWl b)))
      refine Eq.trans ?_ (congrArg (· * rs Y (inf_le_right : W a ⊓ W b ≤ W b)
        (rs Y (hWl b) (u (l b)) ^ K * x' b)) e.symm)
      have h0 := hk (a, b)
      have h1 := unit_shift (res (inf_le_inf (hWp a) (hWp b)) (M.g (p a) (p b))) _ (t + N * d) d K
        (hrel (l a) (l b) (inf_le_left.trans (hWl a)) (inf_le_right.trans (hWl b))
          (inf_le_inf (hWl a) (hWl b)))
      simp only [map_mul, map_pow, rs_rs]
      rw [hNK, ← _root_.mul_assoc, h1, ← Nat.sub_add_cancel (hK (a, b)), pow_add]
      linear_combination
        rs Y (inf_le_left.trans (hWl a) : W a ⊓ W b ≤ _) (u (l a)) ^ (K - k (a, b)) * h0)
  refine ⟨N + K, s, fun q m => ?_⟩
  refine GlobalTheory.LB.fun_ext_of_cover (fun a => V ⊓ (M.U q ⊓ H.U m) ⊓ W a) (fun _ => inf_le_left)
    (GlobalTheory.LB.le_iSup_inf (top_unique hc) _) fun a => ?_
  change rs Y _ _ = rs Y _ _
  have hM' : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ M.U q ⊓ M.U (p a) :=
    inf_le_inf (inf_le_right.trans inf_le_left) (hWp a)
  have hH' : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ H.U m ⊓ H.U (l a) :=
    inf_le_inf (inf_le_right.trans inf_le_right) (hWl a)
  have hs' : rs Y (le_inf le_top (hWc a)) (SecOn.twCoord s (p a) (l a)) =
    rs Y (hWl a) (u (l a)) ^ K * x' a := hs a
  have e := congrArg (rs Y (inf_le_right : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ W a)) hs'
  rw [map_mul, map_pow, rs_rs, rs_rs, hx' a _ (inf_le_left.trans inf_le_left),
    ← _root_.mul_assoc, ← pow_add, add_comm K N] at e
  rw [map_mul, map_pow, rs_rs, rs_rs,
    SecOn.twCoord_compat s q (p a) m (l a) _ (le_inf le_top (inf_le_right.trans (hWc a))) hM' hH',
    SecOn.twCoord_compat y q (p a) m (l a) _
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans (hWc a))) hM' hH',
    e, ← _root_.mul_assoc, ← _root_.mul_assoc,
    unit_shift _ _ t d (N + K) (hrel m (l a) (hH'.trans inf_le_left) _ hH')]

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem secCube_exactAt_zero_and_one (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ]
    (D : κ → Y.Opens) (hD : ⨆ i, D i = ⊤) :
    (cubeComplex (secCube f M D)).ExactAt 0 ∧ (cubeComplex (secCube f M D)).ExactAt 1 := by
  let O : κ → Y.Opens := fun a => ⨅ i ∈ ({a} : Finset κ), D i
  have hOD (a : κ) : O a = D a := by simp [O]
  have hO (a : κ) : O a ≤ ⨅ i ∈ (∅ : Finset κ), D i :=
    iInf_le_iInf_of_subset D (Finset.empty_subset _)
  have hc : (⨅ i ∈ (∅ : Finset κ), D i) ≤ ⨆ a, O a := by
    simp only [hOD, hD, le_top]
  constructor
  · rw [cubeComplex_exactAt_zero_iff]
    intro s t h
    exact SecOnR.ext_of_cover f O hO hc fun a => congrFun h ⟨{a}, Finset.card_singleton a⟩
  · rw [cubeComplex_exactAt_one_iff]
    intro x
    constructor
    · intro hx
      have key (a b : κ) (hab : a < b) {W : Y.Opens} (ha : W ≤ O a) (hb : W ≤ O b) :
          SecOnR.restrict f M ha (x ⟨{a}, Finset.card_singleton a⟩) =
            SecOnR.restrict f M hb (x ⟨{b}, Finset.card_singleton b⟩) := by
        have e := Cube.d_one_apply_pair (secCube f M D) x hab
        rw [hx] at e
        have e' := (sub_eq_zero.1 e.symm).symm
        have hW : W ≤ ⨅ i ∈ ({a, b} : Finset κ), D i := by
          rw [hOD] at ha hb
          rw [Finset.iInf_insert, Finset.iInf_singleton]
          exact le_inf ha hb
        have e'' := congrArg (SecOnR.restrict f M hW) e'
        exact (SecOnR.restrict_restrict f _ _ _).symm.trans
          (e''.trans (SecOnR.restrict_restrict f _ _ _))
      obtain ⟨t, ht, -⟩ := SecOnR.existsUnique_glue f O hO hc
        (fun a => x ⟨{a}, Finset.card_singleton a⟩) fun a b => by
          rcases lt_trichotomy a b with h | rfl | h
          · exact key a b h _ _
          · rfl
          · exact (key b a h _ _).symm
      refine ⟨t, funext ?_⟩
      rintro ⟨s, hs⟩
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
      exact ht a
    · rintro ⟨t, rfl⟩
      have := Cube.d_zero_apply (secCube f M D) ((Cube.termZeroEquiv _).symm t)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact Cube.d_d _ 0 _

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem GrSum.apply_eq_eval₂Hom_mul {ι R B : Type*} [CommRing R] [CommRing B]
    {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) (c : R →+* B) (b : ι → B)
    (φ : ∀ n, A n → B) (hadd : ∀ n a a', φ n (a + a') = φ n a + φ n a')
    (hsmul : ∀ n (r : R) a, φ n (r • a) = c r * φ n a)
    (hop : ∀ i n a, φ (n + 1) (x i n a) = b i * φ n a)
    (F : MvPolynomial ι R) {t t' : ℤ} {a : A t} {a' : A t'}
    (h : F • GrSum.of hx t a = GrSum.of hx t' a') :
    φ t' a' = MvPolynomial.eval₂Hom c b F * φ t a := by
  letI : Algebra R B := c.toAlgebra
  letI : Algebra (MvPolynomial ι R) B := (MvPolynomial.eval₂Hom c b).toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) B :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C c b r).symm
  let ψ : ∀ n, A n →ₗ[R] B := fun n => ⟨⟨φ n, hadd n⟩, hsmul n⟩
  have hψ : ∀ i n a, ψ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R) • ψ n a :=
    fun i n a => (hop i n a).trans
      (congrArg (· * φ n a) (MvPolynomial.eval₂Hom_X' c b i).symm)
  have e := congrArg (GrSum.lift hx ψ hψ) h
  rw [map_smul, GrSum.lift_of, GrSum.lift_of] at e
  exact e.symm

theorem AbLaw.exists_smul_of_twCoord :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (V : Y.Opens) (F : MvPolynomial (Fin (m + 1)) R) (d t t' : ℤ) (y : SecOn (tw M H t) V), F ∈ polyGrading (Fin (m + 1)) R d → t' = t + d → ∃ y' : SecOn (tw M H t') V, F • GrSum.of (hx V) t (SecOnR.of f _ V y) = GrSum.of (hx V) t' (SecOnR.of f _ V y') ∧ ∀ (p : M.ι) (l : H.ι), SecOn.twCoord y' p l = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (MvPolynomial.eval₂Hom (cst f (H.U l)) (fun j => (s j).f l) F) * SecOn.twCoord y p l := by
  intro R _ Y f H m s M hx V F d t t' y hF ht
  subst ht
  obtain ⟨a, ha⟩ := (GrSum.mem_grading (hx V)).1
    (grSMul_mem (GrSum.grading (hx V)) hF (GrSum.of_mem_grading (hx V) t (SecOnR.of f _ V y)))
  refine ⟨(SecOnR.of f _ V).symm a, ha.symm, fun p l => ?_⟩
  have h₀ : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l := inf_le_right.trans inf_le_right
  have e := GrSum.apply_eq_eval₂Hom_mul (hx V) (cst f (V ⊓ (M.U p ⊓ H.U l)))
    (fun j => rs Y h₀ ((s j).f l))
    (fun n z => SecOn.twCoord ((SecOnR.of f _ V).symm z) p l) (fun _ _ _ => rfl)
    (fun n r z => SecOnR.coord_base_smul r z (p, l)) (fun _ _ _ => rfl) F ha.symm
  refine e.trans (congrArg (· * SecOn.twCoord y p l) ?_)
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  exact RingHom.ext fun r => (rs_cst f h₀ r).symm

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem secOn_basicOpen_localization :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V W : Y.Opens) (a : Γ(Y, V)) (h : W ≤ V), M.IsLB → IsCompact (V : Set Y) → IsQuasiSeparated (V : Set Y) → W = Y.basicOpen a → (∀ x : SecOn M V, SecOn.restrict M h x = 0 → ∃ k : ℕ, a ^ k • x = 0) ∧ ∀ y : SecOn M W, ∃ (k : ℕ) (x : SecOn M V), SecOn.restrict M h x = rs Y h a ^ k • y := by
  intro Y M V W a h hM hV hV' hW
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hM
  refine ⟨fun x hx => GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact (GlobalTheory.LB.toMod M) hV a h hW x hx,
    fun y => ?_⟩
  obtain ⟨k, x, e⟩ := GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod M) hV hV' a h hW y
  exact ⟨k, x, e.symm⟩

end GlobalTheory.AbLaw
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

theorem _root_.GlobalTheory.T.cubeComplex_gradedModule_exactAt_of_large_degree : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  first | exact @GlobalTheory.cubeComplex_grCube_exactAt_of_finite | exact GlobalTheory.cubeComplex_grCube_exactAt_of_finite | (intros; apply GlobalTheory.cubeComplex_grCube_exactAt_of_finite <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

theorem _root_.GlobalTheory.T.finite_homology_cubeComplex_gradedModule : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n p, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) := by
  first | exact @GlobalTheory.finite_cubeComplex_grCube_homology | exact GlobalTheory.finite_cubeComplex_grCube_homology | (intros; apply GlobalTheory.finite_cubeComplex_grCube_homology <;> assumption)
end
