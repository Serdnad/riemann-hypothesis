module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.TrivTwist

variable {X Y : Scheme.{0}}

theorem gm_pull_g (A : LB X) (f : Y ⟶ X) (y : Y) (i j : A.ι) (hi : f y ∈ A.U i) (hj : f y ∈ A.U j) :
    gm (𝟙 Y) y ((A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j)) ((A.pull f).g (fun _ => i) (fun _ => j)) =
      gm f y (A.U i ⊓ A.U j) (A.g i j) := by
  have hp : (𝟙 Y : Y ⟶ Y) y ∈ (A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (A.g i j))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) f y (A.U i ⊓ A.U j) ⟨hi, hj⟩ _).trans (by rw [Category.id_comp]))

theorem isGen_pull_iff (A : LB X) (f : Y ⟶ X) (t : LB.Gen (A.pull f)) :
    t.IsGen ↔ ∀ (i j : A.ι) (y : Y), f y ∈ A.U i → f y ∈ A.U j →
      gm (𝟙 Y) y ((A.pull f).U (fun _ => i)) (t.s (fun _ => i)) =
        gm f y (A.U i ⊓ A.U j) (A.g i j) * gm (𝟙 Y) y ((A.pull f).U (fun _ => j)) (t.s (fun _ => j)) := by
  constructor
  · intro h i j y hi hj
    have hp : (𝟙 Y : Y ⟶ Y) y ∈ (A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j) :=
      ⟨mem_pull.2 hi, mem_pull.2 hj⟩
    have := congrArg (gm (𝟙 Y) y ((A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j))) (h (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ y _ hp, gm_res _ y _ hp, gm_pull_g A f y i j hi hj] at this
    exact this
  · intro h I J
    refine unit_ext fun y hy => ?_
    have hi := mem_pull.1 hy.1
    have hj := mem_pull.1 hy.2
    have := h (I PUnit.unit) (J PUnit.unit) y hi hj
    rw [← gm_pull_g A f y _ _ hi hj] at this
    exact (gm_res _ y _ hy _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ y _ hy _))).symm)

theorem gm_div_g_one (M N : LB X) (hN : ∀ i j, N.g i j = 1) (f : Y ⟶ X) (y : Y) (p q : M.ι × N.ι)
    (hp : f y ∈ (LB.div M N).U p) (hq : f y ∈ (LB.div M N).U q) :
    gm f y ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) = gm f y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) := by
  show gm f y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  have hm : f y ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res f y _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y _ hm _)))).trans ?_)
  rw [hN, map_one, inv_one, _root_.mul_one]

theorem triv_pull_div_iff (M N : LB X) (hc : ∀ x : X, ∃ k, x ∈ N.U k) (hN : ∀ i j, N.g i j = 1) (f : Y ⟶ X) :
    Triv (M.pull f) ↔ Triv ((LB.div M N).pull f) := by
  have hle : ∀ p : M.ι × N.ι, ((LB.div M N).pull f).U (fun _ => p) ≤ (M.pull f).U (fun _ => p.1) :=
    fun p y hy => mem_pull.2 (mem_pull.1 hy).1
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun P => res (hle (P PUnit.unit)) (t.s (fun _ => (P PUnit.unit).1))⟩, (isGen_pull_iff _ f _).2 ?_⟩
    intro p q y hp hq
    rw [gm_div_g_one M N hN f y p q hp hq]
    exact (gm_res (𝟙 Y) y (hle p) (mem_pull.2 hp) _).trans (((isGen_pull_iff M f t).1 ht p.1 q.1 y hp.1 hq.1).trans
      (congrArg _ (gm_res (𝟙 Y) y (hle q) (mem_pull.2 hq) _).symm))
  · rintro ⟨c, hc'⟩
    have H : ∀ (p q : M.ι × N.ι) (y : Y), f y ∈ (LB.div M N).U p → f y ∈ (LB.div M N).U q →
        gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => p)) (c.s (fun _ => p)) =
          gm f y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
            gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => q)) (c.s (fun _ => q)) := fun p q y hp hq => by
      rw [← gm_div_g_one M N hN f y p q hp hq]
      exact (isGen_pull_iff _ f c).1 hc' p q y hp hq
    have glue : ∀ i : M.ι, ∃ s : Γ(Y, (M.pull f).U (fun _ => i))ˣ, ∀ k : N.ι,
        res (hle (i, k)) s = c.s (fun _ => (i, k)) := fun i =>
      glue_unit _ (fun k => ((LB.div M N).pull f).U (fun _ => (i, k))) (fun k => hle (i, k))
        (fun y hy => by
          obtain ⟨k, hk⟩ := hc (f y)
          exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.2 ⟨mem_pull.1 hy, hk⟩⟩)
        (fun k => c.s (fun _ => (i, k))) (fun k k' y hy => by
          have h₁ := mem_pull.1 hy.1
          have h₂ := mem_pull.1 hy.2
          have e := mul_eq_right.1 (H (i, k) (i, k) y h₁ h₁).symm
          have e' := H (i, k) (i, k') y h₁ h₂
          exact e'.trans ((congrArg (· * _) e).trans (_root_.one_mul _)))
    choose s hs using glue
    refine ⟨⟨fun I => s (I PUnit.unit)⟩, (isGen_pull_iff M f _).2 fun i j y hi hj => ?_⟩
    obtain ⟨k, hk⟩ := hc (f y)
    have v : ∀ a, f y ∈ M.U a → gm (𝟙 Y) y ((M.pull f).U (fun _ => a)) (s a) =
        gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => (a, k))) (c.s (fun _ => (a, k))) := fun a ha =>
      (gm_res (𝟙 Y) y (hle (a, k)) (mem_pull.2 ⟨ha, hk⟩) _).symm.trans (congrArg _ (hs a k))
    exact (v i hi).trans ((H (i, k) (j, k) y ⟨hi, hk⟩ ⟨hj, hk⟩).trans (congrArg _ (v j hj).symm))

theorem linComb_pw_zero_g (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j : K → L.ι) :
    (LB.LinComb (pw L 0) φ ε).g i j = 1 := by
  refine Finset.prod_eq_one fun k _ => ?_
  have e : (pw L 0).g (i k) (j k) = 1 := zpow_zero _
  exact (congrArg (· ^ ε k) ((congrArg _ ((congrArg _ e).trans (map_one _))).trans (map_one _))).trans (one_zpow _)

theorem inK_iff_trivial_twist : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → (pw L 0).IsLB ∧ (∃ u : LB.Gen (abelian₂ B (pw L 0)), u.IsGen) ∧ ∀ (O : LB B.left), O = pw L 0 → ∀ (T : Over S) (x : T ⟶ B), InK B L x ↔ (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) := by
  intro S B _ L hL
  refine ⟨isLB_pw hL 0, ⟨⟨fun _ => 1⟩, fun i j => ?_⟩, ?_⟩
  · exact (map_one _).trans
      ((congrArg₂ (· * ·) (linComb_pw_zero_g L _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm
  · rintro O rfl T x
    refine forall_congr' fun p => exists_congr fun U => and_congr Iff.rfl ?_
    refine triv_pull_div_iff _ _ (fun y => ?_) (fun i j => linComb_pw_zero_g L _ _ i j) _
    obtain ⟨k, hk⟩ := exists_chart (isLB_pw hL 0) ((snd T B).left y)
    exact ⟨fun _ => k, mem_pull.2 hk⟩

end GlobalTheory.UU.TrivTwist
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistGen

open LBGerm TopologicalSpace

variable {X : Scheme.{0}} {M H : LB X}

theorem gm_tw_g (M H : LB X) (t : ℕ) (y : X) (p q : M.ι × H.ι) (hp : y ∈ M.U p.1 ⊓ H.U p.2)
    (hq : y ∈ M.U q.1 ⊓ H.U q.2) :
    (gm (𝟙 X) y ((tw M H t).U p ⊓ (tw M H t).U q) ((tw M H t).g p q)).val =
      (gm (𝟙 X) y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1)).val *
        (gm (𝟙 X) y (H.U p.2 ⊓ H.U q.2) (H.g p.2 q.2)).val ^ t := by
  have hy : (𝟙 X : X ⟶ X) y ∈ M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) := ⟨hp, hq⟩
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, tw_g]
  refine congrArg Units.val ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) y _ hy _) ?_))
  rw [zpow_natCast]
  exact (map_pow _ _ _).trans (congrArg (· ^ t) (gm_res (𝟙 X) y _ hy _))

theorem exists_mul_pow (a e : ℕ) (u : LB.Sec (tw M H a)) (s : LB.Sec H) :
    ∃ u' : LB.Sec (tw M H ((a + e : ℕ) : ℤ)), nonzeroLocus u ⊓ nonzeroLocus s ≤ nonzeroLocus u' := by
  let F : ∀ p : M.ι × H.ι, Γ(X, M.U p.1 ⊓ H.U p.2) := fun p =>
    (show Γ(X, M.U p.1 ⊓ H.U p.2) from u.f p) * resG X inf_le_right (s.f p.2) ^ e
  have hF : ∀ (y : X) (p : M.ι × H.ι), y ∈ M.U p.1 ⊓ H.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f p) * gs (𝟙 X) y _ (s.f p.2) ^ e := fun y p hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨secOfGerm (M := tw M H ((a + e : ℕ) : ℤ)) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · refine (hF y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) (gm_tw_g M H (a + e) y p q hp hq) (hF y q hq)).symm)
    rw [gs_compat u (𝟙 X) y (j := p) (j' := q) hp hq, gm_tw_g M H a y p q hp hq,
      gs_compat s (𝟙 X) y (j := p.2) (j' := q.2) hp.2 hq.2]
    ring
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
    refine (mem_nonzeroLocus_iff_isUnit (M := tw M H ((a + e : ℕ) : ℤ)) _ (k := p) hp).2 ?_
    refine (congrArg IsUnit (hF y p hp)).mpr ?_
    exact (((mem_nonzeroLocus_iff_isUnit u hp).1 hy.1).mul
      (((mem_nonzeroLocus_iff_isUnit s hp.2).1 hy.2).pow e))

theorem exists_sec_of_le_chart [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (n : ℕ)
    (σ : ∀ j, Γ(X, H.U j))
    (hσ : ∀ (y : X) j j', y ∈ H.U j → y ∈ H.U j' → gs (𝟙 X) y _ (σ j) =
      (gm (𝟙 X) y (H.U j ⊓ H.U j') (H.g j j')).val ^ n * gs (𝟙 X) y _ (σ j'))
    (V : X.Opens) (hV : ∀ (y : X) j, y ∈ H.U j → (y ∈ V ↔ IsUnit (gs (𝟙 X) y _ (σ j))))
    (k : M.ι) (hk : V ≤ M.U k) :
    ∃ (N : ℕ) (u : LB.Sec (tw M H ((n * N : ℕ) : ℤ))), V ≤ nonzeroLocus u := by
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → M.ι × H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (J a).1 ⊓ H.U (J a).2) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_tw hM hH 0)
  have hW₂ : ∀ a, W a ≤ H.U (J a).2 := fun a => (hW a).trans inf_le_right
  have hb : ∀ (U : X.Opens) (j : H.ι) (hU : U ≤ H.U j) (y : X),
      y ∈ X.basicOpen (resG X hU (σ j)) → y ∈ V := fun U j hU y hy => by
    have hy₁ : y ∈ U := X.basicOpen_le _ hy
    have hs := (isUnit_gs_iff (𝟙 X) y _ hy₁ _).2 hy
    rwa [gs_res _ y _ hy₁, ← hV y j (hU hy₁)] at hs
  have step₁ : ∀ a, ∃ (e : ℕ) (v : Γ(X, W a)), ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ v = gs (𝟙 X) y _ (σ (J a).2) ^ e *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val := fun a => by
    have le : X.basicOpen (resG X (hW₂ a) (σ (J a).2)) ≤ M.U (J a).1 ⊓ M.U k :=
      fun y hy => ⟨(hW a (X.basicOpen_le _ hy)).1, hk (hb _ _ _ y hy)⟩
    obtain ⟨e, v, hv⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (W a) (hWa a).isCompact
      (hWa a).isQuasiSeparated (resG X (hW₂ a) (σ (J a).2)) (resG X le (M.g (J a).1 k).val)
    have hv' : resG X (X.basicOpen_le _) v =
        resG X (X.basicOpen_le _) (resG X (hW₂ a) (σ (J a).2)) ^ e * resG X le (M.g (J a).1 k).val := hv
    refine ⟨e, v, fun y hy hs => ?_⟩
    have hy' : y ∈ X.basicOpen (resG X (hW₂ a) (σ (J a).2)) := (isUnit_gs_iff (𝟙 X) y _ hy _).1 (by
      rw [gs_res _ y _ hy]; exact (hV y _ (hW₂ a hy)).1 hs)
    have e₁ := congrArg (gs (𝟙 X) y _) hv'
    rwa [gs_res _ y _ hy', gs_mul _ y _ hy', gs_pow _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy,
      gs_res _ y _ hy', gs_unit (𝟙 X) y _ (le hy')] at e₁
  choose e v hv using step₁
  obtain ⟨N₁, v', hv'⟩ : ∃ (N₁ : ℕ) (v' : ∀ a, Γ(X, W a)), ∀ a, ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ (v' a) = gs (𝟙 X) y _ (σ (J a).2) ^ N₁ *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val :=
    ⟨Finset.univ.sup e, fun a => resG X (hW₂ a) (σ (J a).2) ^ (Finset.univ.sup e - e a) * v a, fun a y hy hs => by
      rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, hv a y hy hs, ← _root_.mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ a))]⟩
  have step₂ : ∀ p : α × α, ∃ d : ℕ, ∀ y ∈ W p.1 ⊓ W p.2, gs (𝟙 X) y _ (σ (J p.1).2) ^ d *
      (gs (𝟙 X) y _ (v' p.1) - (gm (𝟙 X) y (M.U (J p.1).1 ⊓ M.U (J p.2).1) (M.g (J p.1).1 (J p.2).1)).val *
        (gm (𝟙 X) y (H.U (J p.1).2 ⊓ H.U (J p.2).2)
        (H.g (J p.1).2 (J p.2).2)).val ^ (n * N₁) * gs (𝟙 X) y _ (v' p.2)) = 0 := by
    rintro ⟨a, b⟩
    have hcpt : IsCompact ((W a ⊓ W b : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hWa a).isCompact (W b).isOpen (hWa b).isCompact
    have le₁ : W a ⊓ W b ≤ M.U (J a).1 ⊓ M.U (J b).1 := fun y hy => ⟨(hW a hy.1).1, (hW b hy.2).1⟩
    have le : W a ⊓ W b ≤ H.U (J a).2 ⊓ H.U (J b).2 := fun y hy => ⟨(hW a hy.1).2, (hW b hy.2).2⟩
    have hx : ∀ y ∈ W a ⊓ W b, gs (𝟙 X) y (W a ⊓ W b) (resG X inf_le_left (v' a) -
        resG X le₁ (M.g (J a).1 (J b).1).val * resG X le (H.g (J a).2 (J b).2).val ^ (n * N₁) *
          resG X inf_le_right (v' b)) =
        gs (𝟙 X) y _ (v' a) - (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U (J b).1) (M.g (J a).1 (J b).1)).val *
          (gm (𝟙 X) y (H.U (J a).2 ⊓ H.U (J b).2) (H.g (J a).2 (J b).2)).val ^ (n * N₁) *
            gs (𝟙 X) y _ (v' b) := fun y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
        gs_res _ y _ hy, gs_res _ y _ hy, gs_unit (𝟙 X) y _ (le hy), gs_unit (𝟙 X) y _ (le₁ hy)]
    obtain ⟨d, hd⟩ := exists_pow_mul_gs_eq_zero hcpt (resG X (inf_le_left.trans (hW₂ a)) (σ (J a).2)) _
      fun y hy => by
        have hy₁ : y ∈ W a ⊓ W b := X.basicOpen_le _ hy
        have hs := hb _ _ _ y hy
        refine (hx y hy₁).trans ?_
        rw [hv' a y hy₁.1 hs, hv' b y hy₁.2 hs, hσ y (J a).2 (J b).2 (hW₂ a hy₁.1) (hW₂ b hy₁.2),
          ← gm_cocycle hM (𝟙 X) y (hW a hy₁.1).1 (hW b hy₁.2).1 (hk hs), Units.val_mul]
        ring
    refine ⟨d, fun y hy => ?_⟩
    have := hd y hy
    rwa [hx y hy, gs_res _ y _ hy] at this
  choose d hd using step₂
  obtain ⟨c, hc'⟩ : ∃ c, ∀ p, d p ≤ c := ⟨Finset.univ.sup d, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  have hz : ∀ a, ∀ y ∈ W a, gs (𝟙 X) y _ (resG X (hW₂ a) (σ (J a).2) ^ c * v' a) =
      gs (𝟙 X) y _ (σ (J a).2) ^ c * gs (𝟙 X) y _ (v' a) := fun a y hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
  obtain ⟨u, hu⟩ := exists_sec_of_refinement (isLB_tw hM hH ((n * (N₁ + c) : ℕ) : ℤ)) W J hW hc
    (fun a => resG X (hW₂ a) (σ (J a).2) ^ c * v' a) fun y a b ha hb => by
      obtain ⟨c', hc''⟩ := Nat.exists_eq_add_of_le (hc' (a, b))
      have e₁ := hd (a, b) y ⟨ha, hb⟩
      have e₂ := hσ y (J a).2 (J b).2 (hW₂ a ha) (hW₂ b hb)
      rw [hz a y ha, hz b y hb, gm_tw_g M H _ y (J a) (J b) (hW a ha) (hW b hb)]
      dsimp only at e₁
      rw [e₂] at e₁ ⊢
      rw [hc'']
      generalize gs (𝟙 X) y _ (σ (J b).2) = τ at e₁ ⊢
      generalize Units.val (gm (𝟙 X) y _ (H.g (J a).2 (J b).2)) = w at e₁ ⊢
      linear_combination (w ^ n * τ) ^ c' * e₁
  refine ⟨N₁ + c, u, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  have hs := (hV y _ (hW₂ a ha)).1 hy
  rw [mem_nonzeroLocus_iff_isUnit u (k := J a) (hW a ha), hu y (J a) a (hW a ha) ha, hz a y ha, hv' a y ha hy]
  exact (Units.isUnit _).mul ((hs.pow c).mul ((hs.pow N₁).mul (Units.isUnit _)))

theorem compact_quasiSeparated (hH : H.IsLB) {I : Type} [Finite I] (s : I → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  have mem : ∀ y : X, ∃ i, y ∈ nonzeroLocus (s i) := fun y =>
    Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hc]; trivial)
  refine ⟨⟨?_⟩, quasiSeparatedSpace_iff_forall_affineOpens.2 fun U V => ?_⟩
  · have : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) :=
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (mem y)).symm
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isCompact
  · have : (U.1 ∩ V.1 : Set X) = ⋃ i, ((nonzeroLocus (s i) ⊓ U.1 : X.Opens) : Set X) ∩
        ((nonzeroLocus (s i) ⊓ V.1 : X.Opens) : Set X) := by
      ext y
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨i, hi⟩ := mem y
        exact Set.mem_iUnion.2 ⟨i, ⟨hi, hy.1⟩, ⟨hi, hy.2⟩⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
        exact ⟨hi.1.2, hi.2.2⟩
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isQuasiSeparated _ _ Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) U.2).isCompact Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) V.2).isCompact

theorem exists_nhds [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (s : LB.Sec H)
    (ha : IsAffineOpen (nonzeroLocus s)) (y : X) (hy : y ∈ nonzeroLocus s) :
    ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧ ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := by
  obtain ⟨k, hk⟩ := exists_chart hM y
  have hl := nonzeroLocus_secToPow s (le_refl 1)
  rw [← hl] at ha hy
  obtain ⟨a, hle, hya⟩ := ha.exists_basicOpen_le (V := M.U k) ⟨y, hk⟩ hy
  obtain ⟨m, -, σ, hσ⟩ := exists_nonzeroLocus_eq_basicOpen hH (secToPow s 1) a
  obtain ⟨N, u, hu⟩ := exists_sec_of_le_chart hM hH (1 * m) (powSecFn σ) (fun z j j' hj hj' => by
      have hz : z ∈ H.U j ⊓ H.U j' := ⟨hj, hj'⟩
      have e := congrArg (gs (𝟙 X) z _) (powSecFn_compat σ j j')
      rwa [gs_res _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_pow _ z _ hz, gs_unit _ z _ hz] at e)
    (X.basicOpen a) (fun z j hj => by
      rw [isUnit_gs_iff (𝟙 X) z _ hj, ← nonzeroLocus_inf_powSecFn, hσ]
      exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩) k hle
  refine ⟨X.basicOpen a, 1 * m * N, hya, fun e => ?_⟩
  obtain ⟨u', hu'⟩ := exists_mul_pow _ e u s
  exact ⟨u', (le_inf hu ((X.basicOpen_le a).trans hl.le)).trans hu'⟩

theorem twist_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ M : LB X, M.IsLB → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (n' : ℕ) (u : Fin (n' + 1) → LB.Sec (tw M H t)), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro R _ X f H n s hH hs M hM
  obtain ⟨_, _⟩ := compact_quasiSeparated hH s hs.1 fun i => (hs.2 i).1
  have loc : ∀ y : X, ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧
      ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    exact exists_nhds hM hH (s i) (hs.2 i).1 y hi
  choose V N hy hV using loc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  refine ⟨(T.sup N : ℕ), fun t ht => ?_⟩
  have h : ∀ y : T, ∃ u : LB.Sec (tw M H t), V y ≤ nonzeroLocus u := fun y => by
    have h₁ : N y ≤ T.sup N := Finset.le_sup y.2
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, t = ((N y + e : ℕ) : ℤ) := ⟨(t - N y).toNat, by omega⟩
    exact hV y e
  choose u hu using h
  let c : Option T → LB.Sec (tw M H t) := fun o => o.elim DVR.SecOps.secZero u
  let e : Option T ≃ Fin (Fintype.card T + 1) := Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨_, fun i => c (e.symm i), top_unique fun x _ => ?_⟩
  obtain ⟨y, hyT, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  refine Opens.mem_iSup.2 ⟨e (some ⟨y, hyT⟩), ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hu ⟨y, hyT⟩ hx

end GlobalTheory.TwistGen
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V), IsAdicComplete (maximalIdeal V) V → Function.Injective φ → I.map φ ≤ maximalIdeal V → ∃ (D' : DegData V (maximalIdeal V)) (hD : IsPullDeg φ D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (U' : Unif (maximalIdeal V) D' A' ((Over.pullback (specOf φ)).obj G)), IsSemiAbelian ((Over.pullback (specOf φ)).obj G) ∧ IsPullUnif φ hD (Iso.refl _) U U' ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing V) F (algebraMap V _ (φ r))) → (∀ g, ∃! g', IsPullGtF φ hD F g g') ∧ (∀ g', ∃! g, IsPullGtF φ hD F g g') ∧ (∀ g g' y, IsPullGtF φ hD F g g' → (GtPtF.IsIota (hD.xe y) g ↔ GtPtF.IsIota y g')) ∧ ∀ k g g' h h', IsPullGtF φ hD F g g' → IsPullGtF φ hD F h h' → (GtPtF.IsNsmul k g h ↔ GtPtF.IsNsmul k g' h')) ∧ ∀ E : EndU U.toUnifPre, ∃ E' : EndU U'.toUnifPre, E'.aG = (Over.pullback (specOf φ)).map E.aG ∧ (∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing V) F (algebraMap V _ (φ r))) → ∀ g₁ g₂ g₁' g₂', IsPullGtF φ hD F g₁ g₁' → IsPullGtF φ hD F g₂ g₂' → (E.Act g₁ g₂ ↔ E'.Act g₁' g₂') := by
  first | exact @GlobalTheory.UT.EndBaseChange.main | exact GlobalTheory.UT.EndBaseChange.main | (intros; apply GlobalTheory.UT.EndBaseChange.main <;> assumption)
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor LBGerm

theorem mem_wchart_oneTerm {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (k : K) {j : K → L.ι} {x : X} :
    x ∈ LB.wchart L (fun _ : K => 𝟙 X) j ↔ x ∈ L.U (j k) :=
  ⟨fun h => Set.mem_iInter.1 h k, fun h => Set.mem_iInter.2 fun k' => by
    obtain rfl := Subsingleton.elim k k'; exact h⟩

theorem exists_sec_oneTerm {X : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Unique K] [Fintype K'] [Unique K']
    {e e' : ℤ} (he : e = e') (s : (LB.LinComb L (fun _ : K => 𝟙 X) (fun _ => e)).Sec) :
    ∃ s' : (LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e')).Sec, nonzeroLocus s' = nonzeroLocus s ∧
      ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (s'.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) := by
  subst he
  have le : ∀ j : K' → L.ι, LB.wchart L (fun _ : K' => 𝟙 X) j ≤
      LB.wchart L (fun _ : K => 𝟙 X) (fun _ => j default) := fun j x hx =>
    (mem_wchart_oneTerm default).2 ((mem_wchart_oneTerm (j := j) default).1 hx)
  let s' : (LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e)).Sec :=
    secOfGerm (M := LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e)) (fun j => resG X (le j) (s.f fun _ => j default))
      fun y j j' hj hj' => by
        refine (gs_res (𝟙 X) y (le j) hj _).trans ((sec_trans s (𝟙 X) y (le j hj) (le j' hj')).trans
          (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hj' _).symm))
        refine Eq.trans ?_ (gm_linComb L (fun _ : K' => 𝟙 X) (fun _ => e) (𝟙 X) y j j' hj hj').symm
        rw [trF, Fintype.prod_unique, Fintype.prod_unique]
  have hs : ∀ (x : X) (j : K' → L.ι), x ∈ LB.wchart L (fun _ : K' => 𝟙 X) j →
      gs (𝟙 X) x _ (s'.f j) = gs (𝟙 X) x _ (s.f fun _ => j default) := fun x j hx => gs_res (𝟙 X) x (le j) hx _
  refine ⟨s', nonzeroLocus_eq_of _ _ (fun y hy => ?_) fun y j hj => ?_,
    fun x i hx => hs x _ ((mem_wchart_oneTerm default).2 hx)⟩
  · obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j default, (mem_wchart_oneTerm default).2 ((mem_wchart_oneTerm (j := j) default).1 hj)⟩
  · rw [hs y j hj]
    exact (mem_nonzeroLocus_iff_isUnit s (le j hj)).symm

theorem sec_extend_of_nonzeroLocus : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (N : ℕ) (s : H0 L N), (∀ a : Γ(X, nonzeroLocus s), ∃ (m : ℕ) (t : H0 L (N * m)), ∀ (x : X) (j : Fin 1 → L.ι), x ∈ nonzeroLocus s → x ∈ L.U (j 0) → Geo.Tor.gs (𝟙 X) x _ (t.f j) = Geo.Tor.gs (𝟙 X) x _ (s.f j) ^ m * Geo.Tor.gs (𝟙 X) x _ a) ∧ ∀ (n : ℕ) (t : H0 L n), (∀ (x : X) (j : Fin 1 → L.ι), x ∈ nonzeroLocus s → x ∈ L.U (j 0) → Geo.Tor.gs (𝟙 X) x _ (t.f j) = 0) → ∃ m : ℕ, ∀ j : Fin 1 → L.ι, (show Γ(X, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) from s.f j) ^ m * (show Γ(X, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) from t.f j) = 0 := by
  intro X _ _ L hL N s
  have hj : ∀ j : Fin 1 → L.ι, ∃ i, j = fun _ => i := fun j =>
    ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
  have hJ : ∀ j : PUnit.{1} → L.ι, ∃ i, j = fun _ => i := fun j => ⟨j PUnit.unit, rfl⟩
  obtain ⟨s', hl, hs⟩ : ∃ s' : (lbPow L N).Sec, nonzeroLocus s' = nonzeroLocus s ∧
      ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (powFn s' fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) :=
    exists_sec_oneTerm L (K' := PUnit) rfl s
  refine ⟨fun a => ?_, fun n t ht => ?_⟩
  · obtain ⟨m, hm⟩ := exists_sec_eq_pow_mul (m := 0) hL s' (fun J => resG X (inf_le_left.trans hl.le) a)
      (mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' h hJ hJ' => by
        rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
        exact (gs_res (𝟙 X) y (inf_le_left.trans hl.le) ⟨h, hJ⟩ a).trans
          (gs_res (𝟙 X) y (inf_le_left.trans hl.le) ⟨h, hJ'⟩ a).symm)
    obtain ⟨u, hu⟩ := hm m le_rfl
    obtain ⟨t, -, ht⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((N * m : ℕ) : ℤ)) (by rw [zero_add]) u
    refine ⟨m, t, fun x j hx hxj => ?_⟩
    obtain ⟨i, rfl⟩ := hj j
    have hy : x ∈ nonzeroLocus s' ⊓ powChart L (fun _ => i) := ⟨hl.ge hx, mem_powChart.2 hxj⟩
    have e := congrArg (gs (𝟙 X) x _) (hu fun _ => i)
    rw [gs_res _ x _ hy, gs_mul _ x _ hy, gs_pow _ x _ hy, gs_res _ x _ hy, gs_res _ x _ hy, hs x i hxj] at e
    exact (ht x i hxj).trans e
  · obtain ⟨t', -, ht'⟩ : ∃ t' : (lbPow L n).Sec, nonzeroLocus t' = nonzeroLocus t ∧
        ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (powFn t' fun _ => i) = gs (𝟙 X) x _ (t.f fun _ => i) :=
      exists_sec_oneTerm L (K' := PUnit) rfl t
    obtain ⟨m, hm⟩ := exists_pow_mul_powFn_eq_zero hL s' t' fun J => fn_ext fun y hy => by
      obtain ⟨i, rfl⟩ := hJ J
      rw [gs_res _ y _ hy, gs_zero _ y _ hy, ht' y i (mem_powChart.1 hy.2)]
      exact ht y _ (hl.le hy.1) (mem_powChart.1 hy.2)
    refine ⟨m, fun j => fn_ext fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := hj j
    have hi : y ∈ L.U i := (mem_wchart_oneTerm (j := fun _ : Fin 1 => i) 0).1 hy
    have hp : y ∈ powChart L (fun _ => i) := mem_powChart.2 hi
    have e := congrArg (gs (𝟙 X) y _) (hm fun _ => i)
    rw [gs_mul _ y _ hp, gs_pow _ y _ hp, gs_zero _ y _ hp, hs y i hi, ht' y i hi] at e
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_zero _ y _ hy]
    exact e

end GlobalTheory
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_expandsAt_of_integral_family : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom], (∀ F : Fam D.toPre (FractionRing R) k, ∃ s : U.SecK k, U.Expands k s F) → ∀ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ I hR D A G _ _ _ U k _ hall F f hf
  obtain ⟨s, r, hr, σ₀, f₀, -, hf₀, hE⟩ := hall F
  have hw : (D.toPre.prB (FractionRing R)).left ≫ D.toPre.P.A.hom = (D.toPre.BF (FractionRing R)).hom := Over.w _
  have hm : ∀ α, DVR.SecIsMul D.toPre.P.A.hom r (f₀ α) (f α) := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom
      (fun W => GlobalTheory.IntegralExpansion.prB_app_injective D.toPre W) (hf α) (by rw [hw]; exact hf₀ α)
  have hm' : ∀ α, ∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α j => hm α j
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R I hR D A G U k r hr σ₀ f₀ f hm' hE
  exact ⟨σ, GlobalTheory.T.expandsAt_cancel_nonzero_scalar R I hR D A G U k r hr σ₀ σ f₀ f hm' hσ hE⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.qkToAk_descends_along_baseChange : GlobalFnsSt → SecBaseChangeSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A) (p' : QkPt D'.toPre F k) (x' : TFK (R := R') F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF φ hD F p.g p'.g → x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) → QkToAkU U'.toUnifPre F k p' x' → QkToAkU U.toUnifPre F k p x := by
  first | exact @GlobalTheory.qkToAk_of_baseChange | exact GlobalTheory.qkToAk_of_baseChange | (intros; apply GlobalTheory.qkToAk_of_baseChange <;> assumption)
end
