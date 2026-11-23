module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem abs_lin_le (a a' u w M : ℤ) (hu : |u| ≤ M) (hw : |w| ≤ M) : |a * u - a' * w| ≤ M * (|a| + |a'|) := by
  calc |a * u - a' * w| ≤ |a * u| + |a' * w| := abs_sub _ _
    _ = |a| * |u| + |a'| * |w| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * M + |a'| * M := add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
    _ = M * (|a| + |a'|) := by ring

theorem abs_list_sum_le {α : Type*} (f : α → ℤ) (C : ℤ) :
    ∀ l : List α, (∀ b ∈ l, |f b| ≤ C) → |(l.map f).sum| ≤ l.length * C
  | [], _ => by simp
  | b :: l, h => by
    have h1 := h b (by simp)
    have h2 := abs_list_sum_le f C l fun x hx => h x (by simp [hx])
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add_one, add_mul, one_mul,
      add_comm ((l.length : ℤ) * C) C]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem abs_auxiliaryVectorUniformizerExponent_le (a a' : ℤ) {n : Type*} (c M : ℕ) (hc : c ≤ M) (y : n ⊕ Fin c) :
    |auxiliaryVectorUniformizerExponent a a' c y| ≤ (M : ℤ) * (|a| + |a'|) := by
  rcases y with x | p
  · simp only [auxiliaryVectorUniformizerExponent, abs_zero]; positivity
  · simp only [auxiliaryVectorUniformizerExponent]
    have hp := p.2
    apply abs_lin_le
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem abs_vtxExp_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (j x : ℕ) (hx : x < G.rank (G.m, j)) :
    |vtxExp a a' (G.m - 1 - j) (topRank G j) x| ≤ (G.m : ℤ) * (|a| + |a'|) := by
  have key := topRank_add hs j
  unfold vtxExp
  split_ifs with h
  · apply abs_lin_le
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  · simp only [abs_zero]; positivity

theorem abs_vtxDet_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) (X : ℕ × ℕ) (hX : X.2 ≤ G.m) :
    |vtxDet G a a' X| ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by
  unfold vtxDet
  split_ifs with h
  · calc |∑ x : Fin (G.rank (G.m, X.2)), vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x|
          ≤ ∑ x : Fin (G.rank (G.m, X.2)), |vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : Fin (G.rank (G.m, X.2)), (G.m : ℤ) * (|a| + |a'|) :=
            Finset.sum_le_sum fun x _ => abs_vtxExp_le G hs a a' X.2 x x.2
      _ = (G.rank (G.m, X.2) : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by simp
      _ ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hN _ _ le_rfl hX
  · simp only [abs_zero]; positivity

theorem mem_oppositePath_bound {m : ℕ} {b : Edge} (hb : b ∈ oppositePath m) :
    b.src.1 ≤ m ∧ b.src.2 ≤ m ∧ b.tgt.1 ≤ m ∧ b.tgt.2 ≤ m := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Edge.src, Edge.tgt]; omega
  · simp only [Edge.src, Edge.tgt]; omega

theorem length_oppositePath (m : ℕ) : (oppositePath m).length = 2 * m := by
  simp [oppositePath]; ring

theorem abs_pathSum_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) :
    |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
      ≤ ((2 * G.m : ℕ) : ℤ) * (2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))))) := by
  rw [← length_oppositePath]
  apply abs_list_sum_le
  intro b hb
  obtain ⟨h1, h2, h3, h4⟩ := mem_oppositePath_bound hb
  have e1 := abs_vtxDet_le G hs a a' N hN b.src h2
  have e2 := abs_vtxDet_le G hs a a' N hN b.tgt h4
  have r1 : ((G.rank b.tgt : ℕ) : ℤ) ≤ N := by exact_mod_cast hN _ _ h3 h4
  have r2 : ((G.rank b.src : ℕ) : ℤ) ≤ N := by exact_mod_cast hN _ _ h1 h2
  have hC : 0 ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by positivity
  calc |vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src|
        ≤ |vtxDet G a a' b.src * G.rank b.tgt| + |vtxDet G a a' b.tgt * G.rank b.src| := abs_sub _ _
    _ = |vtxDet G a a' b.src| * G.rank b.tgt + |vtxDet G a a' b.tgt| * G.rank b.src := by
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
    _ ≤ ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))) * N + ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))) * N :=
        add_le_add (mul_le_mul e1 r1 (by positivity) hC) (mul_le_mul e2 r2 (by positivity) hC)
    _ = 2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)))) := by ring

theorem abs_boxExp_le (G : Grid k) (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    |boxExp G a a' j v| ≤ (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by
  have hj := j.2
  have e1 := abs_auxiliaryVectorUniformizerExponent_le a a' (G.m - 2 - j + 1) G.m (by omega) v.1.2
  have e2 := abs_auxiliaryVectorUniformizerExponent_le a a' (G.m - 2 - j) G.m (by omega) v.1.1
  unfold boxExp
  have ha : |a| ≤ |a| + |a'| := le_add_of_nonneg_right (abs_nonneg _)
  calc |a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1|
        ≤ |a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1| := abs_add_le _ _
    _ ≤ |a| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1| := by
        gcongr; exact abs_sub _ _
    _ ≤ (|a| + |a'|) + (G.m : ℤ) * (|a| + |a'|) + (G.m : ℤ) * (|a| + |a'|) := by gcongr
    _ = (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by ring

open Classical in
theorem card_stepVar_le (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) (j : Fin (G.m - 1)) :
    Fintype.card (StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N * N := by
  have hj := j.2
  have k0 := topRank_add hs j
  have k1 := topRank_add hs ((j : ℕ) + 1)
  have n0 := hN G.m j le_rfl (by omega)
  have n1 := hN G.m (j + 1) le_rfl (by omega)
  refine (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans ?_
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  exact Nat.mul_le_mul (by omega) (by omega)

open Classical in
theorem abs_boxSum_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) :
    |∑ j, ∑ v, boxExp G a a' j v| ≤ ((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|))) := by
  have hC : 0 ≤ (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by positivity
  calc |∑ j, ∑ v, boxExp G a a' j v| ≤ ∑ j, |∑ v, boxExp G a a' j v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (G.m - 1), (N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc |∑ v, boxExp G a a' j v| ≤ ∑ v, |boxExp G a a' j v| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j)),
                (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := Finset.sum_le_sum fun v _ => abs_boxExp_le G a a' j v
          _ = (Fintype.card (StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ) *
                ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by simp
          _ ≤ (N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by
                apply mul_le_mul_of_nonneg_right _ hC
                exact_mod_cast card_stepVar_le G hs N hN j
    _ = ((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|))) := by simp

theorem abs_expo_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (G : Grid k), 1 ≤ G.s → ∀ (a a' : ℤ) (N : ℕ), (∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) →
      |expo G a a'| ≤ 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by
  intro k _ _ _ _ G hs a a' N hN
  classical
  have hP := abs_pathSum_le G hs a a' N hN
  have hB := abs_boxSum_le G hs a a' N hN
  have hpoly : 4 * (G.m : ℤ) ^ 2 + 2 * ((G.m - 1 : ℕ) : ℤ) * (2 * (G.m : ℤ) + 1) ≤ 8 * (G.m : ℤ) ^ 3 := by
    rcases Nat.eq_zero_or_pos G.m with h | h
    · simp [h]
    · have h1 : ((G.m - 1 : ℕ) : ℤ) = (G.m : ℤ) - 1 := by push_cast [Nat.cast_sub h]; ring
      have h2 : (1 : ℤ) ≤ G.m := by exact_mod_cast h
      rw [h1]; nlinarith
  have hT : 0 ≤ (N : ℤ) ^ 2 * (|a| + |a'|) := by positivity
  unfold expo
  calc _ ≤ |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
          + |2 * ∑ j, ∑ v, boxExp G a a' j v| := abs_sub _ _
    _ = |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
          + 2 * |∑ j, ∑ v, boxExp G a a' j v| := by rw [abs_mul]; norm_num
    _ ≤ ((2 * G.m : ℕ) : ℤ) * (2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))))) +
          2 * (((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)))) := by gcongr
    _ = (4 * (G.m : ℤ) ^ 2 + 2 * ((G.m - 1 : ℕ) : ℤ) * (2 * (G.m : ℤ) + 1)) * ((N : ℤ) ^ 2 * (|a| + |a'|)) := by
          push_cast; ring
    _ ≤ 8 * (G.m : ℤ) ^ 3 * ((N : ℤ) ^ 2 * (|a| + |a'|)) := mul_le_mul_of_nonneg_right hpoly hT
    _ = 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by ring

end GlobalTheory.OriginBox
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.PowIsoRe

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (e1 : W ≤ V) (e2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res e1 (res e2 x) = res (e1.trans e2) x := by
  ext1
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem preimage_comp_le {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) : h ⁻¹ᵁ V ≤ (h ≫ φ) ⁻¹ᵁ W := by
  intro x hx
  exact e hx

theorem pullU_res_pullU {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) (u : Γ(Z, W)ˣ) :
    pullU h V (res e (pullU φ W u)) = res (preimage_comp_le h φ e) (pullU (h ≫ φ) W u) := by
  have key : φ.app W ≫ Y.presheaf.map (homOfLE e).op ≫ h.app V =
      (h ≫ φ).app W ≫ X.presheaf.map (homOfLE (preimage_comp_le h φ e)).op := by
    rw [Scheme.Hom.naturality, Scheme.Hom.comp_app]
    rfl
  ext1
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem res_pull_comp {X Y Z : Scheme.{0}} (h : X ⟶ Y) (m : Y ⟶ Z) {W : Z.Opens} {V1 : Y.Opens}
    {V2 V3 T : X.Opens} (u : Γ(Z, W)ˣ) (e1 : V1 ≤ m ⁻¹ᵁ W) (e2 : V2 ≤ h ⁻¹ᵁ V1) (e3 : T ≤ V2)
    (e4 : V3 ≤ (h ≫ m) ⁻¹ᵁ W) (e5 : T ≤ V3) :
    res e3 (res e2 (pullU h V1 (res e1 (pullU m W u)))) = res e5 (res e4 (pullU (h ≫ m) W u)) := by
  rw [pullU_res_pullU, res_res, res_res, res_res]

theorem res_res' {X : Scheme.{0}} {U V V' W : X.Opens} (x : Γ(X, U)ˣ) (e1 : W ≤ V) (e2 : V ≤ U)
    (e3 : W ≤ V') (e4 : V' ≤ U) : res e1 (res e2 x) = res e3 (res e4 x) := by
  rw [res_res, res_res]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem wchart_le_M {X Y Z : Scheme.{0}} (M : LB Z) (h : X ⟶ Y) (m : Y ⟶ Z) (j : Fin 1 → M.ι) :
    LB.wchart M (fun _ : Fin 1 => h ≫ m) j ≤
      LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => j 0) := by
  intro x hx
  have hx0 := Set.mem_iInter.1 hx 0
  refine Set.mem_iInter.2 fun _ => ?_
  refine Set.mem_iInter.2 fun _ => ?_
  simpa using hx0

theorem wchart_le_L {X Z : Scheme.{0}} (L : LB Z) (f : X ⟶ Z) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f) j ≤ LB.wchart L (fun _ : PUnit => f) (fun _ => j 0) := by
  intro x hx
  exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0

theorem exists_powIso {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂)
    (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  dsimp only [LB.Gen.IsGen, LB.div, LB.LinComb, LB.pull, powPull] at w hw ⊢
  have hle : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      LB.wchart M (fun _ : Fin 1 => h ≫ m) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤
        LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => p.1 0) ⊓
          LB.wchart L (fun _ : PUnit => f) (fun _ => p.2 0) := fun p =>
    inf_le_inf (wchart_le_M M h m p.1) (wchart_le_L L f p.2)
  dsimp only [LB.pull, LB.LinComb] at hle
  refine ⟨⟨fun p => (res (hle p) (w.s (fun _ _ => p.1 0, fun _ => p.2 0))) ^ k⟩, ?_⟩
  dsimp only
  intro p p'
  have e := congrArg (fun x => (res (inf_le_inf (hle p) (hle p')) x) ^ k)
    (hw (fun _ _ => p.1 0, fun _ => p.2 0) (fun _ _ => p'.1 0, fun _ => p'.2 0))
  simp only [map_mul, map_inv, map_pow, map_zpow, map_prod, res_res, pullU_res_pullU,
    Fin.prod_univ_one, Fintype.prod_unique, Fin.default_eq_zero, zpow_one, zpow_natCast, mul_pow, inv_pow] at e ⊢
  convert e using 5
  · exact (res_pull_comp h m (W := M.U (p.1 0) ⊓ M.U (p'.1 0))
      (V1 := LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p.1 0) ⊓ LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p'.1 0))
      (M.g (p.1 0) (p'.1 0)) _ _ _ _ _).symm
  · exact res_res' (U := f ⁻¹ᵁ (L.U (p.2 0) ⊓ L.U (p'.2 0))) (pullU f _ (L.g (p.2 0) (p'.2 0))) _ _ _ _

end GlobalTheory.PowIsoRe
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.QuotSec

variable {X : Scheme.{0}}

abbrev rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (s : Γ(X, U)) :
    rs h' (rs h s) = rs (h'.trans h) s := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem coe_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res h u : Γ(X, V)ˣ) : Γ(X, V)) = rs h (u : Γ(X, U)) := rfl

theorem rs_coe_inv {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    rs h ((u⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (((res h u)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := by
  rw [← map_inv]; rfl

theorem res_g_self (L : LB X) (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i ⊓ L.U i) :
    res h (L.g i i) = 1 := by
  apply Units.ext
  rw [coe_res, ← rs_rs (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (h.trans inf_le_left), ← coe_res,
    hL.g_self]
  simp

def GenRel (P Q : LB X) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Prop :=
  ∀ p₁ q p₁' q', res (inf_le_left : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q) (a p₁ q) =
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁ ⊓ P.U p₁') (P.g p₁ p₁') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ Q.U q ⊓ Q.U q') (Q.g q q'))⁻¹ *
      res (inf_le_right : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁' ⊓ Q.U q') (a p₁' q')

theorem genRel_of_isGen (P Q : LB X) (α : LB.Gen (LB.div P Q)) (hα : α.IsGen) :
    GenRel P Q (fun p₁ q => α.s (p₁, q)) :=
  fun p₁ q p₁' q' => hα (p₁, q) (p₁', q')

theorem quot_compat (P Q : LB X) (hQ : Q.IsLB) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ) (ha : GenRel P Q a)
    (σ : LB.Sec P) (q : Q.ι) (p₁ p₁' : P.ι) :
    rs (inf_le_left : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁ ⊓ Q.U q)
      ((((a p₁ q)⁻¹ : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁)) =
    rs (inf_le_right : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁' ⊓ Q.U q)
      ((((a p₁' q)⁻¹ : Γ(X, P.U p₁' ⊓ Q.U q)ˣ) : Γ(X, P.U p₁' ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁' ⊓ Q.U q ≤ P.U p₁') (σ.f p₁')) := by
  have e := ha p₁ q p₁' q
  rw [res_g_self Q hQ q, inv_one, _root_.mul_one] at e
  have hσ := congrArg (rs (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁ ⊓ P.U p₁')) (σ.compat p₁ p₁')
  simp only [map_mul, rs_rs] at hσ ⊢
  rw [rs_coe_inv, rs_coe_inv, e, hσ, ← coe_res, mul_inv_rev, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem exists_quot_sec (P Q : LB X) (hP : P.IsLB) (hQ : Q.IsLB) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ)
    (ha : GenRel P Q a) (σ : LB.Sec P) :
    ∃ s : LB.Sec Q, ∀ p₁ q, rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁) =
      ((a p₁ q : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q) (s.f q) := by
  have hcov : ∀ (V : X.Opens), V ≤ ⨆ p₁, P.U p₁ ⊓ V := fun V x hx => by
    have : x ∈ (⨆ p₁, P.U p₁ : X.Opens) := by rw [hP.cover]; trivial
    obtain ⟨p₁, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p₁, hp, hx⟩
  have hglue : ∀ q, ∃ t : Γ(X, Q.U q), ∀ p₁, rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q) t =
      (((a p₁ q)⁻¹ : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁) := fun q =>
    (X.sheaf.existsUnique_gluing' (fun p₁ => P.U p₁ ⊓ Q.U q) (Q.U q) (fun _ => homOfLE inf_le_right)
      (hcov (Q.U q)) _ (fun p₁ p₁' => quot_compat P Q hQ a ha σ q p₁ p₁')).exists
  choose t ht using hglue
  refine ⟨⟨t, fun q q' => ?_⟩, fun p₁ q => ?_⟩
  · refine X.sheaf.eq_of_locally_eq' (fun p₁ => P.U p₁ ⊓ (Q.U q ⊓ Q.U q')) (Q.U q ⊓ Q.U q')
      (fun _ => homOfLE inf_le_right) (hcov _) _ _ (fun p₁ => ?_)
    change rs _ (rs _ (t q)) = rs _ ((Q.g q q' : Γ(X, Q.U q ⊓ Q.U q')) * rs _ (t q'))
    simp only [map_mul, rs_rs]
    rw [      ← rs_rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q)
        (le_inf inf_le_left (inf_le_right.trans inf_le_left) : P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q),
      ← rs_rs (inf_le_right : P.U p₁ ⊓ Q.U q' ≤ Q.U q')
        (le_inf inf_le_left (inf_le_right.trans inf_le_right) : P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q'),
      ht, ht]
    have e := congrArg (fun u : Γ(X, (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁ ⊓ Q.U q'))ˣ =>
      rs (le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right)) :
          P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁ ⊓ Q.U q')) (u⁻¹ : Γ(X, _)ˣ)) (ha p₁ q p₁ q')
    rw [res_g_self P hP p₁, _root_.one_mul, mul_inv_rev, inv_inv] at e
    simp only [map_mul, rs_rs, rs_coe_inv, Units.val_mul, ← coe_res] at e ⊢
    simp only [map_inv, ReciprocityTheory.ChartRestriction.G.DVR.res_res'] at e ⊢
    rw [e]
    ring
  · rw [ht, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]

end GlobalTheory.QuotSec

namespace GlobalTheory.HomFixMat

theorem divSec_exists : ∀ {X Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (a : ℤ) (α : LB.Gen (LB.div (powPull M g a) (powPull L f a))), α.IsGen → L.IsLB → M.IsLB → ∀ σ : LB.Sec (powPull M g a), ∃ s : LB.Sec (powPull L f a), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (X.presheaf.map (homOfLE (inf_le_left : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart M (fun _ : Fin 1 => g) p.1)).op).hom (σ.f p.1) = (show Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) from (α.s p).val) * (X.presheaf.map (homOfLE (inf_le_right : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s.f p.2) := by
  intro X Z₁ Z₂ L M f g a α hα hL hM σ
  obtain ⟨s, hs⟩ := GlobalTheory.QuotSec.exists_quot_sec (powPull M g a) (powPull L f a)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB M hM _ _) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _)
    (fun p₁ q => α.s (p₁, q)) (GlobalTheory.QuotSec.genRel_of_isGen _ _ α hα) σ
  exact ⟨s, fun p => hs p.1 p.2⟩

end GlobalTheory.HomFixMat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixUniq

open GlobalTheory.HomFixMat

theorem psi_unique {Rg : Type} [CommRing Rg] {A : Over (Sp Rg)} [GrpObj A] {X : Scheme.{0}} (ψ ψ₂ : X ⟶ (topS Rg ⊗ A).left)
    (h : ψ ≫ (snd (topS Rg) A).left = ψ₂ ≫ (snd (topS Rg) A).left) : ψ = ψ₂ := by
  haveI : Mono (topS Rg).hom := by
    show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  have e : ψ ≫ (fst (topS Rg) A).left = ψ₂ ≫ (fst (topS Rg) A).left := by
    rw [← cancel_mono (topS Rg).hom]
    simp only [Category.assoc, Over.w]
    rw [← Over.w (snd (topS Rg) A), ← Category.assoc, h, Category.assoc]
  exact pullback.hom_ext e h

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]


variable (L : LB A.left) (M : LB B.left) in
def RigEq (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R]
    (t : Sp R ⟶ Sp Rg) {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) : Prop :=
  ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k

theorem isoLB_cover {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left}
    {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB) (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)}
    (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (x : A'.left) :
    ∃ p, x ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := by
  have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
  obtain ⟨iM, hiM⟩ := hc M hM ((((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)).base x)
  obtain ⟨iL, hiL⟩ := hc L hL (((ψA ≫ (snd (topS Rg) A).left)).base x)
  exact ⟨(fun _ => iM, fun _ => iL), Set.mem_iInter.2 fun _ => hiM, Set.mem_iInter.2 fun _ => hiL⟩

end GlobalTheory.HomFixUniq
end
end
