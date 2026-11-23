module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFrameLA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

structure RGHyp (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop where
  hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (H.W0 t₂.f t₂.f')
  hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f')
  hsd₁ : H.IsSelfDual t₁.abelian₂
  hsd₂ : H.IsSelfDual Λ₂
  hMM₁ : MMo H t₁ ≤ t₁.abelian₂
  hMM₂ : MMo H t₂ ≤ Λ₂
  hth : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂
  hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂
  hsurj₁ : ∀ m₁ : ↥(MMsharp H t₁), ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂
  hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW t₂.f ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩
  hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW t₂.f' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩
  hC2 : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X t₂.f),
        φ (H.mkW t₁.f ⟨u, hu⟩) = H.mkW t₂.f ⟨u', hu'⟩
  hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X t₂.f'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW t₂.f' ⟨u', hu'⟩

theorem RGHyp.trF {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X t₁.f))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X t₁.f))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X t₂.f)) (hx₂ : a + b ∈ H.perp (H.X t₂.f))
    (h : φ (H.mkW t₁.f ⟨u₁ + n, hx₁⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩) :
    b = ψ n ∧ φ (H.mkW t₁.f ⟨u₁, hu₁p⟩) = H.mkW t₂.f ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hφ⟩ := D.hC2 u₁ hu₁U hu₁p
  have hn : (n : V) ∈ H.perp (H.X t₁.f) := mem_perp_isotropicSpan_of_mem_framePerp H n.2
  have hsplit : H.mkW t₁.f ⟨u₁ + n, hx₁⟩ = H.mkW t₁.f ⟨u₁, hu₁p⟩ + H.mkW t₁.f ⟨n, hn⟩ := by
    rw [← map_add (f := _)]
    rfl
  rw [hsplit, map_add (f := _), hφ, D.hC1 n, ← map_add (f := _)] at h
  have hX : ((u' + ψ n : V)) - (a + b) ∈ H.X t₂.f := sub_mem_X_of_mkW_eq H h
  have hXle : H.X t₂.f ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i.castSucc, rfl⟩
  have hdiff : (ψ n : V) - b = ((u' + ψ n) - (a + b)) - (u' - a) := by abel
  have hmemS : (ψ n : V) - b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [hdiff]
    exact Submodule.sub_mem _ (hXle hX) (Submodule.sub_mem _ hu'U ha)
  have hmemW : (ψ n : V) - b ∈ H.W0 t₂.f t₂.f' := Submodule.sub_mem _ (ψ n).2 hb
  have h0 : (ψ n : V) - b = 0 := (Submodule.disjoint_def.1 D.hU₂.disjoint) _ hmemS hmemW
  have hbψ : b = ψ n := (sub_eq_zero.1 h0).symm
  refine ⟨hbψ, ?_⟩
  rw [hφ]
  have hua : (u' : V) - a ∈ H.X t₂.f := by
    have e1 : (u' : V) - a = (u' + ψ n) - (a + b) := by
      rw [hbψ]
      abel
    rw [e1]
    exact hX
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact hua

theorem RGHyp.trF' {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X t₁.f'))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X t₁.f'))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X t₂.f')) (hx₂ : a + b ∈ H.perp (H.X t₂.f'))
    (h : φ' (H.mkW t₁.f' ⟨u₁ + n, hx₁⟩) = H.mkW t₂.f' ⟨a + b, hx₂⟩) :
    b = ψ n ∧ φ' (H.mkW t₁.f' ⟨u₁, hu₁p⟩) = H.mkW t₂.f' ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hφ⟩ := D.hC2' u₁ hu₁U hu₁p
  have hn : (n : V) ∈ H.perp (H.X t₁.f') := mem_perp_isotropicSpan_of_mem_framePerp' H n.2
  have hsplit : H.mkW t₁.f' ⟨u₁ + n, hx₁⟩ = H.mkW t₁.f' ⟨u₁, hu₁p⟩ + H.mkW t₁.f' ⟨n, hn⟩ := by
    rw [← map_add (f := _)]
    rfl
  rw [hsplit, map_add (f := _), hφ, D.hC1' n, ← map_add (f := _)] at h
  have hX : ((u' + ψ n : V)) - (a + b) ∈ H.X t₂.f' := sub_mem_X_of_mkW_eq H h
  have hXle : H.X t₂.f' ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inr i.castSucc, rfl⟩
  have hdiff : (ψ n : V) - b = ((u' + ψ n) - (a + b)) - (u' - a) := by abel
  have hmemS : (ψ n : V) - b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [hdiff]
    exact Submodule.sub_mem _ (hXle hX) (Submodule.sub_mem _ hu'U ha)
  have hmemW : (ψ n : V) - b ∈ H.W0 t₂.f t₂.f' := Submodule.sub_mem _ (ψ n).2 hb
  have h0 : (ψ n : V) - b = 0 := (Submodule.disjoint_def.1 D.hU₂.disjoint) _ hmemS hmemW
  have hbψ : b = ψ n := (sub_eq_zero.1 h0).symm
  refine ⟨hbψ, ?_⟩
  rw [hφ]
  have hua : (u' : V) - a ∈ H.X t₂.f' := by
    have e1 : (u' : V) - a = (u' + ψ n) - (a + b) := by
      rw [hbψ]
      abel
    rw [e1]
    exact hX
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact hua

end RG3

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem dec_of {U W : Submodule E V} (h : IsCompl U W) (x : V) : ∃ a ∈ U, ∃ b ∈ W, a + b = x := by
  have hx : x ∈ U ⊔ W := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  exact Submodule.mem_sup.mp hx

theorem dec_unique {U W : Submodule E V} (h : IsCompl U W) {a a' b b' : V} (ha : a ∈ U) (ha' : a' ∈ U)
    (hb : b ∈ W) (hb' : b' ∈ W) (e : a + b = a' + b') : a = a' ∧ b = b' := by
  have h1 : a - a' ∈ U := U.sub_mem ha ha'
  have heq : a - a' = b' - b := by
    rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
  have h2 : a - a' ∈ W := by
    rw [heq]
    exact W.sub_mem hb' hb
  have h0 : a - a' = 0 := by
    have hbot := h.inf_eq_bot
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot _ ⟨h1, h2⟩
  have haa : a = a' := sub_eq_zero.mp h0
  refine ⟨haa, ?_⟩
  rw [haa] at e
  exact add_left_cancel e

theorem dec_diff {U W : Submodule E V} (h : IsCompl U W) (c : E) {a a' a'' b b' b'' x x' y : V}
    (ha : a ∈ U) (ha' : a' ∈ U) (ha'' : a'' ∈ U) (hb : b ∈ W) (hb' : b' ∈ W) (hb'' : b'' ∈ W)
    (hx : a + b = x) (hx' : a' + b' = x') (hy : a'' + b'' = y) (hd : x - x' = c • y) :
    a - a' = c • a'' ∧ b - b' = c • b'' := by
  have hsum : (a - a') + (b - b') = c • a'' + c • b'' := by
    rw [← smul_add, hy, ← hd, ← hx, ← hx']
    abel
  exact dec_unique h (U.sub_mem ha ha') (U.smul_mem c ha'') (W.sub_mem hb hb') (W.smul_mem c hb'') hsum

theorem part_MMsharp (t : Term V M r) (Λ : Submodule M.L.O V) (hsd : H.IsSelfDual Λ) (hMM : MMo H t ≤ Λ)
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t.f t.f'))) (hb : b ∈ H.W0 t.f t.f')
    (hab : a + b ∈ Λ) : a ∈ MMsharp H t := by

  have hmm_le : ∀ i, H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
    intro i
    unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
    rcases hs : M.split with _ | g
    · dsimp only
      rcases i with i | i
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    · dsimp only
      rcases i with i | i
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
          (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  have hspan : Submodule.span E (Set.range (Sum.elim t.f t.f')) ≤ Submodule.span E (Set.range (H.MMfam t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
    rcases hs : M.split with _ | g
    · dsimp only
      exact Submodule.subset_span ⟨i, rfl⟩
    · dsimp only
      rcases i with i | i
      · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
        have e : t.f' i = t.f i + algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (t.f' i - t.f i)) := by
          rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]
          abel
        show t.f' i ∈ _
        rw [e]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  refine ⟨hspan ha, fun m hm => ?_⟩
  have hmΛ : m ∈ Λ := hMM hm
  have hab' := (hsd.2.2 (a + b)).mp hab m hmΛ
  have hmX : m ∈ H.Xp t.f ⊔ H.Xp t.f' := by
    have hle : MMo H t ≤ (H.Xp t.f ⊔ H.Xp t.f').restrictScalars M.L.O := by
      unfold Formalism.L2.SG.LsDatumA.MMo
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmm_le i
    exact hle hm
  have hbm : H.h b m = 0 := (show ∀ x ∈ H.Xp t.f ⊔ H.Xp t.f', H.h b x = 0 from hb) m hmX
  rw [H.h_add_left, hbm, add_zero] at hab'
  exact hab'

theorem perp_left {g : Fin (r + 1) → V} {a b : V} (hb : b ∈ H.perp (H.X g)) (hab : a + b ∈ H.perp (H.X g)) :
    a ∈ H.perp (H.X g) := by
  have h1 := (H.perp (H.X g)).sub_mem hab hb
  simpa using h1

theorem smul_cancel_q (g : SplitG M.L) {v w : V}
    (h : algebraMap F E (g.q : F) • v = algebraMap F E (g.q : F) • w) : v = w := by
  have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hu : IsUnit (algebraMap F E (g.q : F)) := (IsUnit.mk0 _ hq).map _
  exact (hu.smul_left_cancel).mp h

end RG2

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

def lin {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) : S.V := ∑ i, c i • u i

theorem hT_lin_right {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) (x : S.V) :
    S.hT x (lin u c) = ∑ i, c i * S.hT x (u i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin, map_sum, map_smul, smul_eq_mul]

theorem hT_lin_left {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) (x : S.V) :
    S.hT (lin u c) x = ∑ i, star (c i) * S.hT (u i) x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply]

theorem hT_lin_lin {ι : Type*} [Fintype ι] (u : ι → S.V) (c d : ι → E) :
    S.hT (lin u c) (lin u d) = ∑ i, ∑ j, star (c i) * d j * S.hT (u i) (u j) := by
  rw [hT_lin_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT_lin_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem lin_add {ι : Type*} [Fintype ι] (u : ι → S.V) (c d : ι → E) : lin u (c + d) = lin u c + lin u d := by
  simp [lin, add_smul, Finset.sum_add_distrib]

theorem lin_smul {ι : Type*} [Fintype ι] (u : ι → S.V) (t : E) (c : ι → E) : lin u (t • c) = t • lin u c := by
  simp [lin, smul_smul, Finset.smul_sum]

theorem lin_sub {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) : lin u c ∈ Submodule.span E (Set.range u) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def pc {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (v : S.V) : ι → E :=
  (gram S u u)⁻¹ *ᵥ fun k => S.hT (u k) v

theorem pc_add {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (x y : S.V) :
    pc u (x + y) = pc u x + pc u y := by
  unfold pc
  rw [← Matrix.mulVec_add]
  congr 1
  funext k
  exact map_add (S.hT (u k)) x y

theorem pc_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (t : E) (x : S.V) :
    pc u (t • x) = t • pc u x := by
  unfold pc
  rw [← Matrix.mulVec_smul]
  congr 1
  funext k
  exact map_smul (S.hT (u k)) t x

theorem hT_u_lin {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (c : ι → E) (k : ι) :
    S.hT (u k) (lin u c) = (gram S u u *ᵥ c) k := by
  rw [hT_lin_right]
  simp [Matrix.mulVec, dotProduct, gram, mul_comm]

theorem hT_u_rem {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (v : S.V)
    (k : ι) : S.hT (u k) (v - lin u (pc u v)) = 0 := by
  rw [map_sub, hT_u_lin]
  unfold pc
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  simp

theorem hT_span_rem {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (v z : S.V)
    (hz : z ∈ Submodule.span E (Set.range u)) : S.hT z (v - lin u (pc u v)) = 0 ∧ S.hT (v - lin u (pc u v)) z = 0 := by
  have first : S.hT z (v - lin u (pc u v)) = 0 := by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hT_u_rem u hdet v k
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [LinearMap.map_smulₛₗ₂, hx]
  refine ⟨first, ?_⟩
  rw [← S.herm.eq z, first]
  simp

def isoG {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := v - lin u (pc u v) + lin u' (pc u v)
  map_add' x y := by
    rw [pc_add, lin_add, lin_add]; abel
  map_smul' t x := by
    rw [pc_smul, lin_smul, lin_smul, RingHom.id_apply, smul_add, smul_sub]

theorem isoG_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (v : S.V) :
    isoG u u' v = v - lin u (pc u v) + lin u' (pc u v) := rfl

theorem pc_self {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (m : ι) :
    pc u (u m) = Pi.single m 1 := by
  have hcol : (fun k => S.hT (u k) (u m)) = gram S u u *ᵥ Pi.single m 1 := by
    funext k
    simp [Matrix.mulVec, dotProduct, gram, Pi.single_apply]
  unfold pc
  rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem lin_single {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (m : ι) : lin u (Pi.single m 1) = u m := by
  simp [lin, Pi.single_apply, ite_smul]

private theorem hT_isoG_of_gram_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (hG : gram S u' u' = gram S u u)
    (hdet : (gram S u u).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range u)) (x y : S.V) :
    S.hT (isoG u u' x) (isoG u u' y) = S.hT x y := by
  have hlin : ∀ (w : ι → S.V) (c : ι → E), (∀ i, w i ∈ Submodule.span E (Set.range u)) →
      lin w c ∈ Submodule.span E (Set.range u) := by
    intro w c hw
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hw i)
  have hu : ∀ i, u i ∈ Submodule.span E (Set.range u) := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hgram : ∀ (w : ι → S.V) (c d : ι → E), S.hT (lin w c) (lin w d) =
      ∑ i, ∑ j, star (c i) * d j * gram S w w i j := by
    intro w c d
    rw [hT_lin_lin]
    simp [gram]
  have ex : x = (x - lin u (pc u x)) + lin u (pc u x) := by abel
  have ey : y = (y - lin u (pc u y)) + lin u (pc u y) := by abel
  have gx : isoG u u' x = (x - lin u (pc u x)) + lin u' (pc u x) := by rw [isoG_apply]
  have gy : isoG u u' y = (y - lin u (pc u y)) + lin u' (pc u y) := by rw [isoG_apply]
  have o1 := fun z hz => (hT_span_rem u hdet x z hz)
  have o2 := fun z hz => (hT_span_rem u hdet y z hz)
  have A1 := (o2 _ (hlin u' (pc u x) hsp)).1
  have A2 := (o1 _ (hlin u' (pc u y) hsp)).2
  have B1 := (o2 _ (hlin u (pc u x) hu)).1
  have B2 := (o1 _ (hlin u (pc u y) hu)).2
  conv_rhs => rw [ex, ey]
  rw [gx, gy]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [A1, A2, B1, B2, hgram u', hgram u, hG]

theorem isom_ext {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (hG : gram S u' u' = gram S u u)
    (hdet : (gram S u u).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range u)) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ (∀ i, g (u i) = u' i) ∧
      (∀ w, (∀ k, S.hT (u k) w = 0) → g w = w) ∧
      ∀ v, g v = v + ∑ k, S.hT (u k) v • ∑ m, (gram S u u)⁻¹ m k • (u' m - u m) := by
  haveI := S.fd
  have hinj : Function.Injective (isoG u u') := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply S.nondeg.1 x
    intro y
    rw [← hT_isoG_of_gram_eq u u' hG hdet hsp x y, hx]
    simp
  have hsurj : Function.Surjective (isoG u u') := LinearMap.injective_iff_surjective.mp hinj
  have hbij : Function.Bijective (isoG u u') := ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.ofBijective (isoG u u') hbij, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact hT_isoG_of_gram_eq u u' hG hdet hsp x y
  · intro i
    simp only [LinearEquiv.ofBijective_apply, isoG_apply, pc_self u hdet, lin_single]
    abel
  · intro w hw
    have hp : pc u w = 0 := by
      unfold pc
      have : (fun k => S.hT (u k) w) = 0 := funext hw
      rw [this, Matrix.mulVec_zero]
    simp only [LinearEquiv.ofBijective_apply, isoG_apply, hp]
    simp [lin]
  · intro v
    simp only [LinearEquiv.ofBijective_apply, isoG_apply]
    have key : lin u' (pc u v) - lin u (pc u v) =
        ∑ k, S.hT (u k) v • ∑ m, (gram S u u)⁻¹ m k • (u' m - u m) := by
      simp only [lin, pc, Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← smul_sub,
        Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
    rw [← key]
    abel

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA
end
end
