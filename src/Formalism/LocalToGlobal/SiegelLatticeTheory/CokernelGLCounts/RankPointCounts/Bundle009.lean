module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle007

@[expose] public section

section

noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.LprU

open Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

def GramInvE {ι : Type} [Fintype ι] [DecidableEq ι] (H : HermSp M V) (v : ι → V) : Prop :=
  ∃ N : Matrix ι ι E, N * H.gram v = 1

theorem eqz {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInvE H v) {z : V}
    (hz : z ∈ Submodule.span E (Set.range v)) (h0 : ∀ i, H.h z (v i) = 0) : z = 0 := by
  obtain ⟨N, hN⟩ := hN
  have hz0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V),
      H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [hz0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hz
  have hg : H.gram v *ᵥ c = 0 := by
    funext i
    rw [Pi.zero_apply, ← h0 i, hsum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc : c = 0 := by
    have h2 := congrArg (fun u => N *ᵥ u) hg
    simp only [Matrix.mulVec_mulVec, hN, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  simp [hc]

theorem decompE {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInvE H v) (x : V) :
    ∃ c : ι → E, ∀ i, H.h (x - ∑ j, c j • v j) (v i) = 0 := by
  obtain ⟨N, hN⟩ := hN
  have hN' : H.gram v * N = 1 := mul_eq_one_comm.mp hN
  have h0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V),
      H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  let w : ι → E := fun i => H.h x (v i)
  refine ⟨N *ᵥ w, fun i => ?_⟩
  have hsub : ∀ y z : V, H.h (y - z) (v i) = H.h y (v i) - H.h z (v i) := fun y z => by
    rw [sub_eq_add_neg, H.h_add_left, ← neg_one_smul E z, H.h_smul_left]
    ring
  rw [hsub, hsum]
  have e : ∑ j, (N *ᵥ w) j * H.h (v j) (v i) = (H.gram v *ᵥ (N *ᵥ w)) i :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e, Matrix.mulVec_mulVec, hN', Matrix.one_mulVec, sub_self]

theorem y_eq_om {r : ℕ} (f f' : Fin (r + 1) → V) (α : Fin (r + 1) → E)
    (hy : ∀ b, b ≠ Fin.last r → H.h (∑ a, α a • f a) (f' b) = 0) :
    M.L.cj (H.Zhat f f').det • ∑ a, α a • f a = H.h (∑ a, α a • f a) (f' (Fin.last r)) • H.om f f' := by
  have h0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset (Fin (r + 1))) (c : (Fin (r + 1)) → E) (y : V),
      H.h (∑ a ∈ s, c a • f a) y = ∑ a ∈ s, c a * H.h (f a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  set Z := H.Zhat f f' with hZ
  set W := Z.map M.L.cj with hW
  set β : Fin (r + 1) → E := fun b => H.h (∑ a, α a • f a) (f' b) with hβdef

  have hβ : β = Wᵀ *ᵥ α := by
    funext b
    simp only [hβdef]
    rw [hsum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [H.h_herm (f' b) (f a)]
      exact mul_comm _ _

  have hcr : W.det • α = W.adjugateᵀ *ᵥ β := by
    rw [hβ, Matrix.mulVec_mulVec, Matrix.adjugate_transpose, Matrix.adjugate_mul, Matrix.det_transpose]
    first
      | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      | (ext a; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
  have hdet : W.det = M.L.cj Z.det := by
    first
      | exact (RingHom.map_det M.L.cj Z).symm
      | exact (RingHom.map_det (M.L.cj : E →+* E) Z).symm
  have hadj : W.adjugate = Z.adjugate.map M.L.cj := by
    first
      | (have h := RingHom.map_adjugate (M.L.cj : E →+* E) Z
         simp only [RingHom.mapMatrix_apply, RingHom.coe_coe] at h
         exact h.symm)
  have hcomp : ∀ a, M.L.cj Z.det * α a = β (Fin.last r) * M.L.cj (Z.adjugate (Fin.last r) a) := by
    intro a
    have h1 := congrFun hcr a
    rw [Pi.smul_apply, smul_eq_mul, hdet] at h1
    rw [h1, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.transpose_apply, hadj, Matrix.map_apply]
      ring
    · intro b _ hb
      have hb0 : β b = 0 := hy b hb
      rw [hb0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold Formalism.MainNotions.S.Loc.HermSp.om
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul, hcomp a]

end Formalism.MainNotions.S.Loc.HermSp.LprU
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem exists_of_mem_smulLat {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {c : E} {abelian₂ : Submodule M.L.O V} {x : V} (hx : x ∈ H.smulLat c abelian₂) : ∃ l ∈ abelian₂, x = c • l := by
  unfold Formalism.MainNotions.S.Loc.HermSp.smulLat at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨l, hl, rfl⟩
  | zero => exact ⟨0, abelian₂.zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨m, hm, rfl⟩ := hz
    exact ⟨l + m, abelian₂.add_mem hl hm, by simp [smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨a • l, abelian₂.smul_mem a hl, smul_comm a c l⟩

def Lemma0G (M : Model F E) (r : ℕ) : Prop :=
  ∀ g : SplitG M.L, M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    H.IsGeneric t → ∀ (w : V) (hw : w ∈ H.W0 t.f t.f'),
      (w ∈ t.abelian₂ ↔ (H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩ ∈ H.Lset t.abelian₂ t.f ∧
        H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩ ∈ H.Lset t.abelian₂ t.f' ∧
        (H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩) ∈ H.iotaGraph g t))

theorem lemma0G_holds (M : Model F E) (r : ℕ) : Lemma0G M r := by
  intro g hg V _ _ H t hgen w hw
  constructor
  · intro hwL
    refine ⟨⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, rfl⟩, ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, hwL, rfl⟩, ?_⟩
    refine ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, hwL, ?_, rfl⟩
    simp only [sub_self]
    exact Submodule.zero_mem _
  · rintro ⟨-, -, x', x, hx'L, hxL, hxx, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [HermSp.mkW, Submodule.mkQ_apply] at hp1 hp2

    have ha' : w - (x' : V) ∈ H.X t.f' := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp1
    have ha : w - (x : V) ∈ H.X t.f := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp2
    obtain ⟨α', hα'⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha'
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha
    obtain ⟨l, hl, hxl⟩ := exists_of_mem_smulLat H hxx
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (by exact_mod_cast h0)
    have hqqi : algebraMap F E (g.q : F) * algebraMap F E ((g.q : F)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
    have hqiq : algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F) = 1 := by
      rw [mul_comm, hqqi]
    have hMM : H.MMfam t =
        Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      simp only [HermSp.MMfam, hg]
    obtain ⟨-, hli, hprim⟩ := hgen.2
    rw [hMM] at hli hprim

    let γ : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim
      (Fin.snoc (fun i => algebraMap F E ((g.q : F)⁻¹) * (α' i - α i)) 0) (Fin.snoc α' 0)
    have hsum : ∑ j, γ j • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      have key : algebraMap F E (g.q : F) • ∑ j, γ j • Sum.elim t.f
          (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j =
          algebraMap F E (g.q : F) • l := by
        rw [← hxl, Fintype.sum_sum_type]
        simp only [γ, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, zero_smul, add_zero, smul_add, Finset.smul_sum]
        have e1 : (x : V) - x' = (w - x') - (w - x) := by abel
        rw [e1, ← hα', ← hα, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← mul_assoc, hqqi, one_mul, smul_comm (algebraMap F E (g.q : F)) (α' i),
          smul_smul (algebraMap F E (g.q : F)), hqqi, one_smul, sub_smul, smul_sub]
        abel
      calc _ = (algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F)) • ∑ j, γ j • Sum.elim t.f
              (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j := by
            rw [hqiq, one_smul]
        _ = l := by rw [mul_smul, key, ← mul_smul, hqiq, one_smul]
    have hlO := hprim l hl ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨γ, hsum⟩)
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 hlO
    have hβ' : ∑ j, (β j : E) • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      simpa only [Subring.smul_def] using hβ
    have hzero := Fintype.linearIndependent_iff.1 hli (fun j => (β j : E) - γ j) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hβ', hsum, sub_self])

    have hmem : ∀ i : Fin r, α' i ∈ M.L.O := by
      intro i
      have := hzero (Sum.inr i.castSucc)
      simp only [γ, Sum.elim_inr, Fin.snoc_castSucc, sub_eq_zero] at this
      rw [← this]
      exact (β _).2
    have hf'L := hgen.1.2.2.1.1.1
    have hw' : w = (x' : V) + ∑ i, α' i • t.f' i.castSucc := by rw [hα']; abel
    rw [hw']
    refine t.abelian₂.add_mem hx'L (Submodule.sum_mem _ fun i _ => ?_)
    have := t.abelian₂.smul_mem (⟨α' i, hmem i⟩ : M.L.O) (hf'L i.castSucc)
    simpa only [Subring.smul_def] using this

end G

end Formalism.L2.SG.LsDatumA
end
end
