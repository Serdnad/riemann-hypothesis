module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle036
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle038
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericDatumLatticeEqPerpQuotientImageTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFamiliesCongrModUnitriangular
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle040
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameDual

open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

theorem hf_sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

end

theorem exists_unip_change_dual : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (t : E) (gs gs2 : Fin r → S.V), (∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0) → (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → (∀ a j, hf L S.Hm (g a) (gs2 j) = if a = j.castSucc then 1 else 0) → (∀ i j, hf L S.Hm (gs i) (gs j) = 0) → (∀ i j, hf L S.Hm (gs2 i) (gs2 j) = 0) → ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧ (∀ j, m (gs j) = gs2 j) ∧ ∀ A : Submodule L.O S.V, (∀ x ∈ S.spanTo g r, x ∈ A) → (∀ x ∈ A, x ∈ perp L S.Hm (S.spanTo g r)) → m • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) = A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs2))).restrictScalars L.O := by
  intro F _ _ _ _ _ E _ _ _ L r k S g t gs gs2 hg hd hd2 hi hi2
  have hcj := hf_cj L S.herm.1
  obtain ⟨G, hG⟩ : ∃ G : Fin r → S.V, ∀ j, G j = g j.castSucc := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin r → S.V, ∀ j, w j = gs2 j - gs j := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin r → S.V, ∀ j, u j = w j + ∑ i, hf L S.Hm (gs j) (w i) • G i :=
    ⟨_, fun _ => rfl⟩
  have hGa : ∀ i a, hf L S.Hm (G i) (g a) = 0 := fun i a => by
    rw [hG, hg, if_neg]; rintro ⟨h, -⟩; exact Fin.castSucc_ne_last i h
  have haG : ∀ a i, hf L S.Hm (g a) (G i) = 0 := fun a i => by
    rw [hG, hg, if_neg]; rintro ⟨-, h⟩; exact Fin.castSucc_ne_last i h
  have hGG : ∀ i j, hf L S.Hm (G i) (G j) = 0 := fun i j => by rw [hG j]; exact hGa i _
  have hgw : ∀ a i, hf L S.Hm (g a) (w i) = 0 := fun a i => by rw [hw, hf_sub_r, hd, hd2, sub_self]
  have hwg : ∀ i a, hf L S.Hm (w i) (g a) = 0 := fun i a => by rw [← hcj, hgw, map_zero]
  have hGw : ∀ i j, hf L S.Hm (G i) (w j) = 0 := fun i j => by rw [hG i]; exact hgw _ _
  have hwG : ∀ i j, hf L S.Hm (w i) (G j) = 0 := fun i j => by rw [hG j]; exact hwg _ _
  have hGu : ∀ i j, hf L S.Hm (G i) (u j) = 0 := fun i j => by
    simp only [hu, hf_add_r, hf_sum_r, hf_smul_r, hGw, hGG, mul_zero, Finset.sum_const_zero, add_zero]
  have huG : ∀ j i, hf L S.Hm (u j) (G i) = 0 := fun j i => by
    simp only [hu, hf_add_l, hf_sum_l, hf_smul_l, hwG, hGG, mul_zero, Finset.sum_const_zero, add_zero]
  have huw : ∀ j i, hf L S.Hm (u j) (w i) = hf L S.Hm (w j) (w i) := fun j i => by
    simp only [hu, hf_add_l, hf_sum_l, hf_smul_l, hGw, mul_zero, Finset.sum_const_zero, add_zero]
  have huu : ∀ j l, hf L S.Hm (u j) (u l) = hf L S.Hm (w j) (w l) := fun j l => by
    conv_lhs => rw [hu l]
    simp only [hf_add_r, hf_sum_r, hf_smul_r, huG, huw, mul_zero, Finset.sum_const_zero, add_zero]
  have hgsG : ∀ j l, hf L S.Hm (gs j) (G l) = if l = j then 1 else 0 := fun j l => by
    rw [← hcj, hG, hd]
    by_cases h : l = j
    · subst h; simp
    · rw [if_neg (fun e => h (Fin.castSucc_injective _ e)), if_neg h, map_zero]
  have K : ∀ j i, hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (gs i) + hf L S.Hm (w j) (w i) = 0 := by
    intro j i
    have e : ∀ j, gs2 j = gs j + w j := fun j => by rw [hw]; abel
    have h2 := hi2 j i
    rw [e, e, hf_add_l, hf_add_r, hf_add_r, hi] at h2
    linear_combination h2

  obtain ⟨ff, hff⟩ : ∃ ff : S.V → S.V, ∀ v, ff v = v + ∑ j, hf L S.Hm v (G j) • u j -
      ∑ i, hf L S.Hm v (w i) • G i := ⟨_, fun _ => rfl⟩
  obtain ⟨fi, hfi⟩ : ∃ fi : S.V → S.V, ∀ v, fi v = v - ∑ j, hf L S.Hm v (G j) • u j +
      ∑ i, (hf L S.Hm v (w i) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w i)) • G i :=
    ⟨_, fun _ => rfl⟩
  have hff_l : ∀ v y, hf L S.Hm (ff v) y = hf L S.Hm v y + ∑ j, hf L S.Hm v (G j) * hf L S.Hm (u j) y -
      ∑ i, hf L S.Hm v (w i) * hf L S.Hm (G i) y := fun v y => by
    rw [hff]; simp only [hf_add_l, hf_sub_l, hf_sum_l, hf_smul_l]
  have hff_r : ∀ y v, hf L S.Hm y (ff v) = hf L S.Hm y v + ∑ j, hf L S.Hm (G j) v * hf L S.Hm y (u j) -
      ∑ i, hf L S.Hm (w i) v * hf L S.Hm y (G i) := fun y v => by
    rw [hff]; simp only [hf_add_r, hf_sub_r, hf_sum_r, hf_smul_r, hcj]
  have hfi_l : ∀ v y, hf L S.Hm (fi v) y = hf L S.Hm v y - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (u j) y +
      ∑ i, (hf L S.Hm v (w i) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w i)) * hf L S.Hm (G i) y :=
    fun v y => by
    rw [hfi]; simp only [hf_add_l, hf_sub_l, hf_sum_l, hf_smul_l]
  have h1 : ∀ v, ff (fi v) = v := fun v => by
    have eG : ∀ l, hf L S.Hm (fi v) (G l) = hf L S.Hm v (G l) := fun l => by
      simp only [hfi_l, huG, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
    have ew : ∀ l, hf L S.Hm (fi v) (w l) =
        hf L S.Hm v (w l) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w l) := fun l => by
      simp only [hfi_l, huw, hGw, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hff]; simp only [eG, ew]; rw [hfi]; abel
  have h2 : ∀ v, fi (ff v) = v := fun v => by
    have eG : ∀ l, hf L S.Hm (ff v) (G l) = hf L S.Hm v (G l) := fun l => by
      simp only [hff_l, huG, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
    have ew : ∀ l, hf L S.Hm (ff v) (w l) =
        hf L S.Hm v (w l) + ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w l) := fun l => by
      simp only [hff_l, huw, hGw, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [hfi]; simp only [eG, ew, add_sub_cancel_right]; rw [hff]; abel
  obtain ⟨m, hm⟩ : ∃ m : S.GLV, ∀ v, m v = ff v := by
    refine ⟨{ toFun := ff, invFun := fi, left_inv := h2, right_inv := h1, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro x y; simp only [hff, hf_add_l, add_smul, Finset.sum_add_distrib]; abel
    · intro c x; simp only [hff, hf_smul_l, smul_add, smul_sub, Finset.smul_sum, mul_smul, RingHom.id_apply]
  have iso : ∀ v v', hf L S.Hm (ff v) (ff v') = hf L S.Hm v v' := by
    intro v v'
    rw [hff_l]
    simp only [hff_r, huu, huG, hGu, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

    have hvu : ∀ j, hf L S.Hm v (u j) = hf L S.Hm v (w j) + ∑ i, hf L S.Hm (w i) (gs j) * hf L S.Hm v (G i) := by
      intro j; rw [hu, hf_add_r, hf_sum_r]; simp only [hf_smul_r, hcj]
    have huv : ∀ j, hf L S.Hm (u j) v' = hf L S.Hm (w j) v' + ∑ i, hf L S.Hm (gs j) (w i) * hf L S.Hm (G i) v' := by
      intro j; rw [hu, hf_add_l, hf_sum_l]; simp only [hf_smul_l]
    simp only [hvu, huv]
    have e1 : ∑ j, hf L S.Hm (G j) v' * (hf L S.Hm v (w j) + ∑ i, hf L S.Hm (w i) (gs j) * hf L S.Hm v (G i)) =
        ∑ j, hf L S.Hm v (w j) * hf L S.Hm (G j) v' +
          ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * hf L S.Hm (w j) (gs i) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ x, hf L S.Hm v (G x) * (hf L S.Hm (w x) v' + ∑ i, hf L S.Hm (gs x) (w i) * hf L S.Hm (G i) v' +
          ∑ l, hf L S.Hm (G l) v' * hf L S.Hm (w x) (w l)) =
        ∑ x, hf L S.Hm (w x) v' * hf L S.Hm v (G x) +
          ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * (hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (w i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_add, mul_add, mul_comm (hf L S.Hm v (G x)), add_assoc]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have key : (∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * hf L S.Hm (w j) (gs i)) +
        ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * (hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (w i)) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      linear_combination hf L S.Hm v (G j) * hf L S.Hm (G i) v' * K j i
    rw [e1, e2]
    linear_combination key

  have hiso : ∀ x y, hf L S.Hm (m x) (m y) = hf L S.Hm x y := by simp only [hm]; exact iso
  have hmg : ∀ a, m (g a) = g a := fun a => by
    rw [hm, hff]; simp only [haG, hgw, zero_smul, Finset.sum_const_zero, add_zero, sub_zero]
  have hmgs : ∀ j, m (gs j) = gs2 j := fun j => by
    rw [hm, hff]
    simp only [hgsG, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hu, hw]; abel
  have hX : ∀ i, G i ∈ S.spanTo g r := fun i => by
    rw [hG]; exact Submodule.subset_span ⟨i.castSucc, by simp, rfl⟩
  have hfix : ∀ J, ∀ v ∈ S.spanTo g J, m v = v := by
    intro J v hv
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨a, -, rfl⟩ := hy; exact hmg a
    | zero => exact map_zero m
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have hspan : ∀ J v, m v ∈ S.spanTo g J ↔ v ∈ S.spanTo g J := fun J v =>
    ⟨fun h => by
      have e : m (m v) = m v := hfix J _ h
      rw [m.injective e] at h; exact h,
     fun h => by rw [hfix J v h]; exact h⟩
  have hmperp : ∀ v ∈ perp L S.Hm (S.spanTo g r), m v = v - ∑ i, hf L S.Hm v (w i) • G i := by
    intro v hv
    rw [hm, hff]
    simp only [hv _ (hX _), zero_smul, Finset.sum_const_zero, add_zero]
  have hperp : ∀ v, m v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r) := fun v =>
    ⟨fun h y hy => by
      have := h y hy
      rwa [← hfix r y hy, hiso] at this,
     fun h y hy => by
      rw [← hfix r y hy, hiso]; exact h y hy⟩
  have hpspan : ∀ (f : Fin r → S.V) x,
      x ∈ perp L S.Hm (Submodule.span E (Set.range f)) ↔ ∀ l, hf L S.Hm x (f l) = 0 := fun f x =>
    ⟨fun h l => h _ (Submodule.subset_span ⟨l, rfl⟩),
     fun h => GlobalTheory.FramePsi.hf_span_right L S.Hm x _ (by rintro _ ⟨l, rfl⟩; exact h l)⟩
  refine ⟨m, ?_, hmg, hmgs, ?_⟩
  · simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf]
    refine ⟨⟨hiso, fun j => ⟨fun v => hspan _ v, fun v hv => ?_⟩⟩, hperp, fun v hv => ?_⟩
    · rw [hfix _ v hv, sub_self]; exact Submodule.zero_mem _
    · rw [hmperp v hv, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i))
  · intro A hXA hAp
    have hsum : ∀ x, ∑ i, hf L S.Hm x (w i) • G i ∈ A := fun x =>
      hXA _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i))
    have hAm : ∀ x, m x ∈ A ↔ x ∈ A := fun x =>
      ⟨fun h => by
        have hp : x ∈ perp L S.Hm (S.spanTo g r) := (hperp x).1 (hAp _ h)
        have e : x = m x + ∑ i, hf L S.Hm x (w i) • G i := by rw [hmperp x hp]; abel
        rw [e]; exact A.add_mem h (hsum x),
       fun h => by rw [hmperp x (hAp x h)]; exact A.sub_mem h (hsum x)⟩
    have hPm : ∀ x, m x ∈ perp L S.Hm (Submodule.span E (Set.range gs2)) ↔
        x ∈ perp L S.Hm (Submodule.span E (Set.range gs)) := fun x => by
      rw [hpspan, hpspan]
      simp only [← hmgs, hiso]
    have hsm : ∀ (Λ : Submodule L.O S.V) x, m x ∈ m • Λ ↔ x ∈ Λ := fun Λ x => by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨fun ⟨y, hy, e⟩ => (m.injective e) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    ext y
    obtain ⟨x, rfl⟩ := m.surjective y
    rw [hsm]
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, hAm, hPm]

end GlobalTheory.FrameDual
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.eichler_map_mem_unipotent_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ (j : Fin r) (x u : S.V) (s : E), x ∈ S.spanTo g (j + 1) → u ∈ perp L S.Hm (S.spanTo g (j + 1)) → s + L.cj s = S.h u u → ∃ n ∈ S.Nof g, (∀ v, n v = eich L S.Hm x u s v) ∧ (∀ v, n⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v ∈ S.spanTo g (j + 1), n v = v) ∧ ∀ m ∈ S.Nof g, S.psiOf g gs n = L.psi0 (algebraMap F E S.th⁻¹ * (S.h x (gs j) * S.h (m (g j.succ)) u)) := by
  first | exact @GlobalTheory.HL.EichlerUnip.eichler_mem_unip | exact GlobalTheory.HL.EichlerUnip.eichler_mem_unip | (intros; apply GlobalTheory.HL.EichlerUnip.eichler_mem_unip <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.RatExt

section General
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R)

theorem single_comp {n : ℕ} (i : Fin n) :
    (fun j => ι ((Pi.single i 1 : Fin n → E) j)) = (Pi.single i 1 : Fin n → R) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem span_range {n : ℕ} :
    Submodule.span R (Set.range fun (x : Fin n → E) (i : Fin n) => ι (x i)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun R (Fin n)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, by simpa using single_comp ι i⟩

theorem lin_ext {n : ℕ} {M : Type} [AddCommGroup M] [Module R M] (a b : (Fin n → R) →ₗ[R] M)
    (h : ∀ x : Fin n → E, a (fun i => ι (x i)) = b (fun i => ι (x i))) : a = b :=
  LinearMap.ext_on_range (span_range ι) h

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R) in
theorem _root_.GlobalTheory.HL.RatExt.exists_equiv {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    ∃ g' : (Fin n → R) ≃ₗ[R] (Fin n → R), ∀ x, g' (fun i => ι (x i)) = fun i => ι (g x i) := by
  set M := LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))
  set N := LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))
  have hMN : M * N = 1 := by
    simp only [M, N, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hNM : N * M = 1 := by
    simp only [M, N, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  refine ⟨LinearEquiv.ofLinear (Matrix.toLin' (M.map ι)) (Matrix.toLin' (N.map ι)) ?_ ?_, ?_⟩
  · rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.toLin'_one]
  · intro x
    funext i
    simp only [LinearEquiv.ofLinear_apply, Matrix.toLin'_apply]
    have h := LinearMap.toMatrix'_mulVec (g : (Fin n → E) →ₗ[E] (Fin n → E)) x
    rw [show g x = M.mulVec x from h.symm, RingHom.map_mulVec]
    rfl

end General

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem exists_dual_family_of_linearIndependent {E : Type} [Field E] {n m : ℕ} {v : Fin m → Fin n → E}
    (hv : LinearIndependent E v) :
    ∃ φ : Fin m → (Fin n → E) →ₗ[E] E, ∀ a b, φ b (v a) = if a = b then 1 else 0 := by
  choose φ hφ using fun b =>
    LinearMap.exists_extend ((Module.Basis.span hv).coord b)
  refine ⟨φ, fun a b => ?_⟩
  have h := LinearMap.congr_fun (hφ b) ⟨v a, Submodule.subset_span (Set.mem_range_self a)⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h
  rw [h]
  have hb : (⟨v a, Submodule.subset_span (Set.mem_range_self a)⟩ : Submodule.span E (Set.range v))
      = Module.Basis.span hv a := by
    ext; simp [Module.Basis.span_apply]
  rw [hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]


open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.RatExt.rational_extend : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig), ∀ (n : ℕ) (p : HeightOneSpectrum (𝓞 F)), Function.Injective (A.bc (n := n) p) ∧ Submodule.span (A.loc p).Ep (Set.range (A.bc (n := n) p)) = ⊤ ∧ (∀ g : (Fin n → E) ≃ₗ[E] (Fin n → E), ∃! g', A.Ext p g g') ∧ (∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) g' (Λ : Submodule (𝓞 E) (Fin n → E)), A.Ext p g g' → A.lat p (Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) = g' • A.lat p Λ) ∧ (∀ (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E), _root_.GlobalTheory.HL.hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p y) = (A.loc p).ιE (∑ i, ∑ j, x i * Hm i j * sig (y j))) ∧ ∀ (m : ℕ) (v : Fin m → Fin n → E), LinearIndependent E v ↔ LinearIndependent (A.loc p).Ep fun a => A.bc p (v a) := by
  intro F E _ _ _ _ _ sig A n p
  have hbc : ∀ x : Fin n → E, A.bc p x = fun i => (A.loc p).ιE (x i) := fun _ => rfl
  haveI : Nontrivial (A.loc p).Ep := by
    have h := (A.L p).rank
    exact Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by omega)
  have hinj : Function.Injective (A.bc (n := n) p) := by
    intro x y h
    funext i
    exact (A.loc p).ιE.injective (congrFun h i)
  have hspan : Submodule.span (A.loc p).Ep (Set.range (A.bc (n := n) p)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (A.loc p).Ep (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    rw [hbc, Pi.basisFun_apply]
    funext j
    rcases eq_or_ne j i with rfl | h <;> simp [*]
  have hext : ∀ g : (Fin n → E) ≃ₗ[E] (Fin n → E), ∃ g', A.Ext p g g' := by
    intro g
    obtain ⟨g', hg'⟩ := _root_.GlobalTheory.HL.RatExt.exists_equiv (A.loc p).ιE g
    exact ⟨g', fun x => hg' x⟩
  refine ⟨hinj, hspan, fun g => ?_, fun g g' Λ hg => ?_, fun Hm x y => ?_, fun m v => ?_⟩
  · obtain ⟨g', hg'⟩ := hext g
    refine ⟨g', hg', fun g'' hg'' => ?_⟩
    apply LinearEquiv.toLinearMap_injective
    refine LinearMap.ext_on_range hspan fun x => ?_
    simp only [LinearEquiv.coe_coe]
    rw [hg'' x, hg' x]
  · unfold _root_.GlobalTheory.HL.Places.lat
    rw [Submodule.smul_span]
    congr 1
    rw [Submodule.map_coe, Set.image_image, ← Set.image_smul, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [LinearEquiv.smul_def, hg x]
    rfl
  · unfold _root_.GlobalTheory.HL.hf
    rw [_root_.GlobalTheory.HL.Places.L_cj]

    simp [hbc, map_sum, map_mul, Matrix.map_apply, _root_.Formalism.MainNotions.S.Loc.LocAt.cj_ιE]
  · constructor
    · intro hv
      obtain ⟨φ, hφ⟩ := exists_dual_family_of_linearIndependent hv
      rw [Fintype.linearIndependent_iff]
      intro c hc b
      have key : ∀ a, ∑ j, (A.loc p).ιE (v a j) *
          (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) = if a = b then 1 else 0 := by
        intro a
        have h := congrArg (A.loc p).ιE (LinearMap.pi_apply_eq_sum_univ (φ b) (v a))
        rw [hφ] at h

        simp only [map_sum, smul_eq_mul, map_mul] at h
        rw [← h]
        split_ifs <;> simp
      calc c b = ∑ a, c a * (if a = b then 1 else 0) := by simp
        _ = ∑ a, c a * ∑ j, (A.loc p).ιE (v a j) *
              (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) := by simp only [key]
        _ = ∑ j, (∑ a, c a • A.bc p (v a)) j *
              (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hbc, Finset.mul_sum,
            Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
        _ = 0 := by rw [hc]; simp
    · intro hv
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro c hc a
      have h := hv (fun a => (A.loc p).ιE (c a)) (by
        funext j
        have hj := congrFun hc j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hbc] at hj ⊢

        rw [← map_zero (A.loc p).ιE, ← hj, map_sum]
        simp [map_mul])
      exact (map_eq_zero_iff _ (A.loc p).ιE.injective).mp (h a)

end GlobalTheory.HL.RatExt
end

section

open NumberField GlobalTheory.HL
open scoped Classical

noncomputable section

namespace GlobalTheory.HL.TraceConjugationCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

def stMat (G : GFrames A r k) (x : G.GLV) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  if h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a then h.choose else 0

theorem stMat_spec (G : GFrames A r k) (x : G.GLV)
    (h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) :
    ∀ b, x (G.f' b) = ∑ a, stMat G x a b • G.f' a := by
  unfold stMat; rw [dite_eq_left h]; exact h.choose_spec

end GlobalTheory.HL.TraceConjugationCover

end
end

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (k n : ℕ), 2 * k + 1 ≤ 2 * n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.quad_count | exact GlobalTheory.GramCount.quad_count | (intros; apply GlobalTheory.GramCount.quad_count <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ act : MulAction P.UW0 (LocNG.Datum P), (∀ (g : P.UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧ ∀ d (g : P.UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
  first | exact @GlobalTheory.InnerDatumAct.exists_mulAction | exact GlobalTheory.InnerDatumAct.exists_mulAction | (intros; apply GlobalTheory.InnerDatumAct.exists_mulAction <;> assumption)
end

section

open Formalism.MainNotions.S


theorem _root_.GlobalTheory.T.nonGenericDatum_lattice_eq_perpQuotientImage_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := by
  first | exact @GlobalTheory.InnerRead.datum_eq_Lset | exact GlobalTheory.InnerRead.datum_eq_Lset | (intros; apply GlobalTheory.InnerRead.datum_eq_Lset <;> assumption)
end

section

open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.term_families_congr_mod_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) {r : ℕ} (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r) (sg : Loc.SplitG M.L), M.split = some sg → LocNG.IsTermOver P d τ → ∀ (y x : Fin (r + 1) → V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = B a a) → (∀ a, B a a ∈ M.L.O ∧ ∃ t ∈ M.L.O, t * B a a = 1) → (∀ b, y b = ∑ a, B a b • P.A.f a) → (∀ b, x b = ∑ a, B' a b • P.B.f a) → (∀ a, y a ∈ τ.abelian₂) → (∀ b, x b ∈ τ.abelian₂) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ M.L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, x b - ∑ a, ξ a b • y a ∈ H.smulLat (algebraMap F E (sg.q : F)) τ.abelian₂ := by
  first | exact @GlobalTheory.loc_cong_unitri | exact GlobalTheory.loc_cong_unitri | (intros; apply GlobalTheory.loc_cong_unitri <;> assumption)
end

section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow' : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ s : ℝ, 1 < s → (classNumber K : ℝ) * Units.regulator K ≤ Real.sqrt |(discr K : ℝ)| ^ s * (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow | exact GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow | (intros; apply GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow <;> assumption)
end
