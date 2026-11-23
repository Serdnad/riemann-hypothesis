module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle270
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem split_by_target {W Y Z : Type} [AddCommGroup W] (A B : AddSubgroup W) (M : W → Prop) (m : W → Z)
    (f : Y → Z) (hf : Function.Injective f) (hB : Fine A (ind M) B)
    (hm : ∀ w, M w → ∀ b ∈ B, m (w + b) = m w) (hex : ∀ w, M w → ∃ y, f y = m w) (c : ℝ) (hc : 0 ≤ c) :
    {y | ∃ w, M w ∧ f y = m w}.Finite ∧ (∀ y, Nice A (ind fun w => M w ∧ f y = m w)) ∧
    {y | c * (cint A (ind fun w => M w ∧ f y = m w)).re ≠ 0}.Finite ∧
    (∀ y, 0 ≤ c * (cint A (ind fun w => M w ∧ f y = m w)).re) ∧
    ∀ (P : Y → Prop) (g : Y → ℂ) (G : W → ℂ), (∀ w y, (M w ∧ f y = m w) → G w = if P y then g y else 0) →
      (∀ w, ¬ M w → G w = 0) → Nice A G ∧
      ∑ᶠ y : {y // P y}, ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y =
        (c : ℂ) * cint A G := by
  obtain ⟨hBA, hidx, hinv, hfin⟩ := hB
  have hsupp : Function.support (ind M) = {w | M w} := by
    ext w
    simp [ind]
  have hMinv : ∀ w, ∀ b ∈ B, (M (w + b) ↔ M w) := by
    intro w b hb
    have h := hinv w b hb
    simp only [ind] at h
    by_cases h1 : M (w + b) <;> by_cases h2 : M w <;> simp [h1, h2] at h ⊢
  have hTfin : {y | ∃ w, M w ∧ f y = m w}.Finite := by
    let g : Y → W ⧸ B := fun y =>
      if h : ∃ w, M w ∧ f y = m w then (QuotientAddGroup.mk h.choose : W ⧸ B) else 0
    refine Set.Finite.of_finite_image (f := g) (hfin.subset ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : ∃ w, M w ∧ f y = m w := hy
      refine ⟨hy'.choose, ?_, ?_⟩
      · rw [hsupp]
        exact hy'.choose_spec.1
      · simp only [g, dif_pos hy']
    · intro y1 hy1 y2 hy2 heq
      have hy1' : ∃ w, M w ∧ f y1 = m w := hy1
      have hy2' : ∃ w, M w ∧ f y2 = m w := hy2
      simp only [g, dif_pos hy1', dif_pos hy2'] at heq
      apply hf
      rw [hy1'.choose_spec.2, hy2'.choose_spec.2]
      have hb : -hy1'.choose + hy2'.choose ∈ B := QuotientAddGroup.eq.mp heq
      have h := hm _ hy1'.choose_spec.1 _ hb
      rw [add_neg_cancel_left] at h
      exact h.symm
  have hFine : ∀ y, Fine A (ind fun w => M w ∧ f y = m w) B := by
    intro y
    refine ⟨hBA, hidx, ?_, hfin.subset ?_⟩
    · intro w b hb
      simp only [ind]
      by_cases hw : M w
      · have h1 : M (w + b) := (hMinv w b hb).mpr hw
        simp only [h1, hw, true_and, hm w hw b hb]
      · have h1 : ¬ M (w + b) := fun h => hw ((hMinv w b hb).mp h)
        simp only [h1, hw, false_and]
    · apply Set.image_mono
      intro w hw
      rw [hsupp]
      by_contra hM
      refine (Function.mem_support.mp hw) ?_
      simp only [ind]
      rw [if_neg (fun h => hM h.1)]
  have hnice : ∀ y, Nice A (ind fun w => M w ∧ f y = m w) := fun y => ⟨B, hFine y⟩
  have hzero : ∀ y, y ∉ {y | ∃ w, M w ∧ f y = m w} → cint A (ind fun w => M w ∧ f y = m w) = 0 := by
    intro y hy
    have h : (ind fun w => M w ∧ f y = m w) = fun _ => 0 := by
      funext w
      simp only [ind]
      rw [if_neg]
      exact fun h => hy ⟨w, h⟩
    rw [h]
    simp [cint]
  obtain ⟨-, hI2, hI3, hI4⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A
  refine ⟨hTfin, hnice, hTfin.subset ?_, fun y => mul_nonneg hc (hI3 _).1, ?_⟩
  · intro y hy
    change c * _ ≠ 0 at hy
    by_contra hyT
    rw [hzero y hyT] at hy
    simp at hy
  · intro P g G hG hG0
    have hGeq : G = fun w => ∑ y ∈ hTfin.toFinset.filter P, g y * ind (fun w => M w ∧ f y = m w) w := by
      funext w
      by_cases hw : M w
      · obtain ⟨y0, hy0⟩ := hex w hw
        have hy0T : y0 ∈ hTfin.toFinset := by
          rw [Set.Finite.mem_toFinset]
          exact ⟨w, hw, hy0⟩
        rw [hG w y0 ⟨hw, hy0⟩]
        have hother : ∀ y, y ≠ y0 → ind (fun w => M w ∧ f y = m w) w = 0 := by
          intro y hne
          simp only [ind]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (hf (h.trans hy0.symm))
        by_cases hP : P y0
        · rw [if_pos hP, Finset.sum_eq_single y0]
          · simp only [ind]
            rw [if_pos ⟨hw, hy0⟩, mul_one]
          · intro y _ hne
            rw [hother y hne, mul_zero]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨hy0T, hP⟩) h
        · rw [if_neg hP, Finset.sum_eq_zero]
          intro y hy
          have hne : y ≠ y0 := by
            rintro rfl
            exact hP (Finset.mem_filter.mp hy).2
          rw [hother y hne, mul_zero]
      · rw [hG0 w hw, Finset.sum_eq_zero]
        intro y _
        simp only [ind]
        rw [if_neg (fun h => hw h.1), mul_zero]
    have hcG : Nice A G ∧ cint A G =
        ∑ y ∈ hTfin.toFinset.filter P, g y * cint A (ind fun w => M w ∧ f y = m w) := by
      obtain ⟨hn, hs⟩ := hI4 Y (hTfin.toFinset.filter P)
        (fun y w => g y * ind (fun w => M w ∧ f y = m w) w) (fun y _ => (hI2 (g y) _ (hnice y)).1)
      rw [hGeq]
      exact ⟨hn, hs.trans (Finset.sum_congr rfl fun y _ => (hI2 (g y) _ (hnice y)).2)⟩
    refine ⟨hcG.1, ?_⟩
    rw [hcG.2]
    have hsub : Function.support (fun y : {y // P y} =>
        ((c * (cint A (ind fun w => M w ∧ f y.1 = m w)).re : ℝ) : ℂ) * g y.1) ⊆
        ↑(hTfin.toFinset.subtype P) := by
      intro y hy
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset]
      by_contra hyT
      refine (Function.mem_support.mp hy) ?_
      rw [hzero y.1 hyT]
      simp
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine (Finset.sum_subtype_eq_sum_filter
      (fun y => ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have him := (hI3 (fun w => M w ∧ f y = m w)).2
    have hre : ((cint A (ind fun w => M w ∧ f y = m w)).re : ℂ) = cint A (ind fun w => M w ∧ f y = m w) :=
      Complex.ext (by simp) (by simp [him])
    push_cast
    rw [hre]
    ring

theorem moves_split_by_target : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → {Λ₁ : Submodule L.O S.V | ∃ w, S.MvTo (j + 1) d Λ Λ₁ w}.Finite ∧ (∀ Λ₁, Nice (S.refA (j + 1) Λ) (ind (S.MvTo (j + 1) d Λ Λ₁))) ∧ {Λ₁ | S.kern β (j + 1) βJ d Λ Λ₁ ≠ 0}.Finite ∧ (∀ Λ₁, 0 ≤ S.kern β (j + 1) βJ d Λ Λ₁) ∧ ∀ (P : Submodule L.O S.V → Prop) (g : Submodule L.O S.V → ℂ) (G : S.MW → ℂ), (∀ w Λ₁, S.MvTo (j + 1) d Λ Λ₁ w → G w = if P Λ₁ then g Λ₁ else 0) → (∀ w, ¬ S.Mv (j + 1) d Λ w → G w = 0) → Nice (S.refA (j + 1) Λ) G ∧ ∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * g y = (S.cK β βJ : ℂ) * cint (S.refA (j + 1) Λ) G := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF
  obtain ⟨B, hB, hinv⟩ := GlobalTheory.T.exists_fineSubgroup_moves_at_lattice L r k S j β βJ d Λ hT hFF
  have hex : ∀ w, S.Mv (j + 1) d Λ w →
      ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ w.1.1 w.2.1 (S.sOf w) := by
    intro w hw
    obtain ⟨Λ₁, h1, -⟩ := GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hFF w.1.1 w.1.2 w.2.1 (S.sOf w) hw
    exact ⟨Λ₁, h1⟩
  have hc : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  exact split_by_target (S.refA (j + 1) Λ) B (S.Mv (j + 1) d Λ)
    (fun w => S.moved Λ w.1.1 w.2.1 (S.sOf w)) (fun Λ₁ : Submodule L.O S.V => (Λ₁ : Set S.V))
    SetLike.coe_injective hB (fun w hw b hb => (hinv w hw b hb).1) hex (S.cK β βJ) hc

end GlobalTheory.HL
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernSym

def flipMv (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] :
    A × B × C ≃+ A × B × C where
  toFun w := (w.1, -w.2)
  invFun w := (w.1, -w.2)
  left_inv w := by simp
  right_inv w := by simp
  map_add' w w' := by
    ext <;> simp [add_comm]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem refA_map_flip (J : ℕ) (Λ : Submodule L.O S.V) :
    (S.refA J Λ).map (flipMv (S.V × S.V) S.V E).toAddMonoidHom = S.refA J Λ := by
  have key : ∀ w : S.MW, w ∈ S.refA J Λ → ((w.1, -w.2) : S.MW) ∈ S.refA J Λ := by
    intro w hw
    rw [Frames.refA, AddSubgroup.mem_prod] at hw ⊢
    exact ⟨hw.1, neg_mem hw.2⟩
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact key v hv
  · intro hw
    refine ⟨(w.1, -w.2), key w hw, ?_⟩
    show ((w.1, - -w.2) : S.MW) = w
    simp

theorem sOf_flip [CharZero F] (w : S.MW) (hs : S.sOf w + L.cj (S.sOf w) = S.h w.2.1 w.2.1) :
    S.sOf (w.1, -w.2) = L.cj (S.sOf w) := by
  have h1 : S.h (-w.2.1) (-w.2.1) = S.h w.2.1 w.2.1 := by
    simp [Frames.h, hf]
  have h2 : algebraMap F E 2⁻¹ + algebraMap F E 2⁻¹ = 1 := by
    rw [← map_add (f := _), ← map_one (algebraMap F E)]
    congr 1
    norm_num
  have h3 : L.cj (S.sOf w) = S.h w.2.1 w.2.1 - S.sOf w := by
    rw [← hs]; ring
  rw [h3]
  show algebraMap F E 2⁻¹ * S.h (-w.2.1) (-w.2.1) + -w.2.2 = _
  rw [h1, Frames.sOf]
  linear_combination (S.h w.2.1 w.2.1) * h2
end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mvTo_flip (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ Λ' : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hF : S.InFF β (j + 1) βJ d Λ) (hF' : S.InFF β (j + 1) βJ d Λ')
    (w : S.MW) (hw : S.MvTo (j + 1) d Λ Λ' w) : S.MvTo (j + 1) d Λ' Λ (w.1, -w.2) := by
  obtain ⟨hm, he⟩ := hw
  obtain ⟨Λ₁, h1, -, h3, h4, -⟩ :=
    GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hF w.1.1 w.1.2 w.2.1 (S.sOf w) hm
  have hΛ : Λ₁ = Λ' := SetLike.coe_injective (h1.trans he.symm)
  subst hΛ
  have hs := sOf_flip S w hm.2.2.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · show S.IsMove (j + 1) d Λ₁ w.1.1 w.1.2 (-w.2.1) (S.sOf (w.1, -w.2))
    rw [hs]
    exact h4 hF'
  · show (Λ : Set S.V) = S.moved Λ₁ w.1.1 (-w.2.1) (S.sOf (w.1, -w.2))
    rw [hs]
    exact h3.symm
end

theorem kern_symm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → S.kern β (j + 1) βJ d Λ Λ' = S.kern β (j + 1) βJ d Λ' Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF Λ' hT' hF'
  obtain ⟨hr, hne⟩ := GlobalTheory.T.hermitianFrames_reference_subgroups_relIndex_eq L r k S j β βJ d Λ hT hF Λ' hT' hF'
  obtain ⟨hmap, hchg⟩ := @GlobalTheory.T.indexMeasureIntegral_transport_and_change S.MW _ S.MW _
  have e1 := (hmap (flipMv (S.V × S.V) S.V E) (S.refA (j + 1) Λ)
    (ind (S.MvTo (j + 1) d Λ' Λ))).2
  rw [refA_map_flip] at e1
  have e2 : (fun w => ind (S.MvTo (j + 1) d Λ' Λ) (flipMv (S.V × S.V) S.V E w)) =
      ind (S.MvTo (j + 1) d Λ Λ') := by
    funext w
    have hiff : S.MvTo (j + 1) d Λ' Λ (flipMv (S.V × S.V) S.V E w) ↔ S.MvTo (j + 1) d Λ Λ' w := by
      constructor
      · intro h
        have h' := mvTo_flip S j β βJ d Λ' Λ hT' hF' hF _ h
        have hw : (((flipMv (S.V × S.V) S.V E w).1, -(flipMv (S.V × S.V) S.V E w).2) : S.MW) = w := by
          show ((w.1, - -w.2) : S.MW) = w
          simp
        rwa [hw] at h'
      · intro h
        exact mvTo_flip S j β βJ d Λ Λ' hT hF hF' w h
    simp only [ind, hiff]
  rw [e2] at e1
  have e3 := (hchg (S.refA (j + 1) Λ) (S.refA (j + 1) Λ') (ind (S.MvTo (j + 1) d Λ' Λ)) hne
    (hr ▸ hne)).2
  rw [← hr] at e3
  have e4 := mul_right_cancel₀ (Nat.cast_ne_zero.mpr hne) e3
  unfold Frames.kern
  rw [e4, e1]

end GlobalTheory.HL.KernSym
end
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.CyclicQuot

theorem match_of_coprime {A K ι : Type} [CommRing A] [CommRing K] (p : A →+* K) (H : AddSubgroup (ι → A))
    (T k : ℤ) (hc : IsCoprime k T) (y z : ι → A) (hy : T • y ∈ H) (hz : z ∈ H)
    (h : ∀ b, p (z b) = (k : K) * p (y b)) : ∃ z' ∈ H, ∀ b, p (z' b) = p (y b) := by
  obtain ⟨u, w, huw⟩ := hc
  refine ⟨u • z + w • (T • y), H.add_mem (H.zsmul_mem hz u) (H.zsmul_mem hy w), fun b => ?_⟩
  have h' : (u : K) * k + w * T = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huw
  simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_zsmul, h b]
  simp only [zsmul_eq_mul]
  linear_combination (p (y b)) * h'

theorem coprime_sub {T : ℕ} (hT : T.Prime) (i j : Fin T) (hij : i ≠ j) :
    IsCoprime (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) (T : ℤ) := by
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.mp hT
  refine (hp.irreducible.coprime_iff_not_dvd.mpr fun hd => hij ?_).symm
  have hi := i.2
  have hj := j.2
  have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  exact Fin.ext (by omega)

theorem cyclic_of_components {A K ι : Type} [CommRing A] [CommRing K] (sp : A ≃+* K × K) (O : Subring A)
    (e : A) (he : e ∈ O) (hsp : sp e = (1, 0)) (M D : Submodule O (ι → A)) (T : ℕ) (hT : T.Prime)
    (hTD : ∀ y ∈ D, (T : ℤ) • y ∈ M)
    (y₁ : ι → A) (hy₁ : y₁ ∈ D) (h₁ : ¬ ∃ z ∈ M, ∀ b, (sp (z b)).1 = (sp (y₁ b)).1)
    (y₂ : ι → A) (hy₂ : y₂ ∈ D) (h₂ : ¬ ∃ z ∈ M, ∀ b, (sp (z b)).2 = (sp (y₂ b)).2)
    (hidx : M.toAddSubgroup.relIndex D.toAddSubgroup = T ^ 2) :
    ∃ d ∈ D, ∀ x ∈ D, ∃ a ∈ O, x - a • d ∈ M := by
  classical
  let eO : O := ⟨e, he⟩
  let d : ι → A := eO • y₁ + (1 - eO) • y₂
  have hd : d ∈ D := D.add_mem (D.smul_mem _ hy₁) (D.smul_mem _ hy₂)
  have hdb : ∀ b, sp (d b) = ((sp (y₁ b)).1, (sp (y₂ b)).2) := by
    intro b
    have : d b = e * y₁ b + (1 - e) * y₂ b := rfl
    rw [this, map_add (f := _), map_mul, map_mul, map_sub, map_one, hsp]
    ext <;> simp
  let a : Fin T × Fin T → O := fun ij => ((ij.1 : ℕ) : O) * eO + ((ij.2 : ℕ) : O) * (1 - eO)
  have ha : ∀ ij, sp (a ij : A) = (((ij.1 : ℕ) : K), ((ij.2 : ℕ) : K)) := by
    intro ij
    have : (a ij : A) = ((ij.1 : ℕ) : A) * e + ((ij.2 : ℕ) : A) * (1 - e) := by
      simp [a, eO]
    rw [this, map_add (f := _), map_mul, map_mul, map_sub, map_one, hsp, map_natCast, map_natCast]
    ext <;> simp
  let φ : Fin T × Fin T → D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup :=
    fun ij => QuotientAddGroup.mk ⟨a ij • d, D.smul_mem _ hd⟩
  have hcard : Nat.card (D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup) = T ^ 2 := hidx
  have hfin : Finite (D.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf D.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hT.ne_zero)
  have hinj : Function.Injective φ := by
    intro s t hst
    have hm : -(a s • d) + a t • d ∈ M := QuotientAddGroup.eq.mp hst
    have hc : ∀ b, sp ((-(a s • d) + a t • d) b) =
        ((((t.1 : ℕ) : K) - ((s.1 : ℕ) : K)) * (sp (y₁ b)).1,
          (((t.2 : ℕ) : K) - ((s.2 : ℕ) : K)) * (sp (y₂ b)).2) := by
      intro b
      have : (-(a s • d) + a t • d) b = -((a s : A) * d b) + (a t : A) * d b := rfl
      rw [this, map_add (f := _), map_neg, map_mul, map_mul, ha, ha, hdb]
      ext <;> simp <;> ring
    by_contra hne
    by_cases h1 : t.1 = s.1
    · have h2 : t.2 ≠ s.2 := fun h2 => hne (Prod.ext h1.symm h2.symm)
      refine h₂ (match_of_coprime ((RingHom.snd K K).comp sp.toRingHom) M.toAddSubgroup T _
        (coprime_sub hT _ _ h2) y₂ _ (hTD _ hy₂) hm fun b => ?_)
      have := congrArg Prod.snd (hc b)
      push_cast
      exact this
    · refine h₁ (match_of_coprime ((RingHom.fst K K).comp sp.toRingHom) M.toAddSubgroup T _
        (coprime_sub hT _ _ h1) y₁ _ (hTD _ hy₁) hm fun b => ?_)
      have := congrArg Prod.fst (hc b)
      push_cast
      exact this
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by rw [hcard]; simp [sq])
  refine ⟨d, hd, fun x hx => ?_⟩
  obtain ⟨s, hs⟩ := hbij.2 (QuotientAddGroup.mk ⟨x, hx⟩)
  have hm : -(a s • d) + x ∈ M := QuotientAddGroup.eq.mp hs
  refine ⟨a s, (a s).2, ?_⟩
  rw [sub_eq_neg_add]
  exact hm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idem [StarRing E] (cm : CMData F E) (v : HeightOneSpectrum (𝓞 F))
    (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h1 : ∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x))
    (h2 : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ e ∈ intV E v, sp e = (1, 0) := by
  have hH : IsHerm (cm.sig : E →+* E) (1 : Matrix (Fin 1) (Fin 1) E) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [cT]
  let L : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have hL : ∀ x ∈ L, ∀ b, x b ∈ intOE E := by
    intro x hx b
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨c, by simp [Algebra.smul_def]⟩
  have hloc : ∀ y ∈ loc v L, ∀ b, y b ∈ intV E v := by
    intro y hy b
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact Subring.subset_closure (Or.inl ⟨⟨x b, hL x hx b⟩, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact mul_mem c.2 hx
  have hone : (fun _ => 1 : Fin 1 → E ⊗[F] v.adicCompletion F) ∈ loc v L :=
    Submodule.subset_span ⟨fun _ => 1, Submodule.subset_span rfl, by funext i; simp⟩
  have hmem := ((GlobalTheory.T.split_place_lattice_components F E cm 1 1 hH (by simp) v sp h1 h2).1 L (fun _ => sp.symm (1, 0))).mpr
    ⟨⟨_, hone, fun b => by simp⟩, ⟨0, zero_mem _, fun b => by simp⟩⟩
  exact ⟨sp.symm (1, 0), hloc _ hmem 0, by simp⟩

theorem smul_mem_loc {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (h : ∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L)
    (v : HeightOneSpectrum (𝓞 F)) : ∀ y ∈ loc v (dualL σ J L), (T : ℤ) • y ∈ loc v L := by
  have h0 : ∀ x ∈ dualL σ J L, (T : ℤ) • x ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have := h x hx
      rwa [Nat.cast_smul_eq_nsmul, ← natCast_zsmul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact L.smul_mem c hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h0 x hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, map_zsmul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem local_dual_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 → ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT _ _ hL v hv sp h1 h2 hiff hidx
  obtain ⟨e, he, hsp⟩ := exists_idem cm v sp h1 h2
  obtain ⟨x, hx, hxn⟩ := hL.2.2.2.2 v hv
  have crit := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v sp h1 h2).1 L x
  have n1 : ¬ ∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1 :=
    fun h => hxn (crit.mpr ⟨h x hx, hiff.mp h x hx⟩)
  have n2 : ¬ ∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2 :=
    fun h => n1 (hiff.mpr h)
  obtain ⟨y₁, hy₁⟩ := not_forall.mp n1
  obtain ⟨y₂, hy₂⟩ := not_forall.mp n2
  obtain ⟨hy₁, h₁⟩ := Classical.not_imp.mp hy₁
  obtain ⟨hy₂, h₂⟩ := Classical.not_imp.mp hy₂
  exact cyclic_of_components sp (intV E v) e he hsp _ _ T hT
    (smul_mem_loc cm.sig J T L hL.2.2.1 v) y₁ hy₁ h₁ y₂ hy₂ h₂ hidx

end GlobalTheory.St.G.CyclicQuot

end
end
