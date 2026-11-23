module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle043
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle076
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003

@[expose] public section

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernInv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def mvEquiv (h : S.GLV) : S.MW ≃+ S.MW :=
  (h.toAddEquiv.prodCongr h.toAddEquiv).prodCongr (h.toAddEquiv.prodCongr (AddEquiv.refl E))

end GlobalTheory.HL.KernInv

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma form_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (x y : S.V) :
    S.h (h x) (h y) = S.h x y := by
  unfold _root_.GlobalTheory.HL.Frames.St at hh
  have hN := (Subgroup.mem_inf.mp hh).1
  unfold _root_.GlobalTheory.HL.Frames.N _root_.GlobalTheory.HL.Frames.Nof at hN
  have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hN).1).1
  unfold _root_.GlobalTheory.HL.isomG at hI
  unfold _root_.GlobalTheory.HL.Frames.h
  exact hI x y

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma addSubgroup_eq_map_of_apply_mem_iff {M : Type} [AddCommGroup M] (e : M ≃+ M)
    (A B : AddSubgroup M) (hAB : ∀ w, e w ∈ B ↔ w ∈ A) : B = A.map e.toAddMonoidHom := by
  ext w
  constructor
  · intro hw
    exact ⟨e.symm w, (hAB _).mp (by simpa using hw), by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact (hAB w).mpr hw

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma mem_refB_iff (J : ℕ) (Λ : Submodule L.O S.V) (a b : S.V) :
    (a, b) ∈ S.refB J Λ ↔ a ∈ S.spanTo S.f J ∧ b ∈ S.spanTo S.f' J ∧
      ∃ y ∈ Λ, a + b = (algebraMap F E) S.th • y := by
  unfold _root_.GlobalTheory.HL.Frames.refB
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_comap, AddSubgroup.mem_map,
    Submodule.mem_toAddSubgroup, and_assoc]
  exact Iff.rfl.and (Iff.rfl.and (exists_congr fun _ => Iff.rfl.and eq_comm))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_sup_iff_of_apply_mem_iff (h : S.GLV) (A B : Submodule E S.V)
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (v : S.V) :
    h v ∈ A ⊔ B ↔ v ∈ A ⊔ B := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨h.symm y, (hA _).mp (by simpa using hy), h.symm z, (hB _).mp (by simpa using hz), ?_⟩
    rw [← map_add (f := _), hyz, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨h y, (hA y).mpr hy, h z, (hB z).mpr hz, (map_add h y z).symm⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_perp_Ysp_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (J : ℕ) (u : S.V) :
    h u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) ↔
      u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  have hY : ∀ v, h v ∈ S.Ysp J ↔ v ∈ S.Ysp J := by
    unfold _root_.GlobalTheory.HL.Frames.Ysp
    exact apply_mem_sup_iff_of_apply_mem_iff S h _ _
      (_root_.GlobalTheory.FrameAct.spanTo_iff S h hh J)
      (_root_.GlobalTheory.FrameAct.spanTo_iff' S h hh J)
  unfold _root_.GlobalTheory.HL.perp
  show (∀ y ∈ S.Ysp J, _ = 0) ↔ (∀ y ∈ S.Ysp J, _ = 0)
  constructor
  · intro H y hy
    rw [← hform]
    exact H _ ((hY y).mpr hy)
  · intro H y hy
    have hyy : h (h.symm y) = y := h.apply_symm_apply y
    rw [← hyy, hform]
    exact H _ ((hY _).mp (hyy.symm ▸ hy))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma coe_smul_submodule_eq_iff_of_apply_mem_iff (h : S.GLV) (Λ₁ : Submodule L.O S.V) (P Q : Set S.V)
    (hPQ : ∀ v, h v ∈ Q ↔ v ∈ P) :
    ((h • Λ₁ : Submodule L.O S.V) : Set S.V) = Q ↔ (Λ₁ : Set S.V) = P := by
  simp only [Set.ext_iff, SetLike.mem_coe]
  rw [h.surjective.forall]
  simp only [_root_.GlobalTheory.FrameAct.mem_smul_iff, hPQ]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma eich_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (a b v : S.V) (c : E) :
    _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) = h (_root_.GlobalTheory.HL.eich L S.Hm a b c v) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  unfold _root_.GlobalTheory.HL.eich
  rw [hform, hform]
  simp only [map_add (f := _), map_sub, map_smul]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_moved_smul_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (Λ : Submodule L.O S.V) (a b v : S.V) (c : E) :
    h v ∈ S.moved (h • Λ) (h a) (h b) c ↔ v ∈ S.moved Λ a b c := by
  unfold _root_.GlobalTheory.HL.Frames.moved
  show _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) ∈ h • Λ ↔
    _root_.GlobalTheory.HL.eich L S.Hm a b c v ∈ Λ
  rw [eich_apply_apply_of_mem_St S hh, _root_.GlobalTheory.FrameAct.mem_smul_iff]


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
theorem _root_.GlobalTheory.HL.kern_smul_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (β J βJ : ℕ) (Λ₁ : Submodule L.O S.V), ∀ h ∈ S.St, S.kern β J βJ d (h • Λ) (h • Λ₁) = S.kern β J βJ d Λ Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT β J βJ Λ₁ h hh
  have hform := form_apply_apply_of_mem_St S hh
  have hmove := (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.2.2.2.2
  have hA : S.refA J (h • Λ) =
      (S.refA J Λ).map (_root_.GlobalTheory.HL.KernInv.mvEquiv S h).toAddMonoidHom := by
    refine addSubgroup_eq_map_of_apply_mem_iff _ _ _ ?_
    rintro ⟨⟨a, b⟩, u, t⟩
    unfold _root_.GlobalTheory.HL.Frames.refA
    simp only [AddSubgroup.mem_prod]
    change (h a, h b) ∈ S.refB J (h • Λ) ∧ h u ∈ S.refU J (h • Λ) ∧ t ∈ S.refT ↔
      (a, b) ∈ S.refB J Λ ∧ u ∈ S.refU J Λ ∧ t ∈ S.refT
    rw [mem_refB_iff, mem_refB_iff, ← map_add (f := _),
      _root_.GlobalTheory.FrameAct.spanTo_iff S h hh,
      _root_.GlobalTheory.FrameAct.spanTo_iff' S h hh]
    have hth := _root_.GlobalTheory.FrameAct.inTh_iff S h Λ (a + b)
    unfold _root_.GlobalTheory.HL.Frames.InTh at hth
    rw [hth]
    unfold _root_.GlobalTheory.HL.Frames.refU
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup,
      _root_.GlobalTheory.FrameAct.mem_smul_iff, apply_mem_perp_Ysp_iff_of_mem_St S hh]
  have hP : ∀ w, _root_.GlobalTheory.IdxInt.ind (S.MvTo J d (h • Λ) (h • Λ₁))
      (_root_.GlobalTheory.HL.KernInv.mvEquiv S h w) = _root_.GlobalTheory.IdxInt.ind (S.MvTo J d Λ Λ₁) w := by
    rintro ⟨⟨a, b⟩, u, t⟩
    have hs : S.sOf ((h a, h b), (h u, t)) = S.sOf ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.sOf
      simp only [hform]
    have hiff : S.MvTo J d (h • Λ) (h • Λ₁) ((h a, h b), (h u, t)) ↔
        S.MvTo J d Λ Λ₁ ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.MvTo _root_.GlobalTheory.HL.Frames.Mv
      change S.IsMove J d (h • Λ) (h a) (h b) (h u) (S.sOf ((h a, h b), (h u, t))) ∧
          ((h • Λ₁ : Submodule L.O S.V) : Set S.V) =
            S.moved (h • Λ) (h a) (h u) (S.sOf ((h a, h b), (h u, t))) ↔
        S.IsMove J d Λ a b u (S.sOf ((a, b), (u, t))) ∧
          (Λ₁ : Set S.V) = S.moved Λ a u (S.sOf ((a, b), (u, t)))
      rw [hs]
      exact and_congr (hmove J a b u _).symm
        (coe_smul_submodule_eq_iff_of_apply_mem_iff S h Λ₁ _ _ fun v => apply_mem_moved_smul_iff_of_mem_St S hh Λ a u v _)
    unfold _root_.GlobalTheory.IdxInt.ind
    exact if_congr hiff rfl rfl
  unfold _root_.GlobalTheory.HL.Frames.kern
  rw [hA, (_root_.GlobalTheory.IdxInt.Transport.cint_map_and_change.1 _ _ _).2]
  simp only [hP]

end GlobalTheory.HL
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.FrMap

theorem hform_eq_dot {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) : hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J M : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) : hform s J (M *ᵥ x) (M *ᵥ y) = hform s (cT s M * J * M) x y := by
  rw [hform_eq_dot, hform_eq_dot]
  have h1 : (fun i => s ((M *ᵥ x) i)) = (M.map s) *ᵥ (fun i => s (x i)) := by
    funext i; simp [mulVec, dotProduct, map_sum]
  rw [h1, cT, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm, dotProduct_mulVec,
    dotProduct_comm]

theorem inModL_map {A : Type} [CommRing A] {O : Subring A} {n : ℕ} {Λ Λ' : Submodule O (Fin n → A)} (m : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : ∀ z ∈ Λ, P *ᵥ z ∈ Λ') {S S' : Set (Fin n → A)}
    (hS : ∀ s ∈ S, P *ᵥ s ∈ S') {x : Fin n → A} (hx : InModL Λ m S x) : InModL Λ' m S' (P *ᵥ x) := by
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  let f : (Fin n → A) →ₗ[O] (Fin n → A) := (Matrix.mulVecLin P).restrictScalars O
  refine ⟨P *ᵥ s, ?_, P *ᵥ z, hP z hz, by rw [mulVec_add, mulVec_smul]⟩
  have : f s ∈ Submodule.span O (f '' S) := by
    rw [← Submodule.map_span]; exact Submodule.mem_map_of_mem hs
  exact Submodule.span_mono (by rintro _ ⟨t, ht, rfl⟩; exact hS t ht) this

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) (h : UPts σ J (Ad F)), (∀ x, (h⁻¹).1.1 *ᵥ x ∈ Λ' ↔ x ∈ Λ) → ∀ Fr : AdFrame σ J Λ g k, ∃ Fr' : AdFrame σ J Λ' g k, ∀ y : UPts σ J (Ad F), (Fr.InK y.1 ↔ Fr'.InK (h⁻¹ * y * h : UPts σ J (Ad F)).1) ∧ Fr.chi y.1 = Fr'.chi (h⁻¹ * y * h : UPts σ J (Ad F)).1 := by
  intro F E _ _ _ _ _ n σ J Λ Λ' g k h hΛ Fr
  set M : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := h.1.1 with hM
  set Mi : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := (h⁻¹).1.1 with hMi
  have hMMi : M * Mi = 1 := by
    rw [hM, hMi]; show (h.1 * h.1⁻¹).val = 1; rw [mul_inv_cancel]; rfl
  have hMiM : Mi * M = 1 := by
    rw [hM, hMi]; show (h.1⁻¹ * h.1).val = 1; rw [inv_mul_cancel]; rfl
  have hinvM : ∀ u v, hR σ J (Ad F) (M *ᵥ u) (M *ᵥ v) = hR σ J (Ad F) u v := by
    intro u v; unfold hR; rw [hform_mulVec]; congr 1; exact h.2
  have hinvMi : ∀ u v, hR σ J (Ad F) (Mi *ᵥ u) (Mi *ᵥ v) = hR σ J (Ad F) u v := by
    intro u v; unfold hR; rw [hform_mulVec]; congr 1; exact (h⁻¹).2
  have hΛ'' : ∀ x, x ∈ Λ' ↔ M *ᵥ x ∈ Λ := by
    intro x; rw [← hΛ (M *ᵥ x), mulVec_mulVec, hMiM, one_mulVec]
  have hMiΛ : ∀ z ∈ Λ, Mi *ᵥ z ∈ Λ' := fun z hz => (hΛ z).2 hz
  have hMΛ' : ∀ z ∈ Λ', M *ᵥ z ∈ Λ := fun z hz => (hΛ'' z).1 hz
  have hMMiv : ∀ v, M *ᵥ (Mi *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMMi, one_mulVec]
  have hMiMv : ∀ v, Mi *ᵥ (M *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMiM, one_mulVec]
  let Fr' : AdFrame σ J Λ' g k :=
    { eps := Fr.eps, eps_idem := Fr.eps_idem, eps_orth := Fr.eps_orth, eps_int := Fr.eps_int,
      eps_full := by
        intro y hy
        obtain ⟨z, hz, e⟩ := Fr.eps_full (M *ᵥ y) (hMΛ' y hy)
        refine ⟨Mi *ᵥ z, hMiΛ z hz, ?_⟩
        have := congrArg (Mi *ᵥ ·) e
        simp only [mulVec_smul, hMiMv] at this
        exact this
      b := fun i => Mi *ᵥ Fr.b i, bd := fun i => Mi *ᵥ Fr.bd i,
      b_mem := fun i => hMiΛ _ (Fr.b_mem i), bd_mem := fun i => hMiΛ _ (Fr.bd_mem i),
      b_eps := fun i => by
        show Mi *ᵥ Fr.b i = Fr.eps • (Mi *ᵥ Fr.b i)
        rw [← mulVec_smul, ← Fr.b_eps i]
      bd_eps := fun i => by
        show Mi *ᵥ Fr.bd i = sigR σ (Ad F) Fr.eps • (Mi *ᵥ Fr.bd i)
        rw [← mulVec_smul, ← Fr.bd_eps i]
      dual := fun i j => by
        show ∃ t ∈ OAd F E, hR σ J (Ad F) (Mi *ᵥ Fr.bd i) (Mi *ᵥ Fr.b j) - _ = _
        rw [hinvMi]; exact Fr.dual i j
      span := by
        intro y hy
        have := inModL_map g Mi hMiΛ (S' := Set.range (fun i => Mi *ᵥ Fr.b i) ∪ Set.range (fun i => Mi *ᵥ Fr.bd i))
          (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩])
          (Fr.span (M *ᵥ y) (hMΛ' y hy))
        rwa [hMiMv] at this
      psi := Fr.psi, psi_add := Fr.psi_add, psi_int := Fr.psi_int, psi_rat := Fr.psi_rat }
  refine ⟨Fr', fun y => ?_⟩
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := y.1.1 with hY
  have hconj : ((h⁻¹ * y * h : UPts σ J (Ad F)).1 : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F)) = Mi * Y * M := rfl
  have hc1 : M * (Mi * Y * M) = Y * M := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMMi, Matrix.one_mul]
  have hc3 : M * (Mi * Y * M - 1) = (Y - 1) * M := by
    rw [Matrix.mul_sub, hc1, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
  have hc4 : (Mi * Y * M - 1) * Mi = Mi * (Y - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hMMi, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hc5 : (Mi * Y * M) * Mi = Mi * Y := by
    rw [Matrix.mul_assoc, hMMi, Matrix.mul_one]
  constructor
  · unfold AdFrame.InK
    rw [hconj]
    have key1 : ∀ x, (Mi * Y * M) *ᵥ x ∈ Λ' ↔ Y *ᵥ (M *ᵥ x) ∈ Λ := by
      intro x; rw [hΛ'', mulVec_mulVec, hc1, ← mulVec_mulVec]
    have key2 : ∀ x, (Mi * Y * M - 1) *ᵥ x ∈ Λ' ↔ (Y - 1) *ᵥ (M *ᵥ x) ∈ Λ := by
      intro x; rw [hΛ'', mulVec_mulVec, hc3, ← mulVec_mulVec]
    have keyd : ∀ x, (∀ z ∈ Λ', hR σ J (Ad F) z x ∈ OAd F E) ↔ (∀ z ∈ Λ, hR σ J (Ad F) z (M *ᵥ x) ∈ OAd F E) := by
      intro x; constructor
      · intro H z hz; have := H _ (hMiΛ z hz); rwa [← hinvM, hMMiv] at this
      · intro H z hz; have := H _ (hMΛ' z hz); rwa [hinvM] at this
    refine and_congr ?_ (and_congr ?_ ?_)
    · show (∀ x, x ∈ Λ ↔ Y *ᵥ x ∈ Λ) ↔ (∀ x, x ∈ Λ' ↔ (Mi * Y * M) *ᵥ x ∈ Λ')
      constructor
      · intro H x; rw [hΛ'', key1]; exact H _
      · intro H x; have := H (Mi *ᵥ x); rwa [hΛ'', key1, hMMiv] at this
    · constructor
      · intro H x hx; rw [key2]; exact H _ ((keyd x).1 hx)
      · intro H x hx
        have := H (Mi *ᵥ x) ((keyd _).2 (by rwa [hMMiv]))
        rwa [key2, hMMiv] at this
    · refine forall_congr' fun i => ?_
      show _ ↔ InModL Λ' g ((fun j => Mi *ᵥ Fr.b j) '' {j | j.1 < i.1}) ((Mi * Y * M - 1) *ᵥ (Mi *ᵥ Fr.b i))
      rw [mulVec_mulVec, hc4, ← mulVec_mulVec]
      constructor
      · intro H
        exact inModL_map g Mi hMiΛ (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩) H
      · intro H
        have := inModL_map g M hMΛ' (S' := Fr.b '' {j | j.1 < i.1})
          (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, (hMMiv _).symm⟩) H
        rwa [hMMiv] at this
  · unfold AdFrame.chi
    rw [hconj]
    show Fr.psi _ = Fr.psi _
    congr 2
    unfold supSum
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · show hR σ J (Ad F) (Fr.bd i) (Y *ᵥ Fr.b _) = hR σ J (Ad F) (Mi *ᵥ Fr.bd i) ((Mi * Y * M) *ᵥ (Mi *ᵥ Fr.b _))
      rw [mulVec_mulVec, hc5, ← mulVec_mulVec, hinvMi]
    · rfl

end GlobalTheory.St.G.FrMap
end
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem selfDualAt_of_tLat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∉ v.asIdeal → SelfDualAt cm.sig J v L := by
  intro F E _ _ _ _ _ _ cm n J _ _ T f L hL v hv
  obtain ⟨⟨hfin, _⟩, hint, hT, _, _⟩ := hL
  exact self_dual_local F E n cm.sig J v L T hfin (fun x hx y hy => hint y hy x hx)
    (fun y hy => hT y hy) hv

end GlobalTheory.St.G
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem exists_adelic_of_finset {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hh : ∀ v, h v ∈ UPts σ J (v.adicCompletion F)) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ x ∈ UPts σ J (Ad F), (∀ v ∈ S, bc (prV (E := E) v) x = h v) ∧
      ∀ v ∉ S, bc (prV (E := E) v) x = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, fun v _ => map_one _⟩
  | insert w S hw ih =>
    obtain ⟨x, hx, h1, h2⟩ := ih
    have hne : ∀ v, v ≠ w →
        bc (prV (E := E) v) (Formalism.UG.P.afsplitU w (h w) x) = bc (prV (E := E) v) x := fun v hv =>
      Units.ext (Formalism.UG.P.afsplitC_prV_ne w v hv _ _)
    refine ⟨Formalism.UG.P.afsplitU w (h w) x, Formalism.UG.P.afsplitU_mem w σ J _ _ (hh w) hx, ?_, ?_⟩
    · intro v hv
      by_cases e : v = w
      · subst e
        exact Units.ext (Formalism.UG.P.afsplitC_prV v _ _)
      · rw [hne v e]
        exact h1 v ((Finset.mem_insert.1 hv).resolve_left e)
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [hne v hv.1]
      exact h2 v hv.2

theorem exists_adelic_of_finite_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F)), (∀ v, h v ∈ UPts σ J (v.adicCompletion F)) → {v | h v ≠ 1}.Finite → ∃ x ∈ UPts σ J (Ad F), ∀ v, bc (prV (E := E) v) x = h v := by
  intro F E _ _ _ _ _ n σ J h hh hf
  obtain ⟨x, hx, h1, h2⟩ := exists_adelic_of_finset σ J h hh hf.toFinset
  refine ⟨x, hx, fun v => ?_⟩
  by_cases hv : v ∈ hf.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    by_contra e
    exact hv (hf.mem_toFinset.2 fun e' => e e'.symm)

end GlobalTheory.St.G
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem Frames.stab_commensurable_invVol_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ Λ : Submodule L.O S.V, IsLat L Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 ∧ ∀ h ∈ S.H0, invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV (h • Λ)) = invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV Λ)) ∧ ∀ d Λ, S.IsTerm d Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV d) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV d).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  obtain ⟨x, hdet, hspan, hH0, hstd, -⟩ := GlobalTheory.T.exists_nondegenerate_tuple_complement_fixer L r k S
  set Λs : Submodule L.O S.V := Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V)) with hΛs
  have hK : S.complementReferenceCompactSubgroup = S.H0 ⊓ MulAction.stabilizer S.GLV Λs := rfl
  have comm : ∀ Λ Λ' : Submodule L.O S.V, IsLat L Λ → IsLat L Λ' →
      (S.H0 ⊓ MulAction.stabilizer S.GLV Λ').relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 :=
    fun Λ Λ' hΛ hΛ' => (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ' hΛ hΛ' S.H0).1
  have latPart : ∀ Λ : Submodule L.O S.V, IsLat L Λ →
      S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
        (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨comm Λ Λs hΛ hstd, comm Λs Λ hstd hΛ⟩
  refine ⟨fun Λ hΛ => ⟨(latPart Λ hΛ).1, (latPart Λ hΛ).2, ?_⟩, ?_⟩
  · intro h hh
    have hfix : S.H0 = fixG L S.Hm (Submodule.span E (Set.range x)) := by rw [hspan]; exact hH0
    have hh' : h ∈ fixG L S.Hm (Submodule.span E (Set.range x)) := hfix ▸ hh
    have key := GlobalTheory.T.unitaryGroup_orthogonalComplement_unimodular L S.Hm S.herm (2 * r + 2) x hdet Λs Λ hstd hΛ h hh'
    rw [hK, hfix]
    exact key
  · intro d Λ hT
    have hΛ : IsLat L Λ := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1.1
    obtain ⟨hlo, Λ₂, hΛ₂, hhi⟩ := GlobalTheory.T.datum_stabilizer_between_lattice_stabilizers L r k S d Λ hT
    refine ⟨fun h0 => (latPart Λ₂ hΛ₂).1 (Subgroup.relIndex_eq_zero_of_le_right hhi h0),
      fun h0 => (latPart Λ hΛ).2 (Subgroup.relIndex_eq_zero_of_le_left hlo h0)⟩

end GlobalTheory.HL
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_unique_global_lattice_of_local_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)), (∀ p, IsLat (A.L p) (Λ p)) → {p | Λ p ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite → ∃! Γ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Γ ∧ ∀ p, A.lat p Γ = Λ p := by
  first | exact @GlobalTheory.HL.Glue.glue | exact GlobalTheory.HL.Glue.glue | (intros; apply GlobalTheory.HL.Glue.glue <;> assumption)
end
