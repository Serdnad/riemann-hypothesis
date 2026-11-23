module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.WittCompl

theorem hT_coords {D : D7} (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) =
      ∑ k, ∑ l, star (a k) * V.gram k l * b l := by
  simp only [Module.Basis.equivFun_symm_apply]

  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, HSpace.gram,
  starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hT_cols {D : D7} (V : HSp D) {m : ℕ} (A B : Matrix (Fin V.rank) (Fin m) D.host.E) (i j : Fin m) :
    V.hT (V.frame.equivFun.symm fun k => A k i) (V.frame.equivFun.symm fun k => B k j) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) i j := by
  rw [hT_coords]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_perp {E : Type} [Field E] [NumberField E] [StarRing E] (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (V : HSpace E) {n : ℕ} (c d : Fin n → V.V) (hcc : ∀ i j, V.hT (c i) (c j) = 0)
    (hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), HSpace.IsIsomEmb V' V ι ∧
      ∀ v, v ∈ LinearMap.range ι ↔ ∀ i, V.hT (c i) v = 0 ∧ V.hT (d i) v = 0 := by
  classical
  have hs := V.herm
  have hdc : ∀ i j, V.hT (d i) (c j) = if i = j then 1 else 0 := fun i j => by
    rw [← hs.eq (c j) (d i), hcd]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : LinearIndependent E c := Fintype.linearIndependent_iff.2 fun g hg j => by
    have := congrArg (V.hT (d j)) hg

    simpa [map_sum, hdc] using this
  obtain ⟨V', ι, hr, hι, h0⟩ := GlobalTheory.WittLow.exists_lower hst V c hc hcc
  have h0' : ∀ x a, V.hT (c a) (ι x) = 0 := fun x a => by rw [← hs.eq (ι x) (c a), h0, map_zero]
  let p : V.V →ₗ[E] V.V := LinearMap.id - ∑ k, (V.hT (d k)).smulRight (c k)
  have hp : ∀ v, p v = v - ∑ k, V.hT (d k) v • c k := fun v => by simp [p, LinearMap.sum_apply]
  have hcp : ∀ a v, V.hT (c a) (p v) = V.hT (c a) v := fun a v => by simp [hp, map_sum, hcc]
  have hdp : ∀ a v, V.hT (d a) (p v) = 0 := fun a v => by simp [hp, map_sum, hdc]
  have hiso : HSpace.IsIsomEmb V' V (p ∘ₗ ι) := fun x y => by
    rw [← hι x y]
    show V.hT (p (ι x)) (p (ι y)) = V.hT (ι x) (ι y)
    have e1 : V.hT (ι x) (p (ι y)) = V.hT (ι x) (ι y) := by simp [hp, map_sum, h0]

    rw [hp (ι x), map_sub, LinearMap.sub_apply, e1, map_sum, LinearMap.sum_apply]
    simp [hcp, h0']
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun x hx =>
    V'.nondeg.1 x fun y => by rw [← hι x y, hx]; simp
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (c j)) with hP
  have hdisj : Disjoint (LinearMap.range ι) (Submodule.span E (Set.range c)) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : x = 0 := V'.nondeg.1 x fun y => by
      rw [← hι x y, ← hg]

      simp [map_sum, LinearMap.sum_apply, h0']
    rw [this, map_zero]
  have hle : LinearMap.range ι ⊔ Submodule.span E (Set.range c) ≤ P :=
    sup_le (by rintro _ ⟨x, rfl⟩; exact funext fun j => h0' x j)
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact funext fun a => hcc a j))
  have heq : LinearMap.range ι ⊔ Submodule.span E (Set.range c) = P := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) (Submodule.span E (Set.range c))
    rw [hdisj.eq_bot, finrank_bot, LinearMap.finrank_range_of_inj hinj, finrank_span_eq_card hc, Fintype.card_fin] at e1
    have e2 := GlobalTheory.WittLow.finrank_orth hs V.nondeg c hc
    have e3 : Module.finrank E V'.V = V'.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V'.frame
    have e4 : Module.finrank E V.V = V.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V.frame
    rw [← hP] at e2
    omega
  refine ⟨V', p ∘ₗ ι, hiso, fun v => ⟨?_, fun hv => ?_⟩⟩
  · rintro ⟨x, rfl⟩ i
    exact ⟨(hcp i _).trans (h0' x i), hdp i _⟩
  · have hvP : v ∈ P := funext fun j => (hv j).1
    rw [← heq] at hvP
    obtain ⟨_, ⟨x, rfl⟩, u, hu, rfl⟩ := Submodule.mem_sup.1 hvP
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hu
    refine ⟨x, ?_⟩
    have hg : ∀ k, V.hT (d k) (ι x) = -g k := fun k => by
      have := (hv k).2

      simp [map_sum, hdc] at this
      exact eq_neg_of_add_eq_zero_left this
    show p (ι x) = _
    simp [hp, hg, sub_eq_add_neg]

theorem exists_compl : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  intro D V m X Y h T
  classical
  let e := Fintype.equivFin {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}
  let c : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => X j (e.symm k).1
  let d : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => Y j (e.symm k).1
  have hcc : ∀ i j, V.hT (c i) (c j) = 0 := fun i j => by
    simp only [c]
    rw [hT_cols, h.xx]
    rfl
  have hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0 := fun i j => by
    simp only [c, d]
    rw [hT_cols, h.xy, Matrix.one_apply]
    simp only [Subtype.val_inj, e.symm.apply_eq_iff_eq]
  obtain ⟨V', ι, hι, hr⟩ := exists_perp Formalism.BasicNotions.Examples₂.star_isIntegral V c d hcc hcd
  refine ⟨V', ι, hι, fun v => ?_⟩
  rw [hr]
  constructor
  · intro hv i hi
    have := hv (e ⟨i, hi⟩)
    simpa [c, d] using this
  · intro hv k
    exact hv _ (e.symm k).2

end GlobalTheory.CompanionTheory.WittCompl

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

def IsAdapted {D : D7} (V : HSp D) {m : ℕ} (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, ∃ (k : Formalism.REAL.KG (ε τ)) (S : Set (Fin V.rank)),
    Submodule.span ℂ (Set.range (fun i : upTo T => (fr τ *ᵥ fun j => tauE D τ (X j i))) ∪
        Set.range (fun i : upTo T => (fr τ *ᵥ fun j => tauE D τ (Y j i)))) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin V.rank) (1 : ℂ) : Fin V.rank → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit

section Lin

variable {A : Type} [CommRing A] {n m : ℕ}

theorem mulVec_eq_of_mem (C : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A) (U : Matrix (Fin m) (Fin n) A)
    (W : Matrix (Fin n) (Fin m) A) (I : Set (Fin m)) (hDC : D * C = 0) (hUC : ∀ i j, j ∈ I → (U * C) i j = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Cᵀ i) '' I)) : (1 + C * U + W * D) *ᵥ y = y := by
  obtain ⟨a, ha, rfl⟩ := (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff C I y).1 hy
  have h1 : (U * C) *ᵥ a = 0 := funext fun i => by
    show ∑ l, (U * C) i l * a l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l ∈ I
    · rw [hUC i l hl, zero_mul]
    · rw [ha l hl, mul_zero]
  have h2 : (1 + C * U + W * D) *ᵥ (C *ᵥ a) = C *ᵥ a + C *ᵥ ((U * C) *ᵥ a) + W *ᵥ ((D * C) *ᵥ a) := by
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec]
  rw [h2, h1, hDC]
  simp

theorem mulVec_sub_mem (C : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A) (U : Matrix (Fin m) (Fin n) A)
    (W : Matrix (Fin n) (Fin m) A) (I : Set (Fin m)) (hU : ∀ i v, i ∉ I → U i v = 0) {y : Fin n → A}
    (hy : W *ᵥ (D *ᵥ y) = 0) : (1 + C * U + W * D) *ᵥ y - y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) := by
  have h : (1 + C * U + W * D) *ᵥ y - y = C *ᵥ (U *ᵥ y) := by
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec, hy]
    abel
  rw [h]
  refine (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff C I _).2 ⟨U *ᵥ y, fun l hl => ?_, rfl⟩
  show ∑ v, U l v * y v = 0
  exact Finset.sum_eq_zero fun v _ => by rw [hU l v hl, zero_mul]

theorem mem_iff_of_fix {M : Matrix (Fin n) (Fin n) A} (hM : Function.Injective M.mulVec) (S : Submodule A (Fin n → A))
    (hS : ∀ y ∈ S, M *ᵥ y = y) (y : Fin n → A) : y ∈ S ↔ M *ᵥ y ∈ S :=
  ⟨fun h => by rwa [hS y h], fun h => by rwa [← hM (hS _ h)]⟩

end Lin

theorem mem_unip {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin m) E) (T : Finset (Fin m)) (g : GAd σ J)
    (U : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) (W : Matrix (Fin n) (Fin m) (AF F ⊗[F] E))
    (hX : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hU : ∀ i v, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → U i v = 0)
    (hW : ∀ v i, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → W v i = 0)
    (hUX : ∀ i j, j ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → (U * GlobalTheory.SiegelSet.adMat F X) i j = 0)
    (hg : (GlobalTheory.AdelicU.matHom _ σ J g).1 =
      1 + GlobalTheory.SiegelSet.adMat F X * U + W * GlobalTheory.SiegelSet.adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) :
    g ∈ GlobalTheory.StdPar.unip σ J X T := by
  have hDC : adMat F (Formalism.UG.cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [adMat, adMat, ← Matrix.map_mul, hX]
    exact Matrix.map_zero _ (map_zero _)
  have hinj : Function.Injective (GlobalTheory.AdelicU.matHom _ σ J g).1.mulVec :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit _)
  have hfix : ∀ y ∈ colSpan F X (upTo T), (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    rw [hg]
    exact mulVec_eq_of_mem _ _ U W _ hDC hUX hy
  have hsub : ∀ y, W *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) = 0 →
      (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y - y ∈ colSpan F X (upTo T) := fun y hy => by
    rw [hg]
    exact mulVec_sub_mem _ _ U W _ hU hy
  have hiff : ∀ S ≤ colSpan F X (upTo T), ∀ y, y ∈ S ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y ∈ S := fun S hS =>
    mem_iff_of_fix hinj S fun y hy => hfix y (hS hy)
  refine ⟨Subgroup.mem_iInf.2 fun j => ?_, hiff _ le_rfl, fun y hy => hsub y ?_⟩
  · by_cases hj : j ∈ upTo T
    · have hA : colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ≤ colSpan F X (upTo T) :=
        Submodule.span_mono (Set.image_mono fun i ⟨k, hk, hik, _⟩ => ⟨k, hk, hik⟩)
      have hB : colSpan F X {j} ≤ colSpan F X (upTo T) :=
        Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj))
      refine ⟨hiff _ hA, fun y hy => ?_⟩
      rw [hfix y (hB hy), sub_self]
      exact zero_mem _
    · have hA : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = upTo T := Set.ext fun i =>
        ⟨fun ⟨k, hk, hik, _⟩ => ⟨k, hk, hik⟩, fun ⟨k, hk, hik⟩ =>
          ⟨k, hk, hik, not_le.1 fun h => hj ⟨k, hk, h⟩⟩⟩
      rw [hA]
      refine ⟨hiff _ le_rfl, fun y hy => hsub y ?_⟩
      obtain ⟨a, -, rfl⟩ := (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff _ _ y).1 hy
      rw [mulVec_mulVec a, hDC, zero_mulVec, mulVec_zero]
  · funext v
    show ∑ i, W v i * (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ upTo T
    · have h : (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0 := by
        simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy
        exact hy i hi
      rw [h, mul_zero]
    · rw [hW v i hi, zero_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit
end
end
