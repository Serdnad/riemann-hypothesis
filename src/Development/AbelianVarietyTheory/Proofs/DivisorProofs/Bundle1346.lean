module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped RealInnerProductSpace

noncomputable section

namespace GlobalTheory.WeilAdm.RealModel

variable {F : Type} [Field F] [NumberField F]

def pt (a : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

def fstH : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _

def sndH : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

theorem pt_ext {x y : AdeleRing (𝓞 F) F} (h1 : fstH x = fstH y) (h2 : sndH x = sndH y) : x = y :=
  Prod.ext h1 h2

theorem dot_infE_infE {κ : Type} [Fintype κ] (z y : κ → mixedEmbedding.mixedSpace F) :
    infE F z ⬝ᵥ infE F y = pt (∑ i, z i * y i) := by
  refine pt_ext ?_ ?_
  · simp only [dotProduct, map_sum, map_mul]
    change ∑ i, (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i) *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (∑ i, z i * y i)
    simp only [map_sum, map_mul]
  · simp only [dotProduct, map_sum, map_mul]
    change ∑ i, (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    simp

theorem invOf_two_mul_pt (S : mixedEmbedding.mixedSpace F) :
    ∃ t, ⅟(2 : AdeleRing (𝓞 F) F) * pt S = pt t ∧ t + t = S := by
  set c : InfiniteAdeleRing F := fstH (⅟(2 : AdeleRing (𝓞 F) F))
  refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace F (c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S), ?_, ?_⟩
  · refine pt_ext ?_ ?_
    · rw [map_mul]
      show c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
      rw [RingEquiv.symm_apply_apply]
    · rw [map_mul]
      show _ * (0 : FiniteAdeleRing (𝓞 F) F) = 0
      exact mul_zero _
  · have hc : c * 2 = 1 := by
      have h := congrArg fstH (invOf_mul_self (2 : AdeleRing (𝓞 F) F))
      rwa [map_mul, map_ofNat, map_one] at h
    rw [← map_add (f := _), ← add_mul, ← mul_two, hc, one_mul, RingEquiv.apply_symm_apply]

theorem schrInf_eq (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hψ : ∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a))
    {κ : Type} [Fintype κ] (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    schrInf F ψ v φ z = Complex.exp (2 * Real.pi * Complex.I *
      (β (∑ i, z i * v.2 i) + β (∑ i, v.1 i * v.2 i) / 2)) * φ (z + v.1) := by
  have hψ' : ∀ a, ψ (pt a) = Complex.exp (2 * Real.pi * Complex.I * β a) := hψ
  obtain ⟨t, ht, htt⟩ := invOf_two_mul_pt (F := F) (∑ i, v.1 i * v.2 i)
  have hsum : ∀ a b : mixedEmbedding.mixedSpace F, pt (F := F) a + pt b = pt (a + b) := by
    intro a b
    refine pt_ext ?_ ?_
    · rw [map_add (f := _)]
      exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
    · rw [map_add (f := _)]
      exact add_zero (0 : FiniteAdeleRing (𝓞 F) F)
  have hbt : β t = β (∑ i, v.1 i * v.2 i) / 2 := by
    rw [← htt, map_add (f := _)]; ring
  show ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * φ (z + v.1) = _
  rw [dot_infE_infE, dot_infE_infE, ht, hsum, hψ', map_add (f := _), hbt]
  push_cast
  ring_nf

end GlobalTheory.WeilAdm.RealModel

namespace GlobalTheory.WeilAdm.RealModel

variable {F : Type} [Field F] [NumberField F]

def bil (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z y => β (∑ i, z i * y i))
    (fun z z' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c z y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun z y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c z y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul])

theorem bil_apply (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ]
    (z y : κ → mixedEmbedding.mixedSpace F) : bil β κ z y = β (∑ i, z i * y i) := rfl

def qmap (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ] {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun y := (InnerProductSpace.toDual ℝ _).symm
    (LinearMap.toContinuousLinearMap (((bil β κ).flip y).comp (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] _).toLinearMap))
  map_add' y y' := by
    refine ext_inner_right ℝ fun x => ?_
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' c y := by
    refine ext_inner_right ℝ fun x => ?_
    simp [InnerProductSpace.toDual_symm_apply, real_inner_smul_left]

theorem inner_qmap (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ] {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) (y : κ → mixedEmbedding.mixedSpace F)
    (x : EuclideanSpace ℝ (Fin n)) : ⟪qmap β Q y, x⟫ = bil β κ (Q x) y := by
  simp [qmap, InnerProductSpace.toDual_symm_apply]

theorem qmap_injective (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    Function.Injective (qmap β Q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨b, hb⟩ := hβ (y i) hi
  have h := inner_qmap β Q y (Q.symm (Pi.single i b))
  rw [hy, inner_zero_left, ContinuousLinearEquiv.apply_symm_apply, bil_apply] at h
  have hs : ∑ j, (Pi.single i b : κ → mixedEmbedding.mixedSpace F) j * y j = y i * b := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp [mul_comm]
  rw [hs] at h
  exact hb h.symm

def qEquiv (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.linearEquivOfInjective (qmap β Q) (qmap_injective β hβ Q) Q.toLinearEquiv.finrank_eq.symm

theorem qmap_qEquiv_symm (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
    (q : EuclideanSpace ℝ (Fin n)) : qmap β Q ((qEquiv β hβ Q).symm q) = q := by
  exact (qEquiv β hβ Q).apply_symm_apply q

def Peq {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] V)
    (Y : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] V) : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] V × V where
  toFun w := (Q (GlobalTheory.RealWeil.pPart w), Y (GlobalTheory.RealWeil.qPart w))
  invFun p := Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))
  map_add' w w' := by simp [GlobalTheory.RealWeil.pPart_add, GlobalTheory.RealWeil.qPart_add]
  map_smul' c w := by simp [GlobalTheory.RealWeil.pPart_smul, GlobalTheory.RealWeil.qPart_smul]
  left_inv w := by
    funext j
    cases j <;> simp [GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart]
  right_inv p := by
    have h1 : GlobalTheory.RealWeil.pPart (Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))) = Q.symm p.1 := by
      simp [GlobalTheory.RealWeil.pPart]
    have h2 : GlobalTheory.RealWeil.qPart (Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))) = Y.symm p.2 := by
      simp [GlobalTheory.RealWeil.qPart]
    simp only [h1, h2, LinearEquiv.apply_symm_apply]

theorem exists_model : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  intro F _ _ ψ β hψ hβ κ _
  let Q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F))) ≃L[ℝ]
      (κ → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin).toContinuousLinearEquiv
  let Y := (qEquiv β hβ Q).symm
  refine ⟨_, Q, Peq Q.toLinearEquiv Y, fun w φ => ?_⟩
  funext x
  have hq := qmap_qEquiv_symm β hβ Q (GlobalTheory.RealWeil.qPart w)
  have h1 := inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) x
  have h2 := inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) (GlobalTheory.RealWeil.pPart w)
  rw [hq, bil_apply] at h1 h2
  simp only [Function.comp_apply, GlobalTheory.RealWeil.rhoFun, GlobalTheory.RealWeil.phase]
  rw [schrInf_eq ψ β hψ]
  show Complex.exp (2 * Real.pi * Complex.I * (β (∑ i, Q x i * Y (GlobalTheory.RealWeil.qPart w) i) +
      β (∑ i, Q (GlobalTheory.RealWeil.pPart w) i * Y (GlobalTheory.RealWeil.qPart w) i) / 2)) *
      φ (Q x + Q (GlobalTheory.RealWeil.pPart w)) = _
  rw [← h1, ← h2, ← map_add (f := _), real_inner_comm (GlobalTheory.RealWeil.pPart w)]
  congr 2
  push_cast
  ring

end GlobalTheory.WeilAdm.RealModel
end
end

section

open scoped SchwartzMap Matrix

open scoped RealInnerProductSpace
noncomputable section
namespace GlobalTheory.ArchUniq
open GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def leftForm {P : V → V → ℝ} (hP : IsPairing P) (b : V) : V →ₗ[ℝ] ℝ where
  toFun x := P x b
  map_add' x x' := hP.addL x x' b
  map_smul' c x := hP.smulL c x b

theorem pair_expand {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) (y b : V) :
    P y b = ∑ i, C y i * P (C.symm (EuclideanSpace.single i 1)) b := by
  have hy : y = ∑ i, C y i • C.symm (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← C.symm_apply_apply y, ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (C y)]

    simp [map_sum]
  have e : P y b = leftForm hP b y := rfl
  rw [e]
  conv_lhs => rw [hy]

  rw [map_sum]
  simp [leftForm, hP.smulL]

def pairCoordsL {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) :
    V × V →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) where
  toFun v := Sum.elim (fun i => C v.1 i) (fun i => -P (C.symm (EuclideanSpace.single i 1)) v.2)
  map_add' v v' := by
    funext j
    rcases j with i | i <;> simp [hP.addR]; ring
  map_smul' c v := by
    funext j
    rcases j with i | i <;> simp [hP.smulR]

theorem pairCoordsL_injective {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) :
    Function.Injective (pairCoordsL C hP) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, b⟩ h
  have ha : a = 0 := by
    apply C.injective
    ext i
    simpa [pairCoordsL] using congrFun h (Sum.inl i)
  have hb : b = 0 := by
    apply hP.nondegR
    intro x
    rw [pair_expand C hP]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h (Sum.inr i)
    simp [pairCoordsL] at this
    simp [this]
  simp [ha, hb]

theorem exists_pairing_coords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := by
  intro V _ _ _ P hP n hn
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  have hp : ∀ v : V × V, pPart (φ v) = C v.1 := by
    intro v; ext i; simp [hφ, pPart, pairCoordsL]
  have hq : ∀ (v : V × V) (x : EuclideanSpace ℝ (Fin n)),
      ⟪qPart (φ v), x⟫ = -∑ i, P (C.symm (EuclideanSpace.single i 1)) v.2 * x i := by
    intro v x
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]
  have hq' : ∀ (v : V × V) (y : V), ⟪qPart (φ v), C y⟫ = -P y v.2 := by
    intro v y
    rw [hq, pair_expand C hP y v.2]
    simp [mul_comm]
  have hCq : ∀ (v : V × V) (y : V), ⟪C y, qPart (φ v)⟫ = -P y v.2 := by
    intro v y
    rw [real_inner_comm, hq']
  refine ⟨C, φ, ?_, ?_⟩
  · intro v v'
    simp only [sympl, omega, hp, hCq, hq']
    ring
  · intro v f
    funext y
    simp only [schrF, rhoFun, phase, Function.comp_apply, map_add (f := _), hp, hq', hCq]
    congr 1
    congr 1
    push_cast
    ring
end GlobalTheory.ArchUniq
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Type := UG (cA σ) (dbl (incM F W.J))

def matD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  g.1.1

def latAtD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (Fin d ⊕ Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  {z | (fun i => z (Sum.inl i)) ∈ GlobalTheory.InertSph.latAt W v ∧ (fun i => z (Sum.inr i)) ∈ GlobalTheory.InertSph.latAt W v}

def KAtD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {g | At (evFin F v) (matD g - 1) ∧
    ∀ z ∈ latAtD W v, matD g *ᵥ z ∈ latAtD W v ∧ matD g⁻¹ *ᵥ z ∈ latAtD W v}

def antiCols (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := Matrix.fromRows 1 (-1)

def ParD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {p | p ∈ KAtD σ W v ∧ ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

def NabD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {n | n ∈ KAtD σ W v ∧ matD n * antiCols d = antiCols d ∧
    ∃ b : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD n * diagCols (Fin d) = diagCols (Fin d) + antiCols d * b}

theorem fromBlocks_mem {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (k : UA σ W.J) :
    ((Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))ᵀ * dbl (incM F W.J) *
      (Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F W.J) := by
  have hk : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, dbl, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hk, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]

def inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : UA σ W.J →* UD σ W where
  toFun k := ⟨⟨Matrix.fromBlocks (mat k) 0 0 1, Matrix.fromBlocks (mat k⁻¹) 0 0 1,
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one],
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one]⟩,
    fromBlocks_mem k⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (1 : UA σ W.J)) 0 0 1 = 1
    simp [mat, Matrix.fromBlocks_one]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (a * b)) 0 0 1 = Matrix.fromBlocks (mat a) 0 0 1 * Matrix.fromBlocks (mat b) 0 0 1
    rw [Matrix.fromBlocks_multiply]; simp [mat]

theorem matD_inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (k : UA σ W.J) :
    matD (inlD σ W k) = Matrix.fromBlocks (mat k) 0 0 1 := rfl

def dblFun {κ : Type} (Ψ : (κ → AF F) → ℂ) : (κ ⊕ κ → AF F) → ℂ := boxFun Ψ fun x => star (Ψ x)

end GlobalTheory.InertDbl

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CoordinateEmbeddingMaps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ball (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (C : ℝ) (hC : 0 ≤ C) : AddSubgroup (Fv F v) where
  carrier := {c | ‖c‖ ≤ C}
  zero_mem' := by simpa using hC
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := by
    intro a ha
    simpa using ha

theorem norm_le_one_of_mem {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (a : Fv F v) (h : a ∈ v.adicCompletionIntegers F) :
    ‖a‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr h

def coordE (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (n : ℕ) (x : (_ : Fin n) × Fin (Module.finrank F E)) :
    (Fin n → E) →+ Fv F v where
  toFun y := algebraMap F (Fv F v) ((Module.finBasis F E).repr (y x.1) x.2)
  map_zero' := by simp
  map_add' := by intro a b; simp

theorem main : (let d1 : (F E : Type) → [inst : Field F] → [inst_1 : NumberField F] → [inst_2 : Field E] → [NumberField E] → [inst_4 : Algebra F E] → (n : ℕ) → Module.Basis ((_ : Fin n) × Fin (Module.finrank F E)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := @(fun (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) ↦ Pi.basis fun (x : Fin n) ↦ Module.Basis.baseChange (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Module.finBasis F E)); ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {n : ℕ} (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), Submodule.FG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc.L W) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∃ (C : ℝ), ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ (x : (_ : Fin n) × Fin (Module.finrank F E)), ‖(GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (((Module.Basis.repr (d1 F E n) : (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (_ : Fin n) × Fin (Module.finrank F E) →₀ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) z : (_ : Fin n) × Fin (Module.finrank F E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x)‖ ≤ C) := by
  intro d1 F E _ _ _ _ _ n W hL v
  obtain ⟨s, hs⟩ := (hL.restrictScalars : (W.L.restrictScalars ℤ).FG)
  set C : ℝ := ∑ x : (_ : Fin n) × Fin (Module.finrank F E), ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖ with hCdef
  have hC : 0 ≤ C := by positivity
  refine ⟨C, ?_⟩

  have hLb : ∀ x, ∀ y ∈ W.L, ‖coordE (F := F) (E := E) v n x y‖ ≤ C := by
    intro x y hy
    have hle : W.L.restrictScalars ℤ ≤ ((ball v C hC).comap (coordE (F := F) (E := E) v n x)).toIntSubmodule := by
      rw [← hs, Submodule.span_le]
      intro g hg
      show ‖coordE (F := F) (E := E) v n x g‖ ≤ C
      calc ‖coordE (F := F) (E := E) v n x g‖
          ≤ ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖ :=
            Finset.single_le_sum (f := fun g => ‖coordE (F := F) (E := E) v n x g‖) (fun _ _ => norm_nonneg _) hg
        _ ≤ C := Finset.single_le_sum (f := fun x => ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ x)
    exact hle hy
  intro z hz x

  let φ : (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →+ Fv F v :=
    (GlobalTheory.AdelicU.evFin F v).toAddMonoidHom.comp
      ((Finsupp.applyAddHom x).comp (d1 F E n).repr.toLinearMap.toAddMonoidHom)
  have hφ : ∀ z, φ z = GlobalTheory.AdelicU.evFin F v ((d1 F E n).repr z x) := fun z => rfl
  have key : GlobalTheory.InertSph.latAt W v ≤ (ball v C hC).comap φ := by
    unfold GlobalTheory.InertSph.latAt
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, -, ha, y, hy, rfl⟩
    show ‖φ _‖ ≤ C
    rw [hφ]
    have : (d1 F E n).repr (a • fun i => inclR (F := F) (AF F) (y i)) x
        = a * algebraMap F (AF F) ((Module.finBasis F E).repr (y x.1) x.2) := by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      congr 1
      simp only [d1, Pi.basis_repr]
      show ((Module.finBasis F E).baseChange (AF F)).repr ((1 : AF F) ⊗ₜ[F] y x.1) x.2 = _
      rw [Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
    rw [this, map_mul, AlgHom.commutes, norm_mul]
    have h1 := norm_le_one_of_mem _ ha
    have h2 := hLb x y hy
    calc _ ≤ 1 * C := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  exact key hz

end GlobalTheory.CoordinateEmbeddingMaps
end
end
