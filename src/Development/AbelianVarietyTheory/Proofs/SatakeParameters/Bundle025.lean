module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.LinearAlgebra.Matrix.Rank
public import GroundTheory.AutomorphicForms.AffineBruhat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle009
public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle010

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise

namespace GlobalTheory.SmoothRiesz

theorem exists_mem_eq_on_of_finiteDimensional {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  first
  | exact @_root_.GlobalTheory.ExistsRepresentation.exists_represent
  | exact _root_.GlobalTheory.ExistsRepresentation.exists_represent
  | (apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsRepresentation.exists_represent <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsRepresentation.exists_represent ..)

theorem finite_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (hsm : IsSmooth σ)
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (y : V) :
    ((fun k : G => σ k y) '' (K : Set G)).Finite := by
  let S : Set G := {g | σ g y = y}
  have hSo : IsOpen S := hsm y
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun g : K => (g : G) • S) (fun g => hSo.smul _)
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, Set.mem_smul_set.2 ⟨1, by simp [S], by simp⟩⟩)
  refine ((t.finite_toSet.image (fun i : K => σ (i : G) y))).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.1 hki
  refine ⟨i, hi, ?_⟩
  have hs' : σ s y = y := hs
  simp only [smul_eq_mul, map_mul, Module.End.mul_apply, hs']

theorem exists_eq_of_invariant {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hadm : IsAdmissible σ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (hinv : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w) (L : V →ₗ⋆[ℂ] ℂ)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hL : ∀ s ∈ K, ∀ w, L (σ s w) = L w) : ∃ u : V, ∀ w, L w = Bf u w := by
  haveI : FiniteDimensional ℂ (fixed σ K) := hadm.2 K hKo hKc
  obtain ⟨u, huK, hu⟩ := exists_mem_eq_on_of_finiteDimensional Bf hpos L (fixed σ K)
  have hfix : ∀ k ∈ K, σ k u = u := fun k hk => by
    simpa using huK ⟨k, hk⟩
  refine ⟨u, fun w => ?_⟩
  have hcomp : ∀ (a b : G) (x : V), σ a (σ b x) = σ (a * b) x := fun a b x => by
    rw [map_mul, Module.End.mul_apply]
  let O : Finset V := (finite_orbit σ hadm.1 K hKc w).toFinset
  have hO : ∀ x, x ∈ O ↔ ∃ k ∈ K, σ k w = x := fun x => by simp [O]
  have hwO : w ∈ O := (hO w).2 ⟨1, K.one_mem, by simp⟩
  have hcard : ((O.card : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hwO⟩)
  have heK : (∑ x ∈ O, x) ∈ fixed σ K := by
    intro k

    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sum]
    refine Finset.sum_nbij' (fun x => σ k x) (fun x => σ (k : G)⁻¹ x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨k * c, K.mul_mem k.2 hc, (hcomp _ _ _).symm⟩
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨(k : G)⁻¹ * c, K.mul_mem (K.inv_mem k.2) hc, (hcomp _ _ _).symm⟩
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rfl
  have hLO : ∀ x ∈ O, L x = L w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    exact hL c hc w
  have hBO : ∀ x ∈ O, Bf u x = Bf u w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    conv_lhs => rw [← hfix c hc]
    exact hinv c u w
  have key := hu _ heK

  rw [map_sum, map_sum, Finset.sum_congr rfl hLO, Finset.sum_congr rfl hBO, Finset.sum_const,
  Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at key
  exact mul_left_cancel₀ hcard key

end GlobalTheory.SmoothRiesz

namespace GlobalTheory

theorem exists_vector_of_smooth_antilinear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsAdmissible σ → (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) →
    (∀ v, v ≠ 0 → 0 < (Bf v v).re) → (∀ g v w, Bf (σ g v) (σ g w) = Bf v w) →
    ∀ (L : V →ₗ⋆[ℂ] ℂ) (S : Subgroup (GL (Fin r) k)), IsOpen (S : Set (GL (Fin r) k)) →
      (∀ s ∈ S, ∀ w, L (σ s w) = L w) → ∃ u : V, ∀ w, L w = Bf u w := by
  intro k _ _ _ _ r V _ _ σ Bf hadm _ hpos hinv L S hSo hL
  have hKo : IsOpen ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_right
  exact SmoothRiesz.exists_eq_of_invariant σ Bf hadm hpos hinv L _ hKo hKc
    fun s hs => hL s hs.1

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweZero

section Gen

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_isIrreducible {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨a, b, hab⟩ := hσ.toNontrivial.exists_pair_ne
  exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem equiv_trivial_of_fixed {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) {v : V} (hv : v ≠ 0)
    (hfix : ∀ g, σ g v = v) : Nonempty (σ.Equiv (Representation.trivial ℂ G ℂ)) := by
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g x hx => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩
  have hS : S = ⊤ := by
    rcases hσ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hv
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have htop : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hS
  have hall : ∀ g (x : V), σ g x = x := by
    intro g x
    have : x ∈ ℂ ∙ v := htop ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 this
    rw [map_smul, hfix]
  let e : ℂ ≃ₗ[ℂ] V := (LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)
  exact ⟨Representation.Equiv.mk e.symm fun g => by
    ext x
    simp [hall]⟩

theorem fixed_of_tensor_left (e : V ≃ₗ[ℂ] ℂ) (τ : Representation ℂ H W) (t : V ⊗[ℂ] W) (ht0 : t ≠ 0)
    (ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) t = t) : ∃ w : W, w ≠ 0 ∧ ∀ h, τ h w = w := by
  let L : V ⊗[ℂ] W ≃ₗ[ℂ] W := (TensorProduct.congr e (LinearEquiv.refl ℂ W)).trans (TensorProduct.lid ℂ W)
  refine ⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun h => ?_⟩
  have key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (1 : Module.End ℂ V) (τ h) s) = τ h (L s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [L]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← key, ht]

theorem fixed_of_tensor_right (e : W ≃ₗ[ℂ] ℂ) (σ : Representation ℂ G V) (t : V ⊗[ℂ] W) (ht0 : t ≠ 0)
    (ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) t = t) : ∃ v : V, v ≠ 0 ∧ ∀ g, σ g v = v := by
  let L : V ⊗[ℂ] W ≃ₗ[ℂ] V := (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  refine ⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun g => ?_⟩
  have key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (σ g) (1 : Module.End ℂ W) s) = σ g (L s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [L]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← key, ht]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gl_zero_eq_one (g : GL (Fin 0) k) : g = 1 :=
  Units.ext (Matrix.ext fun i => Fin.elim0 i)

theorem nabs_one' : nabs k 1 = 1 := by simp [nabs]

theorem detRep_one (m : ℕ) : detRep (Fin m) (1 : kˣ →* ℂˣ) = Representation.trivial ℂ (GL (Fin m) k) ℂ := by
  unfold detRep ofChar detChar
  rw [MonoidHom.one_comp, twist_one]

theorem om_left (n : ℕ) (h : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin 0) k → ℂ) :
    om (1 : kˣ →* ℂˣ) (1 : GL (Fin 0) k) h Φ = Φ := by
  funext x
  simp [om, nabs_one']
  exact congrArg Φ (Matrix.ext fun i j => Fin.elim0 j)

theorem om_right (r : ℕ) (g : GL (Fin r) k) (Φ : Matrix (Fin 0) (Fin r) k → ℂ) :
    om (1 : kˣ →* ℂˣ) g (1 : GL (Fin 0) k) Φ = Φ := by
  funext x
  simp [om, nabs_one']
  exact congrArg Φ (Matrix.ext fun i j => Fin.elim0 i)

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), r = 0 ∨ n = 0 → σ.IsIrreducible → τ.IsIrreducible → OmQuot 1 σ τ → Nonempty (σ.Equiv (detRep (Fin r) (1 : kˣ →* ℂˣ))) ∧ Nonempty (τ.Equiv (detRep (Fin n) (1 : kˣ →* ℂˣ))) := by
  intro k _ _ _ _ r n V W _ _ _ _ σ τ hrn hσ hτ hq
  obtain ⟨f, hf0, hf⟩ := hq
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, f Φ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext hc)
  rw [detRep_one, detRep_one]
  rcases hrn with rfl | rfl
  · haveI := nontrivial_of_isIrreducible hσ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨eσ⟩ := equiv_trivial_of_fixed hσ hv (fun g => by rw [gl_zero_eq_one g, map_one]; rfl)
    have ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) (f Φ) = f Φ := fun h => by
      have := hf 1 h Φ Φ (om_left n h Φ).symm
      rw [map_one] at this
      exact this.symm
    obtain ⟨w, hw0, hw⟩ := fixed_of_tensor_left eσ.toLinearEquiv τ _ hΦ ht
    exact ⟨⟨eσ⟩, equiv_trivial_of_fixed hτ hw0 hw⟩
  · haveI := nontrivial_of_isIrreducible hτ
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨eτ⟩ := equiv_trivial_of_fixed hτ hw (fun h => by rw [gl_zero_eq_one h, map_one]; rfl)
    have ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) (f Φ) = f Φ := fun g => by
      have := hf g 1 Φ Φ (om_right r g Φ).symm
      rw [map_one] at this
      exact this.symm
    obtain ⟨v, hv0, hv⟩ := fixed_of_tensor_right eτ.toLinearEquiv σ _ hΦ ht
    exact ⟨equiv_trivial_of_fixed hσ hv0 hv, ⟨eτ⟩⟩

end GlobalTheory.HoweZero
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HoweTranspose

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def trH (a b : ℕ) : Matrix (Fin a) (Fin b) k ≃ₜ Matrix (Fin b) (Fin a) k where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

theorem comp_trH_mem {a b : ℕ} {f : Matrix (Fin b) (Fin a) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin b) (Fin a) k)) : f ∘ trH a b ∈ SB (Matrix (Fin a) (Fin b) k) :=
  ⟨hf.1.comp_continuous (trH a b).continuous, hf.2.comp_homeomorph (trH a b)⟩

def trL (a b : ℕ) : SB (Matrix (Fin b) (Fin a) k) →ₗ[ℂ] SB (Matrix (Fin a) (Fin b) k) where
  toFun Ψ := ⟨Ψ.1 ∘ trH a b, comp_trH_mem Ψ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trL_trL (a b : ℕ) (Φ : SB (Matrix (Fin a) (Fin b) k)) : trL a b (trL b a Φ) = Φ := by
  apply Subtype.ext
  funext x
  show Φ.1 x.transpose.transpose = Φ.1 x
  rw [Matrix.transpose_transpose]

theorem det_transInv {m : ℕ} (θ : GL (Fin m) k →* GL (Fin m) k)
    (hθ : ∀ g, (θ g).val = (g⁻¹).val.transpose) (g : GL (Fin m) k) :
    Matrix.GeneralLinearGroup.det (θ g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hθ, Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_inv]

theorem nabs_det_transInv {m : ℕ} (θ : GL (Fin m) k →* GL (Fin m) k)
    (hθ : ∀ g, (θ g).val = (g⁻¹).val.transpose) (g : GL (Fin m) k) :
    nabs k (Matrix.GeneralLinearGroup.det (θ g)) = (nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  rw [det_transInv θ hθ]
  simp [nabs, map_inv]

theorem rpow_inv_half {a : ℝ} (ha : 0 < a) (c : ℝ) : (a⁻¹) ^ (c / 2) = a ^ (-c / 2) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, neg_div]

theorem om_trans {r n : ℕ} (θr : GL (Fin r) k →* GL (Fin r) k) (θn : GL (Fin n) k →* GL (Fin n) k)
    (hr : ∀ g, (θr g).val = (g⁻¹).val.transpose) (hn : ∀ g, (θn g).val = (g⁻¹).val.transpose)
    (g : GL (Fin n) k) (h : GL (Fin r) k) (Ψ : Matrix (Fin r) (Fin n) k → ℂ) :
    om 1 g h Ψ ∘ trH n r = om 1 (θr h) (θn g) (Ψ ∘ trH n r) := by
  funext x
  have hm : ((θn g)⁻¹ : GL (Fin n) k).val * x * (θr h).val = (h⁻¹.val * x.transpose * g.val).transpose := by
    rw [← map_inv, hn, hr, inv_inv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  simp only [om, Function.comp_apply, map_one, MonoidHom.one_apply, Units.val_one, inv_one, one_mul,
    Fintype.card_fin]
  rw [nabs_det_transInv θr hr, nabs_det_transInv θn hn, rpow_inv_half (nabs_pos' k _),
    rpow_inv_half (nabs_pos' k _), neg_neg, hm]
  have e1 : trH n r (h⁻¹.val * x.transpose * g.val).transpose = h⁻¹.val * x.transpose * g.val :=
    Matrix.transpose_transpose _
  have e2 : trH n r x = x.transpose := rfl
  rw [e1, e2]
  ring

end GlobalTheory.HoweTranspose


open GlobalTheory.HoweTranspose in
theorem GlobalTheory.omQuot_transpose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) (θr : GL (Fin r) k →* GL (Fin r) k) (θn : GL (Fin n) k →* GL (Fin n) k), (∀ g, (θr g).val = (g⁻¹).val.transpose) → (∀ g, (θn g).val = (g⁻¹).val.transpose) → OmQuot 1 σ τ → OmQuot 1 (τ.comp θn : Representation ℂ (GL (Fin n) k) W) (σ.comp θr : Representation ℂ (GL (Fin r) k) V) := by
  intro k _ _ _ _ r n V W _ _ _ _ σ τ θr θn hr hn ⟨f, hf0, hf⟩
  refine ⟨(TensorProduct.comm ℂ V W).toLinearMap ∘ₗ f ∘ₗ trL n r, ?_, ?_⟩
  · intro h0
    apply hf0
    ext Φ
    have := LinearMap.congr_fun h0 (trL r n Φ)
    simp only [LinearMap.coe_comp, Function.comp_apply, trL_trL, LinearEquiv.coe_coe,
      LinearMap.zero_apply] at this
    simpa using this
  · intro g h Ψ Ψ' hΨ
    have key : f (trL n r Ψ') = TensorProduct.map (σ (θr h)) (τ (θn g)) (f (trL n r Ψ)) := by
      refine hf (θr h) (θn g) _ _ ?_
      show Ψ'.1 ∘ trH n r = om 1 (θr h) (θn g) (Ψ.1 ∘ trH n r)
      rw [hΨ]
      exact om_trans θr θn hr hn g h Ψ.1
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, key, MonoidHom.coe_comp]
    exact (TensorProduct.map_comm _ _ _).symm
end
end

section

open GlobalTheory.LatHecke GlobalTheory.SatakeInv

theorem _root_.GlobalTheory.T.relIndex_glMap_standardLattice_of_integral : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K), (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K) → (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ∧ (IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 → IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin) := by
  first | exact @GlobalTheory.LatHecke.relIndex_glMap_std_of_integral | exact GlobalTheory.LatHecke.relIndex_glMap_std_of_integral | (intros; apply GlobalTheory.LatHecke.relIndex_glMap_std_of_integral <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

theorem _root_.GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)), glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 = (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔ g ∈ GLint (Fin n) (Ov E w) := by
  first | exact @GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint | exact GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint | (intros; apply GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint <;> assumption)
end

section

open GlobalTheory.LatHecke GlobalTheory.SatakeInv

theorem _root_.GlobalTheory.T.card_quot_matrix_range_dvr_eq_residue_pow_corank : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (A : Matrix (Fin r) (Fin r) O), IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin → Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) = qRes O ^ (r - (A.map (IsLocalRing.residue O)).rank) := by
  first | exact @GlobalTheory.IdxRank.card_quot_range | exact GlobalTheory.IdxRank.card_quot_range | (intros; apply GlobalTheory.IdxRank.card_quot_range <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsIwVec {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (θ : Fin n → kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin n) k) V) (v : V) : Prop :=
  (∀ h ∈ KO k (Fin n), (∀ i j, j < i → valuation k (h.val i j) < 1) →
    (∀ i, valuation k (h.val i i - 1) < 1) → π h v = v) ∧
  ∀ t ∈ torusO k (Fin n), π (diagT k (Fin n) t) v = (torusChar θ t : ℂ) • v

end GlobalTheory.TameIwahori
end
end

section

open ValuativeRel Matrix

namespace GlobalTheory.IwEq

theorem iwahori_eq_glnLocal_iwahori : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : ℕ),
    GlobalTheory.SmGL.iwahori k (Fin a) = GroundTheory.Automorphic.GLnLocal.iwahori k a := by
  intro k _ _ _ _ a
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]
      intro i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply]
      exact hu i j hij
    · ext i j
      rfl
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel]
      intro i j hij
      have h := hu i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply] at h
      exact h
    · ext i j
      rfl

end GlobalTheory.IwEq
end

section

open Matrix

theorem _root_.GlobalTheory.T.finite_skewHermitian_valuationMax_quot_sum : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (r : ℕ) (e : Fin r → ℕ), Finite (↥(GlobalTheory.Hk3.GramSep.gam σ ϖ e) ⧸
    (GlobalTheory.Hk3.GramSep.gam0 σ ϖ e).addSubgroupOf (GlobalTheory.Hk3.GramSep.gam σ ϖ e)) := by
  first | exact @GlobalTheory.Hk3.GramSep.gam_quot_finite | exact GlobalTheory.Hk3.GramSep.gam_quot_finite | (intros; apply GlobalTheory.Hk3.GramSep.gam_quot_finite <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.trace_skewHermitian_gram_integral_alt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam0 σ ϖ e →
  δ * Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.GramSep.trace_skewHermitian_gram_integral | exact GlobalTheory.Hk3.GramSep.trace_skewHermitian_gram_integral | (intros; apply GlobalTheory.Hk3.GramSep.trace_skewHermitian_gram_integral <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.one_add_maximal_matrix_integral_inverse : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (X : Matrix (Fin n) (Fin n) L), (∀ i j, Valued.v (X i j) < 1) →
  ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧ ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.one_add_maximal_inv_int | exact GlobalTheory.Hk3.one_add_maximal_inv_int | (intros; apply GlobalTheory.Hk3.one_add_maximal_inv_int <;> assumption)
end
