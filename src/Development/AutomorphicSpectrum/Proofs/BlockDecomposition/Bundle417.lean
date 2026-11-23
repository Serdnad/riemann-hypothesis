module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle401
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle402
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

@[expose] public section

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.CapProdProof

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.RgCOBlock (fa fb sz)

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem commute_ev (T : Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ p q, Commute T (E p q))
    (z : FreeAlgebra ℂ (Fin n × Fin n)) : Commute T (CompanionTheory.D.LK.ev E z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r T).symm
  | grade1 p => simpa [CompanionTheory.D.LK.ev] using h p.1 p.2
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add (f := _)]; exact ha.add_right hb

end GlobalTheory.CompanionTheory.PairMult.CapProdProof
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.archimedean_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    κ.map (piInf τ) * (κ.map (piInf τ))ᴴ = 1 → ∀ f e : Fin n → ι,
    ‖piInf τ ((X.1 * κ).submatrix f e).det‖₊ ≤ (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf | exact GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf | (intros; apply GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.denominator_bound_by_height : ∀ (F : Type) [Field F] [NumberField F] (y : F), ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ ∏ᶠ v : Pl (F := F), max 1 ‖algebraMap F (Fv F v) y‖₊ ∧
    IsIntegral ℤ ((m : F) * y) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.Den.denominator_le | exact GlobalTheory.CompanionTheory.GodementH.Den.denominator_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.Den.denominator_le <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.finite_place_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl (F := F)) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    (∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) → ∀ f e : Fin n → ι,
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | exact GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.quadratic_integral_coefficients_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl (F := F)) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes | exact GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes | (intros; apply GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Flow

section Abstract

variable {A : Type} [Ring A] [Algebra ℂ A]

def HD (f f' : ℝ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (p p' : ι → ℝ → ℂ) (C : ι → A),
    (∀ i s, HasDerivAt (p i) (p' i s) s) ∧ (∀ s, f s = ∑ i, p i s • C i) ∧ ∀ s, f' s = ∑ i, p' i s • C i

theorem HD.congr {f f' g g' : ℝ → A} (h : HD f f') (e : ∀ s, g s = f s) (e' : ∀ s, g' s = f' s) : HD g g' := by
  obtain ⟨ι, i, p, p', C, h1, h2, h3⟩ := h
  exact ⟨ι, i, p, p', C, h1, fun s => (e s).trans (h2 s), fun s => (e' s).trans (h3 s)⟩

theorem HD.const (C : A) : HD (fun _ => C) (fun _ => 0) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ _ => 0, fun _ => C, fun _ s => hasDerivAt_const s 1, by simp, by simp⟩

theorem HD.add {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s + g s) (fun s => f' s + g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim p q, Sum.elim p' q', Sum.elim C D, ?_, ?_, ?_⟩
  · rintro (i | j) s
    · exact h1 i s
    · exact k1 j s
  · intro s; simp [h2, k2]
  · intro s; simp [h3, k3]

theorem HD.mul {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s * g s) (fun s => f' s * g s + f s * g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι × κ, inferInstance, fun x s => p x.1 s * q x.2 s,
    fun x s => p' x.1 s * q x.2 s + p x.1 s * q' x.2 s, fun x => C x.1 * D x.2, ?_, ?_, ?_⟩
  · intro x s; exact (h1 x.1 s).mul (k1 x.2 s)
  · intro s
    simp only [h2, k2, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm]
  · intro s
    simp only [h2, h3, k2, k3, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm, add_smul,
      Finset.sum_add_distrib]

theorem HD.const_of_zero {f : ℝ → A} (h : HD f (fun _ => 0)) (l : A →ₗ[ℂ] ℂ) (s t : ℝ) : l (f s) = l (f t) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  have hd : ∀ s, HasDerivAt (fun s => l (f s)) 0 s := by
    intro s
    have h4 : HasDerivAt (fun s => ∑ i, p i s * l (C i)) (∑ i, p' i s * l (C i)) s :=
      HasDerivAt.fun_sum fun i _ => (h1 i s).mul_const _
    have e1 : (fun s => l (f s)) = fun s => ∑ i, p i s * l (C i) := by
      funext s; simp [h2, map_sum]
    have e2 : ∑ i, p' i s * l (C i) = 0 := by
      have := congrArg l (h3 s)

      simpa [map_sum] using this.symm
    rw [e1]
    rwa [e2] at h4
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) s t

theorem hd_adjoin (R Q : ℝ → A) (hRQ : ∀ s, R s * Q s = 1) (hQR : ∀ s, Q s * R s = 1) (L : A) (G : Set A)
    (hG : ∀ B ∈ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s)) :
    ∀ B ∈ Algebra.adjoin ℂ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s) := by
  have hmul : ∀ s x y, R s * x * Q s * (R s * y * Q s) = R s * (x * y) * Q s := by
    intro s x y
    calc R s * x * Q s * (R s * y * Q s) = R s * x * (Q s * R s) * y * Q s := by simp only [mul_assoc]
      _ = R s * (x * y) * Q s := by rw [hQR]; simp only [mul_assoc, mul_one]
  intro B hB
  induction hB using Algebra.adjoin_induction with
  | mem x hx => exact hG x hx
  | algebraMap r =>
    refine (HD.const (algebraMap ℂ A r)).congr (fun s => ?_) (fun s => ?_)
    · rw [← Algebra.commutes, mul_assoc, hRQ, mul_one]
    · rw [Algebra.commutes, sub_self]; simp
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr (fun s => ?_) (fun s => ?_)
    · noncomm_ring
    · noncomm_ring
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr (fun s => ?_) (fun s => ?_)
    · rw [hmul]
    · rw [hmul, hmul, ← add_mul, ← mul_add]
      congr 2
      noncomm_ring

end Abstract

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem Zalg_le : Zalg E a ≤ Algebra.adjoin ℂ (Set.range (lie E a)) := by
  set S := Algebra.adjoin ℂ (Set.range (lie E a)) with hSdef
  have hL : ∀ X, lie E a X ∈ S := fun X => Algebra.subset_adjoin ⟨X, rfl⟩
  have hS : ∀ i j x, lieS E a i j x ∈ S := fun i j x => by rw [lieS_apply]; exact hL _
  have hE : ∀ (τ : E →+* ℂ) i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hS _ _ _) (S.smul_mem (hS _ _ _) _)) _
  refine Algebra.adjoin_le ?_
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem hd_lie {F F' : ℝ → Lie E a} (h : ∀ s, HasDerivAt F (F' s) s) :
    HD (fun s => lie E a (F s)) (fun s => lie E a (F' s)) := by
  classical
  let b := Module.finBasis ℝ (Lie E a)
  have hsum : ∀ X : Lie E a, lie E a X = ∑ m, ((b.repr X m : ℝ) : ℂ) • lie E a (b m) := by
    intro X
    conv_lhs => rw [← b.sum_repr X]

    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul]
    exact (algebraMap_smul ℂ _ _).symm
  refine ⟨_, inferInstance, fun m s => ((b.repr (F s) m : ℝ) : ℂ), fun m s => ((b.repr (F' s) m : ℝ) : ℂ),
    fun m => lie E a (b m), fun m s => ?_, fun s => hsum _, fun s => hsum _⟩
  have hl := (LinearMap.toContinuousLinearMap (b.coord m)).hasFDerivAt.comp_hasDerivAt s (h s)
  exact hl.ofReal_comp

theorem hasDerivAt_matMul {u v : ℝ → Lie E a} {u' v' : Lie E a} {s : ℝ} (hu : HasDerivAt u u' s)
    (hv : HasDerivAt v v' s) :
    HasDerivAt (fun t => toL (Matrix.of (u t) * Matrix.of (v t)))
      (toL (Matrix.of u' * Matrix.of (v s) + Matrix.of (u s) * Matrix.of v')) s := by
  rw [hasDerivAt_pi] at hu hv ⊢
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hu' := fun k => (hasDerivAt_pi.1 (hu i)) k
  have hv' := fun k => (hasDerivAt_pi.1 (hv k)) j
  have := HasDerivAt.fun_sum (u := Finset.univ) fun k (_ : k ∈ Finset.univ) => (hu' k).mul (hv' k)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using this

theorem zalg_comm_rt_curve : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g)) → ∀ z : Module.End ℂ (Sm E a), z ∈ Zalg E a → (∀ X : Lie E a, z * lie E a X = lie E a X * z) → ∀ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 → (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) → (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) → z * rt E a (infGL E a (c 1)) = rt E a (infGL E a (c 1)) * z := by
  intro E _ _ _ a hconj z hz hcomm c Y h0 hc hci
  let R : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s))
  let Q : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s)⁻¹)
  have hRQ : ∀ s, R s * Q s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hQR : ∀ s, Q s * R s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hconj' : ∀ s X, R s * lie E a X * Q s =
      lie E a (toL ((c s).val * Matrix.of X * ((c s)⁻¹).val)) := by
    intro s X
    change rt E a (infGL E a (c s)) * lie E a X * Q s = _
    rw [hconj (c s) X, mul_assoc]
    rw [show rt E a (infGL E a (c s)) * Q s = 1 from hRQ s, mul_one]
  have hG : ∀ B ∈ Set.range (lie E a), HD (fun s => R s * B * Q s)
      (fun s => R s * (lie E a Y * B - B * lie E a Y) * Q s) := by
    rintro _ ⟨X, rfl⟩
    let W : Lie E a := toL (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y)
    have hW : lie E a Y * lie E a X - lie E a X * lie E a Y = lie E a W := by
      rw [lie_comm]
      exact (map_sub (lie E a) _ _).symm
    refine (hd_lie (F := fun s => toL ((c s).val * Matrix.of X * ((c s)⁻¹).val))
      (F' := fun s => toL ((c s).val * Matrix.of W * ((c s)⁻¹).val)) fun s => ?_).congr
      (fun s => hconj' s X) (fun s => by rw [hW]; exact hconj' s W)
    have h1 := hasDerivAt_matMul (hc s) (hasDerivAt_const s X)
    have h2 := hasDerivAt_matMul h1 (hci s)
    refine HasDerivAt.congr_deriv h2 ?_
    change toL (((c s).val * Matrix.of Y * Matrix.of X + (c s).val * 0) * ((c s)⁻¹).val +
      ((c s).val * Matrix.of X) * (-(Matrix.of Y * ((c s)⁻¹).val))) =
      toL ((c s).val * (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y) * ((c s)⁻¹).val)
    congr 1
    noncomm_ring
  have h := hd_adjoin R Q hRQ hQR (lie E a Y) _ hG z (Zalg_le hz)
  have h' : HD (fun s => R s * z * Q s) (fun _ => 0) :=
    h.congr (fun _ => rfl) fun s => by rw [hcomm Y, sub_self, mul_zero, zero_mul]
  let l : Sm E a → GA E a → (Module.End ℂ (Sm E a) →ₗ[ℂ] ℂ) := fun φ x =>
    { toFun := fun B => (B φ).1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have e1 : R 1 * z * Q 1 = R 0 * z * Q 0 :=
    LinearMap.ext fun φ => Subtype.ext <| funext fun x => h'.const_of_zero (l φ x) 1 0
  have hR0 : R 0 = 1 := by
    change rt E a (infGL E a (c 0)) = 1
    rw [h0, map_one, map_one]
  have hQ0 : Q 0 = 1 := by
    change rt E a (infGL E a (c 0)⁻¹) = 1
    rw [h0, inv_one, map_one, map_one]
  rw [hR0, hQ0, one_mul, mul_one] at e1
  change z * R 1 = R 1 * z
  calc z * R 1 = R 1 * z * Q 1 * R 1 := by rw [e1]
    _ = R 1 * z * (Q 1 * R 1) := by simp only [mul_assoc]
    _ = R 1 * z := by rw [hQR, mul_one]

end GlobalTheory.CompanionTheory.SmoothRep.Flow
end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.center_commutes_lie_action : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X, z * lie E a X = lie E a X * z := by
  first | exact @GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie | exact GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie | (intros; apply GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem Zalg_comm_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z :=
  GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

theorem _root_.GlobalTheory.T.lie_central_element_trace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  exact @GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.casimir_signature_mem_center : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Z : ι → GlobalTheory.CuspRep.Lie E a) (K : Finset ι), Submodule.span ℝ (Set.range Z) = ⊤ ∧ (∀ κ ∈ K, (Matrix.of (Z κ))ᴴ = -(Matrix.of (Z κ))) ∧ (∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ)) ∈ Zalg E a := by
  first | exact @GlobalTheory.CompanionTheory.CasFamily.exists_family | exact GlobalTheory.CompanionTheory.CasFamily.exists_family | (intros; apply GlobalTheory.CompanionTheory.CasFamily.exists_family <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem rt_infGL_mul_lie (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (g : GL (Fin a) (Cinf E)) (X : Lie E a) :
    rt E a (infGL E a g) * lie E a X =
      lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  refine LinearMap.ext fun ψ => Subtype.ext <| funext fun x => ?_
  have hd : DifferentiableAt ℝ (chart ψ.1 x) (toL g.val) :=
    (contDiffAt_chart ψ.2 x (val_mem_invSet g)).differentiableAt (by simp)
  have e1 : lmul (toL g.val) (oneL E a) = toL g.val := mul_one g.val
  have e2 : rmul (toL g.val) (oneL E a) = toL g.val := one_mul g.val
  have e3 : lmul (toL g.val) X = rmul (toL g.val) (toL (g.val * Matrix.of X * (g⁻¹).val)) := by
    change g.val * Matrix.of X = g.val * Matrix.of X * (g⁻¹).val * g.val
    rw [mul_assoc (g.val * Matrix.of X), ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  change fderiv ℝ (chart ψ.1 (x * infGL E a g)) (oneL E a) X =
    fderiv ℝ (chart (fun y => ψ.1 (y * infGL E a g)) x) (oneL E a)
      (toL (g.val * Matrix.of X * (g⁻¹).val))
  rw [chart_mul, chart_rt_inf,
    fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL g.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL g.val)).differentiableAt,
    e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [e3]

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.one_parameter_subgroup_exists : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a), ∃ c : ℝ → GL (Fin a) (Cinf E), Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => toL (c t).val) X 0 ∧ ((Matrix.of X)ᴴ = -(Matrix.of X) → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  first | exact @GlobalTheory.CompanionTheory.LieCurve.exists_curve | exact GlobalTheory.CompanionTheory.LieCurve.exists_curve | (intros; apply GlobalTheory.CompanionTheory.LieCurve.exists_curve <;> assumption)
end
