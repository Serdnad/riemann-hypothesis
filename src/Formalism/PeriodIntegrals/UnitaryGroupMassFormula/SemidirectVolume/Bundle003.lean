module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
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

@[expose] public section

section

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem continuous_lin [IsTopologicalRing (R ⊗[F] E)] (x : Fin n → R ⊗[F] E) :
    Continuous fun g : HA R σ J => lin R σ J g x := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  simp only [lin, Matrix.mulVecLin_apply]
  exact hm.matrix_mulVec continuous_const

theorem exists_proj_mat (K : Submodule E (Fin n → E)) :
    ∃ P : Matrix (Fin n) (Fin n) E, (∀ x, P *ᵥ x ∈ K) ∧ ∀ x ∈ K, P *ᵥ x = x := by
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl K
  refine ⟨LinearMap.toMatrix' (K.subtype ∘ₗ Submodule.linearProjOfIsCompl K K' hK), fun x => ?_, fun x hx => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    exact (Submodule.linearProjOfIsCompl K K' hK x).2
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply]
    have := Submodule.linearProjOfIsCompl_apply_left hK ⟨x, hx⟩
    exact congrArg Subtype.val this

variable {R}

theorem ratV_mem_spanR {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Y '' s)) : ratV (F := F) R x ∈ spanR (F := F) R Y s := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    have h0 : ratV (F := F) R (0 : Fin n → E) = 0 := by
      funext i
      simp [ratV]
    rw [h0]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have h0 : ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
      funext i
      simp [ratV]
    rw [h0]
    exact add_mem hx hy
  | smul c x _ hx =>
    have h0 : ratV (F := F) R (c • x) = inclR (F := F) R c • ratV (F := F) R x := by
      funext i
      simp [ratV]
    rw [h0]
    exact Submodule.smul_mem _ _ hx

theorem ratV_mulVec (P : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratV (F := F) R (P *ᵥ x) = (P.map (inclR (F := F) R)) *ᵥ ratV (F := F) R x := by
  funext i

  simp [ratV, Matrix.mulVec, dotProduct, map_sum]

theorem mem_spanR_iff {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m))
    (P : Matrix (Fin n) (Fin n) E) (hP1 : ∀ x, P *ᵥ x ∈ Submodule.span E (Y '' s))
    (hP2 : ∀ x ∈ Submodule.span E (Y '' s), P *ᵥ x = x) (v : Fin n → R ⊗[F] E) :
    v ∈ spanR (F := F) R Y s ↔ (P.map (inclR (F := F) R)) *ᵥ v = v := by
  have hfix : ∀ a ∈ s, (P.map (inclR (F := F) R)) *ᵥ ratV (F := F) R (Y a) = ratV (F := F) R (Y a) := by
    intro a ha
    rw [← ratV_mulVec, hP2 _ (Submodule.subset_span ⟨a, ha, rfl⟩)]
  have hsingle : ∀ j : Fin n, ratV (F := F) R (Pi.single j (1 : E)) = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      simp [ratV]
    · simp [ratV, Pi.single_apply, hij]
  constructor
  · intro hv
    have hle : spanR (F := F) R Y s ≤ LinearMap.eqLocus (Matrix.mulVecLin (P.map (inclR (F := F) R))) LinearMap.id := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      exact hfix a ha
    exact hle hv
  · intro h
    rw [← h]
    have hv : v = ∑ j, v j • Pi.single j (1 : R ⊗[F] E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ ?_
    have := ratV_mem_spanR (F := F) (R := R) Y s _ (hP1 (Pi.single j 1))
    rwa [ratV_mulVec, hsingle] at this

theorem isClosed_spanR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) :
    IsClosed (spanR (F := F) R Y s : Set (Fin n → R ⊗[F] E)) := by
  obtain ⟨P, h1, h2⟩ := exists_proj_mat (Submodule.span E (Y '' s))
  have hset : (spanR (F := F) R Y s : Set (Fin n → R ⊗[F] E)) =
      {v | (P.map (inclR (F := F) R)) *ᵥ v = v} := by
    ext v
    exact mem_spanR_iff (F := F) (R := R) Y s P h1 h2 v
  rw [hset]
  exact isClosed_eq (continuous_const.matrix_mulVec continuous_id) continuous_id

variable (R)

theorem isClosed_stabT [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {a : ℕ}
    (X : Fin a → Fin n → E) : IsClosed (stabT R σ J X : Set (HA R σ J)) := by
  have hset : (stabT R σ J X : Set (HA R σ J)) =
      ⋂ b, {g | lin R σ J g (ratV (F := F) R (X b)) = ratV (F := F) R (X b)} := by
    ext g
    simp [mem_stabT]
  rw [hset]
  exact isClosed_iInter fun b => isClosed_eq (continuous_lin R σ J _) continuous_const

end Gen

end PI.VolSemiDirect.W
end
end

section

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {A : Type} [CommRing A] [Algebra F A]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def Bf (u v : Fin M → A ⊗[F] E) : A := Algebra.trace A (A ⊗[F] E) (hR A σ J u v)

theorem sigR_algebraMap (c : A) :
    sigR A σ (algebraMap A (A ⊗[F] E) c) = algebraMap A (A ⊗[F] E) c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

theorem trace_algebraMap_mul (c : A) (y : A ⊗[F] E) :
    Algebra.trace A (A ⊗[F] E) (algebraMap A (A ⊗[F] E) c * y) =
      c * Algebra.trace A (A ⊗[F] E) y := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem Bf_smul_left (c : A) (u v : Fin M → A ⊗[F] E) : Bf σ J (c • u) v = c * Bf σ J u v := by
  have h : hR A σ J (c • u) v = algebraMap A (A ⊗[F] E) c * hR A σ J u v := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold Bf
  rw [h, trace_algebraMap_mul]

theorem Bf_smul_right (c : A) (u v : Fin M → A ⊗[F] E) : Bf σ J u (c • v) = c * Bf σ J u v := by
  have h : hR A σ J u (c • v) = algebraMap A (A ⊗[F] E) c * hR A σ J u v := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold Bf
  rw [h, trace_algebraMap_mul]

theorem Bf_sum_left {k : ℕ} (x : Fin k → Fin M → A ⊗[F] E) (v : Fin M → A ⊗[F] E) :
    Bf σ J (∑ a, x a) v = ∑ a, Bf σ J (x a) v := by
  have h : hR A σ J (∑ a, x a) v = ∑ a, hR A σ J (x a) v := by

    simp only [hR, Formalism.UG.hform, Finset.sum_apply, _root_.map_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  unfold Bf

  rw [h, _root_.map_sum]

theorem Bf_sum_right {k : ℕ} (u : Fin M → A ⊗[F] E) (y : Fin k → Fin M → A ⊗[F] E) :
    Bf σ J u (∑ a, y a) = ∑ a, Bf σ J u (y a) := by
  have h : hR A σ J u (∑ a, y a) = ∑ a, hR A σ J u (y a) := by
    simp only [hR, Formalism.UG.hform, Finset.sum_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  unfold Bf

  rw [h, _root_.map_sum]

theorem Bf_expand {k : ℕ} (b : Fin k → Fin M → A ⊗[F] E) (x y : Fin k → A) :
    Bf σ J (∑ a, x a • b a) (∑ c, y c • b c) = ∑ a, ∑ c, x a * (Bf σ J (b a) (b c) * y c) := by
  rw [Bf_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Bf_smul_left, Bf_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Bf_smul_right]
  ring

theorem Bf_lin (g : HA A σ J) (u v : Fin M → A ⊗[F] E) :
    Bf σ J (lin A σ J g u) (lin A σ J g v) = Bf σ J u v := by
  have hf : ∀ x y : Fin M → A ⊗[F] E, hR A σ J x y =
      dotProduct (Matrix.vecMul (fun i => sigR A σ (x i)) (JR A J)) y := by
    intro x y
    simp only [hR, Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
    exact Finset.sum_comm
  have hs : ∀ (P : Matrix (Fin M) (Fin M) (A ⊗[F] E)) (x : Fin M → A ⊗[F] E),
      (fun i => sigR A σ (P.mulVec x i)) =
        Matrix.vecMul (fun i => sigR A σ (x i)) (Formalism.UG.cT (sigR A σ) P) := by
    intro P x
    funext j

    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.map_apply, _root_.map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hg : (HA.mat A σ J g) ∈ HR A σ J := (show ↥(HR A σ J) from g).2
  have hg' : Formalism.UG.cT (sigR A σ) ((HA.mat A σ J g : GL (Fin M) (A ⊗[F] E)) : Matrix _ _ _) * JR A J *
      ((HA.mat A σ J g : GL (Fin M) (A ⊗[F] E)) : Matrix _ _ _) = JR A J := hg
  unfold Bf lin
  congr 1
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hf, hf, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg']

end Alg

end PI.VolSemiDirect.W.Cj
end
end

section

noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct Matrix

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def sigRLin : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : R →ₗ[R] R) σ.toLinearMap

theorem sigRLin_eq (x : R ⊗[F] E) : sigRLin R σ x = sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigRLin, sigR]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

variable [IsTopologicalRing (R ⊗[F] E)]

theorem continuous_sigR : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (sigRLin R σ) := IsModuleTopology.continuous_of_linearMap _
  have he : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = sigRLin R σ :=
    funext fun x => (sigRLin_eq R σ x).symm
  rw [he]
  exact hc

theorem continuous_hR {X : Type} [TopologicalSpace X] {u v : X → Fin M → R ⊗[F] E}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => hR R σ J (u x) (v x) := by
  unfold hR Formalism.UG.hform
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_sigR R σ).comp ((continuous_apply i).comp hu)).mul continuous_const).mul
    ((continuous_apply j).comp hv)

theorem continuous_linear_action {X : Type} [TopologicalSpace X] {g : X → HA R σ J}
    {v : X → Fin M → R ⊗[F] E} (hg : Continuous g) (hv : Continuous v) :
    Continuous fun x => lin R σ J (g x) (v x) := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  unfold lin
  simp only [Matrix.mulVecLin_apply]
  exact (hm.comp hg).matrix_mulVec hv

end Cont

section HAcont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem mat_inv_eq (hJ : IsHermND σ J) (g : HA R σ J) :
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J⁻¹).map (inclR (F := F) R) *
        Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J := by
  obtain ⟨_, hdet⟩ := hJ
  set A : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
    ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) with hA
  set B : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) with hB
  set Ji : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (J⁻¹).map (inclR (F := F) R) with hJi
  have hmem : Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * A = JR (F := F) R J := g.2
  have hAB : A * B = 1 := by
    have e : (HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) = (HA.mat R σ J g)⁻¹ := by
      first
        | rfl
        | exact Subgroup.coe_inv _
    rw [hA, hB, e]
    exact Units.mul_inv _
  have hJJ : Ji * JR (F := F) R J = 1 := by
    rw [hJi]
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hdet)]
    simp
  calc B = (Ji * JR (F := F) R J) * B := by rw [hJJ, Matrix.one_mul]
    _ = Ji * (Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * A) * B := by rw [hmem]
    _ = Ji * Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * (A * B) := by simp only [Matrix.mul_assoc]
    _ = Ji * Formalism.UG.cT (sigR R σ) A * JR (F := F) R J := by rw [hAB, Matrix.mul_one]

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]

theorem continuous_into_HA (hJ : IsHermND σ J) {X : Type} [TopologicalSpace X] {f : X → HA R σ J}
    (hf : Continuous fun x => ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E))) : Continuous f := by
  have hcT : Continuous fun x => Formalism.UG.cT (sigR R σ)
      ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    refine continuous_matrix fun i j => ?_
    exact (continuous_sigR R σ).comp (hf.matrix_elem j i)
  have hI : Continuous fun x =>
      ((HA.mat R σ J (f x)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    have e : (fun x =>
        ((HA.mat R σ J (f x)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) =
        fun x => (J⁻¹).map (inclR (F := F) R) *
          Formalism.UG.cT (sigR R σ) ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :
            Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J :=
      funext fun x => mat_inv_eq hJ (f x)
    rw [e]
    exact (continuous_const.matrix_mul hcT).matrix_mul continuous_const
  have hGL : Continuous fun x => (HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :=
    Units.continuous_iff.2 ⟨hf, hI⟩
  first
    | exact continuous_induced_rng.2 hGL
    | exact hGL.subtype_mk fun x => (f x).2

end HAcont

section Raw

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

end Raw

end PI.VolSemiDirect.W.Md
end
end

section

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def HasStableRangeOne (A : Type) [CommRing A] : Prop :=
  ∀ a b x y : A, a * x + b * y = 1 → ∃ t, IsUnit (a + t * b)

def AdeleStableRankOne : Prop := ∀ (F : Type) [Field F] [NumberField F], HasStableRangeOne (AF F)

def ElimSR1 : Prop :=
  ∀ (A : Type) [CommRing A], HasStableRangeOne A → ∀ (k : ℕ) (X : GL (Fin k) A),
    X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})

def TransvHaar : Prop :=
  ∀ (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A] (k : ℕ)
    (i j : Fin k), i ≠ j → ∀ (c : A) (μ : Measure (Fin k → A)), μ.IsAddHaarMeasure →
      μ.map (Matrix.mulVec (Matrix.transvection i j c)) = μ

def OrthInv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (G X : Matrix (Fin k) (Fin k) (AF F)),
    IsUnit G.det → X.transpose * G * X = G →
    ∀ μ : Measure (Fin k → AF F), μ.IsAddHaarMeasure → μ.map (Matrix.mulVec X) = μ

def VMod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (g : HA (AF F) σ J) (μ : Measure (Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure →
      μ.map (lin (AF F) σ J g) = μ

end PI.VolSemiDirect.W.Cj
end
end

section

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

def TraceBase : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E),
    Algebra.trace R (R ⊗[F] E) (hR R σ J (ratV (F := F) R x) (ratV (F := F) R y)) =
      algebraMap F R (Algebra.trace F E (hE σ J x y))

def TraceGramND : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (k : ℕ) (b : Module.Basis (Fin k) F (Fin M → E)),
      (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))).det ≠ 0

end PI.VolSemiDirect.W.Cj
end
end

section

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem stabilizer_fixes_frame_vector {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P) (a : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [S0, mem_stabT] at hg
  have := hg (Fin.castSucc a)
  simpa [F0, Fin.snoc_castSucc] using this

end Gen

end PI.VolSemiDirect.W
end
end
