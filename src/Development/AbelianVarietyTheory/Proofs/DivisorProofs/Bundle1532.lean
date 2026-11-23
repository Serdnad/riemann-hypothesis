module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DiagLagr

def fold (n : ℕ) (i : Fin (n + n)) : Fin n := Sum.elim id id (finSumFinEquiv.symm i)

theorem diagCols_mul {A : Type} [CommRing A] {n m : ℕ} (u : Matrix (Fin n) (Fin m) A) :
    ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id) * u =
      u.submatrix (fold n) id := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i <;>
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, fold, Equiv.symm_apply_apply] <;>
    simp [diagCols, Matrix.one_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_fold (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (JB : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) (u v : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)) :
    hTens (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)ᵀ) JB (u.submatrix (fold n) id)
      (v.submatrix (fold n) id) = 0 := by
  simp only [hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.submatrix_apply, fold,
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG, incM, Matrix.map_apply, Matrix.transpose_apply, Matrix.reindex_apply,
    Equiv.symm_apply_apply, id]
  simp [dbl]

def repL (F : Type) [Field F] [NumberField F] [Algebra F E] (n m : ℕ) :
    Matrix (Fin n) (Fin m) E →ₗ[F] Matrix (Fin (n + n)) (Fin m) (AF F ⊗[F] E) where
  toFun x := (incM F x).submatrix (fold n) id
  map_add' x y := by ext i j; simp [incM]
  map_smul' a x := by
    ext i j
    simp [incM, inclR, TensorProduct.tmul_smul]

theorem repL_injective (n m : ℕ) : Function.Injective (repL (E := E) F n m) := by
  intro x y h
  have : Nontrivial (AF F) :=
    (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).nontrivial
  have hi : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    have : Nontrivial (AF F ⊗[F] E) :=
      (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E)
        (algebraMap F E).injective).nontrivial
    exact RingHom.injective _
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j
  simp only [repL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, fold, Equiv.symm_apply_apply, incM,
    Matrix.map_apply, Sum.elim_inl, id] at this
  exact hi this

theorem exists_diag_lagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
    (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card κ ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E),
        co.e (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) = t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ κ _ co hrat
  have hinj := NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F
  have : Nontrivial (AF F) := hinj.nontrivial
  let i1 : (κ → F) →ₗ[F] (κ → AF F) := (Algebra.linearMap F (AF F)).compLeft κ
  let ι : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F)) := i1.prodMap i1
  have hι : ∀ w, ι w = ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) :=
    fun _ => rfl
  have hιi : Function.Injective ι := by
    intro a b h
    rw [hι, hι, Prod.mk.injEq] at h
    exact Prod.ext (funext fun i => hinj (congrFun h.1 i)) (funext fun i => hinj (congrFun h.2 i))
  let g : Matrix (Fin nT) (Fin nS) E →ₗ[F] ((κ → AF F) × (κ → AF F)) :=
    (co.e.toLinearMap.restrictScalars F) ∘ₗ repL F nT nS
  have hg : ∀ x, g x = co.e ((incM F x).submatrix (fold nT) id) := fun _ => rfl
  have hgi : Function.Injective g := co.e.injective.comp (repL_injective nT nS)
  have hle : LinearMap.range g ≤ LinearMap.range ι := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat (x.submatrix (fold nT) id)
    exact ⟨(y, z), h.symm⟩
  refine ⟨(LinearMap.range g).comap ι, ?_, ?_, ?_⟩
  · rintro a ⟨x, hx⟩ b ⟨x', hx'⟩
    have h := co.form ((incM F x).submatrix (fold nT) id) ((incM F x').submatrix (fold nT) id)
    rw [symp, hTens_fold, mul_zero, map_zero, ← hg, ← hg, hx, hx', hι, hι, eq_comm, sub_eq_zero] at h
    apply hinj

    simpa only [dotProduct, map_sum, map_mul] using h
  · have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have h1 : Module.finrank F ((LinearMap.range g).comap ι) = nT * nS * Module.finrank F E := by
      rw [(Submodule.equivMapOfInjective ι hιi _).finrank_eq, Submodule.map_comap_eq_of_le hle,
        LinearMap.finrank_range_of_inj hgi, Module.finrank_matrix]
      simp
    have h2 := co.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h2
    simp only [Fintype.card_fin] at h2
    rw [h1]
    nlinarith [h2]
  · rintro t w ⟨x, hx⟩
    refine ⟨t • incM F x, ?_⟩
    rw [← hι, ← hx, hg, diagCols_mul, ← map_smul]
    rfl

end GlobalTheory.WeilSchrodinger.DiagLagr

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DiagEmbU

section Gen

variable {A : Type} [CommRing A] {n : ℕ}

def dg (M : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + n)) (Fin (n + n)) A :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 1)

theorem dg_mul (M N : Matrix (Fin n) (Fin n) A) : dg (M * N) = dg M * dg N := by
  simp only [dg, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem dg_one : dg (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  simp [dg, Matrix.fromBlocks_one]

theorem dg_sub_one_apply (M : Matrix (Fin n) (Fin n) A) (i j : Fin (n + n)) :
    (dg M - 1) i j = Sum.elim (fun a => Sum.elim (fun b => (M - 1) a b) (fun _ => 0)) (fun _ _ => 0)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [← dg_one]
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp

theorem det_dg (M : Matrix (Fin n) (Fin n) A) : (dg M).det = M.det := by
  rw [dg, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem continuous_dg [TopologicalSpace A] : Continuous (dg (A := A) (n := n)) :=
  (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const continuous_const).matrix_reindex _ _

def dgHom : Matrix (Fin n) (Fin n) A →* Matrix (Fin (n + n)) (Fin (n + n)) A where
  toFun := dg
  map_one' := dg_one
  map_mul' := dg_mul

def diagGL : GL (Fin n) A →* GL (Fin (n + n)) A := Units.map (dgHom (A := A) (n := n))

theorem continuous_diagGL [TopologicalSpace A] : Continuous (diagGL (A := A) (n := n)) :=
  Continuous.units_map _ continuous_dg

theorem dg_map {B : Type} [CommRing B] (φ : A →+* B) (M : Matrix (Fin n) (Fin n) A) :
    (dg M).map φ = dg (M.map φ) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp [Matrix.one_apply]

theorem bc_diagGL {B : Type} [CommRing B] (φ : A →+* B) (g : GL (Fin n) A) :
    Formalism.UG.bc φ (diagGL g) = diagGL (Formalism.UG.bc φ g) := by
  ext : 1
  exact dg_map φ _

theorem cT_dg (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT s (dg M) = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Formalism.UG.cT s M) 0 0 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp [Matrix.one_apply, eq_comm]

theorem diagGL_mem (s : A →+* A) (J K : Matrix (Fin n) (Fin n) A) {g : GL (Fin n) A}
    (hg : g ∈ Formalism.UG.UJ s J) :
    diagGL g ∈ Formalism.UG.UJ s (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks J 0 0 K)) := by
  have hg' : Formalism.UG.cT s (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J := hg
  show Formalism.UG.cT s (dg (g : Matrix (Fin n) (Fin n) A)) * _ * dg (g : Matrix (Fin n) (Fin n) A) = _
  rw [cT_dg, dg]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [hg']

end Gen

end GlobalTheory.DiagEmbU

namespace GlobalTheory.DiagEmbU

open GlobalTheory.WeilSchrodinger.DblTarget

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem JR_dblG (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (JR (F := F) R J) 0 0 (-JR (F := F) R J)) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [JR, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]

theorem dblG_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG J =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks J 0 0 (-J)) := rfl

def diagU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) :=
  ((diagGL (A := AF F ⊗[F] E)).comp (Formalism.IndefR.DatumF.matHomF σ J)).codRestrict
    (HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) fun g => by
      have hg : (show HR (AF F) σ J from g).1 ∈ Formalism.UG.UJ (sigR (AF F) σ) (JR (F := F) (AF F) J) :=
        (show HR (AF F) σ J from g).2
      have := diagGL_mem (sigR (AF F) σ) (JR (F := F) (AF F) J) (-JR (F := F) (AF F) J) hg
      show _ ∈ Formalism.UG.UJ (sigR (AF F) σ) (JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J))
      rw [JR_dblG]
      exact this

theorem mtF_diagU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (h : Formalism.IndefR.DatumF.GAF σ J) :
    Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (diagU σ J h) =
      dg (Formalism.IndefR.DatumF.mtF σ J h) := rfl

end Main

end GlobalTheory.DiagEmbU

namespace GlobalTheory.DiagEmbU

open GlobalTheory.WeilSchrodinger.DblTarget

theorem exists_diagEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      ∃ ι : Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J),
        Continuous ι ∧
        (∀ h, Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ J h) 0 0 1)) ∧
        (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ι γ ∈ Formalism.IndefR.DatumF.GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) ∧
        (∀ e h, Formalism.IndefR.DatumF.SuppAtF σ e J h → Formalism.IndefR.DatumF.SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h)) ∧
        (∀ e h y, Formalism.IndefR.DatumF.IsDetAtF σ e J h y →
          Formalism.IndefR.DatumF.IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) y) := by
  intro F E _ _ _ _ _ σ n J
  refine ⟨diagU σ J, ?_, fun h => mtF_diagU σ J h, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_diagGL.comp continuous_subtype_val) _
  · intro γ hγ
    have h1 : (show HR (AF F) σ J from γ).1 ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.mp hγ
    obtain ⟨γ₀, hγ₀, he⟩ := Subgroup.mem_map.mp h1
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨diagGL γ₀, ?_, ?_⟩)
    · rw [dblG_eq]
      exact diagGL_mem _ J (-J) hγ₀
    · rw [bc_diagGL, he]
      rfl
  · intro e h hs i j
    rw [mtF_diagU]
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [dg_sub_one_apply]
    rcases i with a | a <;> rcases j with b | b <;> simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, mul_zero]
    exact hs a b
  · intro e h y hy
    show (y : Formalism.IndefR.DatumF.AEF F E) = e * (Formalism.IndefR.DatumF.mtF σ _ (diagU σ J h)).det + (1 - e)
    rw [mtF_diagU, det_dg]
    exact hy

end GlobalTheory.DiagEmbU
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.DblThetaProd

theorem tsum_prod_mul {α β : Type} (f : α → ℂ) (g : β → ℂ) :
    ∑' p : α × β, f p.1 * g p.2 = (∑' a, f a) * (∑' b, g b) := by
  by_cases hf : Summable f
  · by_cases hg : Summable g
    · exact (tsum_mul_tsum_of_summable_norm ((summable_norm_iff (E := ℂ)).mpr hf)
        ((summable_norm_iff (E := ℂ)).mpr hg)).symm
    · rw [tsum_eq_zero_of_not_summable hg, mul_zero]
      by_cases h0 : ∀ a, f a = 0
      · simp [h0]
      · push_neg at h0
        obtain ⟨a, ha⟩ := h0
        refine tsum_eq_zero_of_not_summable fun hs => hg ?_
        have h1 : Summable fun b => f a * g b :=
          hs.comp_injective (i := fun b => (a, b)) (fun _ _ h => (Prod.ext_iff.mp h).2)
        simpa [ha] using h1.mul_left (f a)⁻¹
  · rw [tsum_eq_zero_of_not_summable hf, zero_mul]
    by_cases h0 : ∀ b, g b = 0
    · simp [h0]
    · push_neg at h0
      obtain ⟨b, hb⟩ := h0
      refine tsum_eq_zero_of_not_summable fun hs => hf ?_
      have h1 : Summable fun a => f a * g b :=
        hs.comp_injective (i := fun a => (a, b)) (fun _ _ h => (Prod.ext_iff.mp h).1)
      simpa [hb] using h1.mul_right (g b)⁻¹

theorem thetaTr_coDbl_boxFun : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro F E _ _ _ _ _ σ B hB hstd nS nT JT JA JB ξ hA κ _ co φ₁ _ φ₂ _
  have hψ : ∀ x, ‖B.ψ x‖ = 1 := hstd.1.2.1
  have hc : ∀ x, starRingEnd ℂ (B.ψ x) = B.ψ (-x) := fun x => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ x)]
  funext w
  rw [GlobalTheory.DblTargetDelta.deltaT_apply]
  have he : (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co).e w =
      (Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).1 (co.e (GlobalTheory.DblTargetDelta.botR w)).1,
        Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).2 (-(co.e (GlobalTheory.DblTargetDelta.botR w)).2)) := rfl
  have hn : co.e (-GlobalTheory.DblTargetDelta.botR w) = -(co.e (GlobalTheory.DblTargetDelta.botR w)) := map_neg _ _
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, he, hn]
  generalize co.e (GlobalTheory.DblTargetDelta.topR w) = p₁
  generalize co.e (GlobalTheory.DblTargetDelta.botR w) = p₂
  obtain ⟨x₁, y₁⟩ := p₁
  obtain ⟨x₂, y₂⟩ := p₂
  simp only

  set A : (κ → F) → (κ → AdeleRing (𝓞 F) F) := fun b i => algebraMap F (AdeleRing (𝓞 F) F) (b i) with hAdef
  have key : ∀ q : (κ → F) × (κ → F),
      schr B.ψ (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) (boxFun φ₁ φ₂)
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm q i)) =
        schr B.ψ (x₁, y₁) φ₁ (A q.1) *
          (B.ψ (-(A q.2 ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A q.2 + x₂)) := by
    rintro ⟨a, b⟩
    have h1 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inl = A a + x₁ := by
      funext i; simp [hAdef]
    have h2 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inr = A b + x₂ := by
      funext i; simp [hAdef]
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun]
    rw [h1, h2, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr, hAdef]
    ring
  rw [← (Equiv.sumArrowEquivProdArrow κ κ F).symm.tsum_eq]
  refine (tsum_congr key).trans ?_
  refine (tsum_prod_mul (fun a => schr B.ψ (x₁, y₁) φ₁ (A a))
    (fun b => B.ψ (-(A b ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A b + x₂))).trans ?_
  congr 1
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun b => ?_
  have h3 : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.neg (κ → F)) b i)) = -A b := by
    funext i; simp [hAdef]
  simp only [GlobalTheory.WeilM.schr, h3, map_mul, Complex.conj_conj, hc,
    Prod.fst_neg, Prod.snd_neg]
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, neg_add, sub_eq_add_neg, mul_neg]

end GlobalTheory.DblThetaProd

end
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

section General

variable {C : Type} [Ring C] [Algebra ℚ C] {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ C)
  {R : Type} [CommRing R] [Algebra ℚ R] (S : Subring R)

theorem repr_mul_mem (hc : ∀ i j k, algebraMap ℚ R (b.repr (b i * b j) k) ∈ S)
    {y y' : R ⊗[ℚ] C} (hy : ∀ i, (Algebra.TensorProduct.basis R b).repr y i ∈ S)
    (hy' : ∀ i, (Algebra.TensorProduct.basis R b).repr y' i ∈ S) (k : ι) :
    (Algebra.TensorProduct.basis R b).repr (y * y') k ∈ S := by
  set B := Algebra.TensorProduct.basis R b
  have hB : ∀ i j, B.repr (B i * B j) k = algebraMap ℚ R (b.repr (b i * b j) k) := by
    intro i j
    simp [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  rw [← B.sum_repr y, ← B.sum_repr y', Finset.sum_mul_sum]

  simp only [smul_mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
  Finsupp.smul_apply, smul_eq_mul, hB]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.mul_mem (S.mul_mem (hy i) (hy' j)) (hc i j k)

end General

theorem eventually_rat_mem (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (show Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] from
    algebraMap ℚ (AfP p) q).2
  filter_upwards [h] with v hv
  have e : (AfP.eval v) (algebraMap ℚ (AfP p) q) = algebraMap ℚ (Qv v) q := (AfP.eval v).commutes q
  rw [← e]
  exact hv

theorem mul_mem_IntV_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  intro p _ G
  have hall : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k,
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem p _
  filter_upwards [hall] with v hv
  intro a ha a' ha'
  obtain ⟨h1, h2, h3, h4⟩ := ha
  obtain ⟨h1', h2', h3', h4'⟩ := ha'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h1 h1' k
    simpa [IsIntV, basV] using this
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h2' h2 k
    simpa [IsIntV, basV, _root_.mul_inv_rev] using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h3 h3'
    simpa using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h4' h4
    simpa [_root_.mul_inv_rev] using this

end GlobalTheory.OrbFinAf
end
