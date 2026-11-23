module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open scoped Matrix Kronecker

noncomputable section

namespace GlobalTheory

namespace FockEmb

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (fun a => if a.isLeft then (1 : ℂ) else -1) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem reindex_kron_J (p q r s : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Formalism.UG.Jpq p q ⊗ₖ Formalism.UG.Jpq r s) = Formalism.UG.Jpq (p * r + q * s) (p * s + q * r) := by
  rw [Jpq_eq_diagonal, Jpq_eq_diagonal, Jpq_eq_diagonal, Matrix.diagonal_kronecker_diagonal,
    Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨l, rfl⟩ := (lineEquiv p q r s).surjective x
  simp only [Function.comp, Equiv.symm_apply_apply, lineEquiv_isLeft]
  rcases l with ⟨a | a, c | c⟩ <;> simp [linePos]

def kronGL (p q r s : ℕ) :
    GL (Ix p q) ℂ × GL (Ix r s) ℂ →* GL (Ix (p * r + q * s) (p * s + q * r)) ℂ where
  toFun x := Units.map (Matrix.reindexAlgEquiv ℂ ℂ (lineEquiv p q r s)).toMonoidHom
    (Matrix.GeneralLinearGroup.kronecker x.1 x.2)
  map_one' := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.kronecker]
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.kronecker, Matrix.mul_kronecker_mul]

theorem kronGL_val {p q r s : ℕ} (g : GL (Ix p q) ℂ) (h : GL (Ix r s) ℂ) :
    ((kronGL p q r s (g, h) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) =
      Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
        ((g : Mat p q) ⊗ₖ (h : Mat r s)) := rfl

theorem mem_Upq_iff {p q : ℕ} (g : GL (Ix p q) ℂ) :
    g ∈ Formalism.UG.Upq p q ↔ (g : Mat p q)ᴴ * Formalism.UG.Jpq p q * (g : Mat p q) = Formalism.UG.Jpq p q :=
  Iff.rfl

theorem kronGL_mem {p q r s : ℕ} {g : GL (Ix p q) ℂ} {h : GL (Ix r s) ℂ}
    (hg : g ∈ Formalism.UG.Upq p q) (hh : h ∈ Formalism.UG.Upq r s) :
    kronGL p q r s (g, h) ∈ Formalism.UG.Upq (p * r + q * s) (p * s + q * r) := by
  rw [mem_Upq_iff] at *
  rw [kronGL_val, ← reindex_kron_J]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hg, hh]

theorem kronGL_det {p q r s : ℕ} (g : GL (Ix p q) ℂ) (h : GL (Ix r s) ℂ) :
    ((kronGL p q r s (g, h) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)).det =
      (g : Mat p q).det ^ (r + s) * (h : Mat r s).det ^ (p + q) := by
  rw [kronGL_val, Matrix.det_reindex_self, Matrix.det_kronecker]
  simp

end FockEmb


open FockEmb in
theorem exists_cover_tensor_hom :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), ∃ emb : T1.G × T2.G →* T0.G, (∀ g h, ((T0.cov (emb (g, h)) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) = Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Matrix.kroneckerMap (· * ·) ((T1.cov g : GL _ ℂ) : Mat p q) ((T2.cov h : GL _ ℂ) : Mat r s))) ∧ ∀ g h, T0.sq (emb (g, h)) = T1.sq g ^ (r + s) * T2.sq h ^ (p + q) := by
  intro p q r s T0 T1 T2
  have key : ∀ x : T1.G × T2.G, ∃! y : T0.G, T0.cov y = kronGL p q r s (T1.cov x.1, T2.cov x.2) ∧
      T0.sq y = T1.sq x.1 ^ (r + s) * T2.sq x.2 ^ (p + q) := by
    intro x
    apply T0.bij _ (kronGL_mem (T1.cov_mem _) (T2.cov_mem _))
    rw [kronGL_det, ← T1.sq_sq, ← T2.sq_sq]
    push_cast
    ring
  choose f hf huniq using key
  refine ⟨MonoidHom.mk' f ?_, fun g h => ?_, fun g h => (hf (g, h)).2⟩
  · intro x y
    symm
    apply huniq
    constructor
    · rw [map_mul, (hf x).1, (hf y).1, ← map_mul]
      simp
    · rw [map_mul, (hf x).2, (hf y).2]
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
      exact mul_mul_mul_comm _ _ _ _
  · show ((T0.cov (f (g, h)) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) = _
    rw [(hf (g, h)).1]
    rfl

end GlobalTheory
end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.WeightDecomp

lemma comp_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) (S : Finset (Ix p q → ℚ)) :
    ∀ f : (Ix p q → ℚ) → V, (∀ ν, f ν ∈ wtSub act ν) → ∑ ν ∈ S, f ν ∈ N → ∀ ν ∈ S, f ν ∈ N := by
  first
  | exact @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | (apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem ..)

theorem mem_iSup_inf_wtSub : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V),
    (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) →
      x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  intro p q V _ _ act N hN x hx hx'
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have h := comp_mem act N hN f.support f hf hx
  refine Submodule.sum_mem _ fun ν hν => ?_
  exact Submodule.mem_iSup_of_mem ν ⟨h ν hν, hf ν⟩

end GlobalTheory.WeightDecomp
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.ExtremalGen

open GlobalTheory.TensorHW (mem_wt diag_comm)

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def Supp (S : Ix p q → Ix p q → Prop) (Z : Mat p q) : Prop := ∀ a b, ¬ S a b → Z a b = 0

lemma supp_Eab {S : Ix p q → Ix p q → Prop} {a b : Ix p q} (h : S a b) : Supp S (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

lemma supp_mul {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : S a c
  · rw [hZ c b (fun hcb => hab (hS.trans hac hcb)), mul_zero]
  · rw [hY a c hac, zero_mul]

lemma supp_comm {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z - Z * Y) := by
  intro a b hab
  rw [Matrix.sub_apply, supp_mul hS hY hZ a b hab, supp_mul hS hZ hY a b hab, sub_zero]

lemma supp_ind {S : Ix p q → Ix p q → Prop} (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, S a b → act (Eab a b) y ∈ N) {Z : Mat p q} (hZ : Supp S Z) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]

  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  by_cases hab : S a b
  · have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
      rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (h a b hab)
  · rw [hZ a b hab]
    simp

lemma lie_apply {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (Y Z : Mat p q) (y : V) :
    act Y (act Z y) = act Z (act Y y) + act (Y * Z - Z * Y) y := by
  rw [hL Y Z]
  simp

lemma eig_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (c : Ix p q → ℂ)
    (a b : Ix p q) {t : ℂ} {y : V}
    (hy : y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) t) :
    act (Eab a b) y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (t + (c a - c b)) := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [lie_apply hL, diag_comm, hy, map_smul, map_smul, LinearMap.smul_apply, add_smul]

lemma eig_of_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (c : Ix p q → ℂ) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ wtSub act μ) :
    v ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (∑ a, c a * ((μ a : ℚ) : ℂ)) := by
  rw [mem_wt] at hv
  rw [Module.End.mem_eigenspace_iff]
  have : (Matrix.diagonal c : Mat p q) = ∑ a, c a • Eab a a := by
    ext i j
    simp only [Matrix.sum_apply, Eab, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [this]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, Finset.sum_smul,
  mul_smul]

theorem exists_generated :
    ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  intro p q V _ _ act hL S hS r hr μ v hv hup
  have hv' := mem_wt.1 hv
  set F : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ a b, S a b → r a < r b → ∀ y ∈ N, act (Eab b a) y ∈ N} with hF
  have hG : sInf F ∈ F := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b hab hlt y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b hab hlt y (Submodule.mem_sInf.1 hy M hM)
  have hG' : (sInf F ⊓ ⨅ (Z : Mat p q) (_ : Supp S Z), (sInf F).comap (act Z)) ∈ F := by
    constructor
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      refine ⟨hG.1, fun Z hZ => supp_ind act _ v (fun a b hab => ?_) hZ⟩
      rcases lt_trichotomy (r a) (r b) with h | h | h
      · rw [hup a b hab h]; exact Submodule.zero_mem _
      · obtain rfl := hr h
        rw [hv']; exact Submodule.smul_mem _ _ hG.1
      · exact hG.2 b a (hS.symm hab) h v hG.1
    · intro a b hab hlt y hy
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
      refine ⟨hG.2 a b hab hlt y hy.1, fun Z hZ => ?_⟩
      have hE := supp_Eab (hS.symm hab)
      rw [lie_apply hL]
      exact Submodule.add_mem _ (hG.2 a b hab hlt _ (hy.2 Z hZ)) (hy.2 _ (supp_comm hS hZ hE))
  set c : Ix p q → ℂ := fun a => (r a : ℂ) with hc
  set h : Module.End ℂ V := act (Matrix.diagonal c) with hh
  have hcast : ∀ ν : Ix p q → ℚ,
      ∑ a, c a * ((ν a : ℚ) : ℂ) = ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν; simp [hc]
  have heig : ∀ (ν : Ix p q → ℚ) (x : V), x ∈ wtSub act ν →
      x ∈ h.eigenspace ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν x hx
    rw [← hcast]; exact eig_of_wt c hx
  set m : ℚ := ∑ a, (r a : ℚ) * μ a with hm
  have hvm : v ∈ h.eigenspace (m : ℂ) := heig μ v hv
  set Q : Submodule ℂ V := ⨆ (t : ℚ) (_ : m < t), h.eigenspace (t : ℂ) with hQ
  have hshift : ∀ a b, r a < r b → ∀ t : ℚ, m ≤ t →
      ∀ y ∈ h.eigenspace (t : ℂ), act (Eab b a) y ∈ Q := by
    intro a b hab t ht y hy
    have h1 := eig_shift hL c b a hy
    have h2 : (t : ℂ) + (c b - c a) = ((t + ((r b : ℚ) - (r a : ℚ)) : ℚ) : ℂ) := by simp [hc]
    rw [h2] at h1
    have h3 : (r a : ℚ) < r b := by exact_mod_cast hab
    exact (le_iSup₂_of_le (f := fun (t : ℚ) (_ : m < t) => h.eigenspace (t : ℂ)) _
      (by linarith) le_rfl : _ ≤ Q) h1
  have hlow : ∀ a b, r a < r b → ∀ y ∈ (ℂ ∙ v) ⊔ Q, act (Eab b a) y ∈ Q := by
    intro a b hab
    have : (ℂ ∙ v) ⊔ Q ≤ Q.comap (act (Eab b a)) := by
      refine sup_le ?_ (iSup₂_le fun t ht y hy => hshift a b hab t ht.le y hy)
      rw [Submodule.span_singleton_le_iff_mem]
      exact hshift a b hab m le_rfl v hvm
    exact this
  have hle : sInf F ≤ (ℂ ∙ v) ⊔ Q :=
    sInf_le ⟨Submodule.mem_sup_left (Submodule.mem_span_singleton_self v),
      fun a b _ hab y hy => Submodule.mem_sup_right (hlow a b hab y hy)⟩
  have hQle : ∀ n : ℚ, n ≤ m → Q ≤ ⨆ (j : ℂ) (_ : j ≠ (n : ℂ)), h.eigenspace j := by
    intro n hn
    refine iSup₂_le fun t ht => le_iSup₂_of_le (t : ℂ) ?_ le_rfl
    intro he
    have : t = n := by exact_mod_cast he
    linarith
  have hline : ∀ x ∈ sInf F, x ∈ h.eigenspace (m : ℂ) → ∃ s : ℂ, x = s • v := by
    intro x hx hxm
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hzm : z ∈ h.eigenspace (m : ℂ) := by
      have := Submodule.sub_mem _ hxm (Submodule.smul_mem _ s hvm)
      simpa using this
    have hz0 : z = 0 :=
      Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (m : ℂ)) z hzm
        (hQle m le_rfl hz)
    exact ⟨s, by rw [hz0, add_zero]⟩
  refine ⟨sInf F, hG.1, fun a b hab x hx => ?_, fun U' h1 h2 => sInf_le ⟨h1, h2⟩,
    fun x hx hxμ => hline x hx (heig μ x hxμ), fun ν x hx hx0 hxν => ?_⟩
  · have := sInf_le hG' hx
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at this
    exact this.2 _ (supp_Eab hab)
  · have hxn := heig ν x hxν
    set n : ℚ := ∑ a, (r a : ℚ) * ν a with hn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact Or.inr hlt
    · left
      rw [← heq] at hxn
      obtain ⟨s, hs⟩ := hline x hx hxn
      have hxμ : x ∈ wtSub act μ := hs ▸ Submodule.smul_mem _ s hv
      funext a
      have h1 := mem_wt.1 hxν a
      rw [mem_wt.1 hxμ a] at h1
      have h2 := smul_left_injective ℂ hx0 h1
      exact_mod_cast h2.symm
    · exfalso
      apply hx0
      refine Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (n : ℂ)) x hxn ?_
      refine (sup_le ?_ (hQle n hgt.le) : (ℂ ∙ v) ⊔ Q ≤ _) (hle hx)
      rw [Submodule.span_singleton_le_iff_mem]
      have hne : (m : ℂ) ≠ (n : ℂ) := by exact_mod_cast hgt.ne'
      exact (le_iSup₂_of_le (f := fun (j : ℂ) (_ : j ≠ (n : ℂ)) => h.eigenspace j) (m : ℂ) hne
        le_rfl : _ ≤ _) hvm

end GlobalTheory.ExtremalGen
end

section

open Formalism.BasicNotions.TH

namespace GlobalTheory.ExistsHW

open GlobalTheory.TensorHW

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma inf_eig_ne_bot_iff (f : Module.End ℂ V) (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (t : ℂ) :
    N ⊓ f.eigenspace t ≠ ⊥ ↔ Module.End.HasEigenvalue (f.restrict hf) t := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, hx0⟩
    refine ⟨⟨x, hx1⟩, ?_, fun h => hx0 (congrArg Subtype.val h)⟩
    rw [Module.End.mem_eigenspace_iff]
    exact Subtype.ext (Module.End.mem_eigenspace_iff.1 hx2)
  · rintro ⟨x, hx, hx0⟩
    refine ⟨x, ⟨x.2, ?_⟩, fun h => hx0 (Subtype.ext h)⟩
    rw [Module.End.mem_eigenspace_iff] at hx
    exact Module.End.mem_eigenspace_iff.2 (congrArg Subtype.val hx)

lemma exists_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥)
    (hf : ∀ x ∈ N, f x ∈ N) : ∃ t, N ⊓ f.eigenspace t ≠ ⊥ := by
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue (f.restrict hf)
  exact ⟨t, (inf_eig_ne_bot_iff f N hf t).2 ht⟩

lemma finite_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N]
    (hf : ∀ x ∈ N, f x ∈ N) : {t | N ⊓ f.eigenspace t ≠ ⊥}.Finite := by
  simp only [inf_eig_ne_bot_iff f N hf]
  exact Module.End.finite_hasEigenvalue _

lemma exists_common {ι : Type*} (E : ι → Module.End ℂ V) (hE : ∀ a b x, E a (E b x) = E b (E a x))
    (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥) (hst : ∀ a, ∀ x ∈ N, E a x ∈ N)
    (s : Finset ι) : ∃ N' : Submodule ℂ V, N' ≤ N ∧ N' ≠ ⊥ ∧ (∀ a, ∀ x ∈ N', E a x ∈ N') ∧
      ∀ a ∈ s, ∃ t, N' ≤ (E a).eigenspace t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨N, le_rfl, hN, hst, by simp⟩
  | insert b s _ ih =>
    obtain ⟨N', h1, h2, h3, h4⟩ := ih
    haveI : FiniteDimensional ℂ N' := Submodule.finiteDimensional_of_le h1
    obtain ⟨t, ht⟩ := exists_eig (E b) N' h2 (h3 b)
    refine ⟨N' ⊓ (E b).eigenspace t, inf_le_left.trans h1, ht, ?_, ?_⟩
    · rintro a x ⟨hx1, hx2⟩
      refine ⟨h3 a x hx1, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [hE, Module.End.mem_eigenspace_iff.1 hx2, map_smul]
    · intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨t, inf_le_right⟩
      · obtain ⟨u, hu⟩ := h4 a ha
        exact ⟨u, inf_le_left.trans hu⟩

end General

lemma eig_rat {p q : ℕ} (M : GKMod p q) (a : Ix p q) {t : ℂ} {v : M.V} (hv0 : v ≠ 0)
    (hv : v ∈ (M.act (Eab a a)).eigenspace t) : ∃ r : ℚ, (r : ℂ) = t := by
  by_contra hr
  have hd := Module.End.eigenspaces_iSupIndep (M.act (Eab a a)) t
  have hle : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
      ⨆ (j : ℂ) (_ : j ≠ t), (M.act (Eab a a)).eigenspace j := by
    refine iSup_le fun μ => le_iSup₂_of_le ((μ a : ℚ) : ℂ) (fun h => hr ⟨μ a, h⟩) fun x hx => ?_
    exact Module.End.mem_eigenspace_iff.2 (mem_wt.1 hx a)
  exact hv0 (Submodule.disjoint_def.1 hd v hv (hle (M.wts v)))

theorem exists_highestWeight (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V)
    (hfd : FiniteDimensional ℂ W) (hW : KStable M.act W) (h0 : W ≠ ⊥) :
    ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  set c : Ix p q → ℂ := fun a => (grad p q a : ℂ) with hc
  set H : Module.End ℂ M.V := M.act (Matrix.diagonal c) with hH
  have hHW : ∀ x ∈ W, H x ∈ W := hW _ (isKC_diag c)
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image _ Complex.re (finite_eig H W hHW)
    (exists_eig H W h0 hHW)
  set N := W ⊓ H.eigenspace t with hN
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le inf_le_left
  have hkill : ∀ a b, posC a b → ∀ x ∈ N, M.act (Eab a b) x = 0 := by
    intro a b hab x hx
    by_contra hne
    have := hmax (t + (c a - c b)) ((Submodule.ne_bot_iff _).2 ⟨_,
      ⟨hW _ (isKC_Eab (same_of_pos hab)) x hx.1, eig_shift hL c (same_of_pos hab) hx.2⟩, hne⟩)
    simp only [hc, Complex.add_re, Complex.sub_re, Complex.ofReal_re] at this
    linarith [grad_lt hab]
  have hst : ∀ a, ∀ x ∈ N, M.act (Eab a a) x ∈ N := by
    intro a x hx
    refine ⟨hW _ (isKC_Eab (same_refl a)) x hx.1, ?_⟩
    have := eig_shift hL c (same_refl a) hx.2
    rwa [sub_self, add_zero] at this
  have hcomm : ∀ a b x, M.act (Eab a a) (M.act (Eab b b) x) = M.act (Eab b b) (M.act (Eab a a) x) := by
    intro a b x
    rw [lie_apply hL (isKC_Eab (same_refl a)) (isKC_Eab (same_refl b))]
    have : (Eab a a * Eab b b - Eab b b * Eab a a : Mat p q) = 0 := by
      by_cases hab : a = b
      · rw [hab, sub_self]
      · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ hab,
          Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hab), sub_self]
    rw [this, map_zero, LinearMap.zero_apply, add_zero]
  obtain ⟨N', h1, h2, -, h4⟩ := exists_common (fun a => M.act (Eab a a)) hcomm N ht hst Finset.univ
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h2
  have : ∀ a, ∃ r : ℚ, M.act (Eab a a) v = (r : ℂ) • v := by
    intro a
    obtain ⟨u, hu⟩ := h4 a (Finset.mem_univ a)
    obtain ⟨r, rfl⟩ := eig_rat M a hv0 (hu hv)
    exact ⟨r, Module.End.mem_eigenspace_iff.1 (hu hv)⟩
  choose μ hμ using this
  exact ⟨μ, v, (h1 hv).1, hv0, mem_hw.2 ⟨hμ, fun a b hab => hkill a b hab v (h1 hv)⟩⟩

end GlobalTheory.ExistsHW
end
