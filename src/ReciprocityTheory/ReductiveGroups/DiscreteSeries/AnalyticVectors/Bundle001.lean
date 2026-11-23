module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.CStarAlgebra.Spectrum

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def layerWtVecs (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (k : ℕ) : Set M :=
  {w | ∃ ν ω : Fin n → ℝ, ∃ j ≤ k, IsNCSum ε j ω ∧
    (∃ v ∈ V, v ≠ 0 ∧ ∀ a, E a a v = (ν a : ℂ) • v) ∧ ∀ a, E a a w = ((ν + ω) a : ℂ) • w}

theorem isNCSum_add_root {j : ℕ} {ω : Fin n → ℝ} (hω : IsNCSum ε j ω) {a b : Fin n}
    (hab : ε a ≠ ε b) : IsNCSum ε (j + 1) (ω + root a b) := by
  obtain ⟨γ, hγ, rfl⟩ := hω
  refine ⟨Fin.snoc (α := fun _ => Fin n × Fin n) γ (a, b), fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hab
    · simpa using hγ i
  · rw [Fin.sum_univ_castSucc]
    simp

theorem diag_apply_of_weight (hE : IsGlRep E) {ω : Fin n → ℝ} {w : M}
    (hw : ∀ c, E c c w = (ω c : ℂ) • w) (a b c : Fin n) :
    E c c (E a b w) = ((ω + root a b) c : ℂ) • E a b w := by
  have h := congrArg (fun T : Module.End ℂ M => T w) (hE c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h2 : E c c (E a b w) = E a b (E c c w) +
      ((if c = a then E c b else 0) w - (if b = c then E a c else 0) w) := by
    rw [← h]
    abel
  have e1 : (if c = a then E c b else 0) w = ((if c = a then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : c = a
    · subst h'
      simp
    · simp [h']
  have e2 : (if b = c then E a c else 0) w = ((if c = b then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : b = c
    · subst h'
      simp
    · simp [h', Ne.symm h']
  rw [h2, hw c, map_smul, e1, e2]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  module

theorem le_span_weightVecs (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    V ≤ Submodule.span ℂ {v | v ∈ V ∧ ∃ ν : Fin n → ℝ, ∀ a, E a a v = (ν a : ℂ) • v} := by
  haveI := hVf
  have hst : ∀ a, ∀ v ∈ V, E a a v ∈ V := fun a v hv => hVK a a rfl v hv
  let T : Fin n → Module.End ℂ V := fun a => (E a a).restrict (hst a)
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a
    refine LinearMap.IsSymmetric.restrict_invariant (T := E a a) (fun x y => ?_) (hst a)
    rw [hU a a x y]
    simp [adjSign]
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a c _
    have h := hE a a c c
    have hEc : E a a * E c c = E c c * E a a := by
      rw [← sub_eq_zero, h]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Ne.symm hac]
    show T a * T c = T c * T a
    refine LinearMap.ext fun v => Subtype.ext ?_
    show E a a (E c c v) = E c c (E a a v)
    exact congrArg (fun F : Module.End ℂ M => F (v : M)) hEc
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  intro x hx
  have hy : (⟨x, hx⟩ : V) ∈ ⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  show ((⟨x, hx⟩ : V) : M) ∈ _
  refine Submodule.iSup_induction _ (motive := fun y : V => (y : M) ∈ Submodule.span ℂ _) hy ?_ ?_ ?_
  · intro χ y hy
    rw [Submodule.mem_iInf] at hy
    by_cases hy0 : y = 0
    · subst hy0
      exact Submodule.zero_mem _
    · have hreal : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a := by
        intro a
        have hev : Module.End.HasEigenvalue (T a) (χ a) := by
          first
            | exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hy a, hy0⟩
            | exact (Submodule.ne_bot_iff _).2 ⟨y, hy a, hy0⟩
        exact Complex.conj_eq_iff_re.1 ((hsym a).conj_eigenvalue_eq_self hev)
      refine Submodule.subset_span ⟨y.2, fun a => (χ a).re, fun a => ?_⟩
      have h := Module.End.mem_eigenspace_iff.1 (hy a)
      have h' := congrArg Subtype.val h
      simp only [T, LinearMap.restrict_coe_apply, Submodule.coe_smul] at h'
      rw [h', hreal a]
  · exact Submodule.zero_mem _
  · intro y z hy hz
    simpa using Submodule.add_mem _ hy hz

theorem layerWtVecs_mono {k l : ℕ} (h : k ≤ l) : layerWtVecs ε E V k ⊆ layerWtVecs ε E V l := by
  rintro w ⟨ν, ω, j, hj, hω, hv, hw⟩
  exact ⟨ν, ω, j, hj.trans h, hω, hv, hw⟩

theorem layer_le_span (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) (k : ℕ) :
    layer ε E V k ≤ Submodule.span ℂ (layerWtVecs ε E V k) := by
  induction k with
  | zero =>
    refine (le_span_weightVecs hE hU hVf hVK).trans (Submodule.span_le.2 fun w hw => ?_)
    obtain ⟨hwV, ν, hν⟩ := hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨ν, 0, 0, le_refl 0, ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩,
        ⟨w, hwV, hw0, hν⟩, fun a => by simpa using hν a⟩
  | succ k ih =>
    show layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b) ≤ _
    refine sup_le (ih.trans (Submodule.span_mono (layerWtVecs_mono (Nat.le_succ k))))
      (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
    refine (Submodule.map_mono ih).trans ?_
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨w, ⟨ν, ω, j, hj, hω, hv, hw⟩, rfl⟩
    refine ⟨ν, ω + root a b, j + 1, by omega, isNCSum_add_root hω hab, hv, fun c => ?_⟩
    rw [diag_apply_of_weight hE hw a b c, add_assoc]

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma kExp_Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

section L2
open scoped Matrix.Norms.L2Operator

lemma exists_inK_exp_eq_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k := by
  obtain ⟨hu, hc⟩ := hk
  have hfin := Matrix.finite_spectrum k
  have hN : IsStarNormal k := ⟨by
    rw [Commute, SemiconjBy, Unitary.star_mul_self_of_mem hu, Unitary.mul_star_self_of_mem hu]⟩
  have hcl : ContinuousOn Complex.log (spectrum ℂ k) := hfin.continuousOn _

  have hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu hz

  have hJ : Commute k (Jm ε) := hc
  have hJs : Commute (star k) (Jm ε) := by
    have h := congrArg star hc
    simp only [star_mul, Matrix.star_eq_conjTranspose, kExp_Jm_conjTranspose] at h
    exact h.symm
  have hZJ : Commute (cfc Complex.log k) (Jm ε) := Commute.cfc hJ hJs _
  have hstar : star (cfc Complex.log k) = -cfc Complex.log k := by
    rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 := hcirc z hz
    apply Complex.ext <;> simp [Complex.log_re, h1]
  refine ⟨cfc Complex.log k, ⟨?_, hZJ.eq⟩, ?_⟩
  · unfold inG
    rw [← Matrix.star_eq_conjTranspose, hstar, neg_mul, hZJ.eq]
    exact neg_add_cancel _
  · rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (a := cfc Complex.log k) (cfc_predicate _ _),
      ← cfc_comp NormedSpace.exp Complex.log k hN ((hfin.image _).continuousOn _) hcl]
    conv_rhs => rw [← cfc_id ℂ k hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by
      intro h
      have h1 := hcirc z hz
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    simp only [Function.comp_apply, id]
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log hz0]

end L2

theorem exists_exp_eq_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k :=
  exists_inK_exp_eq_of_mem_Kset hk

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs with h <;> simp [h]

private theorem Jm_inv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε :=
  Matrix.inv_eq_right_inv (Jm_mul_Jm ε)

private theorem isUnit_Jm (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, Jm_mul_Jm ε, Jm_mul_Jm ε⟩, rfl⟩

private theorem conjTranspose_eq_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Xᴴ = -(Jm ε * X * Jm ε) := by
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, Jm_mul_Jm, mul_one]
    _ = -(Jm ε * X * Jm ε) := by rw [h1, neg_mul]

theorem exp_smul_mem_UJset {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  have hc : ((t : ℂ) • X)ᴴ = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, conjTranspose_eq_of_inG hX, Jm_inv]
    simp
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ (isUnit_Jm ε), Jm_inv]
  have hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((t : ℂ) • X)
      = Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [mul_assoc (Jm ε * _) (Jm ε) (Jm ε), Jm_mul_Jm, mul_one, mul_assoc]
    _ = Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem exp_add_smul (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

theorem exp_zero_smul (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

theorem exp_mem_Kset {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    NormedSpace.exp Z ∈ Kset ε := by
  have hZh : Zᴴ = -Z := by
    rw [conjTranspose_eq_of_inG hZ.1, ← hZ.2, mul_assoc, Jm_mul_Jm, mul_one]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (NormedSpace.exp Z)ᴴ * NormedSpace.exp Z = 1
    rw [← Matrix.exp_conjTranspose, hZh,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((Commute.exp_left (hZ.2 : Commute Z (Jm ε))) : _)

theorem inP_apply_eq_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    {a b : Fin n} (hab : ε a = ε b) : X a b = 0 := by
  first | exact UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero .. | (apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> first | assumption | infer_instance)

theorem inK_apply_eq_zero {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    {a b : Fin n} (hab : ε a ≠ ε b) : Z a b = 0 := by
  have h := congrFun (congrFun hZ.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b
  all_goals first
    | exact absurd (ha.trans hb.symm) hab
    | (simp [ha, hb] at h; first | linear_combination h / 2 | linear_combination -h / 2)

end ReciprocityTheory.ChartRestriction.DS
end
end
