module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

noncomputable section

namespace GlobalTheory.LatticePartition

def bump (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t

theorem bump_contDiff : ContDiff ℝ ∞ bump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem bump_eq_zero {t : ℝ} (h : 1 ≤ |t|) : bump t = 0 := by
  unfold bump
  rcases le_abs'.1 h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le h]
    simp

theorem bump_local (y : ℝ) (k : ℤ) (hk : k ∉ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ)) :
    bump (y - k) = 0 := by
  apply bump_eq_zero
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have : k ≤ ⌊y⌋ - 2 ∨ ⌊y⌋ + 2 ≤ k := by omega
  rcases this with h | h
  · have h' : (k : ℝ) ≤ (⌊y⌋ : ℝ) - 2 := by exact_mod_cast h
    rw [le_abs']; right; linarith
  · have h' : (⌊y⌋ : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast h
    rw [le_abs']; left; linarith

theorem bump_sum (y : ℝ) : ∑ k ∈ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ), bump (y - k) = 1 := by
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have e1 : y - ((⌊y⌋ - 1 : ℤ) : ℝ) = y - (⌊y⌋ : ℝ) + 1 := by push_cast; ring
  have e2 : y - ((⌊y⌋ + 1 : ℤ) : ℝ) + 1 = y - (⌊y⌋ : ℝ) := by push_cast; ring
  have ha : Real.smoothTransition (y - (⌊y⌋ : ℝ) + 1 + 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hb : Real.smoothTransition (y - ((⌊y⌋ + 1 : ℤ) : ℝ)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)
  unfold bump
  rw [e1, e2, ha, hb]
  ring

theorem summable_lattice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

def bumpProd (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) : ℝ := ∏ i, bump (e x i)

def latPt (e : V ≃L[ℝ] (Fin n → ℝ)) (j : Fin n → ℤ) : V := e.symm (fun i => (j i : ℝ))

theorem bumpProd_contDiff (e : V ≃L[ℝ] (Fin n → ℝ)) : ContDiff ℝ ∞ (bumpProd e) := by
  unfold bumpProd
  refine contDiff_prod fun i _ => bump_contDiff.comp ?_
  exact (contDiff_apply ℝ (fun _ => ℝ) i).comp e.contDiff

theorem bumpProd_compact (e : V ≃L[ℝ] (Fin n → ℝ)) : HasCompactSupport (bumpProd e) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine HasCompactSupport.intro (hK.image e.symm.continuous) ?_
  intro x hx
  have : ∃ i, 1 ≤ |e x i| := by
    by_contra h
    simp only [not_exists, not_le] at h
    exact hx ⟨e x, Set.mem_univ_pi.2 fun i => ⟨(abs_lt.1 (h i)).1.le, (abs_lt.1 (h i)).2.le⟩,
      e.symm_apply_apply x⟩
  obtain ⟨i, hi⟩ := this
  exact Finset.prod_eq_zero (Finset.mem_univ i) (bump_eq_zero hi)

theorem bumpProd_sub (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) (j : Fin n → ℤ) :
    bumpProd e (x - latPt e j) = ∏ i, bump (e x i - j i) := by
  simp [bumpProd, latPt, map_sub]

theorem hasSum_bumpProd (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) :
    HasSum (fun j : Fin n → ℤ => bumpProd e (x - latPt e j)) 1 := by
  simp only [bumpProd_sub]
  generalize e x = y
  have hsum : ∑ j ∈ Fintype.piFinset (fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ)),
      ∏ i, bump (y i - j i) = 1 := by
    rw [← Finset.prod_univ_sum (t := fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ))
      (f := fun i k => bump (y i - k))]
    exact Finset.prod_eq_one fun i _ => bump_sum (y i)
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (f := fun j : Fin n → ℤ => ∏ i, bump (y i - j i))
    (s := Fintype.piFinset (fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ))) (by
      intro j hj
      rw [Fintype.mem_piFinset, not_forall] at hj
      obtain ⟨i, hi⟩ := hj
      exact Finset.prod_eq_zero (Finset.mem_univ i) (bump_local _ _ hi))
  rwa [hsum] at h

theorem summable_latPt [FiniteDimensional ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    ∃ M : ℕ, Summable (fun j : Fin n → ℤ => ((1 + ‖latPt b.equivFunL j‖) ^ M)⁻¹) := by
  have hmem : ∀ j, latPt b.equivFunL j ∈ Submodule.span ℤ (Set.range b) := fun j => by
    have : latPt b.equivFunL j = ∑ i, (j i : ℝ) • b i := b.equivFun_symm_apply _
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj : Function.Injective fun j : Fin n → ℤ =>
      (⟨latPt b.equivFunL j, hmem j⟩ : Submodule.span ℤ (Set.range b)) := by
    intro j k hjk
    have h1 : latPt b.equivFunL j = latPt b.equivFunL k := congrArg Subtype.val hjk
    have h2 : (fun i => (j i : ℝ)) = fun i => (k i : ℝ) := b.equivFunL.symm.injective h1
    funext i
    exact_mod_cast congrFun h2 i
  have h := (summable_lattice (Submodule.span ℤ (Set.range b))).comp_injective hinj
  refine ⟨Module.finrank ℤ (Submodule.span ℤ (Set.range b)) + 1, h.congr fun j => ?_⟩
  simp only [Function.comp_apply, Submodule.coe_norm]

theorem finite_of_summable {ι : Type} (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (M : ℕ)
    (hS : Summable (fun j => ((1 + a j) ^ M)⁻¹)) (R : ℝ) : {j | a j ≤ R}.Finite := by
  have ht := hS.tendsto_cofinite_zero
  have hR : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  have hε : (0 : ℝ) < ((1 + max R 0) ^ M)⁻¹ := by positivity
  have h3 := ht (Iio_mem_nhds hε)
  rw [Filter.mem_map, Filter.mem_cofinite] at h3
  refine h3.subset fun j hj => ?_
  simp only [Set.mem_setOf_eq] at hj
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iio, not_lt]
  have hj' : a j ≤ max R 0 := le_trans hj (le_max_left _ _)
  have h0 := ha j
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) _)

end

theorem exists_lattice_partition :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ ψ : SchwartzMap V ℂ, HasCompactSupport (ψ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (ψ x) = ψ x) ∧
      ∃ v : (Fin (Module.finrank ℝ V) → ℤ) → V, (∀ x, HasSum (fun j => ψ (x - v j)) 1) ∧
        (∀ R : ℝ, {j | ‖v j‖ ≤ R}.Finite) ∧ ∃ M : ℕ, Summable (fun j => ((1 + ‖v j‖) ^ M)⁻¹) := by
  intro V _ _ _
  obtain ⟨M, hS⟩ := summable_latPt (Module.finBasis ℝ V)
  generalize (Module.finBasis ℝ V).equivFunL = e at hS
  have hc : HasCompactSupport (fun x => ((bumpProd e x : ℝ) : ℂ)) :=
    (bumpProd_compact e).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ (fun x => ((bumpProd e x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpProd_contDiff e)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SchwartzMap V ℂ, (ψ : V → ℂ) = fun x => ((bumpProd e x : ℝ) : ℂ) :=
    ⟨hc.toSchwartzMap hd, rfl⟩
  refine ⟨ψ, hψ ▸ hc, ?_, latPt e, ?_, ?_, M, hS⟩
  · intro x
    rw [hψ]
    exact Complex.conj_ofReal _
  · intro x
    rw [hψ]
    have h := Complex.hasSum_ofReal.2 (hasSum_bumpProd e x)
    rwa [Complex.ofReal_one] at h
  · exact finite_of_summable (fun j => ‖latPt e j‖) (fun _ => norm_nonneg _) M hS

end GlobalTheory.LatticePartition
end
end

section

open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzTranslate

private theorem fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (a : V) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : V → F), ContDiff ℝ ∞ g →
      ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m := by
  induction n with
  | zero =>
    intro F _ _ g hg x m
    simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro F _ _ g hg x m
    have hg1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (fderiv ℝ g)) :=
      hg1.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
    have hsym : (fun y => fderiv ℝ (fun z => fderiv ℝ g z a) y)
        = fun y => fderiv ℝ (fderiv ℝ g) y a := by
      funext y
      ext w
      rw [fderiv_clm_apply ((hg1.differentiable (by simp)) y) (differentiableAt_const _)]
      simp
      have h2le : minSmoothness ℝ 2 ≤ ∞ := by simp
      exact (ContDiffAt.isSymmSndFDerivAt (hg.contDiffAt (x := y)) h2le) w a
    simp_rw [iteratedFDeriv_succ_apply_right]
    rw [fderiv_clm_apply ((hdiff x).continuousMultilinear_apply_const _) (differentiableAt_const _)]
    simp
    rw [ih (fderiv ℝ g) hg1 x (Fin.init m), hsym]

theorem fderiv_iteratedFDeriv_apply_comm {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) :
    ∀ (g : V → F), ContDiff ℝ ∞ g → ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m :=
  fun g hg x m => fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv a n g hg x m

theorem hasDerivAt_iteratedFDeriv_line {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) (g : V → F) (hg : ContDiff ℝ ∞ g)
    (x : V) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (x + s • a))
      (iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a)) s := by
  have hline : HasDerivAt (fun s : ℝ => x + s • a) a s := by
    simpa using ((hasDerivAt_id s).smul_const a).const_add x
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
  have key : fderiv ℝ (iteratedFDeriv ℝ n g) (x + s • a) a
      = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a) := by
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply (hd _)]
    exact fderiv_iteratedFDeriv_apply_comm a n g hg _ m
  rw [← key]
  exact (hd _).hasFDerivAt.comp_hasDerivAt s hline

theorem taylor_two {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (φ φ' φ'' : ℝ → G)
    (h1 : ∀ s, HasDerivAt φ (φ' s) s) (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) (M : ℝ)
    (hM : ∀ s, |s| ≤ 1 → ‖φ'' s‖ ≤ M) (t : ℝ) (ht : |t| ≤ 1) :
    ‖φ t - φ 0 - t • φ' 0‖ ≤ M * t ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hd1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ' s - φ' 0‖ ≤ M * |s| := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ') (f' := φ'')
      (s := Set.Icc (-1) 1) (fun x _ => (h2 x).hasDerivWithinAt)
      (fun x hx => hM x (abs_le.mpr hx)) (convex_Icc _ _) h0 hs
    simpa [Real.norm_eq_abs] using this
  have hψ : ∀ s, HasDerivAt (fun s => φ s - s • φ' 0) (φ' s - φ' 0) s := by
    intro s
    convert (h1 s).sub ((hasDerivAt_id s).smul_const (φ' 0)) using 1 <;> first | rfl | simp
  have ht' : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  have h0' : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have hbound : ∀ x ∈ Set.Icc (-|t|) |t|, ‖φ' x - φ' 0‖ ≤ M * |t| := by
    intro x hx
    have hx1 : |x| ≤ |t| := abs_le.mpr hx
    exact (hd1 x (abs_le.mp (hx1.trans ht))).trans (mul_le_mul_of_nonneg_left hx1 hM0)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => φ s - s • φ' 0) (f' := fun s => φ' s - φ' 0)
    (fun x _ => (hψ x).hasDerivWithinAt) hbound (convex_Icc _ _) h0' ht'
  have e : φ t - φ 0 - t • φ' 0 = (φ t - t • φ' 0) - (φ 0 - (0 : ℝ) • φ' 0) := by
    rw [zero_smul, sub_zero, sub_right_comm]
  rw [e]
  calc _ ≤ M * |t| * ‖t - 0‖ := key
    _ = M * t ^ 2 := by rw [sub_zero, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, sq]

theorem seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V)
    (f : 𝓢(V, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by
  set f1 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hf1def
  set f2 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f1 with hf2def
  have hf1 : (⇑f1 : V → ℂ) = fun y => fderiv ℝ f y a := rfl
  have hf2 : (⇑f2 : V → ℂ) = fun y => fderiv ℝ f1 y a := rfl
  have hsm : ∀ g : 𝓢(V, ℂ), ContDiff ℝ ∞ ⇑g := fun g => g.smooth ⊤
  have hsmn : ∀ g : 𝓢(V, ℂ), ContDiff ℝ n ⇑g := fun g => (g.smooth ⊤).of_le (mod_cast le_top)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f2 :=
    ⟨_, rfl⟩
  have hL : ∀ y, (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ n f2 y‖ ≤ 2 ^ k * S := fun y => by
    rw [hS]; exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) le_rfl le_rfl f2 y
  have hS0 : 0 ≤ 2 ^ k * S := le_trans (by positivity) (hL 0)
  refine ⟨(1 + ‖a‖) ^ k * (2 ^ k * S), fun t ht => ?_⟩
  have hC0 : 0 ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := mul_nonneg (by positivity) hS0
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg hC0 (sq_nonneg t)) fun x => ?_
  have hcoe : (⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1) : V → ℂ)
      = (fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1 := by
    funext y; simp [sub_neg_eq_add]
  have hshift : ContDiff ℝ n (fun y => f (y + t • a)) :=
    (hsmn f).comp (contDiff_id.add contDiff_const)
  have hD : iteratedFDeriv ℝ n ((fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1) x
      = iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - (t : ℂ) • iteratedFDeriv ℝ n f1 x := by
    rw [iteratedFDeriv_sub_apply, iteratedFDeriv_sub_apply, iteratedFDeriv_const_smul_apply,
      iteratedFDeriv_comp_add_right]
    all_goals first
      | exact hshift.contDiffAt
      | exact (hsmn f).contDiffAt
      | exact (hsmn f1).contDiffAt
      | exact (hshift.sub (hsmn f)).contDiffAt
      | exact ((hsmn f1).const_smul (t : ℂ)).contDiffAt
  have hre : (t : ℂ) • iteratedFDeriv ℝ n f1 x = t • iteratedFDeriv ℝ n f1 x := by
    ext m; simp [Complex.real_smul]
  rw [hcoe, hD, hre]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖x‖ ^ k := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hdf : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a))
      (c • iteratedFDeriv ℝ n f1 (x + s • a)) s := by
    intro s
    have := hasDerivAt_iteratedFDeriv_line a n f (hsm f) x s
    rw [← hf1] at this
    exact this.const_smul c
  have hdf1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a))
      (c • iteratedFDeriv ℝ n f2 (x + s • a)) s := by
    intro s
    have := hasDerivAt_iteratedFDeriv_line a n f1 (hsm f1) x s
    rw [← hf2] at this
    exact this.const_smul c
  have hbd : ∀ s : ℝ, |s| ≤ 1 →
      ‖c • iteratedFDeriv ℝ n f2 (x + s • a)‖ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := by
    intro s hs
    have h2 : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) hs
    have hxy : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x + s • a‖) := by
      have h3 : ‖x‖ ≤ ‖x + s • a‖ + ‖s • a‖ := by
        have := norm_sub_le (x + s • a) (s • a)
        rwa [add_sub_cancel_right] at this
      nlinarith [norm_nonneg (x + s • a), norm_nonneg a]
    have hpow : c ≤ (1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k := by
      rw [hc, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hxy k
    rw [norm_smul, Real.norm_of_nonneg hc0]
    calc c * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖
        ≤ ((1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k) * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = (1 + ‖a‖) ^ k * ((1 + ‖x + s • a‖) ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖) := by ring
      _ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := mul_le_mul_of_nonneg_left (hL _) (by positivity)
  have hT := taylor_two (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a))
    (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a))
    (fun s : ℝ => c • iteratedFDeriv ℝ n f2 (x + s • a)) hdf hdf1 _ hbd t ht
  simp only [zero_smul, add_zero] at hT
  have e : c • iteratedFDeriv ℝ n f (x + t • a) - c • iteratedFDeriv ℝ n f x
      - t • c • iteratedFDeriv ℝ n f1 x
      = c • (iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - t • iteratedFDeriv ℝ n f1 x) := by
    rw [smul_sub, smul_sub, smul_comm t c]
  rw [e, norm_smul, Real.norm_of_nonneg hc0] at hT
  exact hT

end GlobalTheory.SchwartzTranslate
end

section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_fourier_stable_gaussian_submodule :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  let S : Set (Submodule ℂ (SchwartzMap E ℂ)) := {K | G ∈ K ∧
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ K) ∧
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ K)}
  have hWG : G ∈ sInf S := Submodule.mem_sInf.2 fun K hK => hK.1
  have hWD : ∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.1 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have hWL : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.2 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have htemp : ∀ m : E, Function.HasTemperateGrowth (fun x : E => inner ℝ x m) := by
    intro m
    have : (fun x : E => inner ℝ x m) = (innerSL ℝ m : E →L[ℝ] ℝ) := by
      funext x; simp [real_inner_comm]
    rw [this]; exact (innerSL ℝ m).hasTemperateGrowth
  have hFG : 𝓕 G = G := by
    ext w
    have h1 : (⇑G) = fun v : E => Complex.exp (-(Real.pi : ℂ) * (‖v‖ : ℂ) ^ 2) := by
      funext v; rw [hG]; congr 1; push_cast; ring
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [SchwartzMap.fourier_coe, h1,
      fourier_gaussian_innerProductSpace (by simpa using Real.pi_pos), div_self hpi,
      Complex.one_cpow, one_mul]
    congr 1
    field_simp
  have hK : (sInf S).comap (SchwartzMap.fourierTransformCLM ℂ (V := E) (E := ℂ)).toLinearMap ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · show 𝓕 G ∈ sInf S
      rw [hFG]; exact hWG
    · intro v f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      have h1 : f₁ = LineDeriv.lineDerivOp v f := by
        ext x; rw [h, SchwartzMap.lineDerivOp_apply_eq_fderiv]
      rw [h1, SchwartzMap.fourier_lineDerivOp_eq]
      refine Submodule.smul_mem _ _ (hWL (innerSL ℝ v) _ _ hf' fun x => ?_)
      rw [SchwartzMap.smulLeftCLM_apply_apply (htemp v)]
      simp [real_inner_comm]
    · intro ℓ f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      set u : E := (InnerProductSpace.toDual ℝ E).symm ℓ with hu
      have h1 : f₁ = SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ x u) f := by
        ext x
        rw [h, SchwartzMap.smulLeftCLM_apply_apply (htemp u), real_inner_comm, hu,
          InnerProductSpace.toDual_symm_apply]
        simp
      have h2 : LineDeriv.lineDerivOp u (𝓕 f) ∈ sInf S :=
        hWD u _ _ hf' fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
      rw [SchwartzMap.lineDerivOp_fourier_eq, ← h1, ← SchwartzMap.fourierTransformCLM_apply ℂ,
        map_smul, SchwartzMap.fourierTransformCLM_apply] at h2
      have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
        simp [Real.pi_ne_zero]
      exact (Submodule.smul_mem_iff _ hc).1 h2
  exact ⟨sInf S, sInf_le ⟨hGN, hD, hL⟩, hWG, hWL, fun f hf => sInf_le hK hf⟩

end GlobalTheory
end
