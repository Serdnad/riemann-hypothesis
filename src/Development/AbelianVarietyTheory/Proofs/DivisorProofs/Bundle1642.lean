module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.LeviGA

namespace GlobalTheory.SliceTwo.Growth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_inv {a : ℕ} (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_mul_right_le {a : ℕ} (c : GL (Fin a) (Cinf E)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  obtain ⟨B, hB, h⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c⁻¹))
  refine ⟨B, hB, fun y => ?_⟩
  have := h _ rfl y⁻¹
  rwa [← _root_.mul_inv_rev, height_inv, height_inv] at this


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_toL_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    ‖toL (blkGL hr (1, y)).val‖ ≤ 1 + ‖toL y.val‖ := by
  have h0 : (0 : ℝ) ≤ 1 + ‖toL y.val‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  change ‖(blkGL hr (1, y) : Matrix (Fin a) (Fin a) (Cinf E)) (blkEquiv hr i) (blkEquiv hr j)‖ ≤ _
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.fromBlocks_apply₁₁, Units.val_one]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      refine ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_).trans (by linarith [norm_nonneg (toL y.val)])
      simp
    · rw [Matrix.one_apply_ne hij, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₂]
    exact ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)).trans
      (by linarith)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    height (blkGL hr (1, y)) ≤ 3 * height y := by
  have e : (blkGL hr (1, y))⁻¹ = blkGL hr (1, y⁻¹) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_toL_blkGL_one_le hr y
  have h2 := norm_toL_blkGL_one_le hr y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.SliceTwo.Growth


open GlobalTheory.SliceTwo.Growth in
theorem GlobalTheory.SliceTwo.Growth.norm_slice_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ →
    ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y,
      ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ hF h1 φ hφ m₁ t κ g
  obtain ⟨C, N, hC⟩ := GlobalTheory.ConstTermGrowth.norm_constTerm_le E a r μ 𝓕 hμ hF h1 φ hφ.left hφ.level hφ.growth
    (blkGL hr (m₁, g) * finGL E a t)
  obtain ⟨B, hB0, hB⟩ := height_mul_right_le (E := E) (Unitary.toUnits κ)
  refine ⟨|C| * (3 * B) ^ N, N, fun y => ?_⟩
  have e : GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y) =
      ∫ x in 𝓕, φ.1 (unip x * ((blkGL hr (m₁, g) * finGL E a t) *
        infGL E a (blkGL hr (1, y) * Unitary.toUnits κ))) ∂μ := by
    unfold GlobalTheory.SliceTwo.slice
    congr 1
    funext x
    congr 2
    rw [GlobalTheory.SliceTwo.blkGL_mul_infGL, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (infGL E a (blkGL hr (1, y))) (finGL E a t), infGL_comm]
    simp only [mul_assoc]
  rw [e]
  refine (hC _).trans ?_
  have hy := one_le_height y
  have hb := one_le_height (blkGL hr (1, y) * Unitary.toUnits κ)
  have h3 : height (blkGL hr (1, y) * Unitary.toUnits κ) ≤ 3 * B * height y := by
    calc _ ≤ B * height (blkGL hr (1, y)) := hB _
      _ ≤ B * (3 * height y) := mul_le_mul_of_nonneg_left (height_blkGL_one_le hr y) hB0
      _ = 3 * B * height y := by ring
  calc C * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N
      ≤ |C| * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) _)
    _ ≤ |C| * (3 * B * height y) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h3 _) (abs_nonneg C)
    _ = |C| * (3 * B) ^ N * height y ^ N := by ring

end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.MirPatch.Decomp

open GlobalTheory.JSW GlobalTheory.SmGL Topology

theorem exists_distinct {ι X : Type} [Finite ι] (C : ι → Set X)
    (hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j) :
    ∃ (N : ℕ) (f : Fin N → ι), (∀ i j x, x ∈ C (f i) → x ∈ C (f j) → i = j) ∧
      ∀ x, (∃ i, x ∈ C i) ↔ ∃ j, x ∈ C (f j) := by
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range C)
  have hf : ∀ j, C (e.symm j).2.choose = (e.symm j).1 := fun j => (e.symm j).2.choose_spec
  refine ⟨N, fun j => (e.symm j).2.choose, fun i j x hi hj => ?_, fun x => ⟨fun ⟨i, hi⟩ => ?_, fun ⟨j, hj⟩ => ⟨_, hj⟩⟩⟩
  · have h := hC _ _ x hi hj
    rw [hf, hf] at h
    exact e.symm.injective (Subtype.ext h)
  · refine ⟨e ⟨C i, i, rfl⟩, ?_⟩
    simp only
    rw [hf, Equiv.symm_apply_apply]
    exact hi

theorem exists_finite_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K A : Set G} (hK : IsCompact K) (hA : A ⊆ K) (V : Subgroup G) (hV : IsOpen (V : Set G)) :
    ∃ (ι : Type) (_ : Finite ι) (k : ι → G), (∀ i, k i ∈ A) ∧ ∀ a ∈ A, ∃ i, (k i)⁻¹ * a ∈ V := by
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK (V := (V : Set G))
    (by rw [hV.interior_eq]; exact ⟨1, V.one_mem⟩)
  let ι := {g : G // g ∈ t ∧ ∃ a ∈ A, g * a ∈ V}
  haveI : Finite ι := Finite.of_injective (fun x : ι => (⟨x.1, x.2.1⟩ : t))
    (fun x y h => Subtype.ext (congrArg (fun z : t => (z : G)) h))
  refine ⟨ι, inferInstance, fun x => x.2.2.choose, fun x => x.2.2.choose_spec.1, fun a ha => ?_⟩
  obtain ⟨g, hg, hga⟩ := Set.mem_iUnion₂.1 (ht (hA ha))
  have hga' : g * a ∈ V := hga
  refine ⟨⟨g, hg, a, ha, hga'⟩, ?_⟩
  have hb := (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose_spec.2
  have e : ((⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * a =
      (g * (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * (g * a) := by group
  rw [e]
  exact mul_mem (inv_mem hb) hga'

theorem cell_eq_of_mem {F : Type} [NormedField F] {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (h : g ∈ Cut.cell z (U : Set (GL (Fin n) F))) :
    Cut.cell z (U : Set (GL (Fin n) F)) = Cut.cell g (U : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u⁻¹, mul_mem hu' (inv_mem hu), k⁻¹ * k', mul_mem (inv_mem hk) hk', by group⟩
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u, mul_mem hu' hu, k * k', mul_mem hk hk', by group⟩

variable {E : Type} [Field E] [NumberField E]

theorem map_comp_eq {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem af_eq {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y := FiniteAdeleRing.ext _ h


open Classical in
theorem pLoc_list_prod {n : ℕ} (u : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (v : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E n w (u w)).prod = if v ∈ l then u v else 1 := by
  classical
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos (by simp), mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp only [List.mem_cons, h, false_or]

theorem loc_mem_unipB {a : ℕ} {u : GA E a} (hu : u ∈ NA (E := E) (a := a)) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) u ∈ unipB (w.adicCompletion E) (Fin a) :=
  (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j h => by
    show pLoc E w (pFin E _) = 0
    rw [hu.1 i j h, map_zero, map_zero], fun i => by
    show pLoc E w (pFin E _) = 1
    rw [hu.2 i, map_one, map_one]⟩

variable [_root_.NumberField.IsTotallyComplex E]

theorem finGL_mem_NA {a : ℕ} {v : GL (Fin a) (Af E)}
    (hv : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a)) : finGL E a v ∈ NA (E := E) (a := a) := by
  have e1 : ∀ i j, pInf E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) =
      ((1 : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j := fun i j =>
    congrArg (fun g : GL (Fin a) (Cinf E) => (g : Matrix (Fin a) (Fin a) (Cinf E)) i j) (pInf_finGL (E := E) v)
  have e2 : ∀ i j, pFin E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) = (v : Matrix (Fin a) (Fin a) (Af E)) i j :=
    fun i j => congrArg (fun g : GL (Fin a) (Af E) => (g : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) v)
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [e1, Units.val_one, Matrix.one_apply_ne (ne_of_gt h), map_zero]
  · rw [e2, map_zero]
    exact af_eq fun w => by rw [map_zero]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).1 i j h
  · rw [e1, Units.val_one, Matrix.one_apply_eq, map_one]
  · rw [e2, map_one]
    exact af_eq fun w => by rw [map_one]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).2 i

theorem mem_cell_iff {a : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a)
    {p : GA E a} (hp : p ∈ supS (E := E) (a := a) S) :
    p ∈ cell K q ↔ ∃ k ∈ K,
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) ∈
        unipB (w.adicCompletion E) (Fin a)) ∧
      ∀ w ∈ S, ∃ u ∈ unipB (w.adicCompletion E) (Fin a), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p =
        u * GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) := by
  constructor
  · rintro ⟨u, hu, k, hk, y, rfl⟩
    have hf : GeneralLinearGroup.map (pFin E) (u * q * finGL E a k * infGL E a y) =
        GeneralLinearGroup.map (pFin E) u * (GeneralLinearGroup.map (pFin E) q * k) := by
      rw [map_mul, map_mul, map_mul, pFin_finGL, pFin_infGL, mul_one, mul_assoc]
    refine ⟨k, hk, fun w hw => ?_, fun w _ => ⟨_, loc_mem_unipB hu w, ?_⟩⟩
    · have h1 := hp w hw
      rw [map_comp_eq, hf, map_mul] at h1
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (loc_mem_unipB hu w)
    · rw [map_comp_eq, hf, map_mul, map_comp_eq]
  · rintro ⟨k, hk, hout, hin⟩
    set v := GeneralLinearGroup.map (pFin E) p * (GeneralLinearGroup.map (pFin E) q * k)⁻¹ with hv
    have hvN : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a) := by
      intro w
      rw [hv, map_mul, map_inv]
      by_cases hw : w ∈ S
      · obtain ⟨u, hu, he⟩ := hin w hw
        rw [← map_comp_eq, he, mul_inv_cancel_right]
        exact hu
      · rw [← map_comp_eq, hp w hw, one_mul]
        exact inv_mem (hout w hw)
    refine ⟨finGL E a v, finGL_mem_NA hvN, k, hk,
      (GeneralLinearGroup.map (pInf E) q)⁻¹ * GeneralLinearGroup.map (pInf E) p, ga_ext ?_ ?_⟩
    · simp only [map_mul, pInf_finGL, pInf_infGL, one_mul, mul_one, mul_inv_cancel_left]
    · simp only [map_mul, pFin_finGL, pFin_infGL, mul_one, hv]
      group

end GlobalTheory.JSW.MirPatch.Decomp

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.JSW GlobalTheory.SmGL Decomp

theorem cell_decomp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  intro E _ _ _ m S K hKo hKc q
  classical
  choose U hUo hUc hUK using fun w => LocEx.exists_compact_open (a := m + 1) w K hKo
  set qf := GeneralLinearGroup.map (pFin E) q with hqf
  let A : Set (GL (Fin (m + 1)) (Af E)) := {k | k ∈ K ∧ ∀ w ∉ S,
    GeneralLinearGroup.map (pLoc E w) (qf * k) ∈ unipB (w.adicCompletion E) (Fin (m + 1))}
  let V : Subgroup (GL (Fin (m + 1)) (Af E)) :=
    { carrier := {v | ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) v ∈ U w}
      mul_mem' := fun ha hb w hw => by rw [map_mul]; exact mul_mem (ha w hw) (hb w hw)
      one_mem' := fun w _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun ha w hw => by rw [map_inv]; exact inv_mem (ha w hw) }
  have hVo : IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) := by
    have e : (V : Set (GL (Fin (m + 1)) (Af E))) =
        ⋂ w ∈ S, GeneralLinearGroup.map (pLoc E w) ⁻¹' (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) := by
      ext v; simp [V]
    rw [e]
    exact isOpen_biInter_finset fun w _ => (hUo w).preimage (LocEx.continuous_map_pLoc w)
  obtain ⟨ι, _, k, hkA, hcov⟩ := exists_finite_reps (A := A) hKc (fun x hx => hx.1) V hVo
  let C : ι → Set (∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) := fun i =>
    {x | ∀ w ∈ S, x w ∈ Cut.cell (GeneralLinearGroup.map (pLoc E w) (qf * k i))
      (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}
  have hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j := by
    intro i j x hi hj
    ext y
    exact forall₂_congr fun w hw => by rw [cell_eq_of_mem (hi w hw), cell_eq_of_mem (hj w hw)]
  obtain ⟨N, f, huniq, hiff⟩ := exists_distinct C hC
  refine ⟨U, N, fun j w => GeneralLinearGroup.map (pLoc E w) (qf * k (f j)), fun w _ => ⟨hUc w, hUo w, hUK w⟩,
    fun p _ i j hi hj => huniq i j (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) hi hj,
    fun p hp => ?_⟩
  rw [mem_cell_iff S K q hp.1]
  refine Iff.trans ?_ (hiff (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p))
  constructor
  · rintro ⟨k', hk', hout, hin⟩
    obtain ⟨i, hi⟩ := hcov k' ⟨hk', hout⟩
    refine ⟨i, fun w hw => ?_⟩
    obtain ⟨u, hu, he⟩ := hin w hw
    refine ⟨u, hu, GeneralLinearGroup.map (pLoc E w) ((k i)⁻¹ * k'), hi w hw, ?_⟩
    show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = _
    rw [he, mul_assoc u, ← map_mul, mul_assoc, mul_inv_cancel_left]
  · rintro ⟨i, hi⟩
    choose! uu huu cc hcc heq using hi
    let g : GL (Fin (m + 1)) (Af E) := (S.toList.map fun w => locGL E (m + 1) w (cc w)).prod
    have hgK : g ∈ K := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact hUK w _ (hcc w (Finset.mem_toList.1 hw))
    have hg : ∀ v, GeneralLinearGroup.map (pLoc E v) g = if v ∈ S then cc v else 1 := fun v => by
      rw [pLoc_list_prod cc _ S.nodup_toList v]
      simp only [Finset.mem_toList]
    refine ⟨k i * g, mul_mem (hkA i).1 hgK, fun w hw => ?_, fun w hw => ⟨uu w, huu w hw, ?_⟩⟩
    · rw [← mul_assoc, map_mul, hg w, if_neg hw, mul_one]
      exact (hkA i).2 w hw
    · refine (heq w hw).trans ?_
      rw [← mul_assoc qf, map_mul (GeneralLinearGroup.map (pLoc E w)) (qf * k i) g, hg w, if_pos hw, mul_assoc]

end GlobalTheory.JSW.MirPatch
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem kerOpInf_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hχc hσ hα hαc hαs T hT
  have hdet : ∀ w : InfinitePlace E, ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      (Matrix.of (σ₀ + L p.1)).det w := by
    intro w
    simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply]
    refine ContDiff.sum fun s _ => ?_
    refine ContDiff.mul ?_ (contDiff_prod fun i _ => ?_)
    · exact contDiff_const
    have : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) => σ₀ + L p.1 :=
      contDiff_const.add (L.contDiff.comp contDiff_fst)
    exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 this (s i)) i) w
  have hJ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) := by
    simp only [jacInf, Complex.ofReal_prod, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    exact contDiff_prod fun w _ => ((Complex.conjCLE.contDiff.comp (hdet w)).mul (hdet w)).pow n
  have hΦ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 :=
    ((hχ.comp contDiff_fst).mul hJ).mul (hα.comp contDiff_snd)
  have hΦc : HasCompactSupport fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 := by
    refine HasCompactSupport.intro (hχc.isCompact.prod hαc.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  obtain ⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_rapid_superposition_characters' _ _ hΦ hΦc
  obtain ⟨R, hR⟩ := GlobalTheory.T.smoothing_affine_family_eq_integral_kernel E n Z σ₀ L χ α hχc hσ hαc hαs X ν κ τ h1 h2 h3 (fun z a => h4 (z, a))
  exact GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily E n Z T hT _ _ _ _ _ (GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ h1 h2 h3 R σ₀ L) (smoothMatInf α) _ χ
    (GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth E n α hα.continuous hαc hαs) hR

end GlobalTheory.JSW.MirCinf
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

theorem _root_.GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ N : ℕ, 1 ≤ N ∧ ∀ w : (κ → AF F) × (κ → AF F),
      (∀ i, (w.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.1 i) ∧ (w.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.2 i)) →
      schr ψ w Φ = Φ := by
  first | exact @GlobalTheory.FinSuppHeis.heis_fix_finDiv | exact GlobalTheory.FinSuppHeis.heis_fix_finDiv | (intros; apply GlobalTheory.FinSuppHeis.heis_fix_finDiv <;> assumption)
end

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil


theorem _root_.GlobalTheory.T.latticeIntertwinerRep_trivial_realPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  first | exact @GlobalTheory.FinLatF.IsLatRepF.real_triv | exact GlobalTheory.FinLatF.IsLatRepF.real_triv | (intros; apply GlobalTheory.FinLatF.IsLatRepF.real_triv <;> assumption)
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.continuous_adelicAction_realCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  first | exact @GlobalTheory.RealWeilF.MCont.continuous_mMF | exact GlobalTheory.RealWeilF.MCont.continuous_mMF | (intros; apply GlobalTheory.RealWeilF.MCont.continuous_mMF <;> assumption)
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.realCoordinateAction_unitary_preserves_hermitianForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ p : GAF σ JS × GAF σ JT, (mMF σ JS JT θ p)ᴴ * HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) * mMF σ JS JT θ p = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) := by
  first | exact @GlobalTheory.RealWeilF.mMF_unitary | exact GlobalTheory.RealWeilF.mMF_unitary | (intros; apply GlobalTheory.RealWeilF.mMF_unitary <;> assumption)
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.adelicHomAction_realCoordinates_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (g : GAF σ JS) (h : GAF σ JT) (v : IxF F nS nT → ℂ),
        actOF σ JS JT g h (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) := by
  first | exact @GlobalTheory.RealWeilF.actOF_iotaVF | exact GlobalTheory.RealWeilF.actOF_iotaVF | (intros; apply GlobalTheory.RealWeilF.actOF_iotaVF <;> assumption)
end
