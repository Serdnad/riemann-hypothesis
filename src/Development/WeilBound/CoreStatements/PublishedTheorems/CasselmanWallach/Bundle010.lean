module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

private theorem sobNorm_append' {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → H →L[ℂ] H) (S A : List (List (Mx n))) (w : H) :
    sobNorm σ (S ++ A) w = sobNorm σ S w + sobNorm σ A w := by
  simp [sobNorm, List.map_append, List.sum_append]

private theorem sobNorm_nonneg' {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → H →L[ℂ] H) (S : List (List (Mx n))) (w : H) : 0 ≤ sobNorm σ S w := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  exact norm_nonneg _

private theorem exists_sobNorm_bound_of_sobBdOn_continuous_seminorm {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (σ : Mx n → H →L[ℂ] H) (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p) (T : H →ₗ[ℂ] E)
    (hT : SobBdOn ε σ (Sm ε σ) p T) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ w, Sm ε σ w → q (T w) ≤ C * sobNorm σ S w := by
  have key : ∀ s : Finset ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ w, Sm ε σ w → ∑ j ∈ s, p j (T w) ≤ C * sobNorm σ S w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨[], 0, fun l hl => by simp at hl, le_rfl, fun w _ => by simp⟩
    | insert j s hj ih =>
      obtain ⟨S, C, hS, hC, hb⟩ := ih
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hT j
      refine ⟨S₁ ++ S, max C₁ 0 + C, ?_, by positivity, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · exact hS₁ l h
        · exact hS l h
      · intro w hw
        rw [Finset.sum_insert hj, sobNorm_append']
        have h1 := hb₁ w hw
        have h2 := hb w hw
        have n1 := sobNorm_nonneg' σ S₁ w
        have n2 := sobNorm_nonneg' σ S w
        have h3 : C₁ * sobNorm σ S₁ w ≤ max C₁ 0 * sobNorm σ S₁ w :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC n1]
  obtain ⟨s, C0, -, hle⟩ := Seminorm.bound_of_continuous hp q hq
  obtain ⟨S, C, hS, hC, hb⟩ := key s
  refine ⟨S, C0 * C, hS, mul_nonneg C0.2 hC, fun w hw => ?_⟩
  have hsup : (s.sup p) (T w) ≤ ∑ j ∈ s, p j (T w) :=
    Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      (fun i hi => Finset.single_le_sum (f := fun j => p j (T w)) (fun _ _ => apply_nonneg _ _) hi)
  calc q (T w) ≤ (C0 • s.sup p) (T w) := Seminorm.le_def.1 hle (T w)
    _ = (C0 : ℝ) * (s.sup p) (T w) := by rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    _ ≤ (C0 : ℝ) * ∑ j ∈ s, p j (T w) := mul_le_mul_of_nonneg_left hsup C0.2
    _ ≤ (C0 : ℝ) * (C * sobNorm σ S w) := mul_le_mul_of_nonneg_left (hb w hw) C0.2
    _ = C0 * C * sobNorm σ S w := by ring

theorem d3 : D3 := by
  intro hD0 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hDens T hT hSob w hw
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
  have hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ := hU
  have hp := hπ.withSeminorms
  constructor
  · intro k hk
    have hkU : k ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) := by
      show kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε
      have h1 : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
      rw [mul_assoc, ← hk.2, ← mul_assoc, ← Matrix.star_eq_conjTranspose, h1, one_mul]
    have hkUJ : k ∈ UJset ε := hkU
    let T' : H →ₗ[ℂ] E := T ∘ₗ (σ k).toLinearMap - (π k).toLinearMap ∘ₗ T
    have hT' : ∀ v, T' v = T (σ k v) - π k (T v) := fun _ => rfl
    have hsob : SobBdOn ε σ (Sm ε σ) p T' := by
      intro i
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hSob i
      obtain ⟨S₂, C₂, hS₂, hC₂, hb₂⟩ := exists_sobNorm_bound_of_sobBdOn_continuous_seminorm σ p hp T hSob ((p i).comp (π k).toLinearMap)
        ((hp.continuous_seminorm i).comp (π k).continuous)
      refine ⟨S₁.map (List.map fun X => k⁻¹ * X * k) ++ S₂, max C₁ 0 + C₂, ?_, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
          intro Y hY
          obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
          exact conj_mem_lie hJu hkU (hS₁ l' hl' X hX)
        · exact hS₂ l h
      · intro v hv
        have hsv : σ k v ∈ smooth (Formalism.REAL.Jm ε) σ := translate_mem hJu hU' hkU hv
        have heq : sobNorm σ S₁ (σ k v) =
            sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v := by
          unfold sobNorm
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro l hl
          simp only [Function.comp_apply]
          rw [word_translate hJu hU' hkU hv l (fun X hX => hS₁ l hl X hX), hU.2.1 k hkUJ,
            List.foldr_map]
        have h1 := hb₁ (σ k v) hsv
        have h2 := hb₂ v hv
        have n1 := sobNorm_nonneg' σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v
        have n2 := sobNorm_nonneg' σ S₂ v
        rw [heq] at h1
        rw [hT', sobNorm_append']
        have h3 : (p i) (T (σ k v) - π k (T v)) ≤ p i (T (σ k v)) + p i (π k (T v)) :=
          map_sub_le_add _ _ _
        have h4 : ((p i).comp (π k).toLinearMap) (T v) = p i (π k (T v)) := rfl
        rw [h4] at h2
        have h5 : C₁ * sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v ≤
            max C₁ 0 * sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC₂ n1]
    have h0 := hD0 n ε H σ hU hI E p π dπ hπ hDens T' hsob
      (fun v hv => by rw [hT', hT.1 k hk v hv, sub_self]) w hw
    rw [hT'] at h0
    exact sub_eq_zero.1 h0
  · intro X hX
    obtain ⟨L, hL⟩ := exists_word hJu hU' [X] (fun Y hY => by
      rw [List.mem_singleton] at hY
      rw [hY]
      exact hX)
    let f : smooth (Formalism.REAL.Jm ε) σ →ₗ[ℂ] E :=
      T ∘ₗ (smooth (Formalism.REAL.Jm ε) σ).subtype ∘ₗ L -
        (dπ X).toLinearMap ∘ₗ T ∘ₗ (smooth (Formalism.REAL.Jm ε) σ).subtype
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f
    have hgw : ∀ v (hv : Sm ε σ v), g v = T (dRep σ X v) - dπ X (T v) := by
      intro v hv
      have h := LinearMap.congr_fun hg ⟨v, hv⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
      rw [h]
      simp only [f, LinearMap.sub_apply, LinearMap.comp_apply, Submodule.subtype_apply, hL,
        List.foldr_cons, List.foldr_nil, ContinuousLinearMap.coe_coe]
    have hsob : SobBdOn ε σ (Sm ε σ) p g := by
      intro i
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hSob i
      obtain ⟨S₂, C₂, hS₂, hC₂, hb₂⟩ := exists_sobNorm_bound_of_sobBdOn_continuous_seminorm σ p hp T hSob ((p i).comp (dπ X).toLinearMap)
        ((hp.continuous_seminorm i).comp (dπ X).continuous)
      refine ⟨S₁.map (fun l => l ++ [X]) ++ S₂, max C₁ 0 + C₂, ?_, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
          intro Y hY
          rcases List.mem_append.1 hY with h' | h'
          · exact hS₁ l' hl' Y h'
          · rw [List.mem_singleton.1 h']
            exact hX
        · exact hS₂ l h
      · intro v hv
        have hdv : Sm ε σ (dRep σ X v) := dRep_mem hJu hU' hv hX
        have heq : sobNorm σ S₁ (dRep σ X v) = sobNorm σ (S₁.map (fun l => l ++ [X])) v := by
          unfold sobNorm
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro l _
          simp [List.foldr_append]
        have h1 := hb₁ (dRep σ X v) hdv
        have h2 := hb₂ v hv
        have n1 := sobNorm_nonneg' σ (S₁.map (fun l => l ++ [X])) v
        have n2 := sobNorm_nonneg' σ S₂ v
        rw [heq] at h1
        rw [hgw v hv, sobNorm_append']
        have h3 : (p i) (T (dRep σ X v) - dπ X (T v)) ≤ p i (T (dRep σ X v)) + p i (dπ X (T v)) :=
          map_sub_le_add _ _ _
        have h4 : ((p i).comp (dπ X).toLinearMap) (T v) = p i (dπ X (T v)) := rfl
        rw [h4] at h2
        have h5 : C₁ * sobNorm σ (S₁.map (fun l => l ++ [X])) v ≤
            max C₁ 0 * sobNorm σ (S₁.map (fun l => l ++ [X])) v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC₂ n1]
    have h0 := hD0 n ε H σ hU hI E p π dπ hπ hDens g hsob
      (fun v hv => by rw [hgw v (hDens.1 v hv), hT.2 X hX v hv, sub_self]) w hw
    rw [hgw w hw] at h0
    exact sub_eq_zero.1 h0

end PositivityTheory.CW

end
end

section

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegative

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hs : adjSign ε a b = 1 := by simp [adjSign, hab]
  rw [hU a b, hs, one_mul, ← inner_conj_symm x, hU a b, hs, one_mul, inner_conj_symm]

end PositivityTheory.CW.CasimirNonnegative

namespace PositivityTheory.CW

open CasimirNonnegative in
theorem c2b : CardSubmodulesAndLinearEquivBounds := by
  intro n ε V _ _ E hGl hU hLF
  rw [eq_top_iff]
  intro v _
  obtain ⟨S, hfin, hvS, hstab⟩ := hLF v
  have hK : ∀ w ∈ S, casimirK ε E w ∈ S := by
    intro w hw
    unfold casimirK
    simp only [LinearMap.sum_apply, Module.End.mul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
    have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hstab a b hab.symm _ (hstab b a hab _ hw)
  let T : S →ₗ[ℂ] S := (casimirK ε E).restrict hK
  have hT : T.IsSymmetric := by
    intro x y
    exact casK_symm hU x y
  have hn : Module.finrank ℂ S = Module.finrank ℂ S := rfl
  have hsum := (hT.eigenvectorBasis hn).sum_repr ⟨v, hvS⟩
  have hv : v = ∑ i, ((hT.eigenvectorBasis hn).repr ⟨v, hvS⟩ i) • ((hT.eigenvectorBasis hn i : S) : V) := by
    have h0 := congrArg Subtype.val hsum
    simpa using h0.symm
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hT.eigenvalues hn i, ?_⟩)
  show casimirK ε E (hT.eigenvectorBasis hn i : V) = ((hT.eigenvalues hn i : ℝ) : ℂ) • (hT.eigenvectorBasis hn i : V)
  exact congrArg Subtype.val (hT.apply_eigenvectorBasis hn i)

end PositivityTheory.CW
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace PositivityTheory.CW.SeminormApproximation

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem sup_bound {p : ℕ → Seminorm ℂ E} {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) (s : Finset ℕ) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ x, Sm ε σ x → s.sup p (T x) ≤ C * sobNorm σ S x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨[], 0, fun l hl => by simp at hl, le_refl _, fun x _ => ?_⟩
    simp [Seminorm.bot_eq_zero]
  · intro i s _ ih
    obtain ⟨S, C, hS, hC, h⟩ := ih
    obtain ⟨S', C', hS', h'⟩ := hT i
    refine ⟨S' ++ S, |C'| + C, words_append hS' hS, by positivity, fun x hx => ?_⟩
    rw [Finset.sup_insert, Seminorm.sup_apply, sobNorm_append]
    have e1 := h x hx
    have e2 := h' x hx
    have a := sobNorm_nonneg σ S x
    have b := sobNorm_nonneg σ S' x
    have c1 := mul_nonneg (abs_nonneg C') a
    have c2 := mul_nonneg hC b
    have c3 := mul_nonneg hC a
    have c4 := mul_nonneg (abs_nonneg C') b
    have c5 := mul_le_mul_of_nonneg_right (le_abs_self C') b
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith

theorem q_bound {p : ℕ → Seminorm ℂ E} [TopologicalSpace E] (hp : WithSeminorms p) {T : H →ₗ[ℂ] E}
    (hT : SobBdOn ε σ (Sm ε σ) p T) (Q : Seminorm ℂ E) (hQ : Continuous Q) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ x, Sm ε σ x → Q (T x) ≤ C * sobNorm σ S x := by
  obtain ⟨s, C', -, hle⟩ := Seminorm.bound_of_continuous hp Q hQ
  obtain ⟨S, C, hS, hC, h⟩ := sup_bound hT s
  refine ⟨S, C' * C, hS, mul_nonneg (NNReal.coe_nonneg C') hC, fun x hx => ?_⟩
  have h1 : Q (T x) ≤ (C' • s.sup p) (T x) := hle (T x)
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
  calc Q (T x) ≤ C' * s.sup p (T x) := h1
    _ ≤ C' * (C * sobNorm σ S x) := mul_le_mul_of_nonneg_left (h x hx) (NNReal.coe_nonneg C')
    _ = _ := by ring

theorem approx (hD : Dens ε σ) {p : ℕ → Seminorm ℂ E} [TopologicalSpace E] (hp : WithSeminorms p)
    {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) (Q : Seminorm ℂ E) (hQ : Continuous Q) (l : List (Mx n))
    (hl : ∀ X ∈ l, X ∈ lieSet ε) (y : H) (hy : Sm ε σ y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v, IsKFin ε σ v ∧ Q (T (y - v)) ≤ δ ∧ ‖y - v‖ ≤ δ ∧ ‖Dw σ l (y - v)‖ ≤ δ := by
  obtain ⟨S, C, hS, hC, h⟩ := q_bound hp hT Q hQ
  have hW : Words (lieSet ε) (S ++ [l, []]) := by
    intro m hm X hX
    rcases List.mem_append.1 hm with hm | hm
    · exact hS m hm X hX
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact hl X hX
      · simp at hX
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨v, hv, hlt⟩ := hD.2.2 y hy (S ++ [l, []]) hW (δ / (C + 1)) (div_pos hδ hC1)
  have hsm : Sm ε σ (y - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hy) (sm_iff.1 (hD.1 v hv)))
  have e : sobNorm σ (S ++ [l, []]) (y - v) = sobNorm σ S (y - v) + (‖Dw σ l (y - v)‖ + ‖y - v‖) := by
    rw [sobNorm_append]
    congr 1
    simp [sobNorm]
  rw [e] at hlt
  have a := sobNorm_nonneg σ S (y - v)
  have n1 := norm_nonneg (Dw σ l (y - v))
  have n2 := norm_nonneg (y - v)
  have hρ : δ / (C + 1) ≤ δ := div_le_self hδ.le (by linarith)
  have hCρ : C * (δ / (C + 1)) ≤ δ := by
    have : (C + 1) * (δ / (C + 1)) = δ := by field_simp
    nlinarith [div_pos hδ hC1]
  refine ⟨v, hv, ?_, by linarith, by linarith⟩
  calc Q (T (y - v)) ≤ C * sobNorm σ S (y - v) := h _ hsm
    _ ≤ C * (δ / (C + 1)) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ ≤ δ := hCρ

end PositivityTheory.CW.SeminormApproximation

namespace PositivityTheory.CW

open SeminormApproximation in
theorem e2d : SobolevBoundedPairing := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT Q hQ l η C hl
  have hp := hπ.withSeminorms
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · refine le_of_forall_pos_le_add fun e he => ?_
    have hK : 0 < |C| + ‖η‖ + 1 := by positivity
    obtain ⟨v, hv, h1, h2, -⟩ := approx hD hp hT Q hQ l hl y hy (e / (|C| + ‖η‖ + 1)) (div_pos he hK)
    have hv' := h v hv
    have i1 : ‖⟪η, y⟫_ℂ‖ ≤ ‖⟪η, v⟫_ℂ‖ + ‖η‖ * ‖y - v‖ := by
      have : ⟪η, y⟫_ℂ = ⟪η, v⟫_ℂ + ⟪η, y - v⟫_ℂ := by rw [inner_sub_right]; ring
      rw [this]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_inner_le_norm _ _))
    have i2 : |Q (T v) - Q (T y)| ≤ Q (T (y - v)) := by
      rw [show T (y - v) = T y - T v from map_sub T y v, abs_sub_comm]
      exact abs_sub_map_le_sub Q (T y) (T v)
    have i3 : C * (Q (T v) - Q (T y)) ≤ |C| * Q (T (y - v)) := by
      have := le_abs_self (C * (Q (T v) - Q (T y)))
      rw [abs_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left i2 (abs_nonneg C))
    have i4 : C * Q (T v) = C * Q (T y) + C * (Q (T v) - Q (T y)) := by ring
    have i5 : |C| * Q (T (y - v)) + ‖η‖ * ‖y - v‖ ≤ e := by
      calc |C| * Q (T (y - v)) + ‖η‖ * ‖y - v‖
          ≤ |C| * (e / (|C| + ‖η‖ + 1)) + ‖η‖ * (e / (|C| + ‖η‖ + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg C)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
        _ = (|C| + ‖η‖) * (e / (|C| + ‖η‖ + 1)) := by ring
        _ ≤ (|C| + ‖η‖ + 1) * (e / (|C| + ‖η‖ + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (div_pos he hK).le
        _ = e := by field_simp
    linarith
  · refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨v, hv, h1, -, h3⟩ := approx hD hp hT Q hQ l hl y hy (e / 2) (by positivity)
    have hv' := h v hv
    have hsm : Sm ε σ (y - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hy) (sm_iff.1 (hD.1 v hv)))
    have hsplit : Dw σ l y = Dw σ l (y - v) + Dw σ l v := by
      have := Dw_add hU hl hsm (hD.1 v hv)
      rwa [sub_add_cancel] at this
    have i1 : ‖Dw σ l y‖ ≤ ‖Dw σ l (y - v)‖ + ‖Dw σ l v‖ := by
      rw [hsplit]; exact norm_add_le _ _
    have i2 : Q (T v) ≤ Q (T y) + Q (T (y - v)) := by
      have := map_sub_le_add Q (T y) (T (y - v))
      have e2 : T y - T (y - v) = T v := by rw [map_sub T y v, sub_sub_cancel]
      rwa [e2] at this
    linarith

end PositivityTheory.CW

end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace ZeroOnDense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
  {p : ℕ → Seminorm ℂ E}

theorem zero_on (hp : WithSeminorms p) (hD : Dens ε σ) (Φ : H → E)
    (hsub : ∀ x y, Sm ε σ x → Sm ε σ y → Φ (x - y) = Φ x - Φ y)
    (hb : ∀ i, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧
      ∀ u, Sm ε σ u → p i (Φ u) ≤ C * sobNorm σ S u)
    (h0 : ∀ v, IsKFin ε σ v → Φ v = 0) : ∀ w, Sm ε σ w → Φ w = 0 := by
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 _ hne
  obtain ⟨S, C, hS, hC⟩ := hb i
  have key : ∀ δ : ℝ, 0 < δ → p i (Φ w) ≤ |C| * δ := by
    intro δ hδ
    obtain ⟨v, hv, hd⟩ := hD.2.2 w hw S hS δ hδ
    have hvs : Sm ε σ v := hD.1 v hv
    have hwv : Sm ε σ (w - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hvs))
    have e : Φ w = Φ (w - v) := by rw [hsub w v hw hvs, h0 v hv, sub_zero]
    rw [e]
    calc p i (Φ (w - v)) ≤ C * sobNorm σ S (w - v) := hC _ hwv
      _ ≤ |C| * sobNorm σ S (w - v) := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hd.le (abs_nonneg C)
  have hpos : 0 < p i (Φ w) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hi)
  set x := p i (Φ w) with hx
  have h1 := key (x / (2 * (|C| + 1))) (by positivity)
  have h2 : |C| * (x / (2 * (|C| + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end ZeroOnDense

theorem d0 : D0 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT h0
  exact ZeroOnDense.zero_on hπ.withSeminorms hD T (fun x y _ _ => map_sub T x y) hT h0

end PositivityTheory.CW

end
end
