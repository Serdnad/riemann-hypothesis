module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle082
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle085
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (n : Type) [Fintype n] [DecidableEq n] (H L : Subgroup (GL n k)),
    H ≤ L → L ≤ KO k n → IsOpen (H : Set (GL n k)) →
    0 < (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal ∧
    (H.relIndex L : ℝ) * (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal =
      (volM ν n n (Units.val '' (L : Set (GL n k)))).toReal := by
  first | exact @GlobalTheory.IndexVolume.relIndex_mul_volM | exact GlobalTheory.IndexVolume.relIndex_mul_volM | (intros; apply GlobalTheory.IndexVolume.relIndex_mul_volM <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [Fintype D] (c : A → D → ℤ),
    volM ν A D {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} =
      ν (𝒪[k] : Set k) ^ (Fintype.card A * Fintype.card D) *
        ENNReal.ofReal ((resCard k : ℝ) ^ (-∑ i, ∑ j, c i j)) := by
  first | exact @GlobalTheory.BoxVolume.volM_box | exact GlobalTheory.BoxVolume.volM_box | (intros; apply GlobalTheory.BoxVolume.volM_box <;> assumption)
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.ModRel

theorem ew_append {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (l₁ l₂ : List (Fin n × Fin n)) : ew E (l₁ ++ l₂) = ew E l₁ * ew E l₂ := by
  induction l₁ with
  | nil => simp [ew]
  | cons p w ih => simp only [List.cons_append, ew, ih, mul_assoc]

theorem thetaA_one_onePositionArrayOfIsometry {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (G : Fin n × Fin n → W) : thetaA E 1 (arr1 j G) = ∑ p : Fin n × Fin n, E p.1 p.2 (j (G p)) := by
  rw [theta_map_word_sum_apply]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_
  simp [ew, arr1, arrTo]

theorem theta_vminus {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V} (hg : GlRel E)
    (h0 : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) :
    Vminus ε E Λ u ≤ LinearMap.ker (thetaA E 1) := by
  obtain ⟨-, hθ⟩ := (arrModule V n ε E 1).1 hg
  apply isotypic_part_le_of_forall
  intro y hy μ hμ hyh
  apply compact_span_le_of_stable
  · intro c d _ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hθ, hx, map_zero]
  · rw [LinearMap.mem_ker]
    obtain ⟨a, b, hba, hne, rfl⟩ := hμ
    have hμeq : Λ + root a b = Λ - root b a := by
      rw [root_swap' a b, sub_eq_add_neg]
    refine h0 b a hba (Ne.symm hne) _ ⟨fun c => ?_, fun c d hcd hcomp => ?_⟩
    · rw [← hθ, hyh.1 c, map_smul, hμeq]
    · rw [← hθ, hyh.2 c d hcd hcomp, map_zero]

theorem modJet_jetRel (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (u : V) (j : W →ₗᵢ[ℂ] V) (hL : LowData ε E Λ u j)
    (h0 : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) :
    JetRel ε E Λ u j (modJet E j) := by
  obtain ⟨hg, hu, -, -, -⟩ := hL
  refine ⟨fun l₁ l₂ a b c d => ?_, fun l a b _ y x x' hx => ?_, fun l a b hab y y' x hy => ?_,
    fun l G hG y => ?_⟩
  · have key : ew E (l₁ ++ (a, b) :: (c, d) :: l₂) - ew E (l₁ ++ (c, d) :: (a, b) :: l₂) =
        (if b = c then ew E (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then ew E (l₁ ++ (c, b) :: l₂) else 0) := by
      have h := hg a b c d
      simp only [ew_append, ew]
      rw [← mul_sub, ← mul_assoc (E a b), ← mul_assoc (E c d), ← sub_mul, h]
      split_ifs <;> simp [mul_sub, sub_mul]
    ext y x
    have h2 := congrArg (fun T : Module.End ℂ V => ⟪j y, T (j x)⟫_ℂ) key
    split_ifs at h2 ⊢ <;>
      simpa [modJet_apply, inner_sub_right] using h2
  · simp only [modJet_apply, ew_append, ew, hx, mul_one, Module.End.mul_apply]
  · simp only [modJet_apply, ew, hy, Module.End.mul_apply]
    rw [isUnitary_kUnit ε E hu b a hab.symm]
  · have h := theta_vminus hg h0 hG
    rw [LinearMap.mem_ker, thetaA_one_onePositionArrayOfIsometry] at h
    simp only [modJet_apply, ew_append, ew, mul_one, Module.End.mul_apply]

    rw [← inner_sum, ← map_sum, h, map_zero, inner_zero_right]

end GlobalTheory.SphJet.ModRel
end
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

theorem rev_ofFn_succ {A : Type} {m : ℕ} (α : Fin (m + 1) → A) :
    (List.ofFn α).reverse = α (Fin.last m) :: (List.ofFn (Fin.init α)).reverse := by
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  rfl

theorem wordFun_move_letter {M : Type} [AddCommGroup M] {n : ℕ} (B : List (Fin n × Fin n) → M)
    (hB : ∀ (l₁ l₂ : List (Fin n × Fin n)) (a b c d : Fin n),
      B (l₁ ++ (a, b) :: (c, d) :: l₂) - B (l₁ ++ (c, d) :: (a, b) :: l₂) =
        (if b = c then B (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then B (l₁ ++ (c, b) :: l₂) else 0))
    (c d : Fin n) : ∀ (m : ℕ) (α : Fin m → Fin n × Fin n) (p : List (Fin n × Fin n)),
      B (p ++ (c, d) :: (List.ofFn α).reverse) - B (p ++ ((List.ofFn α).reverse ++ [(c, d)])) =
        ∑ i, ((if d = (α i).1 then B (p ++ (List.ofFn (Function.update α i (c, (α i).2))).reverse) else 0) -
          (if (α i).2 = c then B (p ++ (List.ofFn (Function.update α i ((α i).1, d))).reverse) else 0)) := by
  intro m
  induction m with
  | zero => intro α p; simp
  | succ m ih =>
    intro α p
    rw [Fin.sum_univ_castSucc]
    have hl : ∀ q, (List.ofFn (Function.update α (Fin.last m) q)).reverse =
        q :: (List.ofFn (Fin.init α)).reverse := by
      intro q; rw [rev_ofFn_succ, Function.update_self, Fin.init_update_last]
    have hc : ∀ (i : Fin m) q, (List.ofFn (Function.update α i.castSucc q)).reverse =
        α (Fin.last m) :: (List.ofFn (Function.update (Fin.init α) i q)).reverse := by
      intro i q
      rw [rev_ofFn_succ, Function.update_of_ne (Fin.castSucc_ne_last i).symm, Fin.init_update_castSucc]
    simp only [hl, hc]
    have hi : ∀ i : Fin m, α i.castSucc = Fin.init α i := fun i => rfl
    simp only [hi]
    rw [rev_ofFn_succ α]
    have h1 := ih (Fin.init α) (p ++ [α (Fin.last m)])
    have h2 := hB p (List.ofFn (Fin.init α)).reverse c d (α (Fin.last m)).1 (α (Fin.last m)).2
    simp only [List.append_assoc, List.cons_append, List.nil_append, Prod.mk.eta] at h1 h2 ⊢
    rw [← h1, ← h2]
    abel

theorem jetRel_equivariant : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (m : ℕ), LowData ε E Λ u j → JetRel ε E Λ u j B → ∀ c d : Fin n, ε c = ε d → ∀ y y' : W, j y' = E d c (j y) → ∀ G G' : (Fin m → Fin n × Fin n) → W, arrTo V n m (fun α => j (G' α)) = arrE E m c d (arrTo V n m fun α => j (G α)) → ∑ α, B (List.ofFn α).reverse y (G' α) = ∑ α, B (List.ofFn α).reverse y' (G α) := by
  intro V W _ _ _ _ n ε E Λ u j B m hL hJ c d hcd y y' hy G G' hG
  have hex : ∀ x : W, ∃ x' : W, j x' = E c d (j x) := by
    intro x
    have h1 : j x ∈ kSpan ε E u := by
      rw [← hL.2.2.2.2]; exact ⟨x, rfl⟩
    have h2 := compact_span_compact_stable ε E u c d hcd _ h1
    rw [← hL.2.2.2.2] at h2
    exact h2
  choose T hT using hex
  have happ : ∀ (F : (Fin m → Fin n × Fin n) → V) α, arrTo V n m F α = F α := by
    intro F α; simp [arrTo]
  have hG' : ∀ α, G' α = ∑ i, ((if (α i).1 = c then G (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then G (Function.update α i ((α i).1, c)) else 0)) + T (G α) := by
    intro α
    apply j.injective
    have h := congrArg (fun F : Arr V n m => F α) hG
    simp only [arr_operator_apply, factorAction_apply', happ] at h

    rw [h, map_add (f := _), map_sum, hT]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hR : ∀ α : Fin m → Fin n × Fin n, B (List.ofFn α).reverse y' (G α) =
      ∑ i, ((if d = (α i).1 then B (List.ofFn (Function.update α i (c, (α i).2))).reverse y (G α) else 0) -
          (if (α i).2 = c then B (List.ofFn (Function.update α i ((α i).1, d))).reverse y (G α) else 0)) +
        B (List.ofFn α).reverse y (T (G α)) := by
    intro α
    have h := wordFun_move_letter (fun l => B l y (G α)) (fun l₁ l₂ a b c d => by
      have := congrArg (fun φ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ => φ y (G α)) (hJ.1 l₁ l₂ a b c d)
      simp only [LinearMap.sub_apply] at this
      rw [this]
      split_ifs <;> simp) c d m α []
    simp only [List.nil_append] at h
    rw [← h, hJ.2.1 _ c d hcd y (G α) _ (hT _), hJ.2.2.1 _ c d hcd y y' _ hy]
    ring

  simp only [hR, hG', map_add (f := _), map_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_sub, Finset.sum_sub_distrib]
  congr 1
  · refine ((Finset.sum_congr rfl fun α _ =>
      (apply_ite (B (List.ofFn α).reverse y) _ _ _).trans (by rw [map_zero]))).trans
      ((sum_update_first_index_swap i c d (fun α β => B (List.ofFn α).reverse y (G β))).trans ?_)
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases h : (β i).1 = d
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · exact ((Finset.sum_congr rfl fun α _ =>
      (apply_ite (B (List.ofFn α).reverse y) _ _ _).trans (by rw [map_zero]))).trans
      (sum_update_second_index_swap i c d (fun α β => B (List.ofFn α).reverse y (G β)))

end GlobalTheory.SphJet
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

theorem jetRel_perm_of_vanish_prefix {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V} {j : W →ₗᵢ[ℂ] V}
    {B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} {m : ℕ} (hB : JetRel ε E Λ u j B)
    (h0 : ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) {l l' : List (Fin n × Fin n)} (h : l.Perm l') :
    ∀ l₁ : List (Fin n × Fin n), (l₁ ++ l).length = m + 1 → B (l₁ ++ l) = B (l₁ ++ l') := by
  induction h with
  | nil => intro l₁ _; rfl
  | cons p _ ih =>
    intro l₁ hl
    have := ih (l₁ ++ [p]) (by simpa using hl)
    simpa using this
  | swap p q l =>
    intro l₁ hl
    obtain ⟨a, b⟩ := q
    obtain ⟨c, d⟩ := p
    have h1 := hB.1 l₁ l a b c d
    have hlen : ∀ r : Fin n × Fin n, B (l₁ ++ r :: l) = 0 := by
      intro r
      apply h0
      simp only [List.length_append, List.length_cons] at hl ⊢
      omega
    rw [hlen, hlen, ite_self, ite_self, sub_zero] at h1
    exact sub_eq_zero.mp h1
  | trans h₁ _ ih₁ ih₂ =>
    intro l₁ hl
    rw [ih₁ l₁ hl, ih₂ l₁ (by rw [← hl]; simp [h₁.length_eq])]

theorem jetRel_perm_and_compact_vanish :
    ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (m : ℕ), LowData ε E Λ u j → JetRel ε E Λ u j B → (∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) → (∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l') ∧ ∀ l : List (Fin n × Fin n), l.length = m + 1 → (∃ p ∈ l, ε p.1 = ε p.2) → B l = 0 := by
  intro V W _ _ _ _ n ε E Λ u j B m hL hB h0
  have hperm : ∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l' := by
    intro l l' h hl
    simpa using jetRel_perm_of_vanish_prefix hB h0 h [] (by simpa using hl)
  refine ⟨hperm, ?_⟩
  rintro l hl ⟨⟨a, b⟩, hp, hab⟩
  classical
  have hpe := List.perm_cons_erase hp
  have hlen : (l.erase (a, b)).length ≤ m := by
    have := hpe.length_eq
    simp only [List.length_cons] at this
    omega
  rw [hperm _ _ hpe hl]
  ext y x
  have hy : j y ∈ Formalism.REAL.kSpan ε E u := by
    rw [← hL.2.2.2.2]; exact ⟨y, rfl⟩
  have hy2 : E b a (j y) ∈ Formalism.REAL.kSpan ε E u := compact_span_compact_stable ε E u b a hab.symm _ hy
  rw [← hL.2.2.2.2] at hy2
  obtain ⟨y', hy'⟩ := hy2
  rw [hB.2.2.1 _ a b hab y y' x hy', h0 _ hlen]
  simp

end GlobalTheory.SphJet
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.Taylor

variable {n : ℕ}

theorem analyticAt_Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℂ (Rz Z f) 1 := by
  unfold Rz
  exact (ContinuousLinearMap.id ℂ (Matrix (Fin n) (Fin n) ℂ →L[ℂ] B)).analyticAt_bilinear _ |>.comp₂ hf.fderiv
    (analyticAt_id.mul analyticAt_const)

theorem analyticAt_Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ε : Fin n → Bool)
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (l : List (Fin n × Fin n)) :
    AnalyticAt ℂ (Rw ε l f) 1 := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact analyticAt_Rz ih _

theorem hasDerivAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun t : ℂ => NormedSpace.exp (t • Z)) (NormedSpace.exp (s • Z) * Z) s :=
  hasDerivAt_exp_smul_const Z s

theorem analyticAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => NormedSpace.exp (t • Z)) s :=
  Differentiable.analyticAt (fun t => (hasDerivAt_expC Z t).differentiableAt) s

theorem analyticAt_comp {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℝ (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) 0 := by
  have h1 : AnalyticAt ℂ (fun t : ℂ => L (g (NormedSpace.exp (t • Z)))) 0 :=
    (L.analyticAt _).comp (AnalyticAt.comp_of_eq hg (analyticAt_expC Z 0) (by simp))
  have h2 := AnalyticAt.comp_of_eq (h1.restrictScalars (𝕜 := ℝ)) (Complex.ofRealCLM.analyticAt 0) (by simp)
  exact h2

theorem deriv_comp_eventually {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) =ᶠ[𝓝 0]
      fun t : ℝ => L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z))) := by
  have hc : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) 0 :=
      (hasDerivAt_expC Z ((0 : ℝ) : ℂ)).continuousAt.comp Complex.continuous_ofReal.continuousAt
    simpa [ContinuousAt] using this
  filter_upwards [hc.eventually hg.eventually_analyticAt] with t ht
  have h1 : HasDerivAt (fun s : ℂ => L (g (NormedSpace.exp (s • Z))))
      (L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z)))) (t : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt _ (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_expC Z t))
  exact h1.comp_ofReal.deriv

theorem Rz_thM {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B) (z : Matrix (Fin n) (Fin n) ℂ) :
    Rz (thM ε X) g z = ∑ p : Fin n × Fin n, X p.1 p.2 • Rz (thE ε p) g z := by

  simp only [Rz, thM, Finset.mul_sum, map_sum, mul_smul_comm, map_smul]

theorem iteratedDeriv_inner_exp : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → (∀ l, funJet ε f l = modJet E j l) → ∀ (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (y x : W), iteratedDeriv m (fun t : ℝ => ⟪y, f (NormedSpace.exp ((t : ℂ) • thM ε X)) x⟫_ℂ) 0 = ⟪j y, (actM E X ^ m) (j x)⟫_ℂ := by
  intro V W _ _ _ _ n ε E _ j f hf hJ X m y x
  let L : (W →L[ℂ] W) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)
  have hL : ∀ T : W →L[ℂ] W, L T = ⟪y, T x⟫_ℂ := fun T => rfl
  have key : ∀ (m : ℕ) (l : List (Fin n × Fin n)),
      iteratedDeriv m (fun t : ℝ => L (Rw ε l f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
        ⟪j y, (actM E X ^ m) (ew E l (j x))⟫_ℂ := by
    intro m
    induction m with
    | zero =>
      intro l
      have := congrArg (fun B => B y x) (hJ l)
      simp only [funJet_apply, modJet_apply] at this
      simpa [hL] using this
    | succ m ih =>
      intro l
      rw [iteratedDeriv_succ', (deriv_comp_eventually (analyticAt_Rw ε hf l) L _).iteratedDeriv_eq]
      have e : (fun t : ℝ => L (Rz (thM ε X) (Rw ε l f) (NormedSpace.exp ((t : ℂ) • thM ε X)))) =
          fun t : ℝ => ∑ p : Fin n × Fin n,
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X))) := by
        funext t

        rw [Rz_thM, map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
      rw [e, iteratedDeriv_fun_sum (fun p _ =>
        contDiffAt_const.mul (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt)]
      have e2 : ∀ p : Fin n × Fin n, iteratedDeriv m (fun t : ℝ =>
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
          X p.1 p.2 * ⟪j y, (actM E X ^ m) (E p.1 p.2 (ew E l (j x)))⟫_ℂ := by
        intro p
        rw [iteratedDeriv_const_mul _ (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt, ih]
        simp [ew]
      simp only [e2]
      rw [pow_succ, Module.End.mul_apply]
      have e3 : ∀ v : V, actM E X v = ∑ p : Fin n × Fin n, X p.1 p.2 • E p.1 p.2 v := by
        intro v
        simp [actM, Fintype.sum_prod_type, LinearMap.sum_apply]

      rw [e3, map_sum, inner_sum]
      simp only [map_smul, inner_smul_right]
  simpa [hL, Rw, ew] using key m []

end GlobalTheory.SphJet.Taylor
end
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.matrixLengthExists_of_elementaryDivisors : Smith → FracExists := by
  first | exact @GlobalTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.InertZeta.fracExists_of_smith <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.unitary_levi_summation_geometric_series : Step := by
  first | exact @GlobalTheory.InertZeta.step | exact GlobalTheory.InertZeta.step | (intros; apply GlobalTheory.InertZeta.step <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.lattice_add_vector_det_valuation : AddVec := by
  first | exact @GlobalTheory.InertZeta.addVec | exact GlobalTheory.InertZeta.addVec | (intros; apply GlobalTheory.InertZeta.addVec <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.dual_inter_eq_sum' : Dual := by
  first | exact @GlobalTheory.InertZeta.dual_inter_eq_sum | exact GlobalTheory.InertZeta.dual_inter_eq_sum | (intros; apply GlobalTheory.InertZeta.dual_inter_eq_sum <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets : CosetIntegral := by
  first | exact @GlobalTheory.InertZeta.cosetIntegral_holds | exact GlobalTheory.InertZeta.cosetIntegral_holds | (intros; apply GlobalTheory.InertZeta.cosetIntegral_holds <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_duality : Heis → Dual → SmallCorner := by
  first | exact @GlobalTheory.InertZeta.smallCorner_of_heis_dual | exact GlobalTheory.InertZeta.smallCorner_of_heis_dual | (intros; apply GlobalTheory.InertZeta.smallCorner_of_heis_dual <;> assumption)
end
