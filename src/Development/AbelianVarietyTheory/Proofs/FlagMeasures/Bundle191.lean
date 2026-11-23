module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle174
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle172
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.RowDomain

attribute [local instance] GlobalTheory.HomCovolume.haar_two GlobalTheory.HomCovolume.haar_three

noncomputable def rowLat (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) : Submodule ℤ (VecInf E k) :=
  AddSubgroup.toIntSubmodule
  { carrier := {z | ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ z = fun w b => w.embedding (τ b)}
    zero_mem' := ⟨0, fun y _ => by simp only [zero_dotProduct]; exact Λ₀.zero_mem, by funext w b; simp⟩
    add_mem' := by
      rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
      refine ⟨σ + τ, fun y hy => ?_, by funext w b; simp⟩
      have := Λ₀.add_mem (hσ y hy) (hτ y hy)
      convert this using 1
      funext _; simp
    neg_mem' := by
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨-τ, fun y hy => ?_, by funext w b; simp⟩
      have := Λ₀.neg_mem (hτ y hy)
      convert this using 1
      funext _; simp }

theorem mem_rowLat {E : Type} [Field E] [NumberField E] {k : ℕ} {Λ₀ : Submodule (𝓞 E) (Fin 1 → E)}
    {Λ' : Submodule (𝓞 E) (Fin k → E)} {z : VecInf E k} : z ∈ rowLat E k Λ₀ Λ' ↔
    ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ z = fun w b => w.embedding (τ b) := by
  rfl

theorem hasCov_rowLat (E : Type) [Field E] [NumberField E] (hE : IsTotallyComplex E) (k : ℕ)
    (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)) (h₀ : Submodule.IsFullLattice E Λ₀)
    (h' : Submodule.IsFullLattice E Λ') : GlobalTheory.HomCovolume.HasCov volume (rowLat E k Λ₀ Λ')
      (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k *
        (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) := by
  classical

  let e : VecInf E k ≃L[ℝ] (InfinitePlace E → Fin 1 → Fin k → ℂ) :=
    (LinearEquiv.piCongrRight fun _ : InfinitePlace E =>
      (LinearEquiv.funUnique (Fin 1) ℝ (Fin k → ℂ)).symm).toContinuousLinearEquiv
  have hes : ∀ x w b, e.symm x w b = x w 0 b := fun _ _ _ => rfl
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_pi fun _ : InfinitePlace E =>
      MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) (Fin k → ℂ))
  let L' : Submodule ℤ (InfinitePlace E → Fin 1 → Fin k → ℂ) :=
    (rowLat E k Λ₀ Λ').comap ((e.symm : _ →L[ℝ] VecInf E k).toLinearMap.restrictScalars ℤ)
  have hL' : ∀ z, z ∈ L' ↔ e.symm z ∈ rowLat E k Λ₀ Λ' := fun _ => Iff.rfl
  refine GlobalTheory.HomCovolume.HasCov.of_measurePreserving e hmp (L' := L')
    (fun x => by rw [hL', ContinuousLinearEquiv.symm_apply_apply]) ?_
  have hpos : ∀ j, 0 < GlobalTheory.FlagMeas.detNorm E j (oneInf E j) := fun j => by rw [detNorm_oneInf]; exact one_pos
  obtain ⟨hd, hz, hc⟩ := GlobalTheory.HomCovolume.homCovolume E hE 1 k Λ₀ Λ' h₀ h' (oneInf E 1) (oneInf E k)
    (hpos 1) (hpos k) L' (by
      intro z
      rw [hL', mem_rowLat]
      simp only [of_oneInf, inv_one]
      constructor
      · rintro ⟨τ, hτ, hzτ⟩
        refine ⟨Matrix.of fun _ b => τ b, fun y hy => ?_, fun w => ?_⟩
        · exact hτ y hy
        · ext i b
          fin_cases i
          have := congrFun (congrFun hzτ w) b
          simpa [hes] using this
      · rintro ⟨T, hT, hTz⟩
        refine ⟨fun b => T 0 b, fun y hy => ?_, ?_⟩
        · convert hT y hy using 1
          funext i
          fin_cases i
          rfl
        · funext w b
          have := congrFun (congrFun (hTz w) 0) b
          simpa [hes] using this)
  exact ⟨hd, hz, by rw [hc, pow_one]⟩

theorem rowDomain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → ∃ P : Set (VecInf E k), MeasurableSet P ∧ volume P = ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) ∧ (∀ T : VecInf E k, ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ (fun w b => T w b + w.embedding (τ b)) ∈ P) ∧ ∀ (T : VecInf E k) (τ : Fin k → E), (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) → T ∈ P → (fun w b => T w b + w.embedding (τ b)) ∈ P → τ = 0 := by
  intro E _ _ hE k Λ₀ Λ' h₀ h'
  obtain ⟨hd, hz, hc⟩ := hasCov_rowLat E hE k Λ₀ Λ' h₀ h'

  let b := Module.Free.chooseBasis ℤ (rowLat E k Λ₀ Λ')
  have hspan := b.ofZLatticeBasis_span ℝ
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (VecInf E k))
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZSpan.fundamentalDomain_measurableSet _,
    ?_, fun T => ?_, fun T τ hτ hT hT' => ?_⟩
  · rw [← hc, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF]
    have hfin : (volume : Measure (VecInf E k)) (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top.ne
    exact (ofReal_measureReal hfin).symm
  · obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) T
    have hvL : (v : VecInf E k) ∈ rowLat E k Λ₀ Λ' := hspan.le v.2
    obtain ⟨τ, hτ, hvτ⟩ := mem_rowLat.1 hvL
    refine ⟨τ, hτ, ?_⟩
    convert hv using 1
    rw [Submodule.vadd_def, vadd_eq_add, hvτ]
    funext w b
    simp [add_comm]
  · have hzL : (fun (w : InfinitePlace E) (b : Fin k) => w.embedding (τ b)) ∈
        Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ)) :=
      hspan.ge (mem_rowLat.2 ⟨τ, hτ, rfl⟩)
    have hu := (ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) T).unique
      (y₁ := ⟨_, hzL⟩) (y₂ := 0) (by
        rw [Submodule.vadd_def, vadd_eq_add]
        convert hT' using 1
        funext w b
        simp [add_comm]) (by simpa using hT)
    have h0 : (fun (w : InfinitePlace E) (b : Fin k) => w.embedding (τ b)) = 0 :=
      congrArg Subtype.val hu
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    funext b
    have := congrFun (congrFun h0 w) b
    simpa using this

end GlobalTheory.RowDomain
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
open GlobalTheory.LatFacts Module

noncomputable section

namespace GlobalTheory.CovProd

variable (E : Type) [Field E] [NumberField E] (k : ℕ)

def splitVec : (VecInf E 1 × VecInf E k) ≃ₗ[ℝ] VecInf E (k + 1) where
  toFun p w := Fin.cons (p.1 w 0) (p.2 w)
  invFun x := (fun w _ => x w 0, fun w => Fin.tail (x w))
  map_add' p q := by
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  map_smul' c p := by
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  left_inv p := by
    refine Prod.ext ?_ ?_
    · funext w a
      rw [Subsingleton.elim a 0]
      simp
    · funext w
      simp
  right_inv x := by
    funext w
    simp

theorem mem_fd_prod {ι κ : Type} [Fintype ι] [Fintype κ] (b : Basis ι ℝ (VecInf E 1)) (c : Basis κ ℝ (VecInf E k))
    (x : VecInf E (k + 1)) :
    x ∈ ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) ↔
      ((splitVec E k).symm x).1 ∈ ZSpan.fundamentalDomain b ∧
        ((splitVec E k).symm x).2 ∈ ZSpan.fundamentalDomain c := by
  rw [← ZSpan.map_fundamentalDomain, LinearEquiv.image_eq_preimage_symm, Set.mem_preimage,
    ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, Sum.forall]
  simp only [Basis.prod_repr_inl, Basis.prod_repr_inr]

private theorem measurePreserving_splitVec_symm :
    MeasurePreserving (fun x : VecInf E (k + 1) => (splitVec E k).symm x) volume volume := by
  have h1 : MeasurePreserving
      (fun (x : InfinitePlace E → Fin (k + 1) → ℂ) w =>
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0 (x w))
      (Measure.pi fun _ => Measure.pi fun _ => (volume : Measure ℂ))
      (Measure.pi fun _ => (volume : Measure ℂ).prod (Measure.pi fun _ : Fin k => (volume : Measure ℂ))) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_piFinSuccAbove (fun _ => volume) 0
  have h2 := measurePreserving_arrowProdEquivProdArrow ℂ (Fin k → ℂ) (InfinitePlace E)
    (fun _ => (volume : Measure ℂ)) (fun _ => Measure.pi fun _ : Fin k => (volume : Measure ℂ))
  have h3 : MeasurePreserving
      (fun (y : InfinitePlace E → ℂ) w => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (y w))
      (Measure.pi fun _ => (volume : Measure ℂ))
      (Measure.pi fun _ => Measure.pi fun _ : Fin 1 => (volume : Measure ℂ)) :=
    measurePreserving_pi _ _ fun _ =>
      MeasurePreserving.symm _ (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1))
  have h4 := (h3.prod (MeasurePreserving.id
    (Measure.pi fun _ : InfinitePlace E => Measure.pi fun _ : Fin k => (volume : Measure ℂ)))).comp (h2.comp h1)
  convert h4 using 1
  all_goals rfl

theorem covAt_prod (b : Basis (Idx E 1) ℝ (VecInf E 1)) (c : Basis (Idx E k) ℝ (VecInf E k)) :
    covAt E (k + 1) (Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k)))) =
      covAt E 1 (Submodule.span ℤ (Set.range b)) * covAt E k (Submodule.span ℤ (Set.range c)) := by
  rw [covAt_span, covAt_span, covAt_span]
  have hs : ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) =
      (fun x => (splitVec E k).symm x) ⁻¹' (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c) := by
    ext x
    rw [mem_fd_prod]
    rfl
  have hm : MeasurableSet (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c) :=
    (ZSpan.fundamentalDomain_measurableSet b).prod (ZSpan.fundamentalDomain_measurableSet c)
  rw [hs, measureReal_def, (measurePreserving_splitVec_symm E k).measure_preimage hm.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul, measureReal_def, measureReal_def]

theorem latAt_oneInf (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) :
    latAt E j Λ (oneInf E j) = Submodule.span ℤ (emb E j '' (Λ : Set (Fin j → E))) := by
  simp only [latAt, of_oneInf, inv_one, one_mulVec]
  rfl

theorem span_prod {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module ℝ M] [Module ℝ N] {ι κ : Type}
    (b : Basis ι ℝ M) (c : Basis κ ℝ N) :
    Submodule.span ℤ (Set.range (b.prod c)) =
      (Submodule.span ℤ (Set.range b)).prod (Submodule.span ℤ (Set.range c)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rcases i with i | i
    · refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [Basis.prod_apply_inl_fst]
        exact Submodule.subset_span ⟨i, rfl⟩
      · rw [Basis.prod_apply_inl_snd]
        exact zero_mem _
    · refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [Basis.prod_apply_inr_fst]
        exact zero_mem _
      · rw [Basis.prod_apply_inr_snd]
        exact Submodule.subset_span ⟨i, rfl⟩
  · rintro ⟨x, y⟩ hxy
    rw [Submodule.mem_prod] at hxy
    have hx : Submodule.span ℤ (Set.range b) ≤
        (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inl ℤ M N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨Sum.inl i, ?_⟩
      exact Prod.ext (Basis.prod_apply_inl_fst b c i) (Basis.prod_apply_inl_snd b c i)
    have hy : Submodule.span ℤ (Set.range c) ≤
        (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inr ℤ M N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨Sum.inr i, ?_⟩
      exact Prod.ext (Basis.prod_apply_inr_fst b c i) (Basis.prod_apply_inr_snd b c i)
    have h := add_mem (Submodule.mem_comap.1 (hx hxy.1)) (Submodule.mem_comap.1 (hy hxy.2))
    simpa using h

theorem covAt_latAt_prod : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → covAt E (k + 1) (latAt E (k + 1) Λ (oneInf E (k + 1))) = covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) * covAt E k (latAt E k Λ' (oneInf E k)) := by
  intro E _ _ hE k Λ Λ₀ Λ' h₀ h' hΛ
  rw [latAt_oneInf, latAt_oneInf, latAt_oneInf]
  obtain ⟨b, hb⟩ := exists_basis E 1 Λ₀ h₀
  obtain ⟨c, hc⟩ := exists_basis E k Λ' h'

  set s : (VecInf E 1 × VecInf E k) →ₗ[ℤ] VecInf E (k + 1) :=
    (splitVec E k).toLinearMap.restrictScalars ℤ with hs
  have hsv : ∀ p, s p = splitVec E k p := fun p => rfl

  have hemb : ∀ y : Fin (k + 1) → E,
      emb E (k + 1) y = s (emb E 1 (fun _ => y 0), emb E k (Fin.tail y)) := by
    intro y
    rw [hsv]
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a
    · rfl
    · simp [splitVec, emb, Fin.tail]
  have key : Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E))) =
      Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k))) := by
    have hr : Set.range ((b.prod c).map (splitVec E k)) = s '' Set.range (b.prod c) := by
      rw [Basis.coe_map, Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, span_prod, ← hb, ← hc]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hy' := (hΛ y).1 hy
      refine Submodule.mem_map.2 ⟨(emb E 1 (fun _ => y 0), emb E k (Fin.tail y)),
        Submodule.mem_prod.2 ⟨Submodule.subset_span ⟨_, hy'.1, rfl⟩,
          Submodule.subset_span ⟨_, hy'.2, rfl⟩⟩, (hemb y).symm⟩
    · rw [Submodule.map_le_iff_le_comap]
      rintro ⟨u, v⟩ huv
      rw [Submodule.mem_prod] at huv
      have hu : Submodule.span ℤ (emb E 1 '' (Λ₀ : Set (Fin 1 → E))) ≤
          (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap
            (s.comp (LinearMap.inl ℤ _ _)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        have hz0 : (fun _ : Fin 1 => z 0) = z := by
          funext i
          rw [Subsingleton.elim i 0]
        have hmem : (Fin.cons (z 0) (0 : Fin k → E) : Fin (k + 1) → E) ∈ Λ := by
          refine (hΛ _).2 ⟨?_, ?_⟩
          · simpa only [Fin.cons_zero] using hz0 ▸ hz
          · simpa only [Fin.tail_cons] using zero_mem Λ'
        refine Submodule.subset_span ⟨_, hmem, ?_⟩
        rw [hemb, Fin.tail_cons, map_zero]
        simp only [Fin.cons_zero, hz0, LinearMap.comp_apply, LinearMap.inl_apply]
      have hv : Submodule.span ℤ (emb E k '' (Λ' : Set (Fin k → E))) ≤
          (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap
            (s.comp (LinearMap.inr ℤ _ _)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        have hmem : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
          refine (hΛ _).2 ⟨?_, ?_⟩
          · convert zero_mem Λ₀ using 1
            funext i
            simp
          · rw [Fin.tail_cons]
            exact hz
        refine Submodule.subset_span ⟨_, hmem, ?_⟩
        rw [hemb, Fin.tail_cons]
        simp only [Fin.cons_zero, LinearMap.comp_apply, LinearMap.inr_apply]
        congr 2
        exact map_zero (emb E 1)
      have h := add_mem (Submodule.mem_comap.1 (hu huv.1)) (Submodule.mem_comap.1 (hv huv.2))
      rw [Submodule.mem_comap]
      simpa [← map_add (f := _)] using h
  rw [key, hb, hc]
  exact covAt_prod E k b c

end GlobalTheory.CovProd
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm Module
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CovIdeal

open GlobalTheory.LatFacts

variable (E : Type) [Field E] [NumberField E]

def lat (I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 1 → E) :=
  (I : Submodule (𝓞 E) E).comap (LinearMap.proj 0)

theorem mem_lat (I : FractionalIdeal (𝓞 E)⁰ E) (y : Fin 1 → E) : y ∈ lat E I ↔ y 0 ∈ I := by
  simp [lat]

theorem lat_eq_map (I : FractionalIdeal (𝓞 E)⁰ E) :
    lat E I = (I : Submodule (𝓞 E) E).map (LinearMap.single (𝓞 E) (fun _ : Fin 1 => E) 0) := by
  ext y
  rw [mem_lat, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨y 0, h, ?_⟩
    funext a
    fin_cases a
    simp
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

theorem isLattice_lat (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) : Submodule.IsLattice E (lat E I) := by
  apply Submodule.IsLattice.of_fg
  rw [lat_eq_map]
  exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).map _

theorem latAt_lat [_root_.NumberField.IsTotallyComplex E] (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    latAt E 1 (lat E I.1) (oneInf E 1) = Submodule.span ℤ (Set.range
      ((Pi.basis fun _ : Fin 1 => mixedEmbedding.fractionalIdealLatticeBasis E I).map (mix E 1))) := by
  set B := mixedEmbedding.fractionalIdealLatticeBasis E I

  let φ : mixedEmbedding.mixedSpace E →ₗ[ℤ] VecInf E 1 :=
    ((mix E 1).toLinearMap.toAddMonoidHom.comp
      (AddMonoidHom.single (fun _ : Fin 1 => mixedEmbedding.mixedSpace E) 0)).toIntLinearMap
  have hφ : ∀ z, φ z = mix E 1 (Pi.single 0 z) := fun _ => rfl

  have key : ∀ (y : Fin 1 → E) (w : InfinitePlace E),
      (Matrix.of (oneInf E 1 w))⁻¹ *ᵥ (fun a => w.embedding (y a)) = φ (mixedEmbedding E (y 0)) w := by
    intro y w
    rw [of_oneInf, inv_one, one_mulVec, hφ]
    funext a
    fin_cases a
    simp [mix_apply]
  have hrange : Set.range ((Pi.basis fun _ : Fin 1 => B).map (mix E 1)) = φ '' Set.range B := by
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, rfl⟩
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      exact ⟨B k, ⟨k, rfl⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨⟨0, k⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩

  have hspan : Submodule.span ℤ (mixedEmbedding E '' (I.1 : Set E)) = Submodule.span ℤ (Set.range B) := by
    conv_rhs => rw [← Submodule.span_eq (Submodule.span ℤ (Set.range B))]
    congr 1
    ext x
    rw [SetLike.mem_coe, mixedEmbedding.mem_span_fractionalIdealLatticeBasis]
  unfold latAt
  rw [hrange, Submodule.span_image, ← hspan, ← Submodule.span_image, ← Set.image_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y 0, (mem_lat E _ y).1 hy, funext fun w => (key y w).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨fun _ => t, (mem_lat E _ _).2 ht, funext fun w => key _ w⟩

theorem covAt_lat [_root_.NumberField.IsTotallyComplex E] (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    covAt E 1 (latAt E 1 (lat E I.1) (oneInf E 1)) =
      (FractionalIdeal.absNorm I.1 : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E := by

  have hO := volume_fd_intB E 1
  rw [mul_one, intB, volume_fd_map, pow_one, measureReal_def] at hO

  rw [latAt_lat, covAt_span, volume_fd_map, pow_one, measureReal_def,
    mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hO]

theorem covolume_inv_ideal : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ Λ₀ : Submodule (𝓞 E) (Fin 1 → E), (∀ y, y ∈ Λ₀ ↔ ∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Submodule.IsLattice E Λ₀ ∧ covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) := by
  intro E _ _ hE 𝔞 h𝔞
  have hne : (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

  let J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ (inv_ne_zero hne)
  refine ⟨lat E J.1, fun y => ?_, isLattice_lat E J.1 (inv_ne_zero hne), ?_⟩
  · rw [mem_lat]
    change y 0 ∈ (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔ _
    rw [FractionalIdeal.mem_inv_iff hne]
    constructor
    · intro h t ht
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
        (h (t : E) (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
      exact ⟨r, by rw [hr, mul_comm]⟩
    · intro h x hx
      obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      obtain ⟨r, hr⟩ := h t ht
      exact (FractionalIdeal.mem_one_iff _).2 ⟨r, by rw [hr, mul_comm]⟩
  · have := hE
    rw [covAt_lat E J]
    change (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : ℝ) * _ = _
    rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    ring

end GlobalTheory.CovIdeal
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.farTermsModerateRegion_of_flagBound : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  first | exact @GlobalTheory.Deep.farModerate_of_farBound | exact GlobalTheory.Deep.farModerate_of_farBound | (intros; apply GlobalTheory.Deep.farModerate_of_farBound <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.lowestKType_decayGap_of_compressionFormulaGap : FormulaGap → DecGap := by
  first | exact @GlobalTheory.DecGapBound.decGap_of_formulaGap | exact GlobalTheory.DecGapBound.decGap_of_formulaGap | (intros; apply GlobalTheory.DecGapBound.decGap_of_formulaGap <;> assumption)
end
