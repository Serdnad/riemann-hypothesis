module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CyclicSplitting.IrrDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeSetChange

theorem abstract_change {ι X Z : Type} [Countable ι] {Y : ι → Type} [MeasurableSpace X]
    [MeasurableSpace Z] [∀ v, MeasurableSpace (Y v)] (ν : Measure X) (mi : Measure Z)
    (mv : ∀ v, Measure (Y v)) (p : X → Z) (q : ∀ v, X → Y v) (hq : ∀ v, Measurable (q v))
    (S T S' : Finset ι) (A L : ∀ v, Set (Y v)) (c : ℝ≥0∞)
    (hS' : ∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) (hd : Disjoint S T) (hA : ∀ v, MeasurableSet (A v))
    (hL : ∀ v ∉ S', A v = L v)
    (H : ∀ (fi : Z → ℝ≥0∞) (fv : ∀ v, Y v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x in {x | ∀ v ∉ S', q v x ∈ L v}, fi (p x) * ∏ v ∈ S', fv v (q v x) ∂ν =
        (∫⁻ y, fi y ∂mi) * (∏ v ∈ S', ∫⁻ y, fv v y ∂(mv v)) * c)
    (fi : Z → ℝ≥0∞) (fv : ∀ v, Y v → ℝ≥0∞) (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v)) :
    ∫⁻ x in {x | ∀ v ∉ S, q v x ∈ A v}, fi (p x) * ∏ v ∈ S, fv v (q v x) ∂ν =
      (∫⁻ y, fi y ∂mi) * (∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * c) := by
  classical
  have hSeq : S' = S ∪ T := by
    ext v; rw [hS', Finset.mem_union]
  subst hSeq
  have hmeas : ∀ U : Finset ι, MeasurableSet {x | ∀ v ∉ U, q v x ∈ A v} := by
    intro U
    have : {x | ∀ v ∉ U, q v x ∈ A v} = ⋂ v, ⋂ (_ : v ∉ U), q v ⁻¹' A v := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hq v (hA v)
  let gv : ∀ v, Y v → ℝ≥0∞ := fun v => if v ∈ S then fv v else (A v).indicator 1
  have hgS : ∀ v ∈ S, gv v = fv v := fun v hv => if_pos hv
  have hgT : ∀ v ∈ T, gv v = (A v).indicator 1 := fun v hv =>
    if_neg (fun h => Finset.disjoint_left.mp hd h hv)
  have hgm : ∀ v, Measurable (gv v) := by
    intro v
    by_cases hv : v ∈ S
    · rw [hgS v hv]; exact hfv v
    · have : gv v = (A v).indicator 1 := if_neg hv
      rw [this]; exact measurable_one.indicator (hA v)
  have h1 := H fi gv hfi hgm
  have hset : {x | ∀ v ∉ S ∪ T, q v x ∈ L v} = {x | ∀ v ∉ S ∪ T, q v x ∈ A v} := by
    ext x
    refine forall_congr' fun v => forall_congr' fun hv => ?_
    rw [hL v hv]
  rw [hset, Finset.prod_union hd, ← lintegral_indicator (hmeas _)] at h1
  have e1 : ∏ v ∈ S, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v) :=
    Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  have e2 : ∏ v ∈ T, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ T, mv v (A v) :=
    Finset.prod_congr rfl fun v hv => by rw [hgT v hv]; exact lintegral_indicator_one (hA v)
  rw [e1, e2] at h1
  rw [← lintegral_indicator (hmeas _), ← mul_assoc, mul_assoc (∫⁻ y, fi y ∂mi), ← h1]
  refine lintegral_congr fun x => ?_
  have e3 : ∏ v ∈ S, gv v (q v x) = ∏ v ∈ S, fv v (q v x) :=
    Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  by_cases hx : x ∈ {x | ∀ v ∉ S, q v x ∈ A v}
  · have hx' : x ∈ {x | ∀ v ∉ S ∪ T, q v x ∈ A v} := fun v hv =>
      hx v fun h => hv (Finset.mem_union_left _ h)
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Finset.prod_union hd, e3]
    have : ∏ v ∈ T, gv v (q v x) = 1 := Finset.prod_eq_one fun v hv => by
      rw [hgT v hv, Set.indicator_of_mem (hx v fun h => Finset.disjoint_left.mp hd h hv)]
      rfl
    rw [this, mul_one]
  · rw [Set.indicator_of_notMem hx]
    by_cases hx' : x ∈ {x | ∀ v ∉ S ∪ T, q v x ∈ A v}
    · rw [Set.indicator_of_mem hx', Finset.prod_union hd]
      simp only [Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hvS, hvA⟩ := hx
      have hvT : v ∈ T := by
        by_contra h
        exact hvA (hx' v (by simp [hvS, h]))
      have : ∏ v ∈ T, gv v (q v x) = 0 := Finset.prod_eq_zero hvT (by
        rw [hgT v hvT, Set.indicator_of_notMem hvA])
      rw [this, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem hx']

theorem product_formula_change_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → (∀ v, MeasurableSet (A v)) → (∀ v ∉ S', A v = latV b v) → (∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S', projV v (projFin X) ∈ latV b v}, fi (projInf X) * ∏ v ∈ S', fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S', ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S') → ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v}, fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * tailProd b mv S') := by
  intro F E _ _ _ _ _ d b n M ν mi mv S T S' A hS' hd hA hL H fi fv hfi hfv
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hc := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.2.2
  exact abstract_change ν mi mv projInf (fun v X => projV v (projFin X))
    (fun v => (hc v).measurable) S T S' A (fun v => latV b v) _ hS' hd hA hL H fi fv hfi hfv

end GlobalTheory.GaugeSetChange
end

section

noncomputable section

namespace GlobalTheory.GaugeEx.PairLat

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem ev_incl (e : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    inclR (Fv F v) e ∈ intV b v := by
  filter_upwards [IntBasis.ev_int_coord b e] with v hv
  exact IntBasis.tmul_mem b v (one_mem _) hv

theorem ev_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, A.map (inclR (Fv F v)) i j ∈ intV b v :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_incl b (A i j)

theorem mulVec_mem (v : HeightOneSpectrum (𝓞 F))
    (hm : ∀ y ∈ intV b v, ∀ z ∈ intV b v, y * z ∈ intV b v) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ intV b v)
    (w : Fin n → Fv F v ⊗[F] E) (hw : ∀ j, w j ∈ intV b v) (i : Fin m) :
    A.mulVec w i ∈ intV b v := by
  have h : A.mulVec w i = ∑ j, A i j * w j := rfl
  rw [h]
  exact IntBasis.sum_mem' b v Finset.univ (fun j => A i j * w j) fun j _ => hm _ (hA i j) _ (hw j)

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k : HA (Fv F v) σ J, (∀ i j, (HA.mat (Fv F v) σ J k).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J (k)⁻¹).val i j ∈ intV b v) → ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (y' : Fin 1 → Fin M → Fv F v ⊗[F] E), pairOf (Fv F v) σ J B y k y' ∈ latV b v ↔ y ∈ latV b v ∧ y' ∈ latV b v := by
  intro F E _ _ _ _ _ σ d b M J x a B J' hS
  obtain ⟨-, -, -, -, hJ', hH⟩ := hS
  have hdet : J'.det ≠ 0 := hH.2
  set C : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J) with hC
  have hCB : C * B = 1 := by
    rw [hC, Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  filter_upwards [(IntBasis.main F E σ d b).2.1, ev_map b B, ev_map b C] with v hv hB hCv k hk y y'
  have hm := hv.2.1
  simp only [mem_latV_iff, Fin.forall_fin_two, Fin.forall_fin_one]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := mulVec_mem b v hm _ hCv _ (mulVec_mem b v hm _ (fun i j => (hk i j).2) _ h)
    have h2 : (C.map (inclR (Fv F v))).mulVec (((HA.mat (Fv F v) σ J k)⁻¹).val.mulVec
        (pairOf (Fv F v) σ J B y k y' 1)) = y' 0 := by
      change (C.map (inclR (Fv F v))).mulVec (((HA.mat (Fv F v) σ J k)⁻¹).val.mulVec
        ((HA.mat (Fv F v) σ J k).val.mulVec ((B.map (inclR (Fv F v))).mulVec (y' 0)))) = y' 0
      rw [Matrix.mulVec_mulVec _ _ (HA.mat (Fv F v) σ J k).val, Units.inv_mul, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    intro i
    rw [← h2]
    exact h1 i
  · exact mulVec_mem b v hm _ (fun i j => (hk i j).1) _ (mulVec_mem b v hm _ hB _ h)

end GlobalTheory.GaugeEx.PairLat
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.TailSplit

theorem tprod_split {ι : Type} (a : ι → ℝ) (ha : Summable fun v => |a v - 1|) (S T S' : Finset ι)
    (h : ∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) (hd : Disjoint S T) :
    ∏' v : {v : ι // v ∉ S}, a v.1 = (∏ v ∈ T, a v) * ∏' v : {v : ι // v ∉ S'}, a v.1 := by
  classical
  have e1 : ∏' v : {v : ι // v ∉ S}, a v.1 = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : ∏' v : {v : ι // v ∉ S'}, a v.1 = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have m2 : Multipliable fun v => Set.mulIndicator {v | v ∉ S'} a v := by
    have : Summable fun v => ‖Set.mulIndicator {v | v ∉ S'} a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) ha
      by_cases hv : v ∈ S'
      · simp [Set.mulIndicator, hv]
      · simp [Set.mulIndicator, hv]
    simpa using multipliable_one_add_of_summable this
  have m1 : HasProd (fun v => Set.mulIndicator (T : Set ι) a v) (∏ v ∈ T, a v) := by
    have : HasProd (fun v => Set.mulIndicator (T : Set ι) a v)
        (∏ v ∈ T, Set.mulIndicator (T : Set ι) a v) :=
      hasProd_prod_of_ne_finset_one fun v hv => by simp [Set.mulIndicator, hv]
    rwa [Finset.prod_congr rfl (fun v hv => Set.mulIndicator_of_mem (by simpa using hv) a)] at this
  rw [e1, e2, ← (m1.mul m2.hasProd).tprod_eq]
  refine tprod_congr fun v => ?_
  by_cases hS : v ∈ S
  · have hT : v ∉ T := Finset.disjoint_left.1 hd hS
    simp [Set.mulIndicator, h, hS, hT]
  · by_cases hT : v ∈ T <;> simp [Set.mulIndicator, h, hS, hT]

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → tailProd b mv S = (∏ v ∈ T, mv v (latV b v)) * tailProd b mv S' := by
  intro F E _ _ _ _ _ d b n M mi mv S T S' hc h hd
  obtain ⟨-, hfin, hsum⟩ := hc
  have hne : ∀ v, mv v (latV b v) ≠ ∞ := by
    intro v
    have hk : IsCompact (intV b v) :=
      ((GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b).1 v).1
    have hk2 : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
      have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
          Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b v := by
        ext Y
        rw [mem_latV_iff]
        simp [Set.mem_pi]
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hk
    have := hfin v
    exact hk2.measure_lt_top.ne
  unfold tailProd
  rw [tprod_split (fun v => (mv v (latV b v)).toReal) hsum S T S' h hd,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
  congr 1
  exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hne v)

end GlobalTheory.GaugeEx.TailSplit
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.TwoStepIndep

theorem lintegral_pairOf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → IsInvTup R σ J' m' → ∀ (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g k : HA R σ J), g • ratTup (F := F) R x = k • ratTup (F := F) R x → ∀ f : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ y', f (pairOf R σ J B y g y') ∂m' = ∫⁻ y', f (pairOf R σ J B y k y') ∂m' := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ M J x a B J' m' hS hinv y g k hgk f hf
  obtain ⟨-, ⟨e, he, -⟩, -⟩ := GlobalTheory.FrameStep.frameStep F E σ hCM R M J x a B J' hS
  have hmem : k⁻¹ * g ∈ Hstab R σ J x := by
    have : (k⁻¹ * g) • ratTup (F := F) R x = ratTup (F := F) R x := by
      rw [mul_smul, hgk, inv_smul_smul]
    exact this
  have hrel : FrameRelR R σ J J' B (k⁻¹ * g) (e ⟨k⁻¹ * g, hmem⟩) := he ⟨k⁻¹ * g, hmem⟩
  set u := e ⟨k⁻¹ * g, hmem⟩ with hu
  have hkey : ∀ y', pairOf R σ J B y g y' = pairOf R σ J B y k (u • y') := by
    intro y'
    have hg : g = k * (k⁻¹ * g) := by group
    have h1 : ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
        ((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) *
        ((HA.mat R σ J (k⁻¹ * g) : GL (Fin (M + 1)) (R ⊗[F] E)) :
          Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := by
      conv_lhs => rw [hg]
      rfl
    have h2 : (u • y') 0 = ((HA.mat R σ J' u : GL (Fin M) (R ⊗[F] E)) :
        Matrix _ _ (R ⊗[F] E)).mulVec (y' 0) := rfl
    unfold FrameRelR at hrel
    unfold pairOf
    rw [h1, h2]
    simp only [Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc]
    exact congrArg (fun A : Matrix (Fin (M + 1)) (Fin M) (R ⊗[F] E) =>
      (![y 0, (((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * A).mulVec (y' 0)] :
          Fin 2 → Fin (M + 1) → R ⊗[F] E)) hrel
  have hc : Continuous fun y' => pairOf R σ J B y k y' := by
    refine continuous_pi ?_
    rw [Fin.forall_fin_two]
    refine ⟨continuous_const, ?_⟩
    have h0 : Continuous fun y' : Fin 1 → Fin M → R ⊗[F] E => y' 0 := continuous_apply 0
    show Continuous fun y' : Fin 1 → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J k : GL (Fin (M + 1)) (R ⊗[F] E)) :
        Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec ((B.map (inclR R)).mulVec (y' 0))
    exact continuous_const.matrix_mulVec (continuous_const.matrix_mulVec h0)
  have hm : Measurable fun X : Fin 1 → Fin M → R ⊗[F] E => u • X :=
    (continuous_const_smul u).measurable
  simp_rw [hkey]
  conv_rhs => rw [← hinv u]
  exact (lintegral_map (hf.comp hc.measurable) hm).symm

end GlobalTheory.TwoStepIndep
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → (consCol x B).det ≠ 0 ∧ (∃! e : Hstab R σ J x ≃* HA R σ J', ∀ g : Hstab R σ J x, FrameRelR R σ J J' B (g : HA R σ J) (e g)) ∧ ∀ e : Hstab R σ J x ≃* HA R σ J', (∀ g : Hstab R σ J x, FrameRelR R σ J J' B (g : HA R σ J) (e g)) → Continuous e ∧ Continuous e.symm := by
  first | exact @GlobalTheory.FrameStep.frameStep | exact GlobalTheory.FrameStep.frameStep | (intros; apply GlobalTheory.FrameStep.frameStep <;> assumption)
end

section

noncomputable section

open ValuativeRel
open scoped Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.LocLanglands

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord {x y : kˣ} : valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  rw [ord, ord, neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp)]
  exact (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k)).symm

theorem valuation_eq_iff_ord {x y : kˣ} : valuation k (x : k) = valuation k (y : k) ↔ ord k x = ord k y := by
  rw [le_antisymm_iff, valuation_le_iff_ord, valuation_le_iff_ord]; omega

variable (k) in
theorem exists_unit_pow (a : ℕ) : ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧ ord k p = a := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (R := k) (by simpa using hy.symm)
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
  refine ⟨Units.mk0 y hy0 ^ a, by simp [hy], ?_⟩
  induction a with
  | zero => simpa using ord_eq_zero (k := k) (x := 1) (by simp)
  | succ n ih => rw [pow_succ, ord_mul, ih, h1]; simp

theorem valuation_of_shell {c r : kˣ} {a : ℕ} (hr : ord k r = ord k c - a) :
    valuation k (c : k) = uniformizer k ^ a * valuation k (r : k) := by
  obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
  rw [← hp, ← map_mul, ← Units.val_mul, valuation_eq_iff_ord, ord_mul]; omega

theorem IsShellReps.sum_eq {c : kˣ} {a : ℕ} {R R' : Finset kˣ} (h : IsShellReps c a R) (h' : IsShellReps c a R')
    {g : kˣ → ℂ} (hg : ∀ y r : kˣ, ord k y = ord k c - a → ord k r = ord k c - a →
      valuation k ((y : k) - r) ≤ valuation k (c : k) → g y = g r) :
    ∑ r ∈ R, g r = ∑ r ∈ R', g r := by
  choose i hi hi' using fun r hr => h'.2 r (h.1 r hr)
  refine Finset.sum_bij i (fun r hr => (hi r hr).1) (fun r₁ h₁ r₂ h₂ e => ?_) (fun r' hr' => ?_)
    (fun r hr => hg _ _ (h.1 r hr) (h'.1 _ (hi r hr).1) (hi r hr).2)
  · refine (h.2 _ (h'.1 _ (hi r₁ h₁).1)).unique ⟨h₁, ?_⟩ ⟨h₂, ?_⟩
    · rw [Valuation.map_sub_swap]; exact (hi r₁ h₁).2
    · rw [Valuation.map_sub_swap, e]; exact (hi r₂ h₂).2
  · obtain ⟨r, hr, -⟩ := h.2 r' (h'.1 r' hr')
    exact ⟨r, hr.1, (hi' r hr.1 r' ⟨hr', by rw [Valuation.map_sub_swap]; exact hr.2⟩).symm⟩


variable {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {c : kˣ} {a : ℕ} {R R' : Finset kˣ}

theorem addChar_eq_of_sub (hψ : HasConductor ψ c) {y z : k} (h : valuation k (y - z) ≤ valuation k (c : k)) :
    ψ y = ψ z := by
  have : y = z + (y - z) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.eq_one h, mul_one]

theorem gaussTerm_eq (hψ : HasConductor ψ c) (hχ : HasExponent χ a) {x : k} (hx : valuation k x ≤ 1) (y r : kˣ)
    (hy : ord k y = ord k c - a) (hr : ord k r = ord k c - a)
    (h : valuation k ((y : k) - r) ≤ valuation k (c : k)) :
    (((χ y)⁻¹ : ℂˣ) : ℂ) * (ψ (x * y) : ℂ) = (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
  have h1 : ψ (x * y) = ψ (x * r) := addChar_eq_of_sub hψ (by
    rw [← mul_sub, map_mul]
    exact (mul_le_mul' hx h).trans_eq (one_mul _))
  have hr0 : 0 < valuation k (r : k) := by simp [zero_lt_iff]
  have h2 : χ (y * r⁻¹) = 1 := hχ.1 _ ⟨by
    rw [Units.val_mul, map_mul, valuation_eq_iff_ord.2 (hy.trans hr.symm), ← map_mul]; simp, by
    have : ((y * r⁻¹ : kˣ) : k) - 1 = ((y : k) - r) * (r : k)⁻¹ := by simp [sub_mul]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ hr0, ← valuation_of_shell hr]
    exact h⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h1, h2]

theorem IsTateEps.unique {e e' : ℂ} (h : IsTateEps ψ χ e) (h' : IsTateEps ψ χ e') : e = e' := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  obtain ⟨c', a', R', hc', ha', hR', rfl⟩ := h'
  obtain rfl := ha.unique ha'
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  rw [IsShellReps, valuation_eq_iff_ord.1 h1, h1] at hR'
  have := hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))
  simp only [one_mul] at this
  rw [this]

end GlobalTheory.LocLanglands
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisMap

variable (l : ℕ) [Fact l.Prime]

theorem unit_l (n : ℕ) : IsUnit ((l : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) := by
  have h : IsUnit (algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h2 := h.map (Ideal.Quotient.mk (Per.kerP l ^ n))
  rwa [map_natCast, map_natCast] at h2

end GlobalTheory.MemLoc.CrisMap
end

section

open Formalism.L2.DIV

namespace GlobalTheory.ColumnOrth

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

theorem leftRegular_character (g : G) :
    (Representation.leftRegular ℂ G).character g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  unfold Representation.character
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  by_cases h : g = 1
  · subst h
    simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hx : g * x ≠ x := by simpa using h
    simp [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis, hx]

theorem sum_char_one_mul_char (A : Finset (G → ℂ))
    (hA : ∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) (g : G) :
    ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  obtain ⟨r, d, τ, hirr, hch⟩ :=
    CycSplitWork.char_eq_sum_irreducible (G := G) (L := ℂ) (Representation.leftRegular ℂ G)
  set χ : Fin r → (G → ℂ) := fun i => (τ i).character with hχ
  have hmem : ∀ i, χ i ∈ A := fun i => (hA _).2 ⟨d i, τ i, hirr i, rfl⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmult : ∀ ψ ∈ A, (({i | χ i = ψ} : Finset (Fin r)).card : ℂ) = ψ 1 := by
    intro ψ hψ
    have hψ' := (hA ψ).1 hψ
    have h1 : (Nat.card G : ℂ)⁻¹ * ∑ x : G, (Representation.leftRegular ℂ G).character x * ψ x⁻¹ = ψ 1 := by
      simp_rw [leftRegular_character, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (1 : G)]
      simp [Nat.card_eq_fintype_card, hcard]
    have h2 : (Nat.card G : ℂ)⁻¹ * ∑ x : G, (Representation.leftRegular ℂ G).character x * ψ x⁻¹ =
        ∑ i, if χ i = ψ then (1 : ℂ) else 0 := by
      simp_rw [hch, Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      convert Formalism.L2.Col.gx_orth ⟨d i, τ i, hirr i, rfl⟩ hψ'
    rw [← h1, h2, Finset.sum_boole]
  have hr := leftRegular_character (G := G) g
  rw [hch g] at hr
  rw [← hr, ← Finset.sum_fiberwise_of_maps_to (g := χ) (t := A) (fun i _ => hmem i)]
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => ψ g) fun i hi => congrFun (Finset.mem_filter.1 hi).2 g, Finset.sum_const, nsmul_eq_mul,
    hmult ψ hψ]

end GlobalTheory.ColumnOrth
end
