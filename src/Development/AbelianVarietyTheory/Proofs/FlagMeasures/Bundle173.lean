module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.Bundle024
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle151
public import Formalism.HermitianLattices.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle099
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle153
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle150
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle154
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.Places

noncomputable def placeEquiv (I : AutInst) : InfinitePlace I.F ≃ InfinitePlace I.E :=
  (Equiv.ofBijective _ (GlobalTheory.Count.FrameMajorant.comap_bijective I)).symm

theorem placeEquiv_apply (I : AutInst) (v : InfinitePlace I.F) :
    placeEquiv I v = InfinitePlace.mk (I.φ v) := by
  have h : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [placeEquiv, Equiv.symm_apply_eq]
  show v = (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E)
  rw [InfinitePlace.comap_mk, h, InfinitePlace.mk_embedding]

noncomputable def comapEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    InfinitePlace L ≃ InfinitePlace K where
  toFun w := w.comap (e : K →+* L)
  invFun w := w.comap (e.symm : L →+* K)
  left_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]
  right_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]

theorem exists_twist {K : Type} [Field K] (φ ψ : K →+* ℂ)
    (h : InfinitePlace.mk φ = InfinitePlace.mk ψ) :
    ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧ ∀ y, φ y = τ (ψ y) := by
  rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
  · exact ⟨RingHom.id ℂ, Or.inl rfl, fun y => by rw [h', RingHom.id_apply]⟩
  · refine ⟨starRingEnd ℂ, Or.inr rfl, fun y => ?_⟩
    rw [← h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem places_match : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  intro I I₀ e _

  let σ : InfinitePlace I.F ≃ InfinitePlace I₀.F :=
    (placeEquiv I).trans ((comapEquiv e).trans (placeEquiv I₀).symm)
  have h1 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v y = τ ((placeEquiv I v).embedding y) := fun v =>
    exists_twist _ _ (by rw [InfinitePlace.mk_embedding, placeEquiv_apply])
  have h2 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v (e y) = τ (I₀.φ (σ v) y) := by
    intro v
    refine exists_twist ((I.φ v).comp (e : I₀.E →+* I.E)) (I₀.φ (σ v)) ?_
    rw [← placeEquiv_apply]
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [placeEquiv_apply]
    show _ = (InfinitePlace.mk (I.φ v)).comap (e : I₀.E →+* I.E)
    rw [InfinitePlace.comap_mk]
  choose τ hτ using h1
  choose τ₀ hτ₀ using h2
  exact ⟨placeEquiv I, σ, τ, τ₀, fun v => (hτ v).1, fun v => (hτ₀ v).1, fun v => (hτ v).2,
    fun v => (hτ₀ v).2⟩

end GlobalTheory.LeviIso.Places
end

section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem uh_mul {N : ℕ} {H A B : Matrix (Fin N) (Fin N) ℂ} (hA : Aᴴ * H * A = H) (hB : Bᴴ * H * B = H) :
    (A * B)ᴴ * H * (A * B) = H := by
  rw [Matrix.conjTranspose_mul]
  calc Bᴴ * Aᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hA, hB]

theorem uh_star {N : ℕ} {H A : Matrix (Fin N) (Fin N) ℂ} (hA : Aᴴ * H * A = H) (hu : A * Aᴴ = 1) :
    (Aᴴ)ᴴ * H * Aᴴ = H := by
  rw [Matrix.conjTranspose_conjTranspose]
  calc A * H * Aᴴ = A * (Aᴴ * H * A) * Aᴴ := by rw [hA]
    _ = (A * Aᴴ) * H * (A * Aᴴ) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hu, Matrix.one_mul, Matrix.mul_one]

def subKH (k r : ℕ) : Subgroup (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) where
  carrier := {u | (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ GlobalTheory.ThA.KH k r}
  mul_mem' := by
    intro a b ha hb
    exact ⟨uh_mul ha.1 hb.1, (a * b).2⟩
  one_mem' := by
    refine ⟨?_, (1 : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ).2⟩
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, a⁻¹.2⟩
    have hu : (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) *
        (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ = 1 := by
      have := Matrix.mem_unitaryGroup_iff.mp a.2
      rwa [Matrix.star_eq_conjTranspose] at this
    exact uh_star ha.1 hu

instance (k r : ℕ) : MeasurableSpace (subKH k r) := borel _
instance (k r : ℕ) : BorelSpace (subKH k r) := ⟨rfl⟩

instance (k r : ℕ) : CompactSpace (subKH k r) := by
  have hc : IsClosed ((subKH k r : Set (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ))) := by
    have : ((subKH k r : Set (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ))) =
        (Subtype.val : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ → _) ⁻¹' GlobalTheory.ThA.KH k r := rfl
    rw [this]
    exact (isCompact_KH k r).isClosed.preimage continuous_subtype_val
  exact isCompact_iff_compactSpace.mp hc.isCompact

def incKH (k r : ℕ) (u : subKH k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  ((u : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) : Matrix _ _ ℂ)

theorem continuous_incKH (k r : ℕ) : Continuous (incKH k r) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem incKH_mem (k r : ℕ) (u : subKH k r) : incKH k r u ∈ GlobalTheory.ThA.KH k r := u.2

theorem exists_isHaarKH : ∀ k r : ℕ, ∃ μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    GlobalTheory.KFinAvg.IsHaarKH k r μ := by
  intro k r
  let ν : Measure (subKH k r) := Measure.haarMeasure ⊤
  have hmeas : Measurable (incKH k r) := (continuous_incKH k r).measurable
  have hν : IsProbabilityMeasure ν := ⟨by
    have := Measure.haarMeasure_self (G := subKH k r) (K₀ := ⊤)
    simpa using this⟩
  have hKm : MeasurableSet (GlobalTheory.ThA.KH k r) := (isCompact_KH k r).isClosed.measurableSet
  refine ⟨ν.map (incKH k r), ?_, ?_, ?_, ?_⟩
  · infer_instance
  · rw [Measure.map_apply hmeas hKm.compl]
    have : incKH k r ⁻¹' (GlobalTheory.ThA.KH k r)ᶜ = ∅ := by
      ext u
      simp [incKH_mem k r u]
    rw [this, measure_empty]
  · intro a ha
    let au : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := ⟨a, ha.2⟩
    let a' : subKH k r := ⟨au, ha⟩
    have h := map_mul_left_eq_self ν a'
    rw [Measure.map_map (measurable_const_mul a) hmeas]
    conv_rhs => rw [← h]
    rw [Measure.map_map hmeas (measurable_const_mul _)]
    rfl
  · intro U hU h1
    rw [Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage (continuous_incKH k r)).measure_pos ν ⟨1, h1⟩

end GlobalTheory.KFinAvg
end
end

section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg.PeakPoly

def coord (n : ℕ) : Option ((Fin n × Fin n) × Bool) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | none, _ => 1
  | some ((i, j), false), g => g i j
  | some ((i, j), true), g => star (g i j)

theorem continuous_coord (n : ℕ) (d : Option ((Fin n × Fin n) × Bool)) : Continuous (coord n d) := by
  rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
  · exact continuous_const
  · exact continuous_id.matrix_elem i j
  · exact (continuous_id.matrix_elem i j).star

theorem prod_expand {ι D X : Type*} [Fintype ι] [DecidableEq ι] [Fintype D]
    (x : D → X → ℂ) (c : ι → D → ℂ) (g : X) :
    ∏ j, ∑ e, c j e * x e g = ∑ t : ι → D, (∏ j, c j (t j)) * ∏ j, x (t j) g := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib]

theorem coord_translate (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (d : Option ((Fin n × Fin n) × Bool)) :
    ∃ T : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, coord n d (a * g) = ∑ e, T e * coord n e g := by
  have hmem : (fun g => coord n d (a * g)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n none (a * g)) = coord n none := by
        funext g; rfl
      rw [this]; exact Submodule.subset_span ⟨none, rfl⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), false)) (a * g)) =
          ∑ l, a i l • coord n (some ((l, j), false)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), true)) (a * g)) =
          ∑ l, star (a i l) • coord n (some ((l, j), true)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply, star_sum]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  obtain ⟨T, hT⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨T, fun g => ?_⟩
  have := congrFun hT g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem peak_expand (n : ℕ) :
    ∃ c : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, ((peak n g : ℝ) : ℂ) = ∑ e, c e * coord n e g := by
  have hmem : (fun g => ((peak n g : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    have : (fun g => ((peak n g : ℝ) : ℂ)) = (1 / 2 : ℂ) • coord n none +
        ∑ i, (1 / (4 * (n : ℂ))) • (coord n (some ((i, i), false)) + coord n (some ((i, i), true))) := by
      funext g
      simp only [peak, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, coord]
      push_cast

      rw [Complex.re_eq_add_conj, ← Finset.mul_sum, Finset.sum_add_distrib, Matrix.trace,
      map_sum]
      simp only [Matrix.diag, Complex.star_def]
      ring
    rw [this]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) ?_
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨c, fun g => ?_⟩
  have := congrFun hc g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

end GlobalTheory.KFinAvg.PeakPoly

namespace GlobalTheory.KFinAvg
open PeakPoly

theorem peak_pow_polynomial : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ),
    (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧
    ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  intro n m
  classical
  let e := Fintype.equivFin (Fin m → Option ((Fin n × Fin n) × Bool))
  let bS : (Fin m → Option ((Fin n × Fin n) × Bool)) → Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun s g => ∏ j, coord n (s j) g
  obtain ⟨c0, hc0⟩ := peak_expand n
  refine ⟨Fintype.card (Fin m → Option ((Fin n × Fin n) × Bool)), fun i => bS (e.symm i),
    fun i => ∏ j, c0 (e.symm i j), ?_, ?_, ?_⟩
  · intro i
    exact continuous_finsetProd _ fun j _ => continuous_coord n _
  · intro g
    have h1 : ((peak n g ^ m : ℝ) : ℂ) = ∏ _j : Fin m, ∑ d, c0 d * coord n d g := by
      rw [Complex.ofReal_pow, hc0 g, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1, prod_expand (fun d g => coord n d g) (fun _ => c0) g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, c0 (t j)) * ∏ j, coord n (t j) g)).symm
  · intro a i
    choose T hT using fun j => coord_translate n a (e.symm i j)
    refine ⟨fun k => ∏ j, T j (e.symm k j), fun g => ?_⟩
    show ∏ j, coord n (e.symm i j) (a * g) = _
    simp_rw [hT]
    rw [prod_expand (fun d g => coord n d g) T g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, T j (t j)) * ∏ j, coord n (t j) g)).symm

end GlobalTheory.KFinAvg
end
end

section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem integrable_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hf : Continuous f) (v : H) :
    Integrable (fun g => f g • σ g v) μ := by
  haveI := hμ.1
  have hK := isCompact_KH k r
  have hsub : GlobalTheory.ThA.KH k r ⊆ Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r) := fun g hg => hg.1
  have hc : ContinuousOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) :=
    hf.continuousOn.smul ((hσ.2.2 v).mono hsub)
  have hI : IntegrableOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) μ := hc.integrableOn_compact hK
  have hr : μ.restrict (GlobalTheory.ThA.KH k r) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ.2.1)
  rw [IntegrableOn, hr] at hI
  exact hI

theorem integral_sum_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {N : ℕ} {b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hb : ∀ j, Continuous (b j))
    (c : Fin N → ℂ) (v : H) :
    ∫ g, (∑ j, c j * b j g) • σ g v ∂μ = ∑ j, c j • ∫ g, b j g • σ g v ∂μ := by
  simp_rw [Finset.sum_smul, mul_smul]
  rw [integral_finsetSum Finset.univ (f := fun j g => c j • (b j g • σ g v)) (fun j _ => (Integrable.smul (c j) (integrable_smul_orbit hσ hμ (hb j) v) :
      Integrable (fun g => c j • (b j g • σ g v)) μ))]
  simp_rw [integral_smul]

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg

theorem isKFinHpk_integral_translates : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  intro k r H _ _ _ σ μ hσ hμ N b hb hinv c v
  obtain ⟨w, hw⟩ : ∃ w : Fin N → H, ∀ j, w j = ∫ g, b j g • σ g v ∂μ := ⟨_, fun _ => rfl⟩
  have key : ∀ c' : Fin N → ℂ, ∫ g, (∑ j, c' j * b j g) • σ g v ∂μ = ∑ j, c' j • w j := by
    intro c'
    rw [integral_sum_smul_orbit hσ hμ hb c' v]
    simp_rw [hw]
  have hmem : ∀ c' : Fin N → ℂ, ∑ j, c' j • w j ∈ Submodule.span ℂ (Set.range w) := fun c' =>
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Submodule.span ℂ (Set.range w), FiniteDimensional.span_of_finite ℂ (Set.finite_range w), ?_, ?_⟩
  · rw [key]; exact hmem c
  · intro a ha x hx
    have hu : star a * a = 1 := ha.2.1
    have haa : a⁻¹ * a = 1 := by rw [Matrix.inv_eq_left_inv hu]; exact hu
    have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := by rw [ae_iff]; exact hμ.2.1
    have hgen : ∀ j, σ a (w j) ∈ Submodule.span ℂ (Set.range w) := by
      intro j
      obtain ⟨d, hd⟩ := hinv a⁻¹ j
      have h1 : σ a (w j) = ∫ g, b j g • σ (a * g) v ∂μ := by
        rw [hw, ← (σ a).integral_comp_comm (integrable_smul_orbit hσ hμ (hb j) v)]
        refine integral_congr_ae ?_
        filter_upwards [hae] with g hg
        rw [map_smul, hσ.1.2 a ha.1 g hg.1]
        rfl
      have hcm : Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => a * g) :=
        continuous_const.matrix_mul continuous_id
      have h2 : ∫ g, b j g • σ (a * g) v ∂μ = ∫ g, b j (a⁻¹ * g) • σ g v ∂μ := by
        conv_rhs => rw [← hμ.2.2.1 a ha]
        rw [integral_map hcm.aemeasurable]
        · simp only [← Matrix.mul_assoc, haa, Matrix.one_mul]
        · rw [hμ.2.2.1 a ha]
          exact (integrable_smul_orbit hσ hμ ((hb j).comp (continuous_const.matrix_mul continuous_id)) v).aestronglyMeasurable
      rw [h1, h2]
      simp_rw [hd]
      rw [key]
      exact hmem d
    have hle : Submodule.span ℂ (Set.range w) ≤ (Submodule.span ℂ (Set.range w)).comap (σ a).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgen j
    exact hle hx

end GlobalTheory.KFinAvg
end
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.centredCapelliOperator_forms_agree : ∀ (k r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ) (F : B.Mat k r → V), Q.CV k r Y F = PI.CapelliEig.capC (k := k) (r := r) Y F ∧ Q.CV k r Y F = Formalism.MainNotions.S.capC (k := k) (r := r) Y F := by
  first | exact @GlobalTheory.ThA.centredCapelli_forms_agree | exact GlobalTheory.ThA.centredCapelli_forms_agree | (intros; apply GlobalTheory.ThA.centredCapelli_forms_agree <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.tendsto_ball_mean_bigCellWeight : ∀ (k r : ℕ), Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) / volume (Metric.ball (0 : Fin r → ℂ) ρ)) (𝓝[>] 0) (𝓝 1) := by
  first | exact @GlobalTheory.CellDens.tendsto_mean_cWeight | exact GlobalTheory.CellDens.tendsto_mean_cWeight | (intros; apply GlobalTheory.CellDens.tendsto_mean_cWeight <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.unimodularHermitianMass_mul_le_mass : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (k s : ℕ) (Mb : ℝ) (ms : ℕ → ℝ), 3 ≤ k → 1 ≤ s → s < k → (∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n) → ms 1 ≤ Mb → ms 2 ≤ Mb → 1 ≤ Mb → ms s * ms (k - s) ≤ ms k * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * k * (Formalism.HermitianLatticesTheory.fDeg K))) := by
  first | exact @GlobalTheory.MassRatioBound.mass_mul_mass_le | exact GlobalTheory.MassRatioBound.mass_mul_mass_le | (intros; apply GlobalTheory.MassRatioBound.mass_mul_mass_le <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.ProdFactor

theorem integrable_phLoc_of_integrable_ph : ∀ (D : D7) (X : HidaSetting D), Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hX v
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hd : ∀ v, X.dv v ≠ 0 := fun v =>
    (fdegOf_pos (hU v) (X.ds v).2.2.2.2.1 (hw v)).ne'

  exact integrable_factor' X.B.I.ε X.B.σ X.B.w X.dv hU hw hd hX v

end GlobalTheory.ProdFactor
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.signedBlockAntidiag_with_leadingMinors_encard_le : ∀ (K : Type) [Field K] (j : ℕ) (δ : ℕ → K), (({P : Matrix (Fin j) (Fin j) K | (∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, P a b = w.mat a b * ((sgn b : ℤ) : K)) ∧ ∀ (l : ℕ) (hl : l ≤ j), (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = δ l}).encard : ℕ∞) ≤ 8 ^ j := by
  first | exact @GlobalTheory.signed_block_count | exact GlobalTheory.signed_block_count | (intros; apply GlobalTheory.signed_block_count <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unitarySubgroupChart_almost_isometric_near_one : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ g h : Formalism.REAL.UJ ε, uMat g - 1 ∈ A → uMat h - 1 ∈ A → Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ → Real.sqrt (Formalism.REAL.hs (uMat h - 1)) < δ → ‖(WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d))‖ ≤ Real.sqrt (Formalism.REAL.hs (uMat g - uMat h)) ∧ Real.sqrt (Formalism.REAL.hs (uMat g - uMat h)) ≤ κ * ‖(WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d))‖ := by
  first | exact @GlobalTheory.GaugeSubLip.chart_almost_isometric | exact GlobalTheory.GaugeSubLip.chart_almost_isometric | (intros; apply GlobalTheory.GaugeSubLip.chart_almost_isometric <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_orthonormal_lie_coordinates : ∀ (n d m : ℕ) (ε : Fin n → Bool) (A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), A m = ⊥ → (∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1)) → (∀ c, A (c + 1) ≤ A c) → (∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, E i ∈ A 0 ∧ Formalism.REAL.inG ε (E i)) → ∃ σ : (Fin d → ℝ) → Formalism.REAL.UJ ε, Continuous σ ∧ ∀ x, uMat (σ x) - 1 ∈ A 0 ∧ ∀ i, (((uMat (σ x) - 1) * (E i)ᴴ).trace).re = x i := by
  first | exact @GlobalTheory.NilCovSec.exists_continuous_section | exact GlobalTheory.NilCovSec.exists_continuous_section | (intros; apply GlobalTheory.NilCovSec.exists_continuous_section <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup : ∀ (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (E i)) → ∀ g : Formalism.REAL.UJ ε, (uMat g - 1) - Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε ∈ Submodule.span ℝ (Set.range E) → ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ Formalism.REAL.hs (uMat g - 1) ∧ Formalism.REAL.hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + Formalism.REAL.hs (uMat g - 1) ^ 2 / 4 := by
  first | exact @GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | exact GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | (intros; apply GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le <;> assumption)
end
