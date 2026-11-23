module

import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle001
public import Mathlib.LinearAlgebra.DFinsupp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

section

noncomputable section

namespace PI.AprimeInfG

open MeasureTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  apply Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_fin_prod <;> assumption

theorem lintegral_fintype_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  have h1 : ∀ y : (i' : Fin (Fintype.card ι)) → E (e i'),
      ∏ i, f i ((MeasurableEquiv.piCongrLeft E e) y i) = ∏ i', f (e i') (y i') := by
    intro y
    exact (Fintype.prod_equiv e (fun i' => f (e i') (y i')) _
      (fun i' => by simp [MeasurableEquiv.piCongrLeft_apply_apply])).symm
  simp_rw [h1]
  rw [lintegral_fin_prod (fun i' => f (e i')) (fun i' => hf (e i'))]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem withDensity_pi {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, MeasurableSpace (E i)]
    (lam : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (lam i)] (D : (i : ι) → E i → ℝ)
    (hD : ∀ i, Measurable (D i)) :
    (Measure.pi lam).withDensity (fun z => ∏ i, ENNReal.ofReal (D i (z i))) =
      Measure.pi (fun i => (lam i).withDensity (fun x => ENNReal.ofReal (D i x))) := by
  classical
  haveI : ∀ i, SigmaFinite ((lam i).withDensity fun x => ENNReal.ofReal (D i x)) :=
    fun i => SigmaFinite.withDensity_ofReal (D i)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h1 : (univ.pi s).indicator (fun z : (i : ι) → E i => ∏ i, ENNReal.ofReal (D i (z i))) =
      fun z => ∏ i, (s i).indicator (fun x => ENNReal.ofReal (D i x)) (z i) := by
    funext z
    by_cases hz : z ∈ univ.pi s
    · rw [indicator_of_mem hz]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hz i (mem_univ i)) (fun x => ENNReal.ofReal (D i x))).symm
    · simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      have hz' : z ∉ univ.pi s := fun h => hi (h i (mem_univ i))
      rw [indicator_apply, if_neg hz']
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [indicator_apply, if_neg hi])).symm
  rw [h1, lintegral_fintype_prod (fun i => (s i).indicator (fun x => ENNReal.ofReal (D i x))) (fun i => (ENNReal.measurable_ofReal.comp (hD i)).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

theorem pi_chart_dens {V : Type} [Fintype V] {X E : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (E v)] (μ : ∀ v, Measure (X v)) [∀ v, SigmaFinite (μ v)]
    (lam : ∀ v, Measure (E v)) [∀ v, SigmaFinite (lam v)]
    (Φ : ∀ v, E v → X v) (hΦm : ∀ v, Measurable (Φ v)) (U : ∀ v, Set (E v)) (hU : ∀ v, MeasurableSet (U v))
    (hinj : ∀ v, InjOn (Φ v) (U v))
    (D : ∀ v, E v → ℝ) (hD : ∀ v, Measurable (D v))
    (h : ∀ v, ∀ A ⊆ U v, MeasurableSet A → μ v (Φ v '' A) = ∫⁻ z in A, ENNReal.ofReal (D v z) ∂lam v)
    (A : Set (∀ v, E v)) (hAU : A ⊆ univ.pi U) (hA : MeasurableSet A)
    (hAi : MeasurableSet ((fun z v => Φ v (z v)) '' A)) :
    Measure.pi μ ((fun z v => Φ v (z v)) '' A) =
      ∫⁻ z in A, ∏ v, ENNReal.ofReal (D v (z v)) ∂Measure.pi lam := by
  classical
  set Ψ : (∀ v, E v) → (∀ v, X v) := fun z v => Φ v (z v) with hΨ
  have hΨm : Measurable Ψ := Measurable.of_eval fun v => (hΦm v).comp (measurable_pi_apply v)
  let S : ∀ v, Set (X v) := fun v => Φ v '' U v
  let ν : ∀ v, Measure (E v) := fun v => (lam v).withDensity fun x => ENNReal.ofReal (D v x)
  haveI : ∀ v, SigmaFinite (ν v) := fun v => SigmaFinite.withDensity_ofReal (D v)
  have hκ : ∀ v, ((ν v).restrict (U v)).map (Φ v) = (μ v).restrict (S v) := by
    intro v
    ext C hC
    rw [Measure.map_apply (hΦm v) hC, Measure.restrict_apply (hΦm v hC), Measure.restrict_apply hC]
    have hsub : Φ v ⁻¹' C ∩ U v ⊆ U v := Set.inter_subset_right
    have hme : MeasurableSet (Φ v ⁻¹' C ∩ U v) := (hΦm v hC).inter (hU v)
    rw [show ν v (Φ v ⁻¹' C ∩ U v) = ∫⁻ z in Φ v ⁻¹' C ∩ U v, ENNReal.ofReal (D v z) ∂lam v from
      withDensity_apply _ hme, ← h v _ hsub hme]
    congr 1
    ext x
    constructor
    · rintro ⟨z, ⟨hzC, hzU⟩, rfl⟩
      exact ⟨hzC, z, hzU, rfl⟩
    · rintro ⟨hxC, z, hzU, rfl⟩
      exact ⟨z, ⟨hxC, hzU⟩, rfl⟩
  have hrestr : (Measure.pi μ).restrict (univ.pi S) = Measure.pi fun v => (μ v).restrict (S v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hB), ← Set.pi_inter_distrib, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Measure.restrict_apply (hB v)]
  have hrestr2 : (Measure.pi ν).restrict (univ.pi U) = Measure.pi fun v => (ν v).restrict (U v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hB), ← Set.pi_inter_distrib, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Measure.restrict_apply (hB v)]
  have hmap : (Measure.pi fun v => (ν v).restrict (U v)).map Ψ =
      Measure.pi fun v => (μ v).restrict (S v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.map_apply hΨm (MeasurableSet.univ_pi hB)]
    have hpre : Ψ ⁻¹' univ.pi B = univ.pi fun v => Φ v ⁻¹' B v := by
      ext z
      simp [hΨ]
    rw [hpre, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← hκ v, Measure.map_apply (hΦm v) (hB v)]
  have hΦA : Ψ '' A ⊆ univ.pi S := by
    rintro _ ⟨z, hz, rfl⟩ v -
    exact ⟨z v, hAU hz v (mem_univ v), rfl⟩
  calc Measure.pi μ (Ψ '' A) = (Measure.pi μ).restrict (univ.pi S) (Ψ '' A) := by
        rw [Measure.restrict_apply hAi, Set.inter_eq_left.2 hΦA]
    _ = (Measure.pi fun v => (ν v).restrict (U v)).map Ψ (Ψ '' A) := by rw [hrestr, hmap]
    _ = (Measure.pi fun v => (ν v).restrict (U v)) (Ψ ⁻¹' (Ψ '' A)) := Measure.map_apply hΨm hAi
    _ = (Measure.pi ν).restrict (univ.pi U) (Ψ ⁻¹' (Ψ '' A)) := by rw [hrestr2]
    _ = Measure.pi ν A := by
        rw [Measure.restrict_apply (hΨm hAi)]
        congr 1
        ext z
        constructor
        · rintro ⟨⟨z', hz', hzz⟩, hzU⟩
          have hzz' : z' = z := by
            funext v
            exact hinj v (hAU hz' v (mem_univ v)) (hzU v (mem_univ v)) (congrFun hzz v)
          rw [← hzz']
          exact hz'
        · intro hz
          exact ⟨⟨z, hz, rfl⟩, hAU hz⟩
    _ = ∫⁻ z in A, ∏ v, ENNReal.ofReal (D v (z v)) ∂Measure.pi lam := by
        rw [← withDensity_apply _ hA, withDensity_pi lam D hD]

end PI.AprimeInfG
end
end

section

open Module

noncomputable section

namespace HcS.HermitianLatticesTheory

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def isom (h : V →ₗ⋆[K] V →ₗ[K] K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    change h (a (b x)) (a (b y)) = h x y
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have := ha (a.symm x) (a.symm y)
    change h (a.symm x) (a.symm y) = h x y
    simpa using this.symm

def dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  HcS.E.hdual h L

def IsUnimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Prop :=
  dual h L = L

end Defs

end HcS.HermitianLatticesTheory
end
end

section

noncomputable section

namespace HcS.BasicNotions

open MeasureTheory Filter Topology Matrix

def UpqT (P Q : ℕ) : Type := HcS.UG.Upq P Q

instance (P Q : ℕ) : Group (UpqT P Q) := inferInstanceAs (Group (HcS.UG.Upq P Q))
instance (P Q : ℕ) : TopologicalSpace (UpqT P Q) :=
  inferInstanceAs (TopologicalSpace (HcS.UG.Upq P Q))
instance (P Q : ℕ) : MeasurableSpace (UpqT P Q) := borel (UpqT P Q)

def UpqT.mat {P Q : ℕ} (g : UpqT P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  let g' : HcS.UG.Upq P Q := g; ((g'.1 : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)

def lieU (P Q : ℕ) : Submodule ℝ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) where
  carrier := {X | Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * HcS.UG.Jpq P Q + Yᴴ * HcS.UG.Jpq P Q + (HcS.UG.Jpq P Q * X + HcS.UG.Jpq P Q * Y)
        = (Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X) + (Yᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * Y) := by
          abel
      _ = 0 := by rw [hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, hX,
      smul_zero]

instance (P Q : ℕ) : MeasurableSpace (lieU P Q) := borel (lieU P Q)

def entries {P Q : ℕ} (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ := fun ij => Z ij.1 ij.2

def IsOmegaLeb {P Q : ℕ} (lam : Measure (lieU P Q)) : Prop :=
  lam.IsAddHaarMeasure ∧
    ((lam.prod lam).map (fun ab : lieU P Q × lieU P Q =>
      entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))) = volume

def ballU (P Q : ℕ) (r : ℝ) : Set (lieU P Q) :=
  {X | ∑ i, ∑ j, ‖(X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r}

def OmegaDensity {P Q : ℕ} (μ : Measure (UpqT P Q)) (c : ENNReal) : Prop :=
  ∃ lam : Measure (lieU P Q), IsOmegaLeb lam ∧
    Tendsto (fun r : ℝ => μ {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c)

structure CDHaar where
  cd : ∀ P Q : ℕ, Measure (UpqT P Q)
  haar : ∀ P Q, (cd P Q).IsHaarMeasure
  prob : ∀ N, IsProbabilityMeasure (cd N 0)
  trick : ∀ P Q, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity (cd P Q) c ∧ OmegaDensity (cd (P + Q) 0) c

end HcS.BasicNotions
end
end

section

noncomputable section

namespace PI.AprimeInfW

theorem jm_true (k : ℕ) : Formalism.REAL.Jm (fun _ : Fin k => true) = 1 := by
  simp [Formalism.REAL.Jm]

end PI.AprimeInfW
end
end

section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def reim {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) : EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
  (WithLp.equiv 2 (Fin n × Fin m × Bool → ℝ)).symm fun p => if p.2.2 then (Y p.1 p.2.1).re else (Y p.1 p.2.1).im

def PlaceJac : Prop := ∀ (n m : ℕ) (ε : Fin n → Bool) (S : Finset (Fin n)) (w : Matrix (Fin n) (Fin m) ℂ)
    {ι η : Type} [Fintype ι] [Fintype η]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ),
    n = m + S.card → (∀ i ∈ S, ∀ b, w i b = 0) → (wᴴ * Formalism.REAL.Jm ε * w).det ≠ 0 →
    (∀ x, (L x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * L x = 0 ∧ ∀ i ∈ S, ∀ j ∈ S, L x i j = 0) →
    (∀ x, ∑ i, ∑ j, ‖L x i j‖ ^ 2 = ‖x‖ ^ 2) →
    (∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 →
      (∀ i ∈ S, ∀ j ∈ S, M i j = 0) → ∃ x, L x = M) →
    (∀ t, (H t)ᴴ = H t) → (∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) →
    (∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) →
    (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map
        (fun z => reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2))) =
      ENNReal.ofReal (2 ^ (n * m) / ‖(wᴴ * Formalism.REAL.Jm ε * w).det‖ ^ S.card) • volume

end PI.AprimeInfW
end
end
