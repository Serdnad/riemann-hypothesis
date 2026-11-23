module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle001
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Chebotarev.Bundle001
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.coordinate_bijection_trace_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧ (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧ ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (β : F) (x : Fin M × Fin d → F), gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff | exact GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff | (intros; apply GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_gram_iff <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.finite_adelic_lattice_membership_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (d M : ℕ) (b : Module.Basis (Fin d) F E) (a : ℕ) (X : Fin 1 → Fin M → Af F ⊗[F] E), (∀ v, (fun p i => (a : Fv F v ⊗[F] E) * projV v X p i) ∈ latV b v) ↔ ∀ i v, ((a : Af F) * cv (Af F) b (X 0) i) v ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff | exact GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff | (intros; apply GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.trace_form_invariance_under_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ h : HA (AF F) σ J, (gmat (AF F) σ J b h)ᵀ * B.map (algebraMap F (AF F)) * gmat (AF F) σ J b h = B.map (algebraMap F (AF F))) → (∀ ω w, (ginf e σ J b ω w)ᵀ * B.map (ρ w) * ginf e σ J b ω w = B.map (ρ w)) ∧ ∀ ω, (gfin σ J b ω)ᵀ * B.map (algebraMap F (Af F)) * gfin σ J b ω = B.map (algebraMap F (Af F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry | exact GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem unitChoice_of_isArtinianRing_isReduced :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R], PIW.AdelicOrbitU.UnitChoice R := by
  intro R _ _ _ k f hf
  classical
  let φ := IsArtinianRing.equivPi R
  have hex : ∀ I : MaximalSpectrum R, ∃ i, φ (f i) I ≠ 0 := by
    intro I
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    let ψ : R →+* R ⧸ I.asIdeal :=
      (Pi.evalRingHom (fun J : MaximalSpectrum R => R ⧸ J.asIdeal) I).comp φ.toRingHom
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (RingHom.mem_ker).2 (h i)
    rw [hf] at hle
    have h1 : ψ 1 = 0 := (RingHom.mem_ker).1 (hle Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  choose c hc using hex
  let E : Fin k → ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal := fun i I => if c I = i then 1 else 0
  refine ⟨fun i => φ.symm (E i), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← map_mul]
    apply congrArg φ.symm
    funext I
    by_cases h : c I = i <;> simp [Pi.mul_apply, E, h]
  · intro i j hij
    rw [← map_mul, ← map_zero φ.symm]
    apply congrArg φ.symm
    funext I
    by_cases hi : c I = i
    · simp [Pi.mul_apply, E, hi, hij]
    · simp [Pi.mul_apply, E, hi]

  · rw [← map_sum, ← map_one φ.symm]
    apply congrArg φ.symm
    funext I
    simp [Finset.sum_apply, E]

  · rw [← isUnit_map_iff φ, map_sum, Pi.isUnit_iff]
    intro I
    have hcomp : (∑ i, φ (φ.symm (E i) * f i)) I = φ (f (c I)) I := by
      simp only [map_mul, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.mul_apply, E, ite_mul,
        one_mul, zero_mul, Fintype.sum_ite_eq]
    rw [hcomp]
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact isUnit_iff_ne_zero.2 (hc I)

end GlobalTheory.CompanionTheory.SW
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.DetScale

open Matrix
open scoped Pointwise

section Ring

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurable_mulVec (A : Matrix ι ι R) :
    Measurable (fun x : ι → R => A *ᵥ x) :=
  (continuous_const.matrix_mulVec continuous_id : Continuous fun x : ι → R => A *ᵥ x).measurable

theorem char_smul_map (lam : Measure R) [lam.IsAddHaarMeasure] (u : Rˣ) :
    distribHaarChar R u • lam.map (fun x => (u : R) * x) = lam := by
  have hm : Measurable fun x : R => (u : R) * x :=
    (continuous_const.mul continuous_id).measurable
  ext S hS
  rw [Measure.smul_apply, Measure.map_apply hm hS]
  have h1 := distribHaarChar_mul lam u ((fun x : R => (u : R) * x) ⁻¹' S)
  have e : u • ((fun x : R => (u : R) * x) ⁻¹' S) = S := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e] at h1
  rw [ENNReal.smul_def, smul_eq_mul]
  exact h1

theorem map_transvection (lam : Measure R) [lam.IsAddHaarMeasure] (i j : ι) (c : R) (hij : i ≠ j) :
    (Measure.pi fun _ : ι => lam).map (fun x => transvection i j c *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  have ht := measurable_mulVec (transvection i j c)
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  simp [transvection, add_mulVec, single_mulVec, hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)]

theorem map_diagonal (lam : Measure R) [lam.IsAddHaarMeasure] (d : ι → Rˣ) :
    distribHaarChar R (∏ i, d i) •
        (Measure.pi fun _ : ι => lam).map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.smul_apply, Measure.map_apply (measurable_mulVec _) (MeasurableSet.univ_pi hs)]
  have h1 : (fun x : ι → R => diagonal (fun i => (d i : R)) *ᵥ x) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i => (fun y : R => (d i : R) * y) ⁻¹' s i := by
    ext f
    simp [mulVec_diagonal]
  have hm : ∀ i, Measurable fun x : R => (d i : R) * x := fun i =>
    (continuous_const.mul continuous_id).measurable
  rw [h1, Measure.pi_pi, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 := congrArg (fun m : Measure R => m (s i)) (char_smul_map lam (d i))
  simp only [Measure.smul_apply, Measure.map_apply (hm i) (hs i)] at h2
  rw [← h2]
  rfl

end Ring

theorem smul_map_pi {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    {ι : Type} [Fintype ι] [DecidableEq ι] (lam : Measure R) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι F) (h : A.det ≠ 0) :
    distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  let u : Fˣ →* Rˣ := Units.map (algebraMap F R : F →* R)
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun A : Matrix ι ι F => ∀ h : A.det ≠ 0, distribHaarChar R (u (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam) A h ?_ ?_ ?_ h
  · intro D hD h
    have hD' : ∀ i, D i ≠ 0 := fun i => by
      rw [det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have e1 : u (Units.mk0 (diagonal D).det h) = ∏ i, u (Units.mk0 (D i) (hD' i)) := by
      rw [← map_prod]
      congr 1
      ext
      simp [det_diagonal]
    have e2 : (diagonal D).map (algebraMap F R) =
        diagonal fun i => ((u (Units.mk0 (D i) (hD' i)) : Rˣ) : R) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [u]
      · simp [u, hab]
    rw [e1, e2]
    exact map_diagonal lam _
  · intro t h
    obtain ⟨i, j, hij, c⟩ := t
    have e1 : u (Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h) = 1 := by
      rw [show Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h = 1 from
        Units.ext (by simpa [TransvectionStruct.toMatrix] using det_transvection_of_ne i j hij c), map_one]
    have e2 : (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ : Matrix ι ι F).map (algebraMap F R) =
        transvection i j (algebraMap F R c) := by
      ext a b
      simp [TransvectionStruct.toMatrix, transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, apply_ite (algebraMap F R)]
    rw [e1, e2, map_one, one_smul]
    exact map_transvection lam i j _ hij
  · intro A B hA hB IHA IHB h
    have e1 : Units.mk0 (A * B).det h = Units.mk0 A.det hA * Units.mk0 B.det hB :=
      Units.ext (by simp [det_mul])
    have e2 : (fun x : ι → R => (A * B).map (algebraMap F R) *ᵥ x) =
        (fun x => A.map (algebraMap F R) *ᵥ x) ∘ (fun x => B.map (algebraMap F R) *ᵥ x) := by
      ext1 x
      simp [Matrix.map_mul, mulVec_mulVec]
    rw [e1, e2, map_mul, map_mul, mul_smul,
      ← Measure.map_map (measurable_mulVec _) (measurable_mulVec _),
      ← Measure.map_smul _ (measurable_mulVec _).aemeasurable, IHB hB]
    exact IHA hA

theorem map_mulVec_eq_smul : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R),
    lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam →
    ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure →
      μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  intro F _ R _ _ _ _ _ _ _ _ _ ι _ _ A hA lam hlam c hc μ hμ
  have h1 := smul_map_pi lam A hA
  have h2 := char_smul_map lam (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  set d := distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  have h2' : d • lam.map (fun x => algebraMap F R A.det * x) = lam := h2
  rw [hc] at h2'
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set R, IsCompact K ∧ K ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  have hdc : d * c = 1 := by
    have h3 := congrArg (fun m : Measure R => m K) h2'
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    rw [← mul_assoc, ← ENNReal.coe_mul] at h3
    have h4 : ((d * c : ℝ≥0) : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds lam hK0).ne' hKc.measure_lt_top.ne).1
        (h3.trans (one_mul _).symm)
    exact_mod_cast h4
  have h4 : (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      c • Measure.pi fun _ : ι => lam := by
    conv_rhs => rw [← h1]
    rw [smul_smul, mul_comm c d, hdc, one_smul]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • Measure.pi fun _ : ι => lam :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular μ (Measure.pi fun _ : ι => lam)⟩
  rw [hk, Measure.map_smul _ (measurable_mulVec _).aemeasurable, h4, smul_comm]

end GlobalTheory.CompanionTheory.SW.DetScale
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Primes

theorem summable_one_div_absNorm_sq :
    ∀ (F : Type) [Field F] [NumberField F],
      Summable fun v : HeightOneSpectrum (𝓞 F) => 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro F _ _
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F (s := 2) (by norm_num)).comp_injective
    (i := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)
  refine h.congr fun v => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  norm_num

end GlobalTheory.CompanionTheory.SW.Primes
end
