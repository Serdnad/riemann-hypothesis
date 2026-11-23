module

public import Formalism.HarderNarasimhan.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle175
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Formalism.HermitianLattices.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.Bundle002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ProductDecompositionHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup
public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
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
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.hilbertSchmidt_lower_bound_inverseDifferent :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ)
      (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
      (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
      (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ),
      (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → 0 < lo →
      (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) →
      Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi →
      ∀ ψ : Matrix (Fin a) (Fin b) K, (∃ y ∈ B, ψ *ᵥ y ≠ 0) →
        (∀ δ ∈ differentIdeal ℤ (𝓞 K), ∀ y ∈ B, δ • (ψ *ᵥ y) ∈ A) →
        (Formalism.HN.nPl K : ℝ) *
            (lo / (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi)) ^ 2 ≤
          ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ψ.map w.embedding * X' w) i j‖ ^ 2 := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' _ hB hlo hA hhi ψ ⟨y, hyB, hy⟩ hψ
  let φ : (Fin b → K) →ₗ[K] (Fin a → K) := Matrix.toLin' ψ
  let A' : Submodule (𝓞 K) (Fin a → K) := B.map (φ.restrictScalars (𝓞 K))
  let rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ)))
  have hrdpos : 0 < rd :=
    Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)) _
  have hA'fg : A'.FG := hB.map _
  have hA'0 : A' ≠ ⊥ := by
    intro h
    have hmem : ψ *ᵥ y ∈ A' := ⟨y, hyB, by simp [φ]⟩
    rw [h] at hmem
    exact hy hmem
  have hB0 : B ≠ ⊥ := by
    intro h
    apply hA'0
    simp [A', h]
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hleast : lo / rd ≤ leastSize (Pi.basisFun K (Fin a)) X A' := by
    refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
    have hle : differentIdeal ℤ (𝓞 K) • N ≤ A := by
      refine Submodule.smul_le.2 fun δ hδ v hv => ?_
      obtain ⟨z, hz, rfl⟩ := hN hv
      simpa [φ] using hψ δ hδ z hz
    have hspan := Formalism.HN.DualPolygon.twist_span_smul N _ hd
    have hne : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
      intro h
      rw [h] at hspan
      apply hN0
      rw [eq_bot_iff]
      intro v hv
      have hmem : v ∈ Submodule.span K (N : Set (Fin a → K)) := Submodule.subset_span hv
      rw [← hspan] at hmem
      simpa using hmem
    have hsize :
        Formalism.HN.size (Pi.basisFun K (Fin a)) X (differentIdeal ℤ (𝓞 K) • N) =
          Formalism.HN.size (Pi.basisFun K (Fin a)) X N * rd := by
      have hrk : rkK (differentIdeal ℤ (𝓞 K) • N) = rkK N := by
        unfold rkK
        rw [hspan]
      have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) =
          |(NumberField.discr K : ℝ)| := by
        rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
      have hj : (rkK N : ℝ) ≠ 0 := by
        exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
      have hf : (Formalism.HN.nPl K : ℝ) ≠ 0 := by
        have hcard : 0 < Formalism.HN.nPl K := Fintype.card_pos
        exact_mod_cast hcard.ne'
      unfold Formalism.HN.size rd
      rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hNfg hd, hrk, hnorm,
        Real.mul_rpow (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hNfg).le
          (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 2
      field_simp
    rw [div_le_iff₀ hrdpos, ← hsize]
    exact hA _ hle hne
  have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
    rw [(sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
    exact Real.exp_pos _
  have hM := sizeIneq K _ _ _ _ (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
    hB hA'fg le_rfl hA'0
  have h4 : lo / (rd * hi) ≤
      (∏ v, opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ) ^
        ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
    refine le_trans ?_ hM
    rw [← div_div]
    exact div_le_div₀ ((div_pos hlo hrdpos).le.trans hleast) hleast hLpos hhi
  have h5 := GlobalTheory.DualBound.card_mul_geom_sq_le
    (fun v => opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ)
    (fun v => norm_nonneg _)
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg hlo.le (mul_nonneg hrdpos.le (hLpos.le.trans hhi))) h4 2)
      (Nat.cast_nonneg _)
    _ ≤ _ := h5
    _ ≤ _ := by
      refine Finset.sum_le_sum fun w _ => ?_
      have hmatrix : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a)) φ = ψ := by
        ext i j
        simp [φ]
      unfold opNormAt
      rw [hmatrix]
      exact GlobalTheory.DualBound.opNorm_sq_le_hs _
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.SkewUnit

theorem exists_sub_notMem {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (hσ : ∀ x, σ (σ x) = x) {p : R} (hp : p ≠ 0) (hσp : σ p = p)
    (h : ∀ P : Ideal R, P.IsMaximal → ∃ θ, θ - σ θ ∉ P) :
    ∃ θ, ∀ P : Ideal R, P.IsMaximal → p ∈ P → θ - σ θ ∉ P := by
  classical
  have hfin : {P : Ideal R | P.IsMaximal ∧ p ∈ P}.Finite := by
    have h1 := (Ideal.finite_factors (I := Ideal.span {p}) (by simpa using hp)).image
      (fun v => v.asIdeal)
    refine h1.subset ?_
    rintro P ⟨hP, hpP⟩
    have hne : P ≠ ⊥ := fun h0 => hp (by simpa [h0] using hpP)
    exact ⟨⟨P, hP.isPrime, hne⟩, by
      simpa [Ideal.dvd_span_singleton] using hpP, rfl⟩
  have : Finite {P : Ideal R // P.IsMaximal ∧ p ∈ P} := hfin.to_subtype
  let x : Ideal R → R := fun P => Classical.epsilon (fun θ => θ - σ θ ∉ P)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal
    (ι := {P : Ideal R // P.IsMaximal ∧ p ∈ P}) (I := fun P => P.1)
    (fun P Q hPQ => by
      have := P.2.1
      have := Q.2.1
      exact Ideal.isCoprime_iff_sup_eq.2
        (Ideal.IsMaximal.coprime_of_ne P.2.1 Q.2.1 (fun e => hPQ (Subtype.ext e))))
    (fun P => x P.1)
  refine ⟨r, fun P hP hpP hmem => ?_⟩
  have hsurj : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩
  have := hP
  have hQ : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hpQ : p ∈ P.comap σ := by rw [Ideal.mem_comap, hσp]; exact hpP
  have hx : x (P.comap σ) = x P := by
    have : (fun θ => θ - σ θ ∉ P.comap σ) = (fun θ => θ - σ θ ∉ P) := by
      funext θ
      rw [Ideal.mem_comap, map_sub, hσ, ← neg_sub, Ideal.neg_mem_iff]
    simp only [x, this]
  have h1 : r - x P ∈ P := hr ⟨P, hP, hpP⟩
  have h2 : r - x (P.comap σ) ∈ P.comap σ := hr ⟨_, hQ, hpQ⟩
  rw [hx, Ideal.mem_comap, map_sub] at h2
  have h3 : x P - σ (x P) ∉ P := Classical.epsilon_spec (h P hP)
  apply h3
  have : x P - σ (x P) = (r - σ r) - (r - x P) + (σ r - σ (x P)) := by ring
  rw [this]
  exact add_mem (sub_mem hmem h1) h2

theorem prod_norm_sq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ι : Type} [Fintype ι]
    (φ : ι → E →+* ℂ) (hφ : Function.Bijective (fun v => InfinitePlace.mk (φ v))) (δ : 𝓞 E) :
    ∏ v, ‖φ v (δ : E)‖ ^ 2 = ((Algebra.norm ℤ δ).natAbs : ℝ) := by
  have h1 := InfinitePlace.prod_eq_abs_norm (δ : E)
  rw [← hφ.prod_comp (fun w => w (δ : E) ^ w.mult)] at h1
  simp only [IsTotallyComplex.mult_eq, InfinitePlace.apply] at h1
  rw [h1, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

theorem exists_skew_norm_coprime : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ p : ℕ, p.Prime → ∃ (δ : 𝓞 E) (N : ℕ), star (δ : E) = -(δ : E) ∧ ¬ p ∣ N ∧ ∏ v, ‖φ v (δ : E)‖ ^ 2 = N := by
  intro E _ _ _ hE ι _ φ hφ p hp
  have := hE.1
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ x, ((σ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])
  obtain ⟨θ, hθ⟩ := exists_sub_notMem σ hσσ (p := (p : 𝓞 E)) (by exact_mod_cast hp.ne_zero)
    (map_natCast σ p) (fun P hP => by
      obtain ⟨θ, t, ht, hm⟩ := hE.2.2 P hP
      have : σ θ = t := RingOfIntegers.ext (by rw [hσ]; exact ht.symm)
      exact ⟨θ, by rwa [this]⟩)
  refine ⟨θ - σ θ, (Algebra.norm ℤ (θ - σ θ)).natAbs, ?_, ?_, prod_norm_sq φ hφ _⟩
  · rw [← hσ, map_sub σ, hσσ, ← neg_sub θ]
    exact map_neg (algebraMap (𝓞 E) E) _
  · intro hd
    rw [← Ideal.absNorm_span_singleton] at hd
    obtain ⟨P, hP, hu, hdv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm
      (Nat.prime_iff_prime_int.1 hp) _ (Int.natCast_dvd_natCast.2 hd)
    refine hθ P hP ?_ (Ideal.dvd_span_singleton.1 hdv)
    have : (p : ℤ) ∈ Ideal.under ℤ P := hu ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this

end GlobalTheory.RadCov.SkewUnit
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.MeasWord

theorem exists_measW_prescribed :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r)
      (T : F), P.IsStd σ J T → ∀ (μNinf : Measure (Nsub (Ainf F) σ J P))
      (μHinf : Measure (Hsub (Ainf F) σ J P)) (μN : Measure (Nsub (AF F) σ J P))
      (μH : Measure (Hsub (AF F) σ J P))
      (μSv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Ssub (Fv F v) σ J P)),
      μNinf.IsHaarMeasure → μHinf.IsHaarMeasure → μN.IsHaarMeasure → μH.IsHaarMeasure →
      (∀ v, (μSv v).IsHaarMeasure) →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf ∧ W.μN = μN ∧ W.μH = μH ∧
        W.μSv = μSv := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP μNinf μHinf μN μH μSv hNinf hHinf hN hH hSv
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  obtain ⟨eH, heH⟩ := PI.UnitaryGroupMassFormula.MeasWCore.hermitian_measure_splitting F E σ n J r P T hCM hJ hP
  obtain ⟨eN, heN⟩ := PI.UnitaryGroupMassFormula.MeasWCore.nilpotent_measure_splitting F E σ n J r P T hCM hJ hP
  have hsm : Measurable (splitA σ J) := (PI.UnitaryGroupMassFormula.MeasWCore.continuous_measure_splitting F E σ n J hCM).measurable
  have : SecondCountableTopology (Hsub (AF F) σ J P) :=
    eH.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Nsub (AF F) σ J P) :=
    eN.toHomeomorph.symm.isEmbedding.secondCountableTopology
  obtain ⟨μHf, hHf, hHeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eH μHinf μH
  obtain ⟨μNf, hNf, hNeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eN μNinf μN
  obtain ⟨μSf, hSH, hSeq⟩ := PI.UnitaryGroupMassFormula.MeasWCore.product_decomposition_holds F E σ n J r P T hCM hJ hP μNf μHf hNf hHf
  have : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance
  have : SigmaFinite μHinf := inferInstance
  have : SigmaFinite μNinf := inferInstance
  have : SigmaFinite μHf := inferInstance
  have : SigmaFinite μNf := inferInstance
  refine ⟨{ μH := μH, μHinf := μHinf, μHf := μHf, μN := μN, μNinf := μNinf, μNf := μNf, μSf := μSf,
            μSv := μSv }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hH, hHinf, hHf, hN, hNinf, hNf, hSH, hSv, ?_, ?_, hSeq⟩
  · show (μH.map Subtype.val).map (splitA σ J) = _
    rw [← hHeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eH eH.continuous.measurable heH μHinf μHf
  · show (μN.map Subtype.val).map (splitA σ J) = _
    rw [← hNeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eN eN.continuous.measurable heN μNinf μNf

end GlobalTheory.St.MeasWord
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselSchur

theorem fdegHC_pos {n : ℕ} {mu : Fin n → ℝ} (h : StrictAnti mu) : 0 < Formalism.QuantumDeterminants.fdegHC mu := by
  unfold Formalism.QuantumDeterminants.fdegHC
  refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
  · have := h (Finset.mem_filter.1 hb).2
    exact abs_pos.2 (sub_ne_zero.2 this.ne')
  · have : (a : ℕ) < b := (Finset.mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
    linarith

theorem measurableEmbedding_lmul {k r : ℕ} {t : MatKR k r} (ht : IsUnit t.det) :
    MeasurableEmbedding (fun x : Mt k r => (fun i j => (t⁻¹ * Matrix.of x) i j : Mt k r)) := by
  have hc : ∀ s : MatKR k r, Continuous (fun x : Mt k r => (fun i j => (s * Matrix.of x) i j : Mt k r)) := fun s => by
    have h1 : Continuous (fun x : Mt k r => (Matrix.of x : MatKR k r)) := continuous_id
    exact continuous_const.matrix_mul h1
  let e : Mt k r ≃ᵐ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => by
        show t * (t⁻¹ * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
      right_inv := fun x => by
        show t⁻¹ * (t * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul]
      measurable_toFun := (hc _).measurable
      measurable_invFun := (hc _).measurable }
  exact e.measurableEmbedding

theorem isBesselMapSm_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Wp : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp} (h : IsBesselMapSm z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW σ w v := fun w v => by
    induction w with
    | nil => rfl
    | cons X w ih => exact congrArg (dsig σ X) ih
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simpa only [e] using h5 v hv

theorem theta_pos (D : D7) {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (hv : 0 ≤ D.host.v) (hW : GoodW D τ w w' θ W) : 0 < θ := by
  by_contra hθ
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, q1, -⟩ := hW
  have hk : kapN D θ = 0 :=
    ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by positivity) _) (not_lt.1 hθ))
  have hN0 : W.μN = 0 := by rw [hN, hk]; unfold haarLie; exact zero_smul _ _
  have h1 := q1 (fun _ => 1) measurable_const
  rw [hN0] at h1
  simp only [muS, Measure.prod_zero, Measure.map_zero, lintegral_const, one_mul, Measure.coe_zero,
    Pi.zero_apply, zero_mul] at h1
  exact hG.2.1 (Measure.measure_univ_eq_zero.1 h1)

end GlobalTheory.BesselSchur
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.SkewSpan

theorem skew_conj {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) : Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε = -B := by
  have h' : Bᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * B) := eq_neg_of_add_eq_zero_left h
  rw [Matrix.mul_assoc, h', Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self,
    Matrix.one_mul]

theorem trace_twisted {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) (X : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace = - starRingEnd ℂ (X * Bᴴ).trace := by
  have h1 : (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace
      = (Xᴴ * (Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : starRingEnd ℂ (X * Bᴴ).trace = (Xᴴ * B).trace := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  rw [h1, h2, skew_conj ε h, Matrix.mul_neg, Matrix.trace_neg]

theorem real_span (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (s : Set (Fin d)) (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hG : ∀ i, Formalism.REAL.inG ε (B i)) :
    (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧
    (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧
    ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace
      = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  have h2 : ∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0 := by
    intro X hX i hi
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [hB, if_neg]
      rintro rfl
      exact hi hk
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  have hexp : ∀ X ∈ Submodule.span ℂ (B '' s), X = ∑ i, (X * (B i)ᴴ).trace • B i := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      simp [hB]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Matrix.add_mul, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul c x _ hx =>
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_assoc, ← Finset.smul_sum]
      rw [← hx]
  refine ⟨fun X => ⟨?_, ?_⟩, h2, fun X i => trace_twisted ε (hG i) X⟩
  · rintro ⟨hX, hXG⟩
    rw [hexp X hX]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ s
    · have h3 := trace_twisted ε (hG i) X
      rw [skew_conj ε hXG, Matrix.neg_mul, Matrix.trace_neg, neg_inj] at h3
      have h4 : (X * (B i)ᴴ).trace = (((X * (B i)ᴴ).trace.re : ℝ) : ℂ) :=
        (Complex.conj_eq_iff_re.mp h3.symm).symm
      rw [h4, Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [h2 X hX i hi, zero_smul]
      exact Submodule.zero_mem _
  · intro hX
    refine ⟨Submodule.span_le_restrictScalars ℝ ℂ _ hX, ?_⟩
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hG k
    | zero => simp [Formalism.REAL.inG]
    | add x y _ _ hx hy =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hx, hy,
        add_zero]
    | smul c x _ hx =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        hx, smul_zero]

end GlobalTheory.SkewSpan
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem lintegral_pi_prod_mul : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν] (f : ∀ i, X i → ENNReal) (g : Y → ENNReal), (∀ i, Measurable (f i)) → Measurable g → ∫⁻ p, (∏ i, f i (p.1 i)) * g p.2 ∂((Measure.pi μ).prod ν) = (∏ i, ∫⁻ y, f i y ∂(μ i)) * ∫⁻ y, g y ∂ν := by
  intro ι _ X _ μ _ Y _ ν _ f g hf hg
  have hm : Measurable fun x : ∀ i, X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
  rw [← GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf]
  exact lintegral_prod_mul hm.aemeasurable hg.aemeasurable

end GlobalTheory.StabUnfold
end
