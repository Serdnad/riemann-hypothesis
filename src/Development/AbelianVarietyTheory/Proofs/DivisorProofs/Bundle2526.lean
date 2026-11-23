module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle065
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle053
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle128
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorEigenspace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle083
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle599
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCore.CMDiff0

theorem idxZero {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L N : Submodule (𝓞 K) V) : idx K 0 L N = ⊤ := by
  have : detSpan K 0 N = detSpan K 0 L := by
    unfold detSpan
    congr 1
    ext w
    simp
  rw [idx, this]
  exact (Ideal.eq_top_iff_one _).2 (Submodule.mem_colon.2 fun _ h => by simpa using h)

theorem cmDiff_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re := by

  intro E _ _ _ H hH _ χ hχ K _ _ ρ σ₁ p q X F h hF hq τ hτ
  subst hq
  classical
  let FA : ∀ b, GenFib (X.A b).pol := fun b =>
    (GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K (X.A b).pol).some
  have hM : ∀ j : Fin p ⊕ Fin 0, ∃ M, (FA j.isLeft).IsDiffOf F (X.φ j) M := fun j =>
    (DiffCoord.existsUnique_isDiffOf K _ (FA j.isLeft) _ F (X.φ j) (X.lin j).1).1.exists
  choose M hM using hM
  obtain ⟨gP, gQ, hg⟩ := GlobalTheory.T.exists_gramMatrices_cmUnitaryShimuraObject E H K ρ σ₁ p 0 X
  have hD : IsDiffs (FA true) (FA false) F (fun a => M (.inl a)) (fun a => M (.inr a)) :=
    ⟨fun a => hM (.inl a), fun a => hM (.inr a)⟩
  obtain ⟨𝔫, h𝔫₀, hid₀⟩ := GlobalTheory.T.cmDefinite_lieIndex_ideal_eq_norm_ideal E H hH K ρ σ₁ p X gP gQ hg
  have hQd : gQ.det = 1 := Matrix.det_fin_zero
  have h𝔫 : 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} := by
    rw [hQd, mul_one]; exact h𝔫₀
  have hid' : idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ) * Ideal.span {τ gQ.det} =
      𝔫.map τ * idx K 0 (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
        (subQ (FA false) F (fun a => M (.inr a)) (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
    rw [hQd, map_one, Ideal.span_singleton_one, Ideal.mul_top, idxZero, Ideal.mul_top]
    exact hid₀ (FA true) F (fun a => M (.inl a)) hD.1 τ hτ
  obtain ⟨hP0, hQ0, hdP, hdQ⟩ :=
    GlobalTheory.T.degree_images_eigenLines_cmUnitaryShimuraObject GlobalTheory.cmCurve_closed GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H K ρ σ₁ p 0 X χ hχ gP gQ hg (FA true) (FA false) F _ _ hD h hF τ hτ
  obtain ⟨hle, hrk1, -, hind, -⟩ :=
    GlobalTheory.CM.Indep.letters_independent GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 E H K ρ σ₁ p 0 X FA F M hM
  set τb : 𝓞 E →+* 𝓞 K := τ.comp (H.bar : 𝓞 E →+* 𝓞 E) with hτb
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτb' : τb H.rt = -ρ := by
    simp [hτb, GlobalTheory.CM.EigDec.bar_rt, hτ]
  have hne : ¬ τb H.rt = ρ := by
    rw [hτb']
    intro e
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact hρ ((mul_eq_zero.1 this).resolve_left two_ne_zero)
  have hdec := (GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ X.B F p 0 X.split X.typeB X.ρ_sq).1
  have hrkP : latRank K (F.eigLat X.B.t.act τ) = p := by rw [hdec, if_pos hτ]
  have hrkQ : latRank K (F.eigLat X.B.t.act τb) = 0 := by rw [hdec, if_neg hne]
  have hfg : ∀ σ, (F.eigLat X.B.t.act σ).FG := fun σ =>
    Submodule.FG.of_le (LieLattice.lieLat_fg_and_span_eq_top K _ F).1
      (Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩)
  have hsubP : subP (FA true) F (fun a => M (.inl a)) τ ≤ F.eigLat X.B.t.act τ :=
    iSup_le fun a => hle (.inl a, τ)
  have hsubQ : subQ (FA false) F (fun a => M (.inr a)) τb ≤ F.eigLat X.B.t.act τb :=
    iSup_le fun a => hle (.inr a, τb)
  have hrsP : latRank K (subP (FA true) F (fun a => M (.inl a)) τ) = p := by
    unfold subP
    beta_reduce
    refine (GlobalTheory.FlatCore.CMDiff.latRank_iSup (fun a : Fin p => ((FA true).eigLat (X.A true).t.act τ).map
        ((M (.inl a)).restrictScalars (𝓞 K)))
      (iSupIndep.comp hind (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin 0), τ))
      fun a b e => by simpa using e)).trans ?_
    have h1 : ∀ a : Fin p, latRank K (((FA true).eigLat (X.A true).t.act τ).map
        ((M (.inl a)).restrictScalars (𝓞 K))) = 1 := fun a => by
      have := hrk1 (.inl a, τ)
      simpa [hτ] using this
    calc _ = ∑ _a : Fin p, 1 := Finset.sum_congr rfl fun a _ => h1 a
      _ = p := by simp
  have hrsQ : latRank K (subQ (FA false) F (fun a => M (.inr a)) τb) = 0 := by
    unfold subQ
    beta_reduce
    refine (GlobalTheory.FlatCore.CMDiff.latRank_iSup (fun a : Fin 0 => ((FA false).eigLat (X.A false).t.act τb).map
        ((M (.inr a)).restrictScalars (𝓞 K)))
      (iSupIndep.comp hind (f := fun a : Fin 0 => ((Sum.inr a : Fin p ⊕ Fin 0), τb))
      fun a b e => by simpa using e)).trans ?_
    simp
  obtain ⟨hneP, hdegP⟩ := GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index K _ h p _ _ hsubP (hfg τ) hrkP hrsP
  obtain ⟨hneQ, hdegQ⟩ := GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index K _ h 0 _ _ hsubQ (hfg τb) hrkQ hrsQ
  rw [hdegP, hdegQ, hdP, hdQ]
  have hdvd := (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ ⊥).1
  have hfE : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfK : 0 < Module.finrank ℚ K := Module.finrank_pos
  set n := Module.finrank ℚ K / Module.finrank ℚ E with hn
  have hnK : (Module.finrank ℚ K : ℝ) = n * Module.finrank ℚ E := by
    rw [hn, Nat.cast_div hdvd (by exact_mod_cast hfE.ne')]
    field_simp
  have hn0 : 0 < n := Nat.div_pos (Nat.le_of_dvd hfK hdvd) hfE
  have hbar : Ideal.absNorm (𝔫.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm 𝔫 := by
    rw [(GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E E _ 𝔫).2, Nat.div_self hfE, pow_one]
  have hnorm : ∀ x : 𝓞 E, (Ideal.absNorm (Ideal.span {x}) : ℝ) = |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| := fun x => by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast
    rfl
  have hspan : Ideal.span {τ gQ.det} = (Ideal.span {gQ.det}).map τ := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan] at hid'
  have e1 := congrArg Ideal.absNorm hid'
  rw [map_mul, map_mul, (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ _).2, (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ _).2] at e1
  have e2 := congrArg Ideal.absNorm h𝔫
  rw [map_mul, hbar, ← Ideal.span_singleton_mul_span_singleton, map_mul] at e2
  have hA : (Ideal.absNorm (idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ)) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hneP)
  have hB : (Ideal.absNorm (idx K 0 (F.eigLat X.B.t.act τb) (subQ (FA false) F (fun a => M (.inr a)) τb)) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hneQ)
  have hP1 : (Ideal.absNorm (Ideal.span {gP.det}) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 (Ideal.span_singleton_eq_bot.not.2 hP0))
  have hQ1 : (Ideal.absNorm (Ideal.span {gQ.det}) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 (Ideal.span_singleton_eq_bot.not.2 hQ0))
  have hN1 : (Ideal.absNorm 𝔫 : ℝ) ≠ 0 := by
    intro h0
    have : ((Ideal.absNorm 𝔫 * Ideal.absNorm 𝔫 : ℕ) : ℝ) = 0 := by push_cast; rw [h0, zero_mul]
    rw [e2] at this
    push_cast at this
    exact (mul_ne_zero hP1 hQ1) this
  have l1 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e1
  have l2 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e2
  simp only [Nat.cast_mul, Nat.cast_pow] at l1 l2
  rw [Real.log_mul hA (pow_ne_zero _ hQ1), Real.log_mul (pow_ne_zero _ hN1) hB, Real.log_pow, Real.log_pow] at l1
  rw [Real.log_mul hN1 hN1, Real.log_mul hP1 hQ1] at l2
  rw [← hnorm, ← hnorm]
  have hfE' : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast hfE.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have key : Real.log (Ideal.absNorm (idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ)) : ℝ)
        / Module.finrank ℚ K
      - Real.log (Ideal.absNorm (idx K 0 (F.eigLat X.B.t.act τb) (subQ (FA false) F (fun a => M (.inr a)) τb)) : ℝ)
        / Module.finrank ℚ K =
      Real.log (Ideal.absNorm (Ideal.span {gP.det}) : ℝ) / (2 * Module.finrank ℚ E)
        - Real.log (Ideal.absNorm (Ideal.span {gQ.det}) : ℝ) / (2 * Module.finrank ℚ E) := by
    rw [← sub_div, ← sub_div, hnK]
    rw [div_eq_div_iff (mul_ne_zero hn' hfE') (mul_ne_zero two_ne_zero hfE')]
    linear_combination (2 * Module.finrank ℚ E : ℝ) * l1 + (n : ℝ) * (Module.finrank ℚ E : ℝ) * l2
  linear_combination key

end GlobalTheory.FlatCore.CMDiff0

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FacUpOdd

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem inPsi_conj_iff (H : Host E) (τ : E →+* ℂ) :
    InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have him := congrArg Complex.im H.sqrt_neg_disc_sq
  simp [pow_two] at hre him
  have hre0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := Complex.ext (by simp [hre0]) (by simp)
  have h0 : H.rt0 ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
    exact H.d_prime.ne_zero (by exact_mod_cast hre)
  have h3 : ¬ (-H.rt0 = H.rt0) := fun h => h0 (by linear_combination (-1/2 : ℂ) * h)
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [this]; simp
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · rw [h, hc]; simp [h3]
  · rw [h, map_neg, hc, neg_neg]; simp [h3]

theorem mult_of_inPsi {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : InPsi H τ) : Dw.mult τ = Dw.p := by
  unfold Datum.mult; rw [if_pos (show τ (H.rt : E) = H.rt0 from h)]

theorem mult_of_not_inPsi {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : ¬ InPsi H τ) : Dw.mult τ = Dw.q := by
  unfold Datum.mult; rw [if_neg (show ¬ τ (H.rt : E) = H.rt0 from h)]

theorem rpow_neg_succ (p : ℕ) (hp : 0 < p) (i : ℕ) :
    (p : ℝ) ^ (-((i : ℝ) + 1)) = ((p : ℝ)⁻¹) ^ (i + 1) := by
  have hp0 : (0 : ℝ) ≤ p := by positivity
  rw [Real.rpow_neg hp0, show ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, inv_pow]

theorem tsum_const (p : ℕ) (hp : 1 < p) (q : ℝ) :
    ∑' i : ℕ, (p : ℝ) ^ (-((i : ℝ) + 1)) * q = q / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have r0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have r1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have e : (fun i : ℕ => (p : ℝ) ^ (-((i : ℝ) + 1)) * q) = fun i => ((p : ℝ)⁻¹) ^ i * ((p : ℝ)⁻¹ * q) := by
    funext i; rw [rpow_neg_succ p (by omega), pow_succ]; ring
  rw [e, tsum_mul_right, tsum_geometric_of_lt_one r0 r1]
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  have : (p : ℝ) ≠ 0 := by linarith
  field_simp

theorem tsum_alt (p : ℕ) (hp : 1 < p) (a b : ℝ) :
    ∑' i : ℕ, (p : ℝ) ^ (-((i : ℝ) + 1)) * (if Even i then a else b) = (a * p + b) / ((p : ℝ) ^ 2 - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have r0 : (0 : ℝ) ≤ r ^ 2 := by positivity
  have r1 : r ^ 2 < 1 := by
    have : r < 1 := inv_lt_one_of_one_lt₀ hp1
    have : 0 ≤ r := by positivity
    nlinarith
  set g : ℕ → ℝ := fun i => (p : ℝ) ^ (-((i : ℝ) + 1)) * (if Even i then a else b) with hg
  have ge : (fun k => g (2 * k)) = fun k => (r ^ 2) ^ k * (r * a) := by
    funext k
    simp only [hg]
    rw [rpow_neg_succ p (by omega), if_pos (even_two_mul k), ← hr, pow_succ, pow_mul]; ring
  have go : (fun k => g (2 * k + 1)) = fun k => (r ^ 2) ^ k * (r ^ 2 * b) := by
    funext k
    simp only [hg]
    rw [rpow_neg_succ p (by omega), if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)), ← hr,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add, pow_mul]; ring
  have hs := summable_geometric_of_lt_one r0 r1
  rw [← tsum_even_add_odd (by rw [ge]; exact hs.mul_right _) (by rw [go]; exact hs.mul_right _), ge, go,
    tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one r0 r1]
  have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) - r ^ 2 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rw [hr]
  field_simp

end GlobalTheory.FacUpOdd

namespace GlobalTheory.FacUpOdd

theorem nuFac_le_odd_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit (p : T.V) → y.IsAlg → p ≠ 2 → ¬ (p : ℤ) ∣ discr E → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → (SplitInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1)) : ℝ) : EReal)) ∧ (InertInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) : ℝ) : EReal)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y hnu hy hp2 hdisc f k hpsi
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨X⟩ := GlobalTheory.CharDepth.nonempty_valExt T p hnu
  obtain ⟨Ch⟩ := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).1 (fun _ => rfl) T io y
  obtain ⟨hfot, horb⟩ := GlobalTheory.T.frobenius_orbit_of_unramified_prime E H l c p T io X hdisc
  obtain ⟨τ, i⟩ := f
  obtain ⟨h, hh, -, lab, hl0, hfr, hinj, -⟩ := horb τ
  haveI : NeZero h := ⟨hh.ne'⟩
  subst hl0
  obtain ⟨xs, hxs, hle⟩ := GlobalTheory.CharMinor.colength_bound p (GlobalTheory.ChF.unramified_companion_chart_characters p) hp2 E H Dw l Xo c
    T io y Ch X hy hdisc h lab hinj (fun s x => hfr s x) 0
  have hnu := (GlobalTheory.T.flagStep_characters_of_colength E H Dw l Xo c p T io y Ch X ⟨lab 0, i⟩ xs _ hxs hle).2 k
  have hstep : ∀ n : ℕ, lab ((n + 1 : ℕ) : ZMod h) = lab ((n : ZMod h) + 1) := fun n => by push_cast; rfl
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · have hall : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) := by
      intro n
      induction n with
      | zero => simpa using hpsi
      | succ n ih => rw [hstep]; exact ((hfot _ _ (hfr _)).1 hs).2 ih
    refine hnu.trans (le_of_eq ?_)
    congr 2
    rw [← tsum_const p hp1]
    refine tsum_congr fun n => ?_
    rw [zero_add, mult_of_not_inPsi Dw ((inPsi_conj_iff H _).1.mt (not_not.2 (hall (n + 1))))]
  · have halt : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) ↔ Even n := by
      intro n
      induction n with
      | zero => simpa using hpsi
      | succ n ih =>
        rw [hstep, ((hfot _ _ (hfr _)).2 hi), inPsi_conj_iff, ih, Nat.even_add_one]
    refine hnu.trans (le_of_eq ?_)
    congr 2
    have e : ∀ n : ℕ, (Dw.mult (ComplexEmbedding.conjugate (lab (0 + ((n + 1 : ℕ) : ZMod h)))) : ℝ) =
        if Even n then (Dw.p : ℝ) else Dw.q := by
      intro n
      rw [zero_add]
      by_cases hn : Even n
      · rw [if_pos hn, mult_of_inPsi Dw ((inPsi_conj_iff H _).2 (fun h' => ?_))]
        have := (halt (n + 1)).1 h'
        rw [Nat.even_add_one] at this
        exact this hn
      · rw [if_neg hn, mult_of_not_inPsi Dw (fun h' => ?_)]
        have := (inPsi_conj_iff H _).1 h'
        rw [halt, Nat.even_add_one, not_not] at this
        exact hn this
    rw [tsum_congr fun n => by rw [e n], tsum_alt p hp1]
    have hp1' : (1 : ℝ) < p := by exact_mod_cast hp1
    have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring

end GlobalTheory.FacUpOdd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareResChars

theorem resEta_mul_pow {D : D7} {c η : (AE D)ˣ →* Circle} (hc : ResEta D c 0) (hη : ResEta D η 1) {n k : ℕ}
    (h : n % 2 = k % 2) : ResEta D (c * η ^ (n % 2)) k := by
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · rw [e, pow_zero, mul_one]
    exact resEta_parity hc (by omega)
  · rw [e, pow_one]
    exact resEta_parity (resEta_mul hc hη) (by omega)

theorem resEta_alpha_beta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), GlobalTheory.LFun.ResEta D.host.F D.host.E (alpha G t i j) (spW₁ G i j).rank ∧
      GlobalTheory.LFun.ResEta D.host.F D.host.E (beta G i j) (spW G i j).rank := by
  intro D T L sc G μ₀ hL t i j
  have hi := i.2
  have hj := j.2
  have hη := GlobalTheory.HeckeCharacterRestriction.resEta_eta hL
  have hμ := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hχ : ResEta D (G.ch.chi (D.R.m - i)) 0 := ⟨hη.1, fun η _ a => by
    rw [pow_zero]
    exact GlobalTheory.GridWeil.triv_base (G.ch.chi_eq _ (by omega) (by omega)) (G.ch.triv _ (by omega) (by omega)) a⟩
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hpar : (spW₁ G i j).rank % 2 = (spW G i j).rank % 2 := by
    have e : (spW G i j).rank = (spW₁ G i j).rank + D.R.t + sLen D := by
      show (G.V (.grid (i + 1) (j + 1))).rank = (G.V (.grid i j)).rank + _ + _
      rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
      simp only [rankV]
      ring
    obtain ⟨p, hp⟩ := D.R.t_odd
    obtain ⟨q, hq⟩ := odd_sLen D
    omega
  have h1 : ResEta D (alpha G t i j) (spW₁ G i j).rank := resEta_mul_pow hμ hη rfl
  have h2 : ResEta D (beta G i j) (spW G i j).rank := resEta_mul_pow hχ hη hpar
  exact ⟨h1, h2⟩

end GlobalTheory.SquareResChars
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_gridDatum_pureTensor_vacuaAE : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧ φ₀ ∈ GlobalTheory.WeilM.SB _ ∧ φ₀ ≠ 0 ∧
        ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin (G.V (.grid i j)).rank → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → D.host.E))
          (θ : 𝓞 D.host.E), (θ : D.host.E) + D.sp.cm.sig θ = 1 ∧ (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) ∧
          ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀ := by
  first | exact @GlobalTheory.SmallDatumVac.exists_datum_pure_vac | exact GlobalTheory.SmallDatumVac.exists_datum_pure_vac | (intros; apply GlobalTheory.SmallDatumVac.exists_datum_pure_vac <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.howeAlg_of_cyclic_highest_weight : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  first | exact @GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic | exact GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic | (intros; apply GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic <;> assumption)
end
