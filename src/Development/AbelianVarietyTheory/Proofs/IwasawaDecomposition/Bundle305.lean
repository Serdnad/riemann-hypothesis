module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle106
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle135
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle138
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle228
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.PlaceVec

open GlobalTheory.AdelicLatMove

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapAdj_eq (x : WO S T) : frMapAdj S T βS βT x =
    ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) * ((x.map (toEAf D)).map (cF D))ᵀ * (T.gram.map (eToEAf D) * βT.val) := by
  have e : ((x.map (cA D))ᵀ).map (toEAf D) = ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => toEAf_cA _
  unfold frMapAdj
  rw [Matrix.map_mul, Matrix.map_mul, e]
  simp only [Matrix.mul_assoc]
  rfl

theorem frMapAdj_add (x y : WO S T) : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  have e : (((x + y).map (toEAf D)).map (cF D))ᵀ = ((x.map (toEAf D)).map (cF D))ᵀ + ((y.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => ((cF D).comp (toEAf D)).map_add (x j i) (y j i)
  rw [frMapAdj_eq, frMapAdj_eq, frMapAdj_eq, e, Matrix.mul_add, Matrix.add_mul]

theorem cF_cF_toEAf (a : AE D) : cF D (cF D (toEAf D a)) = toEAf D a := by
  rw [← toEAf_cA, ← toEAf_cA, GlobalTheory.DualPairCheck.cA_cA]

theorem sandwich_cancel {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (hA : A * A' = 1) (hG : G * G' = 1)
    (hB : B * B' = 1) (hH : H * H' = 1) : (G * A) * ((A' * G') * N * (H * B)) * (B' * H') = N := by
  calc _ = (G * (A * A') * G') * N * (H * (B * B') * H') := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hA, hB, Matrix.mul_one, Matrix.mul_one, hG, hH, Matrix.one_mul, Matrix.mul_one]

theorem gram_map_mul_inv : S.gram.map (eToEAf D) * (S.gram⁻¹).map (eToEAf D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem frMapAdj_up : ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (x.map (toEAf D)) → IsIntM (k • frMapAdj S T βS βT x) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) (T.gram.map (eToEAf D) * βT.val)
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [frMapAdj_eq]
  exact h _ fun i j => cF_mem_int (hx j i)

theorem frMapAdj_down :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (frMapAdj S T βS βT x) → IsIntM (k • x.map (toEAf D)) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int (S.gram.map (eToEAf D) * βS.val) ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))
  refine ⟨k, hk, fun x hx i j => ?_⟩
  have h1 := h _ hx
  rw [frMapAdj_eq, sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv (gram_map_mul_inv S) βT.mul_inv
    (gram_map_mul_inv T)] at h1
  have h2 : cF D (k • cF D (toEAf D (x i j))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := cF_mem_int (h1 j i)
  rw [nsmul_eq_mul, RingHom.map_mul, map_natCast, cF_cF_toEAf, ← nsmul_eq_mul] at h2
  exact h2

theorem thPVecExists : ∀ D : D7, ThPVecExists D := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf₀
  classical
  have hinf := infPart_cA (idemSum_infPart he)
  have hSfull := selfDual_isFullLattice S ΛS hS
  have hTfull := selfDual_isFullLattice T ΛT hT
  obtain ⟨f, hf⟩ := exists_isThetaAt hf₀.1 hS hT (a := cA D e) (by rw [← RingHom.map_mul, idemSum_mul_self he]) hinf
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf₀.1 S T ΛS ΛT hS hT _ e he f₀ hf₀.2.theta hf₀.2.lat).2
    (isSBHalf_of_red hSfull hTfull hinf (frMapAdj S T βS βT) (frMapAdj_add S T βS βT) (frMapAdj_up S T βS βT)
      (frMapAdj_down S T βS βT) (Pg ∪ Q) (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])
  exact ⟨f, hf₀, e, he, hf⟩

end GlobalTheory.PlaceVec

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

noncomputable section

namespace GlobalTheory.Mem.Col2.ChiFacLaw

open GlobalTheory.PeriodTransport GlobalTheory.IdealTransport

theorem detId_image (D : D7) {n : ℕ} (L₀ L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (G G' : Matrix (Fin n) (Fin n) D.host.E) (hu : G * G' = 1)
    (h : ∀ x ∈ L, G.mulVec x ∈ L') (h' : ∀ x ∈ L', G'.mulVec x ∈ L) :
    TaylorLogMetric.detId D L₀ L' = Submodule.span (𝓞 D.host.E) {G.det} * TaylorLogMetric.detId D L₀ L := by
  unfold TaylorLogMetric.detId
  rw [Submodule.span_mul_span, Set.singleton_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨(G' * A).det, ⟨_, fun v hv => ?_, rfl⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec]
      exact h' _ (hA v hv)
    · show G.det * (G' * A).det = A.det
      rw [← Matrix.det_mul, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨G * A, fun v hv => ?_, (Matrix.det_mul _ _).symm⟩
    rw [← Matrix.mulVec_mulVec]
    exact h _ (hA v hv)

theorem norm_one_span (D : D7) (z : D.host.E) (hz : z * D.host.conj z = 1) :
    TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {z}) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← hst] at hz
  have key : ∀ w x : D.host.E, x ∈ Submodule.span (𝓞 D.host.E) {w} → star x ∈ Submodule.span (𝓞 D.host.E) {star w} := by
    intro w x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine Submodule.mem_span_singleton.2 ⟨⟨star (r : D.host.E), r.2.map (starRingEnd D.host.E).toIntAlgHom⟩, ?_⟩
    exact (star_mul' (r : D.host.E) w).symm
  refine ⟨Submodule.span (𝓞 D.host.E) {star z}, fun x => ?_, ?_⟩
  · rw [← hst]
    exact ⟨fun h => by simpa using key _ _ h, fun h => by simpa using key _ _ h⟩
  · rw [Submodule.span_mul_span, Set.singleton_mul_singleton, hz, Submodule.one_eq_span]

theorem star_det_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    star ((LinearEquiv.det γ.1 : Eˣ) : E) * ((LinearEquiv.det γ.1 : Eˣ) : E) = 1 := by
  set M : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) with hM
  have hd : ((LinearEquiv.det γ.1 : Eˣ) : E) = M.det := by
    rw [LinearEquiv.coe_det, hM, LinearMap.det_toMatrix']
  have hu : M.conjTranspose * M = 1 := by
    ext i j
    have h := γ.2 (Pi.single i 1) (Pi.single j 1)
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hM, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    refine h.trans ?_
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
  rw [hd, ← Matrix.det_conjTranspose, ← Matrix.det_mul, hu, Matrix.det_one]

theorem matT_eq {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n : ℕ}
    (x : HomE E n n) : matT e n n x = (e : E →+* E').mapMatrix (LinearMap.toMatrix' x) := rfl

variable {D : D7} {X : Fields} (s : Seam D X)

theorem detId_lat_gmap {n : ℕ} (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D L₀ (s.lat (gmap g N)) =
      Submodule.span (𝓞 D.host.E) {s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)} * TaylorLogMetric.detId D L₀ (s.lat N) := by
  have hd : s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) = (matT s.iE n n g.toLinearMap).det := by
    rw [matT_eq, ← RingHom.map_det, LinearMap.det_toMatrix', LinearEquiv.coe_det]
    rfl
  rw [hd]
  refine detId_image D L₀ _ _ _ (matT s.iE n n g.symm.toLinearMap) ?_
    ((matT_carries s.iE N (gmap g N) _).2 fun y hy => ⟨y, hy, rfl⟩) ((matT_carries s.iE (gmap g N) N _).2 ?_)
  · rw [matT_eq, matT_eq, ← map_mul, ← LinearMap.toMatrix'_comp]
    simp
  · rintro _ ⟨y, hy, rfl⟩
    simpa using hy

theorem chi_lat_gmap (hs : s.Ok) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {n : ℕ} (γ : UF X.E n)
    {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat (gmap γ.1 N))) =
      (∏ τ, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h1 : star (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) * s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 := by
    rw [hst, ← hs.2, ← map_mul, star_det_mul, map_one]
  let z : unitary D.host.E := ⟨s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E), h1, by rw [mul_comm]; exact h1⟩
  have hL := sd_lat s hs hN
  rw [detId_lat_gmap, hχ.1 _ _ (norm_one_span D z.1 (by rw [← hst, mul_comm]; exact h1))
    (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (GlobalTheory.ThetaMove.Moved.sd_stdL D n) hL hL).1, hχ.2 z,
    Finset.prod_inv_distrib, ← s.iT.prod_comp]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (hs.1 τ _).symm

theorem chiLaw_ambOf : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → TaylorLogMetric.IsChi D χ → (ambOf s B χ cD).ChiLaw a b := by
  intro D X s cc δ B χ cD a b hs hχ γ γ' N N' hN hN'
  change Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) =
    (∏ τ, X.embC s.σ₀ τ _) ^ _ * (∏ τ, X.embC s.σ₀ τ _) ^ _ * Base.chiFac χ a b (s.lat N) (s.lat N')
  unfold Base.chiFac
  rw [chi_lat_gmap s hs hχ γ hN, chi_lat_gmap s hs hχ γ' hN', mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg]
  ring

end GlobalTheory.Mem.Col2.ChiFacLaw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockBasis

section Mat

variable {m n : ℕ}

theorem unitMap_mul (B u : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j =
      ∑ a, ∑ b, (k a i * u⁻¹ j b) • Formalism.IndefR.Datum.unitMap B B' a b := by
  have e : k * Matrix.single i j (1 : ℂ) * u⁻¹ = ∑ a, ∑ b, (k a i * u⁻¹ j b) • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.matrix_eq_sum_single (k * Matrix.single i j (1 : ℂ) * u⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc]
    · simp
  unfold Formalism.IndefR.Datum.unitMap
  rw [Matrix.mul_inv_rev]
  calc B' * k * Matrix.single i j (1 : ℂ) * (u⁻¹ * B⁻¹) = B' * (k * Matrix.single i j (1 : ℂ) * u⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e]
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]


open scoped ComplexOrder in
theorem isCartanInv_one {G B : Matrix (Fin n) (Fin n) ℂ} (hB : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * 1 * B⁻¹ := by
    rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  refine ⟨Matrix.one_mul _, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_mul_same Matrix.PosDef.one ?_
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))

end Mat

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (s : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
include hψ hθ hf

theorem aPlus_add_dir (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z + z') f =
      Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f + Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z' f := by
  have e : cplxO 1 s (z + z') = cplxO 1 s z + cplxO 1 s z' := by
    simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  simp only [GlobalTheory.FockSubst.aPlus_eq, e, fun z => (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem dRho_smul_dir (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (c • z) f =
      (c.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ z f + (c.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (Complex.I • z) f := by
  have e : c • z = (c.re : ℂ) • z + (c.im : ℂ) • (Complex.I • z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.1, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1,
    (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_smul_dir (e : Bool) (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (hz : cplxO 1 s z = (Complex.I * if e then 1 else -1) • z) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (c • z) f =
      (if e then c else star c) • Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f := by
  have e1 : cplxO 1 s (c • z) = c • cplxO 1 s z := by
    simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_comm c]
  simp only [GlobalTheory.FockSubst.aPlus_eq]
  rw [e1, hz, smul_smul, dRho_smul_dir hψ hθ τ hf c, dRho_smul_dir hψ hθ τ hf (c * _),
    dRho_smul_dir hψ hθ τ hf (Complex.I * _)]
  generalize ((fockScale D τ : ℝ) : ℂ)⁻¹ = r
  cases e
  · match_scalars <;> apply Complex.ext <;> simp <;> ring
  · match_scalars <;> apply Complex.ext <;> simp <;> ring

theorem aPlus_sum_dir {ι : Type} (t : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (∑ i ∈ t, z i) f =
      ∑ i ∈ t, Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z i) f := by
  induction t using Finset.induction_on with
  | empty =>
    have h := aPlus_add_dir hψ hθ τ s hf 0 0
    rw [add_zero] at h
    rw [Finset.sum_empty, Finset.sum_empty]
    exact left_eq_add.1 h
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, aPlus_add_dir hψ hθ τ s hf, ih]

theorem aPlus_unitMap_mul {ε : Fin T.rank → Bool} {B' k : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (ht : s * B' = B' * diagonal fun a => if ε a then (1 : ℂ) else -1) (hk : k ∈ Formalism.REAL.Kset ε)
    (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) {u : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) (i : Fin T.rank) (j : Fin S.rank) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j) f =
      ∑ a, ∑ b, (if ε i = true then k a i * u⁻¹ j b else k⁻¹ i a * u b j) •
        Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap B B' a b) f := by
  rw [unitMap_mul, aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [aPlus_smul_dir hψ hθ τ _ hf (ε a) _ _ (GlobalTheory.FockIndep.cplxO_unitMap ht a b)]
  refine congrArg (· • _) ?_
  have hk1 : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)
  have hu1 : u⁻¹ = uᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hu)
  have hc := congrFun (congrFun hk.2 a) i
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  rw [hk1, hu1, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, star_mul', star_star]
  by_cases h : ε a = ε i
  · rw [h]
  · have h0 : k a i = 0 := by
      cases h1 : ε a <;> cases h2 : ε i <;> simp only [h1, h2, not_true, if_true, Bool.false_eq_true, if_false] at h hc
      · linear_combination hc / 2
      · linear_combination -hc / 2
    simp [h0]

omit hψ hθ hf

section Generic

variable {ι κ μ X : Type} [Fintype κ] [Fintype μ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {g : X → ℂ} (c : ι → κ → μ → ℂ) (e : ι → κ → μ → ι)
    (hm : ∀ Q, P (pureTensorL A g Q))
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (hA : ∀ v h, P h → A' v h = ∑ a, ∑ b, c v a b • A (e v a b) h) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' g Q = pureTensorL A g
      (MvPolynomial.aeval (fun v => ∑ a, ∑ b, MvPolynomial.C (c v a b) * MvPolynomial.X (e v a b)) Q) := by
  have hC : ∀ (A : ι → (X → ℂ) → (X → ℂ)) a, pureTensorL A g (MvPolynomial.C a) = a • g := fun A a => by
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, GlobalTheory.FockIndep.pure_one]
  induction Q using MvPolynomial.induction_on with
  | C a => rw [hC, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hC]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, hX', hp, map_mul, MvPolynomial.aeval_X, hA _ _ (hm _)]

    simp only [Finset.sum_mul, map_sum, mul_assoc]
    simp only [MvPolynomial.C_mul', map_smul, smul_mul_assoc, hX]

end Generic

theorem pureTensorO_basis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (k : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∀ f, IsThetaFunO ψ S T f → ∀ P : PolF D T.rank S.rank, pureTensorO ψ θ S T (fun _ => 1) (cart M) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fsub M.ε k u P) := by
  intro D ψ θ S T Sp M BS hψ hθ hB k u hk hu f hf P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  have hfr := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hfr τ)]
    rfl
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ B B' v g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v g) :=
    fun _ _ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ B B' v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f Q) := fun B B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm (hth B B') ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hA : ∀ v g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) v g =
      ∑ a, ∑ b, (if M.ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
        else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) •
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (v.1, a, b) g := fun v g hg => by
    unfold aPlusAll
    exact aPlus_unitMap_mul hψ hθ v.1 _ hg (ht v.1) (hk v.1) _ (hu v.1) v.2.1 v.2.2
  have key := pure_subst (P := IsThetaFunO ψ S T) _ _
    (GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm (hth _ _) hf) (hX _ _) (hX _ _) hA P
  unfold pureTensorO fsub
  exact key

end GlobalTheory.FockBasis
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.eventually_block_val_at_and_exists_inv_eq : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ) (μ η : HChar E), AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r → ∀ (μH ηH : Formalism.L2.NC.HC E), μH.χ = (μ : Ideles E →* ℂˣ) → ηH.χ = (η : Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite, (μH * ηH⁻¹).At v ((((block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (normV v) : ℂ) ^ (-(r : ℤ))) ∧ ∃ y : K, ε y = (((block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  first | exact @GlobalTheory.BlockVal.block_val_ae | exact GlobalTheory.BlockVal.block_val_ae | (intros; apply GlobalTheory.BlockVal.block_val_ae <;> assumption)
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (R : MvPolynomial (ι × ℕ) ℝ), R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n → (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.CuspDecay

theorem bounded_of_smooth_unifModGrowth : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ φ → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsUnifModGrowth V θ φ → IsCuspFun V φ → ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  intro hP D θ V hθ φ ha hs hg hc
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hs' := (GlobalTheory.SmoothForms.smooth_iff R φ).1 hs
  exact (hP D θ hθ V _ (GlobalTheory.SmoothForms.isExpFam_expInf R) φ ha hs'
    ((GlobalTheory.SmoothForms.growth_iff hθ R ha hs').1 hg) hc).bounded

end GlobalTheory.CuspDecay
end
