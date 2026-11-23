module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

section Ring

open scoped Pointwise

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A]

theorem map_mul_unit (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (u : Aˣ) :
    μ.map (fun x => (u : A) * x) = (distribHaarChar A u)⁻¹ • μ := by
  have hm : Measurable fun x : A => (u : A) * x := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun x : A => (u : A) * x) ⁻¹' B = u⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, map_inv]
  rfl

theorem exists_pos_finite (μ : Measure A) [μ.IsAddHaarMeasure] :
    ∃ K : Set A, μ K ≠ 0 ∧ μ K ≠ ∞ := by
  obtain ⟨K, hK, hn⟩ := exists_compact_mem_nhds (0 : A)
  refine ⟨K, ?_, hK.measure_lt_top.ne⟩
  exact (Measure.measure_pos_of_mem_nhds μ hn).ne'

theorem smul_inj (μ : Measure A) [μ.IsAddHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have e := congrArg (fun m : Measure A => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem char_map (s : A ≃+* A) (hs : Continuous s) (hs' : Continuous s.symm) (u : Aˣ) :
    distribHaarChar A (Units.map (s : A →* A) u) = distribHaarChar A u := by
  let H : A ≃ₜ A := ⟨s.toEquiv, hs, hs'⟩
  let μ : Measure A := Measure.addHaar
  have : (μ.map H).IsAddHaarMeasure := s.toAddEquiv.isAddHaarMeasure_map μ hs hs'
  have : (μ.map H).Regular := Measure.Regular.map H
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have hap : ∀ S : Set A, (μ.map H) S = μ (H ⁻¹' S) := fun S =>
    H.toMeasurableEquiv.map_apply S
  have hpre : H ⁻¹' (H '' K) = K := H.injective.preimage_image K
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.map H) (s := H '' K)
    (by rwa [hap, hpre]) (by rwa [hap, hpre]) ?_
  rw [hap, hap, hpre, distribHaarChar_mul]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, hy⟩
    refine ⟨k, hk, H.injective ?_⟩
    rw [← hy]
    simp [H, Units.smul_def]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨H k, ⟨k, hk, rfl⟩, ?_⟩
    simp [H, Units.smul_def]

end Ring

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

theorem coordK_map_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (c : Fv F v ⊗[F] E) (t : Fv F v) (w : ℕ), IsUnit c → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = ((qv v : ℝ) ^ w)⁻¹ → (coordK (Fv F v) b lam).map (fun x => c * x) = (qv v ^ w) • coordK (Fv F v) b lam := by
  intro F E _ _ _ _ _ σ hσ d b v lam hlam c t w hc ht hnorm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, hsc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set μ := coordK (Fv F v) b lam with hμ
  haveI : μ.Regular := inferInstance
  have hss : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, sigma_sigma σ hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  let s : (Fv F v ⊗[F] E) ≃+* (Fv F v ⊗[F] E) :=
    { toFun := sigR (Fv F v) σ, invFun := sigR (Fv F v) σ, left_inv := hss, right_inv := hss,
      map_mul' := map_mul _, map_add' := map_add _ }
  let u : (Fv F v ⊗[F] E)ˣ := hc.unit
  have hu : (u : Fv F v ⊗[F] E) = c := hc.unit_spec
  have hchar := char_map s hsc hsc u
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hqv : (qv v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by simp [qv]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero, hqv] at hnorm
    exact inv_ne_zero (pow_ne_zero w hq) hnorm.symm
  have hk : ‖t‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ w := by
    rw [hnorm, hqv, inv_pow]
  have h1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam t ht0 w hk
  have h2 := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam t ht0 _ h1
  have h3 := map_mul_unit μ (Units.map (s : _ →* _) u * u)
  have hval : ((Units.map (s : _ →* _) u * u : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t := by
    rw [ht, ← hu]
    rfl
  rw [hval, h2, map_mul, hchar] at h3
  have h4 := smul_inj μ h3
  have h5 : (distribHaarChar (Fv F v ⊗[F] E) u)⁻¹ = qv v ^ w := by
    refine (pow_left_inj₀ zero_le' zero_le' two_ne_zero).1 ?_
    rw [inv_pow, pow_two]
    exact h4.symm
  rw [← h5, ← map_mul_unit μ u, hu]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal Matrix

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramNear (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (U : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ u ∈ U, (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X = (u : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def gramTest (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (ρ : HermR R σ n → ℝ)
    (X : Fin n → Fin M → R ⊗[F] E) : ℝ := by
  classical
  exact if h : (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X ∈ HermR R σ n then ρ ⟨_, h⟩ else 0

end Loc

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxF {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxF A).indicator (fun _ => (1 : ℂ)) (projFin X)

def intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (AF F) σ n) :=
  {B | ∀ v, v ∉ S → projV v (projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) ∈ latV (M := n) (n := n) b v}

def coefS (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ B, (intH σ b S).indicator (fun _ => (1 : ℂ)) B *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ B * ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))) ∂db

end Adelic

end GlobalTheory.CompanionTheory.WhitFree
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

namespace GlobalTheory.CompanionTheory.SwUnf

open PositivityTheory.GramSchwartzFunctions.EC

section Blocks

variable {K : Type} [Field K] {n : ℕ}

theorem lowerC_apply' (M : Matrix (Fin (n + n)) (Fin (n + n)) K) (i j : Fin n) :
    lowerC M i j = M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) := rfl

theorem lowerC_siegel_mul {y : Matrix (Fin (n + n)) (Fin (n + n)) K} (hy : IsSiegelP y)
    (W : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    lowerC (y * W) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD y * lowerC W := by
  have hy' : ∀ i j : Fin n, y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := hy
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hy', zero_mul, Finset.sum_const_zero, zero_add, GlobalTheory.CompanionTheory.RatPtsUnn.blkD]

theorem lowerC_mul_unip (X : Matrix (Fin (n + n)) (Fin (n + n)) K) (b : Matrix (Fin n) (Fin n) K) :
    lowerC (X * blk4 1 b 0 1) = lowerC X := by
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, Matrix.one_apply, Matrix.zero_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]

end Blocks

variable {D : D7} {n : ℕ}

private theorem incA_injective' (D : D7) : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing D.host.F ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))
  haveI : Nontrivial (AF D.host.F ⊗[D.host.F] D.host.E) :=
    Function.Injective.nontrivial
      (Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective)
  exact (incA D).injective

theorem isUnit_det_of_mat (x : GF D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (h : mat (x : G D n) = g.map (incA D)) : IsUnit g.det := by
  obtain ⟨g', hg', -, hg'm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 (x : G D n) x.2
  have hgg : g = g' := Matrix.map_injective (incA_injective' D) (h.symm.trans hg'm)
  rw [hgg]
  exact hg'

private theorem mat_mul_eq_ite_of_hasMult {D : D7} {n : ℕ} (a b : G D n) : mat (a * b) = mat a * mat b := by
  simp only [mat, map_mul, Units.val_mul]

theorem cosetCell_rmulEquiv : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  intro D n q γ b h
  set q' := rmulEquiv (P D n) (GF D n) γ q with hq'
  have e3 : GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) :=
    calc GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = q' := Quotient.out_eq q'
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ q := rfl
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ (GlobalTheory.AutomorphicL2Unitary.mk _ q.out) :=
        congrArg (GlobalTheory.AutomorphicL2Unitary.rmul _ γ) (Quotient.out_eq q).symm
      _ = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) := GlobalTheory.AutomorphicL2Unitary.rmul_mk _ _
  obtain ⟨p, hp⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.mp e3
  have hp' : ((p : GF D n) : G D n) * (q'.out : G D n) = (q.out : G D n) * (γ : G D n) :=
    congrArg Subtype.val hp
  have hb : blk4 1 (b.map (incA D)) 0 1 = (blk4 1 b 0 1).map (incA D) := by
    have h1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := (incA D).mapMatrix.map_one
    have h0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := (incA D).mapMatrix.map_zero
    unfold blk4
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, h1, h0]
  have hm := congrArg mat hp'
  rw [mat_mul_eq_ite_of_hasMult, mat_mul_eq_ite_of_hasMult, h, mat_ratOf, mat_ratOf, mat_ratOf, hb, ← Matrix.map_mul,
    ← Matrix.map_mul] at hm
  have hm2 : ratOf (p : GF D n) * ratOf q'.out = ratOf q.out * blk4 1 b 0 1 :=
    Matrix.map_injective (incA_injective' D) hm
  have hpP : ((p : GF D n) : G D n) ∈ P D n := Subgroup.mem_subgroupOf.mp p.2
  have hS : IsSiegelP (ratOf (p : GF D n)) :=
    (GlobalTheory.CompanionTheory.RatPtsUnn.clause3 _ (p : GF D n).2 _ (mat_ratOf (p : GF D n))).mp hpP
  have hC : lowerC (ratOf q.out) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) * lowerC (ratOf q'.out) := by
    rw [← lowerC_mul_unip (ratOf q.out) b, ← hm2, lowerC_siegel_mul hS]
  have hU : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n))).det := by
    have hd := isUnit_det_of_mat (p : GF D n) (mat_ratOf (p : GF D n))
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero _ hS] at hd
    exact isUnit_of_mul_isUnit_right hd
  have hinj : ∀ w, GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul _ hU, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero]
  simp only [cosetCell, cellKer]
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [hC, ← Matrix.mulVec_mulVec]
  constructor
  · intro h0
    rw [h0, Matrix.mulVec_zero]
  · intro h0
    exact hinj _ h0

end GlobalTheory.CompanionTheory.SwUnf
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Period

variable {D : D7}

theorem rat_sub' {m n : ℕ} (p p₀ : Matrix (Fin m) (Fin n) D.host.E) :
    (rat (p - p₀) : Mx D m n) = rat p - rat p₀ := by
  ext i j
  simp [rat]

theorem psi_inner_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q q₀ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    ψ (trA (Matrix.trace (inner V (rat q) (rat q₀)))) = 1 := by
  have h : (inner V (rat q) (rat q₀) : Mx D s s) = rat (qᴴ * (V.gram * q₀)) := by
    change (adj (rat q) ⬝ (gA V ⬝ rat q₀) : Mx D s s) = rat (qᴴ * (V.gram * q₀))
    rw [rat_mul, rat_mul, rat_conjTranspose, gA]
  have ht : ∀ M : Matrix (Fin s) (Fin s) D.host.E,
      Matrix.trace (rat M : Mx D s s) = incA D (Matrix.trace M) := fun M => by

    simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [h, ht, GlobalTheory.CompanionTheory.ThetaInv.trA_incA]
  exact hψ.2.2.1 _

theorem inner_add_right' (V : HSp D) {s : ℕ} (x y z : Mx D V.rank s) :
    (inner V x (y + z) : Mx D s s) = inner V x y + inner V x z := by
  change (adj x ⬝ (gA V ⬝ (y + z)) : Mx D s s) = adj x ⬝ (gA V ⬝ y) + adj x ⬝ (gA V ⬝ z)
  simp [Matrix.mul_add]

theorem trA_add' (x y : AE D) : trA (x + y) = trA x + trA y := by
  simp [trA]

theorem term_shift {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (Φ : Mx D V.rank (r + s) → ℂ)
    (p p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) :
    cellTerm ψ V b a Φ p q (y₁ + rat p₀) (y₂ + rat q₀) = cellTerm ψ V b a Φ (p - p₀) q y₁ y₂ := by
  have e₁ : y₁ + rat p₀ - rat p = y₁ - rat (p - p₀) := by rw [rat_sub']; abel
  have e₂ : rat p - (y₁ + rat p₀) = rat (p - p₀) - y₁ := by rw [rat_sub']; abel
  have e₃ : ψ (trA (Matrix.trace (inner V (rat q) (y₂ + rat q₀)))) =
      ψ (trA (Matrix.trace (inner V (rat q) y₂))) := by
    rw [inner_add_right', Matrix.trace_add, trA_add', AddChar.map_add_eq_mul, psi_inner_rat hψ, mul_one]
  unfold cellTerm
  rw [e₁, e₂, e₃]

theorem tsum_cellTerm_add_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s),
    ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 (y₁ + rat p₀) (y₂ + rat q₀) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂ := by
  intro D ψ hψ V r s b a Φ p₀ q₀ y₁ y₂
  simp only [term_shift hψ]
  exact (Equiv.prodCongr (Equiv.subRight p₀) (Equiv.refl _)).tsum_eq
    (fun pq => cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂)

end GlobalTheory.CompanionTheory.EisUnfold.Period

end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.CompanionTheory.MixZ

theorem codimOne_holds : CodimOne := by
  intro X _ p D hD z hz
  let C : Closeds X := ⟨closure {z}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  haveI : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal C
  have hrange : Set.range I.subschemeι = closure {z} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hemb : Topology.IsEmbedding I.subschemeι := I.subschemeι.isClosedEmbedding.isEmbedding
  haveI : IrreducibleSpace I.subscheme := by
    have hs : IsIrreducible (Set.range I.subschemeι) := by
      rw [hrange]; exact isIrreducible_singleton.closure
    haveI := Subtype.irreducibleSpace hs
    have h2 := (IrreducibleSpace.isIrreducible_univ (Set.range I.subschemeι)).image
      hemb.toHomeomorph.symm hemb.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ_of_surjective hemb.toHomeomorph.symm.surjective] at h2
    exact (irreducibleSpace_def _).2 h2
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hgen : I.subschemeι (genericPoint I.subscheme) = z := by
    have h1 := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
    rw [Set.image_univ, hrange, closure_closure] at h1
    exact h1.eq isGenericPoint_closure
  have key := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one ℤ X p D hD I.subscheme I.subschemeι
    (by rw [hgen]; exact hz)
  calc topologicalKrullDim (closure ({z} : Set X))
      = topologicalKrullDim I.subscheme := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb hrange
    _ = D := key

end GlobalTheory.CompanionTheory.MixZ
end
