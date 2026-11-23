module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle051
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle723
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle724
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle536
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle539
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle726
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.LocalFourierHaar
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat

theorem coordW_latV_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ v, coordW (Fv F v) b (lam v) 1 1 (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam v
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := (hlam v).1
  have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Fv F v) b) :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mv := GlobalTheory.CompanionTheory.SW.WBox.map_coordW (Fv F v) hK (lam v) 1 1
  have hset : (latV b v : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) =
      (GlobalTheory.CompanionTheory.SW.WBox.eW (Fv F v) hK 1 1) ⁻¹'
        Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mv.measure_preimage_equiv, Measure.pi_pi]
  simp [(hlam v).2]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelTheta

def colMajorant {D : D7} (θ : InfFam D) (m : ℕ) (L : Set (Matrix (Fin m) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)))
    (N : ℕ) (v : Mx D m 1) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ v i 0‖) ^ N)⁻¹ *
    Set.indicator L (fun _ => (1 : ℝ)) (v.map (finPart D)))

def pureT {D : D7} (θ : InfFam D) {m n : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (x : Mx D m n) : ℂ :=
  f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))

theorem pure_le_colMajorant (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact L ∧ ∀ N : ℕ, ∃ C : ℝ,
      ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
        ‖pureT θ f g (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ ≤
          ENNReal.ofReal C * ∏ j : Fin n, colMajorant θ V.rank L N (fun i (_ : Fin 1) => x i j) := by
  obtain ⟨C0, L, hL, h0⟩ := GlobalTheory.T.theta_series_siegel_bound D θ hθ V n f g hg C₁ hC₁ 0
  refine ⟨L, hL, fun N => ?_⟩
  obtain ⟨CN, LN, -, hN⟩ := GlobalTheory.T.theta_series_siegel_bound D θ hθ V n f g hg C₁ hC₁ N
  refine ⟨CN, fun y hy x => ?_⟩
  by_cases hall : ∀ j : Fin n, (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) ∈ L
  · refine (hN y hy x).trans ?_
    gcongr with j _
    unfold colMajorant
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) = 1 :=
      Set.indicator_of_mem (hall j) _
    refine le_trans ?_ (le_of_eq h1.symm)
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) _ |>.trans le_rfl
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hz : ‖pureT θ f g (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ = 0 := by
      refine le_antisymm ((h0 y hy x).trans (le_of_eq ?_)) bot_le
      rw [Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
      rw [Set.indicator_of_notMem hj, mul_zero, ENNReal.ofReal_zero]
    rw [hz]
    exact bot_le

theorem absTheta_pure_le (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) {c : ℝ} (hc : 0 < c)
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ C₁, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a →
      absTheta V (pureT θ f g) (a * y) ≤
        ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  obtain ⟨L, hL, hmaj⟩ := pure_le_colMajorant D θ hθ V n f g hg C₁ hC₁
  obtain ⟨N₀, hcount⟩ := GlobalTheory.T.theta_rapid_decay_siegel_set D θ hθ V Xf Yf hW hc L hL
  obtain ⟨C', hC'⟩ := hcount N₀ le_rfl
  obtain ⟨C, hC⟩ := hmaj N₀
  refine ⟨max C 0 * max C' 0 ^ n, by positivity, fun y hy t ht a ha => ?_⟩
  have h1 := GlobalTheory.CompanionTheory.ColProd.absTheta_le_pow_of_colProd D V (pureT θ f g) (colMajorant θ V.rank L N₀)
    (ENNReal.ofReal C) y (hC y hy) a
  have hP : 0 ≤ ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have h2 : ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, colMajorant θ V.rank L N₀ (invPt V a ξ) ≤
      ENNReal.ofReal (max C' 0 * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) :=
    (hC' t ht a ha).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hP))
  have hpow : (∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) ^ n =
      ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul]
    congr 1
    ring
  calc absTheta V (pureT θ f g) (a * y)
      ≤ ENNReal.ofReal C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, colMajorant θ V.rank L N₀ (invPt V a ξ)) ^ n := h1
    _ ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal (max C' 0 * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) ^ n := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (max C 0 * max C' 0 ^ n * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_pow (mul_nonneg (le_max_right _ _) hP),
          ← ENNReal.ofReal_mul (le_max_right _ _), mul_pow, hpow, mul_assoc]

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Φ : Mx D V.rank n → ℂ), Φ ∈ schwartzA θ V.rank n → ∀ {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (Ω C₀ : Set (GA D V)) (K : Subgroup (GA D V)) (c : ℝ), IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GA D V)) → 0 < c → (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → a⁻¹ * p * a ∈ C₀) → ∃ C : ℝ, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ k ∈ K, absTheta V Φ (p * a * k) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hsub
  have hC₁ : IsCompact (C₀ * (K : Set (GA D V))) := hC₀.mul hK
  obtain ⟨-, m, f, g, hg, hdom⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ V.rank n Φ hΦ
  have key := fun i => absTheta_pure_le D θ hθ V n (f i) (g i) (hg i) Xf Yf hW hc _ hC₁
  choose Ci hCi0 hCi using key
  refine ⟨∑ i, Ci i, fun p hp t ht a ha k hk => ?_⟩
  have hy : a⁻¹ * p * a * k ∈ C₀ * (K : Set (GA D V)) := Set.mul_mem_mul (hsub p hp t ht a ha) hk
  have hsplit : p * a * k = a * (a⁻¹ * p * a * k) := by group
  have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  rw [hsplit]
  calc absTheta V Φ (a * (a⁻¹ * p * a * k))
      ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ∑ i, ‖pureT θ (f i) (g i) (invPt V (a * (a⁻¹ * p * a * k)) ξ)‖ₑ :=
        ENNReal.tsum_le_tsum fun ξ => hdom _
    _ = ∑ i, absTheta V (pureT θ (f i) (g i)) (a * (a⁻¹ * p * a * k)) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ i, ENNReal.ofReal (Ci i * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        Finset.sum_le_sum fun i _ => hCi i _ hy t ht a ha
    _ = ENNReal.ofReal ((∑ i, Ci i) * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hCi0 i) hP]

end GlobalTheory.CompanionTheory.SiegelTheta
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem hU_thU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig (Jst D n) v) :
    hU D n v τ (thU D n v τ g) = GlobalTheory.LocIntw.hgtUp _ D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
      (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) g := by
  unfold hU
  rw [Function.leftInverse_invFun (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).1 g]

theorem hU_isHgt (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    IsHgt (O := Ov D v) (nvL D v) (hU D n v τ) := by
  intro a d b κ
  obtain ⟨y, hy⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (pM a d b)
  obtain ⟨k, hk⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL κ)
  have hkK : k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ k).2 ⟨κ, hk.symm⟩
  obtain ⟨hyP, hab⟩ := GlobalTheory.T.modulus_upper_parabolic_local D n v τ y a d b hy
  rw [← hy, ← hk, ← map_mul, hU_thU]
  exact (GlobalTheory.LocIntw.hgtUp_mul (GlobalTheory.LocIntw.isIwasawaUp_fin D n v) ⟨y, hyP⟩ hkK).trans hab

theorem rank_beta0 {k : Type} [Field k] {n r t : ℕ} (h : r + t = n) :
    (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : k) else 0).rank = r := by
  classical
  rw [Matrix.rank_diagonal]
  have hr : r ≤ n := by omega
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  exact Fintype.card_fin_lt_of_le hr

theorem psiV_lift (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) (w : (Lv D v)ˣ) (ψ₀ : AddChar (kv D v) ℂ)
    (h : ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) =
      ψ₀ (IsLocalRing.residue (Ov D v) c))
    (ℓ : kv D v → Ov D v) (hℓ : ∀ a, IsLocalRing.residue (Ov D v) (ℓ a) = a) {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) (kv D v)) (T₀ : Matrix (Fin n) (Fin n) (Ov D v)) :
    psiV D.host.F ψ v (Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))) =
      ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
  have key : Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))
      = ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, mul_assoc]
  have key2 : Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v))) =
      IsLocalRing.residue (Ov D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, hℓ]
  rw [key, h, key2]

theorem split_place_rank_cut_of_local_computation : JpCondition → SplitPlaceRankCutEigenvalue := by
  intro hA D n r t hrt hr ψ hψ nb hnb v hgood τ
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ov D v)
  have hϖ0 : algebraMap (Ov D v) (Lv D v) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (Ov D v) (Lv D v))]
    exact hϖ.ne_zero
  obtain ⟨w, hw⟩ : ∃ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ := ⟨Units.mk0 _ hϖ0, rfl⟩
  obtain ⟨ψ₀, hψ₀, hψ₀c⟩ := GlobalTheory.T.exists_residue_character_of_conductor D ψ v hgood ϖ hϖ w hw
  have hok := GlobalTheory.T.normalized_valuation_uniformizer D v ϖ hϖ w hw
  choose ℓ hℓ using fun a : kv D v => IsLocalRing.residue_surjective (R := Ov D v) a
  have hβ : (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0).rank = r := rank_beta0 hrt
  obtain ⟨ρ, hρ, hρs, hρm⟩ := GlobalTheory.T.surjective_reduction_maximal_compact D n v τ
  obtain ⟨c, hcd, hct, hcint⟩ := hA (Ov D v) (Lv D v) n r t hrt hr ψ₀ hψ₀ _ hβ
  choose f hinf hoff hfX _ using fun Y : Matrix (Fin n) (Fin n) (kv D v) =>
    GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ (((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y)
  have hfinj : Function.Injective f := by
    intro Y Y' hYY
    have h1 : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y =
        ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y' := by
      rw [← hfX Y, ← hfX Y', hYY]
    funext i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply] at h2
    have h3 := IsFractionRing.injective (Ov D v) (Lv D v) (mul_left_cancel₀ (Units.ne_zero _) h2)
    rw [← hℓ (Y i j), ← hℓ (Y' i j), h3]
  have hsinf : ∀ x ∈ Finset.univ.image f, ∀ (w' : NumberField.InfinitePlace D.host.F) (i j : Fin n),
      (GlobalTheory.AdelicU.compInf D.host.F D.host.E w') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hinf Y
  have hsoff : ∀ x ∈ Finset.univ.image f, ∀ (v' : Pl D), v' ≠ v → ∀ (i j : Fin n),
      (PositivityTheory.Rg.Rsw.L.cv D v') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hoff Y
  refine ⟨⟨Finset.univ.image f, fun x => coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
    (Function.invFun f x), hsinf, hsoff⟩, c, ?_, hcd, hct, ?_⟩
  · intro β' hβ' hint
    have hTint : ∀ i j, (β'.1.map τ) i j ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v := by
      apply GlobalTheory.T.integral_of_character_trivial_on_lattice D ψ v hgood n
      intro X hX
      obtain ⟨x, hinf', hoff', htx, hint'⟩ := GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ X
      rw [← htx, ← GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ x hinf' hoff' β']
      apply hint
      unfold PositivityTheory.Rg.Rsw.L.IntAt
      exact ⟨hinf', hoff', hint' hX⟩
    let T₀ : Matrix (Fin n) (Fin n) (Ov D v) := fun i j => ⟨(β'.1.map τ) i j, hTint i j⟩
    have hT : (β'.1.map τ : Matrix (Fin n) (Fin n) (Lv D v)) = T₀.map (algebraMap (Ov D v) (Lv D v)) := rfl
    have hne : T₀.map (IsLocalRing.residue (Ov D v)) ≠
        Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0 := by
      intro heq
      have h1 := GlobalTheory.T.rank_residue_le_rank_generic (Ov D v) (Lv D v) n T₀
      have h2 := GlobalTheory.Core.Rk.rank_map_field (τ : D.host.E →+* Fv D.host.F v) β'.1
      rw [heq, hβ] at h1
      have h3 : (T₀.map (algebraMap (Ov D v) (Lv D v))).rank = (β'.1.map τ).rank := by rw [← hT]
      exact absurd (h1.trans (h3.trans h2).le) (not_le.2 hβ')
    have hpch : ∀ Y, PositivityTheory.Rg.Rsw.L.pch ψ (f Y).1 (GlobalTheory.MixModel.rat β'.1) =
        ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
      intro Y
      rw [GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ (f Y) (hinf Y) (hoff Y) β', hfX Y, hT]
      exact psiV_lift D ψ v w ψ₀ hψ₀c ℓ hℓ Y T₀
    show ∑ x ∈ Finset.univ.image f, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
      (Function.invFun f x) * PositivityTheory.Rg.Rsw.L.pch ψ x.1 (GlobalTheory.MixModel.rat β'.1) = 0
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    calc _ = ∑ Y, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0) Y *
          ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
            refine Finset.sum_congr rfl fun Y _ => ?_
            rw [Function.leftInverse_invFun hfinj Y, hpch Y]
      _ = 0 := GlobalTheory.T.sum_character_orthogonality_matrices (kv D v) n ψ₀ hψ₀ _ _ hne
  · intro νv hH hP z
    have e1 : ∀ g, GlobalTheory.CompanionTheory.Jp.sphV D n v z g =
        GlobalTheory.Doubling.npow (hU D n v τ (thU D n v τ g)) (z + (n : ℂ) / 2) := by
      intro g
      rw [hU_thU]
      rfl
    rw [← hcint ϖ hϖ w hw ℓ hℓ (nvL D v) hok (hU D n v τ) (hU_isHgt D n v τ) _ νv ρ hρs (hρm ϖ hϖ) z]
    dsimp only
    congr 1
    funext k
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Function.leftInverse_invFun hfinj Y, e1, map_mul, map_mul, hρ k, GlobalTheory.T.local_image_of_unipotent_element D n nb hnb v τ (f Y), hfX Y]
    rfl

end GlobalTheory.CompanionTheory.Jp

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi.Test

theorem psiA_isTest : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiA S g a v) ∧ HasCompactSupport (psiA S g a v) := by
  intro F _ _ S g a hg v
  have hu : (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    have h : ((a : AF F) * ((a⁻¹ : (AF F)ˣ) : AF F)).2 v = (1 : AF F).2 v := by rw [a.mul_inv]
    exact h
  have ha : (a : AF F).2 v ≠ 0 := left_ne_zero_of_mul_eq_one hu
  let e : (Unit → Fv F v) ≃ₜ Fv F v :=
    (Homeomorph.funUnique Unit (Fv F v)).trans (Homeomorph.mulLeft₀ ((a : AF F).2 v) ha)
  have he : ∀ y, e y = (a : AF F).2 v * y () := fun y => rfl
  have hO : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isClopen_integer _
  have hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have key : ∀ h : Fv F v → ℝ, Continuous h → HasCompactSupport h →
      Continuous (h ∘ e) ∧ HasCompactSupport (h ∘ e) := fun h h1 h2 =>
    ⟨h1.comp e.continuous, h2.comp_isClosedEmbedding e.isClosedEmbedding⟩
  by_cases hv : v ∈ S
  · have hfun : psiA S g a v = g v ∘ e := by
      funext y
      simp [psiA, hv, he]
    rw [hfun]
    exact key _ (hg v hv).1 (hg v hv).2
  · have hfun : psiA S g a v =
        (Set.indicator (v.adicCompletionIntegers F : Set (Fv F v)) (fun _ => (1 : ℝ))) ∘ e := by
      funext y
      simp [psiA, hv, he, Set.indicator_apply]
    rw [hfun]
    refine key _ (hO.continuous_indicator continuous_const) ?_
    exact HasCompactSupport.intro hOc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.CompanionTheory.BasePsi.Test

end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem phiA_test : ∀ (F : Type) [Field F] [NumberField F] (G : Ainf F → ℝ) (a : (AF F)ˣ), Continuous G → HasCompactSupport G →
    Continuous (phiA G a) ∧ HasCompactSupport (phiA G a) := by
  intro F _ _ G a hc hs
  have h1 : (a : AF F).1 * ((a⁻¹ : (AF F)ˣ) : AF F).1 = 1 :=
    congrArg Prod.fst (a.mul_inv)
  have h2 : ((a⁻¹ : (AF F)ˣ) : AF F).1 * (a : AF F).1 = 1 :=
    congrArg Prod.fst (a.inv_mul)
  let m : Ainf F ≃ₜ Ainf F :=
    { toFun := fun x => (a : AF F).1 * x
      invFun := fun x => ((a⁻¹ : (AF F)ˣ) : AF F).1 * x
      left_inv := fun x => by simp only [← mul_assoc, h2, one_mul]
      right_inv := fun x => by simp only [← mul_assoc, h1, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let e : (Unit → Ainf F) ≃ₜ Ainf F := (Homeomorph.funUnique Unit (Ainf F)).trans m
  have he : phiA G a = G ∘ e := by
    funext y
    rfl
  rw [he]
  exact ⟨hc.comp e.continuous, hs.comp_homeomorph e⟩

end GlobalTheory.CompanionTheory.BasePsi

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.nu_pair_of_derivatives_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k → GlobalTheory.BZSeg.NuPair k := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | exact GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | (intros; apply GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourier_jacobi_expansion_bounded : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (g : G D n) (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∀ B : ℝ, (∀ y x, ‖zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))‖ ≤ B) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g))) → FJ M m ψ b₀ F g φ = ∫ v in m.𝓕 ×ˢ m.𝓕, zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) * conj (th ψ b₀ φ 0 v.2 v.1) ∂(m.μ.prod m.μ) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fj_fold_mean | exact GlobalTheory.CompanionTheory.FJE.fj_fold_mean | (intros; apply GlobalTheory.CompanionTheory.FJE.fj_fold_mean <;> assumption)
end
