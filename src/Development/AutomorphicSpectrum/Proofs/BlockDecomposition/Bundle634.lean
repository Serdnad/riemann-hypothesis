module

public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle624
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle029
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle626
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle007
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

namespace GlobalTheory.CompanionTheory.ConeInt

theorem setLIntegral_Ici_rpow_lt_top {a b : ℝ} (ha : a < -1) (hb : 0 < b) :
    ∫⁻ x in Ici b, ENNReal.ofReal (x ^ a) < ⊤ := by
  have h : IntegrableOn (fun x : ℝ => x ^ a) (Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2 (integrableOn_Ioi_rpow_of_lt ha hb)
  exact h.lintegral_lt_top

theorem le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (i : Fin r) :
    min c 1 ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hb0 : 0 < min c 1 := lt_min hc one_pos
  have hb1 : min c 1 ≤ 1 := min_le_right _ _
  have key : ∀ (k : ℕ) (i : Fin r), i.val + k + 1 = r → min c 1 ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simpa using (min_le_left c 1).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp only; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : min c 1 * t ⟨i.val + 1, hj⟩ ≤ c * t ⟨i.val + 1, hj⟩ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hpos _).le
      calc min c 1 ^ (k + 1 + 1) = min c 1 * min c 1 ^ (k + 1) := pow_succ' _ _
        _ ≤ min c 1 * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hb0.le
        _ ≤ t i := h3.trans h2
  have hk : i.val + (r - i.val - 1) + 1 = r := by omega
  refine le_trans ?_ (key (r - i.val - 1) i hk)
  exact pow_le_pow_of_le_one hb0.le hb1 (by omega)

theorem integrand_eq (F : Type) [Field F] [NumberField F] (n : ℕ) {r : ℕ} (m : ℕ) {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) =
      ∏ i, ENNReal.ofReal (t i ^ (-(m : ℝ) -
        ((2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1)) := by
  have hnn : (0 : ℝ) ≤ ∏ i, (t i)⁻¹ ^ m := Finset.prod_nonneg fun i _ => pow_nonneg (inv_pos.2 (ht i)).le _
  rw [← ENNReal.ofReal_mul hnn, ← ENNReal.ofReal_prod_of_nonneg fun i _ => Real.rpow_nonneg (ht i).le _]
  congr 1
  unfold modulus
  rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := ht i
  rw [Real.rpow_sub h, Real.rpow_sub h, Real.rpow_neg h.le, Real.rpow_natCast, Real.rpow_intCast, Real.rpow_one,
    inv_pow, mul_inv]
  field_simp

end GlobalTheory.CompanionTheory.ConeInt

namespace GlobalTheory.CompanionTheory.ConeInt


open GlobalTheory.SiegelSet in
theorem lintegral_cone_lt_top : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) (c : ℝ), 0 < c → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n r c hc
  refine ⟨2 * Module.finrank ℚ F * (2 * r + 1) + 1, fun m hm => ?_⟩
  have hb : 0 < min c 1 ^ r := pow_pos (lt_min hc one_pos) _
  let a : Fin r → ℝ := fun i => -(m : ℝ) -
    ((2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1
  have ha : ∀ i, a i < -1 := by
    intro i
    have hz : (-(m : ℤ)) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) < 0 := by
      have hi : (i.val : ℤ) + 1 ≤ r := by exact_mod_cast i.isLt
      have hm' : 2 * (Module.finrank ℚ F : ℤ) * (2 * r + 1) + 1 ≤ m := by exact_mod_cast hm
      have hd : (0 : ℤ) ≤ 2 * (Module.finrank ℚ F : ℤ) := by positivity
      have hn : (0 : ℤ) ≤ n := by positivity
      have : 2 * (Module.finrank ℚ F : ℤ) * (-(n : ℤ) + 2 * (i.val : ℤ) + 1) ≤
          2 * (Module.finrank ℚ F : ℤ) * (2 * r + 1) :=
        mul_le_mul_of_nonneg_left (by omega) hd
      nlinarith
    have hz' : ((-(m : ℤ) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) < 0 := by
      exact_mod_cast hz
    have : a i = ((-(m : ℤ) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1 := by
      simp only [a]; push_cast; ring
    rw [this]; linarith
  have hsub : cone r c ⊆ Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r) :=
    fun t ht i _ => le_of_mem_cone hc ht i
  have hmeas : MeasurableSet (Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ici
  calc ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹)
      ≤ ∫⁻ t in Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r),
          ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ t in Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r), ∏ i, ENNReal.ofReal (t i ^ a i) :=
        setLIntegral_congr_fun hmeas fun t ht =>
          integrand_eq F n m fun i => hb.trans_le (ht i (mem_univ i))
    _ = ∏ i, ∫⁻ x in Ici (min c 1 ^ r), ENNReal.ofReal (x ^ a i) := by
        rw [volume_pi, Measure.restrict_pi_pi]
        exact GlobalTheory.RestrMeas.lintegral_fin_prod_eq_prod (E := fun _ => ℝ)
          (f := fun i x => ENNReal.ofReal (x ^ a i))
          fun i => ((measurable_id.pow_const (a i)).ennreal_ofReal).aemeasurable
    _ < ⊤ := ENNReal.prod_lt_top fun i _ => setLIntegral_Ici_rpow_lt_top (ha i) hb

end GlobalTheory.CompanionTheory.ConeInt
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.TorusCoord

variable {K : Type} [CommRing K] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) K} {Rx Ry : Matrix (Fin r) (Fin n) K}

theorem left_proj (h1 : Rx * X = 0) (h3 : Rx * Y = 1) : Rx * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, h3, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem left_proj' (h2 : Ry * Y = 0) (h4 : Ry * X = 1) : Ry * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h2, h4, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem lin (h1 : Rx * X = 0) (h2 : Ry * Y = 0) (h3 : Rx * Y = 1) (h4 : Ry * X = 1)
    {A B : Matrix (Fin n) (Fin n) K} (hAB : A * B = 1) {T S : Matrix (Fin r) (Fin r) K} (hTS : T * S = 1)
    (hST : S * T = 1) (hX : B * X = X * T) (hY : B * Y = Y * S) (ξ : Matrix (Fin n) (Fin 1) K)
    (hq : B * ((1 - X * Ry - Y * Rx) * ξ) = (1 - X * Ry - Y * Rx) * ξ) :
    Ry * (A * ξ) = S * (Ry * ξ) ∧ Rx * (A * ξ) = T * (Rx * ξ) ∧
      (1 - X * Ry - Y * Rx) * (A * ξ) = (1 - X * Ry - Y * Rx) * ξ := by
  have hRxQ := left_proj (Ry := Ry) h1 h3
  have hRyQ := left_proj' (Rx := Rx) h2 h4
  have e : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K),
      (1 - X * Ry - Y * Rx) * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  generalize hQ : 1 - X * Ry - Y * Rx = Q at hq hRxQ hRyQ ⊢
  have eQ : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K), Q * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    rw [← hQ]; exact e M
  have hAX : A * X = X * S := by
    have h : A * (B * X) = X := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hX, ← Matrix.mul_assoc] at h
    calc A * X = A * X * (T * S) := by rw [hTS, Matrix.mul_one]
      _ = (A * X * T) * S := by simp only [Matrix.mul_assoc]
      _ = X * S := by rw [h]
  have hAY : A * Y = Y * T := by
    have h : A * (B * Y) = Y := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hY, ← Matrix.mul_assoc] at h
    calc A * Y = A * Y * (S * T) := by rw [hST, Matrix.mul_one]
      _ = (A * Y * S) * T := by simp only [Matrix.mul_assoc]
      _ = Y * T := by rw [h]
  have hAQ : A * (Q * ξ) = Q * ξ := by
    conv_lhs => rw [← hq]
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have hQX : Q * X = 0 := by rw [eQ, h1, h4]; simp
  have hQY : Q * Y = 0 := by rw [eQ, h2, h3]; simp
  have hQQ : Q * Q = Q := by rw [eQ, hRxQ, hRyQ]; simp
  have hdec : ξ = X * (Ry * ξ) + Y * (Rx * ξ) + Q * ξ := by rw [eQ]; abel
  have hu : A * ξ = X * (S * (Ry * ξ)) + Y * (T * (Rx * ξ)) + Q * ξ := by
    conv_lhs => rw [hdec]
    rw [Matrix.mul_add, Matrix.mul_add, hAQ, ← Matrix.mul_assoc A X, ← Matrix.mul_assoc A Y, hAX, hAY,
      Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hu]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Ry X, ← Matrix.mul_assoc Ry Y, ← Matrix.mul_assoc Ry Q, h4, h2,
      hRyQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Rx X, ← Matrix.mul_assoc Rx Y, ← Matrix.mul_assoc Rx Q, h3, h1,
      hRxQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Q X, ← Matrix.mul_assoc Q Y, ← Matrix.mul_assoc Q Q, hQX, hQY,
      hQQ]
    simp

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  have h := congrArg Units.val (map_mul (Formalism.L2.Theta.matHom V) a⁻¹ a)
  rw [inv_mul_cancel, map_one] at h
  exact h.symm

theorem map_mt_eq_archMat {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (ρ : D.what₂.Tau) (a : GA D V) :
    (Formalism.L2.Theta.mt V a).map (fun x => θ ρ (infPart D x)) =
      GlobalTheory.Orb.archMat D.sp.cm.sig V.gram (embOverOf D ρ) (projArch D.sp.cm.sig V.gram (placeOf D ρ) a) := by
  have e := eq_infProj hθ (embOverOf D ρ) rfl
  have h := infMat_infProj (J := V.gram) (isCMExt_host D) (embOverOf D ρ) a
  rw [← e] at h
  refine Eq.trans ?_ (h.trans (GlobalTheory.Orb.archMat_eq_archEquiv V.gram (isCMExt_host D) _ _).symm)
  ext i j
  rfl

theorem torus_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ (ξ : Matrix (Fin V.rank) (Fin 1) D.host.E), (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∧ ∀ ρ, (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => ((t i : ℂ))⁻¹) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ξ).map (tauE D ρ)) ∧ (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => (t i : ℂ)) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ξ).map (tauE D ρ)) ∧ (((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ).map (tauE D ρ)) := by
  intro D θ hθ V r Xf Yf hW t ht a ha ξ
  have hcm := isCMExt_host D
  have hJ := isHermND_gram V
  refine ⟨?_, fun ρ => ?_⟩
  · have h1 : (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 :=
      GlobalTheory.CompanionTheory.SiegelArch.map_matHom_fin V.gram (inv_mem ha.1)
    change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map (finPart D) = _
    rw [Matrix.map_mul, h1, Matrix.one_mul, Matrix.map_map]
    ext i j
    exact GlobalTheory.LatVac.finPart_incA _
  · have hhτ : ∀ x, θ ρ (infPart D (incA D x)) = tauE D ρ x := fun x => (hθ ρ).1 x
    let φ : AE D →+* ℂ := (θ ρ).comp (infPart D)
    have hAB : (Formalism.L2.Theta.mt V a⁻¹).map φ * (Formalism.L2.Theta.mt V a).map φ = 1 := by
      rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hB : (Formalism.L2.Theta.mt V a).map φ = _ := map_mt_eq_archMat hθ V ρ a
    have hcomp : compAt θ ρ (invPt V a ξ) = (Formalism.L2.Theta.mt V a⁻¹).map φ * ξ.map (tauE D ρ) := by
      change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map φ = _
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hhτ _
    obtain ⟨hX, hY, hZ⟩ := ha.2 (placeOf D ρ) (embOverOf D ρ)
    rw [← hB] at hX hY hZ
    simp only [embOverOf_val] at hX hY hZ
    obtain ⟨-, -, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)
    have hxx := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).1
    have hyy := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).2.1
    have hJc : (V.gram.map (tauE D ρ))ᴴ = V.gram.map (tauE D ρ) := by
      ext i j
      rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hJ.1]
    have hyx := GlobalTheory.CentreFin.dual_swap hJc hxy
    have hR : ∀ C : Matrix (Fin V.rank) (Fin r) D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (tauE D ρ) =
          (C.map (tauE D ρ))ᴴ * V.gram.map (tauE D ρ) := fun C => by
      rw [Matrix.map_mul, GlobalTheory.CentreFin.map_cT_emb hcm]
    have h1 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hxx
    have h2 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hyy
    have h3 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hxy
    have h4 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hyx
    have h4E : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * Xf = 1 := by
      refine Matrix.map_injective (tauE D ρ).injective ?_
      beta_reduce
      rw [Matrix.map_mul, h4, Matrix.map_one _ (map_zero _) (map_one _)]
    have hQm : (1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ) =
        1 - Xf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ) -
          Yf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ) := by
      change (tauE D ρ).mapMatrix _ = _
      rw [map_sub, map_sub, map_one]
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul]
    have hxq := left_proj (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.xx hW.xy
    have hyq := left_proj' (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.yy h4E
    have hq := hZ (fun i => ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ :
            Matrix (Fin V.rank) (Fin 1) D.host.E) i 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hxq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hyq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
    have hq' := by
      refine lin h1 h2 h3 h4 hAB (T := diagonal fun i => (t i : ℂ)) (S := diagonal fun i => (t i : ℂ)⁻¹) ?_ ?_ hX hY
        (ξ.map (tauE D ρ)) ?_
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact mul_inv_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact inv_mul_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [← hQm, ← Matrix.map_mul]
        ext i j
        obtain rfl : j = 0 := Subsingleton.elim _ _
        exact congrFun hq i
    obtain ⟨c1, c2, c3⟩ := hq'
    have m : ∀ {a : ℕ} (M : Matrix (Fin a) (Fin V.rank) D.host.E),
        (M * ξ).map (tauE D ρ) = M.map (tauE D ρ) * ξ.map (tauE D ρ) := fun M => Matrix.map_mul
    rw [hcomp, m, m, m, hQm]
    exact ⟨c1, c2, c3⟩

end GlobalTheory.CompanionTheory.TorusCoord
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ


theorem _root_.GlobalTheory.T.twisted_schwartz_function_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), dx.IsAddHaarMeasure →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ b : HermR (AF F) σ n, Integrable (fun X => Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)))) dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt

theorem integrable_isSchwartzBruhat_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M n dx hdx Φ hΦ
  exact (GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.continuous_integrable σ hCM dx hdx hΦ).2

end GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.LeviOne

theorem sum_parts {S : Type} [Ring S] {n r : ℕ} {a b : Matrix (Fin n) (Fin r) S} {c d : Matrix (Fin r) (Fin n) S}
    (ca : c * a = 0) (db : d * b = 0) (cb : c * b = 1) (da : d * a = 1) :
    a * Matrix.diagonal (fun i => (d * (1 : Matrix (Fin n) (Fin n) S) * a) i i) * d +
      b * Matrix.diagonal (fun i => (c * (1 : Matrix (Fin n) (Fin n) S) * b) i i) * c +
      (1 - a * d - b * c) * (1 : Matrix (Fin n) (Fin n) S) * (1 - a * d - b * c) = 1 := by
  have hd : ∀ m : Matrix (Fin r) (Fin r) S, m = 1 → Matrix.diagonal (fun i => m i i) = 1 := by
    intro m hm
    subst hm
    simp
  have hPa : (1 - a * d - b * c) * a = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, da, Matrix.mul_assoc, ca, Matrix.mul_one,
      Matrix.mul_zero]
    simp
  have hPb : (1 - a * d - b * c) * b = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, db, Matrix.mul_assoc, cb, Matrix.mul_one,
      Matrix.mul_zero]
    simp
  have hPP : (1 - a * d - b * c) * (1 - a * d - b * c) = 1 - a * d - b * c := by
    conv_lhs => rw [Matrix.mul_sub (1 - a * d - b * c) (1 - a * d) (b * c), Matrix.mul_sub (1 - a * d - b * c) 1 (a * d)]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPa, hPb, Matrix.zero_mul, Matrix.zero_mul, Matrix.mul_one]
    simp
  rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, hPP, hd _ da, hd _ cb, Matrix.mul_one, Matrix.mul_one]
  abel

theorem leviMat_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A], leviMat σ J A X Y (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)) = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW A _ _
  have hX : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j
    simp [cT, cm_conj_conj h]
  have hJJ : cT (σ : E →+* E) J = J := by
    ext i j
    simpa [cT] using hJ.1 i j
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have e := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at e
    exact e
  have m0 : ∀ {M : Matrix (Fin r) (Fin n) E} {N : Matrix (Fin n) (Fin r) E}, M * N = 0 →
      M.map (inclR (F := F) A) * N.map (inclR (F := F) A) = 0 := by
    intro M N e
    rw [← Matrix.map_mul, e, Matrix.map_zero _ (map_zero _)]
  have m1 : ∀ {M : Matrix (Fin r) (Fin n) E} {N : Matrix (Fin n) (Fin r) E}, M * N = 1 →
      M.map (inclR (F := F) A) * N.map (inclR (F := F) A) = 1 := by
    intro M N e
    rw [← Matrix.map_mul, e, Matrix.map_one _ (map_zero _) (map_one _)]
  exact sum_parts (m0 hW.xx) (m0 hW.yy) (m1 hW.xy) (m1 yx)

end GlobalTheory.CompanionTheory.KFin.LeviOne

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinActS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def sf {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, LF a b i.pl
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

end GlobalTheory.CompanionTheory.FinActS

end
end
