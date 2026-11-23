module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClass
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle794
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle792
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle599
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaOfDiscCocycle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle257
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle795
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle360
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisCoboundary_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → TWmap (frobOB l O) T (actB (sQ l) T g b - b) = actB (sQ l) T g b - b := by
  first | exact @GlobalTheory.BKGal.PhiFix.frob_fixed_coboundary | exact GlobalTheory.BKGal.PhiFix.frob_fixed_coboundary | (intros; apply GlobalTheory.BKGal.PhiFix.frob_fixed_coboundary <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_frobeniusPotential_cocycle_class : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), (∀ y ∈ D.Y, ∃ b, R.IsPotential y b) ∧ (∀ y c c', R.ClassOf y c → R.ClassOf y c' → c - c' ∈ latticeCoboundaries T.L) ∧ (∀ y c (k : ℕ), R.ClassOf y c → R.ClassOf ((l : K) ^ k • y) ((l : K) ^ k • c)) ∧ ∀ y c, ∀ m ∈ D.Minv, R.ClassOf y c → R.ClassOf (y + (D.phi m - m)) c := by
  first | exact @GlobalTheory.GalPot.potential_class | exact GlobalTheory.GalPot.potential_class | (intros; apply GlobalTheory.GalPot.potential_class <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_integral_crystal_stratification_matrix : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := ↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  first | exact @GlobalTheory.CrysStrat.exists_stratification | exact GlobalTheory.CrysStrat.exists_stratification | (intros; apply GlobalTheory.CrysStrat.exists_stratification <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  first | exact @GlobalTheory.CrysGal.galois_taylor_basis | exact GlobalTheory.CrysGal.galois_taylor_basis | (intros; apply GlobalTheory.CrysGal.galois_taylor_basis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.monodromy_image_mem_BdRplus_lattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ m ∈ P.M, ∀ n : ℕ, E ↥LL.1 l e ^ n • P.EN m ∈ P.Man → ∀ w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e, (∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) = hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i)) → ∀ i, ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => w τ i) ∈ Ideal.span {ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ n} := by
  first | exact @GlobalTheory.GalStep.main | exact GlobalTheory.GalStep.main | (intros; apply GlobalTheory.GalStep.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_truncLog_gal_mod_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk C c hc m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.T.exists_approx_root_eisenstein_away_prime l K bk m
  obtain ⟨N, r, hr⟩ := GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow l K bk M m q hq1
  obtain ⟨d, hd⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l m
  set w₀ : bk.S := ((l : bk.S) ^ M * X - q) * r with hw₀
  have hE : bk.E ∣ w₀ := by
    have e1 : (l : bk.S) ^ M * X - q = -(q - (l : bk.S) ^ M * X) := by ring
    rw [hw₀, e1]
    exact (dvd_neg.2 hq1).mul_right _
  set s' : bk.S := ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : bk.S) * w₀ ^ (j + 1) *
    (l : bk.S) ^ (N * (m - (j + 1))) with hs'
  set s : bk.S := (bk.Ep.natDegree : bk.S) * PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d) * s' with hsdef
  refine ⟨m + N * m, s, ?_, fun g => ?_⟩
  · rw [hsdef]
    apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro j _
    exact ((hE.pow (Nat.succ_ne_zero j)).mul_left _).mul_right _

  set R := Per.AinfP l ⧸ Per.kerP l ^ m
  let qm : Per.AinfP l →+* R := Ideal.Quotient.mk _
  let ι : Per.Ainf l →+* Per.AinfP l := algebraMap (Per.Ainf l) (Per.AinfP l)
  have hev : ∀ x, Per.ev l m (aDp l x) = qm (ι x) := fun x => LogFun.ev_alg m (ι x)
  let I : Ideal R := (Per.kerP l).map qm
  have hI : I ^ m = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have hnil : ∀ x ∈ I, x ^ m = 0 := fun x hx => by
    have := Ideal.pow_mem_pow hx m
    rwa [hI, Ideal.mem_bot] at this
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := fun n hn => by
    have := (GlobalTheory.RingBasics.isUnit_nat l n hn).map qm
    rwa [map_natCast] at this
  obtain ⟨lam, hlam⟩ : ∃ lam : R, (l : R) * lam = 1 := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map qm
    rw [map_natCast] at this
    exact this.exists_right_inv
  let f : bk.S →+* R := qm.comp (ι.comp bk.ev)
  let fσ : bk.S →+* R := qm.comp (ι.comp ((Per.σA (g : GQ l)).comp bk.ev))
  have hEm : ι (bk.ev bk.E) ∈ Per.kerP l := by
    have h0 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    first | exact GlobalTheory.RingIface.alg_mem_kerP _ h0 | exact GlobalTheory.RingIface.alg_mem_kerP h0
  have hfE : f bk.E ∈ I := Ideal.mem_map_of_mem _ hEm
  have hfσE : fσ bk.E ∈ I := by
    refine Ideal.mem_map_of_mem _ ?_
    have := GlobalTheory.RingBasics.ker_σ (g : GQ l) hEm
    rwa [Ideal.mem_comap, GlobalTheory.RingBasics.awayMap_algebraMap₂] at this
  have hdvd : ∀ (φ : bk.S →+* R), φ bk.E ∈ I → ∀ x : bk.S, bk.E ^ m ∣ x → φ x = 0 := by
    intro φ hφ x ⟨y, hy⟩
    rw [hy, map_mul, map_pow, hnil _ hφ, zero_mul]
  have hfr : f q * f r = (l : R) ^ N := by
    have := hdvd f hfE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hfσr : fσ q * fσ r = (l : R) ^ N := by
    have := hdvd fσ hfσE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hσq : fσ q = f q := by
    have h := GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil l K bk m M q hq1 hq2 g
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, hev, map_sub, map_sub] at h
    exact sub_eq_zero.1 h
  have hlamN : (l : R) ^ N * lam ^ N = 1 := by rw [← mul_pow, hlam, one_pow]
  have hσr : fσ r = f r := by
    have hu : IsUnit (f q) := isUnit_iff_exists_inv.2 ⟨f r * lam ^ N, by rw [← mul_assoc, hfr, hlamN]⟩
    apply hu.mul_left_cancel
    rw [← hσq, hfσr, hσq, hfr]
  obtain ⟨e, hxe, he1, hlog⟩ := GlobalTheory.T.galois_factor_tilt_log_bdRPlus l C bk.flat (g : GQ l) (c g) (hc g)
  set τ : R := qm (ι (Per.tm e)) with hτ
  have hσX : fσ X = f X * τ := by
    change qm (ι (Per.σA (g : GQ l) (bk.ev X))) = qm (ι (bk.ev X)) * qm (ι (Per.tm e))
    rw [bk.ev_X, ← map_mul, ← map_mul]
    congr 2
    change Per.σA (g : GQ l) (WittVector.teichmuller l _) = _
    rw [GlobalTheory.RingIface.sigA_teich, hxe, map_mul]
  have hσC : ∀ w, fσ (PowerSeries.C w) = f (PowerSeries.C w) := fun w => by
    change qm (ι (Per.σA (g : GQ l) (bk.ev (PowerSeries.C w)))) = qm (ι (bk.ev (PowerSeries.C w)))
    rw [bk.ev_C, bk.gal_w]
  let T : R → R := fun a => ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : R) * a ^ (j + 1)
  have hT : ∀ (φ : bk.S →+* R) (a : R), φ w₀ = a * (l : R) ^ N → φ s' = (l : R) ^ (N * m) * T a := by
    intro φ a ha

    simp only [hs', map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, ha, T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : N * m = N * (j + 1) + N * (m - (j + 1)) := by
      rw [← mul_add]; congr 1; have := Finset.mem_range.1 hj; omega
    rw [hjm]
    ring
  set A : R := f w₀ * lam ^ N with hAdef
  set B : R := fσ w₀ * lam ^ N with hBdef
  have hA : f w₀ = A * (l : R) ^ N := by rw [hAdef]; linear_combination (-(f w₀)) * hlamN
  have hB' : fσ w₀ = B * (l : R) ^ N := by rw [hBdef]; linear_combination (-(fσ w₀)) * hlamN
  have hAI : A ∈ I := by
    obtain ⟨u, hu⟩ := hE
    rw [hAdef, hu, map_mul]
    exact I.mul_mem_right _ (I.mul_mem_right _ hfE)
  have hbI : τ - 1 ∈ I := by
    have := Ideal.mem_map_of_mem qm (LogFun.mu_mem he1)
    simpa [GlobalTheory.MemLoc.mu, hτ] using this
  have hB : B = A + (τ - 1) + A * (τ - 1) := by
    rw [hBdef, hAdef]
    simp only [hw₀, map_mul, map_sub, map_pow, map_natCast, hσX, hσq, hσr]
    linear_combination (τ - 1) * lam ^ N * hfr + (τ - 1) * hlamN
  have htr : T B = T A + T (τ - 1) := by
    rw [hB]
    exact LogAdd.trunc_add hR m I hI A (τ - 1) hAI hbI
  have hl := GlobalTheory.CrisIncl.factorial_mul_ev l e _ he1 hlog m
  have hl2 : (m.factorial : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t) = T (τ - 1) := by
    rw [hl]

    simp only [T, map_sum, map_mul, map_pow, map_sub, map_one, map_natCast, map_neg, hτ]
    rfl
  have hfC : (m.factorial : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) = (l : R) ^ m := by
    have := congrArg (f.comp (PowerSeries.C.comp (algebraMap ℤ_[l] (Wq l bk.a)))) hd
    simpa only [map_mul, map_natCast, map_pow, RingHom.comp_apply] using this
  have hfs' := hT f A hA
  have hfσs' := hT fσ B hB'
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  have e1 : Per.ev l m (aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s)) = fσ s - f s := by
    rw [hev, map_sub, map_sub]; rfl
  have e2 : Per.ev l m ((l : Per.BdRp l) ^ (m + N * m) *
      (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t)) =
      (l : R) ^ (m + N * m) * ((bk.Ep.natDegree : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t)) := by
    simp only [map_mul, map_pow, map_natCast]; ring
  rw [map_sub, e1, e2]
  have e3 : fσ s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * fσ s' := by
    rw [hsdef, map_mul, map_mul, map_natCast, hσC]
  have e4 : f s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * f s' := by
    rw [hsdef, map_mul, map_mul, map_natCast]
  rw [e3, e4, hfs', hfσs']
  apply (hR _ m.factorial_ne_zero).mul_left_cancel
  rw [mul_zero]
  linear_combination ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (T B - T A)) * hfC -
    ((l : R) ^ (m + N * m) * (bk.Ep.natDegree : R)) * hl2 + ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (l : R) ^ m) * htr

end GlobalTheory.BSP.BK
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem GlobalTheory.BSP.equivariant_matrix_over_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf
  obtain ⟨X, hX, hfix, hphi⟩ := GlobalTheory.T.stratPeriodMatrix_exists_fixed_frobenius_solution l K bk d d' S S' ρ ρ' T T' hT hT' f hf
  have hOE := GlobalTheory.T.equivariant_phiModule_matrix_mem_OE l K bk d d' S S' X hfix hphi
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_breuilKisin_frobenius_period l K bk
  obtain ⟨M, x, hx⟩ := GlobalTheory.T.exists_ainf_lift_period_pow_smul_intertwiner l K bk τ hτ d d' S S' ρ ρ' T T' hT hT' f X hX
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_powerSeries_lift_of_period_pow_smul_integral_matrix l K bk τ hτ d d' M X x hOE hx
  exact ⟨Y, by rw [hY]; exact hX⟩
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem envelope_dvd_lpow_aux₁ {R : Type} [CommRing R] {ι : Type} (s : Finset ι) (L a b : R) (u v : ι → R)
    (hL : L ∈ nonZeroDivisors R) (h : a * (L * b) = ∑ i ∈ s, L * u i * v i) : a * b = ∑ i ∈ s, u i * v i := by
  refine sub_eq_zero.1 ((mem_nonZeroDivisors_iff.mp hL).2 _ ?_)
  have e : ∑ i ∈ s, u i * v i * L = ∑ i ∈ s, L * u i * v i := Finset.sum_congr rfl fun i _ => by ring
  rw [sub_mul, Finset.sum_mul, e, ← h]
  ring

theorem envelope_dvd_lpow_aux₂ {R : Type} [CommRing R] (L w z : R) (k : ℕ)
    (hL : ∀ x : R, L * x = 0 → x = 0) (h : L * w = L ^ (k + 1) * z) : L ^ k ∣ w :=
  ⟨z, sub_eq_zero.1 (hL _ (by rw [mul_sub, h, pow_succ', mul_assoc, sub_self]))⟩

theorem envelope_dvd_lpow_aux₄ {R : Type} [CommRing R] (L x y : R) (k : ℕ) (hxy : x = L * y) (h : L ^ k ∣ y) :
    L ^ (k + 1) ∣ x := by
  rw [hxy, pow_succ']
  exact mul_dvd_mul_left _ h

theorem envelope_dvd_lpow_aux₃ {l : ℕ} [Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} (σ : Hom B (ainfObj K))
    (x y : B.A) (k : ℕ) (hxy : x = (l : B.A) * y) (h : ((l : ℕ) : (ainfObj K).A) ^ (k + 1) ∣ σ.f x) :
    ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f y := by
  subst hxy
  obtain ⟨z, hz⟩ := h
  rw [map_mul, map_natCast] at hz
  exact envelope_dvd_lpow_aux₂ (R := Ainf l) (l : Ainf l) (σ.f y) z k ainf_torsionFree hz

theorem envelope_dvd_lpow_of_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (c : κ → κ → En.Q.A) (h k : ℕ) (x : κ → En.Q.A), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ^ k ∣ x j := by
  intro l _ K bk En κ _ c h k
  have hreg : ((l : ℕ) : En.Q.A) ∈ nonZeroDivisors En.Q.A :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk En.Q.A (BK.hf En.inl) (Digits l) En.tb).2.2.1
  induction k with
  | zero => intro x _ _ j; rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    intro x hx hσ j
    have h1 := GlobalTheory.T.dvd_l_of_galoisSections_breuilKisinCoproduct l K bk En κ x c h hx
      (fun g σ e1 e2 i => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) (hσ g σ e1 e2 i))
    choose y hy using h1
    have hyeq : ∀ j, BK.hf En.inl bk.E ^ h * y j = ∑ i, En.Q.D.φ (y i) * c i j := by
      intro j
      have hxj := hx j
      simp only [hy, map_mul, map_natCast] at hxj
      exact envelope_dvd_lpow_aux₁ Finset.univ _ _ _ (fun i => En.Q.D.φ (y i)) (fun i => c i j) hreg hxj
    have hσ' : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
        σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (y j) := by
      intro g σ e1 e2 i
      exact envelope_dvd_lpow_aux₃ σ (x i) (y i) k (hy i) (hσ g σ e1 e2 i)
    exact envelope_dvd_lpow_aux₄ _ _ _ k (hy j) (ih y hyeq hσ' j)

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.exists_bounded_periods_disc_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  first | exact @GlobalTheory.BSP.exists_bounded_periods | exact GlobalTheory.BSP.exists_bounded_periods | (intros; apply GlobalTheory.BSP.exists_bounded_periods <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.exists_beta_of_disc_cocycle_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (φε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (H : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsUnit H → (∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∀ a b, bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) a b) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) → ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b := by
  first | (exact @GlobalTheory.BKLim.exists_beta_of_disc_cocycle) | (exact GlobalTheory.BKLim.exists_beta_of_disc_cocycle) | (intros; apply GlobalTheory.BKLim.exists_beta_of_disc_cocycle  <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

private theorem flat_strictMono (d h : ℕ) : StrictMono (fun p : Fin (d * h) =>
    (toLex ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2⟩ : Σₗ _ : Fin d, Fin h)) := by
  intro p q hpq
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨a', b'⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [Equiv.symm_apply_apply]
  have h1 : (b : ℕ) + h * a < b' + h * a' := hpq
  rcases lt_trichotomy a a' with hlt | rfl | hgt
  · exact Sigma.Lex.left _ _ hlt
  · exact Sigma.Lex.right _ _ (show b < b' from by
      rw [Fin.lt_def]; omega)
  · exfalso
    have h2 : (a' : ℕ) + 1 ≤ a := hgt
    have h3 := Nat.mul_le_mul_left h h2
    have h4 := b'.2
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega

theorem _root_.GlobalTheory.T.parabolicInduction_in_stages_product_of_products : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d h : ℕ) (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM')) := by
  intro k _ _ _ _ d h y N M hN hM hM'
  have hφ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) d N (fun _ => h) (fun a b => (y a b).1)
    (fun a => stdBlocks (fun b => (y a b).1) (hN a)) _ (fun a b => (y a b).rep) (Fin M) (stdBlocks N hM)
  obtain ⟨E0, ⟨φ⟩⟩ := hφ
  let F : Fin (d * h) ≃ Σₗ _ : Fin d, Fin h :=
    finProdFinEquiv.symm.trans ((Equiv.sigmaEquivProd (Fin d) (Fin h)).symm.trans toLex)
  let E : (Σ p : Fin (d * h), Fin (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) ≃ Fin M :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ _ : Fin d, Fin h => Fin (y (ofLex c).1 (ofLex c).2).1) F).trans E0
  have hψ := GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) F (flat_strictMono d h) F.surjective E0 E
    (fun _ _ => rfl) fun c => (y (ofLex c).1 (ofLex c).2).rep
  obtain ⟨ψ⟩ := hψ
  have hχ := GlobalTheory.ProdReorder.multiProd_placing (k := k) E
    (stdBlocks (fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) hM')
    fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).rep
  obtain ⟨χ⟩ := hχ
  exact ⟨φ.trans (ψ.trans χ)⟩
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSpan

theorem hkSS_of_rows_guarded {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y)
    (hG : CommG D) (hC : HkComm D) (hSF : SupFull D)
    (X : NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0))
    (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (hEmb : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x,
      D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x))
    (hBr : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, LinearMap.range (D.nexp.embB i j b) =
      D.nexp.Bsup i j b ⊓ (V0 D.nexp i j b).restrictScalars (D.ntw.O i))
    (hSp : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ((LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).Splits) :
    HkSS D := by
  intro i hi j hj b
  have := D.nexp.towFm i j b

  have hspan : ∀ x ∈ V0 D.nexp i j b,
      x ∈ Submodule.span (FractionRing (D.ntw.O i)) (Set.range (D.nexp.embB i j b)) := by
    intro x hx
    have hx' : x ∈ Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) := by
      rw [(hSF i hi j hj b).2]; exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (D.ntw.O i))).1 hx'
    rw [Submodule.span_eq] at hy
    have hyV : y ∈ V0 D.nexp i j b := by
      have e : y = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (z : D.ntw.O i)) •
          (IsLocalization.mk' (FractionRing (D.ntw.O i)) (1 : D.ntw.O i) z • y) := by
        rw [smul_smul, mul_comm, IsLocalization.mk'_spec, map_one, one_smul]
      rw [e]; exact Submodule.smul_mem _ _ hx
    have hyR : y ∈ LinearMap.range (D.nexp.embB i j b) := by
      rw [hBr i hi j hj b]
      exact Submodule.mem_inf.2 ⟨hy, (Submodule.restrictScalars_mem _ _ _).2 hyV⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (LinearMap.mem_range.1 hyR))

  have hpoly : ∀ k P, HkIdx i k P → ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧ p.Splits ∧
      ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
    intro k P hkP
    obtain ⟨p1, hp10, hp1s, hp1k⟩ := GlobalTheory.T.split_charpoly_lattice_kills_span (D.ntw.O i) (D.nexp.Fm i j b) (D.ntw.B i j b)
      (D.nexp.embB i j b) (D.ntw.hk i j b k P) (D.nexp.hkF i j b k P) (hEmb i hi j hj b k P hkP)
      (hSp i hi j hj b k P hkP)
    obtain ⟨p2, hp2s, hp2k⟩ :=
      GlobalTheory.GoodSS.hkF_separable Rl F cG S Y H hG hC X hR hU hI hS0c hS02 hS0b i hi j hj b k P hkP
    classical
    refine ⟨EuclideanDomain.gcd p1 p2, hp2s.of_dvd (EuclideanDomain.gcd_dvd_right _ _),
      hp1s.of_dvd hp10 (EuclideanDomain.gcd_dvd_left _ _), ?_⟩
    intro x hx
    rw [EuclideanDomain.gcd_eq_gcd_ab, mul_comm p1, mul_comm p2, map_add (f := _), map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp1k x (hspan x hx), hp2k x hx,
      map_zero, map_zero, add_zero]

  have hJ := GlobalTheory.JointDiag.le_iSup_jointEigenspace_inf (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) {a : ℕ × PlE D.host // HkIdx i a.1 a.2}
    (fun a => D.nexp.hkF i j b a.1.1 a.1.2) (V0 D.nexp i j b)
    (fun a c => hC i hi j hj b _ _ _ _ a.2 c.2)
    (fun a x hx => GlobalTheory.T.hecke_preserves_good_part D hG i hi j hj b _ _ a.2 x hx)
    (fun a => hpoly _ _ a.2)
  refine hJ.trans (iSup_le fun ev => ?_)
  classical
  refine le_iSup_of_le (fun k P => if h : HkIdx i k P then ev ⟨(k, P), h⟩ else 0) (inf_le_inf_right _ ?_)
  unfold Eigsp
  refine le_iInf fun k => le_iInf fun P => le_iInf fun h => ?_
  refine (iInf_le _ ⟨(k, P), h⟩).trans ?_
  simp only [dif_pos h]
  exact le_rfl

end GlobalTheory.GoodSpan
end
end
