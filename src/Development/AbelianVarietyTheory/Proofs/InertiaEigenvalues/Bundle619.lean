module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApprox
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableExpCocycleCoboundaryModFil
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle239
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle227
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle464
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle601
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle604
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistable_invariant_bdRPlus_basis_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) (k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), Mn ^ d = 0 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∀ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) → ∃ Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l), (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.SFil.invariant_basis_approx) | (exact GlobalTheory.SstPer.SFil.invariant_basis_approx) | (intros; apply GlobalTheory.SstPer.SFil.invariant_basis_approx  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistable_periods_over_Acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∀ (k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * GlobalTheory.SstPer.kap C bk k₀ k Mn (c g))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  first | (exact @GlobalTheory.CrisPeriods.periods_over_Acris_sst) | (exact GlobalTheory.CrisPeriods.periods_over_Acris_sst) | (intros; apply GlobalTheory.CrisPeriods.periods_over_Acris_sst  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistable_exp_cocycle_coboundary_mod_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → Mn ^ d = 0 → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∀ m : ℕ, ∃ (kk : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ kk • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((GlobalTheory.SstPer.kap C bk k₀ k Mn (c g) * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.Cob.cocycle_cob) | (exact GlobalTheory.SstPer.Cob.cocycle_cob) | (intros; apply GlobalTheory.SstPer.Cob.cocycle_cob  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem finiteTowerBound : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E T : ℕ) (G : ℕ → Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Antitone G → G 0 ≤ lowerRamificationGroup K L 0 → ¬ G 0 ≤ G 1 → (∀ σ ∈ G 0, σ ^ p ∈ G 1) → (∀ j, j + 1 ≤ 2 * T + 8 → ∀ σ ∈ G 0, σ ^ p ∈ G (j + 1) → σ ∈ G j) → (∀ k ≤ 2 * T, Detects p 8 (G k) (G (k + 8))) → 2 ^ T * Nat.card ↥(G 0) < E := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E T G hp hE hord hax hanti h0 h01 hpow hlift hdet

  have hG0 : ∀ k, G k ≤ lowerRamificationGroup K L 0 := fun k => le_trans (hanti (Nat.zero_le k)) h0

  have hcomm : ∀ k ≤ 2 * T, ∀ σ ∈ G k, ∀ τ ∈ G k, σ * τ * σ⁻¹ * τ⁻¹ ∈ G (k + 8) :=
    fun k hk => GlobalTheory.T.commutator_mem_of_coboundary_detects_quotient K L p E 8 (G k) (G (k + 8)) hp hE hord (hdet k hk)
  obtain ⟨hw, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot K L

  refine doublingArith (fun a b => jumpSum (wild K L) (G a) (G b)) E T (Nat.card ↥(G 0)) hE ?_ ?_ ?_ ?_
  · intro k hk j hj1 hj8
    refine GlobalTheory.T.ramificationJumpSum_pow_growth K L p E (G k) (G (k + j)) (G (k + j + 1)) (hG0 k) hord ?_ ?_
    · intro σ hσ τ hτ
      exact hanti (show k + j + 1 ≤ k + 8 by omega) (hcomm k hk σ hσ τ hτ)
    · intro σ hσ hσp
      exact hlift (k + j) (by omega) σ (hanti (Nat.zero_le k) hσ) hσp
  · intro k hk
    exact GlobalTheory.T.wildJumpSum_le_of_detecting_coboundary_characters K L p E 8 (G k) (G (k + 8)) hp hE hord hax (hdet k hk)
  · intro k
    exact GlobalTheory.T.ramificationJumpSum_le_add _ (wild K L) (G k) (G (k + 2)) (G (k + 3)) hw hbot (hanti (Nat.le_add_right k 2))
  · refine GlobalTheory.T.card_le_wildJumpSum_of_elementaryAbelian K L p E (G 0) (G 1) hp hE h0 hord ?_ hpow h01
    intro σ hσ τ hτ
    exact hanti (show 1 ≤ 0 + 8 by omega) (hcomm 0 (Nat.zero_le _) σ hσ τ hτ)

end GlobalTheory.PMon.Ram
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

theorem fr_mul_of_fixed (r N : ℕ) (c : ↥(MaximalUnramifiedExtension l)) (h : fr l r c = c) : fr l (r * N) c = c := by
  induction N with
  | zero => simp [fr]
  | succ k ih =>
    change (frobUr l ^ (r * (k + 1))) c = c
    rw [Nat.mul_succ, pow_add, AlgHom.mul_apply]
    change (frobUr l ^ (r * k)) (fr l r c) = c
    rw [h]
    exact ih

theorem isRat_twist {K K' : FinExt l} (hK : K.1 ≤ K'.1) (r N : ℕ) (hN : 0 < N) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (hρ : IsRat r ρ)
    (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l (r * N) c = c → (c : Om l) ∈ K'.1) (hfr : ∀ g, fr l (r * N) (χ g : ↥(MaximalUnramifiedExtension l)) = χ g)
    (hcont : Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) :
    IsRat (r * N) (twist hK ρ χ a) := ⟨Nat.mul_pos hρ.pos hN, hle, fun g i j => by
    rw [twist_val, Matrix.smul_apply, smul_eq_mul, map_mul, fr_mul_of_fixed r N _ (hρ.rat _ i j),
      Units.val_zpow_eq_zpow_val, map_zpow₀, hfr], fun i j => by
    have h1 : Continuous fun g : ↥(GK K') => (((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) :=
      (hρ.cont i j).comp (continuous_subtype_val.subtype_mk _)
    have h2 : Continuous fun g : ↥(GK K') => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l) ^ a :=
      hcont.zpow₀ _ fun g => Or.inl (by
        intro h0
        exact (χ g).ne_zero (Subtype.ext h0))
    refine (h2.mul h1).congr fun g => ?_
    simp only [twist_val, Matrix.smul_apply, smul_eq_mul, Units.val_zpow_eq_zpow_val]
    push_cast
    rfl⟩

theorem potentiallySemistable_of_lubinTateTwist (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ)
    (hact : ∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) :
    AdmSt P (twist hK ρ χ a) → AdmSt P ρ := by
  have msmul : ∀ {R S : Type} [CommRing R] [CommRing S] {F : Type} [FunLike F R S] [RingHomClass F R S] (f : F) (c : R)
      (M : Matrix n n R), (c • M).map f = f c • M.map f := fun f c M => by
    ext i j; simp
  rintro ⟨K'', hK'', Q', hQ'⟩
  refine ⟨K'', hK.trans hK'', scalGL n (Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (x ^ a)) * Q', fun g => ?_⟩
  have hg := hQ' g
  rw [twist_val, msmul, Matrix.smul_mul] at hg
  set g' : ↥(GK K') := ⟨(g : GQ l), GK_le hK'' g.2⟩
  have hx : Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x =
      Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') * x := by
    apply Units.ext
    simpa using hact g'
  have hxa : actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) =
      ks P ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) * Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) := by
    have h2 := congrArg (fun u : P.R.Bˣ => Polynomial.C ((u ^ a : P.R.Bˣ) : P.R.B)) hx
    have e1 : ((Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x ^ a : P.R.Bˣ) : P.R.B) =
        P.actQ (g : GQ l) ((x ^ a : P.R.Bˣ) : P.R.B) := by rw [← map_zpow]; rfl
    have e2 : ((Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') ^ a : P.R.Bˣ) : P.R.B) =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) := by rw [← map_zpow]; rfl
    simp only [mul_zpow] at h2
    rw [e1, Units.val_mul, e2, map_mul] at h2
    rw [actSt_C]
    exact h2
  rw [scalGL_mul_val, msmul, Matrix.mul_smul, Units.coe_map]
  change actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) • _ =
    Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) • _
  rw [hxa]
  conv_rhs => rw [← hg]
  rw [smul_smul, mul_comm (Polynomial.C _)]

omit [DecidableEq n] in
theorem sum_weights (r N : ℕ) (hr : 0 < r) (w : Fin r → n → ℤ) (hN : Fintype.card n = N) :
    ∑ m : Fin (r * N), ∑ j, (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then -∑ m, ∑ j, w m j else 0) = 0 := by
  subst hN
  simp only [Finset.sum_add_distrib]
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range (r * N), (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) i =
      N * ∑ m, ∑ j, w m j := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have : ∑ x ∈ Finset.range r, (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x) =
          ∑ m, ∑ j, w m j := by
        rw [← Fin.sum_univ_eq_sum_range (fun x => (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x))]
        refine Finset.sum_congr rfl fun m _ => ?_
        have e : (⟨(r * k + (m : ℕ)) % r, Nat.mod_lt _ hr⟩ : Fin r) = m := by
          apply Fin.ext
          simp only
          rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt m.2]
        simp only [e]
      rw [this]
      push_cast
      ring
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j), key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => if i = 0 then -∑ m, ∑ j, w m j else 0),
    Finset.sum_ite_eq' (Finset.range _) 0]
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · simp [h0]
  · rw [if_pos (Finset.mem_range.mpr (Nat.mul_pos hr h0))]
    ring

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon

theorem twistStep : TwistStep := by
  intro l _ P AI T n _ _ K r ρ w hρ hw
  by_cases hn : Fintype.card n = 0
  · refine ⟨K, r, ρ, w, hρ, hw, ?_, id⟩
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    simp
  · have hN : 0 < Fintype.card n := Nat.pos_of_ne_zero hn
    have hs : 0 < r * Fintype.card n := Nat.mul_pos hρ.pos hN
    obtain ⟨K', hK, x, χ, hle, hfr, hcont, hact, h1, h2, hj⟩ := GlobalTheory.T.exists_lubinTate_character_unramified_period l P AI T K (r * Fintype.card n) hs
    exact ⟨K', r * Fintype.card n, Twist.twist hK ρ χ (-∑ m, ∑ j, w m j), _,
      Twist.isRat_twist hK r _ hN ρ χ _ hρ hle hfr hcont,
      GlobalTheory.T.hasHodgeTateWeightFrame_character_twist l P AI T n K K' hK r (Fintype.card n) hρ.pos ρ w χ x _ hρ hw hact h1 h2 hj,
      Twist.sum_weights r _ hρ.pos w rfl, Twist.potentiallySemistable_of_lubinTateTwist P hK ρ χ x _ hact⟩

end GlobalTheory.PMon

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.MooreDeterminant

variable {B Q : Type} [CommRing B] [IsDomain B] [Field Q] [Algebra Q B]

theorem det_mem (S : B → Prop) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι B) (hM : ∀ i j, S (M i j)) : S M.det := by
  rw [Matrix.det_apply]
  have hz : S 0 := by simpa using h0 0
  refine Finset.sum_induction _ S hadd hz ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply hmul
  · have := h0 (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Q)
    simpa using this
  · have h1 : S 1 := by simpa using h0 1
    exact Finset.prod_induction _ S hmul h1 (fun i _ => hM _ _)

theorem iter_eq (φ : B →+* B) (m : ℕ) : ⇑(φ ^ m) = (⇑φ)^[m] := RingHom.coe_pow φ m

theorem moore_core (φ : B →+* B) (S : B → Prop)
    (hφ : ∀ b, S b → S (φ b)) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    (L : B) (hL : φ L = L) (h : ℕ)
    (ratio : ∀ s, s < h → ∀ ω ω' : B, S ω → S ω' → φ^[h] ω = L ^ s * ω → φ^[h] ω' = L ^ s * ω' → ω' ≠ 0 →
      φ ω * ω' = ω * φ ω' → ∃ c : Q, ω = c • ω') :
    ∀ (n : ℕ) (a : Fin (n + 1) → B), n + 1 ≤ h → (∀ j, S (a j)) → (∀ j, φ^[h] (a j) = L * a j) →
      LinearIndependent Q a → (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a j)).det ≠ 0 := by
  have hSit : ∀ (i : ℕ) b, S b → S (φ^[i] b) := by
    intro i
    induction i with
    | zero => intro b hb; simpa using hb
    | succ i ih => intro b hb; rw [Function.iterate_succ_apply']; exact hφ _ (ih b hb)
  intro n
  induction n with
  | zero =>
    intro a _ _ _ ha
    rw [Matrix.det_fin_one]
    simpa using ha.ne_zero 0
  | succ n ih =>
    intro a hk hSa hfa ha hdet
    set M : Matrix (Fin (n + 2)) (Fin (n + 2)) B := Matrix.of fun i j => φ^[i] (a j) with hMdef

    have hA := ih (a ∘ Fin.castSucc) (by omega) (fun j => hSa _) (fun j => hfa _)
      (ha.comp _ (Fin.castSucc_injective _))
    set ω : Fin (n + 2) → B := fun m => (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))).det with hωdef
    have hωl : ω (Fin.last _) = (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)).det := by
      simp [ω, Fin.succAbove_last]
    have hωl0 : ω (Fin.last _) ≠ 0 := by rw [hωl]; exact hA
    have hu : ∀ m, M.adjugate m (Fin.last _) = (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * ω m := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      simp only [Fin.val_last, Fin.succAbove_last, ω]
      congr 2
    have hw : ∀ m, M.adjugate m 0 = (-1) ^ (m : ℕ) * φ (ω m) := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hωdef]
      simp only [Fin.val_zero, zero_add, Fin.succAbove_zero]
      rw [RingHom.map_det]
      congr 2
      ext i j
      simp [M, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Function.iterate_succ_apply']
    have hK : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
    have hker : ∀ i c, ∑ m, M i m * M.adjugate m c = 0 := fun i c => by
      have := congrFun (congrFun hK i) c
      simpa [Matrix.mul_apply] using this

    set v : Fin (n + 2) → B := fun m => M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0 -
      M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _) with hvdef
    have hv : ∀ i, ∑ m, M i m * v m = 0 := by
      intro i
      have e1 := hker i 0
      have e2 := hker i (Fin.last _)
      simp only [v, mul_sub, Finset.sum_sub_distrib]
      have : ∑ m, M i m * (M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0) =
          M.adjugate (Fin.last _) (Fin.last _) * ∑ m, M i m * M.adjugate m 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      have : ∑ m, M i m * (M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _)) =
          M.adjugate (Fin.last _) 0 * ∑ m, M i m * M.adjugate m (Fin.last _) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      simp_all
    have hvl : v (Fin.last _) = 0 := by simp only [v]; ring
    have hv' : Matrix.mulVec (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)) (v ∘ Fin.castSucc) = 0 := by
      funext i
      have := hv (Fin.castSucc i)
      rw [Fin.sum_univ_castSucc, hvl, mul_zero, add_zero] at this
      simpa [Matrix.mulVec, dotProduct, M] using this
    have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hA hv'
    have hvall : ∀ m, v m = 0 := by
      intro m
      refine Fin.lastCases hvl (fun j => ?_) m
      exact congrFun hv0 j

    have hcomm : ∀ m, φ (ω m) * ω (Fin.last _) = ω m * φ (ω (Fin.last _)) := by
      intro m
      have E := hvall m
      simp only [v, hu, hw, Fin.val_last, pow_add] at E
      have hs : ((-1 : B) ^ (m : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      have he : ((-1 : B) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      linear_combination ((-1 : B) ^ (m : ℕ)) * E
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * hs
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * ((-1 : B) ^ (m : ℕ)) ^ 2 * he

    have hSω : ∀ m, S (ω m) := fun m => det_mem S h0 hadd hmul _ (fun i j => hSit _ _ (hSa _))
    have hLi : ∀ i : ℕ, φ^[i] L = L := fun i => Function.iterate_fixed hL i
    have hfω : ∀ m, φ^[h] (ω m) = L ^ (n + 1) * ω m := by
      intro m
      rw [← iter_eq, hωdef]
      simp only
      rw [RingHom.map_det]
      have : (φ ^ h).mapMatrix (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) =
          L • (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, iter_eq]
        rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hfa, ← iter_eq, map_mul, iter_eq, hLi]
      rw [this, Matrix.det_smul, Fintype.card_fin]

    have hrat : ∀ m, ∃ c : Q, ω m = c • ω (Fin.last _) := fun m =>
      ratio (n + 1) (by omega) _ _ (hSω m) (hSω _) (hfω m) (hfω _) hωl0 (hcomm m)
    choose c hc using hrat

    have hrow := hker 0 (Fin.last _)
    set d : Fin (n + 2) → Q := fun m => (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * c m with hd
    have hsum : (∑ m, d m • a m) * ω (Fin.last _) = 0 := by
      rw [← hrow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hu, hc m]
      simp only [M, Matrix.of_apply, Fin.val_zero, Function.iterate_zero, id, hd, Algebra.smul_def, map_mul, map_pow,
        map_neg, map_one]
      ring
    have hsum0 : ∑ m, d m • a m = 0 := (mul_eq_zero.1 hsum).resolve_right hωl0
    have hdl := Fintype.linearIndependent_iff.1 ha d hsum0 (Fin.last _)
    have hcl : c (Fin.last _) = 0 := by
      simp only [hd, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, false_or] at hdl
      exact hdl
    apply hωl0
    rw [hc (Fin.last _), hcl, zero_smul]

end GlobalTheory.PMon.MooreDeterminant

namespace GlobalTheory.PMon

theorem moore_statement : Moore := by
  intro l _ P AI T h k hk a hPa hfa ha
  obtain ⟨hF, hinj, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  obtain ⟨hpφ, -, hpR, hpQ, -⟩ := GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T
  haveI : IsDomain P.R.BdR := hF.isDomain
  haveI : IsDomain P.R.B := Function.Injective.isDomain (P.ιB : P.R.B →+* P.R.BdR) hinj
  cases k with
  | zero => simp
  | succ n =>
    exact GlobalTheory.PMon.MooreDeterminant.moore_core (Q := ℚ_[l]) (P.φB : P.R.B →+* P.R.B) (Plus T) hpφ hpQ
      (fun a b ha hb => (hpR a b ha hb).1) (fun a b ha hb => (hpR a b ha hb).2) (l : P.R.B) (map_natCast _ l) h
      (fun s hs ω ω' h1 h2 h3 h4 h5 h6 => GlobalTheory.T.crisPlus_frob_eigenvector_ratio_padic l P AI T h s hs ω ω' h1 h2 h3 h4 h5 h6)
      n a hk hPa hfa ha

end GlobalTheory.PMon
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exII_holds : ExII := GlobalTheory.T.exists_nonzero_frobVector_residue_zero

end GlobalTheory.PMon
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.frame_base_eq_cover_frame_moved_by_arithmetic : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h h₀ : GA D (T.V j σ)), (C.dict₂ h).1 = (C.dict₂ h₀).1 → ∀ γ₀ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h₀).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h₀).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h₀).1).Gm ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h₀).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ), mat (T.dict j σ h₀).2 ⟨τ, h₁⟩ = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h₀).2 ⟨τ, h₂⟩) → ∃ δ ∈ ((T.U j σ).X (T.dict j σ h).1).Γ, ∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  first | exact @GlobalTheory.CoverFrameArith.frame_move_arith | exact GlobalTheory.CoverFrameArith.frame_move_arith | (intros; apply GlobalTheory.CoverFrameArith.frame_move_arith <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isδMap_of_dense_δLocus : ∀ (l : ℕ) [Fact l.Prime] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (D : Delta l Q) (DC : Delta l C) (J : Ideal Q) (JC : Ideal C) (h : Q →+* C), (l : Q) ∈ J → J.map h ≤ JC → IsHausdorff JC C → (∀ (x : Q) (n : ℕ), ∃ a ∈ δLocus D DC h, x - a ∈ J ^ n) → IsδMap D DC h := by
  intro l _ Q _ C _ D DC J JC h hl hJ hH hd x
  have hlC : (l : C) ∈ JC := by
    have := hJ (Ideal.mem_map_of_mem h hl)
    simpa using this
  have hpow : ∀ m : ℕ, (J ^ m).map h ≤ JC ^ m := fun m => by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hJ m
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  obtain ⟨a, ha, hxa⟩ := hd x (n + 1)
  have ha' := (mem_δLocus).1 ha
  set y := x - a with hy
  have hxy : x = a + y := by rw [hy]; ring
  have h1 : D.δ (a + y) - D.δ a ∈ J ^ n := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l Q D J hl n a y hxa
  have h1' : h (D.δ x) - h (D.δ a) ∈ JC ^ n := by
    rw [hxy, ← map_sub]; exact hpow n (Ideal.mem_map_of_mem h h1)
  have hyC : h y ∈ JC ^ (n + 1) := hpow (n + 1) (Ideal.mem_map_of_mem h hxa)
  have h2 : DC.δ (h a + h y) - DC.δ (h a) ∈ JC ^ n := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l C DC JC hlC n (h a) (h y) hyC
  have h2' : DC.δ (h x) - DC.δ (h a) ∈ JC ^ n := by rw [hxy, map_add (f := _)]; exact h2
  have key : h (D.δ x) - DC.δ (h x) ∈ JC ^ n := by
    have := (JC ^ n).sub_mem h1' h2'
    rw [ha'] at this
    convert this using 1; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key

end GlobalTheory
end
