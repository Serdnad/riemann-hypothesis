module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExcludedPrimesFewAndSmallAlongFamily
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle228
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle185
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle227
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle077
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle416
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle417
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle418
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.localBoundZeroAtLargePrimes_of_congruenceBound : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  first | exact @GlobalTheory.NLink.RowE.main | exact GlobalTheory.NLink.RowE.main | (intros; apply GlobalTheory.NLink.RowE.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.excludedPrimes_few_and_small_along_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ exc : Finset ℕ, (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x i) ∧ ExcOK (Fm.L x i) exc := by
  first | exact @GlobalTheory.NLink.excOK_family | exact GlobalTheory.NLink.excOK_family | (intros; apply GlobalTheory.NLink.excOK_family <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Proof.baseSize_bounds_along_family

open Formalism.BasicNotions

theorem baseSize_bounds {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) :
    ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes L,
      2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ L.sc.b := by
  intro W0 hW
  have hls : Formalism.MainNotions.TwistedPlaces.lStar L = LevelStarExponents.lStar L := rfl
  have hl0 : 0 < LevelStarExponents.lStar L := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_pos L
  have hgt : L.sc.b' < LevelStarExponents.lStar L := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_gt L P
  have hleb : LevelStarExponents.lStar L ≤ L.sc.b := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_le_b L
  have hw := Formalism.MainNotions.TwistedPlaces.w''_le_b' L
  have hb'0 := Formalism.MainNotions.TwistedPlaces.b'_pos L
  have hx := L.sc.one_lt_alt
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx.le
  have hfl0 : (0 : ℝ) ≤ ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (div_nonneg hb'0.le (by linarith))
  have hfl1 : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _

  have h3 : 3 * LevelStarExponents.lStar L ≤ L.sc.b := by
    have hp2 := Formalism.MainNotions.TwistedPlaces.lStar_part2 L
    rw [hls] at hp2
    have hk := Formalism.MainNotions.TwistedPlaces.m_le_k D
    have hm := Formalism.MainNotions.TwistedPlaces.m_ge_one D
    have hn := Formalism.MainNotions.TwistedPlaces.n_ge_one D
    have ht : (7 : ℝ) ≤ D.R.t := by
      have := Formalism.MainNotions.TwistedPlaces.t_ge D; have := Formalism.MainNotions.TwistedPlaces.k_le_r D; have := Formalism.MainNotions.TwistedPlaces.k_ge_five D; linarith
    have hS := L.Sc_pos
    have hLg := Formalism.MainNotions.TwistedPlaces.Lg_nonneg L
    have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
    have hA : 3 * (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by
      have e1 : (3 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by nlinarith
      have e2 : (D.R.m : ℝ) * 3 ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
        mul_le_mul hk e1 (by norm_num) (by linarith)
      linarith
    have : LevelStarExponents.lStar L * (3 * (D.R.m : ℝ)) ≤ D.R.m * L.sc.b :=
      le_trans (mul_le_mul_of_nonneg_left hA hl0.le) hp2
    nlinarith

  have hη := L.etaSz_pos
  have hm := Formalism.MainNotions.TwistedPlaces.m_ge_one D
  have hq : 0 ≤ L.sc.b / LevelStarExponents.lStar L := div_nonneg (by linarith) hl0.le
  have hlow : 2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ L.sc.w'' D.R.n := by
    have h1 := P.h0_ge.1
    have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη.le hm
    have h3' := P.mteta
    have ht : (0 : ℝ) ≤ D.R.t := by positivity
    have h4 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
      have : (1 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
      nlinarith
    have h7 : 12 * L.sc.b / LevelStarExponents.lStar L = 12 * (L.sc.b / LevelStarExponents.lStar L) := by ring
    linarith
  rcases hW with rfl | rfl | ⟨t, rfl⟩
  · exact ⟨le_trans hlow (by linarith), le_rfl⟩
  · exact ⟨hlow, by linarith⟩
  · have h1 := L.bT_ge t
    have h2 := Formalism.MainNotions.TwistedPlaces.bT_le_two_mul_b' L P t
    exact ⟨by linarith, by linarith⟩

theorem main : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x), ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
    2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ (Fm.L x a).sc.b := by
  intro eps Fm x hx a W0 hW
  exact baseSize_bounds (Fm.L x a) (Fm.params x hx a) W0 hW

end GlobalTheory.Proof.baseSize_bounds_along_family
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.InertiaEigenvalues

theorem lifting_along_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  intro O K _ _ _ _ _ l e a _ _ _ _ _ _ ι₀ ι₁ ι₂ _ _ _ _ _ _ η H D₀ D₁ D₂ F G N Sig U hH y₂ hy₂ m₂ hm₂ h0
  obtain ⟨hex, hnum, htype, hch2⟩ := hH
  have hl : l.Prime := Fact.out
  have hts : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (NeZero.ne a)
  obtain ⟨hr1, hr4, hrper⟩ := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hl ha hts Sig N hnum.frob_mem hnum.zero_mem_Sig
    hnum.card_Sig hnum.two_le
  set r := maxPeriod l Sig with hr
  obtain ⟨hL1, hL2, hL3, -, -, hL6⟩ :=
    GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η r hnum.two_le hnum.one_le hnum.lt hr4 hnum.large
  have hl2 : l ≠ 2 := by
    have h8 : 8 ≤ N ^ 3 := by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hnum.two_le 3
    have := hnum.large
    generalize H * N ^ 2 = A at this
    generalize N ^ 3 = B at this h8
    omega

  have hB : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H :=
    ⟨hnum.frob_mem, hnum.zero_mem_Sig, hnum.card_Sig, hnum.two_le, hnum.range_U, hnum.zero_mem_U,
      hnum.card_U, hnum.one_le, hnum.lt, hnum.large⟩
  obtain ⟨-, hkM, -, hkMinv, -, hkY'⟩ :=
    GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow O K l e a ι₁ ι₂ Sig U N η H hB D₁ D₂ htype hch2 G hex.finiteLength
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N r with hρ
  have hcast : ∀ v : Vec K a ι₂, (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N : ℕ) • v = (l : K) ^ ρ • v := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul K]
    push_cast
    rfl
  obtain ⟨y₁, hy₁, hGy₁⟩ := hkY' y₂ hy₂
  obtain ⟨m₁, hm₁, hGm₁⟩ := hkMinv m₂ hm₂
  rw [hcast] at hGy₁ hGm₁
  have hG1 : G.app (y₁ + D₁.phi m₁) = (l : K) ^ ρ • (y₂ + D₂.phi m₂) := by
    rw [map_add (f := _), G.app_phi, hGy₁, hGm₁, map_smul, smul_add]

  set ω := D₁.Mon (y₁ + D₁.phi m₁) with hω
  have hω1 : (l : K) ^ (η * (r + 1)) • ω ∈ D₁.Z :=
    GlobalTheory.T.breuilKisinDescent_pow_smul_monodromy_add_phi_mem O K l e a ι₁ η H D₁ hnum.one_le hnum.lt (by omega) hL2 r hr1
      (fun τ c hc => hrper c (htype.chars_subset τ hc)) hL6 hl2 y₁ hy₁ m₁ hm₁

  obtain ⟨hjmp, -, hinj, hker⟩ := GlobalTheory.T.breuilKisin_exactTriple_jumps_characters_lift O K l e a ι₀ ι₁ ι₂ η H D₀ D₁ D₂ F G hex
  have hGω : G.onPol ((l : K) ^ (η * (r + 1)) • ω) = 0 := by
    rw [map_smul, hω, G.onPol_Mon, hG1, map_smul, h0, smul_zero, smul_zero]
  obtain ⟨w₀, hw₀, hFw₀⟩ := hker ρ (fun y hy => by
      obtain ⟨x, hx, h⟩ := hkM y hy
      exact ⟨x, hx, h.trans (hcast y)⟩) _ hω1 hGω
  rw [smul_smul, ← pow_add] at hFw₀
  have hy₁Y : y₁ + D₁.phi m₁ ∈ D₁.Yl := by
    refine D₁.desc.mem_Yl_iff.2 ⟨0, ?_⟩
    rw [pow_zero, one_smul]
    refine add_mem (D₁.desc.Y'_le_Y η hy₁) ⟨?_, fun g => ?_⟩
    · exact (mem_divE (l := l) (e := e)).2 (D₁.upper _ (D₁.phi_mem_L hm₁.1))
    · rw [D₁.desc.act_phi, hm₁.2 g]
  obtain ⟨-, wm, hwm, hLcwm⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι₁ η H D₁ _ hy₁Y
  have hIm := (GlobalTheory.T.breuilKisinDescent_monodromy_image_valuation O K l e a ι₁ η H D₁ U N htype.jumps_subset
    (fun i hi => Finset.mem_Icc.2 (hnum.range_U i hi)) hnum.card_U hnum.lt).1
  obtain ⟨w', hw', hFw'⟩ := GlobalTheory.T.lift_image_eulerE_invariants_quotient O K l e a ι₀ ι₁ η H D₀ D₁ F U hIm ω
    ⟨wm, hwm, hLcwm⟩ _ ⟨w₀, D₀.desc.mem_Zl_of_mem_Z hw₀, hFw₀⟩

  set c₂ := GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂ N η r with hc₂
  have hw₀eq : (l : K) ^ c₂ • D₀.Lc w' = w₀ := by
    apply hinj
    rw [map_smul, hFw', hFw₀, hc₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁, add_comm]
  have hjmp0 : D₀.jumps ⊆ (U : Set ℤ) := hjmp.trans htype.jumps_subset
  have hIcc : U ⊆ Finset.Icc (-(η : ℤ)) H := fun i hi => Finset.mem_Icc.2 (hnum.range_U i hi)
  obtain ⟨y, hy, hLcy⟩ := GlobalTheory.T.exists_mem_tameDescent_class_eq_of_pow_mem O K l e a ι₀ η H D₀ U N hjmp0 hIcc hnum.card_U
    hnum.lt (by omega) hL2 c₂ w' hw' (hw₀eq ▸ hw₀)

  have hff := (GlobalTheory.T.breuilKisinDescent_finite_free_invertPrime O K l e a ι₀ η H D₀).1
  obtain ⟨y₀, hy₀, hMy₀⟩ := GlobalTheory.T.exists_monodromy_eq_leadingCoeff_breuilKisinDescent O K l e a ι₀ η H D₀ U N hjmp0 hIcc hnum.card_U
    hnum.one_le hnum.lt hL3 hL2 (GlobalTheory.T.isAdicComplete_twistedInvariantLattice O K l e a ι₀ η H D₀)
    (GlobalTheory.T.isHausdorff_invariants_quotient_of_finiteFree O K l e a ι₀ η H D₀ hff) y hy

  have hGF : ∀ v : Vec K a ι₀, G.app (F.app v) = 0 := by
    intro v

    rw [eq_sum_bas v, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [F.app_smul_tot, G.app_smul_tot]
    have h1 : F.app (bas i) ∈ D₁.M := F.app_mem_M (D₀.bas_mem_M i)
    rw [(hex.exact _ h1).2 ⟨bas i, D₀.bas_mem_M i, rfl⟩, smul_zero]
  set n := c₂ + η + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL N η with hn
  have hs {κ : Type} (v : Vec K a κ) : ((l : O) ^ n) • v = (l : K) ^ n • v := by
    rw [← algebraMap_smul K, map_pow, map_natCast]
  have h3 : ((l : O) ^ n • y₁ - F.app y₀) + D₁.phi ((l : O) ^ n • m₁) =
      (l : K) ^ n • (y₁ + D₁.phi m₁) - F.app y₀ := by
    rw [hs, hs, map_smul, smul_add]
    abel
  refine ⟨_, sub_mem (Submodule.smul_mem _ ((l : O) ^ n) hy₁) (F.app_mem_Y' hy₀), _,
    Submodule.smul_mem _ ((l : O) ^ n) hm₁, ?_, ?_⟩
  · rw [h3, map_sub, map_smul, ← hω, ← F.onPol_Mon, hMy₀, hLcy, map_smul, hFw']
    exact sub_self _
  · rw [h3, map_sub, G.app.map_smul_of_tower, hGF, sub_zero, hG1, smul_smul, ← pow_add]
    rfl

end GlobalTheory.InertiaEigenvalues
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unramified_weilDeligne_eq_diagonal_inv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (y : WD h), y.unr → ∃ α : Fin y.lpDim → ℂˣ, y = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  first | exact @GlobalTheory.LocLanglands.unr_eq_diag_inv | exact GlobalTheory.LocLanglands.unr_eq_diag_inv | (intros; apply GlobalTheory.LocLanglands.unr_eq_diag_inv <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weil_group_restriction : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), ∃ r : Weil h' →* Weil h, (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) ∧ ∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r) := by
  first | exact @GlobalTheory.WeilRestrict.weil_restrict | exact GlobalTheory.WeilRestrict.weil_restrict | (intros; apply GlobalTheory.WeilRestrict.weil_restrict <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weil_deligne_semisimple : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (n : ℕ) (a : WDRep h (Fin n → ℂ)), a.ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho | exact GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho | (intros; apply GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.RegDivide

theorem exists_pow_mul_not_dvd {R : Type*} [CommRing R] (ξ : R) [IsHausdorff (Ideal.span {ξ}) R]
    {y : R} (hy : y ≠ 0) : ∃ (n : ℕ) (z : R), y = ξ ^ n * z ∧ ¬ ξ ∣ z := by
  classical
  have hex : ∃ n : ℕ, ¬ ξ ^ (n + 1) ∣ y := by
    by_contra h
    push Not at h
    apply hy
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ξ}) R)
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow ξ (Nat.le_succ n)).trans (h n)
  have h1 : ξ ^ (Nat.find hex) ∣ y := by
    rcases h : Nat.find hex with _ | k
    · simp
    · by_contra hk
      exact Nat.find_min hex (by omega : k < Nat.find hex) hk
  obtain ⟨z, hz⟩ := h1
  refine ⟨Nat.find hex, z, hz, ?_⟩
  rintro ⟨w, rfl⟩
  apply Nat.find_spec hex
  exact ⟨w, by rw [pow_succ, mul_assoc]; exact hz⟩

theorem abstract {B R D : Type*} [CommRing B] [CommRing R] [CommRing D] (ι : B →+* D) (a : R →+* D)
    (hι : Function.Injective ι) (ξ v : R) [IsHausdorff (Ideal.span {ξ}) R] (hv : IsUnit v)
    (t : B) (ht : IsUnit t) (hιt : ι t = a (ξ * v))
    (hD : ∀ x : D, ∃ (n : ℕ) (y : R), x * a ξ ^ n = a y) (b : B) (hb : b ≠ 0) :
    ∃ (m n : ℕ) (b' : B) (y : R), b * t ^ m = t ^ n * b' ∧ ι b' = a y ∧ ¬ ξ ∣ y := by
  obtain ⟨m, y₀, h0⟩ := hD (ι b)
  obtain ⟨s, hs⟩ := ht.exists_right_inv
  obtain ⟨w, hw⟩ := hv.exists_right_inv
  have h1 : ι (b * t ^ m) = a (y₀ * v ^ m) := by
    rw [map_mul, map_pow, hιt, map_mul, map_mul, ← h0, map_pow]
    ring
  have hne : y₀ * v ^ m ≠ 0 := by
    intro h
    rw [h, map_zero, ← map_zero ι] at h1
    exact hb ((ht.pow m).mul_left_eq_zero.1 (hι h1))
  obtain ⟨n, z, hz, hnd⟩ := exists_pow_mul_not_dvd ξ hne
  refine ⟨m, n, b * t ^ m * s ^ n, z * w ^ n, ?_, ?_, ?_⟩
  · calc b * t ^ m = b * t ^ m * (t * s) ^ n := by rw [hs, one_pow, mul_one]
      _ = _ := by ring
  · have h2 : a ξ * a v * ι s = 1 := by rw [← map_mul a, ← hιt, ← map_mul, hs, map_one]
    have h3 : a v * a w = 1 := by rw [← map_mul, hw, map_one]
    rw [map_mul, h1, hz, map_mul, map_mul, map_pow, map_pow, map_pow]
    calc a ξ ^ n * a z * ι s ^ n = a ξ ^ n * a z * ι s ^ n * (a v * a w) ^ n := by
          rw [h3, one_pow, mul_one]
      _ = a z * a w ^ n * (a ξ * a v * ι s) ^ n := by ring
      _ = _ := by rw [h2, one_pow, mul_one]
  · intro h
    apply hnd
    have : z = z * w ^ n * v ^ n := by
      rw [mul_assoc, ← mul_pow, mul_comm w v, hw, one_pow, mul_one]
    rw [this]
    exact h.mul_right _

theorem exists_divide : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l), b ≠ 0 →
    ∃ (m n : ℕ) (b' : Per.Bcris l) (y : Per.BdRp l), b * C.tB ^ m = C.tB ^ n * b' ∧
      C.ι b' = algebraMap (Per.BdRp l) (Per.BdR l) y ∧ Per.θD l y ≠ 0 := by
  intro l _ C b hb
  have he := core_isEps l C
  obtain ⟨hF, -, hc, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨ht, h1, h2, -⟩ := core_t_unit_fil l C
  obtain ⟨-, hk, hu, -⟩ := thetaD_props l
  have hinj := (ULaws.u_laws l C).2.2.2.1
  have hD := (BdRField.bdR_isField l).2.2.2 C.ε he
  have hθ : ∀ y : Per.BdRp l, ¬ aDp l (xi C.ε) ∣ y → Per.θD l y ≠ 0 := fun y hy h =>
    hy (by simpa only [pow_one] using (hF 1 y).1 ((hk y).1 h))
  obtain ⟨v, hv⟩ := (hF 1 _).1 h1
  rw [pow_one] at hv
  have hvu : IsUnit v := by
    apply hu
    apply hθ
    rintro ⟨w, hw⟩
    apply h2
    refine (hF 2 _).2 ⟨w, ?_⟩
    rw [hv, hw, pow_two, mul_assoc]
  haveI := hc.toIsHausdorff
  obtain ⟨m, n, b', y, e1, e2, e3⟩ := abstract C.ι (algebraMap (Per.BdRp l) (Per.BdR l)) hinj
    (aDp l (xi C.ε)) v hvu C.tB ht (by rw [← hv]; exact C.ι_j C.t) hD b hb
  exact ⟨m, n, b', y, e1, e2, hθ y e3⟩

end GlobalTheory.MemLoc.RegDivide
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem regular_of_full : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), (∀ b : Per.Bcris l, b ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b) → C.Regular := by
  intro l _ C H K b hb hx
  classical
  have hK := K.2
  have hidx : (GK K).index ≠ 0 := by
    rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  have hfin : Fintype (GQ l ⧸ GK K) := Subgroup.fintypeOfIndexNeZero hidx
  have hmul : ∀ (g h : GQ l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x) :=
    (ActLaws.act_laws l).1
  have hone : ∀ x : Per.Bcris l, Per.σB (1 : GQ l) x = x := (ActLaws.act_laws l).2.1
  have hinv : ∀ (g : GQ l) (x : Per.Bcris l), Per.σB g⁻¹ (Per.σB g x) = x := fun g x => by
    rw [← hmul, inv_mul_cancel, hone]
  have hfix : ∀ (g : GQ l) (x : ℚ_[l]), Per.σB g (C.qB x) = C.qB x := fun g x =>
    (ULaws.u_laws l C).2.1 g _ _ (g.commutes x)
  have hD : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain
  have hB : IsDomain (Per.Bcris l) := (ULaws.u_laws l C).2.2.2.1.isDomain C.ι
  have fout : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * Per.σB (g : GQ l ⧸ GK K).out b := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    obtain ⟨x, hx'⟩ := hx (h : GQ l)⁻¹ (inv_mem h.2)
    refine ⟨x, ?_⟩
    rw [← hfix (g : GQ l ⧸ GK K).out x, ← map_mul, ← hx', ← hmul, hh, mul_inv_cancel_right]
  choose c hc using fout
  have hP : IsUnit (∏ q : GQ l ⧸ GK K, Per.σB q.out b) := by
    refine H _ (Finset.prod_ne_zero_iff.2 fun q _ h0 => hb ?_) fun g => ⟨∏ q : GQ l ⧸ GK K, c (g * q.out), ?_⟩
    · rw [← hinv q.out b, h0, map_zero]
    · rw [map_prod, map_prod,
        ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ GK K => Per.σB q.out b,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun q _ => ?_
      have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ GK K) := by
        rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      rw [e, ← hmul, ← hc]
  have hu := isUnit_of_dvd_unit
    (Finset.dvd_prod_of_mem (fun q : GQ l ⧸ GK K => Per.σB q.out b) (Finset.mem_univ ((1 : GQ l) : GQ l ⧸ GK K))) hP
  have := hu.map (Per.σB (((1 : GQ l) : GQ l ⧸ GK K).out)⁻¹)
  rwa [hinv] at this

end GlobalTheory.MemLoc
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLink.adm5_tab | exact GlobalTheory.NLink.adm5_tab | (intros; apply GlobalTheory.NLink.adm5_tab <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab | exact GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab | (intros; apply GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.smallPrimeLengthBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree | exact GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree | (intros; apply GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree <;> assumption)
end
