module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle515
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialExistsUniqueCyclotomicLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
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
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

@[expose] public section

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (π₀ : CuspSub E a) (ω : HChar E),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧ π₀.IsUnitary ∧
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, HasSatGL w.1 (π₀.locRep w.1) (Finset.univ.val.map (α w)) := by
  first | (exact @GlobalTheory.BumpData.bumpData) | (exact GlobalTheory.BumpData.bumpData) | (intros; apply GlobalTheory.BumpData.bumpData  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem Fits.invB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvB := by
  intro K b hb
  set b' : P.R.B := T.eB.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actB g b' = b' := by
    intro g
    rw [P.PD_actB]
    apply T.eB.injective
    rw [T.actB, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invB b' hfix
  refine ⟨IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c, (inf_le_left : K0 K ≤ K.1) c.2, ?_⟩
  rw [← hF.u]
  have : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem Fits.invdR {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvdR := by
  intro K b hb
  set b' : P.R.BdR := T.eD.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actdR g b' = b' := by
    intro g
    rw [P.PD_actdR]
    apply T.eD.injective
    rw [T.actD, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invdR b' hfix
  refine ⟨(c : Om l), c.2, ?_⟩
  rw [← hF.o]
  have : algebraMap (Om l) P.R.BdR (c : Om l) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem fits_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (C : Core l), Fits T C → C.InvB ∧ C.InvdR :=
  fun _ _ _ _ _ _ hF => ⟨hF.invB, hF.invdR⟩

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bcris_regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_tensorInj | exact GlobalTheory.MemLoc.regular_of_tensorInj | (intros; apply GlobalTheory.MemLoc.regular_of_tensorInj <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem mem_N_iff_of_points (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (P : ZMod n → LL → Prop) (Φ : ZMod n → LL → Prop)
    (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T)
    (hkey : ∀ i ζ, P i ζ → (Φ i ζ ↔ ∀ j, nb.repr ⟨W.Q ^ k • x, hx⟩ j ∈ van W i ζ k))
    (hQ : ∀ i ζ, P i ζ → ∃ w : PowerSeries LL, W.lev i ζ W.Q = PowerSeries.X * w)
    (hdiv : ∀ a : LetA O n, (∀ i ζ, P i ζ → a ∈ van W i ζ k) → W.Q ^ k ∣ a)
    (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    x ∈ W.N T ↔ ∀ i ζ, P i ζ → Φ i ζ := by
  constructor
  · intro hxN i ζ hζ
    rw [hkey i ζ hζ]
    intro j
    have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • (⟨x, hxN⟩ : ↥(W.N T)) := rfl
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨w, hw⟩ := hQ i ζ hζ
    refine Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)
    rw [map_mul, map_pow, hw]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  · intro H
    have hd : ∀ j, W.Q ^ k ∣ nb.repr ⟨W.Q ^ k • x, hx⟩ j := fun j =>
      hdiv _ (fun i ζ hζ => (hkey i ζ hζ).1 (H i ζ hζ) j)
    choose b hb using hd
    let z : ↥(W.N T) := ∑ j, b j • nb j
    have hz : W.Q ^ k • ((z : ↥(W.N T)) : W.DD T) = W.Q ^ k • x := by
      have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • z := by
        conv_lhs => rw [← nb.sum_repr ⟨W.Q ^ k • x, hx⟩]
        simp only [z, Finset.smul_sum, hb, mul_smul]
      exact (congrArg Subtype.val e).symm
    have hu : IsUnit (algebraMap (LetA O n) W.EE (W.Q ^ k)) := by
      rw [map_pow]
      exact hunit.pow k
    obtain ⟨u, hu'⟩ := hu
    have h1 : ∀ y : W.DD T, W.Q ^ k • y = (u : W.EE) • y := fun y => by
      rw [hu', algebraMap_smul]
    rw [h1, h1] at hz
    have hx' : x = (z : W.DD T) := by
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hz
      simp only [smul_smul, Units.inv_mul, one_smul] at this
      exact this.symm
    rw [hx']
    exact z.2

end Generic


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem mem_N_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  intro D HW F Cm l _ K s LL h W C T hT k x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  refine mem_N_iff_of_points W T nb (fun i ζ => IsPrimitiveRoot ζ (l ^ s)) _ k x hx ?_ ?_ ?_ ?_
  · intro i ζ hζ
    exact ((GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩
      (GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ)).2 _ nb).2.2 _ k
  · intro i ζ hζ
    obtain ⟨⟨w, _, hw⟩, -⟩ := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ
    exact ⟨w, hw⟩
  · exact (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).1 k
  · have h0 := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    simpa using h0

end GlobalTheory.NL.WachModulePoleQuotient
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.Approx

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_sum (e : PowerSeries L) (f : ℤ → M) (k : ℤ) (N : ℕ)
    (hN : ∀ j : ℕ, N ≤ j → f (k - j) = 0) :
    conv e f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j e • f (k - j) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hj (by rw [hN j (not_lt.1 hc), smul_zero])

theorem exists_bound {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (k : ℤ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → f (k - j) = 0 := by
  refine ⟨(k - m₀ + 1).toNat, fun j hj => hf _ ?_⟩
  have h1 := Int.self_le_toNat (k - m₀ + 1)
  have h2 : (((k - m₀ + 1).toNat : ℕ) : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  omega

theorem conv_add {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (e e' : PowerSeries L) :
    conv (e + e') f = conv e f + conv e' f := by
  funext k
  obtain ⟨N, hN⟩ := exists_bound hf k
  simp only [Pi.add_apply, conv_eq_sum _ f k N hN, map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem conv_smul {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (c : L) (e : PowerSeries L) :
    conv (c • e) f = c • conv e f := by
  funext k
  obtain ⟨N, hN⟩ := exists_bound hf k
  simp only [Pi.smul_apply, conv_eq_sum _ f k N hN, map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem conv_smul_add {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (c : L) (e e' : PowerSeries L) :
    conv (c • (e + e')) f = c • conv e f + c • conv e' f := by
  rw [conv_smul hf, conv_add hf, smul_add]

theorem conv_X_pow_mul {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (m : ℕ) (p : PowerSeries L)
    (k : ℤ) : conv (PowerSeries.X ^ m * p) f k = conv p f (k - m) := by
  obtain ⟨N, hN⟩ := exists_bound hf (k - m)
  have hN' : ∀ j : ℕ, m + N ≤ j → f (k - j) = 0 := by
    intro j hj
    have := hN (j - m) (by omega)
    rwa [show k - (m : ℤ) - ((j - m : ℕ) : ℤ) = k - j by push_cast [show m ≤ j by omega]; ring] at this
  rw [conv_eq_sum _ f k _ hN', conv_eq_sum _ f (k - m) N hN, Finset.sum_range_add]
  rw [Finset.sum_eq_zero, zero_add]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), show m + j - m = j by omega]
    congr 2
    push_cast
    ring
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]

theorem combine {ι : Type} [Fintype ι] (F : ι → ℤ → M) (m₀ : ι → ℤ) (hbd : ∀ j, ∀ k < m₀ j, F j k = 0)
    (c : L) (e p : ι → PowerSeries L) (m : ℕ) (k : ℤ) :
    (∑ j, conv (c • (e j + PowerSeries.X ^ m * p j)) (F j)) k - c • (∑ j, conv (e j) (F j)) k =
      (∑ j, c • conv (p j) (F j)) (k - m) := by
  simp only [fun j => conv_smul_add (hbd j) c (e j) (PowerSeries.X ^ m * p j), Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, Finset.sum_add_distrib, Finset.smul_sum, fun j => conv_X_pow_mul (hbd j) m (p j) k]
  abel

end Series


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem approx : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ g ∈ Lat C h T i ζ, ∀ m : ℕ, ∃ (n : ↥(W.N T)) (c : ↥LL.1), c ≠ 0 ∧ ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ n j - c • g j = f (j - m) := by
  intro D HW F Cm l _ K s LL h W C T hT i ζ hζ g hg m
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := ⟨s, hζ⟩
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hFull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ
  obtain ⟨hsm, hB⟩ := GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ hζ' hFull
  obtain ⟨-, hspan, -⟩ := hB _ nb
  obtain ⟨e, rfl⟩ := hspan g hg
  have hW := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).2.2.1 i ζ hζ'
  choose a c hc hdiv using fun j => hW (e j) m
  choose p hp using hdiv
  haveI := LL.2
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ↥(OL LL)) c
  have ho : ∀ j, ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = (b : ↥(OL LL)) • c j :=
    fun j => RingHom.mem_rangeS.1 (hb j)
  choose o ho using ho
  obtain ⟨cc, hccd⟩ : ∃ x : ↥LL.1, x = algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) := ⟨_, rfl⟩
  have hcc : cc ≠ 0 := hccd ▸ IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have ho' : ∀ j, algebraMap ↥(OL LL) ↥LL.1 (o j) = cc * c j := by
    intro j
    rw [ho j, hccd, Algebra.smul_def]
  choose m0 hm0 using fun j => (C.C K s LL h).tie.levB_supp T i ζ (nb j)
  have hlev : ∀ j, W.lev i ζ (o j • a j) = cc • (e j + PowerSeries.X ^ m * p j) := by
    intro j
    rw [map_smul, ← algebraMap_smul ↥LL.1 (o j), ho' j, mul_smul, ← hp j, add_sub_cancel]
  have hbd : ∀ j, ∀ k < m0 j, ex C h T i ζ (nb j) k = 0 := hm0
  have hexn : ex C h T i ζ (∑ j, (o j • a j) • nb j) =
      ∑ j, conv (cc • (e j + PowerSeries.X ^ m * p j)) (ex C h T i ζ (nb j)) := by
    have := map_sum ((C.C K s LL h).tie.levB T i ζ) (fun j => (o j • a j) • nb j) Finset.univ
    refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← hlev j]
    exact hsm _ _
  refine ⟨∑ j, (o j • a j) • nb j, cc, hcc, ∑ j, cc • conv (p j) (ex C h T i ζ (nb j)),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p j, nb j, rfl⟩),
    fun k => ?_⟩
  rw [hexn]
  exact combine _ m0 hbd cc e p m k

end GlobalTheory.NL.Approx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem min_jumpSum_le_of_pow_mem_of_inertia_eq_top : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B C : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) ≤ jumpSum (wild F L) ⊤ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B C h0 hE hcomm hpow
  by_cases hB : B = ⊤
  ·
    subst hB
    have hzero : jumpSum (wild F L) ⊤ (⊤ : Subgroup (L ≃ₐ[F] L)) = 0 := by
      simp [jumpSum]
    simp [hzero]
  ·
    obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hE
    have hcard : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = Nat.card (L ≃ₐ[F] L) := by
      rw [hram, h0]; simp
    have hnpos : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      exact_mod_cast Nat.card_pos

    obtain ⟨σ, hσ, hσB⟩ := GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' F L B h0 hB
    have hv : (0 : ℝ) ≤ (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      positivity

    obtain ⟨τ, hτ, hτC⟩ := GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator F L p e _ C hcomm hv he σ hσ

    have hτ' : τ ∉ C := by
      intro hτmem
      apply hσB
      apply hpow
      have hsplit : σ ^ p = τ * (τ⁻¹ * σ ^ p) := by group
      rw [hsplit]
      exact C.mul_mem hτmem hτC
    have key := GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem F L C _ h0 τ hτ hτ'
    have hR : ((min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) : ℕ) : ℝ)
        ≤ (jumpSum (wild F L) ⊤ C : ℝ) := by
      refine le_trans (le_of_eq ?_) key
      rw [mul_min_of_nonneg _ _ hnpos.le, hEe, hcard]
      push_cast
      congr 1
      · field_simp
      · field_simp
    exact_mod_cast hR

end GlobalTheory.PMon.Ram
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms : ∀ (l : ℕ) [Fact l.Prime] (h d : ℕ) (r : ℝ) (y : Fin d → ℕ → Fl l), 2 ≤ h → 0 ≤ r → r < 1 → (∀ a k, ‖sh (y a k)‖ ≤ r) → (∀ n : Fin d → ℕ, ‖sh (∑ a, n a • y a 0)‖ ≤ r ^ l ^ h → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  first | exact @GlobalTheory.PSer.Lam_indep_of_first_terms | exact GlobalTheory.PSer.Lam_indep_of_first_terms | (intros; apply GlobalTheory.PSer.Lam_indep_of_first_terms <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

theorem charpoly_redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (s : G D.host.E D.nd.Om) :
    Matrix.charpoly ((redF D i ρ s : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) := by
  rw [← Matrix.charpoly_map]
  rfl

end GlobalTheory.TypeLeaf
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_lower_comparison : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f, (1 - 1 / (g : ℝ)) * wtC L (eU g N ψ) f ≤ wtC L (eJ g N k s ψ) f := by
  first | exact @GlobalTheory.GLq.lowerWtComparison | exact GlobalTheory.GLq.lowerWtComparison | (intros; apply GlobalTheory.GLq.lowerWtComparison <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.dualExponential_existsUnique_cyclotomicLevel : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, (∀ z : GQ l → ℚ_[l], CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z → ∃ α ∈ Ks K s, ExpStar D.loc (Gj K s) e z α) ∧ ∀ (z : GQ l → ℚ_[l]) (α α' : Om l), α ∈ Ks K s → α' ∈ Ks K s → ExpStar D.loc (Gj K s) e z α → ExpStar D.loc (Gj K s) e z α' → α = α' := by
  first | exact @GlobalTheory.ExpDef.expStar_existsUnique | exact GlobalTheory.ExpDef.expStar_existsUnique | (intros; apply GlobalTheory.ExpDef.expStar_existsUnique <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.exists_tau_component_frame_of_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (τ : S.K →ₐ[S.Qp] S.LL), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ), (∀ u, u ∈ J → IsJumpV S.PD T.ρ τ u) ∧ {u | IsJumpV S.PD T.ρ τ u}.Finite ∧ Frame (D.loc l).χQ K (mN l s (M0 + h0)) U g ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K (mN l s (M0 + h0))) U (J : Set ℤ) ∧ (∀ σ ∈ Gj K (mN l s (M0 + h0)), Pm * M σ = U σ * Pm.map ((D.locA l).actC σ)) ∧ ball l r ⊆ Pm.mulVec '' ball l d ∧ (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧ ∀ y : Fin d → ℚ_[l], Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d → ∀ a, ‖y a‖ ≤ 1 := by
  first | exact @GlobalTheory.TauFrame.exists_tau_frame | exact GlobalTheory.TauFrame.exists_tau_frame | (intros; apply GlobalTheory.TauFrame.exists_tau_frame <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ), (∀ χ : Gn g n → ℂ, IsIrr χ → ∃! f, HasLabel L χ f) ∧ (∀ (χ : Gn g n → ℂ) f, HasLabel L χ f → f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1)) ∧ ((Q.map Prod.fst : List _) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f ∧ degL (Q.map Prod.snd) = n ∧ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} = {hcL (Q.map Prod.snd) n} := by
  first | exact @GlobalTheory.GLq.Label.label_main | exact GlobalTheory.GLq.Label.label_main | (intros; apply GlobalTheory.GLq.Label.label_main <;> assumption)
end
