module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallySubMemPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle627
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle260
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_coord_acris_bcris_alt : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l]), (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ (ΦA : TW (OCr l O) T →+ Per.Acris l) (ΦB : TW (OB l O) T →+ Per.Bcris l), (∀ (a : Per.Acris l) (w : TW (OCr l O) T), ΦA (((1 : O) ⊗ₜ[ℤ_[l]] a : OCr l O) • w) = a * ΦA w) ∧ (∀ (y : Per.Bcris l) (w : TW (OB l O) T), ΦB (((1 : O) ⊗ₜ[ℤ_[l]] y : OB l O) • w) = y * ΦB w) ∧ (∀ x : ↥T.L.T, ΦB ((1 : OB l O) ⊗ₜ[O] x) = algebraMap ℤ_[l] (Per.Bcris l) (φ x)) ∧ (∀ (N : ℕ) (w : TW (OCr l O) T), ΦA (((l : O) ^ N) • w) = (l : Per.Acris l) ^ N * ΦA w) ∧ (∀ w : TW (OCr l O) T, ΦB (TWincl (toOB l O) T w) = acrisToBcris l (ΦA w)) := by
  first | exact @GlobalTheory.exists_coord_acris_bcris | exact GlobalTheory.exists_coord_acris_bcris | (intros; apply GlobalTheory.exists_coord_acris_bcris <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_smul_eq_acrisLattice_image : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T), ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ β : TW (OCr l O) T, ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) • b = TWincl (toOB l O) T β := by
  first | exact @GlobalTheory.DenomCris.exists_smul_eq_TWincl | exact GlobalTheory.DenomCris.exists_smul_eq_TWincl | (intros; apply GlobalTheory.DenomCris.exists_smul_eq_TWincl <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.one_tmul_injective_locLat : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O), Function.Injective fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.TensorOneInj.tensor_one_injective | exact GlobalTheory.TensorOneInj.tensor_one_injective | (intros; apply GlobalTheory.TensorOneInj.tensor_one_injective <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.OCrCont

open Filter Topology

theorem galOCr_sub_smul_eventually {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    (r : OCr l O) (m : ℕ) :
    ∀ᶠ h in nhds (1 : GQ l), ∃ w : OCr l O, galOCr O h r - r = ((l : O) ^ m) • w := by
  induction r using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun h => ⟨0, by simp⟩
  | tmul o a =>
    filter_upwards [GlobalTheory.AcrisGal.galC_sub_dvd_mem_nhds l a m] with h hh
    obtain ⟨c, hc⟩ := hh
    refine ⟨o ⊗ₜ c, ?_⟩
    have e1 : galOCr O h (o ⊗ₜ[ℤ_[l]] a) = o ⊗ₜ galC h a := rfl
    rw [e1, ← TensorProduct.tmul_sub, hc, TensorProduct.smul_tmul', smul_eq_mul]
    have e2 : ((l : Per.Acris l) ^ m * c) = ((l : ℤ_[l]) ^ m) • c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [e2, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow, map_natCast]
  | add x y hx hy =>
    filter_upwards [hx, hy] with h ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), smul_add, ← hu, ← hv]; abel

theorem twact_sub_smul_eventually : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]
    (s : G →* GQ l), Continuous s → ∀ (T : LocLat G ℚ_[l] K O),
    (∀ t ∈ T.L.T, ∀ m : ℕ, ∀ᶠ g in nhds (1 : G), ∃ t' ∈ T.L.T, T.ρ g t - t = ((l : O) ^ m) • t') →
    ∀ (β : TW (OCr l O) T) (m : ℕ), ∀ᶠ g in nhds (1 : G), ∃ γ : TW (OCr l O) T,
      TWact (galOCr O (s g)) T g β - β = ((l : O) ^ m) • γ := by
  intro l _ O K _ _ _ _ _ _ G _ _ s hs T hT β m
  have hts : Tendsto s (nhds 1) (nhds 1) := by
    simpa [map_one] using hs.tendsto (1 : G)
  induction β using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun g => ⟨0, by simp⟩
  | tmul r t =>
    filter_upwards [hts.eventually (galOCr_sub_smul_eventually r m), hT t.1 t.2 m] with g ⟨w, hw⟩ ⟨t', ht', htt⟩
    refine ⟨w ⊗ₜ T.actT g t + r ⊗ₜ ⟨t', ht'⟩, ?_⟩
    have e1 : TWact (galOCr O (s g)) T g (r ⊗ₜ[O] t) = galOCr O (s g) r ⊗ₜ T.actT g t := rfl
    have e2 : T.actT g t - t = ((l : O) ^ m) • (⟨t', ht'⟩ : ↥T.L.T) := Subtype.ext (by
      rw [Submodule.coe_sub, Submodule.coe_smul]; exact htt)
    have e3 : galOCr O (s g) r ⊗ₜ[O] T.actT g t - r ⊗ₜ[O] t
        = (galOCr O (s g) r - r) ⊗ₜ[O] T.actT g t + r ⊗ₜ[O] (T.actT g t - t) := by
      rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
    rw [e1, e3, hw, e2, smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  | add x y hx hy =>
    filter_upwards [hx, hy] with g ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), smul_add, ← hu, ← hv]; abel

end GlobalTheory.OCrCont
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.FrobCong

theorem sigma_eq_pow_add (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  have h0 : sigma l a w - w ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow]
    simp [WittVector.constantCoeff_apply, coeff_sigma]
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨x, by rw [mul_comm, hx]; ring⟩

end GlobalTheory.FrobCong
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  first | exact @GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem | exact GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem | (intros; apply GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_action_cyclotomic_power : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l), ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  first | exact @GlobalTheory.BKReal.gal_wA_pow | exact GlobalTheory.BKReal.gal_wA_pow | (intros; apply GlobalTheory.BKReal.gal_wA_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_root_of_unity_kummer_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  first | exact @GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf | exact GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf | (intros; apply GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.le_adjoin_compatibleRoots_of_finite_kummerTower : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (ϖ : PiSys l e) (F : IntermediateField ℚ_[l] (Om l)), FiniteDimensional ℚ_[l] F → F ≤ ϖ.Kinf → ∃ n : ℕ, F ≤ IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  first | exact @GlobalTheory.KinfFin.main | exact GlobalTheory.KinfFin.main | (intros; apply GlobalTheory.KinfFin.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_pow_ramifiedUniformizerField_zpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Om l), y ∈ (ϖ.field a).1 → y ≠ 0 → ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  first | exact @GlobalTheory.ValGroupKprime.norm_pow_field | exact GlobalTheory.ValGroupKprime.norm_pow_field | (intros; apply GlobalTheory.ValGroupKprime.norm_pow_field <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_galois_prescribed_unramified_kummer : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ (m : ZMod a) (ζ : Om l), ζ ^ e = 1 → ∃ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val) ∧ g (ϖ.seq 0) = ζ * ϖ.seq 0 := by
  first | exact @GlobalTheory.TameFrob.exists_cover | exact GlobalTheory.TameFrob.exists_cover | (intros; apply GlobalTheory.TameFrob.exists_cover <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem placesOk_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), q0.Prime → (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≡ 1 [MOD H.QS * H.q * H.d]) → (∀ k, q0 ≠ H.g k) → q0 ≠ H.pde → q0 ≠ H.pde' → OverP H q0 w0 → PlacesOk H q0 w0 ∧ 5 ≤ q0 := by
  intro R H q0 w0 hq hmod hg hp hp' hw
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := by
    intro p h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    exacts [H.g_prime 0, H.g_prime 1, H.pde_prime, H.pde'_prime, hq]
  have h4 : (4 : ℕ) ∣ H.QS * H.q * H.d := (by norm_num : 4 ∣ 16).trans H.sixteen_dvd_condN
  have h5 : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], 5 ≤ p := by
    intro p h
    have h1 : p % 4 = 1 % 4 := (hmod p h).of_dvd h4
    have h2 := (hprime p h).two_le
    omega
  refine ⟨⟨hw, ?_, fun p h => ?_⟩, h5 q0 (by simp)⟩
  · have a1 := H.g_ne
    have a2 := H.pde_ne
    have a3 := H.pde_ne_g 0
    have a4 := H.pde_ne_g 1
    have a5 := hg 0
    have a6 := hg 1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    omega
  · have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p (hprime p h) (hmod p h)
    have := h5 p h
    refine ⟨hprime p h, by omega, ?_, fun P hP => (GlobalTheory.Mem.Chr.splitsC_main R H p (hprime p h) hs P hP).1⟩
    exact GlobalTheory.SplitEmbSep.not_dvd_discr_of_split (hprime p h) _
      ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver (hprime p h)).symm.trans hs)

end GlobalTheory.LamTie
end
