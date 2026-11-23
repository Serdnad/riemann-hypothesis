module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallySubMemPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersPowersOfOmega
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle685
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle676
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle688
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : GlobalTheory.BKGal.QLat LL)
      (Pl : LocPrime l) (AI : LocAinf l Pl), GlobalTheory.Per.IsStd Pl AI →
      ∃ β : TW (GlobalTheory.BKReal.OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B,
        (∀ x : ↥T.L.T,
          β ((1 : GlobalTheory.BKReal.OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) =
            (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) ∧
        (∀ g b, β (GlobalTheory.BKGal.actB (GlobalTheory.BKGal.sQ l) T g b) =
          actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b)) ∧
        (∀ b, β (TWmap (GlobalTheory.BKReal.frobOB l ↥(OL LL)) T b) =
          φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (β b)) ∧
        ∀ c ∈ continuousCocycles T.ρ,
          c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔
            ∃ b, GlobalTheory.BKGal.IsCobOf (GlobalTheory.BKGal.sQ l) T b c := by
  exact @GlobalTheory.BKGal.CrisTensor.exists_equiv
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleCont

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]

theorem twact_smul {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : R) (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWact, TensorProduct.smul_tmul', TensorProduct.map_tmul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem twincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWincl, TensorProduct.smul_tmul', TensorProduct.map_tmul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem twact_incl (T : LocLat G ℚ_[l] K O) (h : GQ l) (g : G) (z : TW (OCr l O) T) :
    TWact (galOB O h) T g (TWincl (toOB l O) T z) = TWincl (toOB l O) T (TWact (galOCr O h) T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWact, TWincl, TensorProduct.map_tmul, galOB_toOB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem natCast_pow_smul {O K : Type} [CommRing O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K]
    (T : LocLat G ℚ_[l] K O) (k : ℕ) (v : T.V) : ((l : O) ^ k) • v = ((l : K) ^ k) • v := by
  rw [← algebraMap_smul K, map_pow, map_natCast]

theorem main_gen {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (s : G →* GQ l) (hs : Continuous s) (T : LocLat G ℚ_[l] K O) (hK : (l : K) ≠ 0)
    (hcont : ∀ (β : TW (OCr l O) T) (m : ℕ), ∀ᶠ g in nhds (1 : G), ∃ γ : TW (OCr l O) T,
      TWact (galOCr O (s g)) T g β - β = ((l : O) ^ m) • γ)
    (hden : ∀ v : T.V, ∃ n : ℕ, ∃ x ∈ T.L.T, x = ((l : O) ^ n) • v)
    (hmem : ∀ (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) →
      ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y)
    (b : TW (OB l O) T) (c : G → T.V) (hc : IsCobOf s T b c) (m : ℕ) :
    ∀ᶠ g in nhds (1 : G), ∃ x ∈ T.L.T, c g = ((l : O) ^ m) • x := by
  obtain ⟨s0, hs0, β, hβ⟩ := GlobalTheory.T.exists_smul_eq_acrisLattice_image T b
  obtain ⟨C, hC⟩ := GlobalTheory.T.acris_lpow_dvd_bound_teichmullerMonoid l (s0 * s0) (by rw [map_mul]; exact mul_ne_zero hs0 hs0)
  set a : Per.Acris l := ainfToAcris l s0 with ha
  set m' := m + C + 1 with hm'
  have h2 : ∀ᶠ g in nhds (1 : G), (l : Per.Acris l) ^ m' ∣ galC (s g) a - a := by
    have h := GlobalTheory.AcrisGal.galC_sub_dvd_mem_nhds l a m'
    rw [← map_one s] at h
    exact hs.continuousAt.preimage_mem_nhds h
  filter_upwards [hcont β m', h2] with g ⟨γ, hγ⟩ ⟨w, hw⟩
  obtain ⟨n, x, hxT, hx⟩ := hden (c g)
  have hcob := hc g n ⟨x, hxT⟩ (by show x = _; rw [hx, ← algebraMap_smul K, map_pow, map_natCast])
  have hconv : ∀ (k : ℕ) (v : T.V), ((l : O) ^ k) • v = ((l : K) ^ k) • v := fun k v => by
    rw [← algebraMap_smul K, map_pow, map_natCast]
  set x' : ↥T.L.T := ⟨x, hxT⟩ with hx'
  set ga : Per.Acris l := galC (s g) a with hga
  set σA : OCr l O := (1 : O) ⊗ₜ[ℤ_[l]] a with hσA
  set gσA : OCr l O := (1 : O) ⊗ₜ[ℤ_[l]] ga with hgσA
  have hgσA' : galOCr O (s g) σA = gσA := rfl
  set σ : OB l O := toOB l O σA with hσ
  set gσ : OB l O := toOB l O gσA with hgσ
  have hgσ' : galOB O (s g) σ = gσ := by rw [hσ, galOB_toOB, hgσA']
  have hβ' : σ • b = TWincl (toOB l O) T β := hβ
  set gβ := TWact (galOCr O (s g)) T g β with hgβ
  have key1 : gσ • actB s T g b = TWincl (toOB l O) T gβ := by
    rw [actB, ← hgσ', ← twact_smul, hβ', twact_incl]
  have key : (σ * gσ) • ((1 : OB l O) ⊗ₜ[O] x') = TWincl (toOB l O) T (((l : O) ^ n) • (σA • gβ - gσA • β)) := by
    rw [hcob, smul_comm, map_smul, map_sub, twincl_smul, twincl_smul, ← hσ, ← hgσ, smul_sub, mul_smul, key1,
      mul_comm, mul_smul, hβ']
  have hfin : ∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ X : Per.Acris l, a * a * algebraMap ℤ_[l] (Per.Acris l) (φ x') =
      (l : Per.Acris l) ^ (n + m') * X - (l : Per.Acris l) ^ m' * (a * w * algebraMap ℤ_[l] (Per.Acris l) (φ x')) := by
    intro φ hφ
    obtain ⟨ΦA, ΦB, hA, hB, h1, hN, hI⟩ := GlobalTheory.T.exists_coord_acris_bcris_alt T φ hφ
    have hσσ : σ * gσ = (1 : O) ⊗ₜ[ℤ_[l]] (acrisToBcris l a * acrisToBcris l ga) := by
      rw [hσ, hgσ, hσA, hgσA]
      simp only [toOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e1 := congrArg ΦB key
    rw [hσσ, hB, h1, hI, hN, map_sub, hA, hA] at e1
    have hΦ : ΦA gβ - ΦA β = (l : Per.Acris l) ^ m' * ΦA γ := by rw [← map_sub, hγ, hN]
    have heq : a * ga * algebraMap ℤ_[l] (Per.Acris l) (φ x') = (l : Per.Acris l) ^ n * (a * ΦA gβ - ga * ΦA β) := by
      have hinj : Function.Injective (acrisToBcris l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
      apply hinj
      have := e1
      simp only [map_mul, AlgHom.commutes] at this ⊢
      exact this
    refine ⟨a * ΦA γ - w * ΦA β, ?_⟩
    linear_combination heq - (a * algebraMap ℤ_[l] (Per.Acris l) (φ x')) * hw + ((l : Per.Acris l) ^ n * a) * hΦ - ((l : Per.Acris l) ^ n * ΦA β) * hw
  have hdiv : ∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ (n + m) ∣ φ x' := by
    intro φ hφ
    by_cases hz : φ x' = 0
    · rw [hz]; exact dvd_zero _
    have hspec := PadicInt.unitCoeff_spec hz
    suffices hv : n + m ≤ (φ x').valuation by
      rw [hspec]
      exact Dvd.dvd.mul_left (pow_dvd_pow _ hv) _
    by_contra hlt
    push_neg at hlt
    obtain ⟨X, hX⟩ := hfin φ hφ
    set v := (φ x').valuation
    have hzA : algebraMap ℤ_[l] (Per.Acris l) (φ x') =
        algebraMap ℤ_[l] (Per.Acris l) (PadicInt.unitCoeff hz : ℤ_[l]) * (l : Per.Acris l) ^ v := by
      conv_lhs => rw [hspec]
      rw [map_mul, map_pow, map_natCast]
    have hd : (l : Per.Acris l) ^ (min (n + m') (m' + v)) ∣ ainfToAcris l (s0 * s0) * algebraMap ℤ_[l] (Per.Acris l) (φ x') := by
      rw [map_mul, ← ha, hX]
      refine Dvd.dvd.sub (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_left _ _)) _) ?_
      refine (pow_dvd_pow _ (min_le_right _ _)).trans ?_
      rw [hzA, pow_add]
      exact ⟨a * w * algebraMap ℤ_[l] (Per.Acris l) (PadicInt.unitCoeff hz : ℤ_[l]), by ring⟩
    have := hC (φ x') _ hz hd
    omega
  obtain ⟨y, hyT, hy⟩ := hmem x' (n + m) hdiv
  refine ⟨y, hyT, ?_⟩
  have h3 : ((l : K) ^ n) • c g = ((l : K) ^ n) • (((l : O) ^ m) • y) := by
    rw [← hconv, ← hconv, ← mul_smul, ← pow_add]
    exact hx.symm.trans hy
  exact smul_right_injective T.V (pow_ne_zero n hK) h3



theorem cont_at_one : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := by
  intro l _ _ LL T b c hc m
  have hK : (l : ↥LL.1) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] ↥LL.1)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  refine (main_gen (sQ l) continuous_subtype_val T hK (GlobalTheory.T.twistedAction_acrisTensor_sub_eventually_lpow (sQ l) continuous_subtype_val T ?hT) ?hD
    (GlobalTheory.T.mem_pow_smul_lattice_of_coord_dvd T) b c hc m).mono ?fin
  case fin =>
    rintro g ⟨x, hx, e⟩
    exact ⟨x, hx, e.trans (natCast_pow_smul T m x)⟩
  case hT =>
    intro t ht k
    filter_upwards [GlobalTheory.T.galoisLattice_sub_mem_pow_smul_eventually l LL T t ht k] with g ⟨t', ht', e⟩
    exact ⟨t', ht', e.trans (natCast_pow_smul T k t').symm⟩
  case hD =>
    intro v
    obtain ⟨n, x, hx, e⟩ := GlobalTheory.T.exists_pow_smul_mem_galoisStableLattice_Ql l LL T v
    exact ⟨n, x, hx, e.trans (natCast_pow_smul T n v).symm⟩

end GlobalTheory.CocycleCont
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots : ∀ (l : ℕ) [Fact l.Prime], (∃ ε : OCb l, IsEps ε) ∧ ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∃ ξ : Ainf l, Ideal.span {ξ} = RingHom.ker (Per.θ l) ∧ muOf ε = ξ * muOf δ) ∧ WittVector.frobenius (muOf δ) = muOf ε ∧ Per.θ l (muOf δ) ≠ 0 ∧ IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) ∧ IsUnit (inclW l (muOf ε)) ∧ (∀ g : GQ l, ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε) ∧ ∀ x : OCb l, x.untilt = 1 → muOf ε ∣ muOf x := by
  first | exact @GlobalTheory.MuOfEps.main | exact GlobalTheory.MuOfEps.main | (intros; apply GlobalTheory.MuOfEps.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.EpsilonAssociated

theorem isEps_bk {l : ℕ} [Fact l.Prime] {e : OCb l} (h : IsEps e) : GlobalTheory.BKGal.IsEps e :=
  ⟨h.1, (frobeniusEquiv (OCb l) l).symm e, frobeniusEquiv_symm_pow_p (OCb l) l e, h.2⟩

theorem mu_associated : ∀ (l : ℕ) [Fact l.Prime] (e e' : OCb l), IsEps e → IsEps e' →
    Associated (mu e) (mu e') := by
  intro l _ e e' he he'
  have h1 : mu e ∣ mu e' := GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he) he'.1
  have h2 : mu e' ∣ mu e := GlobalTheory.MuOfEps.muOf_dvd (isEps_bk he') he.1
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hne : mu e ≠ 0 := GlobalTheory.MuOfEps.muOf_ne_zero (isEps_bk he)
  have hab : a * b = 1 := by
    have h3 : (a * b - 1) * mu e = 0 := by
      have : mu e = mu e * a * b := by rw [← ha]; exact hb
      linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

end GlobalTheory.EpsilonAssociated
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.theoremT_descend_smaller_coefficients : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  first | exact @GlobalTheory.BaseCoef.thmT_descend | exact GlobalTheory.BaseCoef.thmT_descend | (intros; apply GlobalTheory.BaseCoef.thmT_descend <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tame_type_of_extension_lattice : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL) (Sig : Finset (ZMod e)), (0 : ZMod e) ∈ Sig → TameType a ϖ Pl T Sig → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → TameType a ϖ Pl (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) Sig := by
  first | exact @GlobalTheory.TameExt.tameType_extLat | exact GlobalTheory.TameExt.tameType_extLat | (intros; apply GlobalTheory.TameExt.tameType_extLat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tame_inertia_characters_powers_of_omega : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ w ^ e = 1) ∧ (∃ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ IsPrimitiveRoot w e) ∧ ∀ (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → Nat.Coprime (orderOf χ) l → (∀ (Fr : Gl l), (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Fr : GQ l) x - x ^ l‖ < 1) → ∀ g h : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (g : Gl l) = Fr⁻¹ * h * Fr → χ h = χ g ^ l) ∧ (χ ^ e = 1 → ∃ c : ZMod e, ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (w : ↥LL.1), (w : Om l) * ϖ.seq 0 = ((g : Gl l) : GQ l) (ϖ.seq 0) → (χ g : ↥LL.1) = w ^ c.val) := by
  first | exact @GlobalTheory.TameIner.main | exact GlobalTheory.TameIner.main | (intros; apply GlobalTheory.TameIner.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.GKinfStable
variable {l : ℕ} [hl : Fact l.Prime]

theorem map_field_le (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l)
    {x : Om l} (hx : x ∈ (ϖ.field a).1) : g x ∈ (ϖ.field a).1 := by
  have hd : e ∣ l ^ a - 1 := ⟨1, by omega⟩
  have := ϖ.isGalois_field a hd
  exact (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g) ⟨x, hx, rfl⟩

theorem conj_mem (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∀ h ∈ GK (ϖ.field a), g⁻¹ * h * g ∈ GK (ϖ.field a) := by
  intro h hh
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh (g x) (map_field_le a e ϖ he g hx)
  simp only [AlgEquiv.mul_apply, h1]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem res_exists (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∃ σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a)),
      ∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l) := by
  let F := (ϖ.field a).1
  let φ : ↥F →ₐ[ℚ_[l]] ↥F :=
    { toFun := fun y => ⟨g y, map_field_le a e ϖ he g y.2⟩
      map_one' := Subtype.ext (map_one g : g (1 : Om l) = 1)
      map_mul' := fun y z => Subtype.ext (map_mul g (y : Om l) (z : Om l))
      map_zero' := Subtype.ext (map_zero g : g (0 : Om l) = 0)
      map_add' := fun y z => Subtype.ext (map_add g (y : Om l) (z : Om l))
      commutes' := fun q => Subtype.ext (g.commutes q) }
  refine ⟨{ toFun := fun x => ⟨φ x, x.2.map (φ.restrictScalars ℤ_[l])⟩
            map_one' := Subtype.ext (map_one φ : φ (1 : ↥F) = 1)
            map_mul' := fun y z => Subtype.ext (map_mul φ (y : ↥F) (z : ↥F))
            map_zero' := Subtype.ext (map_zero φ : φ (0 : ↥F) = 0)
            map_add' := fun y z => Subtype.ext (map_add φ (y : ↥F) (z : ↥F)) }, fun x => rfl⟩

theorem kappa_act {LL : FinExt l} (T : QLat LL) (g : Gl l) (z : letI := zlLat T; WCb l ⊗[ℤ_[l]] ↥T.L.T) :
    letI := zlLat T
    TWact (galOW (↥(OL LL)) (sQ l g)) T g (kappa T z) =
      kappa T (TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) z) := by
  letI := zlLat T
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actZ_mul_apply {LL : FinExt l} (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T g (actZ T h x) = actZ T (g * h) x :=
  Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g h) (x : T.V)).symm

theorem actZ_one_apply {LL : FinExt l} (T : QLat LL) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T 1 x = x :=
  Subtype.ext (LinearMap.congr_fun (map_one T.ρ) (x : T.V))

end GlobalTheory.GKinfStable


open GlobalTheory.GKinfStable in
theorem GlobalTheory.GKinfStable.main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v' := by
  intro BS l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK g γ hcov v hv
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := ↥LL.1)
  choose σ hσ using res_exists (l := l) a e ϖ he (sQ l g)
  choose ψ hψ using GlobalTheory.T.covers_tame_acts_ringEndo_wittPowerSeries a e ϖ LL (sQ l g) γ hcov
  choose H hH using GlobalTheory.T.breuilKisinPrism_galoisLift_isPrismHom a e ϖ (sQ l g) σ hσ ψ hψ
  letI := zlLat T
  obtain ⟨E, j, hR, hiff⟩ := hBK
  let ρg : ↥T.L.T ≃ₗ[ℤ_[l]] ↥T.L.T :=
    LinearEquiv.ofLinear (actZ T g) (actZ T g⁻¹)
      (LinearMap.ext fun x => (actZ_mul_apply T g g⁻¹ x).trans
        ((congrArg (fun k => actZ T k x) (mul_inv_cancel g)).trans (actZ_one_apply T x)))
      (LinearMap.ext fun x => (actZ_mul_apply T g⁻¹ g x).trans
        ((congrArg (fun k => actZ T k x) (inv_mul_cancel g)).trans (actZ_one_apply T x)))
  have hPR := GlobalTheory.T.realisesEtaleFCrystal_pullback_galois (ϖ.field a) E ↥T.L.T _ j hR (sQ l g) σ hσ
    (conj_mem (l := l) a e ϖ he (sQ l g)) ρg (fun h h' hh x => by
      have e2 : g * inclG (ϖ.field a) h' = inclG (ϖ.field a) h * g := by
        rw [show inclG (ϖ.field a) h' = g⁻¹ * inclG (ϖ.field a) h * g from Subtype.ext hh]
        group
      exact (actZ_mul_apply T g _ x).trans ((congrArg (fun k => actZ T k x) e2).trans
        (actZ_mul_apply T _ g x).symm))
  choose gH j' hgH hR' hj' using hPR
  have hBS := (BS l (ϖ.field a) (ainfObj _) (ainfId _) (isAinf_ainfObj _)).2 ↥T.L.T ↥T.L.T _ _
    (E.pullback σ) E j' j hR' hR LinearMap.id (fun _ _ => rfl)
  choose u hu using hBS.exists
  have hx := (hiff (I.j (toW (thetaW a LL) ϖ P v))).2 ⟨v.1, hv, rfl⟩
  choose x hx using hx
  have hm := (hiff (kappa T (j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x)))))).1 ⟨_, rfl⟩
  choose m' hm' hm'eq using hm
  have e1 : gH.comp (ϖ.toAinf a) = ((ϖ.toAinf a).restrict σ).comp H :=
    Hom.ext' (RingHom.ext fun y => by
      change gH.f (ϖ.ev a y) = ϖ.ev a (H.f y)
      rw [hH]
      exact (hgH _).trans (hψ y).symm)
  have key : TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) (j (E.tr (ϖ.toAinf a) x)) =
      j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x))) := by
    have h2 : j (u.u (ainfObj _) ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x))) =
        j' ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x)) := by
      refine (hu _).trans ?_
      exact LinearMap.lTensor_id_apply _ _ _
    refine (hj' (E.tr (ϖ.toAinf a) x)).symm.trans ?_
    refine Eq.trans ?_ ((congrArg j (u.u_tr (ϖ.toAinf a) (E.tr H x))).symm.trans h2).symm
    refine congrArg j' ?_
    refine ((E.tr_comp _ _ x).symm).trans ?_
    refine (congrArg (fun f => E.tr f x) e1).trans ?_
    exact E.tr_comp _ _ x
  refine ⟨⟨m', mem_ME_of_mem_M hm'⟩, hm', ?_⟩
  apply I.j.injective
  refine (Ident.j_act _ _ _ _).trans ?_
  refine Eq.trans ?_ hm'eq
  refine (congrArg (TWact (galOW (↥(OL LL)) (sQ l g)) T g) hx).trans ?_
  exact (kappa_act T g _).trans (congrArg _ key)
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eisenstein_dvd_of_dvd_restrict_closedDisc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → ∀ y, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ R y → toDisc l (X : bk.S) ρ bk.E ∣ y := by
  first | exact @GlobalTheory.BSP.dvd_of_dvd_restrict_discS | exact GlobalTheory.BSP.dvd_of_dvd_restrict_discS | (intros; apply GlobalTheory.BSP.dvd_of_dvd_restrict_discS <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisin_lift_compatible_bdR_prisms : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n : ℕ) (x : ↥(OL K)), ∃ (k : ℕ) (s : bk.S), aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * C.o ((x : ↥K.1) : Om l) ∈ Per.FilP l n ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f s - BK.hf g s)) := by
  first | exact @GlobalTheory.BSP.RingHomLiftCongruence.exists_lift | exact GlobalTheory.BSP.RingHomLiftCongruence.exists_lift | (intros; apply GlobalTheory.BSP.RingHomLiftCongruence.exists_lift <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ) (A : Matrix (Fin d) (Fin d) bk.S), (∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a) → ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (t : ↥Q.I) (y : Fin d → Q.A) (m : M.M Q) (k : ℕ), IsFrac (t : Q.A) (M.Φ Q t (∑ j, y j • M.tr g (e j))) m k → ∃ r : ℕ, (t : Q.A) ^ r • (BK.hf g bk.E ^ a • m - (t : Q.A) ^ k • ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i)) = 0 := by
  first | exact @GlobalTheory.BSP.frob_tr_basis | exact GlobalTheory.BSP.frob_tr_basis | (intros; apply GlobalTheory.BSP.frob_tr_basis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_changeOfBasis_no_pole_at_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m N c₂ : ℕ) (s : Matrix (Fin d) (Fin m) (bk.S)) (n : Fin m → ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S)) (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)), (∀ r i, (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i)))) → X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → X = (s * Matrix.diagonal fun i => bk.E ^ n i) * Q + bk.E ^ (2 * N) • R → (l : bk.S) ^ c₂ • (s * Matrix.diagonal fun i => bk.E ^ n i) = X * Q' → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) := by
  first | exact @GlobalTheory.seed_nopole | exact GlobalTheory.seed_nopole | (intros; apply GlobalTheory.seed_nopole <;> assumption)
end
