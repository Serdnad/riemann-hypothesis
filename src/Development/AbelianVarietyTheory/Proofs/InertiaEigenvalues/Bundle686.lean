module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElementMovingTiltedUniformizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle657
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle661
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal


theorem _root_.GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  first | exact @GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum | exact GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum | (intros; apply GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Count

section Coord

variable {l : ℕ} [hl : Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def cfO {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) : O ⊗[ℤ_[l]] R →ₗ[ℤ_[l]] R :=
  (TensorProduct.lid ℤ_[l] R).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

theorem cfO_tmul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (o : O) (r : R) :
    cfO f (o ⊗ₜ[ℤ_[l]] r) = f o • r := by
  simp [cfO]

theorem cfO_mul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (β : R)
    (y : O ⊗[ℤ_[l]] R) : cfO f (((1 : O) ⊗ₜ[ℤ_[l]] β) * y) = β * cfO f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  | tmul o r => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, cfO_tmul, cfO_tmul, mul_smul_comm]

theorem cfO_map {R R' : Type} [CommRing R] [Algebra ℤ_[l] R] [CommRing R'] [Algebra ℤ_[l] R']
    (f : O →ₗ[ℤ_[l]] ℤ_[l]) (φ : R →ₐ[ℤ_[l]] R') (y : O ⊗[ℤ_[l]] R) :
    cfO f (Algebra.TensorProduct.map (AlgHom.id O O) φ y) = φ (cfO f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul o r => rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, cfO_tmul, cfO_tmul, map_smul]

theorem cfO_natCast_smul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (m : ℕ)
    (y : O ⊗[ℤ_[l]] R) : cfO f ((m : O) • y) = (m : R) * cfO f y := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]

theorem cfO_smul_one {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (o : O) :
    cfO f (o • (1 : O ⊗[ℤ_[l]] R)) = algebraMap ℤ_[l] R (f o) := by
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one, cfO_tmul,
    Algebra.smul_def, mul_one]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [Algebra O LL] [TopologicalSpace LL]

def cfT {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O) :
    TW R T →ₗ[O] R :=
  (TensorProduct.rid O R).toLinearMap ∘ₗ TensorProduct.map LinearMap.id g

theorem cfT_tmul {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O)
    (s : R) (t : ↥T.L.T) : cfT T g (s ⊗ₜ[O] t) = g t • s := by
  simp [cfT]

theorem cfT_incl {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O) (φ : R →ₐ[O] R') (z : TW R T) :
    cfT T g (TWincl φ T z) = φ (cfT T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s t => rw [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      cfT_tmul, cfT_tmul, map_smul]

theorem cfT_smul {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O)
    (r : R) (z : TW R T) : cfT T g (r • z) = r * cfT T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  | tmul s t => rw [TensorProduct.smul_tmul', cfT_tmul, cfT_tmul, smul_eq_mul, mul_smul_comm]

end Coord

end GlobalTheory.BKGal.Count

namespace GlobalTheory.BKGal.Count

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem toB_algebraMap (q : ℤ_[l]) :
    acrisToBcris l (ainfToAcris l (algebraMap ℤ_[l] (Ainf l) q)) = algebraMap ℤ_[l] (Per.Bcris l) q := by
  rw [AlgHom.commutes, AlgHom.commutes]

theorem le_of_bound {n c v j : ℕ} (hj : 2 * j < l - 1) (h : (l - 1) * n ≤ (l - 1) * (c + v) + 2 * j) :
    n ≤ c + v := by
  have h1 : (l - 1) * n < (l - 1) * (c + v + 1) := by
    rw [mul_add, mul_one]; omega
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left h1)

end GlobalTheory.BKGal.Count

namespace GlobalTheory.BKGal.Count

theorem count : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O), l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n c : ℕ),
    2 * j < l - 1 → ∀ (u : TW (OB l O) T) (x : ↥T.L.T) (w : TW (OCr l O) T),
    (l : O) ^ n • u = (1 : OB l O) ⊗ₜ[O] x →
    toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) • ((l : O) ^ c • u) = TWincl (toOB l O) T w →
    ∃ x' : ↥T.L.T, (l : O) ^ c • u = (1 : OB l O) ⊗ₜ[O] x' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T hl2 ε hε j n c hj u x w h1 h2
  let bO := Module.Free.chooseBasis ℤ_[l] O
  let bT := latBasis T
  have hr0 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := by
    simp only [toB, toOB, toOCr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hr : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) =
      (1 : O) ⊗ₜ[ℤ_[l]] (acrisToBcris l (ainfToAcris l (muOf ε)) ^ j) := by
    rw [map_pow, hr0, Algebra.TensorProduct.tmul_pow, one_pow]
  have hlO : ∀ m : ℕ, (l : O) ^ m = ((l ^ m : ℕ) : O) := fun m => by push_cast; rfl
  have key : ∀ k i, (l : ℤ_[l]) ^ (n - c) ∣ bO.coord k (bT.coord i x) := by
    intro k i
    by_cases ha : bO.coord k (bT.coord i x) = 0
    · rw [ha]; exact dvd_zero _
    have e1 := congrArg (fun z => cfO (bO.coord k) (cfT T (bT.coord i) z)) h1
    have e2 := congrArg (fun z => cfO (bO.coord k) (cfT T (bT.coord i) z)) h2
    rw [hlO, map_smul, cfO_natCast_smul, cfT_tmul, cfO_smul_one] at e1
    rw [hr, cfT_smul, cfO_mul, hlO, map_smul, cfO_natCast_smul, cfT_incl, toOB, cfO_map] at e2
    set U := cfO (bO.coord k) (cfT T (bT.coord i) u)
    set a := bO.coord k (bT.coord i x)
    set W' := cfO (bO.coord k) (cfT T (bT.coord i) w)
    have e3 : acrisToBcris l ((l : Per.Acris l) ^ n * W') = acrisToBcris l
        (ainfToAcris l (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ c * a))) := by
      rw [map_mul, map_mul, ← e2, map_pow, map_natCast, map_mul, toB_algebraMap, map_mul, ← e1]
      push_cast
      simp only [map_pow]
      ring
    have e4 := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l e3
    have hne : (l : ℤ_[l]) ^ c * a ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) ha
    have hb := GlobalTheory.T.valuation_bound_of_primePow_dvd_mu_pow_acris l hl2 ε hε j n ((l : ℤ_[l]) ^ c * a) hne ⟨W', e4.symm⟩
    rw [PadicInt.valuation_p_pow_mul c a ha] at hb
    have hv : n - c ≤ a.valuation := by have := le_of_bound hj hb; omega
    exact Ideal.mem_span_singleton.1 ((PadicInt.mem_span_pow_iff_le_valuation a ha (n - c)).2 hv)
  choose q hq using key
  let x' : ↥T.L.T := bT.equivFun.symm fun i => bO.equivFun.symm fun k => q k i
  have hx' : (l : O) ^ (n - c) • x' = x := by
    apply bT.equivFun.injective
    funext i
    rw [map_smul, Pi.smul_apply, LinearEquiv.apply_symm_apply, smul_eq_mul]
    apply bO.equivFun.injective
    funext k
    rw [show (l : O) ^ (n - c) = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ (n - c)) by rw [map_pow, map_natCast],
      ← Algebra.smul_def, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul,
      Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, ← hq k i]
    rfl
  refine ⟨(l : O) ^ (c + (n - c) - n) • x', smul_cancel T (n - c) ?_⟩
  have e5 : (l : O) ^ (n - c) • ((l : O) ^ c • u) = (l : O) ^ (c + (n - c) - n) • ((l : O) ^ n • u) := by
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e5, h1, ← hx', TensorProduct.tmul_smul, TensorProduct.tmul_smul, smul_smul,
    smul_smul, mul_comm]

end GlobalTheory.BKGal.Count
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem thmT_descend : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  intro l _ Pl K' h hN hF hS LL LL' hL C hT
  intro T₁ T₂ F N η H U Sig Fr hp1 hp2 hon hFr hFS h1 hcard h2N hI1 hI2 hU h0U hUc hη hηH hJ1 hJ2 hl
  obtain ⟨k₁, b₁, hb₁⟩ := GlobalTheory.T.exists_integralLatticeBasisLocal l LL T₁
  obtain ⟨k₂, b₂, hb₂⟩ := GlobalTheory.T.exists_integralLatticeBasisLocal l LL T₂
  obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.exists_integral_retraction_finiteExtension_ql l LL LL' hL
  obtain ⟨hFS', hrP, hcard', h1'⟩ := GlobalTheory.T.characterSetMapCoefficientField_properties (incl hL).toRingHom (pc Pl h hN hF hS).Iner Fr Sig
  have key := hT (extLat hL T₁ b₁ hb₁) (extLat hL T₂ b₂ hb₂) (extHom hL hb₁ hb₂ F) N η H U
    (mapSig (incl hL).toRingHom Sig) Fr
    (GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ hp1) (GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ hp2)
    (GlobalTheory.T.latticeHomBaseChange_onto l LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hon) hFr (hFS' hFS) (h1' h1) (hcard'.trans hcard) h2N
    (GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ Sig hI1) (GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ Sig hI2)
    hU h0U hUc hη hηH
    (GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ _ hJ1) (GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ _ hJ2) hl
  rw [hrP] at key
  exact ⟨key.1, GlobalTheory.T.liftable_descends_from_larger_coefficientField l _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr1 hr2 hr3 (by haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2; exact LinearMap.continuous_of_finiteDimensional r) _ key.2⟩

end GlobalTheory.BaseCoef
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_galois_element_moving_tilted_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), l ≠ 2 → ∃ (g : Gl l) (ε : OCb l) (c : ℕ), IsEps ε ∧ c ≠ 0 ∧ sQ l g ∈ GK (ϖ.field a) ∧ ∀ k : ℕ, ϖ.kummer (sQ l (g ^ k)) = ε ^ (c * k) := by
  first | exact @GlobalTheory.KummerMove.main | exact GlobalTheory.KummerMove.main | (intros; apply GlobalTheory.KummerMove.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameExt

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions

theorem aeval_intertwine {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (a : Module.End R M) (b : Module.End R N) (hab : ∀ v, b (f v) = f (a v))
    (p : Polynomial R) (v : M) : Polynomial.aeval b p (f v) = f (Polynomial.aeval a p v) := by
  have hpow : ∀ (n : ℕ) v, (b ^ n) (f v) = f ((a ^ n) v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, hab, ih, pow_succ, Module.End.mul_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, map_smul]

section Gen

variable {G H : Type} [Group G] [Group H] (ι : H →* G)
  {Qp K₀ K K₀' K' B BdR : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
  [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
  [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
  [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
  [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
  [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
  [Algebra K₀' B] [IsScalarTower Qp K₀' B]
  [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
  [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
  (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData H Qp K₀' K' B BdR)
  {LL : Type} [Field LL] [Algebra Qp LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem actVB_comp' (hι : ∀ h b, PD'.actB h b = PD.actB (ι h) b) (ρ : Representation LL G V) (h : H)
    (v : V ⊗[Qp] B) : actVB PD' (ρ.comp ι) h v = actVB PD ρ (ι h) v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b =>
    change ρ (ι h) v ⊗ₜ[Qp] PD'.actB h b = ρ (ι h) v ⊗ₜ[Qp] PD.actB (ι h) b
    rw [hι]

theorem actVB_mulVB' (ρ : Representation LL G V) (g : G) (k : K₀')
    (hk : PD.actB g (algebraMap K₀' B k) = algebraMap K₀' B k) (v : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (LL := LL) k v) = mulVB (LL := LL) k (actVB PD ρ g v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b =>
    change ρ g v ⊗ₜ[Qp] PD.actB g (algebraMap K₀' B k * b) = ρ g v ⊗ₜ[Qp] (algebraMap K₀' B k * PD.actB g b)
    rw [map_mul, hk]

theorem snd_actVB' (ρ : Representation LL H (V × LL)) (hρ : ∀ h v, (ρ h v).2 = v.2) (h : H)
    (w : (V × LL) ⊗[Qp] B) :
    AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (((PD'.actB h).toAlgHom.toLinearMap).restrictScalars Qp)
        (AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) w) =
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (actVB PD' ρ h w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
  | tmul v b =>
    have h2 : LinearMap.snd LL V LL (ρ h v) = v.2 := hρ h v
    simp only [actVB, AlgebraTensorModule.map_tmul, AlgebraTensorModule.rTensor_tmul, h2]
    rfl

theorem aeval_extRep' [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [FiniteDimensional Qp LL]
    (hι : ∀ h b, PD'.actB h b = PD.actB (ι h) b) (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ))
    (hc : ∃ β : V ⊗[Qp] B, ∀ h, (c : G → V) h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h β - β)
    (g : G) (hg : ∀ k : K₀', PD.actB g (algebraMap K₀' B k) = algebraMap K₀' B k)
    (P : Polynomial LL) (hP : (Polynomial.X - Polynomial.C 1) ∣ P)
    (hTP : ∀ x ∈ Dcris PD' (ρ.comp ι), Polynomial.aeval (actVB PD ρ g : Module.End LL (V ⊗[Qp] B)) P x = 0)
    (x : (V × LL) ⊗[Qp] B) (hx : x ∈ Dcris PD' ((extRep ρ c).comp ι)) :
    Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B)) P x = 0 := by
  have hE := extRep_isExt ρ c
  obtain ⟨y, hy, hpy⟩ := (GlobalTheory.CrysExt.coboundary_iff_lift PD hE.1 hE.2).1 hc
  have hyfix : ∀ h : G, actVB PD (extRep ρ c) h y = y := (GlobalTheory.CrysSub.mem_Dcris _ _ _).1 hy
  have hf : ∀ (h : H) (v : V), LinearMap.inl LL V LL ((ρ.comp ι) h v) =
      ((extRep ρ c).comp ι) h (LinearMap.inl LL V LL v) := fun h v => hE.1.2.2.2.1 _ v
  have hq : ∀ (h : H) (v : V × LL), LinearMap.snd LL V LL (((extRep ρ c).comp ι) h v) =
      Representation.trivial LL H LL h (LinearMap.snd LL V LL v) := fun h v => hE.1.2.2.2.2 _ v
  have hkF : ∀ (h : H) (k : K₀'), PD.actB (ι h) (algebraMap K₀' B k) = algebraMap K₀' B k :=
    fun h k => (hι h _).symm.trans (AlgEquiv.commutes _ k)
  have hsm : ∀ (k : K₀') (v : (V × LL) ⊗[Qp] B),
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (mulVB (LL := LL) k v) =
        mulVB (LL := LL) k (AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) v) := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

  have hlift1 : ∀ u : LL ⊗[Qp] K₀', ∃ x₁ : (V × LL) ⊗[Qp] B,
      x₁ ∈ Dcris PD' ((extRep ρ c).comp ι) ∧
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) x₁ = GlobalTheory.CrysExt.incl Qp K₀' B LL u ∧
      actVB PD (extRep ρ c) g x₁ = x₁ := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, zero_mem _, by simp, by simp⟩
    | tmul a k =>
      refine ⟨a • mulVB (LL := LL) k y, (GlobalTheory.CrysSub.mem_Dcris _ _ _).2 fun h => ?_, ?_, ?_⟩
      · rw [map_smul, actVB_comp' ι PD PD' hι, actVB_mulVB' PD _ _ k (hkF h k), hyfix]
      · rw [map_smul, hsm, hpy]
        simp [mulVB, smul_tmul', GlobalTheory.CrysExt.incl, AlgebraTensorModule.map_tmul]
      · rw [map_smul, actVB_mulVB' PD _ _ k (hg k), hyfix]
    | add u v hu hv =>
      obtain ⟨x₁, h1, h2, h3⟩ := hu
      obtain ⟨x₂, h4, h5, h6⟩ := hv
      exact ⟨x₁ + x₂, add_mem h1 h4, by rw [map_add (f := _), map_add (f := _), h2, h5], by rw [map_add (f := _), h3, h6]⟩

  obtain ⟨u, hu⟩ := (GlobalTheory.CrysExt.invariant_iff (fun h : H => PD'.actB h) PD'.invB _).1 fun h => by
    rw [snd_actVB' PD' ((extRep ρ c).comp ι) (fun h v => hE.1.2.2.2.2 (ι h) v) h x, (GlobalTheory.CrysSub.mem_Dcris _ _ _).1 hx h]
  obtain ⟨x₁, hx₁, hsx₁, hgx₁⟩ := hlift1 u

  have hD : x - x₁ ∈ Dcris PD' ((extRep ρ c).comp ι) := sub_mem hx hx₁
  have hker : (⟨x - x₁, hD⟩ : ↥(Dcris PD' ((extRep ρ c).comp ι))) ∈
      LinearMap.ker (GlobalTheory.CrysSub.Dmap PD' _ _ _ hq) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (x - x₁) = 0
    rw [map_sub, hsx₁, hu, sub_self]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.CrysSub.exact_Dmap PD' (ρ.comp ι) ((extRep ρ c).comp ι)
    (Representation.trivial LL H LL) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL)
    hf hq LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective hker
  have hx0 : AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL) (x₀ : V ⊗[Qp] B) = x - x₁ :=
    congrArg Subtype.val hx₀
  have hxe : x = x₁ + AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL) (x₀ : V ⊗[Qp] B) := by
    rw [hx0]; abel

  have hpart1 : Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B)) P x₁ = 0 := by
    obtain ⟨Q, rfl⟩ := hP
    rw [mul_comm, map_mul, Module.End.mul_apply]
    have h1 : Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B))
        (Polynomial.X - Polynomial.C (1 : LL)) x₁ = 0 := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one, LinearMap.sub_apply, Module.End.one_apply,
        hgx₁, sub_self]
    rw [h1, map_zero]
  have hpart2 := aeval_intertwine (AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL))
    (actVB PD ρ g) (actVB PD (extRep ρ c) g)
    (fun v => (GlobalTheory.CrysSub.rTensor_act _ _ _ _ hE.1.2.2.2.1 g v).symm) P (x₀ : V ⊗[Qp] B)
  rw [hxe, map_add (f := _), hpart1, hpart2, hTP _ x₀.2, map_zero, add_zero]

end Gen

end GlobalTheory.TameExt

namespace GlobalTheory.TameExt

theorem tameType_extLat {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l}
    [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL) (Sig : Finset (ZMod e))
    (h0 : (0 : ZMod e) ∈ Sig) (hT : TameType a ϖ Pl T Sig) (z : ↥(latticeCocycles T.L))
    (hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ) :
    TameType a ϖ Pl (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) Sig := by
  intro g hg w hw x hx
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hP : (Polynomial.X - Polynomial.C (1 : ↥LL.1)) ∣ ∏ c ∈ Sig, (Polynomial.X - Polynomial.C (w ^ c.val)) := by
    have h1 := Finset.dvd_prod_of_mem (fun c : ZMod e => Polynomial.X - Polynomial.C (w ^ c.val)) h0
    rwa [ZMod.val_zero, pow_zero] at h1
  exact aeval_extRep' (inclG (ϖ.field a)) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (Pl.PD (ϖ.field a))
    (fun h b => (Pl.PD_actB _ h b).trans (Pl.PD_actB _ (inclG _ h) b).symm) T.ρ ⟨z, z.2.1⟩ hz.2 g
    (fun k => (Pl.PD_actB _ g _).trans (Pl.actQ_Kur _ ⟨k, k.2.2⟩ ⟨k, k.2.2⟩
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (GlobalTheory.BKGal.UnitModel.fix_Kur hg) _ k.2.2)))
    _ hP (hT g hg w hw) x hx

end GlobalTheory.TameExt
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinDatum_structureMap_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  first | exact @GlobalTheory.BSP.bk_ev_injective | exact GlobalTheory.BSP.bk_ev_injective | (intros; apply GlobalTheory.BSP.bk_ev_injective <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_two_homs_E_regular_associated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf f bk.E ∈ nonZeroDivisors B.A ∧ Associated (BK.hf f bk.E) (BK.hf g bk.E) ∧ BK.hf f bk.E ∣ BK.hf g X - BK.hf f X := by
  first | exact @GlobalTheory.BSP.hf_E_pair | exact GlobalTheory.BSP.hf_E_pair | (intros; apply GlobalTheory.BSP.hf_E_pair <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.exists_ainf_lift_period_pow_smul_intertwiner : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ (f : Matrix (Fin d') (Fin d) ℤ_[l]) (X : Matrix (Fin d') (Fin d) (WCb l)), T' * X = zW f * T → ∃ (M : ℕ) (x : Matrix (Fin d') (Fin d) (Ainf l)), x.map (inclW l) = inclW l τ ^ M • X := by
  first | exact @GlobalTheory.BSP.PoleBound.exists_pow_smul | exact GlobalTheory.BSP.PoleBound.exists_pow_smul | (intros; apply GlobalTheory.BSP.PoleBound.exists_pow_smul <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_residueTilt_injective_retract : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (ek : (Fq l bk.a)⟦X⟧ →+* OCb l) (pr : OCb l →+ (Fq l bk.a)⟦X⟧), (∀ s : bk.S, ek (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s) = (bk.ev s).coeff 0) ∧ Function.Injective ek ∧ (∀ a y, pr (ek a * y) = a * pr y) ∧ pr 1 = 1 := by
  first | exact @GlobalTheory.BSP.exists_resTilt_retract | exact GlobalTheory.BSP.exists_resTilt_retract | (intros; apply GlobalTheory.BSP.exists_resTilt_retract <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → IsDomain (bk.DA ρ) ∧ (∀ x y : bk.DA ρ, (ρ : ℝ) ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖) ∧ ∀ a : bk.DA ρ, a ≠ 0 → ∃ C : ℝ, ∀ y, ‖y‖ ≤ C * ‖a * y‖ := by
  first | exact @GlobalTheory.BSP.discAinf_isDomain | exact GlobalTheory.BSP.discAinf_isDomain | (intros; apply GlobalTheory.BSP.discAinf_isDomain <;> assumption)
end
