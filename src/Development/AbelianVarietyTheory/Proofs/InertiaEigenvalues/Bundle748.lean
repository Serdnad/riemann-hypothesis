module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle540
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle539
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisCmpExist

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G]
  {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

theorem twincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul b x => simp [TWincl, TensorProduct.smul_tmul']

theorem twincl_injective {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (hf : Function.Injective f) : Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem inclL_smul' (r : OA l O) (d : ι → OA l O) : inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

variable {I : Ident t ϖ P T} {m n : OA l O}

def dFun (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) : ι → OA l O :=
  (LinearMap.mem_range.1 (hn x)).choose

theorem dFun_spec (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) :
    inclL t ϖ P (dFun hn x) = inclO l O n • I.ofT x :=
  (LinearMap.mem_range.1 (hn x)).choose_spec

def dMap (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : ↥T.L.T →ₗ[O] (ι → OA l O) where
  toFun := dFun hn
  map_add' x y := inclL_injective t ϖ P (by
    rw [map_add (f := _), dFun_spec, dFun_spec, dFun_spec, map_add (f := _), smul_add])
  map_smul' r x := inclL_injective t ϖ P (by
    rw [LinearMap.map_smul, dFun_spec, dFun_spec, LinearMap.map_smul, RingHom.id_apply, smul_comm])

theorem dMap_spec (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) :
    inclL t ϖ P (dMap hn x) = inclO l O n • I.ofT x :=
  dFun_spec hn x

def gA (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : TW (OA l O) T →ₗ[OA l O] (ι → OA l O) :=
  LinearMap.liftBaseChange (OA l O) (dMap hn)

theorem inclL_gA (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (z : TW (OA l O) T) :
    inclL t ϖ P (gA hn z) = inclO l O n • I.j.symm (TWincl (inclO l O) T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul b x =>
    rw [gA, LinearMap.liftBaseChange_tmul, inclL_smul', dMap_spec]
    have : TWincl (inclO l O) T (b ⊗ₜ[O] x) = inclO l O b • ((1 : OW l O) ⊗ₜ[O] x) := by
      simp [TWincl, smul_tmul']
    rw [this, LinearEquiv.map_smul, smul_comm]
    rfl

def zz (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z) (i : ι) :
    TW (OA l O) T :=
  (hm _ ⟨Pi.single i 1, rfl⟩).choose

theorem zz_spec (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (i : ι) : I.j (inclO l O m • inclL t ϖ P (Pi.single i 1)) = TWincl (inclO l O) T (zz hm i) :=
  (hm _ ⟨Pi.single i 1, rfl⟩).choose_spec

def crisComparisonLToBcrisTensorMap (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z) :
    (ι → OB l O) →ₗ[OB l O] TW (OB l O) T :=
  (Pi.basisFun (OB l O) ι).constr (OB l O) fun i => TWincl (toB l O) T (zz hm i)

def crisComparisonBcrisTensorToLMap (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : TW (OB l O) T →ₗ[OB l O] (ι → OB l O) :=
  LinearMap.liftBaseChange (OB l O) (((toB l O).toLinearMap.compLeft ι) ∘ₗ dMap hn)

theorem kisin_jB_toB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (c : ι → OA l O) (z : TW (OA l O) T)
    (hz : I.j (inclO l O m • inclL t ϖ P c) = TWincl (inclO l O) T z) :
    crisComparisonLToBcrisTensorMap hm (fun i => toB l O (c i)) = TWincl (toB l O) T z := by
  have hz' : z = ∑ i, c i • zz hm i := by
    apply twincl_injective (T := T) (inclO l O) inclO_injective

    rw [← hz, map_sum]
    have hc : inclL t ϖ P c = ∑ i, inclO l O (c i) • inclL t ϖ P (Pi.single i 1) := by
      conv_lhs => rw [pi_eq_sum_univ' c]

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => inclL_smul' _ _

    rw [hc, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [twincl_smul, ← zz_spec hm i, smul_comm, LinearEquiv.map_smul]

  rw [hz', map_sum, crisComparisonLToBcrisTensorMap, Module.Basis.constr_apply_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [twincl_smul, Pi.basisFun_equivFun]
  rfl

theorem kisin_kB_tensor_incl (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (z : TW (OA l O) T) :
    crisComparisonBcrisTensorToLMap hn (TWincl (toB l O) T z) = fun i => toB l O (gA hn z i) := by
  induction z using TensorProduct.induction_on with
  | zero => funext i; simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]; funext i; simp
  | tmul b x =>
    have : TWincl (toB l O) T (b ⊗ₜ[O] x) = toB l O b ⊗ₜ[O] x := by simp [TWincl]
    rw [this, crisComparisonBcrisTensorToLMap, gA, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul]
    funext i
    simp

theorem kisin_kB_comp_jB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (v : ι → OB l O) :
    crisComparisonBcrisTensorToLMap hn (crisComparisonLToBcrisTensorMap hm v) = (toB l O m * toB l O n) • v := by
  have h : (crisComparisonBcrisTensorToLMap hn).comp (crisComparisonLToBcrisTensorMap hm) = (toB l O m * toB l O n) • LinearMap.id := by
    refine (Pi.basisFun (OB l O) ι).ext fun i => ?_
    rw [LinearMap.comp_apply, crisComparisonLToBcrisTensorMap, Module.Basis.constr_basis, kisin_kB_tensor_incl, LinearMap.smul_apply, LinearMap.id_apply]
    have hg : gA hn (zz hm i) = (m * n) • Pi.single i 1 := by
      apply inclL_injective t ϖ P
      rw [inclL_gA, ← zz_spec hm i, LinearEquiv.symm_apply_apply, inclL_smul', map_mul, mul_smul, smul_comm]
    rw [hg, Pi.basisFun_apply]
    funext j
    by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_apply, hij]
  exact LinearMap.congr_fun h v

theorem kisin_jB_comp_kB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (w : TW (OB l O) T) :
    crisComparisonLToBcrisTensorMap hm (crisComparisonBcrisTensorToLMap hn w) = (toB l O m * toB l O n) • w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul b x =>
    have h1 : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [h1, LinearMap.map_smul, LinearMap.map_smul, smul_comm]
    congr 1
    rw [crisComparisonBcrisTensorToLMap, LinearMap.liftBaseChange_tmul, one_smul]
    change crisComparisonLToBcrisTensorMap hm (fun i => toB l O (dMap hn x i)) = _
    rw [kisin_jB_toB hm (dMap hn x) ((m * n) ⊗ₜ[O] x)]
    · simp [TWincl, smul_tmul']
    · rw [dMap_spec, smul_smul, ← map_mul, LinearEquiv.map_smul, Ident.j_ofT]
      simp [TWincl, smul_tmul']

theorem exists_of (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (hu : IsUnit (toB l O m)) (hv : IsUnit (toB l O n)) :
    ∃ jB, IsCrisCmp I jB := by
  obtain ⟨u, hu'⟩ := hu
  obtain ⟨v, hv'⟩ := hv
  let F : (ι → OB l O) →ₗ[OB l O] TW (OB l O) T := ((u⁻¹ : (OB l O)ˣ) : OB l O) • crisComparisonLToBcrisTensorMap hm
  let Gm : TW (OB l O) T →ₗ[OB l O] (ι → OB l O) := ((v⁻¹ : (OB l O)ˣ) : OB l O) • crisComparisonBcrisTensorToLMap hn
  have key : ((u⁻¹ : (OB l O)ˣ) : OB l O) * (((v⁻¹ : (OB l O)ˣ) : OB l O) * (toB l O m * toB l O n)) = 1 := by
    rw [← hu', ← hv']
    calc _ = (((u⁻¹ : (OB l O)ˣ) : OB l O) * u) * (((v⁻¹ : (OB l O)ˣ) : OB l O) * v) := by ring
      _ = 1 := by rw [Units.inv_mul, Units.inv_mul, mul_one]
  have key2 : ((v⁻¹ : (OB l O)ˣ) : OB l O) * (((u⁻¹ : (OB l O)ˣ) : OB l O) * (toB l O m * toB l O n)) = 1 := by
    rw [← key]; ring
  refine ⟨LinearEquiv.ofLinear F Gm ?_ ?_, ?_⟩
  · refine LinearMap.ext fun w => ?_
    simp only [F, Gm, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, kisin_jB_comp_kB, smul_smul,
      LinearMap.id_apply]
    rw [key, one_smul]
  · refine LinearMap.ext fun w => ?_
    simp only [F, Gm, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, kisin_kB_comp_jB, smul_smul,
      LinearMap.id_apply]
    rw [key2, one_smul]
  · intro c z hz
    rw [LinearEquiv.ofLinear_apply]
    have hz2 : I.j (inclO l O m • inclL t ϖ P c) = TWincl (inclO l O) T (m • z) := by
      rw [LinearEquiv.map_smul, hz, twincl_smul]
    simp only [F, LinearMap.smul_apply]
    rw [kisin_jB_toB hm c _ hz2, twincl_smul, smul_smul, ← hu', Units.inv_mul, one_smul]

end GlobalTheory.BKGal.CrisCmpExist

theorem GlobalTheory.BKGal.exists_isCrisCmp : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jB, IsCrisCmp I jB := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, hunit, -, -, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  have hU : ∀ k : ℕ, IsUnit (toB l O (1 ⊗ₜ (muOf ε ^ k))) := fun k => by
    have : toB l O (1 ⊗ₜ (muOf ε ^ k)) = (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (muOf ε))) ^ k := by
      rw [← map_pow, ← map_pow, ← map_pow]
      rfl
    rw [this]
    exact (hunit.map _).pow k
  exact GlobalTheory.BKGal.CrisCmpExist.exists_of h4 h3 (hU α) (hU β)
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfEPow

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))

theorem theta_eq_zero_iff (x : Ainf l) : Per.θ l x = 0 ↔ bk.ev bk.E ∣ x := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem theta_of_natPow_mul (n : ℕ) (c : Ainf l) (h : Per.θ l ((l : Ainf l) ^ n * c) = 0) :
    Per.θ l c = 0 := by
  rw [map_mul, map_pow, map_natCast] at h
  have hne : ((l : Per.OC l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  exact (mul_eq_zero.mp h).resolve_left hne

theorem dvd_of_dvd_natPow_mul (n : ℕ) (c : Ainf l) (h : bk.ev bk.E ∣ (l : Ainf l) ^ n * c) :
    bk.ev bk.E ∣ c := by
  rw [← theta_eq_zero_iff] at h ⊢
  exact theta_of_natPow_mul n c h

theorem pow_dvd_of_pow_dvd_l_mul (m : ℕ) : ∀ a : Ainf l,
    bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a := by
      rw [pow_one]; exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    obtain ⟨a', rfl⟩ := dvd_of_dvd_natPow_mul bk 1 a h1
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem pow_dvd_of_pow_dvd_lpow_mul (m k : ℕ) (a : Ainf l)
    (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply pow_dvd_of_pow_dvd_l_mul bk m
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem pow_dvd_of_ev_pow_dvd (m : ℕ) : ∀ s : bk.S,
    bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
    intro s h
    have h1 : bk.ev bk.E ∣ bk.ev s := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    have hE : bk.E ∣ s := by
      set r := bk.str.symm (Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s) with hr
      have hmk : Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s = bk.str r := by
        rw [hr, RingEquiv.apply_symm_apply]
      have hθ := bk.θ_ev r s hmk
      rw [(theta_eq_zero_iff bk _).mpr h1] at hθ
      have hr0 : r = 0 := intToOC_injective K (by rw [← hθ, map_zero])
      rw [hr0, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
      exact hmk
    obtain ⟨s', rfl⟩ := hE
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', map_mul] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem theta_eq_zero_of_forall (y : Per.OC l) (h : ∀ n : ℕ, ∃ z : Per.OC l, y = (l : Per.OC l) ^ n * z) :
    y = 0 := by
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(l : Per.OC l)})) y
  intro n
  obtain ⟨z, hz⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

theorem pow_dvd_of_forall_approx (m : ℕ) : ∀ a : Ainf l,
    (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) →
      bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have hθ : Per.θ l a = 0 := by
      apply theta_eq_zero_of_forall
      intro n
      obtain ⟨b, c, hbc⟩ := h n
      refine ⟨Per.θ l c, ?_⟩
      have hE : Per.θ l (bk.ev bk.E) = 0 := (theta_eq_zero_iff bk _).mpr dvd_rfl
      rw [hbc, map_add (f := _), map_mul, map_mul, map_pow, map_pow, hE, map_natCast]
      simp
    obtain ⟨a', rfl⟩ := (theta_eq_zero_iff bk a).mp hθ
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    intro n
    obtain ⟨b, c, hbc⟩ := h n
    have hc : bk.ev bk.E ∣ (l : Ainf l) ^ n * c :=
      ⟨a' - bk.ev bk.E ^ m * b, by rw [mul_sub, ← mul_assoc, ← pow_succ', hbc]; ring⟩
    obtain ⟨c', rfl⟩ := dvd_of_dvd_natPow_mul bk n c hc
    refine ⟨b, c', ?_⟩
    apply mul_left_cancel₀ (evE_ne_zero bk)
    rw [hbc]; ring

theorem ker_localizedTheta_eq_span_eisenstein (bk : BK K) : Per.kerP l = Ideal.span {(algebraMap (Per.Ainf l) (Per.AinfP l)) (bk.ev bk.E)} :=
  GlobalTheory.MemLoc.ker_localizedTheta_eq_span_of_dvd l _ (fun a => theta_eq_zero_iff bk a)

theorem mem_filtration_iff_eisenstein_pow_dvd (m : ℕ) (a : Ainf l) :
    aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a := by
  have key : aDp l a ∈ Per.FilP l m ↔
      (algebraMap (Per.Ainf l) (Per.AinfP l)) a ∈ Per.kerP l ^ m := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    unfold aDp
    rw [RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [key, ker_localizedTheta_eq_span_eisenstein bk, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
  constructor
  · rintro ⟨y, hy⟩
    haveI : IsLocalization (Submonoid.powers (l : Per.Ainf l)) (Per.AinfP l) :=
      inferInstance
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) y
    obtain ⟨k, hk⟩ := s.2
    simp only at hs hk
    rw [← hk] at hs
    have hl0 : (l : Per.Ainf l) ≠ 0 := fun h => by
      have h' := congrArg (Per.θ l) h
      rw [map_natCast, map_zero] at h'
      exact (Nat.cast_ne_zero.mpr hl.out.ne_zero) h'
    have hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) :=
      IsLocalization.injective (Per.AinfP l) (powers_le_nonZeroDivisors_of_noZeroDivisors hl0)
    have heq : (l : Ainf l) ^ k * a = bk.ev bk.E ^ m * b := by
      apply hinj
      rw [map_mul, map_mul, ← hs, hy]
      ring
    exact pow_dvd_of_pow_dvd_lpow_mul bk m k a ⟨b, heq⟩
  · exact fun h => map_dvd _ h

theorem ePow_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), (∀ a : Ainf l, bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a) ∧ (∀ s : bk.S, bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s) ∧ (∀ a : Ainf l, aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a) ∧ ∀ a : Ainf l, (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) → bk.ev bk.E ^ m ∣ a := by
  intro l _ K bk m
  exact ⟨pow_dvd_of_pow_dvd_l_mul bk m, pow_dvd_of_ev_pow_dvd bk m, mem_filtration_iff_eisenstein_pow_dvd bk m,
    pow_dvd_of_forall_approx bk m⟩

end GlobalTheory.AinfEPow
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem mulVec_frob_of_unit {R D : Type} [CommRing R] [CommRing D] {d : ℕ} (j : R →+* D) (Φ : D →+* D)
    (Ψ : R →+* R) (h : ∀ r, j (Ψ r) = Φ (j r)) (c : Rˣ) (W : Matrix (Fin d) (Fin d) D)
    (B : Matrix (Fin d) (Fin d) R) (hW : j c • W.map Φ = W * B.map j) (x : Fin d → R) :
    W *ᵥ (fun a => j (((c⁻¹ : Rˣ) : R) * (B *ᵥ fun b => Ψ (x b)) a)) =
      fun a => Φ ((W *ᵥ fun b => j (x b)) a) := by
  have e1 : (fun a => j (((c⁻¹ : Rˣ) : R) * (B *ᵥ fun b => Ψ (x b)) a)) =
      j ((c⁻¹ : Rˣ) : R) • (B.map j *ᵥ fun b => Φ (j (x b))) := by
    funext a

    simp [Matrix.mulVec, dotProduct, map_sum, h]
  have e2 : (fun a => Φ ((W *ᵥ fun b => j (x b)) a)) = W.map Φ *ᵥ fun b => Φ (j (x b)) := by
    funext a

    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e1, e2, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hW, Matrix.smul_mulVec, smul_smul, ← map_mul,
    Units.inv_mul, map_one, one_smul]

theorem seed_span_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  intro l hl K bk τ hτ d ρ hρ s y ⟨x, hx⟩
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l bk.S bk.S (frobS l bk.a) X X bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l (Ainf l) (Ainf l) WittVector.frobenius (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hu : IsUnit (((l : ℕ) : bk.DS bk.ρ₀) ^ (s.c₁ + s.c₂) *
      toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) :=
    ((isUnit_l_disc l (X : bk.S) bk.ρ₀).pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  obtain ⟨c, hc⟩ := hu
  refine ⟨fun a => ((c⁻¹ : (bk.DS bk.ρ₀)ˣ) : bk.DS bk.ρ₀) *
    ((s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map (toDisc l (X : bk.S) bk.ρ₀) *ᵥ
      fun b => Ψ (x b)) a, fun j hj => ?_⟩
  have hcomm : j.comp Ψ = Φ.comp j := by
    refine IsDiscMap.unique (DiscBasic.isDiscMap_comp l _ _ hΨ hj) ?_
    have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
      RingHom.ext bk.ev_frob
    rw [e]
    exact DiscBasic.isDiscMap_comp l _ _ hj hΦ
  have hW := GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ
  rw [mulVec_frob_of_unit j Φ Ψ (RingHom.congr_fun hcomm) c s.W _ ?_ x, hx j hj]
  · funext a
    exact hΦ.ext _
  · rw [hc, map_mul, map_pow, map_pow, map_natCast, hj.ext, Matrix.map_map]
    refine hW.trans ?_
    congr 2
    funext a
    exact (hj.ext a).symm

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) → ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  first | exact @GlobalTheory.AcrisDisc.main | exact GlobalTheory.AcrisDisc.main | (intros; apply GlobalTheory.AcrisDisc.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.integral_elements_unit_factorization : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w ∈ bk.OE, ((l : ℕ) : WCb l) ∣ w → ∃ v ∈ bk.OE, w = (l : WCb l) * v) ∧ (∃ w ∈ bk.OE, bk.evW X * w = 1) ∧ (∀ s : bk.S, ¬ (l : bk.S) ∣ s → ∃ w ∈ bk.OE, bk.evW s * w = 1) ∧ (∀ w ∈ bk.OE, w ≠ 0 → ∃ (k : ℕ) (v v' : WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = 1 ∧ w = (l : WCb l) ^ k * v) ∧ (∀ w : ℕ → WCb l, (∀ n, w n ∈ bk.OE) → (∀ n, (l : WCb l) ^ n ∣ w (n + 1) - w n) → ∃ z ∈ bk.OE, ∀ n, (l : WCb l) ^ n ∣ z - w n) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) := by
  first | exact @GlobalTheory.OEDvr.main | exact GlobalTheory.OEDvr.main | (intros; apply GlobalTheory.OEDvr.main <;> assumption)
end
