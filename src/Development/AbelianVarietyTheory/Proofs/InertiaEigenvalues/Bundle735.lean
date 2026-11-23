module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle721
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle658
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle028
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle723
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle562
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle722
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∀ x, inclO l O (1 ⊗ₜ (muOf δ ^ β)) • I.ofT x ∈ MA P) ∧ (∀ v ∈ MA P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf δ ^ α)) • v) = TWincl (inclO l O) T z) ∧ (∀ x, inclO l O (1 ⊗ₜ (muOf ε ^ β)) • I.ofT x ∈ LA t ϖ P) ∧ ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • v) = TWincl (inclO l O) T z := by
  first | exact @GlobalTheory.BKExp.exponents | exact GlobalTheory.BKExp.exponents | (intros; apply GlobalTheory.BKExp.exponents <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galOB_iB_sub_iB_mem_filO : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, (f τ : K⟦X⟧) ∈ invL l (A O K)) → (∀ τ, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (f τ : K⟦X⟧) = E K l e ^ m * h) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → galOB O (sQ l g) (ϖ.iB t K f) - ϖ.iB t K f ∈ filO O C m := by
  first | exact @GlobalTheory.BKGal.TaylorFil.gal_iB_sub_mem_filO | exact GlobalTheory.BKGal.TaylorFil.gal_iB_sub_mem_filO | (intros; apply GlobalTheory.BKGal.TaylorFil.gal_iB_sub_mem_filO <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_galois_decomp_tameCover_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : Gl l), ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ ∃ γ : TameGal K l e a, Covers K t ϖ (sQ l k) γ := by
  first | exact @GlobalTheory.TameCoverGen.main | exact GlobalTheory.TameCoverGen.main | (intros; apply GlobalTheory.TameCoverGen.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.muOf_pow_smul_actB_sub_self_mem_range_TWincl : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  first | exact @GlobalTheory.BKGal.muPow_smul_actB_sub_mem | exact GlobalTheory.BKGal.muPow_smul_actB_sub_mem | (intros; apply GlobalTheory.BKGal.muPow_smul_actB_sub_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CobCont

set_option synthInstance.maxHeartbeats 400000

theorem inj1 : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL),
    Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := by
  intro l _ LL T
  have : Module.Free (↥(OL LL)) ↥T.L.T := T.L.free
  exact GlobalTheory.TContInj.one_tmul_injective l ↥(OL LL) ↥T.L.T

theorem nbhd : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (U : Set T.V), U ∈ nhds (0 : T.V) →
    ∃ m : ℕ, ∀ x ∈ T.L.T, ((l : ↥LL.1) ^ m) • x ∈ U := GlobalTheory.T.galoisLattice_prime_pow_smul_tendsto_zero

theorem cont1 : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T)
    (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l),
      ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := GlobalTheory.T.bcrisCoboundary_eventually_mem_prime_pow_lattice

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

theorem o_smul_mem (T : QLat LL) (o : ↥(OL LL)) (x : T.V) (hx : x ∈ T.L.T) : (o : ↥LL.1) • x ∈ T.L.T := by
  have := T.L.T.smul_mem o hx
  rwa [← algebraMap_smul ↥LL.1 o x] at this

theorem lpow_smul_mem (T : QLat LL) (n : ℕ) (x : T.V) (hx : x ∈ T.L.T) : (l : ↥LL.1) ^ n • x ∈ T.L.T := by
  have := o_smul_mem T ((l : ↥(OL LL)) ^ n) x hx
  simpa using this

theorem exists_pow_smul_mem (T : QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem ..)

theorem actB_tmul_one (T : QLat LL) (g : Gl l) (x : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] T.actT g x := by
  simp [actB, TWact]

theorem galOB_mul' {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g h : GQ l) (o : OB l O) :
    galOB O (g * h) o = galOB O g (galOB O h o) := by
  induction o using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w =>
    exact congrArg (fun z => a ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ w)

theorem actT_mul (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) : T.actT (g * h) x = T.actT g (T.actT h x) :=
  Subtype.ext (by
    show T.ρ (g * h) (x : T.V) = T.ρ g (T.ρ h x)
    rw [map_mul]; rfl)

theorem actB_tmul (T : QLat LL) (g : Gl l) (o : OB l ↥(OL LL)) (x : ↥T.L.T) :
    actB (sQ l) T g (o ⊗ₜ[↥(OL LL)] x) = (galOB ↥(OL LL) (sQ l g) o) ⊗ₜ[↥(OL LL)] T.actT g x :=
  TensorProduct.map_tmul _ _ _ _

set_option maxHeartbeats 1000000 in
theorem actB_mul_a (T : QLat LL) (g h : Gl l) (o : OB l ↥(OL LL)) (x : ↥T.L.T) :
    actB (sQ l) T (g * h) (o ⊗ₜ[↥(OL LL)] x) = actB (sQ l) T g (actB (sQ l) T h (o ⊗ₜ[↥(OL LL)] x)) := by
  have e1 := actB_tmul T (g*h) o x
  have e2 := actB_tmul T h o x
  have e3 := actB_tmul T g (galOB _ (sQ l h) o) (T.actT h x)
  refine e1.trans (Eq.trans ?_ ((congrArg (actB (sQ l) T g) e2).trans e3).symm)
  refine congrArg₂ (fun a b => a ⊗ₜ[↥(OL LL)] b) ?_ (actT_mul T g h x)
  rw [map_mul]
  exact galOB_mul' _ _ o

theorem actB_mul (T : QLat LL) (g h : Gl l) (y : TW (OB l ↥(OL LL)) T) :
    actB (sQ l) T (g * h) y = actB (sQ l) T g (actB (sQ l) T h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul o x => exact actB_mul_a T g h o x

theorem abs_cocycle {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (Fg Fh Fgh : M →ₗ[R] M)
    (hmul : ∀ y, Fgh y = Fg (Fh y)) (b y1 y2 y3 : M) (r : R) (e1 : y1 = r • (Fg b - b))
    (e2 : y2 = r • (Fh b - b)) (e3 : y3 = r • (Fgh b - b)) : y3 = Fg y2 + y1 := by
  rw [e3, e2, e1, hmul, map_smul, map_sub, ← smul_add]
  congr 1
  abel

theorem pow_le_mem (T : QLat LL) {k n : ℕ} (hk : k ≤ n) (v : T.V) (hv : (l : ↥LL.1) ^ k • v ∈ T.L.T) :
    (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul]
  exact lpow_smul_mem T _ _ hv


set_option maxHeartbeats 2000000 in
theorem cocycle (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V) (hc : IsCobOf (sQ l) T b c)
    (g h : Gl l) : c (g * h) = c g + T.ρ g (c h) := by
  obtain ⟨n1, h1⟩ := exists_pow_smul_mem T (c g)
  obtain ⟨n2, h2⟩ := exists_pow_smul_mem T (c h)
  obtain ⟨n3, h3⟩ := exists_pow_smul_mem T (c (g * h))
  have m1 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h1
  have m2 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h2
  have m3 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h3
  have e1 := hc g _ ⟨_, m1⟩ rfl
  have e2 := hc h _ ⟨_, m2⟩ rfl
  have e3 := hc (g * h) _ ⟨_, m3⟩ rfl
  have key : (⟨_, m3⟩ : ↥T.L.T) = T.actT g ⟨_, m2⟩ + ⟨_, m1⟩ := by
    apply inj1 l LL T
    have := abs_cocycle (actB (sQ l) T g) (actB (sQ l) T h) (actB (sQ l) T (g * h)) (actB_mul T g h) _ _ _ _ _ e1 e2 e3
    refine this.trans ?_
    refine (congrArg (· + _) (actB_tmul_one T g _)).trans ?_
    exact (TensorProduct.tmul_add _ _ _).symm
  have key' := congrArg (fun z : ↥T.L.T => (z : T.V)) key
  simp only [Submodule.coe_add] at key'
  change (l : ↥LL.1) ^ (n1 + n2 + n3) • c (g * h) =
    T.ρ g ((l : ↥LL.1) ^ (n1 + n2 + n3) • c h) + (l : ↥LL.1) ^ (n1 + n2 + n3) • c g at key'
  rw [map_smul, ← smul_add] at key'
  have hl : ((l : ↥LL.1) ^ (n1 + n2 + n3)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  rw [smul_right_injective T.V hl key', add_comm]

theorem c_one (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V) (hc : IsCobOf (sQ l) T b c) :
    c 1 = 0 := by
  have h := cocycle T b c hc 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.1 h

theorem contAt_one (hl2 : l ≠ 2) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V)
    (hc : IsCobOf (sQ l) T b c) : ContinuousAt c 1 := by
  rw [ContinuousAt, c_one T b c hc]
  intro U hU
  obtain ⟨m, hm⟩ := nbhd l LL T U hU
  rw [Filter.mem_map]
  filter_upwards [cont1 l hl2 LL T b c hc m] with g hg
  obtain ⟨x, hx, e⟩ := hg
  rw [Set.mem_preimage, e]
  exact hm x hx

theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T)
    (c : Gl l → T.V), IsCobOf (sQ l) T b c → c ∈ continuousCocycles T.ρ := by
  intro l _ hl2 LL T b c hc
  refine ⟨?_, cocycle T b c hc⟩
  have h1 := contAt_one hl2 T b c hc
  have hρ : ∀ g : Gl l, Continuous (T.ρ g) := fun g =>
    IsModuleTopology.continuous_of_linearMap (T.ρ g)
  rw [continuous_iff_continuousAt]
  intro g0
  have e : c = fun g => c g0 + T.ρ g0 (c (g0⁻¹ * g)) := by
    funext g
    rw [← cocycle T b c hc, mul_inv_cancel_left]
  rw [e]
  refine continuousAt_const.add ((hρ g0).continuousAt.comp ?_)
  refine ContinuousAt.comp (f := fun g => g0⁻¹ * g) ?_ (continuous_const.mul continuous_id).continuousAt
  simpa using h1

end GlobalTheory.CobCont
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.extensionLattice_isCrysTameTypeWithJumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ), (0 : ZMod e) ∈ Sig → (0 : ℤ) ∈ U → IsGood a ϖ Pl (unitLat (Gl l) : QLat LL) Sig U ∧ ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ (Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L) (v : Tp.V), IsSESLat (Qp := ℚ_[l]) f g ∧ v ∈ Tp.L.T ∧ g.f v = (1 : ↥LL.1) ∧ (∀ h, Tp.ρ h v - v = f.f (c h)) ∧ IsGood a ϖ Pl Tp Sig U := by
  first | exact @GlobalTheory.ExtGood.extLat_isGood | exact GlobalTheory.ExtGood.extLat_isGood | (intros; apply GlobalTheory.ExtGood.extLat_isGood <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisDisc

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem ev_alg (n : ℕ) (x : _root_.Formalism.Per.AinfP l) :
    Per.ev l n (algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
  GlobalTheory.RingIface.ev_alg l n x

theorem norm_l_le : ‖((l : ℕ) : bk.DA bk.ρ₀)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : bk.DA bk.ρ₀) = ofPre l (bk.ev X) bk.ρ₀
      (algebraMap (Ainf l) (PreDisc l (bk.ev X) bk.ρ₀) (((l : ℕ) : Ainf l) ^ 1 * (bk.ev X) ^ 0) *
        IsLocalization.Away.invSelf ((l : ℕ) : Ainf l) ^ 0) := by
    simp [map_natCast]
  rw [e, norm_ofPre]
  exact gauge_le l (bk.ev X) bk.ρ₀ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, by
    rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], rfl⟩)

theorem norm_l_pow_le (r : ℕ) : ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r‖ ≤ ((l : ℝ)⁻¹) ^ r := by
  induction r with
  | zero => simpa using norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (1 : Ainf l)
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (norm_l_le bk) (norm_nonneg _) (by positivity))

def psi : _root_.Formalism.Per.AinfP l →+* bk.DA bk.ρ₀ :=
  IsLocalization.Away.lift (S := _root_.Formalism.Per.AinfP l) ((l : ℕ) : _root_.Formalism.Per.Ainf l) (g := bk.iA)
    (by rw [map_natCast]; exact isUnit_l_disc l (bk.ev X) bk.ρ₀)

theorem psi_alg_pt (a : _root_.Formalism.Per.Ainf l) : psi bk (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a) = bk.iA a :=
  IsLocalization.Away.lift_eq _ _ a

theorem gamma_acris0 (γ : _root_.Formalism.Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (_root_.Formalism.Per.Acris l) a) = bk.iA a) (s : _root_.Formalism.Per.Acris0 l) :
    γ (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) s) =
      psi bk (s : _root_.Formalism.Per.AinfP l) := by
  set ψ : _root_.Formalism.Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hψa : ∀ a : Ainf l, ψ (algebraMap (Ainf l) (_root_.Formalism.Per.AinfP l) a) = bk.iA a := psi_alg_pt bk
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : _root_.Formalism.Per.Ainf l) (s : _root_.Formalism.Per.AinfP l)
  have hs : s * ((l : ℕ) : _root_.Formalism.Per.Acris0 l) ^ n = algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris0 l) a := by
    apply Subtype.ext
    show (s : _root_.Formalism.Per.AinfP l) * ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ n = algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a
    rw [← h, map_natCast]
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ n) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n
  refine hu.mul_left_injective ?_
  have h1 := congrArg (fun t => γ (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) t)) hs
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 := congrArg ψ h
  simp only [map_mul, map_pow, map_natCast] at h2
  rw [← GlobalTheory.RingIface.tower l a] at h1
  exact h1.trans ((hγ a).trans ((hψa a).symm.trans h2.symm))

end GlobalTheory.AcrisDisc

namespace GlobalTheory.AcrisDisc

theorem isClosed_range_E_pow {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ) :
    IsClosed (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hl.out.one_lt)
    (neg_neg_of_pos (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hnorm := norm_E_mul_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ le_rfl hρ1
  set c : ℝ := (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree with hc_def
  have hc : 0 < c := pow_pos (by exact_mod_cast hρ0) _
  have hpow : ∀ (k : ℕ) (v : bk.DA bk.ρ₀), c ^ k * ‖v‖ ≤ ‖bk.iS bk.E ^ k * v‖ := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have e := hnorm (bk.iS bk.E ^ k * v)
      change ‖bk.iS bk.E * (bk.iS bk.E ^ k * v)‖ = c * ‖bk.iS bk.E ^ k * v‖ at e
      have e2 : bk.iS bk.E ^ (k + 1) * v = bk.iS bk.E * (bk.iS bk.E ^ k * v) := by rw [pow_succ', mul_assoc]
      rw [e2, e, pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih v) hc.le
  set f := AddMonoidHom.mulLeft (bk.iS bk.E ^ m) with hf
  have hcm : 0 < c ^ m := pow_pos hc m
  have hb : ∀ v, ‖v‖ ≤ ((Real.toNNReal (c ^ m)⁻¹ : ℝ≥0) : ℝ) * ‖f v‖ := fun v => by
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hcm.le), hf, AddMonoidHom.coe_mulLeft, inv_mul_eq_div,
      le_div_iff₀ hcm, mul_comm]
    exact hpow m v
  exact (AddMonoidHomClass.antilipschitz_of_bound f hb).isClosed_range
    (AddMonoidHomClass.uniformContinuous_of_bound f ‖bk.iS bk.E ^ m‖ fun v => norm_mul_le _ _)

theorem mem_kerTheta_pow_of_mem_filtration {l : ℕ} [hl : Fact l.Prime] (C : Core l) (m N r : ℕ) (s : _root_.Formalism.Per.Acris0 l) (z : _root_.Formalism.Per.Acris l)
    (a : _root_.Formalism.Per.Ainf l)
    (ha : Per.ev l m (((l : ℕ) : _root_.Formalism.Per.BdRp l) ^ N * C.j z) =
      Ideal.Quotient.mk _ (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a))
    (hy : C.j (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) s + ((l : ℕ) : _root_.Formalism.Per.Acris l) ^ r * z) ∈ _root_.Formalism.Per.FilP l m) :
    ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ N * (s : _root_.Formalism.Per.AinfP l) +
      ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ r * algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a ∈ Per.kerP l ^ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmemF : C.j (((l : ℕ) : _root_.Formalism.Per.Acris l) ^ N *
      (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) s + ((l : ℕ) : _root_.Formalism.Per.Acris l) ^ r * z)) ∈ _root_.Formalism.Per.FilP l m := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  have h0 : Per.ev l m (C.j (((l : ℕ) : _root_.Formalism.Per.Acris l) ^ N *
      (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) s + ((l : ℕ) : _root_.Formalism.Per.Acris l) ^ r * z))) = 0 :=
    (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hmemF
  have e : C.j (((l : ℕ) : _root_.Formalism.Per.Acris l) ^ N *
      (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) s + ((l : ℕ) : _root_.Formalism.Per.Acris l) ^ r * z)) =
      ((l : ℕ) : _root_.Formalism.Per.BdRp l) ^ N * algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) (s : _root_.Formalism.Per.AinfP l) +
      ((l : ℕ) : _root_.Formalism.Per.BdRp l) ^ r * (((l : ℕ) : _root_.Formalism.Per.BdRp l) ^ N * C.j z) := by
    rw [map_mul, map_add (f := _), map_mul, map_pow, map_pow, map_natCast, C.j_cris.on0]
    ring
  rw [e, map_add (f := _), map_mul, map_mul, ha, map_pow, map_pow, map_natCast, ev_alg] at h0
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast]
  exact h0

theorem acris_dense {l : ℕ} [Fact l.Prime] (y : _root_.Formalism.Per.Acris l) (r : ℕ) :
    ∃ (s : _root_.Formalism.Per.Acris0 l) (z : _root_.Formalism.Per.Acris l),
      y = algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) s + ((l : ℕ) : _root_.Formalism.Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨s, z, h⟩ := GlobalTheory.PerfectCompletion.dense ((l : ℕ) : _root_.Formalism.Per.Acris0 l) (e y) r
  refine ⟨s, e.symm z, e.injective ?_⟩
  rw [map_add (f := _), map_mul, map_pow, map_natCast, he, e.apply_symm_apply,
    ← map_natCast (algebraMap (_root_.Formalism.Per.Acris0 l) (AdicCompletion (Ideal.span {((l : ℕ) : _root_.Formalism.Per.Acris0 l)}) (_root_.Formalism.Per.Acris0 l)))]
  exact h

theorem approx {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : _root_.Formalism.Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (_root_.Formalism.Per.Acris l) a) = bk.iA a) (h1 : ∀ x, ‖γ x‖ ≤ 1)
    (m N r : ℕ) (s : _root_.Formalism.Per.Acris0 l) (z : _root_.Formalism.Per.Acris l) (a : _root_.Formalism.Per.Ainf l) (w : _root_.Formalism.Per.AinfP l)
    (hw : ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ N * (s : _root_.Formalism.Per.AinfP l) +
      ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ r * algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a =
        algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (bk.ev bk.E) ^ m * w) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) s + ((l : ℕ) : _root_.Formalism.Per.Acris l) ^ r * z) -
      bk.iS bk.E ^ m * psi bk w‖ ≤ ((l : ℝ)⁻¹) ^ r * 2 := by
  set ψ : _root_.Formalism.Per.AinfP l →+* bk.DA bk.ρ₀ := psi bk with hψ
  have hE : ψ (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (bk.ev bk.E)) = bk.iS bk.E := psi_alg_pt bk _
  have ha : ψ (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a) = bk.iA a := psi_alg_pt bk _
  have hx := congrArg ψ hw
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, ha, map_mul, map_pow, hE] at hx
  have hdiff : ((l : ℕ) : bk.DA bk.ρ₀) ^ N *
      γ (algebraMap (_root_.Formalism.Per.Acris0 l) (_root_.Formalism.Per.Acris l) s + ((l : ℕ) : _root_.Formalism.Per.Acris l) ^ r * z) - bk.iS bk.E ^ m * ψ w =
      ((l : ℕ) : bk.DA bk.ρ₀) ^ r * (γ (((l : ℕ) : _root_.Formalism.Per.Acris l) ^ N * z) - bk.iA a) := by
    rw [← hx, map_add (f := _), gamma_acris0 bk γ hγ s, map_mul, map_mul, map_pow, map_pow, map_natCast]
    ring
  rw [hdiff]
  refine (norm_mul_le _ _).trans (mul_le_mul (norm_l_pow_le bk r) ?_ (norm_nonneg _) (by positivity))
  refine (norm_sub_le _ _).trans ?_
  have := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) a
  have := h1 (((l : ℕ) : _root_.Formalism.Per.Acris l) ^ N * z)
  change ‖bk.iA a‖ ≤ 1 at *
  linarith

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : _root_.Formalism.Per.Acris l →+* bk.DA bk.ρ₀),
    (∀ a : Ainf l, γ (algebraMap (Ainf l) (_root_.Formalism.Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) →
    ∀ (m : ℕ) (y : _root_.Formalism.Per.Acris l), C.j y ∈ _root_.Formalism.Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  intro l hl K bk C γ hγ h1 m y hy
  have hker : Per.kerP l ^ m = Ideal.span {algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (bk.ev bk.E) ^ m} := by
    rw [ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by
      rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton], Ideal.span_singleton_pow]
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  have hmem : ((l : ℕ) : bk.DA bk.ρ₀) ^ N * γ y ∈ closure (Set.range fun v : bk.DA bk.ρ₀ => bk.iS bk.E ^ m * v) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hl.out.one_lt)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (half_pos hε) hlt
    obtain ⟨s, z, hyz⟩ := acris_dense y r
    obtain ⟨a, ha⟩ := hN z
    have hx := mem_kerTheta_pow_of_mem_filtration C m N r s z a ha (hyz ▸ hy)
    rw [hker, Ideal.mem_span_singleton] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨bk.iS bk.E ^ m * psi bk w, ⟨psi bk w, rfl⟩, ?_⟩
    rw [dist_eq_norm, hyz]
    have := approx bk γ hγ h1 m N r s z a w hw
    linarith
  rw [(isClosed_range_E_pow bk m).closure_eq] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hu : IsUnit (((l : ℕ) : bk.DA bk.ρ₀) ^ N) := (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow N
  rw [← hu.dvd_mul_left]
  exact ⟨v, hv.symm⟩

end GlobalTheory.AcrisDisc
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem flatPow_dvd_perPow_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (M n : ℕ), ∃ (c : ℕ) (y : Ainf l), (l : Ainf l) ^ n ∣ bk.ev X ^ c - τ ^ M * y := by
  intro l _ K bk τ hτ M n
  have hU : IsUnit (inclW l (τ ^ M)) := by
    rw [map_pow]
    exact (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1.pow M
  obtain ⟨m, t, h⟩ := GlobalTheory.BSP.BddDen.main l K bk (τ ^ M) hU n
  refine ⟨m, t, ?_⟩
  have : bk.ev X ^ m - τ ^ M * t = -(t * τ ^ M - bk.ev X ^ m) := by ring
  rw [this]
  exact (dvd_neg).2 h

end GlobalTheory.BKLim
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_framedMatrices_of_etaleRealisation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K M (ainfObj K) (ainfId K) T ρ j → ∃ (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U ∧ ∀ k, j (M.tr bk.ι (e k)) = ∑ i, U i k ⊗ₜ[ℤ_[l]] b i := by
  apply _root_.GlobalTheory.BSP.exists_mReal_of_realises <;> assumption
end
