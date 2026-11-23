module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



private theorem UpperTheory.KN.exists_pow_smul_mem_lattice_alt {l : ℕ} [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T :=
  _root_.UpperTheory.Reformulated.B.LatticePowerSmul.exists_pow_smul_mem_lattice_alt LL T v

theorem _root_.UpperTheory.KN.exists_prime_pow_smul_mem_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V), ∃ (n : ℕ) (x : ↥T.L.T), (x : T.V) = ((l : ℚ_[l]) ^ n) • v := by
  intro l _ LL T v
  obtain ⟨n, hn⟩ := UpperTheory.KN.exists_pow_smul_mem_lattice_alt LL T v
  refine ⟨n, ⟨_, hn⟩, ?_⟩
  rw [← algebraMap_smul ↥LL.1 ((l : ℚ_[l]) ^ n) v, map_pow, map_natCast]
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal



theorem _root_.UpperTheory.KN.exists_tensorBdR_action_on_latticeBdR :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), ∃ B : OdR l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdR l) (v : T.V) (c : Pl.R.BdR), B (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := by
  intro l _ LL T Pl AI Td
  have hz : ∀ z : ℤ_[l], Td.eD.symm (algebraMap ℤ_[l] (Per.BdR l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) :=
    fun z => GlobalTheory.BKGal.JumpDR.cD_algebraMap Td z
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdR l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (Td.eD.symm b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add (f := _), add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdR l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdR l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, hz, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal



private noncomputable def gdR {l : ℕ} [Fact l.Prime] (g : GQ l) : Per.BdR l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := Per.σD g
  commutes' z := (GlobalTheory.MemLoc.FilLaws.σD_alg g (algebraMap ℤ_[l] (Per.BdRp l) z)).trans
    (congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) ((GlobalTheory.GalStep.galD g).commutes z))

private noncomputable def gOdR {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) :
    OdR l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (gdR g)

private theorem gOdR_dRO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) (x : OD l O) :
    gOdR O g (dRO l O x) = dRO l O (GlobalTheory.GalStep.galOD O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.MemLoc.FilLaws.σD_alg g w)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem gOdR_iotaO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (g : GQ l) (x : OB l O) :
    gOdR O g (iotaO O C x) = iotaO O C (galOB O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.BKGal.FilStable.ι_σB C g w).symm
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem act_incl {O G Qp LL R R' : Type} [CommRing O] [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (i : R →ₐ[O] R') (f : R →ₐ[O] R) (f' : R' →ₐ[O] R') (h : ∀ r, f' (i r) = i (f r))
    (T : LocLat G Qp LL O) (g : G) (z : TW R T) :
    TWact f' T g (TWincl i T z) = TWincl i T (TWact f T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem _root_.UpperTheory.KN.latticeTensor_deRham_crys_relation_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (g : Gl l) (y : TW (OD l O) T) (b : TW (OB l O) T) (x : OD l O),
    TWincl (dRO l O) T y = dRO l O x • TWincl (iotaO O C) T b →
    TWincl (dRO l O) T (TWact (GlobalTheory.GalStep.galOD O (sQ l g)) T g y) =
      dRO l O (GlobalTheory.GalStep.galOD O (sQ l g) x) • TWincl (iotaO O C) T (TWact (galOB O (sQ l g)) T g b) := by
  intro l _ O K _ _ _ _ _ _ _ T C g y b x h
  have h1 := act_incl (dRO l O) (GlobalTheory.GalStep.galOD O (sQ l g)) (gOdR O (sQ l g)) (gOdR_dRO O (sQ l g)) T g y
  have h2 := act_incl (iotaO O C) (galOB O (sQ l g)) (gOdR O (sQ l g)) (gOdR_iotaO O C (sQ l g)) T g b
  have h3 := GlobalTheory.GalStep.TWact_smul_of (gOdR O (sQ l g)) T g (dRO l O x) (TWincl (iotaO O C) T b)
  have h4 := gOdR_dRO O (sQ l g) x
  refine h1.symm.trans ((congrArg (TWact (gOdR O (sQ l g)) T g) h).trans (h3.trans ?_))
  rw [h4, h2]
end
