module

public import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Perfectoid.Untilt
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle154
public import Mathlib.Topology.Instances.Matrix
public import GroundTheory.LocalFields.Interface
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Defs
public import GroundTheory.LocalFields.UnramifiedNormSurj
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle159
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle151
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Formalism.CharacterColumnKernels.Bundle001
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.LocalFields.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.LocDualInt

theorem exists_root_pow_cyclotomicCharacter_congr {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ) :
    ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) =
      PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
        (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  classical
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity (PadicAlgCl p) (p ^ i) := fun i => by
    haveI : NeZero ((p ^ i : ℕ) : PadicAlgCl p) :=
      ⟨by exact_mod_cast pow_ne_zero i (Fact.out : p.Prime).ne_zero⟩
    infer_instance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ k)
  refine ⟨ζ, hζ.pow_eq_one, fun a ha => ?_⟩
  set c : ZMod (p ^ k) := PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) with hc
  have hspec := cyclotomicCharacter.spec (L := PadicAlgCl p) p
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one
  have hg : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ := rfl
  rw [hg, ha] at hspec
  have hpos : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, hpos, hζ.pow_eq_one⟩
  have hmod : a ≡ c.val [MOD orderOf ζ] := hfin.pow_eq_pow_iff_modEq.mp hspec
  rw [← hζ.eq_orderOf] at hmod
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod).trans (ZMod.natCast_zmod_val c)

end GlobalTheory.LocDualInt
end

section

namespace GlobalTheory.ArtinSchreierTilt

open Formalism.BasicNotions.Loc

namespace Div

open scoped NNReal
open Ideal

section General

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))] [IsAdicComplete (span {(p : O)}) O]

noncomputable def lift (u : PreTilt O p) (m : ℕ) : O :=
  PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[m]) u)

theorem mk_lift (u : PreTilt O p) (m : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (lift u m) = PreTilt.coeff m u := by
  rw [lift, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem lift_succ_pow (u : PreTilt O p) (m : ℕ) : lift u (m + 1) ^ p = lift u m := by
  rw [lift, lift, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

theorem lift_pow (u : PreTilt O p) (m : ℕ) : lift u m ^ p ^ m = PreTilt.untilt u :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow u m

variable (hv : v.Integers O)
include hv

theorem val_eq_untilt (u : PreTilt O p) (hu : u ≠ 0) :
    PreTilt.val K v O hv p u = v (algebraMap O K (PreTilt.untilt u)) := by
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n u ≠ 0 := not_forall.1 fun h => hu (Perfection.ext h)
  have hn' : (Ideal.Quotient.mk (span {(p : O)}) (lift u n) : ModP O p) ≠ 0 := by rwa [mk_lift]
  change PreTilt.valAux K v O p u = _
  rw [PreTilt.valAux_eq hv hn, ← mk_lift, ModP.preVal_mk hv hn', ← lift_pow u n, map_pow, map_pow]

theorem dvd_of_val_le (x y : PreTilt O p)
    (h : PreTilt.val K v O hv p x ≤ PreTilt.val K v O hv p y) : y ∣ x := by
  by_cases hx : x = 0
  · exact hx ▸ dvd_zero y
  by_cases hy : y = 0
  · exfalso
    apply hx
    rw [← PreTilt.map_eq_zero hv]
    rw [hy, map_zero] at h
    exact le_antisymm h zero_le
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective (algebraMap O K) := hv.hom_inj
  rw [val_eq_untilt hv x hx, val_eq_untilt hv y hy] at h
  have hY : ∀ m, lift y m ≠ 0 := by
    intro m h0
    apply hy
    rw [← PreTilt.map_eq_zero hv, val_eq_untilt hv y hy, ← lift_pow y m, h0,
      zero_pow (pow_ne_zero _ hp0), map_zero, map_zero]
  have hle : ∀ m, v (algebraMap O K (lift x m)) ≤ v (algebraMap O K (lift y m)) := by
    intro m
    have h' := h
    rw [← lift_pow x m, ← lift_pow y m, map_pow, map_pow, map_pow, map_pow] at h'
    exact (pow_le_pow_iff_left₀ zero_le zero_le (pow_ne_zero _ hp0)).1 h'
  choose q hq using fun m => hv.dvd_of_le (hle m)
  have hqs : ∀ m, q (m + 1) ^ p = q m := by
    intro m
    have h1 : lift y m * q (m + 1) ^ p = lift y m * q m := by
      rw [← hq m, ← lift_succ_pow y m, ← mul_pow, ← hq (m + 1), lift_succ_pow]
    have hK : algebraMap O K (lift y m) ≠ 0 := fun h0 => hY m (hinj (h0.trans (map_zero _).symm))
    apply hinj
    have h2 := congrArg (algebraMap O K) h1
    rw [map_mul, map_mul] at h2
    exact mul_left_cancel₀ hK h2
  let e : PreTilt O p :=
    (⟨fun m => Ideal.Quotient.mk (span {(p : O)}) (q m), fun m => by
      simp only
      rw [← map_pow, hqs]⟩ : Perfection (ModP O p) p)
  refine ⟨e, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n x = PreTilt.coeff n (y * e)
  rw [map_mul, ← mk_lift, ← mk_lift, hq n, map_mul]
  rfl

end General

end Div

section Complete

open scoped NNReal
open Ideal

variable {p : ℕ} [Fact p.Prime]

theorem isAdicComplete_OC : IsAdicComplete (span {(p : OC p)}) (OC p) := by
  first | infer_instance | exact Formalism.Per.instIsAdicCompleteOCSpanSingletonSetCast _

end Complete

theorem tiltDiv : PI.ArtSch.TiltDiv := by
  intro l _ x y h
  have := isAdicComplete_OC (p := l)
  exact Div.dvd_of_val_le (PadicComplexInt.integers l) x y h

end GlobalTheory.ArtinSchreierTilt

namespace GlobalTheory

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

noncomputable def unitLat (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] (hO : Function.Injective (algebraMap O LL)) : LocLat G Qp LL O where
  V := LL
  ρ := Representation.trivial LL G LL
  cont := fun x => by simpa using continuous_const
  L :=
    { T := Submodule.span O {1}
      fg := Submodule.fg_span_singleton _
      free := Module.Free.of_equiv
        ((LinearEquiv.ofInjective (LinearMap.toSpanSingleton O LL 1)
          (fun a b h => hO (by simpa [Algebra.smul_def] using h))).trans
          (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range O LL 1).symm))
      span := by
        rw [Submodule.span_span_of_tower, eq_top_iff]
        intro x _
        exact Submodule.mem_span_singleton.2 ⟨x, by simp⟩
      stable := fun g x hx => by simpa using hx }

theorem exists_unitLat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), ∃ one : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), (∀ g x, one.ρ g x = x) ∧ ∃ e : one.V, e ≠ 0 ∧ one.L.T = Submodule.span ↥(OL LL) {e} := by
  intro l _ K LL
  have hO : Function.Injective (algebraMap (↥(OL LL)) ↥LL.1) :=
    Subtype.val_injective
  refine ⟨unitLat (↥(GK K)) ℚ_[l] ↥LL.1 ↥(OL LL) hO, fun _ _ => rfl, (1 : ↥LL.1), ?_, rfl⟩
  show (1 : ↥LL.1) ≠ 0
  exact one_ne_zero

end GlobalTheory.HWL
end

section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie


open PowerSeries in
theorem _root_.GlobalTheory.WachTie.exists_invariant_basis : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}, IsUnit (W.DelF.card : O) → Nonempty (Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) → ∃ b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T), ∀ k, (b k : W.DD T) ∈ W.NΔ T := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W T r hu ⟨b⟩
  classical
  have hmul : ∀ g ∈ W.DelF, ∀ δ ∈ W.DelF, g * δ ∈ W.DelF := by
    intro g hg δ hδ
    obtain ⟨a, ha, hga⟩ := (W.DelF_def g).1 hg
    obtain ⟨c, hc, hδc⟩ := (W.DelF_def δ).1 hδ
    refine (W.DelF_def _).2 ⟨a * c, Nat.mul_pos ha hc, ?_⟩
    rw [mul_pow, pow_mul, hga, one_pow, one_mul, mul_comm, pow_mul, hδc, one_pow]
  have himage : ∀ g ∈ W.DelF, W.DelF.image (g * ·) = W.DelF := by
    intro g hg
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hx
      exact hmul g hg δ hδ
    · rw [Finset.card_image_of_injective _ (mul_right_injective g)]
  let avg : W.DD T →ₗ[O] W.DD T := ((↑hu.unit⁻¹ : O)) • ∑ δ ∈ W.DelF, W.γD T δ
  have havg : ∀ x, avg x = (↑hu.unit⁻¹ : O) • ∑ δ ∈ W.DelF, W.γD T δ x := by
    intro x
    simp [avg, LinearMap.sum_apply]
  have hinv : ∀ g ∈ W.DelF, ∀ x, W.γD T g (avg x) = avg x := by
    intro g hg x

    rw [havg, map_smul, map_sum]
    congr 1
    simp_rw [← W.γD_mul T]
    conv_rhs => rw [← himage g hg]
    rw [Finset.sum_image (fun a _ c _ h => mul_left_cancel h)]
  have hN : ∀ x ∈ W.N T, avg x ∈ W.N T := by
    intro x hx
    rw [havg]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => W.N_Γ T δ x hx)
  open Pointwise in
  have hQ : ∀ x ∈ W.N T, avg x - x ∈ (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • W.N T := by
    intro x hx
    have hsplit : avg x - x = (↑hu.unit⁻¹ : O) • ∑ δ ∈ W.DelF, (W.γD T δ x - x) := by
      rw [havg, Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul O,
        smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [hsplit]
    refine Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => ?_)
    obtain ⟨y, hy, hxy⟩ := W.N_π T δ x hx
    rw [hxy]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hy
  have hb : ∀ k, ∃ y : W.N T, (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • y =
      (⟨avg (b k), hN _ (b k).2⟩ : W.N T) - b k := by
    intro k
    open Pointwise in
    obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hQ _ (b k).2)
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hxy)⟩
  choose y hy using hb
  let g : W.N T →ₗ[_root_.Formalism.BasicNotions.LetA O n] W.N T := b.constr (_root_.Formalism.BasicNotions.LetA O n) y
  let f : W.N T →ₗ[_root_.Formalism.BasicNotions.LetA O n] W.N T := LinearMap.id + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • g
  have hf : ∀ k, f (b k) = ⟨avg (b k), hN _ (b k).2⟩ := by
    intro k
    simp only [f, g, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
      Module.Basis.constr_basis, hy]
    abel
  have hunit : IsUnit f := by
    haveI := Module.Free.of_basis b
    haveI := Module.Finite.of_basis b
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix b]
    have hM : LinearMap.toMatrix b b f = 1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g := by
      simp [f, map_add (f := _), LinearMap.toMatrix_id]
    rw [hM, Pi.isUnit_iff]
    intro i
    rw [PowerSeries.isUnit_iff_constantCoeff]
    let ψ : _root_.Formalism.BasicNotions.LetA O n →+* O :=
      (PowerSeries.constantCoeff (R := O)).comp (Pi.evalRingHom (fun _ : ZMod n => O⟦X⟧) i)
    change IsUnit (ψ (Matrix.det (1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g)))
    rw [RingHom.map_det]
    have h2 : ψ.mapMatrix (1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g) = 1 := by
      ext p q
      simp [ψ, _root_.Formalism.BasicNotions.letπ, Matrix.one_apply]
      split_ifs <;> simp
    rw [h2, Matrix.det_one]
    exact isUnit_one
  have hbij := (Module.End.isUnit_iff f).1 hunit
  refine ⟨b.map (LinearEquiv.ofBijective f hbij), fun k => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply, hf]
  exact ⟨hN _ (b k).2, fun δ hδ => hinv δ hδ _⟩

end GlobalTheory.WachTie
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.flat_wachLetterRing_completion_of_dense_saturated : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (p : ℕ) (E : Type) [CommRing E] [Algebra (LetA O n) E], IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E := by
  first | exact @GlobalTheory.flat_letA_of_dense_sat | exact GlobalTheory.flat_letA_of_dense_sat | (intros; apply GlobalTheory.flat_letA_of_dense_sat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.compactGroup_rep_defined_over_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (a : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l)), Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ L₀ : FinExt l, ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := by
  first | exact @GlobalTheory.CompactRepField.exists_finExt_entries_mem | exact GlobalTheory.CompactRepField.exists_finExt_entries_mem | (intros; apply GlobalTheory.CompactRepField.exists_finExt_entries_mem <;> assumption)
end

section

open ValuativeRel

theorem _root_.GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt : ∀ (F E K L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L] [FiniteDimensional F E] [FiniteDimensional K L], (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = 1 → Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ → (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 := by
  first | exact @GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top | exact GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top | (intros; apply GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top <;> assumption)
end

section

open ValuativeRel

namespace GlobalTheory


open GroundTheory.LocalField IsLocalRing in
theorem unramified_quadratic_uniformizer_trace_norm : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  open GroundTheory.LocalField IsLocalRing in
  intro K L _ _ _ _ _ _ _ _ _ _ _ he h2
  haveI : IsUnramified K L := ⟨he⟩
  have memK : ∀ x : K, x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation K), ← Valuation.vle_iff_le]
  have memL : ∀ x : L, x ∈ 𝒪[L] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation L), ← Valuation.vle_iff_le]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  refine ⟨(ϖ : K), hϖ0, (memK _).1 ϖ.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h1
    have hv : ValuativeRel.valuation K (ϖ : K) = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 ((memK _).1 ϖ.2) |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 h1))
    exact hϖ.not_isUnit ((Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv)
  ·
    rintro ⟨y, hy⟩
    have h := ord_norm (K := K) y
    rw [hy, ord_uniformizer hϖ, IsUnramified.residueDegree_eq_finrank K L, h2] at h
    omega
  ·
    intro y hy
    have hπ := irreducible_algebraMap_of_isUnramified (L := L) hϖ
    set y' : 𝒪[L] := ⟨y, (memL y).2 hy⟩
    by_cases hu : IsUnit y'
    · right
      refine ⟨((hu.unit⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (memL _).1 (hu.unit⁻¹ : 𝒪[L]ˣ).1.2, ?_⟩
      have h := hu.unit.mul_inv
      rw [IsUnit.unit_spec] at h
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) h
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      exact this
    · left
      have hm : y' ∈ maximalIdeal 𝒪[L] := (mem_maximalIdeal y').2 hu
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨(c : L), (memL _).1 c.2, ?_⟩
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) hc
      simp only [y', MulMemClass.coe_mul, coe_algebraMap_integer] at this
      exact this
  ·
    intro s hs
    obtain ⟨a, ha⟩ := trace_integer_surjective (K := K) (L := L) ⟨s, (memK s).2 hs⟩
    refine ⟨(a : L), (memL _).1 a.2, ?_⟩
    rw [← coe_trace_integer, ha]
  ·
    intro s hs1 hs2
    set s' : 𝒪[K] := ⟨s, (memK s).2 hs1⟩
    have hv : ValuativeRel.valuation K s = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 hs1 |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 hs2))
    have hu : IsUnit s' := (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv
    obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := K) (L := L) hu.unit
    refine ⟨((w : 𝒪[L]) : L), (memL _).1 (w : 𝒪[L]).2, ?_⟩
    have := congrArg (fun u : 𝒪[K]ˣ ↦ ((u : 𝒪[K]) : K)) hw
    simp only [coe_normIntegerUnits_eq, IsUnit.unit_spec] at this
    rw [← coe_norm_integer]
    exact this

end GlobalTheory
end

section

open Polynomial
open Classical

theorem _root_.GlobalTheory.T.card_roots_closedBall_bounds_ultrametric : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ), 0 < ρ → f.coeff d ≠ 0 → ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) → d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) → Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by
  first | exact @GlobalTheory.card_roots_le_radius_bounds | exact GlobalTheory.card_roots_le_radius_bounds | (intros; apply GlobalTheory.card_roots_le_radius_bounds <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.charpoly_eq_of_trace_powers : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  first | exact @GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq | exact GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq | (intros; apply GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) → ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by
  first | exact @GlobalTheory.s_points_kpt | exact GlobalTheory.s_points_kpt | (intros; apply GlobalTheory.s_points_kpt <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.matrix_commute_of_commute_separable_charpoly : ∀ (E : Type) [Field E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  first | exact @GlobalTheory.CommSep.commute_of_commute_separable | exact GlobalTheory.CommSep.commute_of_commute_separable | (intros; apply GlobalTheory.CommSep.commute_of_commute_separable <;> assumption)
end
