module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle483
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TorsionExponentCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle383
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle535
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

section Lin
variable {n k : Type} [Fintype n] [DecidableEq n] [CommRing k]

theorem gl_mulVec_inv_mulVec (X : GL n k) (v : n → k) :
    (X : Matrix n n k) *ᵥ (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_inv_mulVec_mulVec (X : GL n k) (v : n → k) :
    ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ ((X : Matrix n n k) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_conj_mulVec (X g : GL n k) (v : n → k) :
    ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v =
      (X : Matrix n n k) *ᵥ ((g : Matrix n n k) *ᵥ (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul]

theorem conj_fix_hyperplane_iff (X g : GL n k) (a : n → k) :
    (∀ v, a ⬝ᵥ v = 0 → ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v = v) ↔
      ∀ w, (a ᵥ* (X : Matrix n n k)) ⬝ᵥ w = 0 → (g : Matrix n n k) *ᵥ w = w := by
  constructor
  · intro h w hw
    have h1 := h ((X : Matrix n n k) *ᵥ w) (by rw [Matrix.dotProduct_mulVec]; exact hw)
    rw [gl_conj_mulVec, gl_inv_mulVec_mulVec] at h1
    have h2 := congrArg (fun u => ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ u) h1
    simpa only [gl_inv_mulVec_mulVec] using h2
  · intro h v hv
    rw [gl_conj_mulVec, h _ (by rw [← Matrix.dotProduct_mulVec, gl_mulVec_inv_mulVec]; exact hv),
      gl_mulVec_inv_mulVec]

theorem conj_triv_mod_line_iff (X g : GL n k) (a : n → k) :
    (∀ v, ∃ c : k, ((X * g * X⁻¹ : GL n k) : Matrix n n k) *ᵥ v - v = c • a) ↔
      ∀ w, ∃ c : k, (g : Matrix n n k) *ᵥ w - w = c • (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ a) := by
  constructor
  · intro h w
    obtain ⟨c, h1⟩ := h ((X : Matrix n n k) *ᵥ w)
    rw [gl_conj_mulVec, gl_inv_mulVec_mulVec] at h1
    have h2 := congrArg (fun u => ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ u) h1
    exact ⟨c, by simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, gl_inv_mulVec_mulVec] using h2⟩
  · intro h v
    obtain ⟨c, h1⟩ := h (((X⁻¹ : GL n k) : Matrix n n k) *ᵥ v)
    have h2 := congrArg (fun u => (X : Matrix n n k) *ᵥ u) h1
    refine ⟨c, ?_⟩
    rw [gl_conj_mulVec]
    simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, gl_mulVec_inv_mulVec] using h2

theorem vecMul_gl_ne_zero (X : GL n k) {a : n → k} (ha : a ≠ 0) : a ᵥ* (X : Matrix n n k) ≠ 0 := by
  intro h
  apply ha
  have h2 := congrArg (fun u => u ᵥ* ((X⁻¹ : GL n k) : Matrix n n k)) h
  simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h2
  exact h2

theorem gl_inv_mulVec_ne_zero (X : GL n k) {a : n → k} (ha : a ≠ 0) :
    ((X⁻¹ : GL n k) : Matrix n n k) *ᵥ a ≠ 0 := by
  intro h
  apply ha
  rw [← gl_mulVec_inv_mulVec X a, h, Matrix.mulVec_zero]

theorem det_conj_gl (X g : GL n k) :
    Matrix.GeneralLinearGroup.det (X * g * X⁻¹) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem ite_congr_of_iff {p q : Prop} {dp : Decidable p} {dq : Decidable q} {u v : ℂ} (h : p ↔ q) :
    @ite ℂ p dp u v = @ite ℂ q dq u v := if_congr h rfl rfl

end Lin

theorem mirC_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ) (x : G), ∃ a' : Fin D.R.r → kP PP.1, a' ≠ 0 ∧ ∀ g, mirC R i PP a tr ε (x * g * x⁻¹) = mirC R i PP a' tr ε g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i PP a ha tr ε x
  have he : ∀ g PP', R.eG (x * g * x⁻¹) PP' = R.eG x PP' * R.eG g PP' * (R.eG x PP')⁻¹ := by
    intro g PP'
    rw [map_mul, map_mul, map_inv]
    rfl
  have h1 : ∀ g, (∀ PP', PP' ≠ PP → R.eG (x * g * x⁻¹) PP' = 1) ↔ ∀ PP', PP' ≠ PP → R.eG g PP' = 1 := by
    intro g
    refine forall_congr' fun PP' => forall_congr' fun _ => ?_
    rw [he, conj_eq_one_iff]
  have h2 : ∀ g, Matrix.GeneralLinearGroup.det (R.eG (x * g * x⁻¹) PP) = Matrix.GeneralLinearGroup.det (R.eG g PP) := by
    intro g
    rw [he]
    exact det_conj_gl _ _
  cases tr
  · refine ⟨_, vecMul_gl_ne_zero (R.eG x PP) ha, fun g => ?_⟩
    have h3 := conj_fix_hyperplane_iff (R.eG x PP) (R.eG g PP) a
    rw [← he] at h3
    unfold mirC
    rw [h2]
    refine ite_congr_of_iff (and_congr (h1 g) ?_)
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    exact h3
  · refine ⟨_, gl_inv_mulVec_ne_zero (R.eG x PP) ha, fun g => ?_⟩
    have h3 := conj_triv_mod_line_iff (R.eG x PP) (R.eG g PP) a
    rw [← he] at h3
    unfold mirC
    rw [h2]
    refine ite_congr_of_iff (and_congr (h1 g) ?_)
    rw [if_pos rfl, if_pos rfl]
    exact h3

end GlobalTheory.DownLift.GenFinite
end

section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace CompanionTheory.Member.ThetaTranslation

theorem thetaKO_translate {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hom : IsWeilDatumO ψ S T χS χT om) (θ : InfFam D)
    (hθ : IsInfFam θ) (z : GA D S) (hz : z ∈ GfC S) (sS sT BS BT) (f : WO S T → ℂ) (P) (hf : IsThetaFunO ψ S T f)
    (c : ℂ) (h : GA D S) (g : GA D T) :
    thetaKO om h g (pureTensorO ψ θ S T sS sT BS BT (c • om (z, 1) f) P) =
      c * thetaKO om (h * z) g (pureTensorO ψ θ S T sS sT BS BT f P) := by
  rw [GlobalTheory.FiniteFock.pureTensorO_smul,
    ← GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ S T χS χT om hom θ hθ z hz 1 (one_mem _) sS sT BS BT f P hf]
  unfold thetaKO
  have e : ((h * z, g) : GA D S × GA D T) = (h, g) * (z, 1) := by rw [Prod.mk_mul_mk, mul_one]
  rw [e, map_mul, map_smul, Module.End.mul_apply, Pi.smul_apply, smul_eq_mul]

end CompanionTheory.Member.ThetaTranslation


theorem CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i t z c hz u h w g
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h1 := hC.thP.pt_theta i t 1
    unfold RealDat.ptP at h1
    rwa [GlobalTheory.FiniteFock.pureTensorO_one] at h1
  exact CompanionTheory.Member.ThetaTranslation.thetaKO_translate R.ψ _ _ _ _ (R.ωP i t) (hC.thP.ωP i t) R.θ hC.models.inf z hz _ _ _ _ _ _ hf c h g

end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
theorem _root_.GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  first | exact @CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class | exact CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class | (intros; apply CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class <;> assumption)

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical



namespace GlobalTheory.FlatFourierQ

theorem unitOff_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_prod' {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_of_dvd {N q m : ℕ} {C : ℂ} (hq : q ∣ N) (h0 : C ≠ 0) (hC : IsIntegral ℤ C)
    (hCq : IsIntegral ℤ ((q : ℂ) ^ m * C⁻¹)) : UnitOff N C := by
  obtain ⟨d, rfl⟩ := hq
  have hint : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine ⟨h0, m, ((hint _).pow m).mul hC, ?_⟩
  have e : ((q * d : ℕ) : ℂ) ^ m * C⁻¹ = (d : ℂ) ^ m * ((q : ℂ) ^ m * C⁻¹) := by push_cast; ring
  rw [e]; exact ((hint d).pow m).mul hCq

theorem dite_prod' {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_eq_unit_mul_flat_transform : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n N : ℕ), 0 < N → (∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1 ∧ Nat.card (kP PP) ∣ N) → ∃ Gc : ℂ, UnitOff N Gc ∧ ∀ ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) ub = Gc * ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)), omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) * ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  intro D _ Q ξ ψP r n N _ hQ
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  have hloc : ∀ PP : ↥Q, ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧
      IsIntegral ℤ ((Nat.card (kP PP.1) : ℂ) ^ m * C⁻¹) ∧
      ∀ u : Matrix (Fin n) (Fin r) (kP PP.1),
        (∑ y : Matrix (Fin r) (Fin n) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C * fq PP.1 u := by
    intro PP
    letI := Ideal.Quotient.field PP.1.asIdeal
    obtain ⟨C, m, h0, h1, h2, h3⟩ :=
      GlobalTheory.T.fourier_flat_character_datum_finiteField (kP PP.1) (ψP PP.1) (ξ PP.1) r n (hQ _ PP.2).1 (hQ _ PP.2).2.1
    exact ⟨C, m, h0, h1, by rw [Nat.card_eq_fintype_card]; exact h2, h3⟩
  choose C m hC0 hCi hCm hCe using hloc
  refine ⟨(∏ PP : ↥Q, C PP)⁻¹, ?_, fun ub => ?_⟩
  · have hu : UnitOff N (∏ PP : ↥Q, C PP) :=
      unitOff_prod' _ _ fun PP _ => unitOff_of_dvd (hQ _ PP.2).2.2 (hC0 PP) (hCi PP) (hCm PP)
    obtain ⟨h0, e, h1, h2⟩ := hu
    exact ⟨inv_ne_zero h0, e, h2, by rw [inv_inv]; exact h1⟩
  · have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
      rw [← Finset.attach_eq_univ]
      unfold omegaQ
      convert dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
      intro y
      have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP),
          omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
        intro Y
        unfold omegaFlat
        convert dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
      rw [e0, Finset.attach_eq_univ]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [dif_pos PP.2, Subtype.coe_eta]
    simp only [hf, ← Finset.prod_mul_distrib]
    have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin n) (kP PP.1))))
      (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin n) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
    rw [Fintype.piFinset_univ] at hs
    rw [← hs]
    simp only [hCe]
    rw [Finset.prod_mul_distrib, hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatFourierQ
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjFix

variable {D : D7}

noncomputable def starOEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  { Formalism.L2.DIV.starOHom (E := D.host.E) with
    invFun := Formalism.L2.DIV.starOHom (E := D.host.E)
    left_inv := fun a => Formalism.L2.DIV.starO_starO a
    right_inv := fun a => Formalism.L2.DIV.starO_starO a }

theorem natCast_mem_conjPl_iff (PP : Pl D.host.E) (N : ℕ) :
    ((N : 𝓞 D.host.E)) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔ ((N : 𝓞 D.host.E)) ∈ PP.asIdeal := by
  show Formalism.L2.DIV.starOHom (N : 𝓞 D.host.E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem absNorm_conjPl (PP : Pl D.host.E) :
    Ideal.absNorm (Formalism.L2.DIV.conjPl PP).asIdeal = Ideal.absNorm PP.asIdeal := by
  have h : (Formalism.L2.DIV.conjPl PP).asIdeal = PP.asIdeal.map (starOEquiv (D := D)) := by
    rw [← Ideal.comap_symm]; rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv PP.asIdeal (Formalism.L2.DIV.conjPl PP).asIdeal (starOEquiv (D := D)) h).toEquiv).symm

theorem fixBase_split_conj {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E) :
    FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
      τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) =
        (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  intro hF hN
  have hN' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    rwa [natCast_mem_conjPl_iff]
  have := hF.split (Formalism.L2.DIV.conjPl PP) hN'
  rwa [absNorm_conjPl] at this

end GlobalTheory.ConjFix
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX.SplitDecl

theorem splitRowPrime_of {D : D7} {L : SizeData₂ D} {X : KillingConditions.HubData D} (i : D.nd.Loc)
    (hg : D.nd.l i ∉ TwistedPlaces.gset D) (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
  rw [e]
  fin_cases k <;> simp [TwistedPlaces.gset]

theorem main : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D),
    GlobalTheory.HubX.Canon L HW R X → ∀ (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc), TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D →
    KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) →
    EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ) ∧
      ∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1 := by
  intro D L HW R X h hJ i _ hg hr hs
  have hsp := splitRowPrime_of (L := L) (X := X) i hg hr hs
  refine ⟨GlobalTheory.HubX.Check.decl h hJ i hg hr hs ((GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime D i hJ.choose hsp).1), ?_⟩
  intro v hv
  exact (GlobalTheory.SplitPlaces.placesSplit D.host (D.nd.l i) hsp v hv).1

end GlobalTheory.HubX.SplitDecl
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ), ∀ x ∈ J ^ (n + 1), D.δ x ∈ J ^ n := by
  first | exact @GlobalTheory.BSP.delta_pow_succ_mem_pow | exact GlobalTheory.BSP.delta_pow_succ_mem_pow | (intros; apply GlobalTheory.BSP.delta_pow_succ_mem_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_finite_product_oriented_boundedPrisms : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R), (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∃ (Q : Obj l R) (π : ∀ i, Hom Q (C i)), Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) ∧ (∀ x, x ∈ Q.I ↔ ∀ i, (π i).f x ∈ (C i).I) ∧ ∀ (Z : Obj l R) (a : ∀ i, Hom Z (C i)), ∃ c : Hom Z Q, ∀ i, (π i).comp c = a i := by
  first | exact @GlobalTheory.Prism.finite_product_oriented | exact GlobalTheory.Prism.finite_product_oriented | (intros; apply GlobalTheory.Prism.finite_product_oriented <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.finite_projective_module_element_descent_equalizer : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), p.comp f = q.comp f → Function.Injective f → (∀ b, p b = q b → b ∈ f.range) → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] (PB : Type) [AddCommGroup PB] [Module B PB] (PD : Type) [AddCommGroup PD] [Module D PD] (u : P →ₛₗ[f] PB) (u₁ : PB →ₛₗ[p] PD) (u₂ : PB →ₛₗ[q] PD) (w : P →ₛₗ[p.comp f] PD), SemiBC u → SemiBC w → (∀ x, w x = u₁ (u x)) → (∀ x, w x = u₂ (u x)) → Function.Injective u ∧ ∀ z, u₁ z = u₂ z → ∃ y, u y = z := by
  first | exact @GlobalTheory.BSP.ProjDescent.descent | exact GlobalTheory.BSP.ProjDescent.descent | (intros; apply GlobalTheory.BSP.ProjDescent.descent <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_σF_self {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Per.Fl l) : x ∣ Per.σF g x := by
  apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
  rw [GlobalTheory.RingBasics.untilt_σF]
  generalize x.untilt = y
  by_cases hy : (y : ℂ_[l]) = 0
  · obtain rfl : y = 0 := Subtype.ext hy
    simp
  · refine ⟨⟨Per.σC g y / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, GlobalTheory.RingBasics.norm_σC, div_self (norm_ne_zero_iff.2 hy)]
    · rw [GlobalTheory.RingIface.sigO_coe]
      change Per.σC g y = (y : ℂ_[l]) * (Per.σC g y / y)
      field_simp

theorem galois_discMap : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)) ∧ ∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l,
      ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G := by
  intro l _ K bk
  have h : ∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X) := fun g => by
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich]
    exact map_dvd (WittVector.teichmuller l) (dvd_σF_self g bk.flat)
  refine ⟨h, fun ρ hρ g => ⟨_, isDiscMap_map (Per.σA g) ?_⟩⟩
  obtain ⟨c, hc⟩ := h g
  have h1 := norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  rw [pow_one, pow_one] at h1
  rw [hc, map_mul]
  exact (norm_mul_le _ _).trans ((mul_le_mul h1 (norm_toDisc_le c) (norm_nonneg _) ρ.2).trans (mul_one _).le)

end GlobalTheory.BSP
end
