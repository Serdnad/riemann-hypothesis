module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodEqTangentHodgeTate
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem dIn_top_powerSeriesLog (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] :
    DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  intro α i
  have hα : α = Finsupp.single () (α ()) := Finsupp.unique_single α
  have hc : coeff α (PowerSeries.log Q : MvPowerSeries Unit Q)
      = PowerSeries.coeff (α ()) (PowerSeries.log Q) := by
    conv_lhs => rw [hα]
    rfl
  rw [hc, PowerSeries.coeff_log]
  obtain rfl : i = () := rfl
  split_ifs with h
  · exact ⟨0, trivial, by simp⟩
  · refine ⟨(-1) ^ (α () + 1), trivial, ?_⟩
    have h' : ((α () : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [← map_natCast (algebraMap ℚ Q), ← map_mul, mul_div_cancel₀ _ h']
    simp

theorem hasVal_log_of_hasVal_formalLog : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (g : MvPowerSeries σ B) (q : Q), constantCoeff g = 1 → HasVal p z (formalLog (map (algebraMap B Q) g)) q → HasVal p (fun _ : Unit => E g - 1) (PowerSeries.log Q : MvPowerSeries Unit Q) q := by
  intro p _ B O Q _ _ _ _ _ θ hF σ _ _ z hz E hE g q hg hq
  haveI := hF.complete
  have hu : ∀ j : Unit, constantCoeff ((fun _ : Unit => g - 1) j) = 0 := fun _ => by simp [hg]
  have hEu : E (g - 1) = E g - 1 := by rw [map_sub, map_one]
  have hnil : ∃ N : ℕ, (p : B) ∣ (E g - 1) ^ N :=
    hEu ▸ ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p B B σ z hz).2 E hE).2.1 (g - 1) (hu ())
  have hD := dIn_top_powerSeriesLog B Q
  obtain ⟨q', hq', -⟩ := GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs p B O Q θ hF Unit (fun _ => E g - 1) (fun _ => hnil) _ hD
  have h4 := GlobalTheory.T.pAdicEvaluation_subst_compatible_thickening p B O Q θ hF σ z hz E hE Unit (fun _ => g - 1) _ q' hu hD
    (by simpa only [hEu] using hq')
  have h5 : subst (up Q (fun _ : Unit => g - 1)) (PowerSeries.log Q : MvPowerSeries Unit Q)
      = formalLog (map (algebraMap B Q) g) := by
    unfold formalLog PowerSeries.subst up
    simp only [map_sub, map_one]
  rw [h5] at h4
  rwa [HasVal.unique hF hq h4]

end GlobalTheory.QLog
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.tangentVector_quasiLogarithm_of_congruent_combination : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) C), (∀ m, QL c.μ ⊤ (e m)) → ∀ (L : ι → G.dual.Lie), (∀ m, c.IsLie (e m) (L m)) → ∀ (g : MvPowerSeries (Fin d) C), QL c.μ ⊤ g → ∀ (a : ι → O), In (⊤ : Ideal O) (g - comb a e) → c.IsLie g (∑ m, a m • L m) := by
  first | exact @GlobalTheory.TangentComb.main | exact GlobalTheory.TangentComb.main | (intros; apply GlobalTheory.TangentComb.main <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f l → ∀ t : G.Tate, c.HasPeriod (RingHom.id O) t f (l (hodgeTate G t)) := by
  first | exact @GlobalTheory.QLogPeriod.hasPeriod_hodgeTate | exact GlobalTheory.QLogPeriod.hasPeriod_hodgeTate | (intros; apply GlobalTheory.QLogPeriod.hasPeriod_hodgeTate <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

theorem mem_forms {f : F.G → W} : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W ↔
    ∀ (γ : F.Γ) (g : F.G) (κ : F.K), f ((γ : F.G) * g * κ) = jK κ⁻¹ • f g := Iff.rfl


variable {F lam jK} in
theorem jK_eq (hJ : F.IsJ lam jK) {κ κ' : F.K} (h1 : F.kap κ' = F.kap κ) (h2 : F.chi κ' = F.chi κ) : jK κ' = jK κ := by
  rw [hJ κ', hJ κ, h1, h2]

variable {F lam jK} in
theorem jK_inv_congr {κ κ' : F.K} (h : jK κ' = jK κ) : jK κ'⁻¹ = jK κ⁻¹ := by
  have e1 : jK κ'⁻¹ * jK κ' = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e2 : jK κ * jK κ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc jK κ'⁻¹ = jK κ'⁻¹ * (jK κ * jK κ⁻¹) := by rw [e2, mul_one]
    _ = (jK κ'⁻¹ * jK κ') * jK κ⁻¹ := by rw [h, mul_assoc]
    _ = jK κ⁻¹ := by rw [e1, one_mul]

theorem grpA_one : grpA F.O N lam 1 = 1 := Subtype.ext (by simp [grpA, grp])


variable {F lam jK} in
theorem jK_inv_of_triv (hJ : F.IsJ lam jK) {κ : F.K} (h1 : F.kap κ = 1) (h2 : F.chi κ = 1) : jK κ⁻¹ = 1 := by
  have : jK κ = jK 1 := by rw [hJ κ, h1, h2, map_one, grpA_one]; simp
  rw [jK_inv_congr this, inv_one, map_one]

def heckeFn (i : F.I) (f : F.G → W) : F.G → W := fun g => F.cst i • ∑ s ∈ F.tr i, f (g * s)

variable {F lam jK W}

theorem heckeFn_mem (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) : heckeFn F W i f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W := by
  rw [mem_forms] at hf ⊢
  intro γ g κ
  obtain ⟨σ, hσ⟩ := hOk.perm i κ
  have key : ∀ s : F.tr i, f ((γ : F.G) * g * κ * s) = jK κ⁻¹ • f (g * (σ s : F.G)) := by
    intro s
    obtain ⟨κ', h1, h2, h3⟩ := hσ s
    have e : (γ : F.G) * g * κ * s = γ * (g * σ s) * κ' := by
      rw [mul_assoc ((γ : F.G) * g) (κ : F.G) (s : F.G), h1]; simp only [mul_assoc]
    rw [e, hf γ (g * σ s) κ', jK_inv_congr (jK_eq hJ h2 h3)]
  simp only [heckeFn]
  rw [← Finset.sum_coe_sort (F.tr i), ← Finset.sum_coe_sort (F.tr i)]
  simp_rw [key]
  rw [← Finset.smul_sum, Equiv.sum_comp σ (fun s : F.tr i => f (g * (s : F.G))), smul_comm]

theorem heckeFn_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) :
    heckeFn F W i (heckeFn F W j f) = heckeFn F W j (heckeFn F W i f) := by
  rw [mem_forms] at hf
  funext g
  obtain ⟨σ, hσ⟩ := hOk.comm i j
  have key : ∀ x : F.tr i × F.tr j, f (g * x.1 * x.2) = f (g * (σ x).1 * (σ x).2) := by
    intro x
    obtain ⟨hK, h1, h2⟩ := hσ x
    have e : g * x.1 * x.2 = ((1 : F.Γ) : F.G) * (g * (σ x).1 * (σ x).2) * (⟨_, hK⟩ : F.K) := by
      simp only [OneMemClass.coe_one, one_mul, mul_assoc, mul_inv_cancel_left]
    rw [e, hf, jK_inv_of_triv hJ h1 h2, one_smul]
  have hsum : ∀ (a b : F.I), heckeFn F W a (heckeFn F W b f) g =
      F.cst a • F.cst b • ∑ x : F.tr a × F.tr b, f (g * x.1 * x.2) := by
    intro a b
    simp only [heckeFn, Fintype.sum_prod_type, Finset.smul_sum]
    rw [← Finset.sum_coe_sort (F.tr a)]
    refine Fintype.sum_congr _ _ fun s => ?_
    rw [← Finset.sum_coe_sort (F.tr b)]
  rw [hsum, hsum, smul_comm (F.cst i) (F.cst j)]
  congr 2
  rw [Fintype.sum_congr _ _ key, Equiv.sum_comp σ (fun y : F.tr j × F.tr i => f (g * y.1 * y.2))]

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

def op (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) :
    Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) where
  toFun f := ⟨heckeFn F W i f, heckeFn_mem hOk hJ i f.2⟩
  map_add' f f' := by
    ext g
    simp [heckeFn, Finset.sum_add_distrib, smul_add]
  map_smul' c f := by
    ext g
    simp [heckeFn, Finset.smul_sum, smul_comm (F.cst i) c]

theorem op_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) :
    (op (W := W) hOk hJ i) * op hOk hJ j = op hOk hJ j * op hOk hJ i := by
  ext f : 1
  exact Subtype.ext (heckeFn_comm hOk hJ i j f.2)

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

open scoped IsMulCommutative in
def heckeAlg (hOk : F.Ok) (hJ : F.IsJ lam jK) : F.T →ₐ[F.O] Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) :=
  letI : IsMulCommutative (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))) :=
    Algebra.isMulCommutative_adjoin F.O (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact op_comm hOk hJ i j)
  (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))).val.comp
    (MvPolynomial.aeval fun i => ⟨op hOk hJ i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

theorem heckeAlg_X (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) : heckeAlg (W := W) hOk hJ (X i) = op hOk hJ i := by
  simp [heckeAlg]

theorem hecke_module : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam), F.Ok → F.IsJ lam jK → ∀ (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W], ∃ (_ : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)) (_ : IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)), F.IsHecke lam jK W := by
  intro l _ ι _ _ N F lam jK hOk hJ W _ _ _ _
  letI inst : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W) := Module.compHom _ (heckeAlg (W := W) hOk hJ).toRingHom
  refine ⟨inst, ⟨fun c t f => ?_⟩, fun c f => ?_, fun i f g => ?_⟩
  · change heckeAlg hOk hJ (c • t) f = c • heckeAlg hOk hJ t f
    rw [map_smul, LinearMap.smul_apply]
  · change heckeAlg hOk hJ (C c) f = c • f
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
  · change ((heckeAlg hOk hJ (X i) f : Forms F.O (A := alg F.O N lam) F.Γ jK W) : F.G → W) g = _
    rw [heckeAlg_X]
    rfl

end GlobalTheory.ExpFrame.HeckeMod
end
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SemilinTransport

open MvPolynomial

theorem map_mem {R : Type} [CommRing R] (σ : R →+* R) {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    map σ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro l j hlj
    have e := h2 l j hlj
    simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at e ⊢
    have hc : ∀ g : MvPolynomial (Fin r × Fin n) R,
        map σ (Formalism.GradedWeylDivisibility.colAddGen R l j g) = Formalism.GradedWeylDivisibility.colAddGen R l j (map σ g) := by
      intro g
      unfold Formalism.GradedWeylDivisibility.colAddGen
      rw [aeval_eq_bind₁, map_bind₁]
      congr 2
      funext v
      split_ifs <;> simp
    rw [← hc, e, map_rename]

def onFactor {R : Type} [CommRing R] (σ : R →+* R) (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl R r n ν →+ Formalism.GradedWeylDivisibility.dualWeyl R r n ν where
  toFun f := ⟨map σ (f : MvPolynomial (Fin r × Fin n) R), map_mem σ f.2⟩
  map_zero' := by ext1; simp
  map_add' f f' := by ext1; simp

theorem onFactor_smul {R : Type} [CommRing R] (σ : R →+* R) (r n : ℕ) (ν : Fin n → ℕ) (c : R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : onFactor σ r n ν (c • f) = σ c • onFactor σ r n ν f := by
  ext1
  simp [onFactor, smul_eq_C_mul]

def Tw {R : Type} [CommRing R] (_σ : R →+* R) (M : Type) : Type := M

instance {R : Type} [CommRing R] (σ : R →+* R) (M : Type) [AddCommGroup M] : AddCommGroup (Tw σ M) :=
  inferInstanceAs (AddCommGroup M)

instance {R : Type} [CommRing R] (σ : R →+* R) (M : Type) [AddCommGroup M] [Module R M] :
    Module R (Tw σ M) :=
  Module.compHom M σ

variable {R : Type} [CommRing R] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

def mlin (σ : R →+* R) :
    MultilinearMap (RingHom.id R) (fun τ : ι => Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ)))
      (Tw σ (NablaT R N mu)) where
  toFun x := (PiTensorProduct.tprod R (fun τ => onFactor σ N N _ (x τ)) : NablaT R N mu)
  map_update_add' := by
    intro _ x i a b
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, map_add (f := _)]
    exact (PiTensorProduct.tprod R).map_update_add _ i _ _
  map_update_smul' := by
    intro _ x i c a
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, onFactor_smul]
    exact (PiTensorProduct.tprod R).map_update_smul _ i _ _

def semi (σ : R →+* R) : NablaT R N mu →+ NablaT R N mu :=
  (PiTensorProduct.lift (mlin N mu σ)).toAddMonoidHom

theorem semi_tprod (σ : R →+* R) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    semi N mu σ (PiTensorProduct.tprod R x) = PiTensorProduct.tprod R (fun τ => onFactor σ N N _ (x τ)) :=
  by
    show (PiTensorProduct.lift (mlin N mu σ)) (PiTensorProduct.tprod R x) = _
    rw [PiTensorProduct.lift.tprod]; rfl

theorem semi_smul (σ : R →+* R) (c : R) (y : NablaT R N mu) :
    semi N mu σ (c • y) = σ c • semi N mu σ y :=
  (PiTensorProduct.lift (mlin N mu σ)).map_smul c y

end GlobalTheory.SemilinTransport

namespace GlobalTheory.SemilinTransport

open MvPolynomial

variable {R : Type} [CommRing R] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

theorem semi_left_inv (g : R ≃+* R) (y : NablaT R N mu) :
    semi N mu (g.symm : R →+* R) (semi N mu (g : R →+* R) y) = y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [semi_smul, semi_smul, semi_tprod, semi_tprod]
    congr 1
    · simp
    · congr 1
      funext τ
      ext1
      simp [onFactor, map_map, MvPolynomial.map_id]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem fix_inv (g : R ≃+* R) (u : GL (Fin N) R)
    (hu : ∀ a b, g ((u : Matrix (Fin N) (Fin N) R) a b) = (u : Matrix (Fin N) (Fin N) R) a b) (a b : Fin N) :
    g (((u⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) a b) = ((u⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) a b := by
  have hU : Units.map ((g : R →+* R).mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R).toMonoidHom u = u :=
    Units.ext (by ext i j; simp [hu])
  have h2 : Units.map ((g : R →+* R).mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R).toMonoidHom u⁻¹ = u⁻¹ := by
    rw [map_inv, hU]
  have := congrArg (fun w : GL (Fin N) R => (w : Matrix (Fin N) (Fin N) R) a b) h2
  simpa using this

theorem onFactor_rep (g : R ≃+* R) (u : GL (Fin N) R)
    (hu : ∀ a b, g ((u : Matrix (Fin N) (Fin N) R) a b) = (u : Matrix (Fin N) (Fin N) R) a b) (ν : Fin N → ℕ)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R N N ν) :
    onFactor (g : R →+* R) N N ν (Formalism.UG.dualWeylRep R N N ν u f) =
      Formalism.UG.dualWeylRep R N N ν u (onFactor (g : R →+* R) N N ν f) := by
  ext1
  simp only [onFactor, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Formalism.UG.dualWeylRep_apply]
  unfold Formalism.UG.dwAct Formalism.GradedWeylDivisibility.rowAct
  rw [aeval_eq_bind₁, map_bind₁]
  congr 2
  simp only [map_sum, map_mul, map_C, map_X, RingHom.coe_coe, fix_inv N g u hu]

theorem grp_tprod [DecidableEq ι] (h : ι → GL (Fin N) R)
    (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    grp R N mu h (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun τ => Formalism.UG.dualWeylRep R N N _ (h τ) (x τ)) := by
  simp [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, PiTensorProduct.mapMonoidHom, PiTensorProduct.map_tprod]

theorem semi_grp [DecidableEq ι] (g : R ≃+* R) (h : ι → GL (Fin N) R)
    (hh : ∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b)
    (y : NablaT R N mu) :
    semi N mu (g : R →+* R) (grp R N mu h y) = grp R N mu h (semi N mu (g : R →+* R) y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, semi_smul, semi_smul, map_smul, grp_tprod, semi_tprod, semi_tprod, grp_tprod]
    congr 2
    funext τ
    exact onFactor_rep N g (h τ) (hh τ) _ (x τ)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

end GlobalTheory.SemilinTransport

namespace GlobalTheory

open GlobalTheory.SemilinTransport

theorem semilinear_transport : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (mu : ι → ℕ → ℕ)
    (g : R ≃+* R), ∃ Φ : NablaT R N mu →+ NablaT R N mu, Function.Injective Φ ∧ (∀ (c : R) x, Φ (c • x) = g c • Φ x) ∧
    ∀ (h : ι → GL (Fin N) R), (∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b) →
      ∀ x, Φ (grp R N mu h x) = grp R N mu h (Φ x) := by
  intro R _ ι _ _ N mu g
  refine ⟨semi N mu (g : R →+* R), fun y y' e => ?_, fun c x => semi_smul N mu _ c x,
    fun h hh x => semi_grp N mu g h hh x⟩
  rw [← semi_left_inv N mu g y, ← semi_left_inv N mu g y', e]

end GlobalTheory
end
end

section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

namespace GlobalTheory.ExpFrame.Frame

theorem isUnit_natCast_of_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok →
    ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  intro l _ ι _ N F hF n hn
  obtain ⟨hinj, L, _, hrange⟩ := hF.ring
  have hnorm : ‖(n : PadicAlgCl l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) n, PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hn
  have hne : (n : PadicAlgCl l) ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hmem : (n : PadicAlgCl l)⁻¹ ∈ Set.range F.emb := by
    rw [hrange]
    refine ⟨?_, ?_⟩
    · exact L.inv_mem (L.natCast_mem n)
    · rw [norm_inv, hnorm, inv_one]
  obtain ⟨y, hy⟩ := hmem
  have h1 : (n : F.O) * y = 1 := by
    apply hinj
    rw [map_mul, map_natCast, hy, map_one, mul_inv_cancel₀ hne]
  exact IsUnit.of_mul_eq_one y h1

end GlobalTheory.ExpFrame.Frame
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame

abbrev Letter (O : Type) [CommRing O] (N : ℕ) (ι : Type) : Type :=
  (ι → GL (Fin N) O) ⊕ (ι × (Fin N → ℕ))

def evalE (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] Module.End O (NablaT O N lam) :=
  FreeAlgebra.lift O (Sum.elim (grp O N lam) fun p => P p.1 p.2)

def evalPol (O : Type) [CommRing O] (N : ℕ) :
    FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O (MvPolynomial (Fin N × Fin N) O) :=
  FreeAlgebra.lift O fun p => Formalism.GradedWeylDivisibility.rowDivL O p.1 p.2 1

end GlobalTheory.CapelliLink

end
end

section

open IsLocalRing GlobalTheory.Toroidal

theorem _root_.GlobalTheory.T.exists_monic_simple_root_generating_residue : ∀ (O R' Ω : Type) [CommRing O] [IsLocalRing O] [CommRing R'] [IsLocalRing R'] [Field Ω] (φ' : O →+* R') (u' : R' →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → RingHom.ker u' = maximalIdeal R' → ∃ (G : Polynomial O) (β : Ω), G.Monic ∧ (G.map (u'.comp φ')).eval β = 0 ∧ (G.map (u'.comp φ')).derivative.eval β ≠ 0 ∧ ∀ r : R', ∃ q : Polynomial O, u' r = (q.map (u'.comp φ')).eval β := by
  first | exact @GlobalTheory.exists_monic_simple_root_generator_residue | exact GlobalTheory.exists_monic_simple_root_generator_residue | (intros; apply GlobalTheory.exists_monic_simple_root_generator_residue <;> assumption)
end
