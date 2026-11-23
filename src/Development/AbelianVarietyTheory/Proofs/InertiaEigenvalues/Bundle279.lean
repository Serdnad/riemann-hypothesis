module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle253
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle252
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Mathlib.RingTheory.PowerSeries.Inverse
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

theorem tameGen_image_mem_zpowers {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (γ γ' : G E Ω) (h : TameGenAt A γ) (h' : TameGenAt A γ')
    {M : Type} [Group M] (φ : G E Ω →* M) (hk : IsOpen (φ.ker : Set (G E Ω)))
    (hw : ∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → φ s = 1) :
    φ γ' ∈ Subgroup.zpowers (φ γ) := by
  have hle : φ.ker ≤ (Subgroup.zpowers (φ γ)).comap φ := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact Subgroup.one_mem _
  have hop : IsOpen (((Subgroup.zpowers (φ γ)).comap φ : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isOpen_mono hle hk
  have hcl := Subgroup.isClosed_of_isOpen _ hop
  have hsub : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1})
      ≤ (Subgroup.zpowers (φ γ)).comap φ := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact Subgroup.mem_zpowers _
    · exact hle (hw x hx)
  exact closure_minimal hsub hcl (h.2 h'.1)

theorem tameGen_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ γ' : G E Ω), TameGenAt A γ → TameGenAt A γ' → ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → φ s = 1) → ∃ n : ℕ, n.Coprime (orderOf (φ γ)) ∧ 0 < orderOf (φ γ) ∧ φ γ' = φ γ ^ n := by
  intro E Ω _ _ _ _ _ A γ γ' h h' M _ φ hk hw
  have h1 := tameGen_image_mem_zpowers A γ γ' h h' φ hk hw
  have h2 := tameGen_image_mem_zpowers A γ' γ h' h φ hk hw
  haveI : IsGalois E Ω := IsGalois.mk
  haveI : Finite (G E Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ hk
  have hfin : IsOfFinOrder (φ γ) := by
    have h0 : IsOfFinOrder (QuotientGroup.mk γ : G E Ω ⧸ φ.ker) := isOfFinOrder_of_finite _
    have := (QuotientGroup.kerLift φ).isOfFinOrder h0
    simpa using this
  have hpos : 0 < orderOf (φ γ) := hfin.orderOf_pos
  obtain ⟨n, hn⟩ := (hfin.mem_powers_iff_mem_zpowers).2 h1
  have hn : φ γ ^ n = φ γ' := hn
  have heq : orderOf (φ γ') = orderOf (φ γ) :=
    Nat.dvd_antisymm (orderOf_dvd_of_mem_zpowers h1) (orderOf_dvd_of_mem_zpowers h2)
  refine ⟨n, ?_, hpos, hn.symm⟩
  rw [← hn, hfin.orderOf_pow] at heq
  have hg : (orderOf (φ γ)).gcd n = 1 := by
    rcases Nat.div_eq_self.1 heq with h | h
    · omega
    · exact h
  exact Nat.Coprime.symm hg

end GlobalTheory.TypeLeaf
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.small_traces_dvd_span_image : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → IsSSRep r → ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = ((l : PadicAlgCl l) ^ n) • (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  first | exact @GlobalTheory.smallTrace_dvd_span | exact GlobalTheory.smallTrace_dvd_span | (intros; apply GlobalTheory.smallTrace_dvd_span <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per

namespace GlobalTheory.Per.Val

variable {l : ℕ} [Fact l.Prime]


open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.exists_norm_eq (x : _root_.Formalism.BasicNotions.Loc.Om l) (hx : x ≠ 0) :
    ∃ q : ℚ, ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hi hx
  have hn : (minpoly ℚ_[l] x).natDegree ≠ 0 := (minpoly.natDegree_pos hi).ne'
  refine ⟨((minpoly ℚ_[l] x).coeff 0).valuation / (minpoly ℚ_[l] x).natDegree, ?_⟩
  have h1 : ‖x‖ = ‖(minpoly ℚ_[l] x).coeff 0‖ ^ (1 / ((minpoly ℚ_[l] x).natDegree : ℝ)) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l) x
  rw [h1, Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg l)]
  congr 1
  have hn' : ((minpoly ℚ_[l] x).natDegree : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.mem_OL_iff (LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  haveI := LL.2
  unfold _root_.Formalism.BasicNotions.Loc.OL
  rw [mem_integralClosure_iff]
  have hK : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hnorm : ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = spectralValue (minpoly ℚ_[l] x) := by
    rw [IntermediateField.minpoly_eq x]; rfl
  rw [hnorm, spectralValue_le_one_iff (minpoly.monic hK)]
  constructor
  · intro hi n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, coeff_map]
    simpa using PadicInt.norm_le_one ((minpoly ℤ_[l] x).coeff n)
  · intro h
    have hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hK)
    refine ⟨q, hm, ?_⟩
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, ← eval₂_map, hq]
    exact minpoly.aeval ℚ_[l] x


open Classical in
def vf (x : Om l) : WithTop ℚ := if h : x = 0 then ⊤ else ((exists_norm_eq x h).choose : ℚ)

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem exists_rat_vf_eq_norm_eq_rpow_of_ne_zero {x : _root_.Formalism.BasicNotions.Loc.Om l} (hx : x ≠ 0) :
    ∃ q : ℚ, _root_.GlobalTheory.Per.Val.vf x = q ∧ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) :=
  ⟨_, by simp [_root_.GlobalTheory.Per.Val.vf, hx],
    (_root_.GlobalTheory.Per.Val.exists_norm_eq x hx).choose_spec⟩

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem prime_rpow_neg_le_iff (a b : ℚ) :
    (l : ℝ) ^ (-(a : ℝ)) ≤ (l : ℝ) ^ (-(b : ℝ)) ↔ b ≤ a := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  rw [Real.rpow_le_rpow_left_iff hl, neg_le_neg_iff]
  exact_mod_cast Iff.rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem prime_rpow_neg_inj (a b : ℚ) :
    (l : ℝ) ^ (-(a : ℝ)) = (l : ℝ) ^ (-(b : ℝ)) ↔ a = b := by
  constructor
  · intro h
    exact le_antisymm ((prime_rpow_neg_le_iff b a).1 h.ge) ((prime_rpow_neg_le_iff a b).1 h.le)
  · rintro rfl; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_eq_iff (x : _root_.Formalism.BasicNotions.Loc.Om l) (q : ℚ) :
    _root_.GlobalTheory.Per.Val.vf x = (q : WithTop ℚ) ↔ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  by_cases hx : x = 0
  · subst hx
    simp only [_root_.GlobalTheory.Per.Val.vf, dif_pos, norm_zero, WithTop.top_ne_coe, false_iff]
    exact (Real.rpow_pos_of_pos hl _).ne
  · obtain ⟨a, ha, hn⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
    rw [ha, hn, WithTop.coe_eq_coe, prime_rpow_neg_inj]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_zero : _root_.GlobalTheory.Per.Val.vf (0 : _root_.Formalism.BasicNotions.Loc.Om l) = ⊤ := by
  simp [_root_.GlobalTheory.Per.Val.vf]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.le_vf_iff (x : _root_.Formalism.BasicNotions.Loc.Om l) (q : ℚ) :
    (q : WithTop ℚ) ≤ _root_.GlobalTheory.Per.Val.vf x ↔ ‖x‖ ≤ (l : ℝ) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  by_cases hx : x = 0
  · subst hx
    simp only [_root_.GlobalTheory.Per.Val.vf_zero, le_top, norm_zero, true_iff]
    exact (Real.rpow_pos_of_pos hl _).le
  · obtain ⟨a, ha, hn⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
    rw [ha, hn, WithTop.coe_le_coe, prime_rpow_neg_le_iff]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_mul (x y : _root_.Formalism.BasicNotions.Loc.Om l) :
    _root_.GlobalTheory.Per.Val.vf (x * y) =
      _root_.GlobalTheory.Per.Val.vf x + _root_.GlobalTheory.Per.Val.vf y := by
  by_cases hx : x = 0
  · simp [hx, _root_.GlobalTheory.Per.Val.vf_zero]
  by_cases hy : y = 0
  · simp [hy, _root_.GlobalTheory.Per.Val.vf_zero]
  obtain ⟨a, ha, hna⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
  obtain ⟨b, hb, hnb⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hy
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [ha, hb, ← WithTop.coe_add, _root_.GlobalTheory.Per.Val.vf_eq_iff, norm_mul, hna, hnb,
    ← Real.rpow_add hl]
  push_cast
  ring_nf

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_add (x y : _root_.Formalism.BasicNotions.Loc.Om l) :
    min (_root_.GlobalTheory.Per.Val.vf x) (_root_.GlobalTheory.Per.Val.vf y) ≤
      _root_.GlobalTheory.Per.Val.vf (x + y) := by
  by_cases hxy : x + y = 0
  · simp [hxy, _root_.GlobalTheory.Per.Val.vf_zero]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha, hna⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
  obtain ⟨b, hb, hnb⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hy
  obtain ⟨c, hc, hnc⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hxy
  rw [ha, hb, hc, ← WithTop.coe_min, WithTop.coe_le_coe]
  have hmax : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
  rw [hna, hnb, hnc] at hmax
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    rw [max_eq_left ((prime_rpow_neg_le_iff b a).2 h), prime_rpow_neg_le_iff] at hmax
    exact hmax
  · rw [min_eq_right h]
    rw [max_eq_right ((prime_rpow_neg_le_iff a b).2 h), prime_rpow_neg_le_iff] at hmax
    exact hmax

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_one : _root_.GlobalTheory.Per.Val.vf (1 : _root_.Formalism.BasicNotions.Loc.Om l) = 0 := by
  have := (_root_.GlobalTheory.Per.Val.vf_eq_iff (1 : _root_.Formalism.BasicNotions.Loc.Om l) 0).2 (by simp)
  exact_mod_cast this

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_l : _root_.GlobalTheory.Per.Val.vf ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l) = 1 := by
  have h : ‖((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-((1 : ℚ) : ℝ)) := by
    have : ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l) = algebraMap ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l) (l : ℚ_[l]) := by simp
    rw [this, PadicAlgCl.norm_extends, Padic.norm_p]
    simp [Real.rpow_neg_one]
  exact_mod_cast (_root_.GlobalTheory.Per.Val.vf_eq_iff _ 1).2 h

def vOm (l : ℕ) [Fact l.Prime] : AddValuation (Om l) (WithTop ℚ) :=
  AddValuation.of vf vf_zero vf_one vf_add vf_mul

end GlobalTheory.Per.Val

namespace GlobalTheory.Per

end GlobalTheory.Per
end
end

section

namespace GlobalTheory.HWL.SeriesEval

open PowerSeries IsLocalRing Filter Topology

section Shift

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem X_add_C_mem {c : O} (hc : c ∈ maximalIdeal O) : (X + C c : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simpa using hc

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem exists_shift {c : O} (hc : c ∈ maximalIdeal O) :
    ∃ s : O⟦X⟧ →ₐ[O] O⟦X⟧, s X = X + C c := by
  have : IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := ReciprocityTheory.P1.isAdicComplete_ps
  exact ⟨GlobalTheory.mvEvalAdic (σ := Unit) O (maximalIdeal O⟦X⟧) (fun _ => X + C c)
    (fun _ => X_add_C_mem hc), GlobalTheory.mvEvalAdic_X (σ := Unit) _ _ _ ()⟩

theorem exists_div {c : O} (hc : c ∈ maximalIdeal O) (b : O⟦X⟧) :
    ∃ (r : O) (q : O⟦X⟧), b = C r + (X - C c) * q := by
  have : IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := ReciprocityTheory.P1.isAdicComplete_ps
  obtain ⟨s, hs⟩ := exists_shift hc
  obtain ⟨s', hs'⟩ := exists_shift (neg_mem hc)
  have hC : ∀ r, s' (C r) = C r := fun r => s'.commutes r
  have hX : (s'.comp s) X = X := by
    rw [AlgHom.comp_apply, hs, map_add (f := _), hs', hC, map_neg]; ring
  have h : s'.comp s = AlgHom.id O O⟦X⟧ :=
    GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff (σ := Unit) (maximalIdeal O⟦X⟧)
      (fun _ => by
        change (s'.comp s) X ∈ _
        rw [hX]; simpa using X_add_C_mem (zero_mem (maximalIdeal O)))
      (fun _ => hX)
  refine ⟨constantCoeff (s b), s' (mk fun p => coeff (p + 1) (s b)), ?_⟩
  have h1 : s' (s b) = b := DFunLike.congr_fun h b
  conv_lhs => rw [← h1, eq_X_mul_shift_add_const (s b)]
  rw [map_add (f := _), map_mul, hs', hC, map_neg]
  ring

variable {L : Type*} [CommRing L] [Algebra O L]

theorem exists_ev {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) : ∃ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x := by
  obtain ⟨s, hs⟩ := exists_shift hc
  have hy : HasSubst (x - C (algebraMap O L c)) :=
    HasSubst.of_constantCoeff_zero' (by simp [hx])
  refine ⟨(substAlgHom hy).comp s, ?_⟩
  have hC : (substAlgHom hy : O⟦X⟧ →ₐ[O] L⟦X⟧) (C c) = C (algebraMap O L c) :=
    ((substAlgHom hy : O⟦X⟧ →ₐ[O] L⟦X⟧).commutes c).trans (PowerSeries.algebraMap_apply (r := c))
  rw [AlgHom.comp_apply, hs, map_add (f := _), substAlgHom_X, hC]
  ring

theorem ev_div {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) :
    ∃ z : L⟦X⟧, ∀ b : O⟦X⟧, ∃ (r : O) (q : O⟦X⟧), ∀ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x →
      ev b = C (algebraMap O L r) + X * (z * ev q) := by
  refine ⟨mk fun p => coeff (p + 1) x, fun b => ?_⟩
  obtain ⟨r, q, rfl⟩ := exists_div hc b
  refine ⟨r, q, fun ev hev => ?_⟩
  have hC : ∀ r, ev (C r) = C (algebraMap O L r) := fun r =>
    (ev.commutes r).trans PowerSeries.algebraMap_apply
  rw [map_add (f := _), map_mul, map_sub, hC, hC, hev, ← hx, ← mul_assoc]
  congr 2
  rw [sub_eq_iff_eq_add]
  exact eq_X_mul_shift_add_const x

theorem ev_unique {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) (ev ev' : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (h' : ev' X = x) : ev = ev' := by
  obtain ⟨z, hz⟩ := ev_div hc x hx
  have key : ∀ (k : ℕ) (b : O⟦X⟧), X ^ k ∣ ev b - ev' b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro b
      obtain ⟨r, q, hq⟩ := hz b
      have : ev b - ev' b = X * (z * (ev q - ev' q)) := by rw [hq ev h, hq ev' h']; ring
      rw [this, pow_succ']
      exact mul_dvd_mul_left _ ((ih q).mul_left z)
  refine AlgHom.ext fun b => PowerSeries.ext fun k => ?_
  have := X_pow_dvd_iff.1 (key (k + 1) b) k k.lt_succ_self
  rwa [map_sub, sub_eq_zero] at this

variable {K : Type*} [NormedField K] (i : L →+* K)

theorem ev_bounded (hi : ∀ r : O, ‖i (algebraMap O L r)‖ ≤ 1) {c : O} (hc : c ∈ maximalIdeal O)
    (x : L⟦X⟧) (hx : constantCoeff x = algebraMap O L c) (ev : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (k : ℕ) : ∃ B : ℝ, ∀ b, ‖i (coeff k (ev b))‖ ≤ B := by
  obtain ⟨z, hz⟩ := ev_div hc x hx
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · refine ⟨1, fun b => ?_⟩
      obtain ⟨r, q, hq⟩ := hz b
      simpa [hq ev h] using hi r
    · choose! B hB using ih
      refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ‖i (coeff p.1 z)‖ * B p.2, fun b => ?_⟩
      obtain ⟨r, q, hq⟩ := hz b

      rw [hq ev h, map_add (f := _), coeff_succ_X_mul, coeff_C, if_neg k.succ_ne_zero, zero_add, coeff_mul,
      map_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
      rw [map_mul, norm_mul]
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact mul_le_mul_of_nonneg_left (hB _ (by omega) _) (norm_nonneg _)

theorem ev_tendsto (hi : ∀ r : O, ‖i (algebraMap O L r)‖ ≤ 1) {c : O} (hc : c ∈ maximalIdeal O)
    (hc1 : ‖i (algebraMap O L c)‖ < 1)
    (x : L⟦X⟧) (hx : constantCoeff x = algebraMap O L c) (ev : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (a : O⟦X⟧) (k : ℕ) :
    Tendsto (fun m : ℕ => i (coeff k (ev ((trunc m a : Polynomial O) : O⟦X⟧)))) atTop
      (𝓝 (i (coeff k (ev a)))) := by
  obtain ⟨B, hB⟩ := ev_bounded i hi hc x hx ev h k
  have hC : ev (C c) = C (algebraMap O L c) := (ev.commutes c).trans PowerSeries.algebraMap_apply
  rw [← tendsto_add_atTop_iff_nat k, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (g := fun n => ‖i (algebraMap O L c)‖ ^ n * B)
    (fun n => ?_) (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hc1).mul_const B)
  obtain ⟨b, hb⟩ : X ^ (n + k) ∣ ((trunc (n + k) a : Polynomial O) : O⟦X⟧) - a :=
    X_pow_dvd_iff.2 fun m hm => by simp [coeff_trunc, hm]
  have hmem : (C c + (X - C c) : O⟦X⟧) ^ (n + (k + 1) - 1) ∈
      Ideal.span {C c ^ n, (X - C c) ^ (k + 1)} :=
    Ideal.add_pow_add_pred_mem_of_pow_mem_of_commute _
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) (Commute.all _ _)
  rw [add_sub_cancel, show n + (k + 1) - 1 = n + k by omega, Ideal.mem_span_pair] at hmem
  obtain ⟨u, v, huv⟩ := hmem
  have hy : X ∣ x - C (algebraMap O L c) := X_dvd_iff.2 (by simp [hx])
  have h0 : coeff k ((x - C (algebraMap O L c)) ^ (k + 1) * ev (v * b)) = 0 :=
    X_pow_dvd_iff.1 ((pow_dvd_pow_of_dvd hy _).mul_right _) k k.lt_succ_self
  have he : ev (X ^ (n + k) * b) = C (algebraMap O L c ^ n) * ev (u * b) +
      (x - C (algebraMap O L c)) ^ (k + 1) * ev (v * b) := by
    rw [← huv]
    simp only [map_mul, map_add (f := _), map_pow, map_sub, hC, h]
    ring
  rw [← map_sub, ← map_sub, ← map_sub, hb, he, map_add (f := _), h0, add_zero, coeff_C_mul, map_mul,
    norm_mul, map_pow, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

end Shift

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem existsUnique_ev : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (x : PowerSeries ↥LL.1),
    ‖((PowerSeries.constantCoeff x : ↥LL.1) : Om l)‖ < 1 →
    (∃! ev : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1, ev PowerSeries.X = x) ∧
    ∀ ev : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1, ev PowerSeries.X = x →
      ∀ (a : PowerSeries ↥(OL LL)) (k : ℕ), Filter.Tendsto (fun m : ℕ =>
        ((PowerSeries.coeff k (ev ((PowerSeries.trunc m a : Polynomial ↥(OL LL)) :
          PowerSeries ↥(OL LL))) : ↥LL.1) : Om l)) Filter.atTop
        (nhds ((PowerSeries.coeff k (ev a) : ↥LL.1) : Om l)) := by
  intro l _ LL x hx
  obtain ⟨hDVR, hcomp, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  letI : IsDiscreteValuationRing ↥(OL LL) := hDVR
  letI : IsLocalRing ↥(OL LL) := hDVR.toIsLocalRing
  letI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := hcomp
  have hfin := LL.2
  have hn : ∀ y : ↥LL.1, ‖GlobalTheory.DiscEval.fieldEmb LL.1 y‖ = ‖(y : Om l)‖ := fun y => by
    rw [GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hi : ∀ r : ↥(OL LL), ‖algebraMap ↥LL.1 (Om l) (algebraMap ↥(OL LL) ↥LL.1 r)‖ ≤ 1 :=
    fun r => (hn r).ge.trans ((GlobalTheory.DiscEval.mem_integralClosure_iff_norm LL.1 r).1 r.2)
  let c : ↥(OL LL) := ⟨constantCoeff x,
    (GlobalTheory.DiscEval.mem_integralClosure_iff_norm LL.1 _).2 ((hn _).trans_le hx.le)⟩
  have hxc : constantCoeff x = algebraMap ↥(OL LL) ↥LL.1 c := rfl
  have hc : c ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    apply (IsLocalRing.mem_maximalIdeal _).2
    intro hu
    exact ((hn _).trans_lt hx).ne ((GlobalTheory.DiscEval.isUnit_iff_norm LL.1 c).1 hu)
  have hinst : ((OL LL).toAlgebra : Algebra ↥(OL LL) (↥LL.1)⟦X⟧) = MvPowerSeries.instAlgebra :=
    Algebra.algebra_ext _ _ fun r =>
      (PowerSeries.algebraMap_apply (R := ↥(OL LL)) (A := ↥LL.1) (r := r)).symm
  generalize ((OL LL).toAlgebra : Algebra ↥(OL LL) (↥LL.1)⟦X⟧) = inst at hinst ⊢
  subst hinst
  refine ⟨?_, fun ev hev a k =>
    ev_tendsto (algebraMap ↥LL.1 (Om l)) hi hc hx x hxc ev hev a k⟩
  obtain ⟨ev, hev⟩ := exists_ev hc x hxc
  exact ⟨ev, hev, fun ev' hev' => ev_unique hc x hxc ev' ev hev' hev⟩

end GlobalTheory.HWL.SeriesEval
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.ainf_invPi_mod_xi_pow_bounded_denominator : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (k n M : ℕ), 1 ≤ M → k ≤ (l - 1) * n → ((l : ℕ) : Ainf l) ^ (n + M - 1) ∈ Ideal.span {AI.π₁ ^ k, AI.ξ ^ M} := by
  first | exact @GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator | exact GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator | (intros; apply GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator <;> assumption)
end
