module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite

@[expose] public section

section

noncomputable section

open MeasureTheory Formalism.UG

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def cornerU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (u : GU σ n) : L :=
  ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev

def depthU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (u : GU σ n) : ℕ :=
  (-ordL (cornerU k u)).toNat

def shellU {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (j : ℤ) : Set (cellU y) :=
  {u | Valued.v (cornerU k (u : GU σ n)) ≤ WithZero.exp j}

theorem mem_shellU_iff_depth {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (j : ℕ) (u : cellU y) :
    u ∈ shellU k y j ↔ depthU k (u : GU σ n) ≤ j := by
  unfold shellU depthU
  simp only [Set.mem_setOf_eq]
  by_cases h0 : cornerU k (u : GU σ n) = 0
  · rw [h0]; simp [ordL]
  · rw [GlobalTheory.BorelUMod.v_eq_exp h0, WithZero.exp_le_exp]
    omega

theorem mem_shellU_depth {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) (u : cellU y) :
    u ∈ shellU k y (depthU k (u : GU σ n)) :=
  (mem_shellU_iff_depth k y _ u).2 le_rfl

theorem shellU_mono {σ : L →+* L} {n : ℕ} (k : Fin (n / 2)) (y : GU σ n) {j j' : ℤ} (h : j ≤ j') :
    shellU k y j ⊆ shellU k y j' :=
  fun _ hu => le_trans hu (WithZero.exp_le_exp.2 h)

end WeylUnipotentShell

end WeylCell

end GlobalTheory

end
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace ShellSum

open Function

def shell {X : Type} (H : ℕ → Set X) : ℕ → Set X
  | 0 => H 0
  | j + 1 => H (j + 1) \ H j

def shellVal (q : ℕ) (b : ℂ) : ℕ → ℂ
  | 0 => 1
  | j + 1 => (b / q) ^ (j + 1)

def shellMass (q : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => (q : ℝ) ^ (j + 1) - (q : ℝ) ^ j

theorem shellMass_nonneg (q : ℕ) (hq : 2 ≤ q) (j : ℕ) : 0 ≤ shellMass q j := by
  cases j with
  | zero => simp [shellMass]
  | succ j =>
    simp only [shellMass, sub_nonneg]
    exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) (Nat.le_succ j)

theorem hasSum_shell (q : ℕ) (hq : 2 ≤ q) (b : ℂ) (hb : ‖b‖ < 1) :
    HasSum (fun j => shellVal q b j * (shellMass q j : ℂ)) (cSL q b) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : HasSum (fun j : ℕ => b ^ j * (b * (1 - (q : ℂ)⁻¹))) ((1 - b)⁻¹ * (b * (1 - (q : ℂ)⁻¹))) :=
    (hasSum_geometric_of_norm_lt_one hb).mul_right _
  have hb1 : (1 - b) ≠ 0 := by
    intro h
    have : b = 1 := by linear_combination -h
    rw [this] at hb; simp at hb
  have e1 : (fun n : ℕ => shellVal q b (n + 1) * (shellMass q (n + 1) : ℂ)) =
      fun j => b ^ j * (b * (1 - (q : ℂ)⁻¹)) := by
    funext j; simp only [shellVal, shellMass, div_pow]; push_cast; field_simp; ring
  have e2 : cSL q b - ∑ i ∈ Finset.range 1, shellVal q b i * (shellMass q i : ℂ) =
      (1 - b)⁻¹ * (b * (1 - (q : ℂ)⁻¹)) := by
    simp only [Finset.range_one, Finset.sum_singleton, shellVal, shellMass, cSL, Complex.ofReal_one]
    field_simp; ring
  refine (hasSum_nat_add_iff' 1).1 ?_
  show HasSum (fun n : ℕ => shellVal q b (n + 1) * (shellMass q (n + 1) : ℂ))
    (cSL q b - ∑ i ∈ Finset.range 1, shellVal q b i * (shellMass q i : ℂ))
  rw [e1, e2]; exact h1

theorem mem_shell_iff {X : Type} {H : ℕ → Set X} (hmono : Monotone H) (j : ℕ) (x : X) :
    x ∈ shell H j ↔ x ∈ H j ∧ ∀ i < j, x ∉ H i := by
  cases j with
  | zero => simp [shell]
  | succ j =>
    simp only [shell, Set.mem_diff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i hi hx => h2 (hmono (Nat.lt_succ_iff.1 hi) hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 j (Nat.lt_succ_self j)⟩

theorem shell_disjoint {X : Type} {H : ℕ → Set X} (hmono : Monotone H) :
    Pairwise (Disjoint on shell H) := by
  have key : ∀ i j, i < j → Disjoint (shell H i) (shell H j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    exact ((mem_shell_iff hmono j x).1 hj).2 i hij ((mem_shell_iff hmono i x).1 hi).1
  intro i j hij
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem iUnion_shell {X : Type} {H : ℕ → Set X} (hmono : Monotone H) (hU : ⋃ j, H j = Set.univ) :
    ⋃ j, shell H j = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hex : ∃ n, x ∈ H n := Set.mem_iUnion.1 (hU ▸ Set.mem_univ x)
  exact Set.mem_iUnion.2 ⟨Nat.find hex, (mem_shell_iff hmono _ x).2
    ⟨Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩⟩

theorem integral_geom_on_shells {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℕ) (hq : 2 ≤ q) (a : ℂ)
    (ha : ‖a‖ < 1) (H : ℕ → Set X) (hH : ∀ j, MeasurableSet (H j)) (hmono : Monotone H)
    (hU : ⋃ j, H j = Set.univ) (hμ : ∀ j, μ (H j) = (q : ENNReal) ^ j) (F : X → ℂ)
    (hF0 : ∀ x ∈ H 0, F x = 1) (hF : ∀ j x, x ∈ H (j + 1) → x ∉ H j → F x = (a / q) ^ (j + 1)) :
    Integrable F μ ∧ ∫ x, F x ∂μ = cSL q a ∧ ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ := by
  set S := shell H with hSdef
  have hSm : ∀ j, MeasurableSet (S j) := by
    intro j; cases j with
    | zero => exact hH 0
    | succ j => exact (hH _).diff (hH _)
  have hSd : Pairwise (Disjoint on S) := shell_disjoint hmono
  have hSU : ⋃ j, S j = Set.univ := iUnion_shell hmono hU
  have hSF : ∀ j, ∀ x ∈ S j, F x = shellVal q a j := by
    intro j x hx; cases j with
    | zero => exact hF0 x hx
    | succ j => exact hF j x hx.1 hx.2
  have hSμ : ∀ j, μ (S j) = ENNReal.ofReal (shellMass q j) := by
    intro j; cases j with
    | zero => simp [hSdef, shell, shellMass, hμ]
    | succ j =>
      show μ (H (j + 1) \ H j) = _
      rw [measure_diff (hmono (Nat.le_succ j)) (hH j).nullMeasurableSet
          (by rw [hμ]; exact ENNReal.pow_ne_top (by simp)),
        hμ, hμ, shellMass, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  have hSr : ∀ j, μ.real (S j) = shellMass q j := by
    intro j; rw [Measure.real, hSμ, ENNReal.toReal_ofReal (shellMass_nonneg q hq j)]
  have hmeas : AEStronglyMeasurable F μ := by
    rw [← Measure.restrict_univ (μ := μ), ← hSU, aestronglyMeasurable_iUnion_iff]
    intro j
    refine (aestronglyMeasurable_const (b := shellVal q a j)).congr ?_
    filter_upwards [ae_restrict_mem (hSm j)] with x hx
    exact (hSF j x hx).symm
  set s : ℝ := (1 - (q : ℝ)⁻¹ * ‖a‖) / (1 - ‖a‖) with hsdef
  have hq1 : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ q))
  have hs0 : 0 ≤ s := by
    apply div_nonneg
    · have : (q : ℝ)⁻¹ * ‖a‖ ≤ 1 := mul_le_one₀ hq1 (norm_nonneg a) ha.le
      linarith
    · linarith
  have hsC : ((s : ℝ) : ℂ) = cSL q ((‖a‖ : ℝ) : ℂ) := by
    rw [hsdef]; unfold cSL; push_cast; ring
  have hreal : HasSum (fun j => ‖shellVal q a j‖ * shellMass q j) s := by
    have e : (fun j => ((‖shellVal q a j‖ * shellMass q j : ℝ) : ℂ)) =
        fun j => shellVal q ((‖a‖ : ℝ) : ℂ) j * (shellMass q j : ℂ) := by
      funext j
      cases j with
      | zero => simp [shellVal]
      | succ j => simp [shellVal, norm_pow, norm_div]
    refine Complex.hasSum_ofReal.1 ?_
    show HasSum (fun j => ((‖shellVal q a j‖ * shellMass q j : ℝ) : ℂ)) ((s : ℝ) : ℂ)
    rw [e, hsC]
    exact hasSum_shell q hq ((‖a‖ : ℝ) : ℂ) (by simpa using ha)
  have hL : ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ := by
    rw [← setLIntegral_univ, ← hSU, lintegral_iUnion hSm hSd]
    have hterm : ∀ j, ∫⁻ x in S j, ‖F x‖ₑ ∂μ = ENNReal.ofReal (‖shellVal q a j‖ * shellMass q j) := by
      intro j
      rw [setLIntegral_congr_fun (hSm j) (fun x hx => by rw [hSF j x hx]), setLIntegral_const, hSμ,
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (norm_nonneg _) (shellMass_nonneg q hq j))
      hreal.summable, hreal.tsum_eq, ← hsC, ← ofReal_norm_eq_enorm, Complex.norm_real,
      Real.norm_of_nonneg hs0]
  have hint : Integrable F μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hL]
    exact enorm_lt_top
  refine ⟨hint, ?_, hL⟩
  have h1 := hasSum_integral_iUnion hSm hSd hint.integrableOn
  rw [hSU, Measure.restrict_univ] at h1
  refine h1.unique ?_
  have e3 : (fun n => ∫ x in S n, F x ∂μ) = fun j => shellVal q a j * (shellMass q j : ℂ) := by
    funext j
    rw [setIntegral_congr_fun (hSm j) (fun x hx => hSF j x hx), setIntegral_const, hSr, Complex.real_smul,
      mul_comm]
  rw [e3]
  exact hasSum_shell q hq a ha

end ShellSum

theorem integral_geometric_shells : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℕ), 2 ≤ q →
    ∀ (a : ℂ), ‖a‖ < 1 →
    ∀ (H : ℕ → Set X), (∀ j, MeasurableSet (H j)) → Monotone H → ⋃ j, H j = Set.univ →
    (∀ j, μ (H j) = (q : ENNReal) ^ j) → ∀ (F : X → ℂ), (∀ x ∈ H 0, F x = 1) →
    (∀ j x, x ∈ H (j + 1) → x ∉ H j → F x = (a / q) ^ (j + 1)) →
    Integrable F μ ∧ ∫ x, F x ∂μ = cSL q a ∧ ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ :=
  fun μ q hq a ha H hH hmono hU hμ F hF0 hF =>
    ShellSum.integral_geom_on_shells μ q hq a ha H hH hmono hU hμ F hF0 hF

end GlobalTheory

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.GalDef

def wAt {n : ℕ} (lam : DomWeight n) (k : ℕ) : ℤ := if h : k < n then lam.w ⟨k, h⟩ else 0

def IsRunAt {n : ℕ} (lam : DomWeight n) (p t : ℕ) : Prop :=
  p + t ≤ n ∧ (∀ k, p ≤ k → k < p + t → wAt lam k = wAt lam p) ∧ (1 ≤ p → wAt lam p < wAt lam (p - 1)) ∧
    (p + t < n → wAt lam (p + t) < wAt lam p)

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def jumpsOf (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight n) (τ : E →+* Qbar l) : Multiset ℤ :=
  Finset.univ.val.map fun k : Fin n => (k : ℤ) - (lam (ι.toRingHom.comp τ)).w k

def FrobSat (ι : Qbar l ≃+* ℂ) (π : Submodule ℂ (UA E n → ℂ)) (sgn : ℤˣ) (cp : G E Ω → Polynomial (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsUnramU π w →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → GlobalTheory.LFun.HasSatGL w σ.ρ T →
      ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
        cp (g ^ (sgn : ℤ)) = (T.map fun z : ℂˣ =>
          X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod

def HasString (l : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (t : ℕ) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 E), IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ IsUnramU π w ∧
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ) (ν : ℂ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ T ∧ ‖ν‖ = 1 ∧
        (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
          T.map fun z : ℂˣ => (z : ℂ)

end GlobalTheory.GalDef

end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MuExist

def nsUnits (E : Type) [Field E] [NumberField E] [IsCMField E] : Subgroup (Neutral.B1.Ideles E) :=
  Subgroup.closure {x | ∃ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ GlobalTheory.UnitaryBC.IsSplitAt w ∧
    Valued.v (u : w.adicCompletion E) = 1 ∧ x = Neutral.B1.localIdele E w u}

theorem localIdele_mem_nsUnits {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (u : (w.adicCompletion E)ˣ) (hw : ¬ GlobalTheory.UnitaryBC.IsSplitAt w) (hu : Valued.v (u : w.adicCompletion E) = 1) :
    Neutral.B1.localIdele E w u ∈ nsUnits E :=
  Subgroup.subset_closure ⟨w, u, hw, hu, rfl⟩

end GlobalTheory.MuExist
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelCarry

theorem linComb_prod' {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : linComb y a = ∏ i, y i ^ a i := List.prod_ofFn

theorem unitOn_zpow' {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow _ _ _

theorem unitOn_inj' {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  simp only [unitOn, Units.coe_map] at h'
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective h'

end GlobalTheory.LevelCarry


open GlobalTheory.LevelCarry in
theorem GlobalTheory.levelPoint_baseChange_label : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  intro K C _ _ _ f P P' io hW g k hg ζ lev hk
  subst hg
  have := P'.isAb.comm
  have hk0 : NeZero k := ⟨by omega⟩
  have E : ∀ c : Fin (2 * P'.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  have LP : ∀ a, levelPoint lev rfl a = ∏ i, lev.pt i ^ (a i).val := fun a => by
    rw [levelPoint_rfl]; exact linComb_prod' _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective
      (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.toMonoidHom) lev.prim unitOn_inj'
  · intro a b
    rw [← map_mul]
    congr 1
    rw [LP, LP, LP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, pow_eq_pow_mod ((a i).val + (b i).val) (lev.torsion i), Pi.add_apply, ZMod.val_add]
  · have inj : Function.Injective (levelPoint lev rfl) := by
      intro a b h
      have h₀ := lev.indep C (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩)
        ((E _).trans (h.trans (E _).symm))
      exact funext fun i => ZMod.val_injective k (congrArg Fin.val (congrFun h₀ i))
    exact io.symm.injective.comp inj
  · intro z hz
    have hz' : (io z) ^ k = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨c, hc⟩ := lev.span C (𝟙 _) (io z) hz'
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_⟩
    rw [MulEquiv.symm_apply_eq, levelPoint_rfl, Level.toPt]
    exact (congrArg (linComb lev.pt) (funext fun i => ZMod.val_natCast_of_lt (c i).isLt)).trans
      ((E _).symm.trans hc)
  · intro i j
    haveI : Fact (1 < k) := ⟨by omega⟩
    have hs : ∀ i, levelPoint lev rfl (Pi.single i 1) = lev.pt i := fun i => by
      rw [LP, Finset.prod_eq_single i]
      · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs, hs]
    apply hW
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, unitOn_zpow']
    exact lev.pairing i j
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

namespace GlobalTheory.HenQ.DetSplit

variable {K : Type} [Field K] [NumberField K] [IsTotallyReal K] {n : ℕ}

omit [NumberField K] in
theorem norm_realSymm (w : InfinitePlace K) (r : ℝ) :
    ‖((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r : w.Completion)‖ = |r| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.dist_eq r 0
  have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 : w.Completion) = 0 :=
    map_zero _
  rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
  exact h

theorem ideleModule_infId (u : (Rinf K)ˣ) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (UpperTheory.V.TR.infId K u) : ℝ) = ∏ w, |u.val w| := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).1 = UpperTheory.V.TR.infEq K u.val := by
    show (1 : InfiniteAdeleRing K) - UpperTheory.V.TR.infEq K 1 + UpperTheory.V.TR.infEq K u.val = _
    simp
  have h2 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).2 = 1 := by
    show (1 : Af K) - 0 + 0 = 1
    simp
  rw [h1, h2]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : Af K) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by exact norm_one
  rw [h3, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  exact norm_realSymm w (u.val w)

end GlobalTheory.HenQ.DetSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → (∀ τ, lowT M τ ≠ ⊥) → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, (∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) → T = 0 := by
  first | exact @GlobalTheory.LowTypeDetermined.eq_zero_of_lowT | exact GlobalTheory.LowTypeDetermined.eq_zero_of_lowT | (intros; apply GlobalTheory.LowTypeDetermined.eq_zero_of_lowT <;> assumption)
end
