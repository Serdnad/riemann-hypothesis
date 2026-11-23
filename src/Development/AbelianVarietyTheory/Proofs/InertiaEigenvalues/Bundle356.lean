module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle083
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle088
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle336
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

section

noncomputable section

namespace GlobalTheory.RowModelRoad

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.BlockComplement GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

section Twist

variable {Γ O : Type} [Group Γ] [CommRing O] {n : ℕ}

end Twist

section Lift

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end Lift

section Eig

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) (i : N.Loc)

theorem frobEig_block (θ : A.CG 1) (t : ℕ) (w : PlE H) (b : ℂ) (hu : A.unr (A.locG θ w))
    (hb : A.frobEig (A.locG θ w) = {b}) :
    A.unr (spehLoc N A ⟨1, θ, t⟩ w) ∧ A.frobEig (spehLoc N A ⟨1, θ, t⟩ w) =
      ((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => b * ((normV w : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ) := by
  unfold spehLoc
  dsimp only
  induction List.range t with
  | nil => exact ⟨A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    have h1 := (A.unr_tw _ (((t : ℝ) - 1) / 2 - k)).2 hu
    refine ⟨(A.unr_sum _ _).2 ⟨h1, ih.1⟩, ?_⟩
    refine (A.frobEig_sum _ _ h1 ih.1).trans ?_
    rw [ih.2, A.frobEig_tw _ _ hu, hb]
    simp

end Eig

variable {D : D7}

end GlobalTheory.RowModelRoad
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



namespace GlobalTheory.WeakClosed

theorem tailDecomp {O : Type} [CommRing O] {n : ℕ} (k : ℕ) (a : LetA O n) :
    a = (∑ j ∈ Finset.range k, fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j) +
      (letπ : LetA O n) ^ k * (fun i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (a i)) := by
  funext i
  ext m

  simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, letπ, map_add (f := _), map_sum,
  PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
  Finset.sum_ite_eq, Finset.mem_range]
  by_cases hk : m < k
  · simp [hk, Nat.not_le.2 hk]
  · simp [hk, Nat.le_of_not_lt hk, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]

theorem continuous_of_tail {O : Type} [CommRing O] [TopologicalSpace O] {n : ℕ} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] (Φ : LetA O n →+ M)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ r : LetA O n, Φ (letπ ^ k * r) ∈ U)
    (hmono : ∀ j : ℕ, Continuous fun c : ZMod n → O => Φ (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) :
    Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro a₀
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half hU
  obtain ⟨k, hk⟩ := hsmall V hV
  let mono : ℕ → LetA O n → M := fun j a =>
    Φ (fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j)
  have hcont : ∀ j, Continuous (mono j) := fun j =>
    (hmono j).comp (continuous_pi fun i =>
      (PowerSeries.WithPiTopology.continuous_coeff O j).comp (continuous_apply i))
  let S : LetA O n → M := fun a => ∑ j ∈ Finset.range k, (mono j a - mono j a₀)
  have hS : Continuous S := continuous_finsetSum _ fun j _ => (hcont j).sub continuous_const
  have hS0 : S a₀ = 0 := by simp [S]
  have hSV : ∀ᶠ a in 𝓝 a₀, S a ∈ V := by
    have := hS.continuousAt (x := a₀)
    rw [ContinuousAt, hS0] at this
    exact this hV
  rw [Filter.mem_map]
  filter_upwards [hSV] with a ha
  let tl : LetA O n → LetA O n := fun b i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (b i)
  have hΦ : ∀ b, Φ b = (∑ j ∈ Finset.range k, mono j b) + Φ (letπ ^ k * tl b) := by
    intro b
    conv_lhs => rw [tailDecomp k b]

    rw [map_add (f := _), map_sum]
  have : Φ a - Φ a₀ = S a + Φ (letπ ^ k * (tl a - tl a₀)) := by
    rw [hΦ a, hΦ a₀, mul_sub, map_sub]
    simp only [S, Finset.sum_sub_distrib]
    abel
  show Φ a - Φ a₀ ∈ U
  rw [this]
  exact hVV _ ha _ (hk _)

end GlobalTheory.WeakClosed
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem GK.finite_image_of_trivial_on_open :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (Q : Type) [Group Q] (ρ : ↥(GK K) →* Q)
      (J H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → (∀ g ∈ J, g ∈ H → ρ g = 1) →
      (ρ '' (J : Set ↥(GK K))).Finite := by
  intro l _ K Q _ ρ J H hH hρ
  haveI := GlobalTheory.T.finiteIndex_of_isOpen_absGalois_finExt l K H hH
  exact GlobalTheory.T.finite_image_of_trivial_on_inf_finiteIndex _ Q ρ J H inferInstance hρ

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Topology

namespace GlobalTheory.UnramifiedDegree

theorem exists_degree : ∀ (l : ℕ) [Fact l.Prime],
    (∀ n : ℕ, 0 < n → ∀ σ : GQ l, ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
    (∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) → a ≡ b [MOD n]) →
    ∃ z : GQ l → ℤ_[l], Continuous z ∧ (∀ σ τ, z (σ * τ) = z σ + z τ) ∧
      ∀ (σ : GQ l) (a : ℕ), (∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
        z σ = (a : ℤ_[l]) := by
  intro l hl h1 h2
  have hpos : ∀ k : ℕ, 0 < l ^ k := fun k => pow_pos hl.out.pos k
  choose a ha using fun (σ : GQ l) (k : ℕ) => h1 (l ^ k) (hpos k) σ
  have hdv : ∀ (σ : GQ l) (k : ℕ), (l : ℤ) ^ k ∣ (a σ (k + 1) : ℤ) - (a σ k : ℤ) := by
    intro σ k
    have h := h2 (l ^ k) (a σ k) (a σ (k + 1)) (hpos k) fun x hx => by
      rw [← ha σ k x hx, ← ha σ (k + 1) x (by
        rw [pow_succ l k]; exact GlobalTheory.UnramifiedCrys.pow_pow_mul hx l)]
    exact_mod_cast h.dvd
  obtain ⟨z, hz⟩ : ∃ z : GQ l → ℤ_[l], ∀ σ k, PadicInt.toZModPow k (z σ) = (a σ k : ZMod (l ^ k)) := by
    refine ⟨fun σ => PadicInt.ofIntSeq _
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ)), fun σ k => ?_⟩
    rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ) k,
      Int.cast_natCast]
  have key : ∀ (σ : GQ l) (k b : ℕ), (∀ x : Om l, x ^ l ^ l ^ k = x → σ x = x ^ l ^ b) →
      PadicInt.toZModPow k (z σ) = (b : ZMod (l ^ k)) := by
    intro σ k b hb
    rw [hz, ZMod.natCast_eq_natCast_iff]
    exact h2 _ _ _ (hpos k) fun x hx => by rw [← ha σ k x hx, hb x hx]
  refine ⟨z, ?_, fun σ τ => ?_, fun σ b hb => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro σ₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
    have hev : ∀ᶠ σ in 𝓝 σ₀, ∀ x ∈ {y : Om l | y ^ l ^ l ^ k = y}, σ x = σ₀ x := by
      refine (GlobalTheory.UnramifiedCrys.finite_fixedPow (p := l) (R := Om l) (hpos k)).eventually_all.2
        fun x _ => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x).preimage
        (continuous_const_mul σ₀⁻¹)
      filter_upwards [ho.mem_nhds (show σ₀ ∈ _ by simp)] with σ hσ
      have h : σ₀⁻¹ (σ x) = x := hσ
      have h' := congrArg σ₀ h
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
    filter_upwards [hev] with σ hσ
    refine lt_of_le_of_lt ?_ hk
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, sub_eq_zero, hz σ₀]
    exact key σ k _ fun x hx => by rw [hσ x hx, ha σ₀ k x hx]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_add (f := _), hz σ, hz τ, ← Nat.cast_add]
    refine key _ k _ fun x hx => ?_
    rw [AlgEquiv.mul_apply, ha τ k x hx, map_pow, ha σ k x hx, ← pow_mul, ← pow_add]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_natCast]
    exact key σ k b (hb _ (hpos k))

end GlobalTheory.UnramifiedDegree
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section
namespace GlobalTheory.UnramZl
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem modEq_of_pow_modEq {l d : ℕ} (hl : 1 < l) (hd : 0 < d) {a b : ℕ}
    (h : l ^ a ≡ l ^ b [MOD l ^ d - 1]) : a ≡ b [MOD d] := by
  wlog hab : a ≤ b generalizing a b
  · exact (this h.symm (le_of_not_ge hab)).symm
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 : l ^ d - 1 ∣ l ^ (a + c) - l ^ a :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hl.le hab)).1 h
  rw [pow_add, ← Nat.mul_sub_one] at h1
  have hcop : (l ^ d - 1).Coprime (l ^ a) := by
    apply Nat.Coprime.pow_right
    have h2 : (l ^ d - 1).Coprime (l ^ d) := by
      have : l ^ d = (l ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
      conv_rhs => rw [this]
      simp
    exact h2.coprime_dvd_right (dvd_pow_self l hd.ne')
  have h3 := Nat.gcd_eq_left (hcop.dvd_of_dvd_mul_left h1)
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h3
  have h4 : l ^ d.gcd c = l ^ d := by
    have := Nat.one_le_pow (d.gcd c) l (by omega)
    have := Nat.one_le_pow d l (by omega)
    omega
  have h5 : d ∣ c := (Nat.pow_right_injective hl h4) ▸ Nat.gcd_dvd_right d c
  exact (Nat.modEq_iff_dvd' hab).2 (by simpa using h5)

variable {l : ℕ} [hl : Fact l.Prime]

theorem lev_pos (n : ℕ) : 0 < l ^ (l ^ n) - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow (pow_pos hl.out.pos n).ne' hl.out.one_lt)

theorem not_dvd_lev (n : ℕ) : ¬ l ∣ l ^ (l ^ n) - 1 := fun h => by
  have h1 : l ∣ l ^ (l ^ n) := dvd_pow_self l (pow_pos hl.out.pos n).ne'
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hl.out.pos)] at h2
  exact hl.out.not_dvd_one h2

def Acts (g : GQ l) (n a : ℕ) : Prop :=
  ∀ ζ : Om l, ζ ^ (l ^ (l ^ n) - 1) = 1 → g ζ = ζ ^ (l ^ a)

theorem exists_prim (n : ℕ) : ∃ ξ : Om l, IsPrimitiveRoot ξ (l ^ (l ^ n) - 1) := by
  haveI : NeZero (l ^ (l ^ n) - 1) := ⟨(lev_pos n).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) _

theorem Acts.uniq {g : GQ l} {n a b : ℕ} (ha : Acts g n a) (hb : Acts g n b) :
    a ≡ b [MOD l ^ n] := by
  obtain ⟨ξ, hξ⟩ := exists_prim (l := l) n
  have h := (ha ξ hξ.pow_eq_one).symm.trans (hb ξ hξ.pow_eq_one)
  rw [(hξ.isOfFinOrder (lev_pos n).ne').pow_eq_pow_iff_modEq, ← hξ.eq_orderOf] at h
  exact modEq_of_pow_modEq hl.out.one_lt (pow_pos hl.out.pos n) h

theorem Acts.down {g : GQ l} {n a : ℕ} (ha : Acts g (n + 1) a) : Acts g n a := fun ζ hζ => by
  obtain ⟨c, hc⟩ := Nat.pow_sub_one_dvd_pow_sub_one l (pow_dvd_pow l (Nat.le_succ n))
  exact ha ζ (by rw [hc, pow_mul, hζ, one_pow])

theorem Acts.mul {g h : GQ l} {n a b : ℕ} (ha : Acts g n a) (hb : Acts h n b) :
    Acts (g * h) n (a + b) := fun ζ hζ => by
  rw [AlgEquiv.mul_apply, hb ζ hζ, map_pow, ha ζ hζ, ← pow_mul, pow_add]

theorem exists_acts (g : GQ l) (n : ℕ) : ∃ a, Acts g n a :=
  gal_root g (lev_pos n) (not_dvd_lev n)

theorem exists_deg (g : GQ l) :
    ∃ x : ℤ_[l], ∀ n a, Acts g n a → PadicInt.toZModPow n x = (a : ZMod (l ^ n)) := by
  choose a ha using exists_acts g
  have hdv : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - a i := fun i => by
    have := ((ha i).uniq (ha (i + 1)).down).dvd
    exact_mod_cast this
  refine ⟨PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (a n : ℤ)) l hdv), fun n b hb => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (a n : ℤ)) l hdv n, Int.cast_natCast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 ((ha n).uniq hb)

def deg (g : GQ l) : ℤ_[l] := (exists_deg g).choose

theorem deg_spec {g : GQ l} {n a : ℕ} (h : Acts g n a) :
    PadicInt.toZModPow n (deg g) = (a : ZMod (l ^ n)) := (exists_deg g).choose_spec n a h

theorem deg_mul (g h : GQ l) : deg (g * h) = deg g + deg h := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  obtain ⟨a, ha⟩ := exists_acts g n
  obtain ⟨b, hb⟩ := exists_acts h n
  rw [map_add (f := _), deg_spec ha, deg_spec hb, deg_spec (ha.mul hb), Nat.cast_add]

theorem deg_eq_nat {g : GQ l} {a : ℕ} (h : ∀ n, Acts g n a) : deg g = a := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [deg_spec (h n), map_natCast]

theorem deg_one : deg (1 : GQ l) = 0 := by
  simpa using deg_eq_nat (g := (1 : GQ l)) (a := 0) fun n ζ _ => by simp

theorem deg_pow (g : GQ l) (N : ℕ) : deg (g ^ N) = N * deg g := by
  induction N with
  | zero => simp [deg_one]
  | succ N ih => rw [pow_succ, deg_mul, ih]; push_cast; ring

theorem continuous_deg : Continuous (deg : GQ l → ℤ_[l]) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt l hε
  obtain ⟨ξ, hξ⟩ := exists_prim (l := l) n
  haveI : NeZero (l ^ (l ^ n) - 1) := ⟨(lev_pos n).ne'⟩
  have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) ξ).preimage (continuous_const_mul g⁻¹)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ MulAction.stabilizer (GQ l) ξ by simp)] with h hh
  have h1 : (g⁻¹ * h) ξ = ξ := hh
  have h2 : h ξ = g ξ := by
    conv_rhs => rw [← h1, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
  obtain ⟨a, ha⟩ := exists_acts g n
  have hb : Acts h n a := fun ζ hζ => by
    rw [← ha ζ hζ]
    obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hζ
    rw [map_pow, map_pow, h2]
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hn
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    deg_spec ha, deg_spec hb, sub_self]

theorem deg_inertia {g : GQ l} (h : ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) : deg g = 0 := by
  simpa using deg_eq_nat (g := g) (a := 0) fun n ζ hζ => by
    let a : OO l := ⟨ζ, (norm_root (lev_pos n) hζ).le⟩
    have ha : a ^ (l ^ (l ^ n) - 1) = 1 := Subtype.ext hζ
    have := res_inj (lev_pos n) (not_dvd_lev n) (a := galO g a) (b := a)
      (by rw [← map_pow, ha, map_one]) ha ((res_eq_iff _ _).2 (h ζ a.2))
    rw [pow_zero, pow_one]
    exact congrArg Subtype.val this

theorem exists_deg_eq_one : ∃ g : GQ l, deg g = 1 := by
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨g, hg⟩ := exists_ext σ
  refine ⟨g, ?_⟩
  simpa using deg_eq_nat (g := g) (a := 1) fun n ζ hζ => by
    let c : ↥(MaximalUnramifiedExtension l) :=
      ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨_, lev_pos n, not_dvd_lev n, hζ⟩⟩
    have := hσ c _ (lev_pos n) (not_dvd_lev n) (Subtype.ext hζ)
    rw [show ζ = (c : Om l) from rfl, hg, this, pow_one]; rfl

theorem exists_unramified_character : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    ∃ δ : ↥(GK K) → ℚ_[l], Continuous δ ∧ (∀ g h, δ (g * h) = δ g + δ h) ∧
      (∀ g ∈ IK K, δ g = 0) ∧ ∃ g, δ g ≠ 0 := by
  intro l _ K
  refine ⟨fun g => (deg (g : GQ l) : ℚ_[l]),
    continuous_subtype_val.comp (continuous_deg.comp continuous_subtype_val),
    fun g h => by simp [deg_mul], fun g hg => ?_, ?_⟩
  · have : deg (g : GQ l) = 0 := by
      unfold IK at hg
      induction hg using Subgroup.closure_induction with
      | mem x hx => exact deg_inertia hx
      | one => exact deg_one
      | mul x y _ _ hx hy => rw [Subgroup.coe_mul, deg_mul, hx, hy, add_zero]
      | inv x _ hx =>
        have := deg_mul ((x⁻¹ : ↥(GK K)) : GQ l) x
        rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, deg_one, hx, add_zero] at this
        exact this.symm
    simp [this]
  · obtain ⟨φ, hφ⟩ := exists_deg_eq_one (l := l)
    haveI := K.2
    haveI : Finite (GQ l ⧸ GK K) :=
      Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K.1)
    obtain ⟨N, hN, -, hm⟩ := (GK K).exists_pow_mem_of_index_ne_zero Subgroup.index_ne_zero_of_finite φ
    refine ⟨⟨φ ^ N, hm⟩, ?_⟩
    simp [deg_pow, hφ, hN.ne']

end GlobalTheory.UnramZl
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

theorem _root_.GlobalTheory.T.exists_wachModule_generator_reduction : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {k : Type} [Field k] [Algebra O k] (lam : O), Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 ↔ lam ∣ x) → ((PD.p : ℕ) : k) = 0 → ∃ p : ZMod n → (W.EE →+* k⸨X⸩), (∀ i (a : LetA O n), p i (algebraMap (LetA O n) W.EE a) = ((PowerSeries.map (algebraMap O k) (a i) : k⟦X⟧) : k⸨X⸩)) ∧ (∀ i, Function.Surjective (p i)) ∧ ∀ i e, p i e = 0 → ∃ e', algebraMap (LetA O n) W.EE (letE i) * e = algebraMap O W.EE lam * e' := by
  first | exact @GlobalTheory.RedFun.exists_letter_reduction | exact GlobalTheory.RedFun.exists_letter_reduction | (intros; apply GlobalTheory.RedFun.exists_letter_reduction <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finite_H1_period_datum : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), TateFiniteness (P.PD K) := by
  first | exact @GlobalTheory.TateFiniteH1.tate_finH1 | exact GlobalTheory.TateFiniteH1.tate_finH1 | (intros; apply GlobalTheory.TateFiniteH1.tate_finH1 <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finite_H1_reduction : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  first | exact @GlobalTheory.CocycleModPow.finite_H1Q_lpow | exact GlobalTheory.CocycleModPow.finite_H1Q_lpow | (intros; apply GlobalTheory.CocycleModPow.finite_H1Q_lpow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.H1_lattice_index_growth_of_tateDuality_eulerChar : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  first | exact @GlobalTheory.EulerLevel.card_H1Q_eq | exact GlobalTheory.EulerLevel.card_H1Q_eq | (intros; apply GlobalTheory.EulerLevel.card_H1Q_eq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_mutuallyDual_stable_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ), IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  first | exact @GlobalTheory.StableDual.stable_dual_lattices | exact GlobalTheory.StableDual.stable_dual_lattices | (intros; apply GlobalTheory.StableDual.stable_dual_lattices <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

theorem _root_.GlobalTheory.T.exists_ringHom_of_idempotent_surjective_family : ∀ (I E F R : Type) [Fintype I] [CommRing E] [CommRing F] [CommRing R] (e : I → E), (∀ i, e i * e i = e i) → (∀ i j, i ≠ j → e i * e j = 0) → ∑ i, e i = 1 → ∀ (p : I → (E →+* F)) (r : E →+* R), (∀ i, Function.Surjective (p i)) → (∀ i x, p i x = 0 → r (e i) * r x = 0) → ∃ κ : F →+* R, ∀ i x, r (e i) * κ (p i x) = r (e i) * r x := by
  first | exact @GlobalTheory.exists_diagonal_ringHom_of_letterwise_reductions | exact GlobalTheory.exists_diagonal_ringHom_of_letterwise_reductions | (intros; apply GlobalTheory.exists_diagonal_ringHom_of_letterwise_reductions <;> assumption)
end
