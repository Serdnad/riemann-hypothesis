module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle025
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.Bound
public import Mathlib.Topology.MetricSpace.ProperSpace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle012
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle010
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle011
public import Formalism.FormalDegreeBessel.StatementDS
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
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

@[expose] public section

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.UnitBall

variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]

noncomputable def ball : ValuationSubring L :=
  by apply _root_.UpperTheory.Reformulated.B.BallSubgroup.ball <;> assumption

variable {L}

theorem mem_ball {x : L} : x ∈ ball L ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem isUnit_of_norm_eq_one {x : ball L} (h : ‖(x : L)‖ = 1) : IsUnit x := by
  have hx : (x : L) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact zero_ne_one h
  have hi : (x : L)⁻¹ ∈ ball L := by
    rw [mem_ball, norm_inv, h, inv_one]
  refine IsUnit.of_mul_eq_one ⟨(x : L)⁻¹, hi⟩ ?_
  apply Subtype.ext
  simp [hx]

theorem norm_eq_one_of_isUnit {x : ball L} (h : IsUnit x) : ‖(x : L)‖ = 1 := by
  obtain ⟨y, hy⟩ := h.exists_right_inv
  have h1 : (x : L) * (y : L) = 1 := by
    have := congrArg (Subtype.val) hy
    simpa using this
  have h2 : ‖(x : L)‖ * ‖(y : L)‖ = 1 := by
    rw [← norm_mul, h1, norm_one]
  have hx : ‖(x : L)‖ ≤ 1 := x.2
  have hy' : ‖(y : L)‖ ≤ 1 := y.2
  nlinarith [norm_nonneg (x : L), norm_nonneg (y : L)]

variable {p : Lˣ}

theorem norm_unif_pos (p : Lˣ) : 0 < ‖(p : L)‖ := norm_pos_iff.2 p.ne_zero

theorem exists_nat_norm (hp : IsUnif p) {x : L} (hx : x ≠ 0) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, ‖x‖ = ‖(p : L)‖ ^ m := by
  obtain ⟨a, ha⟩ := hp.2 x hx
  have h0 := norm_unif_pos p
  have hnn : 0 ≤ a := by
    by_contra hneg
    have hlt : a < 0 := not_le.1 hneg
    have : 1 < ‖(p : L)‖ ^ a := one_lt_zpow_of_neg₀ h0 hp.1 hlt
    linarith
  refine ⟨a.toNat, ?_⟩
  rw [ha, ← zpow_natCast, Int.toNat_of_nonneg hnn]

def unif (hp : IsUnif p) : ball L := ⟨p, hp.1.le⟩

theorem unif_coe (hp : IsUnif p) : ((unif hp : ball L) : L) = p := rfl

theorem irreducible_unif (hp : IsUnif p) : Irreducible (unif hp) := by
  have h0 := norm_unif_pos p
  refine ⟨fun h => ?_, ?_⟩
  · have := norm_eq_one_of_isUnit h
    rw [unif_coe] at this
    exact absurd this hp.1.ne
  · intro a b hab
    have hab' : (p : L) = (a : L) * (b : L) := by
      have := congrArg (Subtype.val) hab
      simpa [unif_coe] using this
    have ha0 : (a : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, zero_mul])
    have hb0 : (b : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, mul_zero])
    obtain ⟨i, hi⟩ := exists_nat_norm hp ha0 a.2
    obtain ⟨j, hj⟩ := exists_nat_norm hp hb0 b.2
    have hn : ‖(p : L)‖ ^ 1 = ‖(p : L)‖ ^ (i + j) := by
      rw [pow_one, pow_add, ← hi, ← hj, ← norm_mul, ← hab']
    have hij : 1 = i + j := pow_right_injective₀ h0 hp.1.ne hn
    rcases Nat.eq_zero_or_pos i with h | h
    · left
      apply isUnit_of_norm_eq_one
      rw [hi, h, pow_zero]
    · right
      have : j = 0 := by omega
      apply isUnit_of_norm_eq_one
      rw [hj, this, pow_zero]

theorem isDVR (hp : IsUnif p) : IsDiscreteValuationRing (ball L) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif hp, irreducible_unif hp, ?_⟩
  intro x hx
  have hx0 : (x : L) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨m, hm⟩ := exists_nat_norm hp hx0 x.2
  have h0 := norm_unif_pos p
  have hpm : (p : L) ^ m ≠ 0 := pow_ne_zero _ p.ne_zero
  have hq : ‖(x : L) / (p : L) ^ m‖ = 1 := by
    rw [norm_div, norm_pow, hm]
    exact div_self (pow_ne_zero _ h0.ne')
  let q : ball L := ⟨(x : L) / (p : L) ^ m, hq.le⟩
  obtain ⟨u, hu⟩ := isUnit_of_norm_eq_one (x := q) hq
  refine ⟨m, u, ?_⟩
  apply Subtype.ext
  have hu' : ((u : ball L) : L) = (x : L) / (p : L) ^ m := by rw [hu]
  change ((unif hp : ball L) : L) ^ m * ((u : ball L) : L) = (x : L)
  rw [hu', unif_coe]
  field_simp

theorem map_mem_congK (n : ℕ) (U : GL (Fin n) (ball L)) :
    Matrix.GeneralLinearGroup.map (algebraMap (ball L) L) U ∈ congK L n 1 zero_le_one le_rfl := by
  have key : ∀ (A : Matrix (Fin n) (Fin n) (ball L)) (i j : Fin n),
      ‖(A.map (algebraMap (ball L) L) - 1) i j‖ ≤ 1 := by
    intro A i j
    rw [Matrix.sub_apply, Matrix.map_apply, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (A i j).2 ?_)
    rw [norm_neg, Matrix.one_apply]
    split_ifs <;> simp
  intro i j
  refine ⟨key _ i j, ?_⟩
  rw [← map_inv]
  exact key _ i j

end GlobalTheory.CompanionTheory.CartGL.UnitBall

namespace GlobalTheory.CompanionTheory.CartGL


open UnitBall in
theorem cartan_unitBall (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (p : Lˣ) (hp : IsUnif p) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ congK L n 1 zero_le_one le_rfl,
      ∃ k₂ ∈ congK L n 1 zero_le_one le_rfl, g = k₁ * dPow p a * k₂ := by
  haveI := isDVR hp
  have hdet : IsUnit (g : Matrix (Fin n) (Fin n) L).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  obtain ⟨u, v, a, hu, hv, ha, hg⟩ := GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists (ball L) L n (unif hp)
    (irreducible_unif hp) (g : Matrix (Fin n) (Fin n) L) hdet
  obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det u).2 hu
  obtain ⟨V, rfl⟩ := (Matrix.isUnit_iff_isUnit_det v).2 hv
  refine ⟨a, ha, _, map_mem_congK n U, _, map_mem_congK n V, ?_⟩
  apply Units.ext
  rw [hg, Units.val_mul, Units.val_mul, dPow_val]
  have hd : (Matrix.diagonal fun i => (algebraMap (ball L) L (unif hp)) ^ (a i)) =
      Matrix.diagonal fun i => ((p ^ a i : Lˣ) : L) := by
    congr 1
    funext i
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  rw [hd]
  rfl

end GlobalTheory.CompanionTheory.CartGL
end
end

section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem isCongIdeal_congJ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    {π : L} (hπ : ‖π‖ < 1) {ι : Type} (P : ι → Module.End L V)
    (hP : ∀ i, ∀ x ∈ Λ, P i x ∈ Λ) : IsCongIdeal (congJ Λ π) P := by
  refine ⟨?_, ?_, ?_, GlobalTheory.T.congruence_endomorphism_inverse_exists Λ hΛ π hπ⟩
  · intro x hx y hy v hv
    obtain ⟨z, hz, e1⟩ := hy v hv
    obtain ⟨w, hw, e2⟩ := hx z hz
    refine ⟨π • w, lat_smul hΛ hπ.le hw, ?_⟩
    simp [Module.End.mul_apply, e1, e2]
  · intro i x hx v hv
    obtain ⟨z, hz, e1⟩ := hx v hv
    exact ⟨P i z, hP i z hz, by simp [Module.End.mul_apply, e1]⟩
  · intro i x hx v hv
    exact hx _ (hP i v hv)

theorem congJ_smul {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (π : L) (c : L) (hc : ‖c‖ ≤ 1) (x : Module.End L V)
    (hx : x ∈ congJ Λ π) : c • x ∈ congJ Λ π := by
  intro v hv
  obtain ⟨z, hz, e1⟩ := hx v hv
  refine ⟨c • z, lat_smul hΛ hc hz, ?_⟩
  simp [e1, smul_comm c π z]

theorem isUpper_rev_iff {E : Type} [Ring E] {l : ℕ} (P : Idx l → E) (b : E) :
    IsUpper (fun i => 2 * l - wt i) P b ↔ IsLower wt P b := by
  constructor
  · intro H i j hij
    exact H i j (by have := wt_le i; have := wt_le j; simp only; omega)
  · intro H i j hij
    refine H i j ?_
    have := wt_le i; have := wt_le j
    simp only at hij
    omega

theorem stIwahori : StIwahori := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hΛ hA π hπ k hk hc
  have hδ0 : δ ≠ 0 := hδ.1
  set P := piece hh δ e f with hPdef
  have hP : IsPieces P := isPieces_piece hh hδ0 hF
  have hJ : IsCongIdeal (congJ Λ π) P :=
    isCongIdeal_congJ hΛ hπ P fun i x hx => piece_mem hΛ hA hh hδ0 hF i hx
  obtain ⟨st, hst, st_mul, st_one, st_zero, st_P⟩ :=
    exists_star (δ := δ) (e := e) (f := f) (l := l) hs hh (GlobalTheory.T.hermitian_adjoint_exists s hs h hh)
  have hk1 : (k.toLinearMap : Module.End L V) - 1 ∈ congJ Λ π := fun x hx => by
    obtain ⟨y, hy, e1⟩ := hc x hx
    exact ⟨y, hy, by simpa using e1⟩
  obtain ⟨a, b, ha, hb, hup, hlo, hab⟩ := GlobalTheory.T.iwahori_upper_lower_factorization wt wt_injective P hP _ hJ _ hk1

  obtain ⟨ya, hya, ia1, ia2⟩ := hJ.inv _ ha
  obtain ⟨yb, hyb, ib1, ib2⟩ := hJ.inv _ hb
  rw [add_sub_cancel] at ia1 ia2 ib1 ib2
  have hkk : ∀ y, st (k.toLinearMap) (k y) = y := fun y => by
    refine eq_of_pair hh fun x => ?_
    have := hst k.toLinearMap x (k y)
    simp only [LinearEquiv.coe_coe] at this
    rw [← this, hk x y]
  have hk2 : st (k.toLinearMap) * (k.toLinearMap) = 1 := by
    ext y; exact hkk y
  have hk3 : (k.toLinearMap : Module.End L V) * st (k.toLinearMap) = 1 := by
    ext y
    obtain ⟨z, rfl⟩ := k.surjective y
    simp [Module.End.mul_apply, hkk z]
  rw [hab] at hk2 hk3
  obtain ⟨ua, ub⟩ := GlobalTheory.T.unitary_factors_of_unitary_upper_mul_lowerUni wt P hP rev rev_rev
    (fun i j hij => by have := wt_rev i; have := wt_rev j; omega) wt_injective st st_mul st_one st_zero st_P
    (fun a a' h1 h2 h3 => GlobalTheory.T.upper_triangular_inverse_is_upper wt P hP a a' h1 h2 h3)
    (fun a a' h1 h2 h3 => (isUpper_rev_iff P a').1 (GlobalTheory.T.upper_triangular_inverse_is_upper _ P hP a a' h1 h2 ((isUpper_rev_iff P a).2 h3)))
    a (1 + ya) b (1 + yb) ia1 ia2 ib1 ib2 hup hlo hk2 hk3
  let A : V ≃ₗ[L] V := LinearEquiv.ofLinear a (1 + ya) ia1 ia2
  let B : V ≃ₗ[L] V := LinearEquiv.ofLinear b (1 + yb) ib1 ib2
  have isoOf : ∀ (g : V ≃ₗ[L] V), st (g.toLinearMap) * g.toLinearMap = 1 → IsIso h g := fun g hg x y => by
    have := hst g.toLinearMap x (g y)
    simp only [LinearEquiv.coe_coe] at this
    rw [this]
    have h2 : st g.toLinearMap (g y) = y := by
      have := congrArg (fun m : Module.End L V => m y) hg
      simpa [Module.End.mul_apply] using this
    rw [h2]
  refine ⟨A, B, isoOf A ua, isoOf B ub, ?_, ?_⟩
  · ext x
    have := congrArg (fun m : Module.End L V => m x) hab
    simpa [A, B, Module.End.mul_apply] using this
  · intro u t hu0 hm h1 ht
    have hT := fun i => tor_piece (δ := δ) hh hδ0 hF ht i
    have key := GlobalTheory.T.torus_conjugation_preserves_congruence wt P hP _ hJ (congJ_smul hΛ π) (t.toLinearMap) (t.symm.toLinearMap) (tau s u)
      (tau_ne hu0) (by ext y; simp [Module.End.mul_apply]) (by ext y; simp [Module.End.mul_apply])
      (fun i => (hT i).1) (fun i => (hT i).2)
      (tau_mono hs hu0 hm h1) a b ha hb hup hlo.1
    constructor
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.1 x hx
      exact ⟨y, hy, by simpa [A, Module.End.mul_apply] using e1⟩
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.2 x hx
      exact ⟨y, hy, by simpa [B, Module.End.mul_apply] using e1⟩

end GlobalTheory.CompanionTheory.Iwahori

end
end

section

open Finset

namespace CompanionTheory.RgExh.Fin

def ArrCount : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (χ χ' : Fin n → ℂ), Function.Injective χ → Function.Injective χ' →
    (∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m) →
    (∀ a, (χ' a).im = 0 ∧ ∃ m : ℤ, (χ' a).re - ((n : ℝ) - 1) / 2 = m) →
    ∃ (A : Finset (Equiv.Perm (Fin n) × (Fin n → ℝ))) (A' : Finset (Equiv.Perm (Fin n) × (Fin n → ℝ))),
      A.card = A'.card ∧
      (∀ d, d ∈ A ↔ (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = χ (τ a))) ∧
      (∀ d, d ∈ A' ↔ (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = χ' (τ a)))

end CompanionTheory.RgExh.Fin

namespace GlobalTheory.CompanionTheory.ArrCount

theorem exists_unique_param {n : ℕ} (χ : Fin n → ℂ) (hχ : Function.Injective χ)
    (h : ∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m) :
    ∃ μ : Fin n → ℝ, ∀ m : Fin n → ℝ,
      (Formalism.QuantumDeterminants.IsHCParam m ∧ ∃ τ : Equiv.Perm (Fin n), ∀ a, ((m a : ℝ) : ℂ) = χ (τ a)) ↔ m = μ := by
  have hval : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a := fun a => Complex.ext (by simp) (by simp [(h a).1])
  let r : Fin n → ℝ := fun a => (χ a).re
  have hr : Function.Injective r := fun a b hab => hχ (by
    rw [← hval a, ← hval b]; exact congrArg _ hab)
  let τ₀ : Equiv.Perm (Fin n) := Tuple.sortDesc r
  have hanti : StrictAnti (r ∘ τ₀) :=
    (Tuple.antitone_sortDesc r).strictAnti_of_injective (hr.comp τ₀.injective)
  refine ⟨r ∘ τ₀, fun m => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨hm, -⟩, τ, hτ⟩
    have hmr : m = r ∘ τ := by
      funext a
      change m a = (χ (τ a)).re
      simpa only [Complex.ofReal_re] using congrArg Complex.re (hτ a)
    rw [hmr] at hm ⊢
    exact Tuple.unique_antitone hm.antitone hanti.antitone
  · rintro rfl
    exact ⟨⟨hanti, fun a => (h _).2⟩, τ₀, fun a => hval _⟩

theorem arrCount : CompanionTheory.RgExh.Fin.ArrCount := by
  classical
  intro n ε χ χ' hχ hχ' h h'
  obtain ⟨μ, hμ⟩ := exists_unique_param χ hχ h
  obtain ⟨μ', hμ'⟩ := exists_unique_param χ' hχ' h'
  let P : Finset (Equiv.Perm (Fin n)) :=
    univ.filter fun s => ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b
  have key : ∀ (ψ : Fin n → ℂ) (ν : Fin n → ℝ),
      (∀ m : Fin n → ℝ, (Formalism.QuantumDeterminants.IsHCParam m ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((m a : ℝ) : ℂ) = ψ (τ a)) ↔ m = ν) →
      ∀ d : Equiv.Perm (Fin n) × (Fin n → ℝ), d ∈ P.image (fun s => (s, ν)) ↔
        (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
          ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = ψ (τ a)) := by
    rintro ψ ν hν ⟨s, m⟩
    constructor
    · intro hd
      obtain ⟨t, ht, e⟩ := mem_image.1 hd
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain ⟨h1, h2⟩ := (hν _).2 rfl
      exact ⟨h1, (mem_filter.1 ht).2, h2⟩
    · rintro ⟨h1, h2, h3⟩
      have e : m = ν := (hν m).1 ⟨h1, h3⟩
      exact mem_image.2 ⟨s, mem_filter.2 ⟨mem_univ _, h2⟩, by simp [e]⟩
  have hinj : ∀ ν : Fin n → ℝ, Function.Injective
      (fun s : Equiv.Perm (Fin n) => (s, ν)) := fun ν a b e => (Prod.mk.inj e).1
  refine ⟨P.image fun s => (s, μ), P.image fun s => (s, μ'), ?_, key χ μ hμ, key χ' μ' hμ'⟩
  rw [card_image_of_injective _ (hinj μ), card_image_of_injective _ (hinj μ')]

end GlobalTheory.CompanionTheory.ArrCount
end
