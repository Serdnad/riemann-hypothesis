module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Survey.CrystallineCharacterRatio

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module TensorProduct
  GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]

end Abstract

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω]

theorem chi_eq_cyc (P : LocPrime l) (j : Ω →+* Om l) (σ : Formalism.ConjugateSelfDual.G E Ω) (g : GQ l)
    (h : ∀ x, g (j x) = j (σ x)) :
    ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : l.Prime := Fact.out
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero l := ⟨hl.ne_zero⟩
  set c : ℤ_[l] := ((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hc

  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (c : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hζ' : IsPrimitiveRoot (j ζ) (l ^ m) := hζ.map_of_injective j.injective
    have hσζ : σ ζ = ζ ^ (PadicInt.toZModPow m c).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G E Ω) Ω σ) ζ hζ.pow_eq_one
    obtain ⟨a, ha1, ha2⟩ := P.χQ_cyc g m (j ζ) hζ'.pow_eq_one
    have hne : j ζ ≠ 0 := hζ'.ne_zero (pow_ne_zero _ hl.ne_zero)
    have hpow : (j ζ) ^ a = (j ζ) ^ (PadicInt.toZModPow m c).val := by
      rw [← ha2, h, hσζ, map_pow]
    have hdvd : ((l ^ m : ℕ) : ℤ) ∣ (a : ℤ) - ((PadicInt.toZModPow m c).val : ℤ) := by
      rw [← hζ'.zpow_eq_one_iff_dvd, zpow_sub₀ hne, zpow_natCast, zpow_natCast, hpow,
        div_self (pow_ne_zero _ hne)]
    have h2 : ‖((a : ℚ_[l]) - (((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - ((PadicInt.toZModPow m c).val : ℤ)) m).mpr
        (by exact_mod_cast hdvd)
      exact_mod_cast this
    have h3 : ‖((((PadicInt.toZModPow m c).val : ℕ) : ℤ_[l]) - c)‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        map_natCast, ZMod.natCast_zmod_val, sub_self]
    have h3' : ‖((((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]) - (c : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_def] at h3
      exact_mod_cast h3
    have hsplit : ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (c : ℚ_[l]) =
        (((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) +
          (((a : ℚ_[l]) - (((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l])) +
            ((((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]) - (c : ℚ_[l]))) := by ring
    rw [hsplit]
    refine (Padic.nonarchimedean _ _).trans (max_le ha1 ((Padic.nonarchimedean _ _).trans (max_le h2 h3')))
  refine sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_))
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hl1
  refine (key m).trans ?_
  rw [zpow_neg, zpow_natCast, ← inv_pow, zero_add]
  exact hm.le

end Bridge

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem locChi_eps (g : Br.G D.nbr i w hw) :
    ((Br.locChi D.nbr i w hw (epsU D.nd i) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        (((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) := by
  have hχ := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw g

  have hc := chi_eq_cyc (D.loc (D.nd.l i)) (D.nbr i w hw).j
    ((ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype ((D.nbr i w hw).e.symm g)) _ (fun x => by
      have := (D.nbr i w hw).e_comm ((D.nbr i w hw).e.symm g) x
      rw [MulEquiv.apply_symm_apply] at this
      exact this)
  unfold Br.locChi Br.chiG Br.PD
  rw [hχ, hc]
  unfold epsU Glob.epsO LocBridge.toLL decS Br.ι
  simp only [RingHom.comp_apply, MonoidHom.comp_apply,
    Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  erw [(D.nbr i w hw).eO_alg]
  rfl

end GlobalTheory.Survey.CrystallineCharacterRatio
end
end

section

noncomputable section

namespace GlobalTheory.WachHeightTest

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.DeltaInvariantLattices PowerSeries

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem q_eq : W.q = ∑ k ∈ Finset.range PD.p, (1 + (letπ : LetA O n)) ^ k := by
  funext i
  have h := W.q₀_def
  have h2 : (PowerSeries.X : PowerSeries O) * ∑ k ∈ Finset.range PD.p, (1 + PowerSeries.X) ^ k =
      (1 + PowerSeries.X) ^ PD.p - 1 := by
    have := mul_geom_sum (1 + (PowerSeries.X : PowerSeries O)) PD.p
    simpa using this
  have h3 := PowerSeries.X_mul_cancel (h.trans h2.symm)
  simp [LocWach.q, h3, letπ, Finset.sum_apply]

theorem φ_one_add : W.φA (1 + letπ) = (1 + (letπ : LetA O n)) ^ PD.p := by
  rw [map_add (f := _), map_one, W.φA_π]
  funext i
  have h := W.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q, h]
  ring

theorem φpow_one_add (j : ℕ) : (W.φA ^ j) (1 + letπ) = (1 + (letπ : LetA O n)) ^ (PD.p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φ_one_add, ← pow_mul, pow_succ']

theorem Q_eq : W.Q = ∑ k ∈ Finset.range PD.p, ((1 + (letπ : LetA O n)) ^ (PD.p ^ (W.s - 1))) ^ k := by

  rw [LocWach.Q, q_eq, map_sum]
  simp only [map_pow, φpow_one_add]

theorem value_Q (i : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    PowerSeries.constantCoeff (W.lev i ζ W.Q) =
      ∑ k ∈ Finset.range PD.p, (ζ ^ (PD.p ^ (W.s - 1))) ^ k := by
  obtain ⟨E, hE, -, h⟩ := W.lev_π i ζ hζ
  rw [Q_eq]

  simp only [map_sum, map_pow, map_add (f := _), map_one]
  have : 1 + PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ := by
    have := congrArg PowerSeries.constantCoeff h
    simpa [hE] using this
  rw [this]

include W in
theorem p_ne_zero : ((PD.p : ℕ) : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_one this

theorem qRoot_iff (i : ZMod n) (ζ : LL) :
    QRoot W i ζ ↔ (∃ c : O, algebraMap O LL c = ζ) ∧ IsPrimitiveRoot ζ (PD.p ^ W.s) := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have hs : W.s = W.s - 1 + 1 := by have := W.s_pos; omega
  constructor
  · rintro ⟨hc, ⟨m, hm⟩, h0⟩
    refine ⟨hc, ?_⟩
    have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow PD.hp).1 (orderOf_dvd_of_pow_eq_one hm)
      exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩
    rw [value_Q W i ζ hprim] at h0
    have h1 : ¬ ζ ^ PD.p ^ (W.s - 1) = 1 := by
      intro h
      rw [h] at h0
      apply p_ne_zero W
      simpa using h0
    have h2 : ζ ^ PD.p ^ (W.s - 1 + 1) = 1 := by
      have := geom_sum_mul (ζ ^ PD.p ^ (W.s - 1)) PD.p
      rw [h0, zero_mul] at this
      rw [pow_succ, pow_mul]
      exact (sub_eq_zero.1 this.symm)
    have := orderOf_eq_prime_pow h1 h2
    rw [hs, ← this]
    exact IsPrimitiveRoot.orderOf ζ
  · rintro ⟨hc, hp⟩
    refine ⟨hc, ⟨W.s, hp.pow_eq_one⟩, ?_⟩
    rw [value_Q W i ζ ⟨_, hp⟩]
    have h1 : ζ ^ PD.p ^ (W.s - 1) ≠ 1 :=
      hp.pow_ne_one_of_pos_of_lt (pow_pos PD.hp.pos _).ne'
        (Nat.pow_lt_pow_right PD.hp.one_lt (by omega))
    have := geom_sum_mul (ζ ^ PD.p ^ (W.s - 1)) PD.p
    rw [← pow_mul, ← pow_succ, ← hs, hp.pow_eq_one, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h1)

end Local

end GlobalTheory.WachHeightTest
end
end
