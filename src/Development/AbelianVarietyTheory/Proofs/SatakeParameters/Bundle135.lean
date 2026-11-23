module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle077
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle126
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle127
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLog

theorem exists_full_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
    (∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB)) →
    ∃ x y : P.R.B, x ≠ 0 ∧ ∀ g : GQ l, x * P.actQ g y - P.actQ g x * y = x * P.actQ g x * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P _ K b b' hb h
  haveI := K.2
  haveI : Finite (GQ l ⧸ GK K) := Subgroup.quotient_finite_of_isOpen _ K.1.fixingSubgroup_isOpen
  haveI := Fintype.ofFinite (GQ l ⧸ GK K)
  let ι : P.R.B →+* FractionRing P.R.B := algebraMap P.R.B (FractionRing P.R.B)
  have hι : Function.Injective ι := IsFractionRing.injective P.R.B (FractionRing P.R.B)
  let e : GQ l → FractionRing P.R.B ≃+* FractionRing P.R.B := fun g =>
    IsFractionRing.ringEquivOfRingEquiv (A := P.R.B) (B := P.R.B) (P.actQ g).toRingEquiv
  have he : ∀ g z, e g (ι z) = ι (P.actQ g z) := fun g z =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
  have hmul : ∀ s g z, e s (e g z) = e (s * g) z := by
    intro s g
    have : (e s).toRingHom.comp (e g).toRingHom = (e (s * g)).toRingHom := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors P.R.B)
      ext z
      show e s (e g (ι z)) = e (s * g) (ι z)
      rw [he, he, he, map_mul, AlgEquiv.mul_apply]
    intro z
    exact RingHom.congr_fun this z
  have hne : ∀ g (z : P.R.B), z ≠ 0 → ι (P.actQ g z) ≠ 0 := fun g z hz =>
    (map_ne_zero_iff ι hι).2 ((map_ne_zero_iff _ (P.actQ g).injective).2 hz)
  let T : GQ l → FractionRing P.R.B := fun g => ι ((kummer P g : ℚ_[l]) • P.tB)
  have hT : ∀ s g, e s (T g) = T (s * g) - T s := by
    intro s g
    simp only [T, he, map_smul, localPrime_galoisAction_periodT, kummer_mul, smul_smul, add_smul, map_add (f := _)]
    rw [mul_comm]; abel
  let f : FractionRing P.R.B := ι b' / ι b
  have hb0 : ι b ≠ 0 := (map_ne_zero_iff ι hι).2 hb
  have hf : ∀ g ∈ GK K, e g f - f = T g := by
    intro g hg
    have h1 := congrArg ι (h g hg)
    simp only [map_sub, map_mul] at h1
    have h2 := hne g b hb
    simp only [f, map_div₀, he]
    field_simp
    linear_combination h1
  let Fn : GQ l → FractionRing P.R.B := fun g => e g f - T g
  have h1 : ∀ s g, e s (Fn g) = Fn (s * g) + T s := by
    intro s g
    simp only [Fn, map_sub, hmul, hT]
    abel
  have h2 : ∀ g (k : ↥(GK K)), Fn (g * k) = Fn g := by
    intro g k
    have e1 : Fn k = f := by simp only [Fn, ← hf k k.2]; abel
    have := h1 g k
    rw [e1] at this
    simp only [Fn] at this ⊢
    linear_combination -this
  have h3 : ∀ g, Fn (QuotientGroup.mk g : GQ l ⧸ GK K).out = Fn g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    rw [hk, h2]
  have hnB : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : P.R.B) ≠ 0 := by
    haveI := nontrivial_B P
    rw [← map_natCast (algebraMap ℚ_[l] P.R.B)]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℚ_[l] P.R.B)).2
      (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hn : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero_iff ι hι).2 hnB
  let fa : FractionRing P.R.B := ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B)⁻¹ * ∑ q : GQ l ⧸ GK K, Fn q.out
  have hfa : ∀ s, e s fa - fa = T s := by
    intro s
    have h4 : ∑ q : GQ l ⧸ GK K, Fn (s * q.out) = ∑ q : GQ l ⧸ GK K, Fn q.out :=
      Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => by
        rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, h3, smul_eq_mul]

    simp only [fa, map_mul, map_inv₀, map_natCast, map_sum, h1]
    rw [Finset.sum_add_distrib, h4, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  obtain ⟨y, x, hx, hxy⟩ := IsFractionRing.div_surjective (A := P.R.B) fa
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  refine ⟨x, y, hx0, fun g => ?_⟩
  have hxy' : ι y / ι x = fa := hxy
  have k := hfa g
  rw [← hxy', map_div₀, he, he] at k
  have k1 := hne g x hx0
  have k2 : ι x ≠ 0 := (map_ne_zero_iff ι hι).2 hx0
  apply hι
  simp only [map_sub, map_mul]
  field_simp at k
  linear_combination k

end GlobalTheory.Pst.NoLog
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem wHom_ext (p : ℕ) [Fact p.Prime] (f g : Formalism.L2.G.Pend.WW p →+* ℂ_[p])
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (ht : ∀ y, f (WittVector.teichmuller p y) = g (WittVector.teichmuller p y)) (x : Formalism.L2.G.Pend.WW p) :
    f x = g x := by
  refine Formalism.L2.G.Pend.eq_of_close p fun N => ?_
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  set S := ∑ i ∈ Finset.Iic N, (WittVector.teichmuller p
        (((_root_.frobeniusEquiv (Formalism.L2.G.Pend.kb p) p).symm ^ i) (x.coeff i)) * (p : Formalism.L2.G.Pend.WW p) ^ i) with hS
  have hfS : f S = g S := by

    rw [hS, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, ht]
  have hx : x = S + (p : Formalism.L2.G.Pend.WW p) ^ (N + 1) * c := by rw [← hc]; ring
  have hpC : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := Formalism.L2.G.Pend.norm_p_C p
  have e : f x - g x = (p : ℂ_[p]) ^ (N + 1) * (f c - g c) := by
    rw [hx, map_add (f := _), map_add (f := _), hfS, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]; ring
  rw [e, norm_mul, norm_pow, hpC]
  have h1 : ‖f c - g c‖ ≤ 1 := Formalism.L2.G.Pend.nsub p (hf c) (hg c)
  calc ((p : ℝ)⁻¹) ^ (N + 1) * ‖f c - g c‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((p : ℝ)⁻¹) ^ N * (p : ℝ)⁻¹ := by rw [mul_one, pow_succ]
    _ ≤ ((p : ℝ)⁻¹) ^ N * 1 := mul_le_mul_of_nonneg_left (Formalism.L2.G.Pend.r_lt_one p).le (by positivity)
    _ = ((p : ℝ)⁻¹) ^ N := mul_one _

theorem wToC_frob (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (hζ : ∀ (ζ : ℂ_[p]) (n : ℕ), 0 < n → Nat.Coprime n p → ζ ^ n = 1 → σ ζ = ζ ^ p) (x : FormalGroupSystem.WW p) :
    σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x) := by
  have := wHom_ext p (σ.comp (Formalism.L2.G.Pend.wToC p)) ((Formalism.L2.G.Pend.wToC p).comp (sigW p))
    (fun y => by rw [RingHom.comp_apply, hσ]; exact Formalism.L2.G.Pend.norm_wToC_le p y)
    (fun y => Formalism.L2.G.Pend.norm_wToC_le p _) (fun y => ?_) x
  · exact this
  · rw [RingHom.comp_apply, RingHom.comp_apply]
    have hs : sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p) := by
      show WittVector.frobenius (WittVector.teichmuller p y) = _
      rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]
    rw [hs, map_pow (WittVector.teichmuller p), map_pow (Formalism.L2.G.Pend.wToC p)]
    by_cases hy : y = 0
    · subst hy
      rw [WittVector.teichmuller_zero, map_zero, map_zero, zero_pow (Fact.out : p.Prime).ne_zero]
    · obtain ⟨m, hm, hc, h1⟩ := Formalism.L2.G.Pend.exists_coprime_pow_eq_one p hy
      exact hζ _ m hm hc (by rw [← map_pow, ← map_pow, h1, map_one, map_one])

theorem exists_isFrob_wToC : ∀ (p : ℕ) [Fact p.Prime], ∃ σ : ℂ_[p] →+* ℂ_[p], GlobalTheory.ThBe0.IsFrob σ ∧
    ∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x) := by
  intro p _
  obtain ⟨g, hg⟩ := GlobalTheory.ThBe0.exists_gal_pow p
  have hζ : ∀ (ζ : ℂ_[p]) (n : ℕ), 0 < n → Nat.Coprime n p → ζ ^ n = 1 → Formalism.Per.σC g ζ = ζ ^ p := by
    intro ζ n hn hnl h
    obtain ⟨a, rfl, ha⟩ := GlobalTheory.ThBe0.exists_coe_eq_of_pow_eq_one p ζ n hn h
    rw [GlobalTheory.RingBasics.σC_coe, hg a n hnl ha]
    exact map_pow (algebraMap (PadicAlgCl p) ℂ_[p]) a p
  exact ⟨Formalism.Per.σC g, GlobalTheory.ThBe0.isFrob_of_rootOfUnity _ (GlobalTheory.RingBasics.norm_σC g) hζ,
    wToC_frob p _ (GlobalTheory.RingBasics.norm_σC g) hζ⟩

end GlobalTheory.TwU
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.BeRead

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

local notation "φ" => Formalism.L2.G.Pend.k0ToC p

def lK {ι : Type} (p : ℕ) [Fact p.Prime] (i : ι) : MvPowerSeries ι (FormalGroupSystem.K0 p) :=
  PowerSeries.subst (X i : MvPowerSeries ι (FormalGroupSystem.K0 p)) (FormalGroupSystem.logF p)

theorem cc_logK : PowerSeries.constantCoeff (FormalGroupSystem.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold FormalGroupSystem.logF
  rw [PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg]
  exact (pow_pos hp.out.pos _).ne

theorem cc_lK {ι : Type} (i : ι) : constantCoeff (lK (ι := ι) p i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ cc_logK

theorem hasSubst_lK {ι : Type} [Finite ι] : HasSubst (lK (ι := ι) p) :=
  hasSubst_of_constantCoeff_zero cc_lK

theorem map_lK {ι : Type} (i : ι) : map φ (lK (ι := ι) p i) = GlobalTheory.ThBe0.lg i := by
  unfold lK GlobalTheory.ThBe0.lg
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)), map_X,
    Formalism.L2.G.Pend.logF_map]

theorem inParam_eq {ι : Type} (f : MvPowerSeries ι (FormalGroupSystem.K0 p)) : inParam p f = subst (lK p) f := rfl

theorem map_expS {ι : Type} (f : MvPowerSeries ι (FormalGroupSystem.K0 p)) :
    map φ (expS p f) = Formalism.MainNotions.TaylorLogMetric.expMv (map φ f) := by
  ext n
  rw [coeff_map]
  show φ (expS p f n) = Formalism.MainNotions.TaylorLogMetric.expMv (map φ f) n
  unfold expS Formalism.MainNotions.TaylorLogMetric.expMv

  rw [map_sum]
  have hd : n.degree = n.sum fun _ k => k := rfl
  rw [hd]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, coeff_map, map_mul, map_inv₀, map_natCast, div_eq_inv_mul]

theorem simeqW_of_simeq {ι : Type} [Finite ι] {f g : MvPowerSeries ι (FormalGroupSystem.K0 p)} (h : FormalGroupSystem.Simeq p f g) :
    Formalism.MainNotions.GL3Theta.SimeqW (map φ (inParam p f)) (map φ (inParam p g)) := by
  obtain ⟨h0, w, -, hw⟩ := h
  have hs : map φ (inParam p f) - map φ (inParam p g) = map φ (inParam p (f - g)) := by
    rw [inParam_eq, inParam_eq, inParam_eq, subst_sub hasSubst_lK, map_sub]
  have hc : constantCoeff (inParam p (f - g)) = 0 :=
    constantCoeff_subst_eq_zero hasSubst_lK cc_lK h0
  unfold Formalism.MainNotions.GL3Theta.SimeqW
  rw [hs]
  refine ⟨?_, ?_⟩
  · have := congrArg (φ) hc
    rw [map_zero] at this
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
    exact this
  · rw [← map_expS, hw]
    refine (Formalism.L2.G.Pend.integralW_iff _).2 ⟨1 + w, ?_⟩
    ext n
    simp [coeff_map, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]

def mI {ι : Type} (f : MvPowerSeries ι (FormalGroupSystem.K0 p)) : MvPowerSeries ι ℂ_[p] := map φ (inParam p f)

theorem mI_X {ι : Type} [Finite ι] (i : ι) : mI (X i : MvPowerSeries ι (FormalGroupSystem.K0 p)) = GlobalTheory.ThBe0.lg i := by
  unfold mI
  rw [inParam_eq, subst_X hasSubst_lK, map_lK]

theorem mI_add {ι : Type} [Finite ι] (f g : MvPowerSeries ι (FormalGroupSystem.K0 p)) : mI (f + g) = mI f + mI g := by
  unfold mI
  rw [inParam_eq, inParam_eq, inParam_eq, subst_add hasSubst_lK, map_add (f := _)]

theorem mI_sub {ι : Type} [Finite ι] (f g : MvPowerSeries ι (FormalGroupSystem.K0 p)) : mI (f - g) = mI f - mI g := by
  unfold mI
  rw [inParam_eq, inParam_eq, inParam_eq, subst_sub hasSubst_lK, map_sub]

theorem mI_C_mul {ι : Type} [Finite ι] (a : FormalGroupSystem.K0 p) (f : MvPowerSeries ι (FormalGroupSystem.K0 p)) :
    mI (C a * f) = C (φ a) * mI f := by
  unfold mI
  rw [inParam_eq, inParam_eq, ← smul_eq_C_mul, subst_smul hasSubst_lK, smul_eq_C_mul, map_mul, map_C]

theorem mI_zero {ι : Type} [Finite ι] : mI (0 : MvPowerSeries ι (FormalGroupSystem.K0 p)) = 0 := by
  have := mI_sub (0 : MvPowerSeries ι (FormalGroupSystem.K0 p)) 0
  rwa [sub_zero, sub_self] at this

theorem frobenius_map_subst_pair {κ : Type} [Finite κ] (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)) {x y : MvPowerSeries κ (FormalGroupSystem.K0 p)}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    mI (sub2 p be x y) = GlobalTheory.ThBe0.at2 (map φ be) (mI x) (mI y) := by
  have ha : HasSubst (![x, y] : Fin 2 → MvPowerSeries κ (FormalGroupSystem.K0 p)) :=
    hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hx, hy]
  have hb : HasSubst (fun i : Fin 2 => subst (lK (ι := κ) p) ((![x, y] : Fin 2 → MvPowerSeries κ (FormalGroupSystem.K0 p)) i)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hasSubst_lK cc_lK (by fin_cases i <;> simp [hx, hy])
  unfold mI sub2 GlobalTheory.ThBe0.at2
  rw [inParam_eq, subst_comp_subst_apply ha hasSubst_lK, map_subst hb]
  congr 1
  funext i
  fin_cases i <;> simp [inParam_eq]

theorem simeqW_add {κ : Type} {a b c : MvPowerSeries κ ℂ_[p]} (h : Formalism.MainNotions.GL3Theta.SimeqW (a - b - c) 0) :
    Formalism.MainNotions.GL3Theta.SimeqW a (b + c) := by
  have e : a - (b + c) = a - b - c - 0 := by ring
  unfold Formalism.MainNotions.GL3Theta.SimeqW at h ⊢
  rw [e]
  exact h

theorem isBe0_map : ∀ (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), GlobalTheory.ThBe0.IsFrob σ →
    (∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x)) →
    ∀ be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p), BeProp p be →
      GlobalTheory.ThBe0.IsBe0 σ (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) := by
  intro p _ σ _ hs be hbe
  have cX : ∀ {κ : Type} (i : κ), constantCoeff (X i : MvPowerSeries κ (FormalGroupSystem.K0 p)) = 0 := fun i => constantCoeff_X i
  refine ⟨(Formalism.L2.G.Pend.coefWf_iff _).2 ⟨be, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have h0 : coeff n be ≠ 0 := by
      intro h
      apply hn
      rw [coeff_map, h, map_zero]
    obtain ⟨h1, h2⟩ := hbe.ab n h0
    exact ⟨by omega, by omega⟩
  · have h := simeqW_of_simeq hbe.add1
    apply simeqW_add
    change Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h
    rw [mI_zero, mI_sub, mI_sub, frobenius_map_subst_pair be (by simp) (cX 2), frobenius_map_subst_pair be (cX 0) (cX 2), frobenius_map_subst_pair be (cX 1) (cX 2),
      mI_add, mI_X, mI_X, mI_X] at h
    exact h
  · have h := simeqW_of_simeq hbe.add2
    apply simeqW_add
    change Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h
    rw [mI_zero, mI_sub, mI_sub, frobenius_map_subst_pair be (cX 0) (by simp), frobenius_map_subst_pair be (cX 0) (cX 1), frobenius_map_subst_pair be (cX 0) (cX 2),
      mI_add, mI_X, mI_X, mI_X] at h
    exact h
  · intro α hα h2
    obtain ⟨x, rfl⟩ := (Formalism.L2.G.Pend.mem_Wp_iff p α).1 hα
    have hx : (sigW p)^[2] x = x := by
      apply Formalism.L2.G.Pend.wToC_injective p
      rw [← h2, hs x, hs (sigW p x)]
      rfl
    have h := simeqW_of_simeq (hbe.conj x hx)
    change Formalism.MainNotions.GL3Theta.SimeqW (mI _) (mI _) at h
    rw [frobenius_map_subst_pair be (by simp) (cX 1), frobenius_map_subst_pair be (cX 0) (by simp), mI_C_mul, mI_C_mul, mI_X, mI_X,
      Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, ← hs x] at h
    exact h

end GlobalTheory.BeRead

end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordBox : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := funext fun a => hg a
  rw [hgl]
  have hb := GlobalTheory.HTW.bHat_window L C hR
  refine ⟨?_, ?_, hb.1, hb.2⟩
  · intro a
    obtain ⟨-, hM, hh, -⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    rw [hM, hh]
    exact GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height L C j ε (g 0) ψ hR a
  · intro a hnt
    obtain ⟨hsz, -, -, hth⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    obtain ⟨s, hs1, hs2, -, hs3⟩ := GlobalTheory.T.twistedDualOrbitPageWord_nonThick_size_bounds L C j ε (g 0) ψ hR a (fun h => hnt (hth.2 h))
    refine ⟨s, hs1, le_trans hs2 (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).1, ?_⟩
    have hc : (((recWord L j ε (letter (g 0) ψ)).sz a : ℕ) : ℝ) = (((pageWord L j ε (g 0) ψ).sz a : ℤ) : ℝ) := by
      rw [← hsz]; push_cast; rfl
    rw [hc]; exact hs3

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem alternates_parity {n : ℕ} [NeZero n] {up : ZMod n → Bool} (h : Alternates up) :
    ∃ d : ℕ, ∀ a : ZMod n, up a = decide ((a.val + d) % 2 = 1) := by
  refine ⟨if up 0 then 1 else 0, fun a => ?_⟩
  have key : ∀ k : ℕ, up (k : ZMod n) = decide ((k + (if up 0 then 1 else 0)) % 2 = 1) := by
    intro k
    induction k with
    | zero => cases h0 : up 0 <;> simp [h0]
    | succ k ih =>
      have e : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by push_cast; rfl
      rw [e, h, ih]
      generalize (if up 0 = true then 1 else 0) = d
      by_cases hk : (k + d) % 2 = 1
      · have : ¬ (k + 1 + d) % 2 = 1 := by omega
        simp [hk, this]
      · have : (k + 1 + d) % 2 = 1 := by omega
        simp [hk, this]
  simpa using key a.val

theorem recWord_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 11 ≤ l → ψ.1.2 = -1 →
    WordsNT (recWord L j ε g) ∨ ∃ d, WordsAT l (recWord L j ε g) d := by
  intro D L C j ε n g ψ l hR hO hl hψ
  obtain ⟨rfl, hg⟩ := hO
  obtain ⟨τ, rfl⟩ : ∃ τ, g = letter τ ψ := ⟨g 0, funext hg⟩
  clear hg
  have hT := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR
  obtain ⟨hBox, hcase⟩ := GlobalTheory.T.twistedDualPageWord_inert_prime_dichotomy L C j ε τ ψ l hR hl hψ
  have hsz : ∀ a, (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a :=
    fun a => (hT a).1
  have hη : ∀ a, etaHat L < (recWord L j ε (letter τ ψ)).sz a := fun a => by
    have h6 : ((etaHat L : ℕ) : ℤ) < (pageWord L j ε τ ψ).sz a := hBox.2.2.2.2.2 a
    rw [← hsz a] at h6
    exact_mod_cast h6
  have hSmall : Small (recWord L j ε (letter τ ψ)) :=
    ⟨hBox.1, hBox.2.1, hBox.2.2.1, hBox.2.2.2.1, hBox.2.2.2.2.1, hη⟩
  rcases hcase with ⟨halt, ⟨a, ha⟩, hthree⟩ | ⟨-, ⟨hev, halt, hbig⟩, -⟩
  · left
    refine ⟨hSmall, halt, ⟨a, fun h => ha ((hT a).2.2.2.1 h)⟩, fun i h => hthree i ?_⟩
    exact ⟨(hT _).2.2.2.1 h.1, (hT _).2.2.2.1 h.2.1, (hT _).2.2.2.1 h.2.2⟩
  · right
    haveI : NeZero (orderOf ψ) := ⟨(orderOf_pos ψ).ne'⟩
    obtain ⟨d, hd⟩ := alternates_parity (up := (recWord L j ε (letter τ ψ)).up) halt
    refine ⟨d, hev, hd, hSmall, fun a => ?_, fun M hM a => ?_⟩
    · have hmax : max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L) =
          (recWord L j ε (letter τ ψ)).sz a + sHat L := max_eq_right (by have := hη a; omega)
      change (if (!pos ε (letter τ ψ a)) = true then etaHat L else
          max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L)) = _ ∧
        (if (!pos ε (letter τ ψ a)) = true then
          max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L) else etaHat L) = _
      rw [hmax]
      exact ⟨rfl, rfl⟩
    · have hM' : IsGreatest (Set.range (pageWord L j ε τ ψ).sz) (M : ℤ) := by
        obtain ⟨⟨b, hb⟩, hub⟩ := hM
        refine ⟨⟨b, by rw [← hsz b, hb]⟩, ?_⟩
        rintro _ ⟨c, rfl⟩
        rw [← hsz c]
        exact_mod_cast hub ⟨c, rfl⟩
      obtain ⟨-, h2, h3⟩ := hbig M hM' a
      rw [← hsz a] at h2 h3
      push_cast at h2 h3
      exact ⟨h2, h3⟩

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.existsUnique_embeddingReadsGaloisElement : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  first | exact @GlobalTheory.HTW.Rec.existsUnique_reads | exact GlobalTheory.HTW.Rec.existsUnique_reads | (intros; apply GlobalTheory.HTW.Rec.existsUnique_reads <;> assumption)
end
