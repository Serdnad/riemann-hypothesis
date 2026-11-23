module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle641
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle324
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle130
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinEquivApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle657
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle658
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValApplySubLtOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LamTie.TrueList

section Local

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair GlobalTheory.LamTie.ConjLevel

variable {E : Type} [Field E] [NumberField E]

theorem exists_unit_conj [IsCMField E] {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} (hs : Splits v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hP' : Over P' v) (hne : P ≠ P') (u : (P'.adicCompletion E)ˣ)
    (hu : Valued.v (u : P'.adicCompletion E) = 1) :
    ∃ u' : (P.adicCompletion E)ˣ, Valued.v (u' : P.adicCompletion E) = 1 ∧ χ.loc P u' * χ.loc P' u = 1 := by
  obtain ⟨h2, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  have hmul := loc_mul_loc hF hP hP' hne (h2 P P' hP hP' hne)
  obtain ⟨m, hm⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P'
  obtain ⟨a, h4⟩ := exists_cong hs hP' (m + 1) u hu.le
  have hlt : WithZero.exp (-((m + 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hlt1 : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (iota a P') = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu ▸ h4.trans_lt hlt), hu]
  have hav : a ∉ v.asIdeal ^ 1 := fun h => (h5 ▸ val_iota_le_of_mem hP' 1 h).not_gt hlt1
  have ha0 : a ≠ 0 := fun h => hav (h ▸ zero_mem _)
  have hunit : Valued.v (iota a P) = 1 := by
    have := eq_exp_of_le (m := 0) (by simpa using val_iota_le_one P a) fun h3 => hav (by
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      simpa using h3)
    simpa using this
  have h8 : χ.loc P' (locF P' a ha0 / u) = 1 := by
    refine hm _ ?_ ?_
    · show Valued.v ((locF P' a ha0 / u : (P'.adicCompletion E)ˣ) : P'.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, coe_locF, h5, hu, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu, div_one, coe_locF]
      exact h4.trans (WithZero.exp_le_exp.2 (by omega))
  rw [map_div, div_eq_one] at h8
  exact ⟨locF P a ha0, hunit, h8 ▸ hmul a ha0⟩

def TeichTriv (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : (v.adicCompletion E)ˣ, x ^ (Ideal.absNorm v.asIdeal - 1) = 1 → χ.loc v x = 1

theorem teichTriv_of_split [IsCMField E] {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} (hs : Splits v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hP' : Over P' v) {p : ℕ} (hp : p.Prime)
    (hN : Ideal.absNorm P.asIdeal = p) (hN' : Ideal.absNorm P'.asIdeal = p) (h : TeichTriv χ P) : TeichTriv χ P' := by
  by_cases hne : P = P'
  · exact hne ▸ h
  intro x hx
  rw [hN'] at hx
  have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hu : Valued.v (x : P'.adicCompletion E) = 1 := by
    have := congrArg (fun y : (P'.adicCompletion E)ˣ => Valued.v (y : P'.adicCompletion E)) hx
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
    exact (pow_eq_one_iff_left h1).1 this
  obtain ⟨u, hu', e⟩ := exists_unit_conj hF hs hP hP' hne x hu
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.WildChar.orders_on_units _ χ P).2 h u hu'
  have e1 : χ.loc P' x ^ (p ^ n) = 1 := by
    have := congrArg (· ^ (p ^ n)) e
    rw [hN] at hn
    simpa only [mul_pow, hn, one_mul, one_pow] using this
  have e2 : χ.loc P' x ^ (p - 1) = 1 := by rw [← map_pow, hx, map_one]
  have hc : Nat.Coprime (p ^ n) (p - 1) := Nat.Coprime.pow_left _ (by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    simp)
  have := pow_gcd_eq_one.2 ⟨e1, e2⟩
  rwa [hc, pow_one] at this

end Local

section Global

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_two_readings {L : Type} [Field L] (φ : L →+* ℂ) :
    ∃ (K : Subfield ℂ) (f f' : K →+* L), (∀ x, φ (f x) = K.subtype x) ∧ (∀ x, φ (f' x) = starRingEnd ℂ (K.subtype x)) ∧
      ∀ z, z ∈ φ.fieldRange → starRingEnd ℂ z ∈ φ.fieldRange → z ∈ K := by
  let K : Subfield ℂ := φ.fieldRange ⊓ φ.fieldRange.comap (starRingEnd ℂ)
  let e := φ.rangeRestrictFieldEquiv
  have he : ∀ y, φ (e.symm y) = y := fun y => congrArg Subtype.val (e.apply_symm_apply y)
  exact ⟨K, e.symm.toRingHom.comp (K.subtype.codRestrict φ.fieldRange fun x => x.2.1),
    e.symm.toRingHom.comp (((starRingEnd ℂ).comp K.subtype).codRestrict φ.fieldRange fun x => x.2.2),
    fun x => he _, fun x => he _, fun z h h' => ⟨h, h'⟩⟩

theorem valuesIn_of_unitary {E L : Type} [Field E] [NumberField E] [Field L] {φ : L →+* ℂ} {K : Subfield ℂ}
    (hK : ∀ z, z ∈ φ.fieldRange → starRingEnd ℂ z ∈ φ.fieldRange → z ∈ K) {χ : Formalism.L2.Host.HChar E} (hu : χ.IsUnitary)
    (h : χ.ValuesIn 0 φ) : χ.ValuesIn 0 K.subtype := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  have h1 : ‖χ.valTw 0 v‖ = 1 := by
    simp only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
    exact hu _
  exact ⟨⟨_, hK _ ⟨y, hy⟩ ⟨y⁻¹, by rw [map_inv₀, hy, Complex.inv_eq_conj h1]⟩⟩, rfl⟩

theorem valuesIn_of_isGal {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    {κ : FractionRing O →+* Qbar l} {ι : Qbar l ≃+* ℂ} {χ : Formalism.L2.Host.HChar E} {r : G E Ω →* Oˣ} (h : IsGal art κ ι χ 0 r) :
    χ.ValuesIn 0 (ι.toRingHom.comp κ) := fun v hv => by
  have e := h.frob ha (Or.inr rfl) hv (isPlaceOver_placeOf Ω v) (isFrob_frobOf Ω v)
  refine ⟨(algebraMap O _ (r (frobOf Ω v) : Oˣ))⁻¹, ?_⟩
  rw [map_inv₀]
  simp only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  exact inv_eq_iff_eq_inv.2 e

variable {D : D7} {N : NData D.R D.host D.what₂}

theorem chi_unr {Z : LamDat D} (hZ : Z.Ok) (a : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (h : ¬ (below P).asIdeal ∣ cond0 D.host Z.w0) : (Z.chi a).UnrAt P := by
  refine (hZ.aux a).unr P (fun h4 => h ?_) fun e => h (e ▸ dvd_mul_left _ _)
  refine (dvd_pow ?_ two_ne_zero).mul_right _
  rw [Ideal.dvd_span_singleton, ExpCond.mem_below]
  push_cast
  rcases h4 with ⟨k, hk⟩ | hk | hk
  · fin_cases k
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hk))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hk))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hk)
  · exact Ideal.mul_mem_left _ _ hk

theorem chi_teich {Z : LamDat D} (hZ : Z.Ok) (a : Fin D.R.m) {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : OverP D.host D.host.pde w ∨ OverP D.host D.host.pde' w) (e : below w' = below w) (h : TeichTriv (Z.chi a) w') :
    TeichTriv (Z.chi a) w := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨p, hp, hw⟩ : ∃ p ∈ [D.host.g 0, D.host.g 1, D.host.pde, D.host.pde', Z.q0], (p : 𝓞 D.host.E) ∈ w.asIdeal :=
    hw.elim (fun h => ⟨_, by simp, h⟩) fun h => ⟨_, by simp, h⟩
  obtain ⟨h1, -, h2, h3⟩ := hZ.places.splits p hp
  have hw' : (p : 𝓞 D.host.E) ∈ w'.asIdeal := by rwa [← ExpCond.mem_below, e, ExpCond.mem_below]
  exact teichTriv_of_split (hZ.aux a).triv (SplitBelow.splits_below_of_absNorm _ p h1 h2 h3 w hw) (e ▸ over_below w')
    (over_below w) h1 (h3 w' hw') (h3 w hw) h

theorem exists_reading (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (e : FractionRing (X.O0 i) →+* Qbar (X.l i))
    (ι : Qbar (X.l i) ≃+* ℂ) (he : ∀ z : ℤ_[X.l i], e (algebraMap (X.O0 i) _ (algebraMap ℤ_[X.l i] (X.O0 i) z)) =
      algebraMap ℚ_[X.l i] (Qbar (X.l i)) (z : ℚ_[X.l i])) :
    ∃ ι' : ℂ →+* Kbar X i, ∀ b x, atSide X b ι' (sideIso ι b (e x)) = toBar X i x := by
  let _ : Algebra (FractionRing (X.O0 i)) (Qbar (X.l i)) := e.toAlgebra
  let _ : Algebra (FractionRing (X.O0 i)) (Kbar X i) := (toBar X i).toAlgebra
  have : Algebra.IsAlgebraic (FractionRing (X.O0 i)) (Qbar (X.l i)) := ⟨fun x => by
    have h1 : IsAlgebraic ℤ_[X.l i] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[X.l i] ℚ_[X.l i] _).2 (Algebra.IsAlgebraic.isAlgebraic x)
    refine h1.ringHom_of_comp_eq ((algebraMap (X.O0 i) _).comp (algebraMap ℤ_[X.l i] (X.O0 i))) (RingHom.id _)
      (fun a b hab => ?_) (RingHom.ext he)
    have := congrArg e hab
    rw [RingHom.comp_apply, RingHom.comp_apply, he, he] at this
    exact Subtype.ext ((algebraMap ℚ_[X.l i] (Qbar (X.l i))).injective this)⟩
  let J : Qbar (X.l i) →ₐ[FractionRing (X.O0 i)] Kbar X i := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hJ : ∀ x, J (e x) = toBar X i x := J.commutes
  refine ⟨J.toRingHom.comp ι.symm.toRingHom, fun b x => ?_⟩
  rw [← hJ]
  cases b
  · show J (ι.symm (starRingEnd ℂ (starRingEnd ℂ (ι _)))) = _
    rw [Complex.conj_conj, ι.symm_apply_apply]
  · exact congrArg J (ι.symm_apply_apply _)

theorem xv_mul_val (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) {e : FractionRing (X.O0 i) →+* Qbar (X.l i)}
    {ι : Qbar (X.l i) ≃+* ℂ} {ι' : ℂ →+* Kbar X i} (hι : ∀ x, ι' (ι (e x)) = toBar X i x)
    {art : Ideles D.host.E →* Gab D.host.E N.Om} (ha : IsGlobalArtin art) {χ : Formalism.L2.Host.HChar D.host.E}
    {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (X.O0 i)ˣ} (hr : IsGal art e ι χ n r) {lam : X.abelian₂ i}
    (hG : X.lamG i lam = (Units.map (algebraMap (X.O0 i) (X.O i)).toMonoidHom).comp r)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∉ X.S0 i) (hu : χ.UnrAt P) :
    algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι' ((χ.val P : ℂˣ) : ℂ) = 1 := by
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 P)
  have h3 := congrArg ι' (hr.frob ha (Or.inl fun h => hP (X.twistExcludedPlaces_contains_residueChar i h)) hu (N.plOm.2 P) hσ)
  rw [map_inv₀, toQ, RingHom.comp_apply, hι, toBar_algebraMap] at h3
  rw [X.Xv_def i lam P hP σ hσ, hG]
  exact (congrArg (· * _) h3).trans (inv_mul_cancel₀ ((map_ne_zero _).2 (Units.ne_zero _)))

abbrev Idx (R : Ranks) : Type := Fin R.m × Fin R.m × {s : ℕ // 1 ≤ s ∧ s ≤ BlochKatoReduction.Gen.NFun R + 1} × Bool

instance (n : ℕ) : Fintype {s : ℕ // 1 ≤ s ∧ s ≤ n} := Fintype.subtype (Finset.Icc 1 n) fun _ => Finset.mem_Icc

end Global

end GlobalTheory.LamTie.TrueList
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

theorem root_eq {ε δ : OCb l} (h : δ ^ l = ε) : δ = (frobeniusEquiv (OCb l) l).symm ε := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, ← h]
  rfl

theorem coeff_zero_muOf (x : OCb l) : (muOf x).coeff 0 = x - 1 := by
  change WittVector.constantCoeff (WittVector.teichmuller l x - 1) = x - 1
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem frob_iterate_muOf (x : OCb l) (n : ℕ) :
    WittVector.frobenius^[n] (muOf x) = muOf (x ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, muOf, muOf, map_sub, map_one,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← pow_mul, pow_succ]

theorem theta_muOf (x : OCb l) : Per.θ l (muOf x) = x.untilt - 1 := by
  rw [muOf, map_sub, map_one, WittVector.fontaineTheta_teichmuller]


variable (l) in
def kerAll : Ideal (Ainf l) := ⨅ n : ℕ, RingHom.ker ((Per.θ l).comp (WittVector.frobenius ^ n))

theorem mem_kerAll (a : Ainf l) : a ∈ kerAll l ↔ ∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0 := by
  simp only [kerAll, Ideal.mem_iInf, RingHom.mem_ker, RingHom.comp_apply, RingHom.coe_pow]

theorem muOf_mem_kerAll {x : OCb l} (hx : x.untilt = 1) : muOf x ∈ kerAll l := by
  rw [mem_kerAll]
  intro n
  rw [frob_iterate_muOf, theta_muOf, map_pow, hx, one_pow, sub_self]

theorem kerAll_sat (a : Ainf l) (h : (l : Ainf l) * a ∈ kerAll l) : a ∈ kerAll l := by
  rw [mem_kerAll] at h ⊢
  intro n
  have h1 := h n
  rw [← RingHom.coe_pow, map_mul, map_natCast, map_mul, map_natCast, RingHom.coe_pow] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hl.out.ne_zero)

theorem isEps_mem {ε : OCb l} (hε : IsEps ε) :
    GlobalTheory.MemLoc.IsEps ε := by
  obtain ⟨h1, δ, hδ, hδ1⟩ := hε
  exact ⟨h1, by rw [← root_eq hδ]; exact hδ1⟩

theorem ne_one {ε : OCb l} (hε : IsEps ε) : ε ≠ 1 := by
  obtain ⟨-, δ, hδ, hδ1⟩ := hε
  rintro rfl
  have : δ = 1 := by rw [root_eq hδ, map_one]
  exact hδ1 (by rw [this, map_one])

theorem muOf_dvd {ε : OCb l} (hε : IsEps ε) {x : OCb l} (hx : x.untilt = 1) : muOf ε ∣ muOf x :=
  GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal l (OCb l) (kerAll l) (muOf ε) (muOf_mem_kerAll hε.1) kerAll_sat
    (fun a ha => by rw [coeff_zero_muOf]; exact GlobalTheory.T.epsilon_sub_one_dvd_ainf_coeff_zero_of_theta_vanishing l ε hε a ((mem_kerAll a).1 ha)) _ (muOf_mem_kerAll hx)

theorem muOf_ne_zero {ε : OCb l} (hε : IsEps ε) : muOf ε ≠ 0 := fun h => by
  have := congrArg (fun y : Ainf l => y.coeff 0) h
  simp only [coeff_zero_muOf, WittVector.zero_coeff] at this
  exact ne_one hε (sub_eq_zero.1 this)

theorem σA_muOf (g : GQ l) (x : OCb l) : Per.σA g (muOf x) = muOf (Per.σF g x) := by
  rw [muOf, muOf, map_sub, map_one, GlobalTheory.RingIface.sigA_teich]

theorem untilt_σF_eq {x : OCb l} (hx : x.untilt = 1) (g : GQ l) : (Per.σF g x).untilt = 1 := by
  rw [GlobalTheory.RingBasics.untilt_σF, hx, map_one]

end GlobalTheory.MuOfEps

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  exact ⟨e, he, _, frobeniusEquiv_symm_pow_p (OCb l) l e, hE.2⟩

theorem units_σA {ε : OCb l} (hε : IsEps ε) (g : GQ l) :
    ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε := by
  obtain ⟨a, ha⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g)
  obtain ⟨b, hb⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g⁻¹)
  rw [← σA_muOf] at ha hb
  have h : muOf ε = Per.σA g b * a * muOf ε := by
    have := congrArg (Per.σA g) hb
    rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one, map_mul, ha] at this
    linear_combination this
  have h1 : Per.σA g b * a = 1 := by
    have h2 : (Per.σA g b * a - 1) * muOf ε = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (muOf_ne_zero hε))
  refine ⟨⟨a, Per.σA g b, by rw [mul_comm]; exact h1, h1⟩, ?_⟩
  rw [ha, mul_comm]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∃ ε : OCb l, IsEps ε) ∧ ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∃ ξ : Ainf l, Ideal.span {ξ} = RingHom.ker (Per.θ l) ∧ muOf ε = ξ * muOf δ) ∧ WittVector.frobenius (muOf δ) = muOf ε ∧ Per.θ l (muOf δ) ≠ 0 ∧ IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) ∧ IsUnit (inclW l (muOf ε)) ∧ (∀ g : GQ l, ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε) ∧ ∀ x : OCb l, x.untilt = 1 → muOf ε ∣ muOf x := by
  intro l _
  refine ⟨exists_isEps l, fun ε δ hε hδ => ?_⟩
  have hr := root_eq hδ
  have hE := isEps_mem hε
  refine ⟨⟨GlobalTheory.MemLoc.xi ε, (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE).symm, ?_⟩, ?_, ?_, ?_, ?_, units_σA hε,
    fun x hx => muOf_dvd hε hx⟩
  · rw [GlobalTheory.MemLoc.xi, ← hr, muOf, muOf, geom_sum_mul, ← map_pow, hδ]
  · rw [muOf, muOf, map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, hδ]
  · rw [theta_muOf, sub_ne_zero]
    obtain ⟨-, δ', hδ', hδ'1⟩ := hε
    rwa [root_eq hδ', ← hr] at hδ'1
  · exact GlobalTheory.CrisLoc.unit_of_root l ε hε.1 (ne_one hε)
  · refine WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => ?_
    have h0 : (muOf ε).coeff 0 = 0 :=
      IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm)
    rw [coeff_zero_muOf] at h0
    exact ne_one hε (sub_eq_zero.1 h0)

end GlobalTheory.MuOfEps

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BKGal.CrisTensor

theorem mem_finiteCocycles_iff_bcrisTensor_coboundary {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l)
    (hpow : ∀ v : T.V, ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T)
    (β : TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B)
    (h1 : ∀ x : ↥T.L.T, β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B))
    (h2 : ∀ g b, β (actB (sQ l) T g b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b))
    (c : Gl l → T.V) (hc : c ∈ continuousCocycles T.ρ) :
    c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔ ∃ b, IsCobOf (sQ l) T b c := by
  have hl : ∀ n : ℕ, (l : ↥LL.1) ^ n ≠ 0 := fun n =>
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ (b : TW (OB l ↥(OL LL)) T) (g : Gl l) (n : ℕ),
      β ((l : ↥(OL LL)) ^ n • (actB (sQ l) T g b - b)) =
        (l : ↥LL.1) ^ n • (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b) - β b) := by
    intro b g n
    have e1 := β.map_smul ((l : ↥(OL LL)) ^ n) (actB (sQ l) T g b - b)
    have e2 : β (actB (sQ l) T g b - b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b) - β b :=
      (map_sub β _ _).trans (congrArg (· - β b) (h2 g b))
    have e3 : (((l : ↥(OL LL)) ^ n : ↥(OL LL)) : ↥LL.1) = (l : ↥LL.1) ^ n := by simp
    rw [← e3, ← e2]
    exact e1
  have kx : ∀ (g : Gl l) (n : ℕ) (x : ↥T.L.T), (x : T.V) = (l : ↥LL.1) ^ n • c g →
      β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (l : ↥LL.1) ^ n • (c g ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) := by
    intro g n x hx
    rw [h1, hx]
    exact (TensorProduct.smul_tmul' _ _ _).symm
  constructor
  · rintro ⟨-, y, hy⟩
    obtain ⟨b, rfl⟩ := β.surjective y
    refine ⟨b, fun g n x hx => β.injective ?_⟩
    exact (kx g n x hx).trans ((congrArg (fun z => (l : ↥LL.1) ^ n • z) (hy g)).trans (key b g n).symm)
  · rintro ⟨b, hb⟩
    refine ⟨hc, β b, fun g => ?_⟩
    obtain ⟨n, hn⟩ := hpow (c g)
    have h3 := (kx g n ⟨_, hn⟩ rfl).symm.trans ((congrArg β (hb g n ⟨_, hn⟩ rfl)).trans (key b g n))
    have h4 := congrArg (fun z => ((l : ↥LL.1) ^ n)⁻¹ • z) h3
    simpa only [inv_smul_smul₀ (hl n)] using h4

theorem exists_equiv : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∃ β : TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B, (∀ x : ↥T.L.T, β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) ∧ (∀ g b, β (actB (sQ l) T g b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b)) ∧ (∀ b, β (TWmap (frobOB l ↥(OL LL)) T b) = φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (β b)) ∧ ∀ c ∈ continuousCocycles T.ρ, (c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔ ∃ b, IsCobOf (sQ l) T b c) := by
  intro l _ LL T Pl AI hS
  obtain ⟨Ti⟩ := hS
  have hz : ∀ z : ℤ_[l], Ti.eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z :=
    fun z => (Ti.zB z).trans (GlobalTheory.RingIface.aB_zl l z).symm
  exact ⟨linEquiv T Ti.eB hz, linEquiv_one T Ti.eB hz, linEquiv_act T Ti.eB hz Ti.actB,
    linEquiv_frob T Ti.eB hz Ti.frob,
    mem_finiteCocycles_iff_bcrisTensor_coboundary T Pl (exists_pow_smul_mem T) _ (linEquiv_one T Ti.eB hz) (linEquiv_act T Ti.eB hz Ti.actB)⟩

end GlobalTheory.BKGal.CrisTensor
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.covers_tame_acts_ringEndo_wittPowerSeries : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (g : GQ l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ g γ → ∃ ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧, ∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x) := by
  first | exact @GlobalTheory.BKGal.covers_ringEndo | exact GlobalTheory.BKGal.covers_ringEndo | (intros; apply GlobalTheory.BKGal.covers_ringEndo <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal


theorem _root_.GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∃ s : ι → ZMod a → invL l (S O K e), (∀ j τ, (s j τ : K⟦X⟧) = E K l e ^ η * σ.1 τ j) ∧ toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, ϖ.iB t K (s j) • R.jB (fun i => toB l O (c j i)) := by
  first | exact @GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum | exact GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum | (intros; apply GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (k : GQ l) (s : ZMod a) (z : Fq l a), z ^ e = 1 → (∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w)) → ϖ.kummer k = Fq.val l a z → ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  first | exact @GlobalTheory.CoverGen.exists_covers_of_sigma_teich | exact GlobalTheory.CoverGen.exists_covers_of_sigma_teich | (intros; apply GlobalTheory.CoverGen.exists_covers_of_sigma_teich <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_pow_smul_mem_galoisStableLattice_Ql : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V), ∃ n : ℕ, ∃ x ∈ T.L.T, x = ((l : ↥LL.1) ^ n) • v := by
  first | exact @GlobalTheory.TContMul.main | exact GlobalTheory.TContMul.main | (intros; apply GlobalTheory.TContMul.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tensorBcris_value_frobenius_of_inverse_eisenstein_twist : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (hφ : D.phi y ∈ D.MMl), IsCrisVal t ϖ D.toPhiMod jB (phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩)) (jB (toBcris t ϖ D.toPhiMod ⟨D.phi y, hφ⟩)) := by
  first | exact @GlobalTheory.BKGal.PhiVal.isCrisVal_phi | exact GlobalTheory.BKGal.PhiVal.isCrisVal_phi | (intros; apply GlobalTheory.BKGal.PhiVal.isCrisVal_phi <;> assumption)
end
