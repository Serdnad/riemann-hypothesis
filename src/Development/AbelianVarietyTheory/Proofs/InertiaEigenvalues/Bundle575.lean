module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle038
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle083
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle555
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.ChiUnit

open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_inv {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N u⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  exact ⟨inv_ne_zero hu0, n, hn2, by rw [inv_inv]; exact hn1⟩

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  ⟨one_ne_zero, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩

theorem unitOff_pow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℕ) : UnitOff N (u ^ k) := by
  induction k with
  | zero => simpa using unitOff_one N
  | succ k ih => rw [pow_succ]; exact unitOff_mul ih hu

theorem unitOff_zpow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℤ) : UnitOff N (u ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact unitOff_pow hu m
  · rw [_root_.zpow_neg, zpow_natCast]; exact unitOff_inv (unitOff_pow hu m)

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitOff_one N
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_of_pow {N : ℕ} {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : UnitOff N (u ^ k)) : UnitOff N u := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  have hN : IsIntegral ℤ ((N : ℂ) ^ (n * (k - 1))) := by
    have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
    exact this.pow _
  refine ⟨fun h => hu0 (by rw [h, zero_pow hk.ne']), n, ?_, ?_⟩
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * u ^ k) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn1
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u⁻¹) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * (u ^ k)⁻¹) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, inv_pow]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn2

theorem unitOff_of_pow_eq_one (N : ℕ) {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : UnitOff N u :=
  unitOff_of_pow hk (by rw [hu]; exact unitOff_one N)

theorem unitOff_of_mul_eq {N m : ℕ} {a b : ℂ} (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (hab : a * b = (N : ℂ) ^ m) (hN : N ≠ 0) : UnitOff N a := by
  have hNm : (N : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  have ha0 : a ≠ 0 := fun h => hNm (by rw [← hab, h, zero_mul])
  refine ⟨ha0, m, ?_, ?_⟩
  · have : IsIntegral ℤ ((N : ℂ) ^ m) := by
      have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      exact this.pow _
    exact this.mul ha
  · have e : (N : ℂ) ^ m * a⁻¹ = b := by rw [← hab]; field_simp
    rw [e]; exact hb

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem LR {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (n : ℕ) (h : χ ^ n = 1)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (k : Lˣ) : (χ.locK w k) ^ n = 1 := by
  have e : (χ ^ n).locK w k = (χ.locK w k) ^ n := by
    simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]
  rw [← e, h]
  simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a)
    (h1 : a ∈ w.asIdeal) (h2 : a ∉ w.asIdeal ^ 2) : χ.locK w k = χ.val w :=
  χ.val_eq hw _ (by
    unfold Formalism.L2.Host.IsUnifAt
    rw [GlobalTheory.TypeValues.val_atFin w k a hk, GlobalTheory.TypeValues.intValuation_eq_of_mem h1 h2])

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem finite_ramified_places_hecke_character {D : D7} (χ : Formalism.L2.Host.HChar D.host.E)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬Formalism.L2.Host.OverP D.host (D.host.g k) v) → χ.UnrAt v) :
    {w | ¬ χ.UnrAt w}.Finite := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hI : Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hc
  refine hw (h w fun k hk => hc ?_)
  unfold Formalism.L2.Host.OverP at hk
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hk
  · exact Ideal.mul_mem_left _ _ hk

theorem not_mem_of_prime_ne {L : Type} [Field L] [NumberField L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : (p : 𝓞 L) ∉ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | (apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne ..)

end GlobalTheory.ChiUnit
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.InertiaEigenvalues.TiltGalLog

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem zeta_pow_compat {l : ℕ} [Fact l.Prime] (C : Core l) (c : ℤ_[l]) (m : ℕ) :
    C.ζ m ^ (PadicInt.toZModPow (m + 1) c).val = C.ζ m ^ (PadicInt.toZModPow m c).val := by
  have hz : C.ζ m ^ (l ^ m) = 1 := TAct.zeta_pow C m
  have hred : ∀ a : ℕ, C.ζ m ^ a = C.ζ m ^ (a % l ^ m) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a (l ^ m), pow_add, pow_mul, hz, one_pow, mul_one]
  have hmod : (PadicInt.toZModPow (m + 1) c).val ≡ (PadicInt.toZModPow m c).val [MOD l ^ m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val]
    have h := congrArg (fun f : ℤ_[l] →+* ZMod (l ^ m) => f c)
      (PadicInt.zmod_cast_comp_toZModPow (p := l) m (m + 1) (Nat.le_succ m))
    simpa using h
  rw [hred, hmod, ← hred]

theorem rootT_mul {l : ℕ} [Fact l.Prime] (a b : Per.Fl l) (m : ℕ) :
    rootT (a * b) m = rootT a m * rootT b m := by
  unfold rootT
  rw [← map_mul]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem gal_factor_log : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  intro l _ C x g c H
  obtain ⟨e, he⟩ := NoLog.exists_tilt (fun m => C.ζ m ^ (PadicInt.toZModPow m c).val)
    (fun m => by
      show (C.ζ (m + 1) ^ (PadicInt.toZModPow (m + 1) c).val) ^ l = C.ζ m ^ (PadicInt.toZModPow m c).val
      rw [← pow_mul, mul_comm, pow_mul, C.ζ_succ, zeta_pow_compat]) 1 (by simp [C.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [C.ζ_zero, one_pow, map_one] at this
    exact this)
  have hre : ∀ m, rootT e m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := fun m =>
    Subtype.ext (by rw [he m, SubmonoidClass.coe_pow, C.ε_root m, map_pow])
  have hxe : Per.σF g x = x * e := by
    refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g x) = PreTilt.coeff n (x * e)
    rw [coeff_eq_mk_rootT, coeff_eq_mk_rootT, H n, rootT_mul, hre n, mul_comm]
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  have hyeq := NoLog.log_eq C e c y he hy
  refine ⟨e, hxe, he1, ?_⟩
  have h := LogFun.isLog_map he1 hy C.j_cris
  have hj : C.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) = aDp l (Per.zA l c) := by
    rw [GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap, aDp, RingHom.comp_apply]
  rwa [hyeq, map_mul, hj] at h

end GlobalTheory.InertiaEigenvalues.TiltGalLog
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LevelTypeProj

theorem span_eval_eq_top {X M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (ev : X → Module.Dual ℂ M) (hev : ∀ v, (∀ x, ev x v = 0) → v = 0) :
    Submodule.span ℂ (Set.range ev) = ⊤ := by
  have hbot : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact (Submodule.mem_bot ℂ).2 (hev v fun x => hv (ev x) (Submodule.subset_span ⟨x, rfl⟩))
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hbot,
    Submodule.dualAnnihilator_bot]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem finRep_cptRep (l : GL (Fin N) (Af E)) (k : Kinf E N) (φ : Sm E N) :
    finRep E N l (cptRep E N k φ) = cptRep E N k (finRep E N l φ) := by
  simp only [finRep, cptRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]

def orbitSpan (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : Submodule ℂ (Sm E N) :=
  Submodule.span ℂ {v | ∃ l ∈ L, ∃ k, v = finRep E N l (cptRep E N k ψ)}

theorem mem_orbitSpan_self (L : Subgroup (GL (Fin N) (Af E))) (ψ : Sm E N) : ψ ∈ orbitSpan L ψ :=
  Submodule.subset_span ⟨1, L.one_mem, 1, by rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]⟩

theorem orbitSpan_le {J : Submodule ℂ (Sm E N)} (hJ : _root_.GlobalTheory.CuspRep.IsStable J) (L : Subgroup (GL (Fin N) (Af E)))
    {ψ : Sm E N} (hψ : ψ ∈ J) : orbitSpan L ψ ≤ J :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, k, rfl⟩; exact hJ (.fin l) _ (hJ (.cpt k) _ hψ))

theorem finRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} {l' : GL (Fin N) (Af E)}
    (hl' : l' ∈ L) {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : finRep E N l' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l' * l, L.mul_mem hl' hl, k, ?_⟩
    rw [map_mul (finRep E N), Module.End.mul_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem cptRep_mem_orbitSpan {L : Subgroup (GL (Fin N) (Af E))} {ψ : Sm E N} (k' : Kinf E N)
    {v : Sm E N} (hv : v ∈ orbitSpan L ψ) : cptRep E N k' v ∈ orbitSpan L ψ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, k, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l, hl, k' * k, ?_⟩
    rw [map_mul (cptRep E N), Module.End.mul_apply, finRep_cptRep l k' (cptRep E N k ψ)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem orbitSpan_finiteDimensional (L : Subgroup (GL (Fin N) (Af E))) (hL : IsCompact (L : Set (GL (Fin N) (Af E))))
    (ψ : Sm E N) (hψ : IsAutForm ψ) : FiniteDimensional ℂ (orbitSpan L ψ) := by
  classical
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover (fun l : GL (Fin N) (Af E) => {m | finRep E N (l⁻¹ * m) ψ = ψ})
    (fun l => hψ.level.preimage (continuous_const_mul l⁻¹))
    (fun m _ => Set.mem_iUnion.2 ⟨m, by simp only [Set.mem_setOf_eq, inv_mul_cancel, map_one]; rfl⟩)
  have := hψ.kfin
  refine Submodule.finiteDimensional_of_le
    (S₂ := t.sup fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨m, hm, k, rfl⟩
  obtain ⟨l, hl, hlm⟩ := Set.mem_iUnion₂.1 (ht hm)
  have e : finRep E N m ψ = finRep E N l ψ := by
    calc finRep E N m ψ = finRep E N l (finRep E N (l⁻¹ * m) ψ) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = finRep E N l ψ := by rw [show finRep E N (l⁻¹ * m) ψ = ψ from hlm]
  refine Finset.le_sup (f := fun l => (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)).map (finRep E N l)) hl ?_
  refine ⟨cptRep E N k ψ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  change finRep E N l (cptRep E N k ψ) = finRep E N m (cptRep E N k ψ)
  rw [finRep_cptRep, finRep_cptRep, e]

def typePart (L : Subgroup (GL (Fin N) (Af E))) {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Kinf E N) U) : Submodule ℂ (Sm E N) where
  carrier := {φ | (∀ k ∈ L, finRep E N k φ = φ) ∧
    ∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k hk => by rw [map_add (f := _), hx.1 k hk, hy.1 k hk],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ => map_zero _, fun _ => by
    simp only [map_zero, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k hk => by rw [map_smul, hx.1 k hk],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem exists_proj {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    (S : Submodule ℂ (Sm E N)) (hSW : S ≤ W) [FiniteDimensional ℂ S] :
    ∃ p : W →ₗ[ℂ] W, (∀ x, (p x).1 ∈ S) ∧
      ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0 := by
  haveI : FiniteDimensional ℂ (S.comap W.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hSW).symm.finiteDimensional
  let e := Submodule.equivMapOfInjective (toL2ₗ μ W h) hF (S.comap W.subtype)
  haveI : FiniteDimensional ℂ ((S.comap W.subtype).map (toL2ₗ μ W h)) := e.finiteDimensional
  have e1 : ∀ z, toL2ₗ μ W h ((e.symm z : S.comap W.subtype) : W) = (z : L2 (latticeGL E N) μ) := fun z => by
    have := Submodule.coe_equivMapOfInjective_apply (toL2ₗ μ W h) hF (S.comap W.subtype) (e.symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(S.comap W.subtype).subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    ((S.comap W.subtype).map (toL2ₗ μ W h)).orthogonalProjectionOnto.toLinearMap ∘ₗ toL2ₗ μ W h,
    fun x => (e.symm _).2, fun x y hy => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
  rw [e1]
  exact Submodule.starProjection_inner_eq_zero _ _ ⟨y, hy, rfl⟩

theorem proj_unique {μ : Measure (GA E N)} [μ.IsHaarMeasure] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} {x a b : W} (ha : a.1 ∈ S) (hb : b.1 ∈ S)
    (hxa : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h a) (toL2ₗ μ W h y) = 0)
    (hxb : ∀ y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h b) (toL2ₗ μ W h y) = 0) : a = b := by
  have hm : (b - a).1 ∈ S := S.sub_mem hb ha
  have key : toL2ₗ μ W h (b - a) = (toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b) := by
    rw [map_sub]; abel
  have h0 : inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a)) = 0 := by
    calc inner ℂ (toL2ₗ μ W h (b - a)) (toL2ₗ μ W h (b - a))
        = inner ℂ ((toL2ₗ μ W h x - toL2ₗ μ W h a) - (toL2ₗ μ W h x - toL2ₗ μ W h b)) (toL2ₗ μ W h (b - a)) := by
          rw [← key]
      _ = 0 := by rw [inner_sub_left, hxa _ hm, hxb _ hm, sub_zero]
  exact (sub_eq_zero.1 (hF ((inner_self_eq_zero.1 h0).trans (map_zero _).symm))).symm

theorem proj_rt {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
    (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hF : Function.Injective (toL2ₗ μ W h))
    {S : Submodule ℂ (Sm E N)} (hSW : S ≤ W) (p : W →ₗ[ℂ] W) (hpS : ∀ x, (p x).1 ∈ S)
    (hp : ∀ x y : W, y.1 ∈ S → inner ℂ (toL2ₗ μ W h x - toL2ₗ μ W h (p x)) (toL2ₗ μ W h y) = 0)
    (g : GA E N) (hgW : ∀ x ∈ W, rt E N g x ∈ W) (hgS : ∀ x ∈ S, rt E N g x ∈ S)
    (hgS' : ∀ x ∈ S, rt E N g⁻¹ x ∈ S) (x : W) :
    p ⟨rt E N g x.1, hgW _ x.2⟩ = ⟨rt E N g (p x).1, hgW _ (p x).2⟩ := by
  refine proj_unique h hF (hpS _) (hgS _ (hpS x)) (hp _) fun y hy => ?_
  have hy' : rt E N g⁻¹ y.1 ∈ W := hSW (hgS' _ hy)
  have ey : y = ⟨rt E N g (rt E N g⁻¹ y.1), hgW _ hy'⟩ := Subtype.ext (by
    show y.1 = rt E N g (rt E N g⁻¹ y.1)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  rw [ey, ← R_toL2ₗ h x (hgW _ x.2), ← R_toL2ₗ h (p x) (hgW _ (p x).2), ← R_toL2ₗ h ⟨_, hy'⟩ (hgW _ hy'),
    ← map_sub]
  let Ui : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ := ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  change inner ℂ (Ui _) (Ui _) = 0
  rw [Ui.inner_map_map]
  exact hp x ⟨_, hy'⟩ (hgS' _ hy)

theorem exists_levelType_part : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W J : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ) → _root_.GlobalTheory.CuspRep.IsStable J → J ≤ W → ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (ρ : Representation ℂ (Kinf E N) U), AutFin.IsContRep ρ → ∀ ψ : W, ψ.1 ∈ J → ∃ ψ' : W, ψ'.1 ∈ J ∧ (∀ k ∈ L, finRep E N k ψ'.1 = ψ'.1) ∧ (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k ψ'.1).1 g) ∈ AutFin.coeffSpan ρ) ∧ ∀ φ : W, (∀ k ∈ L, finRep E N k φ.1 = φ.1) → (∀ g : GA E N, (fun k : Kinf E N => (cptRep E N k φ.1).1 g) ∈ AutFin.coeffSpan ρ) → inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ) = inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ψ') := by
  intro E _ _ _ N μ _ _ W J h hW hA hJ hJW L _ hLc U _ _ _ ρ _ ψ hψ
  have hF := toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level
  have hSJ : orbitSpan L ψ.1 ≤ J := orbitSpan_le hJ L hψ
  have hSW := hSJ.trans hJW
  haveI := orbitSpan_finiteDimensional L hLc ψ.1 (hA _ ψ.2)
  haveI : FiniteDimensional ℂ (orbitSpan L ψ.1 ⊓ typePart L ρ : Submodule ℂ (Sm E N)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨p, hpS, hp⟩ := exists_proj h hF (orbitSpan L ψ.1) hSW
  obtain ⟨q, hqQ, hq⟩ := exists_proj h hF (orbitSpan L ψ.1 ⊓ typePart L ρ) (inf_le_left.trans hSW)
  refine ⟨q ψ, hSJ (hqQ ψ).1, (hqQ ψ).2.1, (hqQ ψ).2.2, fun φ hφL hφK => ?_⟩
  have hpT : (p φ).1 ∈ typePart L ρ := by
    refine ⟨fun k hk => ?_, fun g => ?_⟩
    · have hc := proj_rt h hF hSW p hpS hp (finGL E N k) (fun x hx => hW (.fin k) x hx)
        (fun x hx => finRep_mem_orbitSpan hk hx)
        (fun x hx => by rw [← map_inv]; exact finRep_mem_orbitSpan (L.inv_mem hk) hx) φ
      exact (congrArg Subtype.val hc).symm.trans (congrArg (fun x => (p x).1) (Subtype.ext (hφL k hk)))
    · have hcomm : ∀ k : Kinf E N, cptRep E N k (p φ).1 = (p ⟨cptRep E N k φ.1, hW (.cpt k) _ φ.2⟩).1 := fun k =>
        (congrArg Subtype.val (proj_rt h hF hSW p hpS hp (infGL E N (Unitary.toUnits k))
          (fun x hx => hW (.cpt k) x hx) (fun x hx => cptRep_mem_orbitSpan k hx)
          (fun x hx => by rw [← map_inv, ← map_inv]; exact cptRep_mem_orbitSpan k⁻¹ hx) φ)).symm
      have := (hA φ φ.2).kfin
      have hVW : Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1) ≤ W :=
        Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hW (.cpt k) _ φ.2)
      let V := Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)
      let Λ : Module.Dual ℂ V →ₗ[ℂ] (Kinf E N → ℂ) :=
        { toFun := fun ℓ k => ℓ ⟨cptRep E N k φ.1, Submodule.subset_span ⟨k, rfl⟩⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let ev : GA E N → Module.Dual ℂ V := fun x => (LinearMap.proj x).comp ((Sm E N).subtype.comp V.subtype)
      have htop := span_eval_eq_top ev fun v hv => Subtype.ext (Subtype.ext (funext hv))
      have hle : Submodule.span ℂ (Set.range ev) ≤ (AutFin.coeffSpan ρ).comap Λ :=
        Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hφK x)
      let ℓ : Module.Dual ℂ V :=
        (LinearMap.proj g).comp ((Sm E N).subtype.comp (W.subtype.comp (p.comp (Submodule.inclusion hVW))))
      have hℓ : Λ ℓ ∈ AutFin.coeffSpan ρ := hle (htop ▸ Submodule.mem_top)
      convert hℓ using 1
      funext k
      rw [hcomm k]
      rfl
  have hψS : ψ.1 ∈ orbitSpan L ψ.1 := mem_orbitSpan_self L ψ.1
  have hr : (ψ - q ψ).1 ∈ orbitSpan L ψ.1 := (orbitSpan L ψ.1).sub_mem hψS (hqQ ψ).1
  have h1 : inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h (ψ - q ψ)) =
      inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) := by
    have := hp φ (ψ - q ψ) hr
    rwa [inner_sub_left, sub_eq_zero] at this
  have h2 : inner ℂ (toL2ₗ μ W h (p φ)) (toL2ₗ μ W h (ψ - q ψ)) = 0 := by
    have := hq ψ (p φ) ⟨hpS φ, hpT⟩
    rw [map_sub, ← inner_conj_symm, this, map_zero]
  rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, h1, h2]

end GlobalTheory.LevelTypeProj

end
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  first | exact @GlobalTheory.PSerExist.exists_zeros | exact GlobalTheory.PSerExist.exists_zeros | (intros; apply GlobalTheory.PSerExist.exists_zeros <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  first | exact @GlobalTheory.CutCoreUnit.main | exact GlobalTheory.CutCoreUnit.main | (intros; apply GlobalTheory.CutCoreUnit.main <;> assumption)
end
