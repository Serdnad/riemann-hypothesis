module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle002
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle003
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle001
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7
open scoped Pointwise

private theorem pt_pv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) (P : Polynomial (R0 A)) (z : Ω) (b : ℕ) (hz : τ z = z ^ b) :
    pv (Polynomial.expand (R0 A) b P) z = τ (pv P z) := by
  unfold pv
  rw [Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp, Polynomial.eval₂_X_pow, ← hz]
  have hc : ((τ : Ω →+* Ω)).comp (R0 A).subtype = (R0 A).subtype := by
    ext r
    exact r.2.2 τ hτ
  have e : (τ : Ω →+* Ω) (Polynomial.eval₂ (R0 A).subtype z P)
      = Polynomial.eval₂ (R0 A).subtype ((τ : Ω →+* Ω) z) P := by
    rw [Polynomial.hom_eval₂, hc]
  exact e.symm

private theorem pt_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) {x : Ω} (hx : x ∈ A) : τ x ∈ A := by
  have h := mem_Dec.mp (Ine_le_Dec A hτ)
  have h2 := ValuationSubring.smul_mem_pointwise_smul τ x A hx
  rw [h] at h2
  exact h2

private theorem pt_cg {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Type} [Fintype ι] (o : ι → Qbar l) (ho : ∀ i, ‖o i‖ ≤ 1)
    (k : ι → ZMod (l ^ n)) (b : ℕ) (x : Qbar l) (h : Cg n x (∑ i, o i * ((k i).val : Qbar l))) :
    Cg n ((b : Qbar l) * x) (∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)) := by
  unfold Cg at h ⊢
  haveI : NeZero (l ^ n) := ⟨(pow_pos (Nat.Prime.pos Fact.out) n).ne'⟩
  have hc : ∀ i, (((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l))
      = (b : Qbar l) * ((k i).val : Qbar l) - (l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l) := by
    intro i
    have h1 : ((b : ZMod (l ^ n)) * k i).val = (b * (k i).val) % l ^ n := by
      rw [← ZMod.val_natCast (l ^ n) (b * (k i).val)]
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h3 : ((b * (k i).val : ℕ) : Qbar l) = (((b * (k i).val) % l ^ n : ℕ) : Qbar l)
        + (l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l) := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    rw [Nat.cast_mul] at h3
    linear_combination -h3
  have hs : ∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)
      = ∑ i, (b : Qbar l) * (o i * ((k i).val : Qbar l))
        - ∑ i, o i * ((l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hc]; ring)
  have key : (b : Qbar l) * x - ∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)
      = (b : Qbar l) * (x - ∑ i, o i * ((k i).val : Qbar l))
        + ∑ i, o i * ((l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l)) := by
    rw [hs, mul_sub, Finset.mul_sum]
    ring
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(b : Qbar l)‖ * ‖x - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ 1 * ‖(l : Qbar l) ^ n‖ :=
          mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) h (norm_nonneg _) zero_le_one
      _ = ‖(l : Qbar l) ^ n‖ := one_mul _
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => ?_)
    rw [norm_mul, norm_mul]
    calc ‖o i‖ * (‖(l : Qbar l) ^ n‖ * ‖(((b * (k i).val) / l ^ n : ℕ) : Qbar l)‖)
        ≤ 1 * (‖(l : Qbar l) ^ n‖ * 1) := by
          gcongr
          · exact ho i
          · exact IsUltrametricDist.norm_natCast_le_one _ _
      _ = ‖(l : Qbar l) ^ n‖ := by ring

theorem UpperTheory.Kd.C7.pPresTr :
    UpperTheory.Kd.C7.SPresTr := by
  intro l _ hl Ω _ _ _ A hOver c β ζ hR Z hI b hb m n P hB
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hbu : IsUnit (b : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hb ?_)
    have h' : ‖((b : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h')
  obtain ⟨τ, hτ, hτc⟩ := (pFrobEx l hl Ω A hOver).2.2 hbu.unit
  have hmodpow : ∀ (t : Ω) (N a : ℕ), t ^ N = 1 → t ^ a = t ^ (a % N) := by
    intro t N a ht
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, ht, one_pow, mul_one]
  have hτpow : ∀ (t : Ω) (r : ℕ), t ^ l ^ r = 1 → τ t = t ^ b := by
    intro t r ht
    have hs := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω τ) t ht
    have e1 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω τ) = hbu.unit := hτc
    rw [e1, IsUnit.unit_spec, map_natCast, ZMod.val_natCast] at hs
    rw [hmodpow t (l ^ r) b ht]
    exact hs
  have hcyc : cycMod ℚ Ω l m τ = un b hb m := by
    apply Units.ext
    show (PadicInt.toZModPow m) ((cycZ ℚ Ω l τ : ℤ_[l])) = _
    rw [hτc, IsUnit.unit_spec, map_natCast]
    simp [un]
  have hu' : ∀ i, pv (Polynomial.expand (R0 A) b (P i)) (ζ m) = τ (pv (P i) (ζ m)) := fun i =>
    pt_pv hτ (P i) (ζ m) b (hτpow (ζ m) m (hR m).1.pow_eq_one)
  unfold BPres KumPres at hB ⊢
  obtain ⟨hprim, hnm, hunits, hnorm, hmain⟩ := hB
  refine ⟨hprim, hnm, fun i => ?_, hnorm, ?_⟩
  · dsimp only
    rw [hu' i]
    obtain ⟨h1, h2, h3⟩ := hunits i
    refine ⟨pt_mem hτ h1, (map_ne_zero τ).mpr h2, ?_⟩
    rw [← map_inv₀]
    exact pt_mem hτ h3
  · intro s hs hcs hsz
    have hs' : τ⁻¹ * s * τ ∈ Ine A := mul_mem (mul_mem (inv_mem hτ) hs) hτ
    have hcs' : cycMod ℚ Ω l m (τ⁻¹ * s * τ) = 1 := by simp [hcs]
    have hsz' : (τ⁻¹ * s * τ) (ζ n) = ζ n := fix_of_cycMod hnm hcs' hprim.pow_eq_one
    obtain ⟨k, hk, hcg⟩ := hmain _ hs' hcs' hsz'
    haveI : NeZero (l ^ n) := ⟨(pow_pos (Nat.Prime.pos Fact.out) n).ne'⟩
    refine ⟨fun i => (b : ZMod (l ^ n)) * k i, fun i => ?_, ?_⟩
    · obtain ⟨v, hv1, hv2⟩ := hk i
      refine ⟨τ v, ?_, ?_⟩
      · show (τ v) ^ l ^ n = pv (Polynomial.expand (R0 A) b (P i)) (ζ m)
        rw [hu' i, ← map_pow, hv1]
      · have e2 : s (τ v) = τ ((τ⁻¹ * s * τ) v) := by
          rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        have h1 : ((b : ZMod (l ^ n)) * k i).val = (b * (k i).val) % l ^ n := by
          rw [← ZMod.val_natCast (l ^ n) (b * (k i).val)]
          congr 1
          push_cast
          rw [ZMod.natCast_zmod_val]
        rw [e2, hv2, map_mul, map_pow, hτpow (ζ n) n hprim.pow_eq_one, ← pow_mul, h1,
          ← hmodpow (ζ n) (l ^ n) _ hprim.pow_eq_one]
    · have hHm : τ⁻¹ * s * τ ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs', hcs'⟩
      have hC := (pConj l hl Ω A hOver c Z hI m _ hHm τ hτ).2 (un b hb m)
      have e3 : τ * (τ⁻¹ * s * τ) * τ⁻¹ = s := by group
      rw [e3, hcyc, mul_inv_cancel] at hC
      show Cg n ((b : Qbar l) * Z m s (1 * un b hb m)) _
      rw [one_mul, hC]
      exact pt_cg β.val hnorm k b _ hcg
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem cg_mono {l : ℕ} [Fact l.Prime] {n N : ℕ} (h : n ≤ N) {a b : Qbar l} (hc : Cg N a b) : Cg n a b := by
  unfold Cg at *
  refine hc.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) h

private theorem cg_down {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {A : ValuationSubring Ω}
    {Z : Sy Ω l} (hZ : IwI c A Z) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (n r : ℕ) :
    ∀ d, (∀ x, Cg n (Z (r + d) s x) 0) → ∀ x, Cg n (Z r s x) 0 := by
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
    intro h
    apply ih
    intro x
    have hsum := hZ.nrm (r + d) s hs x
    unfold Cg at h ⊢
    rw [sub_zero, hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
    intro x' _
    have := h x'
    rw [sub_zero] at this
    exact this

private theorem unit_lift (l : ℕ) [Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) (x : (ZMod (l ^ m))ˣ) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZModPow m (u : ℤ_[l]) = x := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l ^ m) := ⟨Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt⟩
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) m) := by
    intro y
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
    exact ⟨k, map_natCast _ k⟩
  obtain ⟨u, hu⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hsurj hsurj.isLocalHom x
  exact ⟨u, congrArg Units.val hu⟩

theorem UpperTheory.Kd.C7.pContOf :
    UpperTheory.Kd.C7.SContOf := by
  unfold UpperTheory.Kd.C7.SContOf
  intro l _ hl2 Ω _ _ _ A hA c β ζ hζ Z hZ hP
  obtain ⟨c₀, m₀, hP⟩ := hP
  intro r n
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  set m := r + (m₀ + n + c₀ + 1) with hm_def
  have hm0 : m₀ ≤ m := by omega
  obtain ⟨P, hKP⟩ := hP m hm0
  set N := m - c₀ with hN
  obtain ⟨hprim, hNm, hu, ho, hk⟩ := hKP
  have hlN : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  choose w hw using fun i : Fin β.d => IsAlgClosed.exists_pow_nat_eq (pv (P i) (ζ m)) hlN
  have hfe := UpperTheory.Kd.C7.pFrobEx l hl2 Ω A hA
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hlift : ∀ y : (ZMod (l ^ m))ˣ, ∃ t ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m t = y⁻¹ := by
    intro y
    obtain ⟨u, hu'⟩ := unit_lift l m (by omega) y⁻¹
    obtain ⟨t, ht, htu⟩ := hfe.2.2 u
    refine ⟨t, ht, ?_⟩
    ext
    simp [ReciprocityTheory.Gal.cycMod, htu, hu']
  choose tt htt hcyc using hlift
  let f : (ZMod (l ^ m))ˣ × Option (Fin β.d) → Ω := fun q => (tt q.1)⁻¹ (q.2.elim (ζ N) w)
  let E := IntermediateField.adjoin ℚ (Set.range f)
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  refine ⟨(cycMod ℚ Ω l m).ker ⊓ E.fixingSubgroup, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    refine IsOpen.inter ?_ E.fixingSubgroup_isOpen
    have := (GlobalTheory.KZ.IwC.isLocallyConstant_cycMod (Ω := Ω) (l := l) m).isOpen_fiber 1
    rw [MonoidHom.coe_ker]
    exact this
  · intro s hsU hs
    obtain ⟨hsk, hsE⟩ := Subgroup.mem_inf.mp hsU
    have hfix : ∀ q, s (f q) = f q := by
      intro q
      exact (mem_fixingSubgroup_iff _).mp hsE (f q) (IntermediateField.subset_adjoin ℚ _ ⟨q, rfl⟩)
    apply cg_down hZ hs n r (m₀ + n + c₀ + 1)
    intro y
    have hsH : s ∈ Hm l A m := by
      unfold UpperTheory.Kd.C7.Hm
      exact Subgroup.mem_inf.mpr ⟨hs, hsk⟩
    obtain ⟨hconjH, hconj⟩ := UpperTheory.Kd.C7.pConj l hl2 Ω A hA c Z hZ m s hsH (tt y) (htt y)
    have hZeq : Z m (tt y * s * (tt y)⁻¹) 1 = Z m s y := by
      rw [hconj]
      simp [hcyc]
    have hconjH' := hconjH
    unfold UpperTheory.Kd.C7.Hm at hconjH'
    have hs'I := (Subgroup.mem_inf.mp hconjH').1
    have hs'k : cycMod ℚ Ω l m (tt y * s * (tt y)⁻¹) = 1 := (Subgroup.mem_inf.mp hconjH').2
    have hs'fix : ∀ o : Option (Fin β.d),
        (tt y * s * (tt y)⁻¹) (o.elim (ζ N) w) = o.elim (ζ N) w := by
      intro o
      have h := hfix (y, o)
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, mul_inv_cancel,
        AlgEquiv.one_apply]
    have hz : (tt y * s * (tt y)⁻¹) (ζ N) = ζ N := hs'fix none
    obtain ⟨k, hkv, hcg⟩ := hk _ hs'I hs'k hz
    have hk0 : ∀ i, k i = 0 := by
      intro i
      have hwi : (tt y * s * (tt y)⁻¹) (w i) = w i := hs'fix (some i)
      have h0 : KumVal N (ζ N) (pv (P i) (ζ m)) (tt y * s * (tt y)⁻¹) 0 :=
        ⟨w i, hw i, by rw [hwi]; simp⟩
      exact kumVal_unique hprim hz (hu i).2.1 (hkv i) h0
    rw [← hZeq]
    apply cg_mono (n := n) (N := N) (by omega)
    simpa [hk0] using hcg
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem nat_le_one' {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

private theorem dd_mul_eq_dd_mul_add_mul_dd {R : Type} [CommRing R] (f g : PowerSeries R) :
    dd (f * g) = dd f * g + f * dd g := by
  simp [dd]; ring

private theorem dl_mul_eq_add_of_isUnit {R : Type} [CommRing R] {f g : PowerSeries R}
    (hf : IsUnit f) (hg : IsUnit g) : dl (f * g) = dl f + dl g := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨v, rfl⟩ := hg
  simp only [dl, ← Units.val_mul, Ring.inverse_unit]
  simp only [Units.val_mul, mul_inv_rev, dd_mul_eq_dd_mul_add_mul_dd]
  have h1 : (u : PowerSeries R) * ↑u⁻¹ = 1 := u.mul_inv
  have h2 : (v : PowerSeries R) * ↑v⁻¹ = 1 := v.mul_inv
  linear_combination (dd (u : PowerSeries R) * ↑u⁻¹) * h2 + (dd (v : PowerSeries R) * ↑v⁻¹) * h1

theorem UpperTheory.Kd.C7.pRepAdd :
    UpperTheory.Kd.C7.SRepAdd := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ
  have hB := (pBasEx l c).2 β
  have hpv : ∀ (P Q : Polynomial (R0 A)) (z : Ω), pv (P * Q) z = pv P z * pv Q z := by
    intro P Q z; simp [pv, Polynomial.eval₂_mul]
  refine ⟨?_, ?_⟩
  · rintro Z Z' D D' ⟨c₁, m₁, h₁⟩ ⟨c₂, m₂, h₂⟩
    refine ⟨max c₁ c₂, max (max m₁ m₂) 1, fun m hm => ?_⟩
    have hm₁ : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
    have hm₂ : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
    have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hc₁ : m - max c₁ c₂ ≤ m - c₁ := Nat.sub_le_sub_left (le_max_left _ _) m
    have hc₂ : m - max c₁ c₂ ≤ m - c₂ := Nat.sub_le_sub_left (le_max_right _ _) m
    obtain ⟨P, hP, hPL⟩ := h₁ m hm₁
    obtain ⟨P', hP', hPL'⟩ := h₂ m hm₂
    have hQ := pPresMono l hl Ω A hA c β ζ hζ Z Z m (m - c₁) (m - max c₁ c₂) P hc₁
      (fun s _ => by simp [Cg]) hP
    have hQ' := pPresMono l hl Ω A hA c β ζ hζ Z' Z' m (m - c₂) (m - max c₁ c₂) P' hc₂
      (fun s _ => by simp [Cg]) hP'
    unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres at hQ hQ'
    obtain ⟨hprim, hnr, hu, ho, hk⟩ := hQ
    obtain ⟨-, -, hu', -, hk'⟩ := hQ'
    refine ⟨fun i => P i * P' i, ?_, fun i => ?_⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨hprim, hnr, fun i => ?_, ho, fun s hs hcyc hsζ => ?_⟩
      · dsimp only
        rw [hpv]
        obtain ⟨a₁, a₂, a₃⟩ := hu i
        obtain ⟨b₁, b₂, b₃⟩ := hu' i
        dsimp only at a₁ a₂ a₃ b₁ b₂ b₃
        exact ⟨mul_mem a₁ b₁, mul_ne_zero a₂ b₂, by rw [mul_inv]; exact mul_mem a₃ b₃⟩
      · obtain ⟨k, hkv, hkc⟩ := hk s hs hcyc hsζ
        obtain ⟨k', hkv', hkc'⟩ := hk' s hs hcyc hsζ
        have hsH : s ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩
        have halg := (pKumAlg l hl Ω A hA ζ hζ m (m - max c₁ c₂) (Nat.sub_le _ _) s hsH).1
        refine ⟨k + k', fun i => ?_, ?_⟩
        · dsimp only
          rw [hpv]
          exact (halg _ _ _ _ (hkv i) (hkv' i)).1
        · have hNz : NeZero (l ^ (m - max c₁ c₂)) :=
            ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
          have key : ∀ i, (((k + k') i).val : Qbar l) = (k i).val + (k' i).val
              - (l : Qbar l) ^ (m - max c₁ c₂)
                * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l) := by
            intro i
            rw [Pi.add_apply, ZMod.val_add, eq_sub_iff_add_eq]
            exact_mod_cast Nat.mod_add_div ((k i).val + (k' i).val) (l ^ (m - max c₁ c₂))
          unfold Cg at hkc hkc' ⊢
          dsimp only
          have hsplit : Z m s 1 + Z' m s 1 - ∑ i, β.val i * (((k + k') i).val : Qbar l)
              = (Z m s 1 - ∑ i, β.val i * ((k i).val : Qbar l))
                + (Z' m s 1 - ∑ i, β.val i * ((k' i).val : Qbar l))
                + ∑ i, β.val i * ((l : Qbar l) ^ (m - max c₁ c₂)
                  * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l)) := by
            simp only [key, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
            ring
          rw [hsplit]
          have hN : 0 ≤ ‖(l : Qbar l) ^ (m - max c₁ c₂)‖ := norm_nonneg _
          refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
            (max_le (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hkc hkc')) ?_)
          refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hN (fun i _ => ?_)
          rw [norm_mul, norm_mul]
          have h1 := ho i
          have h2 := nat_le_one' (l := l) (((k i).val + (k' i).val) / l ^ (m - max c₁ c₂))
          calc _ ≤ 1 * (‖(l : Qbar l) ^ (m - max c₁ c₂)‖ * 1) :=
                mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hN) (by positivity) zero_le_one
            _ = _ := by ring
    · have hU : IsUnit (Φ.ser (P i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P i)).2 (hu i)
      have hU' : IsUnit (Φ.ser (P' i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P' i)).2 (hu' i)
      have hs : Φ.ser (P i * P' i) = Φ.ser (P i) * Φ.ser (P' i) := by
        simp [Fr.ser, Polynomial.map_mul, Polynomial.eval₂_mul]
      have ht : Φ.tw m ((D + D') i) = Φ.tw m (D i) + Φ.tw m (D' i) := by
        simp [Fr.tw, map_add (f := _)]
      have e₁ := hPL i
      have e₂ := hPL' i
      unfold LC at e₁ e₂ ⊢
      dsimp only
      rw [ht, hs, dl_mul_eq_add_of_isUnit hU hU', map_add (f := _), map_add (f := _)]
      have f₁ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₁) e₁
      have f₂ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₂) e₂
      convert Ideal.add_mem _ f₁ f₂ using 1
      ring
  · intro Z hZ
    refine ⟨0, 0, fun m _ => ⟨fun _ => 1, ?_, fun i => ?_⟩⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨by simpa using (hζ m).1, by simp, fun i => by simp [pv], fun i => hB.1 i,
        fun s hs hcyc hsζ => ⟨0, fun i => ?_, ?_⟩⟩
      · unfold KumVal
        exact ⟨1, by simp [pv], by simp⟩
      · unfold Cg
        have hz := hZ m s (Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩)
        simp [hz]
    · unfold LC
      simp [Fr.tw, Fr.ser, dl, dd]
end
