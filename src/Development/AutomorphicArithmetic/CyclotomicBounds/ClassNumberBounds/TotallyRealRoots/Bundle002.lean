module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc
public import Mathlib.Algebra.Module.Torsion.Basic
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthFrac
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EmultiplicityPowSubOneOdd
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

namespace KStar.TotallyRealRoots

open IsDiscreteValuationRing

variable (l : ℕ) [Fact l.Prime] (O : Type*) [CommRing O] [Algebra ℤ_[l] O]

def twistInvOver (A : Type*) [AddCommGroup A] [Module O A] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) :
    Submodule O A where
  carrier := {x | ∀ u ∈ U, (algebraMap ℤ_[l] O (u : ℤ_[l]) ^ tr) • x = x}
  zero_mem' := fun u _ => smul_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [smul_add, hx u hu, hy u hu]
  smul_mem' := fun c x hx u hu => by rw [smul_comm, hx u hu]

variable {l O}

theorem mem_twistInvOver {A : Type*} [AddCommGroup A] [Module O A] {U : Subgroup ℤ_[l]ˣ} {tr : ℕ}
    {x : A} : x ∈ twistInvOver l O A U tr ↔
      ∀ u ∈ U, (algebraMap ℤ_[l] O (u : ℤ_[l]) ^ tr) • x = x := Iff.rfl

private theorem torsionBy_pow_le_twistInvOver (A : Type*) [AddCommGroup A] [Module O A] {U : Subgroup ℤ_[l]ˣ}
    {tr n : ℕ} (h : (n : ℕ∞) ≤ nu l U tr) :
    Submodule.torsionBy O A ((l : O) ^ n) ≤ twistInvOver l O A U tr := by
  intro x hx
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [mem_twistInvOver]
  intro u hu
  obtain ⟨c, hc⟩ := le_nu_iff.mp h u hu
  have e : (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ tr - 1 = (l : O) ^ n * algebraMap ℤ_[l] O c := by
    rw [← map_pow, ← map_one (algebraMap ℤ_[l] O), ← map_sub, hc, map_mul, map_pow, map_natCast]
  have e2 : ((algebraMap ℤ_[l] O (u : ℤ_[l])) ^ tr) • x =
      x + ((algebraMap ℤ_[l] O (u : ℤ_[l])) ^ tr - 1) • x := by
    rw [sub_smul, one_smul]
    abel
  rw [e2, e, mul_comm, mul_smul, hx, smul_zero, add_zero]

theorem twistInvOver_eq_torsionBy (A : Type*) [AddCommGroup A] [Module O A] {U : Subgroup ℤ_[l]ˣ}
    {tr n : ℕ} (h : nu l U tr = n) :
    twistInvOver l O A U tr = Submodule.torsionBy O A ((l : O) ^ n) := by
  apply le_antisymm
  · intro x hx
    rw [mem_twistInvOver] at hx
    rw [Submodule.mem_torsionBy_iff]
    have hstar : nuStar (l : ℤ_[l]) ((fun u : ℤ_[l]ˣ => (u : ℤ_[l])) '' (U : Set ℤ_[l]ˣ)) tr = (n : ℕ∞) := h
    obtain ⟨w, ⟨v, hv, rfl⟩, hdvd, hndvd⟩ := exists_exact_of_nuStar_eq hstar
    obtain ⟨c, hc⟩ := hdvd
    have hcu : IsUnit c := by
      by_contra hnu
      rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at hnu
      obtain ⟨d, hd⟩ := hnu
      apply hndvd
      refine ⟨d, ?_⟩
      rw [hc, hd, pow_succ]
      ring
    have e : (algebraMap ℤ_[l] O (v : ℤ_[l])) ^ tr - 1 = (l : O) ^ n * algebraMap ℤ_[l] O c := by
      rw [← map_pow, ← map_one (algebraMap ℤ_[l] O), ← map_sub, hc, map_mul, map_pow, map_natCast]
    have h1 : ((algebraMap ℤ_[l] O (v : ℤ_[l])) ^ tr - 1) • x = 0 := by
      rw [sub_smul, one_smul, hx v hv, sub_self]
    rw [e, mul_comm, mul_smul] at h1
    exact ((hcu.map (algebraMap ℤ_[l] O)).smul_eq_zero).mp h1
  · exact torsionBy_pow_le_twistInvOver A (by rw [h])

variable [IsDomain O] [IsDiscreteValuationRing O]
  (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]


omit [Algebra ℤ_[l] O] in
theorem length_torsionBy_fracMod (b : O) :
    Module.length O (Submodule.torsionBy O (Selmer.FracMod O K) b) = addVal O b := by
  classical
  let Φ : Matrix (Fin 1) (Fin 1) O := Matrix.of (fun _ _ => b)
  have hdet : Φ.det = b := by simp [Φ, Matrix.det_unique]
  conv_rhs => rw [← hdet]
  rw [← Selmer.length_kernel_fraction_module_eq_addVal_det (K := K) Φ]
  let e : (Fin 1 → Selmer.FracMod O K) ≃ₗ[O] Selmer.FracMod O K := LinearEquiv.funUnique (Fin 1) O _
  have hmap : (Selmer.H1c Φ (Selmer.FracMod O K)).map (e : (Fin 1 → Selmer.FracMod O K) →ₗ[O] Selmer.FracMod O K) =
      Submodule.torsionBy O (Selmer.FracMod O K) b := by
    ext x
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_torsionBy_iff]
    simp only [Selmer.H1c, LinearMap.mem_ker]
    constructor
    · intro hx
      have h0 := congrFun hx 0
      rw [Selmer.coefMap_apply] at h0
      simpa [Φ, e] using h0
    · intro hx
      funext i
      rw [Selmer.coefMap_apply]
      simpa [Φ, e] using hx
  rw [← hmap]
  exact ((e.submoduleMap _).length_eq).symm

theorem length_twistInvOver_of_eq {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ} (h : nu l U tr = n) :
    Module.length O (twistInvOver l O (Selmer.FracMod O K) U tr) = n * addVal O (l : O) := by
  rw [twistInvOver_eq_torsionBy _ h, length_torsionBy_fracMod K, addVal_pow, nsmul_eq_mul]

theorem length_twistInvOver (hl : ¬ IsUnit (l : O)) (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) :
    Module.length O (twistInvOver l O (Selmer.FracMod O K) U tr) =
      nu l U tr * addVal O (l : O) := by
  by_cases htop : nu l U tr = ⊤
  · have hv : addVal O (l : O) ≠ 0 := by
      rw [Ne, addVal_eq_zero_iff]
      exact hl
    rw [htop, ENat.top_mul hv, ENat.eq_top_iff_forall_ge]
    intro m
    have hle : Submodule.torsionBy O (Selmer.FracMod O K) ((l : O) ^ m) ≤
        twistInvOver l O (Selmer.FracMod O K) U tr :=
      torsionBy_pow_le_twistInvOver _ (by rw [htop]; exact le_top)
    calc (m : ℕ∞) ≤ (m : ℕ∞) * addVal O (l : O) :=
          le_mul_of_one_le_right (by positivity) (ENat.one_le_iff_ne_zero.mpr hv)
      _ = Module.length O (Submodule.torsionBy O (Selmer.FracMod O K) ((l : O) ^ m)) := by
          rw [length_torsionBy_fracMod K, addVal_pow, nsmul_eq_mul]
      _ ≤ _ := Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [length_twistInvOver_of_eq K hn.symm, ← hn]

end KStar.TotallyRealRoots
end

section

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem gr_enough [CharZero E] (i : ℕ) :
    HasEnoughRootsOfUnity (AlgebraicClosure E) (l ^ i) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  infer_instance

theorem eps_mem_princ_iff [CharZero E] (g : Gal(AlgebraicClosure E/E)) (n : ℕ) :
    eps l E g ∈ princ l n ↔ ∀ ζ : AlgebraicClosure E, ζ ^ l ^ n = 1 → g ζ = ζ := by
  haveI := fun i => gr_enough (l := l) (E := E) i
  set L := AlgebraicClosure E
  set σ : L ≃+* L := MulSemiringAction.toRingAut Gal(L/E) L g with hσ
  have hσg : ∀ x : L, σ x = g x := fun x => rfl
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity L (l ^ n)
  have key : eps l E g ∈ princ l n ↔
      (modularCyclotomicCharacter L hn σ : ZMod (l ^ n)) = 1 := by
    rw [← cyclotomicCharacter.toZModPow]
    simp only [princ, redPow, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
      map_one]
    rfl
  have hpow : ∀ {M : Type _} [Monoid M] (a : M), a ^ l ^ n = 1 →
      a ^ (1 : ZMod (l ^ n)).val = a := by
    intro M _ a ha
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ha, pow_one]
  rw [key]
  constructor
  · intro h ζ hζ
    have := cyclotomicCharacter.spec l σ ζ hζ
    rw [cyclotomicCharacter.toZModPow, h] at this
    rw [← hσg, this, hpow ζ hζ]
  · intro h
    symm
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [mem_rootsOfUnity] at ht
    have ht' : (t : L) ^ l ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    rw [hpow (t : L) ht', hσg, h _ ht']

theorem isClosed_galImage [CharZero E] : IsClosed (galImage l E : Set ℤ_[l]ˣ) := by
  have hc : Continuous (eps l E) :=
    cyclotomicCharacter.continuous l E (AlgebraicClosure E)
  have : (galImage l E : Set ℤ_[l]ˣ) = Set.range (eps l E) := by
    ext x
    simp [galImage]
  rw [this]
  exact (isCompact_range hc).isClosed

end KStar.TotallyRealRoots
end

section

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem lv_princ_le (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H := by
  intro u hu
  refine mem_levelGroup.mpr ⟨1, H.one_mem, ?_⟩
  rw [map_one]
  exact (MonoidHom.mem_ker.mp hu).symm

private theorem lv_red_surjective : Function.Surjective (red l) := by
  intro v
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (v : ZMod l)
  have hx : PadicInt.toZMod (k : ℤ_[l]) = (v : ZMod l) := by
    rw [map_natCast, hk]
  have hu : IsUnit (k : ℤ_[l]) := by
    by_contra hne
    have hm : (k : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hx] at hm
    exact v.ne_zero hm
  refine ⟨hu.unit, Units.ext ?_⟩
  simp [red, hx]

theorem princ_le_levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H ∧ IsOpen (levelGroup l N H : Set ℤ_[l]ˣ) :=
  ⟨lv_princ_le N H, Subgroup.isOpen_mono (lv_princ_le N H) (isOpen_princ _)⟩

theorem levelGroup_eq_top {N : ℕ} (hN : ¬ l ∣ N) (H : Subgroup (ZMod N)ˣ) :
    levelGroup l N H = ⊤ ∧ resOrder l (levelGroup l N H) = l - 1 := by
  have h : levelGroup l N H = ⊤ := by
    rw [eq_top_iff]
    intro u _
    apply lv_princ_le N H
    rw [mem_princ, Nat.factorization_eq_zero_of_not_dvd hN, pow_zero]
    exact one_dvd _
  refine ⟨h, ?_⟩
  rw [h, resOrder, Subgroup.map_top_of_surjective _ lv_red_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units]

end KStar.TotallyRealRoots
end

section

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem gen_exists_nat {t : ℤ_[l]} (ht : IsUnit t) (d : ℤ_[l]) :
    ∃ j : ℕ, (l : ℤ_[l]) ∣ d + t * j := by
  have htz : PadicInt.toZMod t ≠ 0 := (ht.map PadicInt.toZMod).ne_zero
  refine ⟨(-(PadicInt.toZMod d) * (PadicInt.toZMod t)⁻¹ : ZMod l).val, ?_⟩
  have hm : d + t * ((-(PadicInt.toZMod d) * (PadicInt.toZMod t)⁻¹ : ZMod l).val : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [RingHom.mem_ker, map_add (f := _), map_mul, map_natCast, ZMod.natCast_zmod_val]
    field_simp
    ring
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact hm

private theorem gen_emult {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]}
    (hu : emultiplicity (l : ℤ_[l]) (u - 1) = a) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ l ^ n - 1) = ((a + n : ℕ) : ℕ∞) := by
  have hlp : Prime l := Nat.prime_iff.mp Fact.out
  have h1 : (l : ℤ_[l]) ∣ u - 1 := by
    have := pow_dvd_of_le_emultiplicity (k := 1) (a := (l : ℤ_[l])) (b := u - 1)
      (by rw [hu]; exact_mod_cast ha)
    simpa using this
  by_cases hl : l = 2
  · have h2 : (l : ℤ_[l]) ^ 2 ∣ u - 1 :=
      pow_dvd_of_le_emultiplicity (by rw [hu]; exact_mod_cast ha2 hl)
    rw [emultiplicity_pow_sub_one_sq h2, hu, emultiplicity_pow_self_of_prime hlp]
    push_cast
    rfl
  · rw [emultiplicity_pow_sub_one_odd hl h1, hu, emultiplicity_pow_self_of_prime hlp]
    push_cast
    rfl

private theorem isUnit_padicInt_of_not_dvd {t : ℤ_[l]} (h : ¬ (l : ℤ_[l]) ∣ t) : IsUnit t := by
  by_contra hne
  have hm : t ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact h hm

private theorem exists_pow_eq_one_add_mul_sub_add_sq (v : ℤ_[l]) (j : ℕ) :
    ∃ c : ℤ_[l], v ^ j = 1 + (j : ℤ_[l]) * (v - 1) + (v - 1) ^ 2 * c := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨j + v * c, ?_⟩
    push_cast
    rw [pow_succ, hc]
    ring

private theorem gen_dvd {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]} (hunit : IsUnit u)
    (hu : emultiplicity (l : ℤ_[l]) (u - 1) = a) {x : ℤ_[l]} (hx : (l : ℤ_[l]) ^ a ∣ x - 1)
    (n : ℕ) : ∃ k : ℕ, (l : ℤ_[l]) ^ (a + n) ∣ u ^ k - x := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [pow_zero, add_zero]
    have : (1 : ℤ_[l]) - x = -(x - 1) := by ring
    rw [this]
    exact (dvd_neg).mpr hx
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨d, hd⟩ := hk
    set v := u ^ l ^ n with hvdef
    have hv := gen_emult ha ha2 hu n
    have hvd : (l : ℤ_[l]) ^ (a' + 1 + n) ∣ v - 1 :=
      pow_dvd_of_le_emultiplicity (le_of_eq hv.symm)
    obtain ⟨t, ht⟩ := hvd
    have htu : IsUnit t := by
      apply isUnit_padicInt_of_not_dvd
      rintro ⟨s, hs⟩
      have hdv : (l : ℤ_[l]) ^ (a' + 1 + n + 1) ∣ v - 1 := ⟨s, by rw [ht, hs]; ring⟩
      have := le_emultiplicity_of_pow_dvd hdv
      rw [hv] at this
      norm_cast at this
      omega
    obtain ⟨j, e, he⟩ := gen_exists_nat ((hunit.pow k).mul htu) d
    obtain ⟨c, hc⟩ := exists_pow_eq_one_add_mul_sub_add_sq v j
    refine ⟨k + l ^ n * j, e + (l : ℤ_[l]) ^ (a' + n) * u ^ k * t ^ 2 * c, ?_⟩
    rw [pow_add, pow_mul, ← hvdef]
    linear_combination u ^ k * hc + hd + ((u ^ k) * j + u ^ k * c *
      (v - 1 + (l : ℤ_[l]) ^ (a' + 1 + n) * t)) * ht + (l : ℤ_[l]) ^ (a' + 1 + n) * he

theorem exists_pow_redPow_eq {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]ˣ}
    (hu : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a) {x : ℤ_[l]ˣ} (hx : x ∈ princ l a) (b : ℕ) :
    ∃ k : ℕ, redPow l b (u ^ k) = redPow l b x := by
  rw [mem_princ] at hx
  obtain ⟨k, hk⟩ := gen_dvd ha ha2 u.isUnit hu hx b
  refine ⟨k, Units.ext ?_⟩
  have hkb : (l : ℤ_[l]) ^ b ∣ (u : ℤ_[l]) ^ k - x :=
    (pow_dvd_pow _ (Nat.le_add_left b a)).trans hk
  have hm : (u : ℤ_[l]) ^ k - x ∈ RingHom.ker (PadicInt.toZModPow b : ℤ_[l] →+* ZMod (l ^ b)) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact hkb
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  simpa [redPow] using hm

theorem princ_le_of_isClosed {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {U : Subgroup ℤ_[l]ˣ}
    (hU : IsClosed (U : Set ℤ_[l]ˣ)) {u : ℤ_[l]ˣ} (huU : u ∈ U)
    (hu : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a) : princ l a ≤ U := by
  intro x hx
  refine mem_of_isClosed hU fun b => ?_
  obtain ⟨k, hk⟩ := exists_pow_redPow_eq ha ha2 hu hx b
  exact ⟨u ^ k, U.pow_mem huU k, hk⟩

end KStar.TotallyRealRoots
end

section

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nf_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem nf_exists_unit {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

private theorem nf_mem_princ {a s : ℕ} (h : s ≤ a) {u : ℤ_[l]ˣ}
    (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) : u ∈ princ l s := by
  rw [mem_princ, hu]
  exact pow_dvd_pow _ h

private theorem nf_emult {a : ℕ} {u : ℤ_[l]ˣ} (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) :
    emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
  rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]

theorem nu_ne_top {U : Subgroup ℤ_[l]ˣ} (hU : IsOpen (U : Set ℤ_[l]ˣ)) {tr : ℕ} (htr : tr ≠ 0) :
    nu l U tr ≠ ⊤ := by
  obtain ⟨s, h⟩ := (isOpen_iff_princ_le U).mp hU
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (a := s + 2) (by omega)
  have hm : u ∈ U := h (nf_mem_princ (by omega) hu)
  have h1 : (l : ℤ_[l]) ^ 2 ∣ (u : ℤ_[l]) - 1 := by
    rw [hu]
    exact pow_dvd_pow _ (by omega)
  have := nf_nu_le hm tr
  rw [emultiplicity_pow_sub_one_sq h1, nf_emult hu,
    ← padicValNat_eq_emultiplicity htr, ← Nat.cast_add] at this
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) this

end KStar.TotallyRealRoots
end
