module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcCycKFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle004
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
public import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hth_place (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring
    (Ideal.span {(⟨(p : Ω), natCast_mem _ p⟩ : (⊥ : Subring Ω))}) (by
      intro h
      rw [Ideal.span_singleton_eq_top] at h
      obtain ⟨⟨b, hb⟩, hb1⟩ := isUnit_iff_exists_inv.mp h
      obtain ⟨n, rfl⟩ := Subring.mem_bot.mp hb
      have h0 : ((p : Ω) * (n : Ω)) = 1 := congrArg Subtype.val hb1
      have h1 : ((p : ℤ) * n : ℤ) = 1 := by exact_mod_cast h0
      have h2 : (p : ℤ) ∣ 1 := ⟨n, h1.symm⟩
      have h3 : p ∣ 1 := by exact_mod_cast h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3))
  exact ⟨B, B.mem_nonunits_iff.mp (hB ⟨_, Ideal.subset_span rfl, rfl⟩)⟩

private theorem hth_spec (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (w : ℕ) [hw : Fact w.Prime]
    (s : G ℚ Ω) (ζ : Ω) (h : ζ ^ w = 1) : s ζ = ζ ^ ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h1 : ζ ^ w ^ 1 = 1 := by rwa [pow_one]
  exact cyclotomicCharacter.spec (L := Ω) w (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ h1

private theorem hth_iff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (w : ℕ) [hw : Fact w.Prime] (s : G ℚ Ω) :
    (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l) ↔
      cycMod ℚ Ω w 1 s ∈ (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero w := ⟨hw.out.ne_zero⟩
  have hred : ∀ (ζ : Ω) (m : ℕ), ζ ^ w = 1 → ζ ^ m = ζ ^ (m % w) := by
    intro ζ m hζ
    conv_lhs => rw [← Nat.mod_add_div m w, pow_add, pow_mul, hζ, one_pow, mul_one]
  have hcv : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val < w :=
    lt_of_lt_of_eq (ZMod.val_lt _) (pow_one w)
  have hl0 : l ≠ 0 := hl.out.ne_zero
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω w
    have e1 := ha ζ0 hζ0.pow_eq_one
    rw [hth_spec Ω w s ζ0 hζ0.pow_eq_one, hred ζ0 (a ^ l) hζ0.pow_eq_one] at e1
    have e2 : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val = a ^ l % w :=
      hζ0.pow_inj hcv (Nat.mod_lt _ (Nat.pos_of_neZero w)) e1
    have e3 : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)) = (a : ZMod (w ^ 1)) ^ l := by
      apply ZMod.val_injective
      rw [e2, ← Nat.cast_pow, ZMod.val_natCast, pow_one]
    have hu : IsUnit (a : ZMod (w ^ 1)) := (isUnit_pow_iff hl0).mp (e3 ▸ (cycMod ℚ Ω w 1 s).isUnit)
    exact ⟨hu.unit, Units.ext (by simp [e3])⟩
  · rintro ⟨u, hu⟩
    refine ⟨(u : ZMod (w ^ 1)).val, fun ζ hζ => ?_⟩
    have e : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)) =
        (((u : ZMod (w ^ 1)).val ^ l : ℕ) : ZMod (w ^ 1)) := by
      rw [← hu]
      simp
    rw [hth_spec Ω w s ζ hζ, hred ζ (((u : ZMod (w ^ 1)).val) ^ l) hζ, e, hred ζ _ hζ,
      ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self w one_ne_zero)]

theorem UpperTheory.V.Fr.hth :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] → IsOpen (Hth Ω l w : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ Hth Ω l w ∧ (Hth Ω l w).index = l ∧ (∀ B' : ValuationSubring Ω, ¬ B'.valuation (w : Ω) < 1 → Ine (F := ℚ) B' ≤ Hth Ω l w) ∧ ∀ B' : ValuationSubring Ω, B'.valuation (w : Ω) < 1 → ¬ Ine (F := ℚ) B' ≤ Hth Ω l w := by
  intro Ω _ _ _ l hl w hwp hw1
  haveI hw : Fact w.Prime := ⟨hwp⟩
  haveI : Fact (w ^ 1).Prime := ⟨by rw [pow_one]; exact hwp⟩
  have hmem : ∀ s : G ℚ Ω, s ∈ Hth Ω l w ↔
      cycMod ℚ Ω w 1 s ∈ (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range := by
    intro s
    change (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l) ∧
      (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s⁻¹ ζ = ζ ^ a ^ l) ↔ _
    rw [hth_iff Ω l w s, hth_iff Ω l w s⁻¹, map_inv, inv_mem_iff, and_self]
  have hker : (cycMod ℚ Ω w 1).ker ≤ Hth Ω l w := fun s hs =>
    (hmem s).mpr (by rw [MonoidHom.mem_ker.mp hs]; exact one_mem _)
  have hZ : ∀ s, cycMod ℚ Ω w 1 s = KStar.TotallyRealRoots.redPow w 1 (cycZ ℚ Ω w s) := fun s => rfl
  obtain ⟨A, hA⟩ := hth_place Ω w hwp
  have hsurj : Function.Surjective (cycMod ℚ Ω w 1) := by
    intro v
    obtain ⟨u, rfl⟩ := KStar.TotallyRealRoots.redPow_surjective (l := w) 1 v
    obtain ⟨σ, -, hσ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω w A hA u
    exact ⟨σ, by rw [hZ, hσ]⟩
  have hidx : (Hth Ω l w).index = l := by
    have hH : Hth Ω l w =
        (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range.comap (cycMod ℚ Ω w 1) := by
      ext s
      exact hmem s
    rw [hH, Subgroup.index_comap_of_surjective _ hsurj, IsCyclic.index_powMonoidHom_range,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hwp]
    exact Nat.gcd_eq_right ((Nat.modEq_iff_dvd' hwp.one_lt.le).mp hw1.symm)
  refine ⟨?_, ?_, hidx, ?_, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (KStar.TotallyRealRoots.princ w 1).comap (cycZ ℚ Ω w)) ?_ ?_
    · intro s hs
      apply hker
      rw [MonoidHom.mem_ker, hZ]
      exact hs
    · exact (contTw ℚ Ω w).1.isOpen_preimage _ (KStar.TotallyRealRoots.isOpen_princ 1)
  · exact (Abelianization.commutator_subset_ker (cycMod ℚ Ω w 1)).trans hker
  · intro B' hB' s hs
    apply hker
    rw [MonoidHom.mem_ker, hZ, MonoidHom.mem_ker.mp ((places ℚ Ω w B').2.2.2 hB' hs), map_one]
  · intro B' hB' hle
    have htop : Hth Ω l w = ⊤ := by
      refine eq_top_iff.mpr fun s _ => ?_
      obtain ⟨u, hu⟩ := KStar.TotallyRealRoots.redPow_surjective (l := w) 1 (cycMod ℚ Ω w 1 s)
      obtain ⟨σ, hσI, hσ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω w B' hB' u
      have h1 := (hmem σ).mp (hle hσI)
      rw [hZ, hσ, hu] at h1
      exact (hmem s).mpr h1
    rw [htop, Subgroup.index_top] at hidx
    exact hl.out.one_lt.ne hidx
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hlay_place (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hmem : (p : Ω) ∈ (⊥ : Subring Ω) := Subring.mem_bot.mpr ⟨p, by simp⟩
  set x : (⊥ : Subring Ω) := ⟨p, hmem⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨b, hb⟩ := Subring.mem_bot.mp (u⁻¹ : (⊥ : Subring Ω)ˣ).1.2
    have h1 : (u : (⊥ : Subring Ω)) * (↑u⁻¹ : (⊥ : Subring Ω)) = 1 := u.mul_inv
    have h2 : ((p : ℤ) * b : ℤ) = (1 : Ω) := by
      have := congrArg Subtype.val h1
      simp only [Subring.coe_mul, Subring.coe_one] at this
      rw [hu] at this
      push_cast
      rw [hb]
      exact this
    have h3 : (p : ℤ) * b = 1 := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ 1 := ⟨b, h3.symm⟩
    have : p ∣ 1 := by exact_mod_cast h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (ValuationSubring.mem_nonunits_iff B).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

private theorem hlay_cop (l : ℕ) [hl : Fact l.Prime] (m : ℕ) : (l ^ m).Coprime (l - 1) := Nat.Coprime.pow_left m ((Nat.coprime_self_sub_right hl.out.one_le).mpr (Nat.coprime_one_right _))

private theorem hlay_card (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (h2 : l ≠ 2) :
    Nat.card ((⊤ : Subgroup (ZMod (l ^ (m + 1)))ˣ).map (powMonoidHom (l - 1))) = l ^ m := by
  haveI := ZMod.isCyclic_units_of_prime_pow l hl.out h2 (m + 1)
  rw [← MonoidHom.range_eq_map, IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ hl.out]
  have hpos : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  rw [Nat.gcd_comm, Nat.gcd_mul_left_right]
  exact Nat.mul_div_cancel _ hpos

private theorem hlay_inf {l : ℕ} [hl : Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) (h1 : u ∈ KStar.TotallyRealRoots.princ l 1)
    (h : KStar.TotallyRealRoots.redPow l (m + 1) u ^ (l - 1) = 1) : KStar.TotallyRealRoots.redPow l (m + 1) u = 1 := by
  set x := KStar.TotallyRealRoots.redPow l (m + 1) u with hx
  have hd : l ^ 1 ∣ l ^ (m + 1) := pow_dvd_pow l (by omega)
  set f := ZMod.unitsMap hd
  have hfx : f x = 1 := by
    have : f x = KStar.TotallyRealRoots.redPow l 1 u := by
      ext
      simp only [f, hx, ZMod.unitsMap, KStar.TotallyRealRoots.redPow, Units.coe_map, MonoidHom.coe_coe]
      exact congrArg (fun g => g (u : ℤ_[l])) (PadicInt.zmod_cast_comp_toZModPow 1 (m + 1) (by omega))
    rw [this]
    exact h1
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective hd
  have hcardG : Nat.card (ZMod (l ^ (m + 1)))ˣ = l ^ m * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl.out]
  have hcardH : Nat.card (ZMod (l ^ 1))ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out]
  have hker : Nat.card f.ker = l ^ m := by
    have e := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcardH, hcardG] at e
    exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hl.out.one_lt) e
  have hpow : x ^ (l ^ m) = 1 := by
    have := pow_card_eq_one' (G := f.ker) (x := ⟨x, hfx⟩)
    rw [hker] at this
    exact congrArg Subtype.val this
  have hdvd : orderOf x ∣ Nat.gcd (l ^ m) (l - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one h)
  rw [hlay_cop l m, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact hdvd

theorem UpperTheory.V.Fr.hlay :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (m : ℕ), l ≠ 2 → IsOpen (Hlay Ω l m : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ Hlay Ω l m ∧ (Hlay Ω l m).index = l ^ m ∧ Hlay Ω l m ⊓ (cycMod ℚ Ω l 1).ker = (cycMod ℚ Ω l (m + 1)).ker ∧ (∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → Ine (F := ℚ) B' ≤ Hlay Ω l m) ∧ ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → (Hlay Ω l m).relIndex (Ine (F := ℚ) B') = l ^ m ∧ ∀ r, (Ine (F := ℚ) B').map (cycMod ℚ Ω l r) = ⊤ := by
  intro Ω _ _ _ l _ m h2
  obtain ⟨A, hA⟩ := hlay_place Ω l Fact.out
  have hsurjIne : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 →
      ∀ r, (Ine (F := ℚ) B').map (cycMod ℚ Ω l r) = ⊤ := by
    intro B' hB' r
    rw [eq_top_iff]
    rintro y -
    obtain ⟨v, rfl⟩ := KStar.TotallyRealRoots.redPow_surjective (l := l) r y
    obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B' hB' v
    exact ⟨σ, hσ, by rw [← hσv]; rfl⟩
  have hidx : ∀ K : Subgroup (G ℚ Ω), K.map (cycMod ℚ Ω l (m + 1)) = ⊤ →
      (Hlay Ω l m).relIndex K = l ^ m := by
    intro K hK
    have hsub : (Hlay Ω l m).subgroupOf K = ((cycMod ℚ Ω l (m + 1) ^ (l - 1)).comp K.subtype).ker := by
      ext x
      rfl
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
    have hr : ((cycMod ℚ Ω l (m + 1) ^ (l - 1)).comp K.subtype).range =
        (⊤ : Subgroup (ZMod (l ^ (m + 1)))ˣ).map (powMonoidHom (l - 1)) := by
      ext y
      simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_top, true_and, MonoidHom.comp_apply,
        Subgroup.coe_subtype, MonoidHom.pow_apply, powMonoidHom_apply]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨z, rfl⟩
        have hz : z ∈ K.map (cycMod ℚ Ω l (m + 1)) := hK ▸ Subgroup.mem_top z
        obtain ⟨k, hk, rfl⟩ := hz
        exact ⟨⟨k, hk⟩, rfl⟩
    rw [hr]
    exact hlay_card l m h2
  have hcont := (UpperTheory.V.Base.contTw ℚ Ω l).1
  have hkerle : (cycMod ℚ Ω l (m + 1)).ker ≤ Hlay Ω l m := by
    intro σ hσ
    show (cycMod ℚ Ω l (m + 1) σ) ^ (l - 1) = 1
    rw [MonoidHom.mem_ker.mp hσ, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun B' hB' => ⟨hidx _ (hsurjIne B' hB' _), hsurjIne B' hB'⟩⟩
  · apply Subgroup.isOpen_mono hkerle
    have hset : ((cycMod ℚ Ω l (m + 1)).ker : Set (G ℚ Ω)) =
        cycZ ℚ Ω l ⁻¹' (KStar.TotallyRealRoots.princ l (m + 1) : Set ℤ_[l]ˣ) := by
      ext σ
      rfl
    rw [hset]
    exact (KStar.TotallyRealRoots.isOpen_princ (m + 1)).preimage hcont
  · exact Abelianization.commutator_subset_ker _
  · rw [← Subgroup.relIndex_top_right]
    exact hidx ⊤ (top_unique ((hsurjIne A hA _).symm.le.trans (Subgroup.map_mono le_top)))
  · apply le_antisymm
    · rintro σ ⟨h1, h1'⟩
      exact hlay_inf m (cycZ ℚ Ω l σ) h1' h1
    · intro σ hσ
      exact ⟨hkerle hσ, KStar.TotallyRealRoots.princ_anti (by omega) hσ⟩
  · intro B' hB'
    refine ((UpperTheory.V.Base.places ℚ Ω l B').2.2.2 hB').trans ?_
    intro σ hσ
    apply hkerle
    show KStar.TotallyRealRoots.redPow l (m + 1) (cycZ ℚ Ω l σ) = 1
    rw [MonoidHom.mem_ker.mp hσ, map_one]
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem so_cls {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (s : G ℚ Ω) :
    Chr.cls ℚ Ω (l ^ 1) s = cycMod ℚ Ω l 1 s := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  refine (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s _ (fun ζ hζ => ?_)
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ

theorem UpperTheory.V.Fr.sc_om :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l], Af.KillsMu l (omO Ω l O) ∧ ∀ σ : G ℚ Ω, IsCC σ → omO Ω l O σ = -1 := by
  intro Ω _ _ _ l _ O _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact (Fact.out : l.Prime).one_lt⟩
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycMod ℚ Ω l 1 s = 1 := by
      rw [← so_cls]
      refine (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s 1 (fun ζ hζ => ?_)
      rw [pow_one] at hζ
      rw [hs ζ hζ, Units.val_one, ZMod.val_one, pow_one]
    simp only [omO, GC.cycF, MonoidHom.comp_apply, h1, map_one]
  · have h1 : cycMod ℚ Ω l 1 σ = -1 := by
      rw [← so_cls]
      exact (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.1 σ hσ
    simp only [omO, GC.cycF, MonoidHom.comp_apply, h1]
    ext
    simp
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := ‹CharP (ResidueField O) l›
  haveI hp : PerfectRing (ResidueField O) l := inferInstance
  haveI : PerfectRing (O ⧸ maximalIdeal O) l := hp
  let f : (O ⧸ maximalIdeal O) →* O := (Perfection.teichmuller l (maximalIdeal O)).comp
    (Perfection.liftMonoidHom l (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) (MonoidHom.id _))
  refine ⟨f, fun x => ?_⟩
  have h := Perfection.mk_teichmuller (p := l) (I := maximalIdeal O)
    (Perfection.liftMonoidHom l (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) (MonoidHom.id _) x)
  exact h.trans (Perfection.coeffMonoidHom_zero_liftMonoidHom l (MonoidHom.id _) x)

theorem UpperTheory.V.Fr.sc_teich :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l], Finite (ResidueField c.O) → ∃ T : (ResidueField c.O)ˣ →* (Qbar l)ˣ, Function.Injective T ∧ ∀ (u : c.Oˣ) (j : ℕ) (s : G ℚ Ω), ‖(GlobalTheory.GalOfCusp.cycBar ℚ Ω l s ^ j * T (Units.map (residue c.O).toMonoidHom u * (omO Ω l c.O s ^ j)⁻¹)).val - u.val.1‖ < 1 := by
  intro Ω _ _ _ l _ c _ hfin
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (dvrFacts l c.O).2.2.2.1
  obtain ⟨τ, hτ⟩ := teich_ex l c.O
  let ι : c.O →* Qbar l := c.O.val.toRingHom.toMonoidHom
  refine ⟨Units.map (ι.comp τ), ?_, ?_⟩
  · intro x y hxy
    have h1 : ((Units.map (ι.comp τ) x).val) = (Units.map (ι.comp τ) y).val := by rw [hxy]
    have h2 : τ x.val = τ y.val := Subtype.ext h1
    apply Units.ext
    rw [← hτ x.val, ← hτ y.val, h2]
  · intro u j s
    have hω : ((omO Ω l c.O s).val : ResidueField c.O) = residue c.O (chiO ℚ Ω l c.O s).val :=
      (UpperTheory.V.X.cycKFacts Ω l (ResidueField c.O)).2 c (residue c.O) s
    have hc : (GlobalTheory.GalOfCusp.cycBar ℚ Ω l s).val = ((chiO ℚ Ω l c.O s).val : PadicAlgCl l) := rfl
    set w : (ResidueField c.O)ˣ := Units.map (residue c.O).toMonoidHom u * (omO Ω l c.O s ^ j)⁻¹
    have key : (chiO ℚ Ω l c.O s).val ^ j * τ w.val - u.val ∈ maximalIdeal c.O := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residue c.O _ = 0
      rw [map_sub, map_mul, map_pow, hτ, ← hω]
      simp only [w, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.coe_map, MonoidHom.coe_coe]
      have hne : ((omO Ω l c.O s).val : ResidueField c.O) ^ j ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
      rw [mul_left_comm, mul_inv_cancel₀ hne, mul_one]
      exact sub_self _
    have hn := ((sc_norm l c _).2.1 key)
    convert hn using 2
    simp [Units.val_mul, Units.val_pow_eq_pow_val, hc, ι]
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem ax_cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    {s : G ℚ Ω} (hs : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  apply Units.ext
  show PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val) = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ l = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).1 ht)
    simpa using this
  have hl1 : l ^ 1 ≠ 1 := by
    have := hl.out.one_lt
    rw [pow_one]
    omega
  rw [ZMod.val_one'' hl1, pow_one]
  exact hs _ ht'

theorem UpperTheory.V.Fr.auxw_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ Q : ℕ, Q ≠ 0 → ∃ w, FrobeniusWitnessPrime l η Ψ M w ∧ w ≡ 1 [MOD Q] := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ
  obtain ⟨a, hη, hbar⟩ := hG.cyc
  have hM := hG.M_ne
  have hlM := hG.l_dvd
  have hL : M ^ (a + 1) * Q ≠ 0 := mul_ne_zero (pow_ne_zero _ hM) hQ
  obtain ⟨w, hw, hwgt, hw1⟩ := Nat.exists_prime_gt_modEq_one (M ^ (a + 1) * Q) hL
  have hMaL : M ^ a ∣ M ^ (a + 1) * Q := Dvd.dvd.mul_right (pow_dvd_pow M (Nat.le_succ a)) Q
  have hlL : l ∣ M ^ (a + 1) * Q :=
    dvd_trans hlM (dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _))
  have hML : M ∣ M ^ (a + 1) * Q := dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _)
  have hndvd : ∀ m, m ∣ M ^ (a + 1) * Q → ¬ w ∣ m := by
    intro m hm hwm
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hm
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL hm)) hwm
    omega
  refine ⟨w, ⟨hw, hndvd M hML, Nat.ModEq.of_dvd hlL hw1, ?_⟩, Nat.ModEq.of_dvd (dvd_mul_left Q _) hw1⟩
  intro B' hB' s hs
  haveI := Fact.mk hw
  have fix : ∀ m, m ∣ M ^ (a + 1) * Q → ∀ ζ : Ω, ζ ^ m = 1 → s ζ = ζ := by
    intro m hm
    have hcop : m.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).2 (hndvd m hm)).symm
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w B' hB' m hcop s hs
    intro ζ hζ
    rw [hk ζ hζ]
    have hwk : w ^ k ≡ 1 [MOD m] := by
      have := (Nat.ModEq.of_dvd hm hw1).pow k
      rwa [one_pow] at this
    rw [pow_eq_pow_mod _ hζ, show w ^ k % m = 1 % m from hwk, ← pow_eq_pow_mod 1 hζ, pow_one]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact hη s (fix _ hMaL)
  · exact hbar s (fix _ hMaL)
  · rw [MonoidHom.mem_ker]
    change (Units.map _) ((cycMod ℚ Ω l 1) s) = 1
    rw [ax_cycMod_one l (fix l hlL), map_one]
end
