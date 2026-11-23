module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.GenLeOfFintype
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
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
public import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem vg_ne {Γ : Type} [LinearOrderedCommGroupWithZero Γ] : (0 : Γ) < 1 := by
  refine lt_of_le_of_ne zero_le' fun h => ?_
  obtain ⟨x, y, hxy⟩ := (GroupWithZero.toNontrivial (G₀ := Γ)).exists_pair_ne
  exact hxy (by rw [← mul_one x, ← mul_one y, ← h, mul_zero, mul_zero])

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => rw [pow_zero, sub_self, map_zero]; exact vg_ne
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  have h10 : (1 : A.ValueGroup) ≠ 0 := vg_ne.ne'
  exact A.valuation.map_sum_lt h10 fun i _ => power_bounds_of_between A (aux_one A hm hη) h i

private theorem ine_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) (ζ : Ω) (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have h1 := aux_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hζ
    exact zero_ne_one hζ
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine root_of_unity_eq_one_of_close_residue A hm hv (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, h1, div_one]; exact hg.2 ζ h1.le
  exact (div_eq_one_iff_eq h0).1 this

private theorem val_nat_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (natCast_mem A n)

private theorem act_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) (n : ℕ) (s : G ℚ Ω) :
    ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → (s ^ n) ζ = ζ ^ a ^ n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero w := ⟨hw⟩
  haveI : NeZero (w : Ω) := ⟨Nat.cast_ne_zero.2 hw⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω w
  obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one (ξ := s z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  have h1 : ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a := fun ζ h => by
    obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one h
    rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨a, fun ζ h => ?_⟩
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h1 ζ h, ← pow_mul, pow_succ']

private theorem pow_mem_Upl {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    {Hb H₀ : Subgroup (G ℚ Ω)} {w : ℕ} (hw : w ≠ 0) (hab : commutator (G ℚ Ω) ≤ Hb) (hidx : ∃ a : ℕ, Hb.index = l ^ a) (m : ℕ) :
    ∃ N : ℕ, ∀ s ∈ H₀, s ^ l ^ N ∈ Upl l Hb H₀ w m := by
  obtain ⟨a, ha⟩ := hidx
  haveI : Hb.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by group
    rw [this]
    exact Hb.mul_mem (hab (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))) hn⟩
  refine ⟨1 + a + m, fun s hs => ⟨⟨⟨H₀.pow_mem hs _, ?_⟩, ?_⟩, ?_⟩⟩
  · have : s ^ l ∈ Hth Ω l w := ⟨act_pow hw l s, by
      show ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → (s ^ l)⁻¹ ζ = ζ ^ a ^ l
      rw [← inv_pow]; exact act_pow hw l s⁻¹⟩
    rw [add_assoc, pow_add, pow_one, pow_mul]
    exact Subgroup.pow_mem _ this _
  · have : s ^ l ^ a ∈ Hb := ha ▸ Hb.pow_index_mem s
    rw [add_comm 1 a, add_assoc, pow_add, pow_mul]
    exact Subgroup.pow_mem _ this _
  · have : s ^ l ^ m ∈ Hlay Ω l m := by
      have hl : l.Prime := Fact.out
      haveI : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      show (cycMod ℚ Ω l (m + 1) ^ (l - 1)) (s ^ l ^ m) = 1
      rw [MonoidHom.pow_apply, map_pow, ← pow_mul, ← Nat.totient_prime_pow_succ hl, ← ZMod.card_units_eq_totient]
      exact pow_card_eq_one
    rw [add_comm (1 + a) m, pow_add, pow_mul]
    exact Subgroup.pow_mem _ this _

private theorem core {Γ k : Type} [Group Γ] [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (κ : Γ →* kˣ)
    (U H₀ E : Subgroup Γ) (hU : ∃ N : ℕ, ∀ s ∈ H₀, s ^ l ^ N ∈ U) (h2 : H₀.index = 2) (t : Γ) (ht : t ∉ H₀) (htE : t ∈ E)
    (hκ : κ t = 1) (h : ∀ s ∈ U ⊓ E, κ s = 1) : ∀ s ∈ E, κ s = 1 := by
  obtain ⟨N, hN⟩ := hU
  have h0 : ∀ s ∈ H₀, s ∈ E → κ s = 1 := fun s hs hE => by
    have h1 := h _ ⟨hN s hs, E.pow_mem hE _⟩
    rw [map_pow] at h1
    have h3 : (κ s : k) ^ l ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have h4 : ((κ s : k) - 1) ^ l ^ N = 0 := by rw [sub_pow_char_pow, h3, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h4))
  intro s hs
  by_cases hH : s ∈ H₀
  · exact h0 s hH hs
  · have := h0 (s * t) ((Subgroup.mul_mem_iff_of_index_two h2).2 (by simp [hH, ht])) (E.mul_mem hs htE)
    rwa [map_mul, hκ, mul_one] at this

theorem UpperTheory.V.Fr.l15 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (H₀ : Subgroup (G ℚ Ω)) (w : ℕ), FrobeniusSplitPrimeDatum η M H₀ → FrobeniusWitnessPrime l η Ψ M w → ∀ (m : ℕ) (i j : ℤ), ((∀ s ∈ Upl l Hb H₀ w m, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) → ∀ s, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) ∧ ((∀ s ∈ Upl l Hb H₀ w m, omO Ω l O s ^ i * barChar O Ψ s ^ j = etaO O η s) → ∀ s, omO Ω l O s ^ i * barChar O Ψ s ^ j = etaO O η s) ∧ ((∀ s ∈ Upl l Hb H₀ w m ⊓ η.ker, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) → ∀ s ∈ η.ker, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) := by
  intro Ω _ _ _ l hl O _ _ _ η Ψ σ B M Hb hG H₀ w h0 hW m i j
  have hU := pow_mem_Upl l (H₀ := H₀) hW.prime.ne_zero hG.Hb_ab hG.Hb_idx m
  obtain ⟨A, hA, hI⟩ := h0.ram
  obtain ⟨t, ht, htH⟩ := SetLike.not_le_iff_exists.1 hI
  obtain ⟨a, ka, kb⟩ := hG.cyc
  have hM1 : A.valuation (M : Ω) = 1 := le_antisymm (val_nat_le A M) (not_lt.1 hA)
  have hMa : ¬ A.valuation ((M ^ a : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hM1, one_pow]; exact lt_irrefl _
  have hfix := ine_fix A (pow_ne_zero a hG.M_ne) hMa ht
  have hη : η t = 1 := ka t hfix
  have hΨ : barChar O Ψ t = 1 := kb t hfix
  have hlv : ¬ A.valuation (l : Ω) < 1 := fun h => hA (by
    obtain ⟨c, rfl⟩ := hG.l_dvd
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_nat_le A c)) h)
  have hω : omO Ω l O t = 1 := by
    have h1 : cycZ ℚ Ω l t = 1 := (UpperTheory.V.Base.places ℚ Ω l A).2.2.2 hlv ht
    simp [GC.cycF, cycMod, h1]
  have he : etaO O η t = 1 := by simp [hη]
  let κ : G ℚ Ω →* (ResidueField O)ˣ := omO Ω l O ^ i * barChar O Ψ ^ j
  have hκ : ∀ s, κ s = omO Ω l O s ^ i * barChar O Ψ s ^ j := fun s => by simp [κ]
  have hκt : κ t = 1 := by rw [hκ, hω, hΨ]; simp
  refine ⟨fun h s => ?_, fun h s => ?_, fun h s hs => ?_⟩
  · rw [← hκ]
    exact core l κ _ H₀ ⊤ hU h0.idx t htH trivial hκt (fun s hs => by rw [hκ]; exact h s hs.1) s trivial
  · have := core l (κ * (etaO O η)⁻¹) _ H₀ ⊤ hU h0.idx t htH trivial
      (by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκt, he]; simp)
      (fun s hs => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκ, h s hs.1, mul_inv_cancel]) s trivial
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκ] at this
    exact mul_inv_eq_one.1 this
  · rw [← hκ]
    exact core l κ _ H₀ η.ker hU h0.idx t htH hη hκt (fun s hs => by rw [hκ]; exact h s hs) s hs
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem galois_sqrt_sign {Ω : Type} [Field Ω] [CharZero Ω] (s : G ℚ Ω) {x : Ω} {n : ℤ} (hx : x ^ 2 = n) :
    s x = x ∨ s x = -x := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [← map_pow, hx, map_intCast]

private theorem decomposition_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {x : Ω} {k : ℤ}
    (hx : x ^ 2 = ((1 + 4 * k : ℤ) : Ω)) (hk : B.valuation (k : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) B) : s x = x := by
  refine (galois_sqrt_sign s hx).resolve_right fun h => ?_
  set y : Ω := (1 + x) / 2 with hy
  have h1 : s y = 1 - y := by rw [hy, map_div₀, map_add (f := _), map_one, h, map_ofNat]; ring
  have h2 : y * (1 - y) = -k := by
    push_cast at hx
    rw [hy]; linear_combination (-1 / 4 : Ω) * hx
  have h3 : B.valuation (1 - y) < 1 ↔ B.valuation y < 1 := by rw [← h1]; exact valuation_apply_lt_one_iff hs y
  have h4 : B.valuation y < 1 := by
    by_contra h5
    have h6 : 1 ≤ B.valuation (y * (1 - y)) := by
      rw [map_mul]; exact one_le_mul (not_lt.1 h5) (not_lt.1 (h3.not.2 h5))
    rw [h2, Valuation.map_neg] at h6
    exact absurd hk (not_lt.2 h6)
  have h7 := B.valuation.map_add_lt h4 (h3.2 h4)
  have hy' : y + (1 - y) = 1 := by ring
  rw [hy', map_one] at h7
  exact lt_irrefl _ h7

private theorem etaleSimplicialCochain_scheme_section_extension_naturality {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {p n : ℕ} (hp : B.valuation (p : Ω) < 1)
    (h : p.Coprime n) : ¬ B.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hm : ∀ (c : ℤ) (z : Ω), B.valuation z < 1 → B.valuation (c * z) < 1 := fun c z hz => by
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))).trans_lt hz
  have := B.valuation.map_add_lt (hm a _ hp) (hm b _ hn)
  rw [e, map_one] at this
  exact lt_irrefl _ this

private theorem inertia_fixes_sqrt_discriminant {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {δ : Ω} {D : ℕ}
    (hδ : δ ^ 2 = -(D : Ω)) (hD : ¬ B.valuation ((4 * D : ℕ) : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) : s δ = δ := by
  refine (galois_sqrt_sign s (n := -D) (by rw [hδ]; simp)).resolve_right fun h => hD ?_
  have h1 : B.valuation δ ≤ 1 := by
    have : B.valuation δ ^ 2 ≤ 1 := by
      rw [← map_pow, hδ, Valuation.map_neg]; exact (B.valuation_le_one_iff _).2 (natCast_mem B D)
    exact (pow_le_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h2 := hs.2 δ h1
  have e : ((4 * D : ℕ) : Ω) = -((s δ - δ) ^ 2) := by rw [h]; push_cast; linear_combination (4 : Ω) * hδ
  rw [e, Valuation.map_neg, map_pow]
  exact pow_lt_one₀ zero_le' h2 two_ne_zero

private theorem gauss_sqrt_inertia_negates {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 3)
    (B : ValuationSubring Ω) (hB : B.valuation (p : Ω) < 1) :
    ∃ x : Ω, x ^ 2 = -(p : Ω) ∧ ∃ s ∈ Ine (F := ℚ) B, s x = -x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  have h2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  let ψ := AddChar.zmodChar p hζ.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Ω)
  have hχ : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).2 (quadraticChar_ne_one h2)
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hm : χ (-1) = -1 := by
    show ((quadraticChar (ZMod p) (-1) : ℤ) : Ω) = -1
    rw [quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]; simp
  have hmem : (-1 : (ZMod p)ˣ) ∈ (Ine (F := ℚ) B).map (B1.cycN ℚ Ω p) := by
    rw [B1.cycIne Ω p p B hB, B3.pPart, MonoidHom.mem_ker]
    have : ordCompl[p] p = 1 := by rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
    have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨s, hs, hs'⟩ := hmem
  refine ⟨gaussSum χ ψ, by rw [gaussSum_sq hχ hq hψ, hm, ZMod.card]; simp, s, hs, ?_⟩
  have h3 := gaussSum_mulShift χ ψ (-1)
  rw [Units.val_neg, Units.val_one, hm, neg_one_mul, neg_eq_iff_eq_neg] at h3

  rw [← h3, gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul]
  congr 1
  · exact map_intCast s _
  · have h5 : ψ a ^ p = 1 := by rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    rw [B1.cycN_spec ℚ Ω p s h5, hs', ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, AddChar.mulShift_apply]
    simp

private theorem complex_conjugation_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] {τ : G ℚ Ω} (h : IsCC τ) {z : Ω} {n : ℕ} (hn : 0 < n)
    (hz : z ^ 2 = n) : τ z = z := by
  refine (galois_sqrt_sign τ (n := n) (by rw [hz]; simp)).resolve_right fun h1 => ?_
  obtain ⟨j, hj⟩ := h
  have h2 : starRingEnd ℂ (j z) = -j z := by rw [← map_neg, ← h1]; exact (hj z).symm
  have h3 := Complex.mul_conj (j z)
  rw [h2, mul_neg, ← sq, ← map_pow, hz, map_natCast] at h3
  have h4 : -(n : ℝ) = Complex.normSq (j z) := by exact_mod_cast h3
  have h5 := Complex.normSq_nonneg (j z)
  have h6 : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

theorem UpperTheory.V.Fr.exists_twistCharacter_continuousCohomology :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∃ H₀, FrobeniusSplitPrimeDatum η M H₀ := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  have hM := hG.M_ne
  obtain ⟨p, hlt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (4 * D + M) (q := 4 * M) (a := -1) (by omega)
    isCoprime_one_left.neg_left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hmod.dvd
  have ht' : -(p : ℤ) = 1 + 4 * (M * t) := by push_cast at ht; linear_combination ht
  obtain ⟨A, hA⟩ := (B3.placesQ Ω).1 p hp
  obtain ⟨x, hx, s, hs, hsx⟩ := gauss_sqrt_inertia_negates p (by omega) A hA
  have hsδ : s δ = δ := inertia_fixes_sqrt_discriminant A hδ (etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime (by omega) (by omega) hp)) hs
  have hz : (δ * x) ^ 2 = ((D * p : ℕ) : Ω) := by rw [mul_pow, hδ, hx]; push_cast; ring
  have hpos : 0 < D * p := Nat.mul_pos hD hp.pos
  have hz0 : δ * x ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero] at hz
    exact hpos.ne (by exact_mod_cast hz)
  have hne : -(δ * x) ≠ δ * x := fun h => hz0 (by linear_combination (-1 / 2 : Ω) * h)
  have hsz : s (δ * x) = -(δ * x) := by rw [map_mul, hsδ, hsx, mul_neg]
  have hmem : ∀ g : G ℚ Ω, g ∈ MulAction.stabilizer (G ℚ Ω) (δ * x) ↔ g (δ * x) = δ * x := fun g => Iff.rfl
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  refine ⟨MulAction.stabilizer (G ℚ Ω) (δ * x), stabilizer_isOpen_of_isIntegral _, ?_, fun τ hτ => complex_conjugation_fixes_sqrt hτ hpos hz,
    fun B' hB' => ?_, A, etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime hM (by omega) hp), fun h => hne (hsz.symm.trans (h hs))⟩
  · refine Subgroup.index_eq_two_iff.2 ⟨s, fun b => ?_⟩
    rw [hmem, hmem, AlgEquiv.mul_apply, hsz, map_neg]
    rcases galois_sqrt_sign b (n := (D * p : ℕ)) (hz.trans (Int.cast_natCast _).symm) with h | h
    · rw [h]; exact Or.inr ⟨rfl, hne⟩
    · rw [h, neg_neg]; exact Or.inl ⟨rfl, hne⟩
  · have hk : B'.valuation ((M * t : ℤ) : Ω) < 1 := by
      rw [Int.cast_mul, Int.cast_natCast, map_mul]
      exact mul_lt_one_of_lt_of_le hB' ((B'.valuation_le_one_iff _).2 (intCast_mem B' t))
    ext g
    refine and_congr_right fun hg => ?_
    have hgx : g x = x := decomposition_fixes_sqrt B' (by rw [← ht', hx]; simp) hk hg
    show g (δ * x) = δ * x ↔ η g = 1
    rw [map_mul, hgx, hη]
    rcases Int.units_eq_one_or (η g) with h | h
    · simp [h]
    · rw [h]
      refine iff_of_false (fun h' => hne ?_) (by decide)
      simpa using h'
end
