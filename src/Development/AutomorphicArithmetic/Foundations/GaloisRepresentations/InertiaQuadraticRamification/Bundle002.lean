module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem relIndex_ker_prime {Γ : Type} [Group Γ] (H H' : Subgroup Γ) (s : Γ →* ℂˣ) (p : ℕ) (hp : p.Prime)
    (hH' : ∀ g, g ∈ H' ↔ g ∈ H ∧ s g = 1) (hs : ∀ g ∈ H, s g ^ p = 1) (τ : Γ) (hτ : τ ∈ H) (hτs : s τ ≠ 1) :
    (H'.relIndex H).Prime := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f : H →* ℂˣ := s.comp H.subtype
  have hker : f.ker = H'.subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hH']
    simp [f]
  have hidx : H'.relIndex H = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hle : f.range ≤ rootsOfUnity p ℂ := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact hs g g.2
  have hcard : Nat.card (rootsOfUnity p ℂ) = p := by
    exact Complex.card_rootsOfUnity p
  have hdvd : Nat.card f.range ∣ p := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard] at this
  have hne : Nat.card f.range ≠ 1 := by
    intro h1
    have hbot : f.range = ⊥ := by
      haveI : Finite (rootsOfUnity p ℂ) := inferInstance
      exact (Subgroup.eq_bot_iff_card _).2 h1
    have : f ⟨τ, hτ⟩ ∈ f.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hτs this
  rw [hidx]
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact absurd h hne
  · rwa [h]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.groupStep :
    GroupStep := by
  intro Γ _ Gd P D Pl Dc I hI hinf hmono hpsi hstep H₀ r hH₀ hP hr n hn hrn
  have hpowk : ∀ (s : Γ →* ℂˣ) (k : ℕ), Gd s.ker → Gd (s ^ k).ker := by
    intro s k hs
    refine hmono _ _ (fun g hg => ?_) hs
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.pow_apply, hg, one_pow]
  have key : ∀ n : ℕ, 0 < n → ∀ r : Γ →* ℂˣ, Gd r.ker → P (H₀ ⊓ (r ^ n).ker) →
      ∃ r' : Γ →* ℂˣ, Gd r'.ker ∧ (∀ g ∈ D, r' g = r g) ∧ P (H₀ ⊓ r'.ker) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn r hr hP
      rcases Nat.lt_or_ge 1 n with h1 | h1
      swap
      · have hn1 : n = 1 := by omega
        subst hn1
        exact ⟨r, hr, fun _ _ => rfl, by simpa using hP⟩
      obtain ⟨p, hp, n', rfl⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      have hn' : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hlt : n' < p * n' := by
        have := hp.two_le
        nlinarith
      obtain ⟨ψ, hψk, hψn, hψD, u, hDc, τ, hτ, hτo⟩ := hpsi (H₀ ⊓ r.ker) (hinf _ _ hH₀ hr) (p * n') hn
      have hr1 : Gd (r * ψ).ker := by
        refine hmono _ _ (fun g hg => ?_) (hinf _ _ hr hψk)
        have h1 : r g = 1 := hg.1
        have h2 : ψ g = 1 := hg.2
        rw [MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]
      have hr1n : (r * ψ) ^ (p * n') = r ^ (p * n') := by
        rw [mul_pow, hψn, mul_one]
      have hτU : τ ∈ H₀ ⊓ r.ker := hDc (hI u hτ)
      have hτr : r τ = 1 := hτU.2
      have hGH : Gd (H₀ ⊓ (r ^ (p * n')).ker) := hinf _ _ hH₀ (hpowk _ _ hr)
      have hGH' : Gd (H₀ ⊓ ((r * ψ) ^ n').ker) := hinf _ _ hH₀ (hpowk _ _ hr1)
      have hval : ∀ g, ((r * ψ) ^ n') g ^ p = (r ^ (p * n')) g := by
        intro g
        rw [← hr1n, MonoidHom.pow_apply, MonoidHom.pow_apply, ← pow_mul, mul_comm n' p]
      have hle : H₀ ⊓ ((r * ψ) ^ n').ker ≤ H₀ ⊓ (r ^ (p * n')).ker := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        have h1 : ((r * ψ) ^ n') g = 1 := hg.2
        show (r ^ (p * n')) g = 1
        rw [← hval, h1, one_pow]
      have hUH : H₀ ⊓ r.ker ≤ H₀ ⊓ (r ^ (p * n')).ker := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        have h1 : r g = 1 := hg.2
        show (r ^ (p * n')) g = 1
        rw [MonoidHom.pow_apply, h1, one_pow]
      have hτs : ((r * ψ) ^ n') τ ≠ 1 := by
        intro h
        rw [MonoidHom.pow_apply, MonoidHom.mul_apply, hτr, one_mul] at h
        have := Nat.le_of_dvd hn' (orderOf_dvd_of_pow_eq_one h)
        omega
      have hprime : ((H₀ ⊓ ((r * ψ) ^ n').ker).relIndex (H₀ ⊓ (r ^ (p * n')).ker)).Prime := by
        refine relIndex_ker_prime _ _ ((r * ψ) ^ n') p hp (fun g => ?_) (fun g hg => ?_) τ (hUH hτU) hτs
        · constructor
          · intro hg
            exact ⟨hle hg, hg.2⟩
          · rintro ⟨hg, hs⟩
            exact ⟨hg.1, hs⟩
        · have h1 : (r ^ (p * n')) g = 1 := hg.2
          rw [hval, h1]
      have hP' : P (H₀ ⊓ ((r * ψ) ^ n').ker) :=
        hstep _ _ u hGH hGH' hP hle hprime (fun x hx => hUH (hDc hx))
          ⟨τ, hτ, fun h => hτs h.2⟩
      obtain ⟨r', h1, h2, h3⟩ := ih n' hlt hn' (r * ψ) hr1 hP'
      refine ⟨r', h1, fun g hg => ?_, h3⟩
      rw [h2 g hg, MonoidHom.mul_apply, hψD g hg, mul_one]
  refine key n hn r hr ?_
  rw [hrn, MonoidHom.ker_one, inf_top_eq]
  exact hP
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.powChar :
    PowChar := by
  intro p _ n hn hdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨ω, hωc⟩ := hprim.isUnit hn.ne'
  have hωp : IsPrimitiveRoot ω n := by
    rw [← IsPrimitiveRoot.coe_units_iff, hωc]
    exact hprim
  have hωo : orderOf ω = n := hωp.eq_orderOf.symm
  have hnd : n ∣ p - 1 := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hdvd
  have hd : orderOf ω ∣ orderOf g := by rw [hωo, hog]; exact hnd
  let lam : (ZMod p)ˣ →* ℂˣ := monoidHomOfForallMemZpowers hg hd
  have hlg : lam g = ω := monoidHomOfForallMemZpowers_apply_gen hg hd
  have hωn : ω ^ n = 1 := hωp.pow_eq_one
  have hpow : ∀ a, (lam a) ^ n = 1 := by
    intro a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    rw [map_zpow, hlg, ← zpow_natCast, zpow_comm, zpow_natCast, hωn, one_zpow]
  refine ⟨lam, ?_, ?_, ?_⟩
  · ext1 a
    rw [MonoidHom.pow_apply, hpow, MonoidHom.one_apply]
  · obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        omega
      · exact h
    have hx2 : (g ^ (n * c)) ^ 2 = 1 := by
      rw [← pow_mul, show n * c * 2 = p - 1 by rw [hc]; ring, ← hog, pow_orderOf_eq_one]
    have hx1 : g ^ (n * c) ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hog, hc] at h1
      have h2 := Nat.le_of_dvd (Nat.mul_pos hn hcpos) h1
      have h3 : 0 < n * c := Nat.mul_pos hn hcpos
      nlinarith
    have hxm : g ^ (n * c) = -1 := by
      have h4 : (((g ^ (n * c) : (ZMod p)ˣ)) : ZMod p) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hx2, Units.val_one]
      rw [sq] at h4
      rcases mul_self_eq_one_iff.mp h4 with h | h
      · exact absurd (Units.ext (by rw [h, Units.val_one])) hx1
      · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
    rw [← hxm, map_pow, hlg, pow_mul, hωn, one_pow]
  · intro a ha
    have htop : Subgroup.zpowers a = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, ha, hcard]
    have hga : g ∈ Subgroup.zpowers a := by rw [htop]; trivial
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hga
    have hωa : (lam a) ^ j = ω := by rw [← map_zpow, hlg]
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hpow a))
    rw [← hωo]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hωa, ← zpow_natCast, zpow_comm, zpow_natCast, pow_orderOf_eq_one, one_zpow]
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normVal :
    NormVal := by
  intro Ω _ _ _ U hU q hq
  classical
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U with hK
  have hfix : K.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩
  have hfin : FiniteDimensional ℚ K := by
    rw [← InfiniteGalois.isOpen_iff_finite, hfix]
    exact hU
  have hq0 : q ≠ 0 := by omega
  have hpp : q.minFac.Prime := Nat.minFac_prime (by omega)
  haveI : Fact q.minFac.Prime := ⟨hpp⟩
  have ha : 0 < padicValNat q.minFac q := by
    rw [Nat.padicValNat_def]
    exact one_le_multiplicity_of_dvd hq0 (Nat.minFac_dvd q)
  refine ⟨Module.finrank ℚ K * padicValNat q.minFac q, Nat.mul_pos Module.finrank_pos ha, ?_⟩
  intro z n c hz hzq
  rcases n with _ | k
  · have h1 : ((q ^ c : ℕ) : Ω) = ((1 : ℕ) : Ω) := by simpa using hzq
    have h2 : q ^ c = 1 := Nat.cast_injective h1
    rcases (Nat.pow_eq_one.1 h2) with h | h
    · omega
    · simp [h]
  have hzK : z ∈ K := (IntermediateField.mem_fixedField_iff U z).2 hz
  set w : K := ⟨z, hzK⟩ with hwdef
  have hw : w ^ (k + 1) * (algebraMap ℚ K (q : ℚ)) ^ c = 1 := by
    apply Subtype.ext
    simpa [hwdef] using hzq
  have hN := congrArg (Algebra.norm ℚ) hw
  rw [map_mul, map_pow, map_pow, Algebra.norm_algebraMap, map_one] at hN
  have hNw : Algebra.norm ℚ w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero k), zero_mul] at hN
    exact zero_ne_one hN
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hv := congrArg (padicValRat q.minFac) hN
  rw [padicValRat.mul (pow_ne_zero _ hNw) (pow_ne_zero _ (pow_ne_zero _ hqQ)),
    padicValRat.pow, padicValRat.pow, padicValRat.pow, padicValRat.one,
    padicValRat.of_nat] at hv
  have hd : ((k + 1 : ℕ) : ℤ) ∣ ((c * (Module.finrank ℚ K * padicValNat q.minFac q) : ℕ) : ℤ) := by
    refine ⟨-padicValRat q.minFac (Algebra.norm ℚ w), ?_⟩
    rw [Nat.padicValNat_def, Nat.cast_mul, Nat.cast_mul]
    linear_combination hv
  exact Int.natCast_dvd_natCast.1 hd
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private lemma normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show 0 < Nat.card (𝓞 F ⧸ t.asIdeal)
  rw [h]
  exact Nat.pos_of_ne_zero (fun h0 => t.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))

private lemma normV_mem' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show ((Nat.card (𝓞 F ⧸ t.asIdeal) : ℕ) : 𝓞 F) ∈ t.asIdeal
  rw [h]
  exact Ideal.absNorm_mem _

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshPrime :
    SplitPlace → RootMod → FreshPrime := by
  intro hS hR
  unfold SplitPlace at hS
  unfold RootMod at hR
  unfold FreshPrime
  intro F Ω _ _ _ _ _ U hU T hT n hn
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (((2 * n : ℕ)) : Ω) := ⟨by exact_mod_cast (by omega : 2 * n ≠ 0)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 * n)
  have hroot : ∀ t : HeightOneSpectrum (𝓞 F), ∃ x : Ω, x ^ n = (normV t : Ω) :=
    fun t => IsAlgClosed.exists_pow_nat_eq _ hn
  choose y hy using hroot
  set S : Set Ω := insert ζ (y '' T) with hSeq
  haveI : Finite S := (Set.Finite.insert ζ (hT.image y)).to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral)
  set U' : Subgroup (G F Ω) := U ⊓ (IntermediateField.adjoin F S).fixingSubgroup with hU'eq
  have hU' : IsOpen (U' : Set (G F Ω)) := by
    rw [hU'eq, Subgroup.coe_inf]
    exact hU.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hfix : ∀ g : G F Ω, g ∈ U' → ∀ x ∈ S, (g : Ω → Ω) x = x := by
    intro g hg x hx
    have hg2 := (Subgroup.mem_inf.mp hg).2
    exact (mem_fixingSubgroup_iff _).mp hg2 x (IntermediateField.subset_adjoin F S hx)
  have hfinset : ∀ a : 𝓞 F, a ≠ 0 → {w : HeightOneSpectrum (𝓞 F) | a ∈ w.asIdeal}.Finite := by
    intro a ha
    have h0 : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact ha
    simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors h0
  have hcast : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 F) ≠ 0 := fun m hm => by exact_mod_cast hm
  set B : Set (HeightOneSpectrum (𝓞 F)) :=
    T ∪ (⋃ t ∈ T, {w | ((normV t : ℕ) : 𝓞 F) ∈ w.asIdeal}) ∪ {w | ((2 * n : ℕ) : 𝓞 F) ∈ w.asIdeal}
    with hBeq
  have hB : B.Finite := by
    refine (hT.union (hT.biUnion fun t _ => hfinset _ (hcast _ (normV_pos' t).ne'))).union ?_
    exact hfinset _ (hcast _ (by omega))
  obtain ⟨u, huB, hp, hpu, hpu2, hdec⟩ := hS F Ω U' hU' B hB
  have hdvd_mem : ∀ m : ℕ, normV u ∣ m → ((m : ℕ) : 𝓞 F) ∈ u.asIdeal := by
    rintro m ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpu
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω u
  have hDA : ∀ x ∈ S, ∀ g ∈ Dec A, (g : Ω → Ω) x = x := fun x hx g hg => hfix g (hdec A hA hg) x hx
  refine ⟨u, fun h => huB (Or.inl (Or.inl h)), hp, hpu, hpu2,
    fun A' hA' => le_trans (hdec A' hA') inf_le_left, ?_, ?_⟩
  · refine (hR F Ω A u hA (normV u) hp rfl ζ (2 * n) (by omega) (hDA ζ (Set.mem_insert _ _))).2 hζ ?_
    intro h2
    exact huB (Or.inr (hdvd_mem _ h2))
  · intro t ht
    refine ⟨?_, (hR F Ω A u hA (normV u) hp rfl (y t) n hn
      (hDA (y t) (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩))).1 (normV t) (hy t)⟩
    intro hut
    by_cases hd : normV u ∣ normV t
    · exact huB (Or.inl (Or.inr (Set.mem_biUnion ht (hdvd_mem _ hd))))
    · have hcop : Nat.Coprime (normV u) (normV t) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
      have hg := Nat.gcd_eq_gcd_ab (normV u) (normV t)
      rw [hcop] at hg
      have hg' := congrArg (Int.cast : ℤ → 𝓞 F) hg
      push_cast at hg'
      have h1 : (1 : 𝓞 F) ∈ t.asIdeal := by
        rw [hg']
        exact t.asIdeal.add_mem (Ideal.mul_mem_right _ _ hut) (Ideal.mul_mem_right _ _ (normV_mem' t))
      exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem chi_of_pow {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (k : ℕ) (h : g ζ = ζ ^ k) :
    ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p) = (k : ZMod p) := by
  have h1 := hζ.autToPow_spec F g
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨p, (Fact.out : p.Prime).pos, hζ.pow_eq_one⟩
  rw [h, hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h1

private theorem chi_one {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (h : g ζ = ζ) : hζ.autToPow F g = 1 := by
  apply Units.ext
  rw [chi_of_pow hζ g 1 (by rw [h, pow_one])]
  simp

private theorem exists_prim {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] : ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (p : Ω) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω p

private theorem chi_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (j : Ω →+* ℂ) (c : G F Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    hζ.autToPow F c = -1 := by
  have hp := (Fact.out : p.Prime)
  have hw : (j ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw hp.ne_zero
  have hcz : c ζ = ζ ^ (p - 1) := by
    apply j.injective
    rw [hc, ← Complex.inv_eq_conj hn, map_pow]
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hw]
  apply Units.ext
  rw [chi_of_pow hζ c (p - 1) hcz, Nat.cast_sub hp.one_lt.le, ZMod.natCast_self]
  simp

private theorem good_ker {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ}
    [Fact p.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (lam : (ZMod p)ˣ →* ℂˣ) (h1 : lam (-1) = 1) :
    Good (lam.comp (hζ.autToPow F)).ker := by
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  refine ⟨?_, Abelianization.commutator_subset_ker _, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (G F Ω) ζ) ?_
      (stabilizer_isOpen_of_isIntegral (K := F) ζ)
    intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_one hζ g hg, map_one]
  · intro j c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_conj hζ j c hc, h1]

private theorem lam_pow {p n : ℕ} [Fact p.Prime] (lam : (ZMod p)ˣ →* ℂˣ) (hn : lam ^ n = 1) (a : (ZMod p)ˣ) :
    lam a ^ n = 1 := by
  rw [← MonoidHom.pow_apply, hn, MonoidHom.one_apply]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshChar :
    PowChar → InertiaGen → DecPow → FreshPrime → FreshChar := by
  intro hPow hIG hDP hFP F Ω _ _ _ _ _ U hU T hT n hn
  obtain ⟨u, huT, hpr, hpu, hpu2, hdec, hdvd, hTt⟩ := hFP F Ω U hU T hT n hn
  haveI : Fact (Nat.Prime (normV u)) := ⟨hpr⟩
  obtain ⟨lam, hlamn, hlam1, hlamord⟩ := hPow (normV u) n hn hdvd
  obtain ⟨ζ, hζ⟩ := exists_prim (F := F) (Ω := Ω) (normV u)
  refine ⟨lam.comp (hζ.autToPow F), good_ker hζ lam hlam1, ?_, ?_, u, huT, hpr, ?_, ?_⟩
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, lam_pow lam hlamn, MonoidHom.one_apply]
  · intro t ht A hA g hg
    obtain ⟨hpt, b, hb⟩ := hTt t ht
    obtain ⟨hD, -⟩ := hDP F Ω A t hA (normV u) hpr hpt ζ hζ
    obtain ⟨k, hk⟩ := hD g hg
    have hχ := chi_of_pow hζ g _ hk
    push_cast at hχ
    rw [← hb] at hχ
    rw [MonoidHom.comp_apply]
    by_cases hb0 : b = 0
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [pow_zero] at hχ
        rw [show hζ.autToPow F g = 1 from Units.ext (by simpa using hχ), map_one]
      · exfalso
        rw [hb0, zero_pow hn.ne', zero_pow hk0.ne'] at hχ
        exact (Units.ne_zero _) hχ
    · have hunit : hζ.autToPow F g = (Units.mk0 b hb0) ^ (n * k) :=
        Units.ext (by rw [hχ]; simp [pow_mul])
      rw [hunit, map_pow, pow_mul, lam_pow lam hlamn, one_pow]
  · intro A hA
    refine ⟨hdec A hA, ?_⟩
    obtain ⟨τ, hτ, a, ha, hτz⟩ := hIG F Ω A u hA (normV u) hpu hpu2 ζ hζ
    refine ⟨τ, hτ, ?_⟩
    have hχ := chi_of_pow hζ τ _ hτz
    rw [ZMod.natCast_zmod_val] at hχ
    rw [MonoidHom.comp_apply, show hζ.autToPow F τ = a from Units.ext hχ]
    exact hlamord a ha
  · intro t A hA hpt τ hτ
    obtain ⟨-, hI⟩ := hDP F Ω A t hA (normV u) hpr hpt ζ hζ
    rw [MonoidHom.comp_apply, chi_one hζ τ (hI τ hτ), map_one]
end
