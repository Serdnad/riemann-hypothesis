module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDecNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle009
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

local instance (priority := 2000) fieldAlgebraIsTorsionFreeForLevelCohomologyBundle011 (K Ω : Type)
    [Field K] [Field Ω] [Algebra K Ω] : Module.IsTorsionFree K Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.locTors : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ n : ℤ, n ≠ 0 → n ≠ 1 → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 k) ∉ v.asIdeal → ∀ z : G k Ω → O, Coc (ψ * chiO k Ω l O ^ n) z → Alg.AdicCont (maximalIdeal O) z → CobOn (ψ * chiO k Ω l O ^ n) z (Dec (F := k) A) := by
  intro lf lt le k Ω _ _ _ _ _ l hl O _ _ _ _ _ ψ ho n h0 h1 v A hA hv z hz hc
  haveI : CharZero O := charZero_of_injective_algebraMap (dvrFacts l O).1
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hlm : (l : O) ∈ maximalIdeal O := by
    haveI := (dvrFacts l O).2.2.1
    rw [← map_natCast (algebraMap ℤ_[l] O)]
    exact map_nonunit _ _ PadicInt.p_nonunit
  obtain ⟨B, hB⟩ := So.locKill lf lt le k Ω l O ψ ho n h0 h1 v A hA hv
  obtain ⟨g, hg, hne⟩ := So.decNe k Ω l O ψ ho n h0 v A hA
  obtain ⟨a, ha, m, hm⟩ := So.cobLim O (Dec (F := k) A) ((ψ * chiO k Ω l O ^ n).comp (Dec (F := k) A).subtype) l B hl0 hlm
    ⟨⟨g, hg⟩, hne⟩ (fun r => hB _ _ _ (isLev_lev (pow_ne_zero r hl0) _)) (fun g => z g) (fun g h => hz g h)
    fun N => (hc N).comp_continuous continuous_subtype_val
  exact ⟨a, ha, m, fun g hg => hm ⟨g, hg⟩ trivial⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.vanOf :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (γ : G ℚ Ω →* kˣ), (∀ z : G ℚ Ω → k, ML.IsCoc γ z → UnrEv l γ z → ∃ m : k, ∀ g, z g = (γ g : k) * m - m) → ∀ (T : Finset ℕ) (pl : ℕ → ValuationSubring Ω) (K : Subgroup (G ℚ Ω)), (∀ p ∈ T, p.Prime ∧ (pl p).valuation (p : Ω) < 1) → K.Normal → ¬ l ∣ K.index → Van T pl K γ := by
  intro Ω _ _ _ l _ k _ γ hL T pl K hT hKn hKl z hzlc hzc hzI hzD
  have hlp : l.Prime := Fact.out
  have hz1 : z 1 = 0 := by
    have h := hzc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    simpa using h
  have hconj : ∀ g x, (γ x : k) = 1 → z (g⁻¹ * x * g) = (γ g⁻¹ : k) * z x := by
    intro g x hx
    have h0 : z g⁻¹ + (γ g⁻¹ : k) * z g = 0 := by rw [← hzc, inv_mul_cancel, hz1]
    rw [mul_assoc, hzc, hzc, hx]
    linear_combination h0
  apply hL z ⟨hzlc, fun g h => by rw [hzc, smul_eq_mul]⟩
  intro A
  by_cases hA : ∀ p ∈ T, ¬ A.valuation (p : Ω) < 1
  · refine ⟨K, fun h => hKl (dvd_trans h (Subgroup.relIndex_dvd_index_of_normal _ _)), ?_⟩
    intro g hgK hgA _
    exact hzI A hA g hgA hgK
  · push_neg at hA
    obtain ⟨p, hpT, hAp⟩ := hA
    obtain ⟨hpp, hplp⟩ := hT p hpT
    obtain ⟨m, hm⟩ := hzD p hpT
    obtain ⟨g, hg⟩ := (B3.placesQ Ω).2.2 p (pl p) A hpp hplp hAp
    refine ⟨⊤, by rw [Subgroup.relIndex_top_left]; exact hlp.not_dvd_one, ?_⟩
    intro x _ hxA hγx
    have hγx' : (γ x : k) = 1 := by rw [hγx, Units.val_one]
    have hγc : (γ (g⁻¹ * x * g) : k) = 1 := by simp [map_mul, hγx]
    have hin : g⁻¹ * x * g ∈ Dec (pl p) := Ine_le_Dec (pl p) (hg x hxA)
    have h1 := hm _ hin
    rw [hconj g x hγx', hγc, one_mul, sub_self] at h1
    exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero _)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem sq_neg_one {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) :
    χ ((-1 : ℤ) : ZMod N) ^ 2 = 1 := by
  have h : ((-1 : ℤ) : ZMod N) ^ 2 = 1 := by
    push_cast
    exact neg_one_sq
  first
    | rw [← map_pow, h, map_one]
    | rw [sq, ← χ.map_mul, ← sq, h, χ.map_one]

private theorem pow_app {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) (a : ℤ)
    (ha : IsCoprime a (N : ℤ)) : (χ ^ k) (a : ZMod N) = χ a ^ k := by
  obtain ⟨u, v, huv⟩ := ha
  have h := congrArg (fun x : ℤ => (x : ZMod N)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
    Int.cast_one] at h
  rw [← show ((⟨_, _, (mul_comm _ _).trans h, h⟩ : (ZMod N)ˣ) : ZMod N) = ((a : ℤ) : ZMod N) from rfl]
  exact MulChar.pow_apply_coe χ k _

theorem UpperTheory.V.X.dirData :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ → ∀ q : ℕ, UnitaryThreeInertia.XData l ψ q → ∀ ω : DirichletCharacter c.O l, ω ^ (l - 1) = 1 → ∃ (d f n : ℕ) (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ ∧ f * 2 ^ n ∣ l * N * N ∧ ∀ a : ℤ, IsCoprime a (l * N * N : ℕ) → prodX φ ξ a = (ω a ^ e * psi2 ψ a * th1 l ψ a) ^ 2 * ((ZMod.χ₄ a : ℤ) : c.O) := by
  intro l hl c N iN e ψ o₁ hD q hX ω hω
  have hl2 : l ≠ 2 := hD.l_odd
  have h4l : 4 ≤ c2 ψ := hD.four_le
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨hq0, hq, hb⟩ := hX
  obtain ⟨-, -, hcod, hf0, hfour, hth, hl1⟩ := UpperTheory.V.X.th1Facts c.O N ψ l hl.out hl2
  obtain ⟨-, -, -, h2c, h2N, -⟩ := UpperTheory.V.HV.compCond c.O N ψ 2 Nat.prime_two
  obtain ⟨ξ, hξp, hξ⟩ :=
    UpperTheory.V.X.xiSq c.O two_ne_zero N (psi2 ψ) (c2 ψ) h4l h2c.symm
  obtain ⟨f, φ, hφp, hfd, hφo, hφ⟩ :=
    UpperTheory.V.X.primProd c.O l N ((ω ^ e) ^ 2) (th1 l ψ ^ 2)
  have hdiv : f * 2 ^ (c2 ψ - 1) ∣ l * N * N :=
    mul_dvd_mul (dvd_trans hfd (mul_dvd_mul_left l (DirichletCharacter.conductor_dvd_level _)))
      (dvd_trans (pow_dvd_pow 2 (Nat.sub_le _ 1)) h2N)
  have unitOf : ∀ (m : ℕ) (a : ℤ), IsCoprime a (m : ℤ) → IsUnit ((a : ZMod m)) := by
    rintro m a ⟨u, v, huv⟩
    have h := congrArg (fun x : ℤ => (x : ZMod m)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
      Int.cast_one] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  refine ⟨f0 l ψ, f, c2 ψ - 1, φ, ξ, ?_, hdiv, ?_⟩
  · have hT : ((ω ^ e) ^ 2) ^ (l ^ f0 l ψ - 1) = 1 := by
      obtain ⟨t, ht⟩ := hl1
      calc ((ω ^ e) ^ 2) ^ (l ^ f0 l ψ - 1) = (ω ^ (l - 1)) ^ (e * 2 * t) := by
            rw [ht, ← pow_mul, ← pow_mul, ← pow_mul]
            congr 1
            ring
        _ = 1 := by rw [hω, one_pow]
    have hT2 : (th1 l ψ ^ 2) ^ (l ^ f0 l ψ - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hth, one_pow]
    refine ⟨hf0, hfour, ?_, hφp, orderOf_dvd_of_pow_eq_one (hφo _ hT hT2), hξp, ?_, ?_⟩
    · exact Odd.of_dvd_nat ((hl.out.odd_of_ne_two hl2).mul hcod) hfd
    · have hfle : f ≤ l * q :=
        Nat.le_of_dvd (Nat.mul_pos hl.out.pos hq0) (dvd_trans hfd (mul_dvd_mul_left l hq))
      have h2 : 2 ^ c2 ψ = 2 * 2 ^ (c2 ψ - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hb' : 2 * (l * q * 4 ^ (l ^ f0 l ψ - 1).factorization 2) ≤ 2 * 2 ^ (c2 ψ - 1) := by
        rw [← mul_assoc, ← h2]
        exact hb
      exact le_trans (Nat.mul_le_mul_right _ hfle) (Nat.le_of_mul_le_mul_left hb' two_pos)
    · have hc1 : IsCoprime (-1 : ℤ) ((l * N : ℕ) : ℤ) := isCoprime_one_left.neg_left
      have hc2 : IsCoprime (-1 : ℤ) (N : ℤ) := isCoprime_one_left.neg_left
      have hm1 : IsCoprime (-1 : ℤ) (l : ℤ) := isCoprime_one_left.neg_left
      have e1 := hφ (-1) hc1
      have e2 := hξ (-1) hc2
      rw [pow_app _ _ _ hm1, pow_app _ _ _ hm1, pow_app _ _ _ hc2] at e1
      have hw : (ω ((-1 : ℤ) : ZMod l) ^ e) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, sq_neg_one, one_pow]
      rw [hw, sq_neg_one, one_mul] at e1
      rw [sq_neg_one, one_mul] at e2
      have h4 : ZMod.χ₄ ((-1 : ℤ) : ZMod 4) = -1 := by
        first
          | decide
          | rfl
          | simp
      have n1 : (-1 : ZMod f) = ((-1 : ℤ) : ZMod f) := by simp
      have n2 : (-1 : ZMod (2 ^ (c2 ψ - 1))) = ((-1 : ℤ) : ZMod (2 ^ (c2 ψ - 1))) := by simp
      rw [n1, n2, e1, e2, h4]
      simp
  · intro a ha
    have haN : IsCoprime a (N : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (dvd_mul_left N (l * N)))
    have halN : IsCoprime a ((l * N : ℕ) : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (dvd_mul_right (l * N) N))
    have hal : IsCoprime a (l : ℤ) :=
      ha.of_isCoprime_of_dvd_right
        (Int.natCast_dvd_natCast.2 (dvd_trans (dvd_mul_right l N) (dvd_mul_right (l * N) N)))
    have had : IsCoprime a ((f * 2 ^ (c2 ψ - 1) : ℕ) : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hdiv)
    obtain ⟨u, hu⟩ := unitOf _ a had
    rw [UpperTheory.V.X.prodX, MulChar.coeToFun_mul, Pi.mul_apply, ← hu,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (R := ZMod f) (Dvd.intro _ rfl : f ∣ f * 2 ^ (c2 ψ - 1)) a,
      ZMod.cast_intCast (R := ZMod (2 ^ (c2 ψ - 1)))
        (Dvd.intro_left _ rfl : 2 ^ (c2 ψ - 1) ∣ f * 2 ^ (c2 ψ - 1)) a,
      hφ a halN, hξ a haN, pow_app _ _ _ hal, pow_app _ _ _ hal, pow_app _ _ _ haN]
    ring
end
