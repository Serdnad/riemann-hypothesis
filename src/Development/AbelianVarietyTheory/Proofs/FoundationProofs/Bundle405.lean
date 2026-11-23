module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle356
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle393
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
import Formalism.PieriBlockIdeals.BlockIdealBound5Derived

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem dual_classes_unbounded : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ¬ GrZero W A → ∃ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) ∧ ∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s) := by
  intro hL l _ Ω _ _ _ e S A W hN hG
  obtain ⟨y, hyZ, hyU, hyG, hyB⟩ : ∃ y ∈ Z1 (Loc.colRep W), Unr W y ∧ Gr W A y ∧
      y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by
    unfold GrZero at hG; push_neg at hG; exact hG
  have hcol : ∀ s (x : Fin 2 → Qbar l), Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  obtain ⟨c0, hc0⟩ := hN.int
  obtain ⟨c, k, hle, hYi, hYu, -, hYg⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c0 y hN.cont hc0 hN.unr hyZ hyU A
  have hW : ∀ s i j, mat W s i j ∈ c.O := fun s i j => hle (hc0 s i j)
  obtain ⟨Y, hY⟩ : ∃ Y : G ℚ Ω → Fin 2 → Qbar l, Y = fun s => ((l : ℕ) : Qbar l) ^ k • y s := ⟨_, rfl⟩
  have hYs : ∀ s, Y s = ((l : ℕ) : Qbar l) ^ k • y s := fun s => by rw [hY]
  have hYZ : Y ∈ Z1 (Loc.colRep W) := by
    have : Y = ((l : ℕ) : Qbar l) ^ k • y := by rw [hY]; rfl
    rw [this]; exact (Z1 _).smul_mem _ hyZ
  have hYcoc : ∀ s t, Y (s * t) = Y s + mat W s *ᵥ Y t := fun s t => by
    rw [hYZ.2 s t, hcol]
  have hYI : ∀ s i, Y s i ∈ c.O := fun s i => by
    rw [hYs, Pi.smul_apply, smul_eq_mul]; exact hYi s i
  have hl0 : ((l : ℕ) : Qbar l) ^ k ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hYB : Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by
    intro h; apply hyB
    rw [mem_coboundaries1] at h ⊢
    obtain ⟨x, hx⟩ := h
    refine ⟨(((l : ℕ) : Qbar l) ^ k)⁻¹ • x, fun g => ?_⟩
    have h1 := hx g
    rw [hYs] at h1
    rw [map_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  obtain ⟨k0, hk0⟩ := GlobalTheory.T.nonzero_class_bounded_torsion l Ω W c Y hW hYZ hYI hYB
  have hY0 : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
    refine GlobalTheory.T.cocycle_vanishes_on_ker_toGS_of_inertia_coboundary l Ω e S A W Y hN hYZ fun q hq B hB => ?_
    have hlq : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal := fun h => hq (hN.above q h)
    obtain ⟨x, -, hx⟩ := hYu q hlq B hB
    exact ⟨x, fun s hs => by rw [hYs]; exact hx s hs⟩
  refine ⟨c, hW, fun m => ?_⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.greenbergWiles_dualSelmer_lower_bound_mod_prime_pow hL l Ω e S A W hN c hW
  obtain ⟨B, hB⟩ := GlobalTheory.T.card_primePowTorsion_selmerClassesModPrimePow_bounded l Ω e S A W hN c hW (GlobalTheory.T.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded_alt hL l Ω e S A W hN c hW) m
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = C * B + 1 := ⟨_, rfl⟩
  have hlt : C * B < l ^ t := by
    have := Nat.lt_pow_self (Fact.out : l.Prime).one_lt (n := t)
    omega
  have hCv : ∀ {n : ℕ} (a b : Fin 2 → Qbar l), a = b → Cv n a b := fun a b h i => by
    subst h; simp [Cg]
  let yF : Fin (l ^ t) → G ℚ Ω → Fin 2 → Qbar l := fun j s => ((j : ℕ) : Qbar l) • Y s
  have hjO : ∀ j : Fin (l ^ t), ((j : ℕ) : Qbar l) ∈ c.O := fun j => natCast_mem _ _
  have hsel : ∀ j, GwCount.SelN c (t + k0) S A W (yF j) := by
    intro j
    refine ⟨⟨?_, fun s i => ?_, fun s _ r _ => hCv _ _ ?_⟩, fun a ha => hCv _ _ ?_, fun q _ hlq => ?_, ?_⟩
    · exact (hYZ.1.const_smul ((j : ℕ) : Qbar l)).continuousOn
    · simp only [yF, Pi.smul_apply, smul_eq_mul]; exact mul_mem (hjO j) (hYI s i)
    · simp only [yF]; rw [hYcoc, smul_add, Matrix.mulVec_smul]
    · simp only [yF]; rw [hY0 a ha, smul_zero]
    · obtain ⟨x, hxO, hx⟩ := hYu q hlq (placeOf Ω q) (isPlaceOver_placeOf Ω q)
      refine ⟨placeOf Ω q, isPlaceOver_placeOf Ω q, ((j : ℕ) : Qbar l) • x, fun i => ?_, fun s hs => hCv _ _ ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_mem (hjO j) (hxO i)
      · simp only [yF]; rw [hYs, hx s hs, Matrix.mulVec_smul, smul_sub]
    · obtain ⟨x, hxO, hx⟩ := hYg hyG
      refine ⟨((j : ℕ) : Qbar l) * x, mul_mem (hjO j) hxO, fun s hs => ?_⟩
      have h1 : yF j s 1 = ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) := by
        simp only [yF, Pi.smul_apply, smul_eq_mul]; rw [hYs, Pi.smul_apply, smul_eq_mul, hx s hs]
      have h2 : ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) = mat W s 1 1 * (((j : ℕ) : Qbar l) * x) - ((j : ℕ) : Qbar l) * x := by ring
      rw [h1, h2]; simp [Cg]
  have hne : ∀ i j, i ≠ j → ¬ Cob1 c (t + k0) W ⊤ (yF i - yF j) := by
    intro i j hij h
    have e1 : yF i - yF j = fun s => ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : Qbar l) • Y s := by
      funext s; simp only [yF, Pi.sub_apply]; push_cast; rw [sub_smul]
    rw [e1] at h
    have hd := hk0 (t + k0) _ (intCast_mem _ _) h
    refine GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow l t k0 (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ?_ ?_ hd
    · intro h0; apply hij; ext; omega
    · have hi := i.2; have hj := j.2
      have : ((l ^ t : ℕ) : ℤ) = (l : ℤ) ^ t := by push_cast; rfl
      rw [← this, abs_lt]; constructor <;> omega
  obtain ⟨N', z, hNC, hzS, hzne⟩ := hC (t + k0) (by omega) (l ^ t) yF hsel hne
  have hex : ∃ i, ¬ Cob1 c (t + k0) (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s) := by
    by_contra h
    push_neg at h
    have h1 := hB (t + k0) N' z hzS hzne h
    have h2 : C * N' ≤ C * B := Nat.mul_le_mul_left C h1
    omega
  obtain ⟨i, hi⟩ := hex
  obtain ⟨h1, h2, h3, h4⟩ := hzS i
  exact ⟨t + k0, z i, h1, h2, h3, h4, hi⟩

end GlobalTheory.Ord2.GwCount
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.DescInv

theorem gamma_anti {a b : ℕ} (h : a ∣ b) :
    CongruenceSubgroup.Gamma b ≤ CongruenceSubgroup.Gamma a := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have key : ∀ (x : ℤ) (c : ZMod b), (x : ZMod b) = c → (x : ZMod a) = ZMod.castHom h (ZMod a) c := by
    intro x c hx; rw [← hx, map_intCast]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key _ _ h1, map_one]
  · simpa using key _ _ h2
  · simpa using key _ _ h3
  · rw [key _ _ h4, map_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem lev_of_dvd {X : Tower Ω ε} {a b : ℕ} (h : a ∣ b) {f : X.K} (hf : Lev X a f) : Lev X b f :=
  fun γ hγ => hf γ (gamma_anti h hγ)

theorem exists_dvd_pow_mul_coprime (M : ℕ) (hM : 0 < M) :
    ∀ N : ℕ, 0 < N → ∃ e b : ℕ, 0 < b ∧ Nat.Coprime M b ∧ N ∣ M ^ e * b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN
  by_cases hc : Nat.Coprime M N
  · exact ⟨0, N, hN, hc, by simp⟩
  · have hd0 : Nat.gcd M N ≠ 0 := (Nat.gcd_pos_of_pos_left N hM).ne'
    have hd1 : 1 < Nat.gcd M N := by
      have : Nat.gcd M N ≠ 1 := hc
      omega
    obtain ⟨N', hN'⟩ := Nat.gcd_dvd_right M N
    have hN'pos : 0 < N' := by
      rcases Nat.eq_zero_or_pos N' with h0 | h0
      · rw [h0, mul_zero] at hN'; omega
      · exact h0
    have hlt : N' < N := by
      rw [hN']; nlinarith
    obtain ⟨e, b, hb, hcop, hdiv⟩ := ih N' hlt hN'pos
    refine ⟨e + 1, b, hb, hcop, ?_⟩
    have : M ^ (e + 1) * b = M * (M ^ e * b) := by ring
    rw [this, hN']
    exact Nat.mul_dvd_mul (Nat.gcd_dvd_left M N) hdiv

end GlobalTheory.KZ.ES.DescInv


open GlobalTheory.KZ.ES.DescInv in
theorem GlobalTheory.KZ.ES.desc_pow_four : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (l n M : ℕ), l.Prime → 0 < M → 6 * l ∣ M → ∀ f : X.Kˣ,
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) →
    ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n M hl hM h6 f hf
  classical
  obtain ⟨M'', hM''pos, hM''⟩ := X.level (f : X.K)
  haveI : NeZero M'' := ⟨hM''pos.ne'⟩

  have hex : ∀ r : SL(2, ZMod M''), ∃ (g : X.Kˣ) (L : ℕ), 0 < L ∧ Lev X L (g : X.K) ∧
      ∀ γ ∈ CongruenceSubgroup.Gamma M,
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ = r →
        X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n) := by
    intro r
    by_cases hr : ∃ γ₀ ∈ CongruenceSubgroup.Gamma M,
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ₀ = r
    · obtain ⟨γ₀, hγ₀, hr0⟩ := hr
      obtain ⟨g, hg⟩ := hf γ₀ hγ₀
      obtain ⟨L, hL, hLg⟩ := X.level (g : X.K)
      refine ⟨g, L, hL, hLg, fun γ _ hrγ => ?_⟩
      have hδ : γ * γ₀⁻¹ ∈ CongruenceSubgroup.Gamma M'' := by
        rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, hrγ, hr0, mul_inv_cancel]
      have hγ : γ = (γ * γ₀⁻¹) * γ₀ := by group
      rw [hγ, map_mul, X.sl_mul, hM'' _ hδ, hg]
    · exact ⟨1, 1, one_pos, fun γ _ => by simp, fun γ hγ hrγ => absurd ⟨γ, hγ, hrγ⟩ hr⟩
  choose G L hLpos hLev hG using hex
  set L₀ : ℕ := ∏ r, L r with hL₀
  have hL₀pos : 0 < L₀ := Finset.prod_pos fun r _ => hLpos r
  have hLdvd : ∀ r, L r ∣ L₀ := fun r => Finset.dvd_prod_of_mem L (Finset.mem_univ r)
  obtain ⟨e, b, hb, hcop, hdiv⟩ := exists_dvd_pow_mul_coprime M hM (M'' * L₀) (Nat.mul_pos hM''pos hL₀pos)
  have hdiv' : M'' * L₀ ∣ M ^ (e + 1) * b :=
    hdiv.trans (Nat.mul_dvd_mul_right (pow_dvd_pow M (Nat.le_succ e)) b)
  have hMa : 0 < M ^ (e + 1) := pow_pos hM _
  have hMMa : M ∣ M ^ (e + 1) := dvd_pow_self M (Nat.succ_ne_zero e)
  have h6a : 6 * l ∣ M ^ (e + 1) := h6.trans hMMa
  have hcopa : Nat.Coprime (M ^ (e + 1)) b := Nat.Coprime.pow_left _ hcop
  have hfLev : Lev X (M ^ (e + 1) * b) (f : X.K) :=
    lev_of_dvd ((dvd_mul_right M'' L₀).trans hdiv') hM''
  have hstep : ∀ γ ∈ CongruenceSubgroup.Gamma (M ^ (e + 1)), ∃ g : X.Kˣ, Lev X (M ^ (e + 1) * b) (g : X.K) ∧
      X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n) := by
    intro γ hγ
    have hγM : γ ∈ CongruenceSubgroup.Gamma M := gamma_anti hMMa hγ
    let r := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ
    exact ⟨G r, lev_of_dvd (((hLdvd r).trans (dvd_mul_left L₀ M'')).trans hdiv') (hLev r), hG r γ hγM rfl⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.classInvariant_descent_coprimeLevel_modPow ε X l n (M ^ (e + 1)) b hl hMa hb h6a hcopa f hfLev hstep
  have hFstep : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ,
      X.sl (ofSL γ) (((f ^ 4 * h ^ (l ^ n) : X.Kˣ)) : X.K) = (f ^ 4 * h ^ (l ^ n) : X.Kˣ) * (g : X.K) ^ (l ^ n) := by
    intro γ hγ
    obtain ⟨g, hg⟩ := hf γ hγ
    have hne : X.sl (ofSL γ) (h : X.K) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (X.sl (ofSL γ)).injective]; exact h.ne_zero
    refine ⟨g ^ 4 * Units.mk0 _ hne * h⁻¹, ?_⟩
    have hh0 : (h : X.K) ≠ 0 := h.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_inv_eq_inv_val, map_mul, map_pow, hg,
      mul_pow, inv_pow]
    have hp : (h : X.K) ^ (l ^ n) ≠ 0 := pow_ne_zero _ hh0
    field_simp
    ring
  obtain ⟨k, h', hh'⟩ := GlobalTheory.T.exists_level_mul_pow_of_invariant_mod_pow ε X l n M (e + 1) hl hM (f ^ 4 * h ^ (l ^ n)) (by simpa using hh) hFstep
  refine ⟨k, h * h', ?_⟩
  convert hh' using 1
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  ring
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

theorem _root_.GlobalTheory.T.approxRoot_fixedField_inertiaCyclotomicKernel : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ x ∈ A) → 0 < v (l : Ω) → v (l : Ω) < 1 → ApproxRoot l v (Fix Ω (ineCyc l A)) := by
  first | (exact @GlobalTheory.RecOne.CycRoots.approxRoot_fix_ineCyc) | (exact GlobalTheory.RecOne.CycRoots.approxRoot_fix_ineCyc) | (intros; apply GlobalTheory.RecOne.CycRoots.approxRoot_fix_ineCyc  <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.EquivCoef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {X : Type} [AddCommGroup X] [Module ℂ X]

def coefL (R : UA E n →* Module.End ℂ X) (F : UA E n → X) : Module.Dual ℂ X →ₗ[ℂ] (UA E n → ℂ) where
  toFun μ := fun g => μ (R g⁻¹ (F g))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFormU_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (X : Type) [AddCommGroup X]
    [Module ℂ X] [FiniteDimensional ℂ X] (R : UA E n →* Module.End ℂ X) (F : UA E n → X),
    (∀ k ∈ finU (E := E) (n := n), R k = 1) → (∀ (u : X) (ℓ : Module.Dual ℂ X), Continuous fun g => ℓ (R g u)) →
    (∀ y ∈ infU E n, ∀ g, F (g * y) = F g) → (∀ γ ∈ ratU E n, ∀ g, F (γ * g) = R γ (F g)) →
    (∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, F (g * y) = F g) →
    ∀ ℓ : Module.Dual ℂ X, IsAutFormU fun g => ℓ (R g⁻¹ (F g)) := by
  intro E _ _ _ n X _ _ _ R F hfin hcont hinf hrat hsm ℓ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA E n => ℓ (R g⁻¹ (F g0)) := (hcont (F g0) ℓ).comp continuous_inv
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g0⁻¹ * g) (𝓝 g0) (𝓝 1) := by
      have : Continuous fun g : UA E n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left] at e
    change ℓ (R g⁻¹ (F g0)) = ℓ (R g⁻¹ (F g))
    rw [e]
  · intro γ hγ g
    change ℓ (R (γ * g)⁻¹ (F (γ * g))) = ℓ (R g⁻¹ (F g))
    rw [hrat γ hγ g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (R γ⁻¹), ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  · let φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F g))
    let H : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n (k : UA E n) φ = φ}
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [← GlobalTheory.DefU.RU_RU, hb, ha]
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n (a : UA E n) _) = _
          rw [GlobalTheory.DefU.RU_RU, inv_mul_cancel, map_one]; rfl }
    have hnb : {k : finU (E := E) (n := n) | ∀ g, F (g * (k : UA E n)) = F g} ∈ 𝓝 (1 : finU (E := E) (n := n)) :=
      (continuous_subtype_val.tendsto (1 : finU (E := E) (n := n))).eventually hsm
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hnb fun k hk => ?_)
    change RU E n (k : UA E n) φ = φ
    funext g
    change ℓ (R (g * (k : UA E n))⁻¹ (F (g * k))) = ℓ (R g⁻¹ (F g))
    rw [hk g, _root_.mul_inv_rev, map_mul, hfin _ ((finU (E := E) (n := n)).inv_mem k.2), one_mul]
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coefL R F)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    change ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F g))) = ℓ (R (g * (k : UA E n))⁻¹ (F (g * k)))
    rw [hinf _ k.2 g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]

end GlobalTheory.EquivCoef
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.DefU

theorem finiteDimensional_vecForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧ ∀ k ∈ K, ∀ v, RU E n (k : UA E n) (f v) = f v) → FiniteDimensional ℂ M := by
  intro E _ _ _ n S _ _ _ ρ K hK M hM
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hK
  let T : M →ₗ[ℂ] (S₀ → Module.Dual ℂ S) :=
    { toFun := fun f s => (LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) (s : UA E n)).comp f.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    obtain ⟨hl, hr, hk⟩ := hM f.1 f.2
    have h0 : ∀ s ∈ S₀, ∀ v, f.1 v s = 0 := fun s hs v => LinearMap.congr_fun (congrFun hf ⟨s, hs⟩) v
    apply Subtype.ext
    refine LinearMap.ext fun v => funext fun g => ?_
    obtain ⟨γ, hγ, s, hs, x, hx, k, hkK, rfl⟩ := hS₀ g
    have e1 : f.1 v (γ * s * x * (k : UA E n)) = f.1 v (γ * s * x) := by
      have := congrFun (hk k hkK v) (γ * s * x)
      rw [← this]; rfl
    have e3 : f.1 v (s * x) = f.1 (ρ ⟨x, hx⟩ v) s := by
      rw [hr ⟨x, hx⟩ v]; rfl
    rw [e1, mul_assoc γ s x, hl v γ hγ, e3, h0 s hs]
    rfl
  exact Module.Finite.of_injective T hT

end GlobalTheory.DefU
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem intSt_and_archSt : IntSt ∧ ArchSt :=
  ⟨GlobalTheory.T.classSumDenominatorBound_of_cmThetaHypotheses GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied, GlobalTheory.T.thetaJetClassSum_archimedeanBound_of_cmTheta GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied⟩

end GlobalTheory.NormSum
end
