module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostCond
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem cc_iff {Ω : Type} [Field Ω] [CharZero Ω] (σ : G ℚ Ω) : IsCC σ ↔ IsConjOm σ.toRingEquiv := Iff.rfl

private noncomputable def dirHom (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (N : ℕ) [NeZero N] :
    DirichletCharacter O N →* (G ℚ Ω →* Oˣ) :=
  MonoidHom.mk' (Chr.dirG ℚ Ω) fun χ χ' => by
    ext σ
    simp [Chr.dirG]

private theorem dirHom_inj (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (N : ℕ) [NeZero N] :
    Function.Injective (dirHom Ω O N) := by
  intro χ χ' h
  rw [← DirichletCharacter.toUnitHom_inj]
  ext u
  obtain ⟨σ, rfl⟩ := (Chr.clsOnto Ω N).1 u
  exact congrArg Units.val (DFunLike.congr_fun h σ)

private theorem ker_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) :
    (Chr.cls ℚ Ω l).ker ≤ (Chr.dirG ℚ Ω (comp l (th0 l ψ))).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  have hl : l.Prime := Fact.out
  by_cases hlN : l ∣ N
  · have hpos : 0 < orderOf ψ := orderOf_pos ψ
    have hord : ¬ l ∣ orderOf (th0 l ψ) := (partOrd _ l hl ψ hpos).2.2.1
    have hord2 : ¬ l ∣ orderOf (comp l (th0 l ψ)) := fun h =>
      hord (dvd_trans h ((compAlg O N l hl).2.2.2.2.2.1 (th0 l ψ)).2.1)
    have hcond : (comp l (th0 l ψ)).conductor ∣ l := ((compOrd O N (th0 l ψ) l hl).2.2.1 hord2).2
    have hft : (comp l (th0 l ψ)).FactorsThrough l :=
      DirichletCharacter.FactorsThrough.mono _ (DirichletCharacter.factorsThrough_conductor _) hcond hlN
    have hk := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hlN).1 hft
    have hmap : ZMod.unitsMap hlN (Chr.cls ℚ Ω N σ) = 1 := by
      have := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 l hlN) σ
      rw [MonoidHom.comp_apply] at this
      rw [this, hσ]
    exact hk (MonoidHom.mem_ker.2 hmap)
  · have h1 : comp l (th0 l ψ) = 1 := ((compAlg O N l hl).2.2.2.2.2.1 (th0 l ψ)).2.2.1 hlN
    rw [h1]
    apply Units.ext
    show ((MulChar.toUnitHom (1 : DirichletCharacter O N)) (Chr.cls ℚ Ω N σ) : O) = 1
    rw [MulChar.coe_toUnitHom]
    simp

private theorem psi_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (e : ℕ) {σ : G ℚ Ω} (h : IsConjOm σ.toRingEquiv) :
    Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 ↔ PsiEven e ψ := by
  have hcyc : chiO ℚ Ω l O σ = -1 := by
    have h1 : cycZ ℚ Ω l σ = -1 := IsConjOm.cyc (E := ℚ) h
    simp only [chiO, MonoidHom.comp_apply, h1]
    ext
    simp
  have hcls : Chr.cls ℚ Ω N σ = -1 := (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h
  have hinv : ((-1 : Oˣ) ^ e)⁻¹ = (-1) ^ e := by rw [← inv_pow, inv_neg_one]
  have hz : (chiO ℚ Ω l O ^ (e : ℤ)) σ = (-1) ^ e := by
    rw [zpow_natCast, MonoidHom.pow_apply, hcyc]
  simp only [Chr.Psi, MonoidHom.mul_apply, hz, Chr.dirG, MonoidHom.comp_apply, hcls, PsiEven]
  rw [mul_eq_one_iff_eq_inv', hinv, ← Units.val_inj, MulChar.coe_toUnitHom]
  simp

theorem UpperTheory.V.HV.psiBar :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (w : G ℚ Ω →* c.Oˣ), IsOmT c w → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N),
      (∃ b < l - 1, Chr.dirG ℚ Ω (comp l (th0 l ψ)) = w ^ b ∧
        ∀ e : ℕ, Congr c (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) (w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ))) ∧
      (∀ e : ℕ, PsiEven e ψ ↔ ∀ σ : G ℚ Ω, IsCC σ → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1) ∧
      orderOf (Chr.dirG ℚ Ω ψ) = orderOf ψ ∧
      ∀ ψ' : DirichletCharacter c.O N, Chr.dirG ℚ Ω (ψ * ψ') = Chr.dirG ℚ Ω ψ * Chr.dirG ℚ Ω ψ' ∧ (Chr.dirG ℚ Ω ψ = Chr.dirG ℚ Ω ψ' → ψ = ψ') := by
  intro Ω _ _ _ l _ c w hw N _ ψ
  have hl : l.Prime := Fact.out
  have cf := congrFacts Ω l c
  have hmul : ∀ a a' : DirichletCharacter c.O N,
      Chr.dirG ℚ Ω (a * a') = Chr.dirG ℚ Ω a * Chr.dirG ℚ Ω a' := fun a a' => map_mul (dirHom Ω c.O N) a a'
  have hpw : ∀ (a : DirichletCharacter c.O N) (n : ℕ),
      Chr.dirG ℚ Ω (a ^ n) = Chr.dirG ℚ Ω a ^ n := fun a n => map_pow (dirHom Ω c.O N) a n
  have hone : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1 := map_one (dirHom Ω c.O N)
  obtain ⟨_, hwc⟩ := hw
  have hfacts := (omT Ω l c).2 w ⟨‹_›, hwc⟩
  have hker : w.ker ≤ (Chr.dirG ℚ Ω (comp l (th0 l ψ))).ker := by
    rw [hfacts.2.1]; exact ker_le Ω l ψ
  obtain ⟨b, hb, hbeq⟩ := hfacts.2.2.2.2.2.2.2 _ hker
  refine ⟨⟨b, hb, hbeq, fun e => ?_⟩, ?_, orderOf_injective (dirHom Ω c.O N) (dirHom_inj Ω c.O N) ψ,
    fun ψ' => ⟨hmul ψ ψ', fun h => dirHom_inj Ω c.O N h⟩⟩
  · have hdec : ψ = comp l (th0 l ψ) * chiP l ψ * kap l ψ := by
      rw [chiP, mul_comm (th0 l ψ), mul_inv_cancel_left, dirichletPrimeToLPart_mul_lPowerPart]
    have hψ' : Chr.dirG ℚ Ω ψ = w ^ b * Chr.dirG ℚ Ω (chiP l ψ) * Chr.dirG ℚ Ω (kap l ψ) := by
      conv_lhs => rw [hdec]
      rw [hmul, hmul, hbeq]
    have hpos : 0 < orderOf ψ := orderOf_pos ψ
    have hkord := (partOrd _ l hl ψ hpos).1
    have hkap : Congr c (Chr.dirG ℚ Ω (kap l ψ)) 1 := by
      apply cf.2.2.1 _ ((orderOf ψ).factorization l)
      rw [← hpw, show kap l ψ = lPart l ψ from rfl, ← hkord, pow_orderOf_eq_one, hone]
    have hcw : Congr c (chiO ℚ Ω l c.O) w := cf.1.symm hwc
    have hpowc : ∀ n : ℕ, Congr c (chiO ℚ Ω l c.O ^ n) (w ^ n) := by
      intro n
      induction n with
      | zero => simp only [pow_zero]; exact cf.1.refl _
      | succ n ih => rw [pow_succ, pow_succ]; exact (cf.2.1 _ _ _ _ ih hcw).1
    have h2 := (cf.2.1 _ _ _ _ (hpowc e)
      (cf.2.1 _ _ _ _ (cf.1.refl (w ^ b * Chr.dirG ℚ Ω (chiP l ψ))) hkap).1).1
    show Congr c (chiO ℚ Ω l c.O ^ (e : ℤ) * Chr.dirG ℚ Ω ψ) (w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ))
    rw [zpow_natCast, hψ', show w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ)
      = w ^ e * (w ^ b * Chr.dirG ℚ Ω (chiP l ψ) * 1) by rw [mul_one, pow_add, mul_assoc]]
    exact h2
  · intro e
    constructor
    · intro hE σ hσ
      exact (psi_cc Ω l ψ e ((cc_iff σ).1 hσ)).2 hE
    · intro hall
      obtain ⟨σ0, hσ0⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
      let σ : G ℚ Ω := AlgEquiv.ofRingEquiv (f := σ0) (fun q => by simp)
      have hσ : IsConjOm σ.toRingEquiv := hσ0
      exact (psi_cc Ω l ψ e hσ).1 (hall σ ((cc_iff σ).2 hσ))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.thmHV :
    PointHV → ∀ (K : BConst) (Ct : ℝ), 0 < Ct → ThmHV K Ct := by
  intro hP K Ct hCt ψ
  obtain ⟨C, r₁, r₂, hr₁, hr₂, hmain⟩ := hP ψ (fun l => Nat.log l (K.Rl l (Lchi ψ l)) + 3)
  refine ⟨(C : ℝ), r₁, r₂, hr₁, hr₂, ?_⟩
  intro eps A1 heps _
  have hJ : 0 < Jchi K Ct eps ψ := BConst.J_pos K hCt heps _ _ _
  refine ⟨(2 : ℝ) ^ Jchi K Ct eps ψ, ?_⟩
  intro e t hadm X hX q d hpair hq hd hlist _ Y hwin x hYx hxY
  obtain ⟨⟨hXY, hYX⟩, hwin'⟩ := hwin
  have hXY' : X ^ (1 / Jchi K Ct eps ψ) ≤ Y := hXY
  have h1 : ((2 : ℝ) ^ Jchi K Ct eps ψ) ^ (1 / Jchi K Ct eps ψ) ≤ X ^ (1 / Jchi K Ct eps ψ) :=
    Real.rpow_le_rpow (by positivity) hX (by positivity)
  rw [one_div, Real.rpow_rpow_inv (by norm_num) hJ.ne'] at h1
  rw [one_div] at hXY'
  have hx2 : (2 : ℝ) ≤ x := by linarith
  obtain ⟨he2, -, ht2, htx⟩ := hadm x hx2
  have hxX : x ≤ X := le_trans hxY hYX
  have htX : (t x : ℝ) ≤ X ^ Ct := le_trans htx (Real.rpow_le_rpow (by linarith) hxX hCt.le)
  intro E _ _ _ hE
  have hB := hwin' x hYx hxY
  have hq' : 2 * t x + 1 < q := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < q by linarith)
  have hd' : 2 * t x + 1 < d := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < d by linarith)
  have hbig : Host.Big ⟨ψ, e x, q, d, he2, hpair⟩ (t x) := by
    refine ⟨hq', hd', ?_⟩
    intro y hy
    apply hlist y
    simp only [Host.q, Host.o, List.mem_cons, List.not_mem_nil] at hy ⊢
    tauto
  have key := hmain ⟨ψ, e x, q, d, he2, hpair⟩ rfl
    (hlist r₁ (by simp)).1 (hlist r₁ (by simp)).2 (hlist r₂ (by simp)).1 (hlist r₂ (by simp)).2
    (t x) ht2 hbig (Real.exp (x ^ (4 * eps / 5))) (Real.exp_pos _).le
    (fun l hl _ => hB.2 l hl) E hE
  rw [hostCond ⟨ψ, e x, q, d, he2, hpair⟩ E hE]
  simpa [Real.rpow_natCast] using key
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem pow_eq_one_of {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (m : ℕ)
    (H : ∀ u : (ZMod N)ˣ, χ.toUnitHom u ^ m = 1) : χ ^ m = 1 := by
  refine MulChar.ext fun u => ?_
  have hu := congrArg Units.val (H u)
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one] at hu
  rw [MulChar.pow_apply_coe, hu, MulChar.one_apply_coe]

private theorem unitHom_pow_orderOf {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    χ.toUnitHom u ^ orderOf χ = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
    MulChar.one_apply_coe, Units.val_one]

theorem UpperTheory.V.HV.hostComp :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ →
      orderOf ψ ∣ 2 ^ (h.ex + 1) * h.o ∧ 0 < orderOf ψ ∧ ∀ r, r.Prime → r ≠ 2 →
        orderOf (comp r ψ) ∣ 2 * h.o ∧ (r ∣ h.q → orderOf (comp r ψ) ∣ h.o) ∧ (¬ r ∣ h.q → comp r ψ ^ 2 = 1) ∧ (¬ r ∣ h.N → comp r ψ = 1) := by
  intro h O _ _ ψ hψ
  have hI := hostIndex h
  have ho : 0 < h.o := hI.2.2.2.1
  have hmemK : ∀ x ∈ h.H, ψ.toUnitHom x = 1 := fun x hx => MonoidHom.mem_ker.mp (hψ hx)
  have hA : ψ ^ (2 ^ (h.ex + 1) * h.o) = 1 :=
    pow_eq_one_of ψ _ (fun u => by
      rw [← map_pow]
      exact hmemK _ (hI.2.2.2.2.2.2.2.2.2 u))
  refine ⟨orderOf_dvd_of_pow_eq_one hA,
    Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hA) (Nat.mul_pos (pow_pos two_pos _) ho), ?_⟩
  intro r hr hr2
  have facts := projFacts h.N r hr
  have hca := compAlg O h.N r hr
  have cu : ∀ u, (comp r ψ).toUnitHom u = ψ.toUnitHom (proj r h.N u) := hca.1 ψ
  have off : ∀ (M : ℕ) (hM : M ∣ h.N), ¬ r ∣ M → ∀ u, ZMod.unitsMap hM (proj r h.N u) = 1 :=
    facts.2.2.2.2.2.2.2.1
  have n2 : ¬ r ∣ 2 ^ (h.ex + 2) := fun hd =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  have sq : ¬ r ∣ h.q → comp r ψ ^ 2 = 1 := by
    intro hq
    refine pow_eq_one_of _ 2 (fun u => ?_)
    rw [cu, ← map_pow]
    apply hmemK
    simp only [Host.H, Subgroup.mem_inf]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.two_pow_dvd h) n2 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.q_dvd h) hq u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow]
      exact ⟨_, rfl⟩
    · rw [Subgroup.mem_comap, map_pow]
      exact ⟨_, rfl⟩
  have hcop := h.pair.2.2.2.2
  have dq : r ∣ h.q → comp r ψ ^ h.o = 1 := by
    intro hq
    have nq1 : ¬ r ∣ h.q1 := fun hd =>
      hr.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_of_dvd_left hd _) hcop) hq)
    have nd : ¬ r ∣ h.d := fun hd =>
      hr.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_of_dvd_right hd _) hcop) hq)
    refine pow_eq_one_of _ h.o (fun u => ?_)
    rw [cu, ← map_pow]
    apply hmemK
    simp only [Host.H, Subgroup.mem_inf]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.two_pow_dvd h) n2 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, MonoidHom.mem_ker, map_pow, map_pow]
      exact unitHom_pow_orderOf _ _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.host_q1_dvd_N h) nq1 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.d_dvd h) nd u, one_pow]
      exact Subgroup.one_mem _
  refine ⟨?_, fun hq => orderOf_dvd_of_pow_eq_one (dq hq), sq, (hca.2.2.2.2.2.1 ψ).2.2.1⟩
  by_cases hq : r ∣ h.q
  · exact (orderOf_dvd_of_pow_eq_one (dq hq)).trans (dvd_mul_left _ _)
  · exact (orderOf_dvd_of_pow_eq_one (sq hq)).trans (dvd_mul_right _ _)
end
