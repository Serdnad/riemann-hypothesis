module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle003
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

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

section Loc

variable {O : Type} [CommRing O] [IsLocalRing O]

private theorem sub_mem_iff (x y : O) :
    x - y ∈ IsLocalRing.maximalIdeal O ↔ IsLocalRing.residue O x = IsLocalRing.residue O y := by
  exact (Ideal.Quotient.eq).symm

private theorem res_eq_one (l : ℕ) [hl : Fact l.Prime] (h : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hx : x ^ l ^ s = 1) :
    IsLocalRing.residue O x = 1 := by
  have h0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact h
  haveI : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  have h1 : (IsLocalRing.residue O x - 1) ^ l ^ s = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hx, map_one, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero s hl.out.ne_zero) |>.1 h1)

private theorem eq_of_res_eq [IsDomain O] (x y : Oˣ) (m : ℕ) (hm : IsUnit (m : O)) (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : x = y := by
  have hw : (x * y⁻¹) ^ m = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have hr : IsLocalRing.residue O ((x * y⁻¹ : Oˣ) : O) = 1 := by
    rw [Units.val_mul, map_mul, h, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hzm : ((x * y⁻¹ : Oˣ) : O) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]
  have hs : IsUnit (∑ i ∈ Finset.range m, ((x * y⁻¹ : Oˣ) : O) ^ i) := by

    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hr, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← map_natCast (IsLocalRing.residue O) m]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hm
  have e := geom_sum_mul ((x * y⁻¹ : Oˣ) : O) m
  rw [hzm, sub_self] at e
  have hz1 := (hs.mul_right_eq_zero).mp e
  have h1 : x * y⁻¹ = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp hz1)
  exact mul_inv_eq_one.mp h1

private theorem res_inv (x : Oˣ) : IsLocalRing.residue O ((x⁻¹ : Oˣ) : O) = (IsLocalRing.residue O x)⁻¹ := by
  exact map_units_inv (IsLocalRing.residue O) x

end Loc

theorem UpperTheory.V.HV.congrFacts :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l), Equivalence (Congr (Ω := Ω) c) ∧
      (∀ a a' b b' : G ℚ Ω →* c.Oˣ, Congr c a a' → Congr c b b' → Congr c (a * b) (a' * b') ∧ Congr c a⁻¹ a'⁻¹) ∧
      (∀ (a : G ℚ Ω →* c.Oˣ) (s : ℕ), a ^ l ^ s = 1 → Congr c a 1) ∧
      (∀ (x y : c.Oˣ) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → y ^ m = 1 → (x : c.O) - y ∈ IsLocalRing.maximalIdeal c.O → x = y) ∧
      ∀ (a b : G ℚ Ω →* c.Oˣ) (m : ℕ), ¬ l ∣ m → a ^ m = 1 → b ^ m = 1 → Congr c a b → a = b := by
  intro Ω _ _ _ l _ c
  haveI := c.dvr
  haveI := c.fin
  have hF := dvrFacts l c.O
  have hlu : ¬ IsUnit ((l : ℕ) : c.O) := by
    intro hu
    have hu' : IsUnit (algebraMap ℤ_[l] c.O ((l : ℕ) : ℤ_[l])) := by rwa [map_natCast]
    haveI := hF.2.2.1
    exact PadicInt.p_nonunit (IsLocalHom.map_nonunit _ hu')
  have cr : ∀ a b : G ℚ Ω →* c.Oˣ, Congr c a b ↔
      ∀ σ, IsLocalRing.residue c.O (a σ : c.O) = IsLocalRing.residue c.O (b σ : c.O) :=
    fun a b => forall_congr' fun σ => sub_mem_iff _ _
  have p4 : ∀ (x y : c.Oˣ) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → y ^ m = 1 →
      (x : c.O) - y ∈ IsLocalRing.maximalIdeal c.O → x = y :=
    fun x y m hm hx hy hxy => eq_of_res_eq x y m (hF.2.2.2.2.2.2.2.2 m hm) hx hy ((sub_mem_iff _ _).mp hxy)
  have papp : ∀ (a : G ℚ Ω →* c.Oˣ) (n : ℕ), a ^ n = 1 → ∀ σ, (a σ) ^ n = 1 := by
    intro a n ha σ
    rw [← MonoidHom.pow_apply, ha, MonoidHom.one_apply]
  refine ⟨⟨fun a => ?_, fun {a b} h => ?_, fun {a b d} h1 h2 => ?_⟩, fun a a' b b' ha hb => ⟨?_, ?_⟩,
    fun a s ha => ?_, p4, fun a b m hm ha hb hab => ?_⟩
  · rw [cr]
    intro σ
    rfl
  · rw [cr] at h ⊢
    intro σ
    exact (h σ).symm
  · rw [cr] at h1 h2 ⊢
    intro σ
    exact (h1 σ).trans (h2 σ)
  · rw [cr] at ha hb ⊢
    intro σ
    simp only [MonoidHom.mul_apply, Units.val_mul, map_mul, ha σ, hb σ]
  · rw [cr] at ha ⊢
    intro σ
    simp only [MonoidHom.inv_apply, res_inv, ha σ]
  · rw [cr]
    intro σ
    have e' : ((a σ : c.O)) ^ l ^ s = 1 := by
      rw [← Units.val_pow_eq_pow_val, papp a _ ha σ, Units.val_one]
    rw [res_eq_one l hlu _ s e', MonoidHom.one_apply, Units.val_one, map_one]
  · apply MonoidHom.ext
    intro σ
    exact p4 _ _ m hm (papp a m ha σ) (papp b m hb σ) (hab σ)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem cond_dvd_iff {O : Type} [CommRing O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) {M : ℕ} (h : M ∣ N) :
    ψ.conductor ∣ M ↔ ∀ u, ZMod.unitsMap h u = 1 → ψ.toUnitHom u = 1 := by
  rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ h, DirichletCharacter.mem_conductorSet_iff,
    DirichletCharacter.factorsThrough_iff_ker_unitsMap h]
  rfl

private theorem comp_hom {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (comp r χ).toUnitHom u = χ.toUnitHom (proj r N u) := by
  unfold comp
  rw [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]
  rfl

private theorem mul_hom {O : Type} [CommRing O] {N : ℕ} (χ ψ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (χ * ψ).toUnitHom u = χ.toUnitHom u * ψ.toUnitHom u := by
  ext
  simp

private theorem rest_hom {O : Type} [CommRing O] {N : ℕ} (χ ψ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (χ * ψ⁻¹).toUnitHom u * ψ.toUnitHom u = χ.toUnitHom u := by
  rw [← mul_hom, inv_mul_cancel_right]

private theorem split_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {r : ℕ} (hr : r.Prime) :
    (comp r χ).conductor = ordProj[r] χ.conductor ∧ (χ * (comp r χ)⁻¹).conductor = ordCompl[r] χ.conductor := by
  obtain ⟨-, -, hid, -, -, hra, hke, -, hnat⟩ := projFacts N r hr
  have hc := (cond_dvd_iff χ χ.conductor_dvd_level).1 dvd_rfl
  have hc' : ∀ u, ZMod.unitsMap χ.conductor_dvd_level u = 1 → (comp r χ).toUnitHom u = 1 := by
    intro u hu
    rw [comp_hom]
    apply hc
    rw [hnat, hu, map_one]
  have ha1 : (comp r χ).conductor ∣ χ.conductor := (cond_dvd_iff _ χ.conductor_dvd_level).2 hc'
  have hb1 : (χ * (comp r χ)⁻¹).conductor ∣ χ.conductor := by
    refine (cond_dvd_iff _ χ.conductor_dvd_level).2 fun u hu => ?_
    have := rest_hom χ (comp r χ) u
    rwa [hc u hu, hc' u hu, mul_one] at this
  have ha2 : (comp r χ).conductor ∣ ordProj[r] N := by
    refine (cond_dvd_iff _ (Nat.ordProj_dvd N r)).2 fun u hu => ?_
    have : u ∈ (proj r N).ker := by rw [hke]; exact hu
    rw [comp_hom, MonoidHom.mem_ker.1 this, map_one]
  have hb2 : (χ * (comp r χ)⁻¹).conductor ∣ ordCompl[r] N := by
    refine (cond_dvd_iff _ (Nat.ordCompl_dvd N r)).2 fun u hu => ?_
    have : u ∈ (proj r N).range := by rw [hra]; exact hu
    obtain ⟨v, rfl⟩ := this
    have := rest_hom χ (comp r χ) (proj r N v)
    rw [comp_hom, hid] at this
    exact mul_eq_right.1 this
  have hcop : (comp r χ).conductor.Coprime (χ * (comp r χ)⁻¹).conductor :=
    ((coprime_ordProj_ordCompl r N).coprime_dvd_left ha2).coprime_dvd_right hb2
  have h1 := hcop.mul_dvd_of_dvd_of_dvd ha1 hb1
  have h2 : χ.conductor ∣ (comp r χ).conductor * (χ * (comp r χ)⁻¹).conductor := by
    have hN := h1.trans χ.conductor_dvd_level
    refine (cond_dvd_iff _ hN).2 fun u hu => ?_
    have e1 := (cond_dvd_iff _ hN).1 (dvd_mul_right _ _) u hu
    have e2 := (cond_dvd_iff _ hN).1 (dvd_mul_left _ _) u hu
    rw [← rest_hom χ (comp r χ) u, e1, e2, mul_one]
  have he := h2.antisymm h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).1 ha2
  have hb3 : ¬ r ∣ (χ * (comp r χ)⁻¹).conductor := fun h =>
    Nat.not_dvd_ordCompl hr (NeZero.ne N) (h.trans hb2)
  have hb0 := (χ * (comp r χ)⁻¹).conductor_ne_zero
  have hf : χ.conductor.factorization r = k := by
    rw [he, hk, Nat.factorization_mul (pow_ne_zero _ hr.ne_zero) hb0]
    simp [hr.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hb3]
  rw [hf]
  refine ⟨hk, ?_⟩
  rw [hk] at he
  exact (Nat.div_eq_of_eq_mul_right (pow_pos hr.pos k) he).symm

theorem UpperTheory.V.HV.compCond :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (r : ℕ), r.Prime →
      (comp r χ).conductor = ordProj[r] χ.conductor ∧ (comp r χ = 1 ↔ ¬ r ∣ χ.conductor) ∧
      (χ * (comp r χ)⁻¹).conductor = ordCompl[r] χ.conductor ∧ 2 ^ c2 χ = (psi2 χ).conductor ∧ 2 ^ c2 χ ∣ N ∧
      ∀ (M : ℕ), M ∣ N → (χ.conductor ∣ M ↔ ∀ p ∈ N.primeFactors, (comp p χ).conductor ∣ M) := by
  intro O _ _ N _ χ r hr
  have h2 : 2 ^ c2 χ = (psi2 χ).conductor := by
    unfold c2 psi2
    rw [(split_cond χ Nat.prime_two).1, Nat.prime_two.factorization_pow]
    simp
  refine ⟨(split_cond χ hr).1, ?_, (split_cond χ hr).2, h2, h2 ▸ (psi2 χ).conductor_dvd_level, fun M _ => ⟨fun h p hp => ?_, fun h => ?_⟩⟩
  · rw [DirichletCharacter.eq_one_iff_conductor_eq_one, (split_cond χ hr).1,
      hr.dvd_iff_one_le_factorization χ.conductor_ne_zero, Nat.pow_eq_one]
    have := hr.one_lt
    omega
  · rw [(split_cond χ (Nat.prime_of_mem_primeFactors hp)).1]
    exact (Nat.ordProj_dvd _ _).trans h
  · rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have hpN : p ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hp, ((dvd_pow_self p hk0.ne').trans hk).trans χ.conductor_dvd_level, NeZero.ne N⟩
      have := h p hpN
      rw [(split_cond χ hp).1] at this
      exact (pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization χ.conductor_ne_zero).1 hk)).trans this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem UpperTheory.V.HV.projProd_ext (N : ℕ) [NeZero N] (a b : (ZMod N)ˣ)
    (h : ∀ r ∈ N.primeFactors, ZMod.unitsMap (Nat.ordProj_dvd N r) a = ZMod.unitsMap (Nat.ordProj_dvd N r) b) :
    a = b := by
  have key : ∀ r ∈ N.primeFactors, (((r ^ N.factorization r : ℕ)) : ℤ) ∣ ((b : ZMod N).val : ℤ) - ((a : ZMod N).val : ℤ) := by
    intro r hr
    have e := congrArg (fun u : (ZMod (r ^ N.factorization r))ˣ => (u : ZMod (r ^ N.factorization r))) (h r hr)
    simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe] at e
    rw [← ZMod.natCast_zmod_val (a : ZMod N), ← ZMod.natCast_zmod_val (b : ZMod N), map_natCast, map_natCast,
      ZMod.natCast_eq_natCast_iff] at e
    exact Nat.modEq_iff_dvd.mp e
  have hcop : (N.primeFactors : Set ℕ).Pairwise (Function.onFun IsCoprime fun r => (((r ^ N.factorization r : ℕ)) : ℤ)) := by
    intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  have hd := Finset.prod_dvd_of_coprime hcop key
  have hN : ∏ r ∈ N.primeFactors, r ^ N.factorization r = N := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self (NeZero.ne N)]
    rw [Finsupp.prod, Nat.support_factorization]
  rw [← Nat.cast_prod, hN] at hd
  have e2 : ((a : ZMod N).val : ZMod N) = ((b : ZMod N).val : ZMod N) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.modEq_iff_dvd.mpr hd)
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at e2
  exact Units.ext e2

theorem UpperTheory.V.HV.projProd :
    ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), ∏ r ∈ N.primeFactors, proj r N u = u := by
  intro N _ u
  apply projProd_ext
  intro r hr
  have hp := Nat.prime_of_mem_primeFactors hr
  rw [map_prod, Finset.prod_eq_single_of_mem r hr]
  · exact (projFacts N r hp).1 u
  · intro s hs hsr
    have hs' := Nat.prime_of_mem_primeFactors hs
    refine (projFacts N s hs').2.2.2.2.2.2.2.1 _ _ ?_ u
    intro hd
    exact hsr ((Nat.prime_dvd_prime_iff_eq hs' hp).1 (hs'.dvd_of_dvd_pow hd))
end
