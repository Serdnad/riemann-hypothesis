module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.GaloisValuations.GlobalB
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cob_of_coord {H k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (a : H → k₀) (z : H → k)
    (h : ∀ φ : k →ₗ[k₀] k₀, ∃ m, ∀ g, φ (z g) = a g * m - m) :
    ∃ m, ∀ g, z g = algebraMap k₀ k (a g) * m - m := by
  by_cases ha : ∀ g, a g = 1
  · refine ⟨0, fun g => ?_⟩
    rw [mul_zero, sub_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ (z g)).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    rw [hm g, ha g, one_mul, sub_self]
  · push_neg at ha
    obtain ⟨g₀, hg₀⟩ := ha
    have hne : a g₀ - 1 ≠ 0 := sub_ne_zero.2 hg₀
    refine ⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩
    rw [← Algebra.smul_def, ← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ _).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    have key : φ ((a g₀ - 1)⁻¹ • z g₀) = m := by
      rw [map_smul, hm g₀, smul_eq_mul, ← sub_one_mul, inv_mul_cancel_left₀ hne]
    rw [map_sub, map_sub, map_smul, key, hm g, smul_eq_mul, sub_self]

theorem UpperTheory.V.GradeZeroInterpolatingElement.xvanExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (k : Type) [Field k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + red (γ g : c.O) * z h) → D.UnrT z 0 → (∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, z g = red (γ g : c.O) * m - m) → ∃ m, ∀ g, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD k _ red hred γ hγ z hz hcoc hunr hloc
  have hlh : IsLocalHom red := ⟨fun a ha => by
    by_contra hn
    have h0 := hred a ((mem_maximalIdeal a).2 hn)
    rw [h0] at ha
    exact not_isUnit_zero ha⟩
  letI : Algebra (ResidueField c.O) k := (ResidueField.lift red).toAlgebra
  have hι : ∀ a : c.O, red a = algebraMap (ResidueField c.O) k (residue c.O a) := fun a =>
    (ResidueField.lift_residue_apply red a).symm
  have hX : D.XVan γ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hD.xvan D.al (by simp)).1
    · exact (hD.xvan D.be (by simp)).1
    · exact (hD.xvan D.th (by simp)).1
    · exact (hD.xvan D.al (by simp)).2
    · exact (hD.xvan D.be (by simp)).2
    · exact (hD.xvan D.th (by simp)).2
  simp only [hι]
  apply cob_of_coord (fun g => Raw.bar γ g) z
  intro φ
  have h1 : ∀ g h, φ (z (g * h)) = φ (z g) + Raw.bar γ g * φ (z h) := by
    intro g h
    rw [hcoc g h, map_add (f := _), hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have h2 : D.UnrT (fun g => φ (z g)) 0 := by
    intro A hA g hg hb
    simp only [hunr A hA g hg hb, map_zero]
  have h3 : ∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, φ (z g) = Raw.bar γ g * m - m := by
    intro v hv
    obtain ⟨m, hm⟩ := hloc v hv
    refine ⟨φ m, fun g hg => ?_⟩
    rw [hm g hg, hι, ← Algebra.smul_def, map_sub, map_smul, smul_eq_mul]
  exact hX (fun g => φ (z g)) (hz.comp fun x => φ x) h1 h2 h3
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem comm_of_integral {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (hk : (p : k) = 0) (f g : k →+* k)
    {x : k} (hx : IsIntegral ℤ x) : f (g x) = g (f x) := by
  haveI hchar : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hk
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxi : IsIntegral (ZMod p) x := hx.tower_top
  haveI := Algebra.finite_adjoin_simple_of_isIntegral hxi
  haveI hF : Finite (Algebra.adjoin (ZMod p) {x}) := Module.finite_of_finite (ZMod p)
  have hxmem : x ∈ Algebra.adjoin (ZMod p) {x} := Algebra.subset_adjoin (Set.mem_singleton x)
  have hfin : (Set.range (fun n : ℕ => x ^ n)).Finite := by
    refine Set.Finite.subset (s := ((Algebra.adjoin (ZMod p) {x} : Subalgebra (ZMod p) k) : Set k))
      (Set.finite_coe_iff.mp hF) ?_
    rintro _ ⟨n, rfl⟩
    exact Subalgebra.pow_mem _ hxmem n
  have hni : ¬ Function.Injective (fun n : ℕ => x ^ n) := fun hinj =>
    (Set.infinite_range_of_injective hinj) hfin
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨i, j, heq', hij⟩ := hni
  obtain ⟨N, hN0, hN⟩ : ∃ N : ℕ, 0 < N ∧ x ^ N = 1 := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, ?_⟩
      have h2 : x ^ i * x ^ (j - i) = x ^ i * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, heq']
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) h2
    · refine ⟨i - j, by omega, ?_⟩
      have h2 : x ^ j * x ^ (i - j) = x ^ j * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, heq']
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) h2
  haveI : NeZero N := ⟨hN0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity N k)
  have mem : ∀ y : k, y ^ N = 1 → ∃ a : ℤ, y = ((ζ : kˣ) : k) ^ a := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hN0.ne'] at hy
      exact zero_ne_one hy
    have hu : Units.mk0 y hy0 ∈ rootsOfUnity N k := by
      rw [mem_rootsOfUnity]
      ext
      simp [hy]
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨_, hu⟩)
    refine ⟨a, ?_⟩
    have h3 := congrArg (fun u : rootsOfUnity N k => ((u : kˣ) : k)) ha
    simp only [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, Units.val_mk0] at h3
    exact h3.symm
  have hzN : ((ζ : kˣ) : k) ^ N = 1 := by
    have h1 : (ζ : kˣ) ^ N = 1 := (mem_rootsOfUnity _ _).mp ζ.2
    have h2 := congrArg Units.val h1
    simpa using h2
  obtain ⟨a, ha⟩ := mem (f ((ζ : kˣ) : k)) (by rw [← map_pow, hzN, map_one])
  obtain ⟨b, hb⟩ := mem (g ((ζ : kˣ) : k)) (by rw [← map_pow, hzN, map_one])
  obtain ⟨c, hc⟩ := mem x hN
  rw [hc]
  simp only [map_zpow₀, ha, hb]
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  congr 1
  ring

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}

private def resA {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A) : A →+* A where
  toFun x := ⟨σ x, (apply_mem_iff_of_mem_Dec hσ _).2 x.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ (a : Ω) b)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ (a : Ω) b)

private theorem resA_local {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A) : IsLocalHom (resA hσ) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have h1 : A.valuation (a : Ω) < 1 := (A.valuation_lt_one_iff a).1 h
  have h2 : A.valuation (σ a) < 1 := (valuation_apply_lt_one_iff hσ _).2 h1
  exact (A.valuation_lt_one_iff (resA hσ a)).2 h2 ha

private theorem comm_mem_Ine {p : ℕ} (hp : p.Prime) (hA : A.valuation (p : Ω) < 1) {g h : G ℚ Ω}
    (hg : g ∈ Dec (F := ℚ) A) (hh : h ∈ Dec (F := ℚ) A) : g * h * g⁻¹ * h⁻¹ ∈ Ine (F := ℚ) A := by
  haveI := resA_local hg
  haveI := resA_local hh
  have hkp : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    simpa using hA
  have hint : ∀ z : Ω, IsIntegral ℤ z → ∀ hz : z ∈ A,
      IsIntegral ℤ (IsLocalRing.residue A ⟨z, hz⟩) := by
    intro z hz hzA
    have h1 : IsIntegral ℤ (⟨z, hzA⟩ : A) := by
      rw [← isIntegral_algHom_iff (A.toSubring.subtype.toIntAlgHom) Subtype.val_injective]
      exact hz
    exact h1.map_of_comp_eq (RingHom.id ℤ) (IsLocalRing.residue A) (RingHom.ext_int _ _)
  have comm : ∀ w : A,
      IsLocalRing.ResidueField.map (resA hg) (IsLocalRing.ResidueField.map (resA hh)
        (IsLocalRing.residue A w)) =
      IsLocalRing.ResidueField.map (resA hh) (IsLocalRing.ResidueField.map (resA hg)
        (IsLocalRing.residue A w)) := by
    intro w
    obtain ⟨s, t, hs, ht, hvs, hst⟩ := exists_den ℚ A (A.valuation_le_one w)
    have hsA := mem_of_isIntegral_int A hs
    have htA := mem_of_isIntegral_int A ht
    have hsunit : IsLocalRing.residue A ⟨s, hsA⟩ ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      simp [hvs]
    have hw : IsLocalRing.residue A w
        = IsLocalRing.residue A ⟨t, htA⟩ / IsLocalRing.residue A ⟨s, hsA⟩ := by
      rw [eq_div_iff hsunit, ← map_mul]
      congr 1
      apply Subtype.ext
      show (w : Ω) * s = t
      rw [mul_comm]
      exact hst
    rw [hw, map_div₀, map_div₀, map_div₀, map_div₀,
      comm_of_integral hp hkp _ _ (hint t ht htA), comm_of_integral hp hkp _ _ (hint s hs hsA)]
  have key : ∀ y : Ω, y ∈ A → A.valuation (g (h y) - h (g y)) < 1 := by
    intro y hy
    have c := comm ⟨y, hy⟩
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue] at c
    have c2 : IsLocalRing.residue A
        (resA hg (resA hh ⟨y, hy⟩) - resA hh (resA hg ⟨y, hy⟩)) = 0 := by
      rw [map_sub, c, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at c2
    exact c2
  have hDec : g * h * g⁻¹ * h⁻¹ ∈ Dec (F := ℚ) A :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg))
      (Subgroup.inv_mem _ hh)
  show _ ∈ Inertia (F := ℚ) A
  simp only [Inertia, Set.mem_setOf_eq]
  refine ⟨hDec, fun x hx => ?_⟩
  have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
  have hyA : g⁻¹ (h⁻¹ x) ∈ A :=
    (apply_mem_iff_of_mem_Dec (Subgroup.inv_mem _ hg) _).2
      ((apply_mem_iff_of_mem_Dec (Subgroup.inv_mem _ hh) _).2 hxA)
  have e : (g * h * g⁻¹ * h⁻¹) x - x = g (h (g⁻¹ (h⁻¹ x))) - h (g (g⁻¹ (h⁻¹ x))) := by
    simp only [AlgEquiv.mul_apply]
    congr 1
    rw [← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel, AlgEquiv.one_apply,
      ← AlgEquiv.mul_apply h h⁻¹, mul_inv_cancel, AlgEquiv.one_apply]
  rw [e]
  exact key _ hyA

end

theorem UpperTheory.V.GradeZeroInterpolatingElement.abP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ p ∈ D.Sb, (∃ τ ∈ D.Ip p, D.ψ τ ≠ 1 ∧ ∀ s ∈ D.Ip p, ∃ n : ℕ, D.ψ s = D.ψ τ ^ n) ∧ ∀ g ∈ D.Gp p, ∀ h ∈ D.Gp p, g * h * g⁻¹ * h⁻¹ ∈ D.Ip p ⊓ D.ψ.ker := by
  intro Ω _ _ _ l _ c D hD p hp
  unfold Raw.Sb at hp
  obtain ⟨hpS, hpl, hldvd⟩ := Finset.mem_filter.mp hp
  have hpp : p.Prime := hD.S_prime p hpS
  have hv := hD.pl_over p hpp
  refine ⟨?_, ?_⟩
  · haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.psi_open
    haveI : Finite D.ψ.range :=
      Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange D.ψ).toEquiv
    haveI hfin : Finite (Subgroup.map D.ψ (D.Ip p)) :=
      Finite.of_injective (Subgroup.inclusion (Subgroup.map_le_range D.ψ _))
        (Subgroup.inclusion_injective _)
    haveI : IsCyclic (Subgroup.map D.ψ (D.Ip p)) := isCyclic_subgroup_units _
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Subgroup.map D.ψ (D.Ip p))
    obtain ⟨τ, hτI, hτγ⟩ := Subgroup.mem_map.mp γ.2
    refine ⟨τ, hτI, ?_, ?_⟩
    · intro h1
      have hγ1 : γ = 1 := Subtype.ext (by rw [← hτγ, h1]; rfl)
      have hsub : ∀ x : Subgroup.map D.ψ (D.Ip p), x = 1 := by
        intro x
        obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hγ x)
        rw [← hz, hγ1, one_zpow]
      have hcard : Nat.card (Subgroup.map D.ψ (D.Ip p)) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hsub a).trans (hsub b).symm⟩, ⟨1⟩⟩
      rw [hcard] at hldvd
      exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.mp hldvd)
    · intro s hs
      have hsH : (⟨D.ψ s, Subgroup.mem_map_of_mem _ hs⟩ : Subgroup.map D.ψ (D.Ip p))
          ∈ Submonoid.powers γ := mem_powers_iff_mem_zpowers.2 (hγ _)
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hsH
      refine ⟨n, ?_⟩
      have h2 := congrArg Subtype.val hn
      simp only [SubgroupClass.coe_pow] at h2
      rw [hτγ]
      exact h2.symm
  · intro g hg h hh
    refine ⟨comm_mem_Ine hpp hv hg hh, ?_⟩
    show g * h * g⁻¹ * h⁻¹ ∈ D.ψ.ker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (D.ψ g), mul_assoc (D.ψ h), mul_inv_cancel, mul_one, mul_inv_cancel]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

section

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_map' (f : R →+* R') (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp [adj_apply, RingHom.mapMatrix_apply]

private theorem smul_map' (f : R →+* R') (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

private theorem isGSp_map (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) : IsGSp (f ν) (f.mapMatrix g) := by
  unfold IsGSp at h ⊢
  have h2 := congrArg f.mapMatrix h
  rw [map_mul, smul_map', map_one, ← adj_map'] at h2
  exact h2

private theorem aeval_map' (f : R →+* R') (X : M4 R) (p : Polynomial R) :
    Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp

private theorem prj_map (f : R →+* R') (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  simp only [prj]
  rw [← aeval_map']
  congr 1
  simp [Polynomial.map_prod]

private theorem ord_map {H : Type} [Group H] (f : R →+* R') {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H}
    {r : H →* M4 R} {r' : H →* M4 R'} (hr : ∀ g, r' g = f.mapMatrix (r g)) {ps' : Fin 4 → H → R'}
    (hps : ∀ i g, ps' i g = f (ps i g)) (h : Ord I ps s₀ r) : Ord I ps' s₀ r' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hr, hps]
    rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp
  · intro g i j hij
    simp only [hr, hps]
    rw [prj_map, prj_map, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [hr, hps]
    have e : f.mapMatrix (r s) - f (ps i s) • (1 : M4 R') = f.mapMatrix (r s - ps i s • 1) := by
      rw [map_sub, smul_map', map_one]
    rw [prj_map, e, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

private theorem condL_map (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt l) R) (h : D.condL R ρ) :
    D.condL R' (ρ.map f) := by
  unfold Raw.condL at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hr : ∀ g, (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    intro g
    ext a b
    rw [Lift.map_hom]
    rfl
  refine ⟨fun g => ?_, ord_map (f : R →+* R') hr (fun i g => (f.commutes _).symm) h2⟩
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h1 g)

private theorem condP_map (p : ℕ) (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt p) R) (h : D.condP p R ρ) :
    D.condP p R' (ρ.map f) := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · have := isGSp_map (f : R →+* R') (h.1 g)
    rw [RingHom.coe_coe, f.commutes] at this
    exact this
  · show (f : R →+* R').mapMatrix (ρ.hom g) = 1
    rw [h.2 g hg, map_one]

private theorem mult_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Mult ρ.hom) : D.Mult (ρ.map f).hom := by
  intro g
  have hr : (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    ext a b
    rw [Lift.map_hom]
    rfl
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h g)

private theorem unr_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.UnrT ρ.hom 1) :
    D.UnrT (ρ.map f).hom 1 := by
  intro A hA g hg h1
  show (f : R →+* R').mapMatrix (ρ.hom g) = 1
  rw [h A hA g hg h1, map_one]

private theorem hEl_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp [Raw.hEl, Lift.map_hom, map_add (f := _), map_mul, f.commutes]

private theorem loc_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (v : ℕ) :
    D.loc (ρ.map f) v = (D.loc ρ v).map f := by
  apply Lift.ext
  rfl

private theorem nrm_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Nrm ρ.hom) : D.Nrm (ρ.map f).hom := by
  refine ⟨fun i j hij => ?_, ?_, ?_⟩
  · rw [Lift.map_hom, h.1 i j hij, map_zero]
  · rw [hEl_map, h.2.1, map_zero]
  · rw [hEl_map, h.2.2, map_zero]

end

private theorem onComp_map {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ]
    [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} {P : Cond O rbar} {ρ₀ : Γ →* Matrix ι ι O}
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') {r : Lift O rbar R} (h : OnComp P ρ₀ r) : OnComp P ρ₀ (r.map f) := by
  obtain ⟨B, i1, i2, i3, i4, ρ', hP, hρ, y, hy⟩ := h
  refine ⟨B, i1, i2, i3, i4, ρ', hP, hρ, f.comp y, ?_⟩
  subst hy
  apply Lift.ext
  ext g a b
  simp [Lift.map_hom]

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), (D.IsPt ρ → D.IsEq ρ) ∧ ∀ (R' : Type) [CommRing R'] [Algebra c.O R'] [IsCO c.O R'] (f : R →ₐ[c.O] R'), (D.IsPt ρ → D.IsPt (ρ.map f)) ∧ (D.IsEq ρ → D.IsEq (ρ.map f)) := by
  intro Ω _ _ _ l _ c D _ R _ _ _ ρ
  have hL : ∀ {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt l) S),
      OnComp D.condL (D.r0At l) r → D.condL S r := by
    intro S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hP, _, y, rfl⟩ := hr
    exact condL_map D y ρ' hP
  have hP : ∀ (p : ℕ) {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt p) S),
      OnComp (D.condP p) (D.r0At p) r → D.condP p S r := by
    intro p S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hQ, _, y, rfl⟩ := hr
    exact condP_map D p y ρ' hQ
  refine ⟨fun h => ⟨h.mult, h.unr, h.nrm, hL _ h.atL, fun p hp => hP p _ (h.atP p hp)⟩, ?_⟩
  intro R' _ _ _ f
  refine ⟨fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩,
    fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩⟩
  · rw [loc_map]
    exact onComp_map f h.atL
  · rw [loc_map]
    exact onComp_map f (h.atP p hp)
  · rw [loc_map]
    exact condL_map D f _ h.atL
  · rw [loc_map]
    exact condP_map D p f _ (h.atP p hp)
end
