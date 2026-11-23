module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle003
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem one_of_pow {l : ℕ} [Fact l.Prime] (c : Coef l) {x : c.Oˣ} (hx : x ^ (l - 1) = 1)
    (h : (x : c.O) - 1 ∈ IsLocalRing.maximalIdeal c.O) : x = 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hu : IsUnit ((l - 1 : ℕ) : c.O) :=
    (dvrFacts l c.O).2.2.2.2.2.2.2.2 _ fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hx' : (x : c.O) ^ (l - 1) = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have h1 := mul_geom_sum (x : c.O) (l - 1)
  rw [hx', sub_self, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact Units.ext (sub_eq_zero.1 h1)
  · exfalso
    have h2 := congrArg (IsLocalRing.residue c.O) h1
    have h3 : IsLocalRing.residue c.O x = 1 := by
      rw [← sub_eq_zero, ← map_one (IsLocalRing.residue c.O), ← map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).2 h

    rw [map_sum, map_zero] at h2
    simp only [map_pow, h3, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h2
    have h4 := hu.map (IsLocalRing.residue c.O)
    rw [map_natCast, h2] at h4
    exact not_isUnit_zero h4

private theorem red_iff {l : ℕ} [Fact l.Prime] (c : Coef l) (u v : ℤ_[l]ˣ) :
    algebraMap ℤ_[l] c.O u - algebraMap ℤ_[l] c.O v ∈ IsLocalRing.maximalIdeal c.O ↔
      KStar.TotallyRealRoots.red l u = KStar.TotallyRealRoots.red l v := by
  have := (dvrFacts l c.O).2.2.1
  rw [← map_sub, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff,
    ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, sub_eq_zero, Units.ext_iff]
  rfl

private theorem exists_strictHenselian_absolutely_closed_local_ring (l : ℕ) [Fact l.Prime] :
    ∃ T : ℤ_[l]ˣ →* ℤ_[l]ˣ, ∀ u, T u ^ (l - 1) = 1 ∧ KStar.TotallyRealRoots.red l (T u) = KStar.TotallyRealRoots.red l u := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hnd : ¬ l ∣ l - 1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  choose t h1 h2 using KStar.TotallyRealRoots.exists_teich (l := l)
  refine ⟨MonoidHom.mk' t fun a b => ?_, fun u => ⟨(mem_rootsOfUnity _ _).1 (h1 u), h2 u⟩⟩
  rw [← mul_inv_eq_one]
  refine KStar.TotallyRealRoots.eq_one_of_mem_princ_one hnd (mul_mem (h1 _) (inv_mem (mul_mem (h1 _) (h1 _)))) ?_
  rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, h2, h2, h2, map_mul, mul_inv_cancel]

private theorem gen_pow {Γ M : Type} [Group Γ] [CommGroup M] {l : ℕ} [Fact l.Prime] {w : Γ →* M} {r : Γ →* (ZMod l)ˣ}
    (h : w.ker = r.ker) {σ : Γ} (hσ : ∀ x, x ∈ Subgroup.zpowers (r σ)) (j : ℕ) : w σ ^ j = 1 ↔ l - 1 ∣ j := by
  rw [← map_pow, ← MonoidHom.mem_ker, h, MonoidHom.mem_ker, map_pow, ← orderOf_dvd_iff_pow_eq_one,
    orderOf_eq_card_of_forall_mem_zpowers hσ, Nat.card_eq_fintype_card, ZMod.card_units]

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem ker_red (c : Coef l) {w : G ℚ Ω →* c.Oˣ} (h : IsOmT c w) :
    w.ker = ((KStar.TotallyRealRoots.red l).comp (cycZ ℚ Ω l)).ker := by
  ext σ
  have h1 : ((w σ : c.Oˣ) : c.O) - algebraMap ℤ_[l] c.O (cycZ ℚ Ω l σ : ℤ_[l]ˣ) ∈ IsLocalRing.maximalIdeal c.O := h.2 σ
  have h2 := red_iff c (cycZ ℚ Ω l σ) 1
  rw [map_one, Units.val_one, map_one] at h2
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, ← h2]
  constructor
  · intro e
    rw [e, Units.val_one] at h1
    simpa using neg_mem h1
  · intro e
    refine one_of_pow c (DFunLike.congr_fun h.1 σ) ?_
    simpa using add_mem h1 e

private theorem cls_pow_one (σ : G ℚ Ω) :
    Chr.cls ℚ Ω (l ^ 1) σ = cycMod ℚ Ω l 1 σ ∧ Chr.cls ℚ Ω (l ^ 1) σ = KStar.TotallyRealRoots.redPow l 1 (cycZ ℚ Ω l σ) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact ⟨(Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 σ _ fun ζ hζ =>
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω σ) ζ hζ,
    (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 σ _ fun ζ hζ => cyclotomicCharacter.spec l σ.toRingEquiv ζ hζ⟩

private theorem cls_ker : (Chr.cls ℚ Ω (l ^ 1)).ker = (Chr.cls ℚ Ω l).ker := by
  ext σ
  have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω (l ^ 1)).2.1 l (pow_one l).symm.dvd) σ
  have h2 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω l).2.1 (l ^ 1) (pow_one l).dvd) σ
  rw [MonoidHom.comp_apply] at h1 h2
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact ⟨fun h => by rw [← h1, h, map_one], fun h => by rw [← h2, h, map_one]⟩

private theorem ker_cls (c : Coef l) {w : G ℚ Ω →* c.Oˣ} (h : IsOmT c w) : w.ker = (Chr.cls ℚ Ω (l ^ 1)).ker := by
  rw [ker_red c h]
  ext σ
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, (cls_pow_one σ).2, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    ← KStar.TotallyRealRoots.princ_one_eq_ker]
  rfl

end

theorem UpperTheory.V.HV.omT :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l), (∃! w : G ℚ Ω →* c.Oˣ, IsOmT c w) ∧ ∀ w : G ℚ Ω →* c.Oˣ, IsOmT c w →
      w.ker = (cycMod ℚ Ω l 1).ker ∧ w.ker = (Chr.cls ℚ Ω l).ker ∧ orderOf w = l - 1 ∧ IsOpen (w.ker : Set (G ℚ Ω)) ∧
      (∀ σ : G ℚ Ω, IsCC σ → l ≠ 2 → w σ = -1) ∧
      (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ w.ker) ∧
      (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ j : ℕ, Ine (F := ℚ) A ≤ (w ^ j).ker → l - 1 ∣ j) ∧
      ∀ θ : G ℚ Ω →* c.Oˣ, w.ker ≤ θ.ker → ∃ b < l - 1, θ = w ^ b := by
  intro Ω _ _ _ l hl c
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  refine ⟨?_, fun w hw => ?_⟩
  · obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring l
    refine ⟨((Units.map (algebraMap ℤ_[l] c.O).toMonoidHom).comp T).comp (cycZ ℚ Ω l), ⟨?_, fun σ => ?_⟩, fun w hw => ?_⟩
    · refine MonoidHom.ext fun σ => ?_
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_pow, (hT _).1, map_one, MonoidHom.one_apply]
    · exact (red_iff c _ _).2 (hT _).2
    · refine MonoidHom.ext fun σ => ?_
      rw [← mul_inv_eq_one]
      set y : c.Oˣ := (((Units.map (algebraMap ℤ_[l] c.O).toMonoidHom).comp T).comp (cycZ ℚ Ω l)) σ with hy
      have h1 : y ^ (l - 1) = 1 := by
        rw [hy, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_pow, (hT _).1, map_one]
      have h2 : (y : c.O) - (chiO ℚ Ω l c.O σ : c.Oˣ) ∈ IsLocalRing.maximalIdeal c.O := (red_iff c _ _).2 (hT _).2
      have h3 : w σ ^ (l - 1) = 1 := DFunLike.congr_fun hw.1 σ
      refine one_of_pow c (by rw [mul_pow, inv_pow, h1, h3, inv_one, mul_one]) ?_
      have h4 := Ideal.mul_mem_right ((y⁻¹ : c.Oˣ) : c.O) _ (sub_mem (hw.2 σ) h2)
      rwa [sub_sub_sub_cancel_right, sub_mul, Units.mul_inv] at h4
  · have hk : w.ker = (Chr.cls ℚ Ω l).ker := (ker_cls c hw).trans cls_ker
    obtain ⟨f1, -, -, f4, f5⟩ := Chr.clsFacts ℚ Ω l
    obtain ⟨σ₀, hσ₀⟩ := (Chr.clsOnto Ω l).1 g
    have hp := gen_pow hk (σ := σ₀) (hσ₀ ▸ hg)
    refine ⟨?_, hk, ?_, hk ▸ f1, fun σ hσ h2 => ?_, fun A hA => hk ▸ f5 A hA, fun A hA j hj => ?_, fun θ hθ => ?_⟩
    · rw [ker_cls c hw, MonoidHom.ext fun σ => (cls_pow_one (l := l) σ).1]
    · exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hw.1)
        ((hp _).1 (DFunLike.congr_fun (pow_orderOf_eq_one w) σ₀))
    · have h1 : Chr.cls ℚ Ω l σ = -1 := f4 σ hσ
      have h3 : w σ ^ 2 = 1 := by
        rw [← map_pow, ← MonoidHom.mem_ker, hk, MonoidHom.mem_ker, map_pow, h1, neg_one_sq]
      have h4 : ((w σ : c.Oˣ) : c.O) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
      rcases sq_eq_one_iff.1 h4 with h5 | h5
      · exfalso
        have h6 : σ ∈ w.ker := Units.ext h5
        rw [hk, MonoidHom.mem_ker, h1] at h6
        have : Fact (2 < l) := ⟨by omega⟩
        exact ZMod.neg_one_ne_one (n := l) (congrArg Units.val h6)
      · exact Units.ext h5
    · obtain ⟨u, hu⟩ := KStar.TotallyRealRoots.red_surjective (l := l) g
      obtain ⟨τ, hτ, e⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
      refine (gen_pow (ker_red c hw) (σ := τ) ?_ j).1 (hj hτ)
      rw [MonoidHom.comp_apply, e, hu]
      exact hg
    · have : NeZero (l - 1) := ⟨by omega⟩
      have h1 : IsPrimitiveRoot (w σ₀) (l - 1) := ⟨(hp _).2 dvd_rfl, fun j => (hp j).1⟩
      have h2 : θ σ₀ ^ (l - 1) = 1 := by
        rw [← map_pow]
        exact hθ (by rw [MonoidHom.mem_ker, map_pow, h1.pow_eq_one])
      obtain ⟨b, hb, e⟩ := h1.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).2 h2)
      refine ⟨b, hb, MonoidHom.ext fun σ => ?_⟩
      obtain ⟨k, hk'⟩ := hg (Chr.cls ℚ Ω l σ)
      have h3 : σ * (σ₀ ^ k)⁻¹ ∈ w.ker := by
        rw [hk, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hσ₀, ← hk', mul_inv_cancel]
      have h4 := hθ h3
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3 h4
      rw [MonoidHom.pow_apply, h3, h4, ← e, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem compIne_map (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) :
    (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI hMz : NeZero (N / r ^ N.factorization r) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hMcop : (N / r ^ N.factorization r).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have fix : ∀ σ ∈ Ine (F := ℚ) A, ∀ ζ : Ω, ζ ^ (N / r ^ N.factorization r) = 1 → σ ζ = ζ :=
    fun σ hσ ζ hζ => (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hMcop ζ hζ).2 σ hσ
  have powOne : ∀ ζ : Ω, ζ ^ (N / r ^ N.factorization r) = 1 →
      ζ ^ (((1 : (ZMod (N / r ^ N.factorization r))ˣ) : ZMod (N / r ^ N.factorization r))).val = ζ := by
    intro ζ hζ
    rw [Units.val_one, ZMod.val_one_eq_one_mod]
    by_cases h1 : N / r ^ N.factorization r = 1
    · rw [h1, pow_one] at hζ
      rw [hζ, one_pow]
    · rw [Nat.mod_eq_of_lt (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hMz.out, h1⟩), pow_one]
  have kerCls : ∀ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω (N / r ^ N.factorization r) σ = 1 := fun σ hσ =>
    (Chr.clsFacts ℚ Ω _).2.2.1 σ 1 (fun ζ hζ => by rw [fix σ hσ ζ hζ, powOne ζ hζ])
  ext u
  rw [Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have e := congrArg (fun f => f σ) ((Chr.clsFacts ℚ Ω N).2.1 _ (Nat.ordCompl_dvd N r))
    simp only [MonoidHom.comp_apply] at e
    rw [e]
    exact kerCls σ hσ
  · intro hu
    obtain ⟨v, hv⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
    obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA v
    refine ⟨σ, hσ, ?_⟩
    apply (Chr.clsFacts ℚ Ω N).2.2.1
    refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).mpr ⟨?_, ?_⟩
    · intro ζ hζ
      rw [hu, powOne ζ hζ]
      exact fix σ hσ ζ hζ
    · rw [← hv, ← hσv]
      rfl

private theorem compIne_unit {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) :
    (comp r χ).toUnitHom = χ.toUnitHom.comp (proj r N) := by
  ext u
  simp [UpperTheory.V.HV.comp]

theorem UpperTheory.V.HV.compIne :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ), r.Prime → ∀ A : ValuationSubring Ω, A.valuation (r : Ω) < 1 →
      (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (proj r N).range ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] (χ : DirichletCharacter O N), (∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω χ σ = Chr.dirG ℚ Ω (comp r χ) σ) ∧
        (Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω χ).ker ↔ comp r χ = 1) := by
  intro Ω _ _ _ N _ r hr A hA
  have hrange : (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (proj r N).range := by
    rw [compIne_map Ω N r hr A hA, (projFacts N r hr).2.2.2.2.2.1]
  refine ⟨hrange, fun O _ _ χ => ?_⟩
  have same : ∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω χ σ = Chr.dirG ℚ Ω (comp r χ) σ := by
    intro σ hσ
    have hm : Chr.cls ℚ Ω N σ ∈ (proj r N).range := by
      rw [← hrange]
      exact Subgroup.mem_map_of_mem _ hσ
    obtain ⟨w, hw⟩ := hm
    simp only [Chr.dirG, MonoidHom.comp_apply, compIne_unit]
    rw [← hw, (projFacts N r hr).2.2.1 w]
  refine ⟨same, ⟨fun h => ?_, fun h σ hσ => ?_⟩⟩
  · rw [MulChar.eq_one_iff]
    intro u
    have hm : proj r N u ∈ (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) := by
      rw [hrange]
      exact ⟨u, rfl⟩
    obtain ⟨σ, hσ, hσu⟩ := hm
    have h1 := h hσ
    rw [MonoidHom.mem_ker] at h1
    simp only [Chr.dirG, MonoidHom.comp_apply] at h1
    rw [← MulChar.coe_toUnitHom, compIne_unit, MonoidHom.comp_apply, ← hσu, h1, Units.val_one]
  · rw [MonoidHom.mem_ker, same σ hσ]
    simp only [Chr.dirG, MonoidHom.comp_apply, h]
    ext
    simp
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.bchiFacts :
    ∀ (h : Host) (t : ℕ), h.Big t → (∀ l ∈ Bchi h.chi, l < h.q1 ∧ l < h.d) ∧ pK h.chi ∈ Bchi h.chi ∧ ¬ pK h.chi ∣ h.N ∧ ¬ pOne h.chi ∣ h.N ∧
      ∀ l, l.Prime → l ≠ 2 → l ∉ Bchi h.chi → 5 ≤ l ∧ ¬ l ∣ h.o ∧ ¬ l ∣ h.q ∧ l ≠ pK h.chi ∧ ¬ l ∣ hStar h.chi ∧ l ≠ pOne h.chi ∧
        ¬ l ∣ h.H.index ∧ ∀ e, 0 < e → e < t → l - 1 ∣ 2 * e → 2 ≤ e ∧ l ≤ 2 * t ∧ ¬ l ∣ h.N := by
  intro h t hB
  obtain ⟨ht1, ht2, hy⟩ := hB
  obtain ⟨hidx, -, -, ho, -, hNp, -⟩ := hostIndex h
  obtain ⟨⟨hKp, -, hK7, hKc⟩, ⟨hOp, -, hOc⟩, -⟩ := pK_pOne_prime_conditions h.chi
  have eq : h.q = h.chi.N := rfl
  have eo : h.o = ordC h.chi := rfl
  obtain ⟨yq1, yqd⟩ := hy h.q (by simp)
  obtain ⟨yo1, yod⟩ := hy h.o (by simp)
  obtain ⟨yK1, yKd⟩ := hy (pK h.chi) (by simp)
  obtain ⟨yS1, ySd⟩ := hy (hStar h.chi) (by simp)
  obtain ⟨yO1, yOd⟩ := hy (pOne h.chi) (by simp)
  have hS0 : hStar h.chi ≠ 0 := (NumberField.classNumber_pos (K := Kstar (pK h.chi))).ne'
  have hq0 : h.chi.N ≠ 0 := h.chi.ne.out
  have hP0 : ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨ho.ne', hq0⟩, hKp.ne_zero⟩, hS0⟩, hOp.ne_zero⟩
  have memB : ∀ l, l.Prime → l ≠ 2 → l ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi →
      l ∈ Bchi h.chi := by
    intro l hl hl2 hlP
    simp only [Bchi, Finset.mem_insert, Finset.mem_erase, Nat.mem_primeFactors]
    exact Or.inr ⟨hl2, hl, hlP, hP0⟩
  have dO : ordC h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (((dvd_mul_right _ _).mul_right _).mul_right _).mul_right _
  have dq : h.chi.N ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (((dvd_mul_left _ _).mul_right _).mul_right _).mul_right _
  have dK : pK h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    ((dvd_mul_left _ _).mul_right _).mul_right _
  have dS : hStar h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (dvd_mul_left _ _).mul_right _
  have dO1 : pOne h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    dvd_mul_left _ _
  refine ⟨?_, memB _ hKp (by omega) dK, ?_, ?_, ?_⟩
  · intro l hl
    simp only [Bchi, Finset.mem_insert, Finset.mem_erase, Nat.mem_primeFactors] at hl
    rcases hl with rfl | ⟨-, hlp, hlP, -⟩
    · exact ⟨by omega, by omega⟩
    · have le : ∀ y, y ≠ 0 → l ∣ y → l ≤ y := fun y hy0 hly => Nat.le_of_dvd (Nat.pos_of_ne_zero hy0) hly
      rcases hlp.dvd_mul.mp hlP with h4 | h5
      · rcases hlp.dvd_mul.mp h4 with h3 | hS
        · rcases hlp.dvd_mul.mp h3 with h2 | hK
          · rcases hlp.dvd_mul.mp h2 with hO | hQ
            · have := le _ ho.ne' hO
              exact ⟨by omega, by omega⟩
            · have := le _ hq0 hQ
              exact ⟨by omega, by omega⟩
          · have := le _ hKp.ne_zero hK
            exact ⟨by omega, by omega⟩
        · have := le _ hS0 hS
          exact ⟨by omega, by omega⟩
      · have := le _ hOp.ne_zero h5
        exact ⟨by omega, by omega⟩
  · intro hd'
    rcases (hNp _ hKp).mp hd' with h2 | hq' | h1 | h1
    · omega
    · exact (Nat.Prime.coprime_iff_not_dvd hKp).mp hKc hq'
    · omega
    · omega
  · intro hd'
    have nd := (Nat.Prime.coprime_iff_not_dvd hOp).mp hOc
    rcases (hNp _ hOp).mp hd' with h2 | hq' | h1 | h1
    · exact nd (by rw [h2]; exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _)
    · exact nd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hq' 2) _)
    · omega
    · omega
  · intro l hl hl2 hlB
    have h3 : l ≠ 3 := by
      intro e
      subst e
      exact hlB (Finset.mem_insert_self _ _)
    have h5 : 5 ≤ l := by
      by_contra hc
      have := hl.two_le
      interval_cases l
      · exact hl2 rfl
      · exact h3 rfl
      · norm_num at hl
    have nd : ∀ y, y ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi → ¬ l ∣ y :=
      fun y hy hly => hlB (memB l hl hl2 (hly.trans hy))
    refine ⟨h5, nd _ dO, nd _ dq, fun e => nd _ dK (by rw [e]), nd _ dS, fun e => nd _ dO1 (by rw [e]), ?_, ?_⟩
    · intro hi
      rcases hl.dvd_mul.mp (hi.trans hidx) with h2 | hO
      · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h2))
      · exact nd _ dO hO
    · intro e he0 het hle
      have hl1 : l - 1 ≤ 2 * e := Nat.le_of_dvd (by omega) hle
      refine ⟨by omega, by omega, fun hN => ?_⟩
      rcases (hNp l hl).mp hN with h2 | hq' | h1 | h1
      · exact hl2 h2
      · exact nd _ dq hq'
      · omega
      · omega
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem coe_unitsMap {g N : ℕ} [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g) = (((u : ZMod N).val : ℕ) : ZMod g) := by
  show ZMod.castHom h (ZMod g) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem pm_iff {n : ℕ} (v : (ZMod n)ˣ) (a : ℕ) (hv : (v : ZMod n) = (a : ZMod n)) :
    (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) ↔ v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) := by
  have key : v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) ↔ v = 1 ∨ v = -1 := by
    constructor
    · rintro ⟨k, rfl⟩
      rcases Int.even_or_odd k with he | ho
      · left
        exact he.neg_one_zpow
      · right
        exact ho.neg_one_zpow
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  rw [key, ← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← hv]
  simp only [Units.ext_iff, Units.val_one, Units.val_neg, eq_neg_iff_add_eq_zero]

private theorem jac_iff {p : ℕ} (hp : p.Prime) (v : (ZMod p)ˣ) (a : ℕ) (hv : (v : ZMod p) = (a : ZMod p)) :
    jacobiSym (a : ℤ) p = 1 ↔ v ∈ (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
  haveI := Fact.mk hp
  have ha : ((a : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    rw [← hv]
    exact v.ne_zero
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p ha]
  push_cast
  rw [← hv]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by simpa using hr)
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← hw]
    simp [sq]

theorem UpperTheory.V.HV.hostLevel :
    ∀ (h : Host) (E : Type) [Field E] [NumberField E], IsChiField h.chi h.ex h.q1 h.d E → Chr.HasLevel E h.N h.H := by
  intro h E _ _ hchi
  have hc := (isCompField_ofChar h.chi h.ex h.q1 h.d E).mpr hchi
  obtain ⟨H', hlev, hmem⟩ := Chr.abLevel.2 (AbF.ofChar h.chi) h.ex h.q1 h.d E hc h.N h.two_pow_dvd h.q_dvd h.host_q1_dvd_N h.d_dvd
  have hq1 : h.q1.Prime := h.pair.1
  have hd : h.d.Prime := h.pair.2.2.1
  convert hlev using 1
  ext u
  have hu : (u : ZMod h.N) = (((u : ZMod h.N).val : ℕ) : ZMod h.N) := (ZMod.natCast_zmod_val _).symm
  rw [hmem u _ hu]
  simp only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap]
  rw [← pm_iff (ZMod.unitsMap h.two_pow_dvd u) _ (coe_unitsMap _ u),
    ← jac_iff hq1 (ZMod.unitsMap h.host_q1_dvd_N u) _ (coe_unitsMap _ u),
    ← jac_iff hd (ZMod.unitsMap h.d_dvd u) _ (coe_unitsMap _ u)]
  have hk : (ZMod.unitsMap h.q_dvd u) ∈ (MulChar.toUnitHom h.chi.χ).ker ↔
      (AbF.ofChar h.chi).ker ((u : ZMod h.N).val) := by
    constructor
    · intro hv
      exact ⟨_, hv, coe_unitsMap _ u⟩
    · rintro ⟨w, hw, hwa⟩
      have hweq : w = ZMod.unitsMap h.q_dvd u := Units.ext (hwa.trans (coe_unitsMap _ u).symm)
      rwa [← hweq]
  rw [hk]
  tauto
end
