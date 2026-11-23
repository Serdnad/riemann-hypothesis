module

public import Formalism.CyclotomicNorms.StatementT
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle050
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle256
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle151
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle109
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle203
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle117
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle215
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle181
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle252
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Mathlib.Data.FunLike.Fintype

@[expose] public section

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PowAut

theorem exists_coprime_lift (N k a : ℕ) (hN : 0 < N) (hk : 0 < k) (ha : a.Coprime N) :
    ∃ b : ℕ, b.Coprime (N * k) ∧ b ≡ a [MOD N] := by
  haveI : NeZero (N * k) := ⟨(Nat.mul_pos hN hk).ne'⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Dvd.intro k rfl : N ∣ N * k)
    (ZMod.unitOfCoprime a ha)
  refine ⟨(u : ZMod (N * k)).val, ZMod.val_coe_unit_coprime u, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have h := congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
    ZMod.coe_unitOfCoprime] at h
  rw [← h, ZMod.natCast_val]

theorem exists_exponents (M n : ℕ) (hM : 0 < M) (hn : n.Coprime M) :
    ∃ a : ℕ → ℕ, a 0 = n ∧ (∀ j, (a j).Coprime (M * j.factorial)) ∧
      ∀ i j, i ≤ j → a j ≡ a i [MOD M * i.factorial] := by
  have step : ∀ j : ℕ, ∀ a : {a : ℕ // a.Coprime (M * j.factorial)},
      ∃ b : {b : ℕ // b.Coprime (M * (j + 1).factorial)}, b.1 ≡ a.1 [MOD M * j.factorial] := by
    intro j a
    obtain ⟨b, hb, hb'⟩ := exists_coprime_lift (M * j.factorial) (j + 1) a.1
      (Nat.mul_pos hM j.factorial_pos) j.succ_pos a.2
    refine ⟨⟨b, ?_⟩, hb'⟩
    rw [Nat.factorial_succ, mul_comm (j + 1), ← mul_assoc]
    exact hb
  choose f hf using step
  let s : ∀ j : ℕ, {a : ℕ // a.Coprime (M * j.factorial)} := fun j =>
    Nat.rec (motive := fun j => {a : ℕ // a.Coprime (M * j.factorial)})
      ⟨n, by simpa using hn⟩ f j
  have hs : ∀ j, s (j + 1) = f j (s j) := fun j => rfl
  refine ⟨fun j => (s j).1, rfl, fun j => (s j).2, ?_⟩
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact Nat.ModEq.refl _
  | succ j hij ih =>
    have h1 : (s (j + 1)).1 ≡ (s j).1 [MOD M * j.factorial] := by rw [hs]; exact hf j (s j)
    exact (h1.of_dvd (Nat.mul_dvd_mul_left M (Nat.factorial_dvd_factorial hij))).trans ih

theorem orderOf_pos_of_ne_zero (g : ℕ) [Fact g.Prime] (x : AlgebraicClosure (ZMod g))
    (hx : x ≠ 0) : 0 < orderOf x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI := Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})
  let y : IntermediateField.adjoin (ZMod g) {x} :=
    ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  have h2 : x ^ (Fintype.card (IntermediateField.adjoin (ZMod g) {x}) - 1) = 1 :=
    congrArg Subtype.val h1
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨_, Nat.sub_pos_of_lt Fintype.one_lt_card, h2⟩)

theorem exists_powHom {K : Type*} [Field K] (hK : ∀ x : K, x ≠ 0 → 0 < orderOf x)
    (M n : ℕ) (hM : 0 < M) (hn : n.Coprime M) :
    ∃ θ : K →* K, Function.Injective θ ∧ (∀ x, orderOf (θ x) = orderOf x) ∧
      ∀ x, x ^ M = 1 → θ x = x ^ n := by
  classical
  obtain ⟨a, ha0, hac, ha⟩ := exists_exponents M n hM hn
  let t : K → K := fun x => if x = 0 then 0 else x ^ a (orderOf x)
  have t0 : t 0 = 0 := if_pos rfl
  have ht : ∀ x : K, x ≠ 0 → ∀ j, orderOf x ≤ j → t x = x ^ a j := by
    intro x hx j hj
    have : t x = x ^ a (orderOf x) := if_neg hx
    rw [this]
    have h := (ha _ _ hj).of_dvd
      (Dvd.dvd.mul_left (Nat.dvd_factorial (hK x hx) le_rfl) M)
    rw [← pow_mod_orderOf x (a j), ← pow_mod_orderOf x (a (orderOf x)), h]
  let θ : K →* K :=
    { toFun := t
      map_one' := by rw [ht 1 one_ne_zero _ le_rfl, one_pow]
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · rw [hx, zero_mul, t0, zero_mul]
        by_cases hy : y = 0
        · rw [hy, mul_zero, t0, mul_zero]
        rw [ht x hx (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          ht y hy (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          ht _ (mul_ne_zero hx hy) (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          mul_pow] }
  have hθ : ∀ x, θ x = t x := fun _ => rfl
  have hord : ∀ x, orderOf (θ x) = orderOf x := by
    intro x
    by_cases hx : x = 0
    · rw [hθ, hx, t0]
    rw [hθ, ht x hx _ le_rfl]
    exact Nat.Coprime.orderOf_pow ((hac (orderOf x)).coprime_dvd_right
      (Dvd.dvd.mul_left (Nat.dvd_factorial (hK x hx) le_rfl) M)).symm
  have hne : ∀ x : K, x ≠ 0 → θ x ≠ 0 := by
    intro x hx
    rw [hθ, ht x hx _ le_rfl]
    exact pow_ne_zero _ hx
  refine ⟨θ, ?_, hord, ?_⟩
  · intro x y hxy
    by_cases hy : y = 0
    · by_contra h
      exact hne x (hy ▸ h) (by rw [hxy, hy, hθ, t0])
    have h1 : θ (x * y⁻¹) * θ y = 1 * θ y := by
      rw [← map_mul, inv_mul_cancel_right₀ hy, one_mul, hxy]
    have h2 := mul_right_cancel₀ (hne y hy) h1
    have h3 : orderOf (x * y⁻¹) = 1 := by rw [← hord, h2, orderOf_one]
    rw [orderOf_eq_one_iff, mul_inv_eq_one₀ hy] at h3
    exact h3
  · intro x hxM
    have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at hxM
      exact zero_ne_one hxM
    have h := (ha 0 (orderOf x) (Nat.zero_le _)).of_dvd
      (Dvd.dvd.mul_right (orderOf_dvd_of_pow_eq_one hxM) _)
    rw [hθ, ht x hx _ le_rfl, ← ha0, ← pow_mod_orderOf x (a 0),
      ← pow_mod_orderOf x (a (orderOf x)), h]

theorem exists_powHom_fbar : ∀ (g : ℕ) [Fact g.Prime] (M n : ℕ), 0 < M → n.Coprime M →
    ∃ θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g, Function.Injective θ ∧
      (∀ x, orderOf (θ x) = orderOf x) ∧ ∀ x, x ^ M = 1 → θ x = x ^ n :=
  fun g _ M n hM hn => exists_powHom (orderOf_pos_of_ne_zero g) M n hM hn

end GlobalTheory.PowAut
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.CocycleCount

theorem card_linear_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Module (ZMod N) A]
    [Finite A] : Finite (A →ₗ[ZMod N] ZMod N) ∧ Nat.card (A →ₗ[ZMod N] ZMod N) ≤ Nat.card A := by
  have h1 : Finite (A →ₗ[ZMod N] ZMod N) := DFunLike.finite _
  have h2 : Finite (A →+ ZMod N) := DFunLike.finite _
  refine ⟨h1, le_trans ?_ (GlobalTheory.natCard_addMonoidHom_zmod_le N A)⟩
  exact Nat.card_le_card_of_injective (fun f => f.toAddMonoidHom) LinearMap.toAddMonoidHom_injective

theorem card_H2_le (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Finite (ReciprocityTheory.Gal.H2 rho) ∧ Nat.card (ReciprocityTheory.Gal.H2 rho) ≤ Nat.card M := by
  have hT := card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  have hTc : Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) ≤ Nat.card M := hT.2
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  have hA := card_linear_le N A
  have hAc : Nat.card A ≤ Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have := hA.1
  refine ⟨Finite.of_equiv _ E.symm, ?_⟩
  rw [Nat.card_congr E]
  exact hA.2.trans (hAc.trans hTc)

theorem card_cocycles_mul_invariants_discrete (R : Type) [CommRing R] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) :
    Nat.card (ReciprocityTheory.Gal.Z1 rho) * Nat.card (ReciprocityTheory.Gal.H0 rho) =
      Nat.card (ReciprocityTheory.Gal.H1 rho) * Nat.card M := by
  have hle : ReciprocityTheory.Gal.B1 rho ≤ ReciprocityTheory.Gal.Z1 rho := by
    rintro _ ⟨m, rfl⟩
    refine ⟨?_, fun g h => ?_⟩
    · exact (hrho.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [ReciprocityTheory.Gal.amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype)
  have h2 : Nat.card ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype) =
      Nat.card (ReciprocityTheory.Gal.B1 rho) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hk : LinearMap.ker (ReciprocityTheory.Gal.d0 rho) = ReciprocityTheory.Gal.H0 rho := by
    ext m
    rw [LinearMap.mem_ker, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [ReciprocityTheory.Gal.amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (ReciprocityTheory.Gal.d0 rho))
  have h4 : Nat.card (M ⧸ LinearMap.ker (ReciprocityTheory.Gal.d0 rho)) = Nat.card (ReciprocityTheory.Gal.B1 rho) :=
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv
  rw [h4, hk] at h3
  rw [h1, h2, h3]
  ring

def repOfAction (N : ℕ) {G M : Type} [Monoid G] [AddCommGroup M] [Module (ZMod N) M]
    (a : G → M →+ M) (h1 : ∀ m, a 1 m = m) (hmul : ∀ g h m, a (g * h) m = a g (a h m)) :
    Representation (ZMod N) G M where
  toFun g := AddMonoidHom.toZModLinearMap N (a g)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hmul g h)

theorem count_of_euler (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (hrho : ReciprocityTheory.Gal.ContAction rho)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m) :
    {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (d + 2) := by
  obtain ⟨hf2, hc2⟩ := card_H2_le _ _ M _ rho e hb
  have hZ := card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have h0 : 0 < Nat.card (ReciprocityTheory.Gal.H0 rho) := Nat.card_pos
  have h2 : 0 < Nat.card (ReciprocityTheory.Gal.H2 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hZ' : Nat.card (ReciprocityTheory.Gal.Z1 rho) =
      Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [hZ, hEu]
    ring
  let E : ↥{c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} ≃
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        (IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun g h => by
          have := c.2.2 (φ g) (φ h)
          rw [ha, φ.symm_apply_apply, ← map_mul] at this
          exact this⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) :=
    Nat.finite_of_card_ne_zero (by rw [hZ']; positivity)
  refine ⟨Set.finite_coe_iff.1 (Finite.of_equiv _ E.symm), ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr E, hZ', pow_succ' _ (_ + 1)]
  exact Nat.mul_le_mul_right _ hc2

theorem cocycles_finite_ncard_le :
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, l ^ r • m = 0) → (∀ m, IsLocallyConstant fun g => a g m) → {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧ {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤ Nat.card M ^ (Module.finrank ℚ_[l] ↥K.1 + 2) := by
  intro hT hE l _ K r M _ _ a h1 hmul hr hlc
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  have hEu := hE l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  exact count_of_euler _ _ _ φ hφ M _ rho hrho e hb _ hEu a fun _ _ => rfl

end GlobalTheory.CocycleCount
end

section

noncomputable section

namespace GlobalTheory.ShapeNeg

open Formalism.NG Formalism.RepresentationBoundsCohomology.JT ReciprocityTheory.Gal

theorem shapeG_of_localDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) :
    ReciprocityTheory.ChartRestriction.T2.ShapeG := by
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hcyc e he M _ _ u ρ hρ
  haveI := hO.ring
  haveI := hO.compact
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  haveI hres : Finite (IsLocalRing.ResidueField O) := GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr hO.adic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]; exact hO.p_mem
  have hpn : ∀ n : ℕ, ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} := fun n => by
    rw [← Ideal.span_singleton_pow]; exact Ideal.pow_mem_pow hpϖ n
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  set d := Module.finrank ℚ_[p] K with hd
  set ε' : Formalism.GaloisCohomology.GK p K →* Oˣ := ε.comp i.symm.toMulEquiv.toMonoidHom with hε'
  have hcyc' : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε') g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n} := hcyc
  have hlcε : ∀ N : ℕ, IsLocallyConstant
      (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O)) := by
    intro N
    have h := (GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow ε' hcyc' N).comp_continuous i.continuous
    convert h using 1
    funext g
    change Ideal.Quotient.mk _ ((ε g : Oˣ) : O) =
      Ideal.Quotient.mk _ ((ε (i.symm (i g)) : Oˣ) : O)
    rw [i.symm_apply_apply]
  have hMt : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer hϖ (u m)
    exact ⟨n, u.injective (by rw [map_smul, hn, map_zero])⟩
  have hMp : ∀ m : M, ∃ N : ℕ, (p : O) ^ N • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := hMt m
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hpn n)
    exact ⟨n, by rw [← hb, mul_smul, hn, smul_zero]⟩
  have hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m := fun m => by
    obtain ⟨y, hy⟩ := GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer hϖ (u m)
    exact ⟨u.symm y, u.injective (by rw [map_smul, LinearEquiv.apply_symm_apply, hy])⟩
  have hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m) := fun m => by
    obtain ⟨N, hN⟩ := hMp m
    exact GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' ε hlcε e ρ hρ m N hN
  set ρ' : Representation O (Formalism.GaloisCohomology.GK p K) M := ρ.comp i.symm.toMulEquiv.toMonoidHom with hρ'def
  have hρ' : ∀ g m, ρ' g m = ((((ε' g) ^ e)⁻¹ : Oˣ) : O) • m := fun g m => hρ _ m
  have hcont : ∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ') := fun n h =>
    GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant ρ' p n (ϖ ^ n) h (fun m _ => (hlc m).comp_continuous i.symm.continuous)
  obtain ⟨σ1, hσ1⟩ := GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' e (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK e he)
  obtain ⟨σ2, hσ2⟩ := GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' (e + 1) (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK (e + 1) (Nat.succ_pos e))
  have hNfin : Finite ρ.invariants := by
    refine GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist u ρ (i.symm σ1) ((((ε (i.symm σ1)) ^ e)⁻¹ : Oˣ) : O) ?_ (hρ _)
    intro h1
    apply hσ1
    have h2 : ((ε (i.symm σ1)) ^ e)⁻¹ = 1 := Units.ext h1
    exact inv_eq_one.1 h2
  obtain ⟨C, hC⟩ := GlobalTheory.T.h2_bounded_twist hT hK hϖ hpϖ ε' hcyc' e u ρ' hρ' σ2 hσ2 hcont
  have hone2 := GlobalTheory.T.card_H2_level_rep_one_le hT hK hϖ u ρ' (hpn 1) (hcont 1 (hpn 1))
  have key : ∀ n : ℕ, 0 < n →
      Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
      (letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) =
        Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) := by
    intro n hn
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)
    obtain ⟨hLf, hLc⟩ := GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot hϖ u n
    obtain ⟨hH1f, -⟩ := GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n))
      (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn (hcont n (hpn n))
    have hEu := hE p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn
      (hcont n (hpn n))
    obtain ⟨t0, t1⟩ := GlobalTheory.T.transfer_card_H0_H1_eq i ρ p n (ϖ ^ n) (hpn n)
    have hH1O : Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) :=
      Nat.finite_of_card_ne_zero (by rw [t1]; exact Nat.card_pos.ne')
    obtain ⟨hXf, hX⟩ := GlobalTheory.T.card_H1_level_rep_formula ρ ϖ n hdiv hlc hH1O
    have h0c := GlobalTheory.T.card_H0_level_rep_eq ρ (ϖ ^ n) hNfin
    set Nq := Nat.card (ρ.invariants ⧸
      LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) with hNq
    haveI : Finite (ρ.invariants ⧸
        LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    have hpos : 0 < Nq := Nat.card_pos
    refine ⟨hXf, ?_⟩
    have e1 : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) * Nq =
        (Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) * Nq := by
      rw [← hX, t1, hEu, ← t0, h0c, hLc, ← pow_mul]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos e1
  have htors := GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion ρ ϖ hMt
  have hfin1 : Finite (LinearMap.ker (ϖ • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) := by
    have h1 := (key 1 one_pos).1
    simpa only [pow_one] using h1
  obtain ⟨a, F, _, _, hFf, ⟨φ⟩⟩ := GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite hϖ (Y := ReciprocityTheory.ChartRestriction.T2.HcLC ρ)
    (fun y => (htors y.1 y.2).imp fun n hn => Subtype.ext (by simpa using hn)) hfin1
  haveI := hFf
  refine GlobalTheory.T.torsion_shape_of_torsion_counts hϖ (ReciprocityTheory.ChartRestriction.T2.HcLC ρ) d a φ ⟨C, fun n hn => ?_⟩ ?_
  · obtain ⟨hXf, hX⟩ := key n hn
    try dsimp only at hX
    have hXpos : 0 < Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) :=
      Nat.card_pos
    rw [hX] at hXpos ⊢
    have hb := hC n hn (hpn n)
    try dsimp only at hb
    have h2pos := Nat.pos_of_mul_pos_right hXpos
    constructor
    · exact Nat.le_mul_of_pos_left _ h2pos
    · exact Nat.mul_le_mul_right _ hb
  · obtain ⟨-, hX⟩ := key 1 one_pos
    try dsimp only at hX hone2
    rw [hX]
    calc _ ≤ q * q ^ (1 * d) := Nat.mul_le_mul_right _ hone2
      _ = q ^ (d + 1) := by ring

end GlobalTheory.ShapeNeg
end
end

section

noncomputable section

namespace GlobalTheory.TripleGal.HodgeOfAtt

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem not_mem_placesOver_of_ne {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (h1 : v ∈ placesOver D.host.E p) : v ∉ placesOver D.host.E q := fun h2 => by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := ((Nat.coprime_primes hp hq).mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  exact hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)

theorem not_mem_pD (D : D7) (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : v ∉ D.ntw.pD i := by
  intro hp
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hp
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  split_ifs at hv' with h
  · exact not_mem_placesOver_of_ne D.host.pde'_prime hl (h ▸ D.host.pde_ne.symm) v hv' hv
  · exact not_mem_placesOver_of_ne D.host.pde_prime hl (Ne.symm h) v hv' hv

end GlobalTheory.TripleGal.HodgeOfAtt

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.cyclotomic_action_on_root_tower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) → ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  first | exact @GlobalTheory.ExpImage.actT_εroot_eq_pow | exact GlobalTheory.ExpImage.actT_εroot_eq_pow | (intros; apply GlobalTheory.ExpImage.actT_εroot_eq_pow <;> assumption)
end
