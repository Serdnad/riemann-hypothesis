module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModulePeriodMapToBcris
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle312
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.TameRel

section Abstract

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]


omit [IsTopologicalGroup Γ] in
theorem hom_trivial {l : ℕ} (hU : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → U.index.Coprime l)
    {C : Type} [Group C] (f : Γ →* C) (hf : IsOpen (f.ker : Set Γ)) (n : ℕ) (hC : ∀ x : C, x ^ l ^ n = 1) (j : Γ) :
    f j = 1 := by
  have h1 : f j ^ f.ker.index = 1 := by
    rw [← map_pow]
    exact f.ker.pow_index_mem j
  have h2 := (hU _ inferInstance hf).pow_right n
  have h3 := pow_gcd_eq_one.2 ⟨h1, hC (f j)⟩
  rwa [h2, pow_one] at h3


omit [IsTopologicalGroup Γ] in
theorem vanish_of_additive {l : ℕ} {J : Subgroup Γ}
    (hU : ∀ U : Subgroup J, U.Normal → IsOpen (U : Set J) → U.index.Coprime l)
    (K : Type) [Field K] [CharP K l] {W : Type} [AddCommGroup W] [Module K W] (w : Γ → W) (hw : IsLocallyConstant w)
    (hadd : ∀ g ∈ J, ∀ h ∈ J, w (g * h) = w g + w h) : ∀ j ∈ J, w j = 0 := by
  intro j hj
  let f : J →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  have hf : IsOpen (f.ker : Set J) := (hw {0}).preimage continuous_subtype_val
  refine hom_trivial hU f hf 1 (fun x => ?_) ⟨j, hj⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, pow_one, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul, toAdd_one]


omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem additive_zpow {D : Subgroup Γ} {W : Type} [AddCommGroup W] (w : Γ → W)
    (hadd : ∀ g ∈ D, ∀ h ∈ D, w (g * h) = w g + w h) {γ : Γ} (hγ : γ ∈ D) (k : ℤ) : w (γ ^ k) = k • w γ := by
  let f : D →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  exact congrArg Multiplicative.toAdd (map_zpow f ⟨γ, hγ⟩ k)

theorem vanish_closure {D J : Subgroup Γ} (hJ : J ≤ D) {W : Type} [AddCommGroup W] (w : Γ → W) (hw : IsLocallyConstant w)
    (hadd : ∀ g ∈ D, ∀ h ∈ D, w (g * h) = w g + w h) {γ : Γ} (hγ : γ ∈ D) (h0 : w γ = 0) (h1 : ∀ j ∈ J, w j = 0) :
    ∀ σ ∈ (Subgroup.zpowers γ ⊔ J).topologicalClosure, w σ = 0 := by
  let f : D →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  have hle : Subgroup.zpowers γ ⊔ J ≤ f.ker.map D.subtype := by
    refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨γ, hγ⟩, ?_, rfl⟩) fun j hj => ⟨⟨j, hJ hj⟩, ?_, rfl⟩
    · exact congrArg Multiplicative.ofAdd h0
    · exact congrArg Multiplicative.ofAdd (h1 j hj)
  have hsub : ((Subgroup.zpowers γ ⊔ J : Subgroup Γ) : Set Γ) ⊆ {x | w x = 0} := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hle hx
    exact congrArg Multiplicative.toAdd hy
  intro σ hσ
  exact closure_minimal hsub (hw.isClosed_fiber 0) hσ


omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem second_pow {D : Subgroup Γ} {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] (z0 z1 : Γ → W)
    (lam : Γ → K) (hlam : ∀ g ∈ D, ∀ h ∈ D, lam (g * h) = lam g + lam h)
    (h1 : ∀ g ∈ D, ∀ h ∈ D, z1 (g * h) = z1 g + z1 h + lam g • z0 h) (h01 : z0 1 = 0) {γ : Γ} (hγ : γ ∈ D) (n : ℕ) :
    z1 (γ ^ n) = (n : K) • z1 γ + ((n.choose 2 : ℕ) : K) • lam γ • z0 γ := by
  induction n with
  | zero =>
    have := h1 1 D.one_mem 1 D.one_mem
    rw [mul_one, h01, smul_zero, add_zero] at this
    simpa using this
  | succ n ih =>
    have e : lam (γ ^ n) = (n : K) * lam γ := by
      have := additive_zpow lam hlam hγ n
      rwa [zpow_natCast, zsmul_eq_mul, Int.cast_natCast] at this
    rw [pow_succ, h1 _ (D.pow_mem hγ n) _ hγ, ih, e, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast
    module

end Abstract

theorem cast_of_mod {K : Type} [Field K] {l M q : ℕ} [CharP K l] (hM : 1 ≤ M) (hq : q % (2 * l ^ M) = 1) :
    (q : K) = 1 ∧ ((q.choose 2 : ℕ) : K) = 0 := by
  have h := Nat.div_add_mod q (2 * l ^ M)
  rw [hq] at h
  generalize q / (2 * l ^ M) = t at h
  have hl : ((l ^ M : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero K l, zero_pow (by omega)]
  refine ⟨?_, ?_⟩
  · rw [← h, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hl]
    simp
  · have : q.choose 2 = q * (l ^ M * t) := by
      rw [Nat.choose_two_right]
      have : q - 1 = 2 * (l ^ M * t) := by rw [← h, Nat.add_sub_cancel, mul_assoc]
      rw [this, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this, Nat.cast_mul, Nat.cast_mul, hl]
    simp

theorem tame_relation : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → 1 ≤ M → normV v % (2 * l ^ M) = 1 → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → (∀ c, ∃ σ ∈ Ine (F := F) A, d σ = c) → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∃ γ ∈ Ine (F := F) A, d γ = Multiplicative.ofAdd 1 ∧ ∀ (K : Type) [Field K] [CharP K l] (W : Type) [AddCommGroup W] [Module K W] (z0 : G F Ω → W), IsLocallyConstant z0 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z0 (g * h) = z0 g + z0 h) → (z0 γ = 0 → ∀ σ ∈ Ine (F := F) A, z0 σ = 0) ∧ ∀ (lam : G F Ω → K) (z1 : G F Ω → W), IsLocallyConstant lam → IsLocallyConstant z1 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, lam (g * h) = lam g + lam h) → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z1 (g * h) = z1 g + z1 h + lam g • z0 h) → lam γ • z0 φ = lam φ • z0 γ := by
  intro hT F Ω _ _ _ _ _ l _ M A v hA hl hM hq d hd hsurj φ hφ
  obtain ⟨-, -, hU, -, ⟨γ0, hγ0⟩, hrel⟩ := hT F Ω l A v hA hl
  have hID : Ine (F := F) A ≤ Dec (F := F) A := fun σ hσ => hσ.1
  have hJI := GlobalTheory.TameQuot.ineKer_le_Ine (F := F) A l
  have hJD := hJI.trans hID
  have hγD : γ0 ∈ Dec (F := F) A := hID hγ0.1
  have hφD : φ ∈ Dec (F := F) A := hφ.1
  have hdJ : ∀ j ∈ GlobalTheory.TameQuot.ineKer F A l, d j = 1 := fun j hj => by
    refine hom_trivial hU (d.comp (GlobalTheory.TameQuot.ineKer F A l).subtype) (hd.preimage continuous_subtype_val) M
      (fun x => ?_) ⟨j, hj⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, toAdd_one]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, d γ0 ^ k = Multiplicative.ofAdd 1 := by
    obtain ⟨σ, hσ, hσd⟩ := hsurj (Multiplicative.ofAdd 1)
    have ho : IsOpen (((Subgroup.zpowers (d γ0)).comap d : Subgroup (G F Ω)) : Set (G F Ω)) :=
      Subgroup.isOpen_mono (H₁ := d.ker) (fun x hx => by
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]; exact Subgroup.one_mem _) hd
    have hle : (Subgroup.zpowers γ0 ⊔ GlobalTheory.TameQuot.ineKer F A l).topologicalClosure ≤
        (Subgroup.zpowers (d γ0)).comap d := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ fun j hj => ?_) (Subgroup.isClosed_of_isOpen _ ho)
      · exact Subgroup.zpowers_le.2 (Subgroup.mem_zpowers _)
      · rw [Subgroup.mem_comap, hdJ j hj]; exact Subgroup.one_mem _
    obtain ⟨k, hk⟩ := hle (hγ0.2 hσ)
    exact ⟨k, hk.trans hσd⟩
  refine ⟨γ0 ^ k, Subgroup.zpow_mem _ hγ0.1 k, by rw [map_zpow, hk], ?_⟩
  intro K _ _ W _ _ z0 hz0 hadd0
  have hkK : (k : K) ≠ 0 := by
    intro h0
    have h1 : (k : ZMod (l ^ M)) * (d γ0).toAdd = 1 := by
      have := congrArg Multiplicative.toAdd hk
      rwa [toAdd_zpow, zsmul_eq_mul] at this
    have h2 := congrArg (ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) K) h1
    rw [map_mul, map_intCast, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  have hz0J := vanish_of_additive hU K z0 hz0 fun g hg h hh => hadd0 g (hJD hg) h (hJD hh)
  have e0 : z0 (γ0 ^ k) = (k : K) • z0 γ0 := by rw [additive_zpow z0 hadd0 hγD, Int.cast_smul_eq_zsmul]
  refine ⟨fun h σ hσ => ?_, fun lam z1 hlam hz1 haddl hadd1 => ?_⟩
  · rw [e0] at h
    exact vanish_closure hJD z0 hz0 hadd0 hγD ((smul_eq_zero.1 h).resolve_left hkK) hz0J σ (hγ0.2 hσ)
  · have hlJ := vanish_of_additive hU K lam hlam fun g hg h hh => haddl g (hJD hg) h (hJD hh)
    have hz1J := vanish_of_additive hU K z1 hz1 fun g hg h hh => by
      rw [hadd1 g (hJD hg) h (hJD hh), hz0J h hh, smul_zero, add_zero]
    have el : lam (γ0 ^ k) = (k : K) * lam γ0 := by rw [additive_zpow lam haddl hγD, zsmul_eq_mul]
    obtain ⟨hq1, hq2⟩ := cast_of_mod (K := K) hM hq
    have hj : (γ0 ^ normV v)⁻¹ * (φ * γ0 * φ⁻¹) ∈ GlobalTheory.TameQuot.ineKer F A l :=
      (hrel ⟨φ, hφD⟩ ⟨γ0, hγD⟩ hφ hγ0).2.1
    generalize hjj : (γ0 ^ normV v)⁻¹ * (φ * γ0 * φ⁻¹) = j at hj
    have hmul : φ * γ0 = γ0 ^ normV v * j * φ := by rw [← hjj]; group
    have hp : γ0 ^ normV v ∈ Dec (F := F) A := Subgroup.pow_mem _ hγD _
    have a1 := hadd1 φ hφD γ0 hγD
    have a2 : z1 (γ0 ^ normV v) = z1 γ0 := by
      rw [second_pow z0 z1 lam haddl hadd1 (hz0J 1 (Subgroup.one_mem _)) hγD, hq1, hq2, one_smul, zero_smul, add_zero]
    have a3 : lam (γ0 ^ normV v) = lam γ0 := by
      have := additive_zpow lam haddl hγD (normV v)
      rwa [zpow_natCast, zsmul_eq_mul, Int.cast_natCast, hq1, one_mul] at this
    rw [hmul, hadd1 _ (Subgroup.mul_mem _ hp (hJD hj)) φ hφD, hadd1 _ hp j (hJD hj), haddl _ hp j (hJD hj), a2, a3,
      hz0J j hj, hz1J j hj, hlJ j hj, smul_zero, add_zero, add_zero, add_zero, add_comm (z1 φ), add_right_inj] at a1
    rw [el, e0, mul_smul, a1, smul_comm]

end GlobalTheory.TameRel
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.GWComplex

section Count

variable {R : Type*} [CommRing R] {A B C D E : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E]

theorem card_eq_ker_mul_range (f : A →ₗ[R] B) :
    Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv]

theorem card_five {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D} {k : D →ₗ[R] E}
    (hf : Function.Injective f) (h1 : Function.Exact f g) (h2 : Function.Exact g h)
    (h3 : Function.Exact h k) :
    Nat.card (LinearMap.ker k) * Nat.card B = Nat.card C * Nat.card A := by
  rw [card_eq_ker_mul_range g, card_eq_ker_mul_range h, h1.linearMap_ker_eq,
    h2.linearMap_ker_eq, h3.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv]
  ring

theorem card_comap {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) (L : Submodule R B) :
    Nat.card (L.comap f) =
      Nat.card (LinearMap.ker f) * Nat.card (LinearMap.ker (g.domRestrict L)) := by
  let u : L.comap f →ₗ[R] L := f.restrict (fun _ hx => hx)
  rw [card_eq_ker_mul_range u]
  have e1 : LinearMap.range u = LinearMap.ker (g.domRestrict L) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, h x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨y, by rw [Submodule.mem_comap, hy]; exact x.2⟩, Subtype.ext hy⟩
  have e2 : Nat.card (LinearMap.ker u) = Nat.card (LinearMap.ker f) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [Submodule.mem_comap, LinearMap.mem_ker.1 x.2]; exact L.zero_mem⟩, Subtype.ext x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e1, e2]

theorem card_pi {I : Type*} [Fintype I] {P : I → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] (L : ∀ i, Submodule R (P i)) :
    Nat.card (Submodule.pi Set.univ L) = ∏ i, Nat.card (L i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, x.2 i trivial⟩
      invFun := fun x => ⟨fun i => (x i).1, fun i _ => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Count

theorem arith {k p h2 h0 s i h1 s' q h0' m : ℕ} (a1 : k * p = h2 * h0) (a2 : s = k * i)
    (a3 : i * h1 = s' * q) (a4 : h0' * h2 * m = h1) : s * h0' * p * m = s' * h0 * q := by
  calc s * h0' * p * m = (k * p) * i * h0' * m := by rw [a2]; ring
    _ = i * (h0' * h2 * m) * h0 := by rw [a1]; ring
    _ = s' * h0 * q := by rw [a4, a3]; ring


open PoitouTate in
theorem ker_flip_eq {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Av : S → ValuationSubring Ω}
    {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
    {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
    (hj : ∀ v, Function.Injective (j v))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}
    (hρ : ContAction ρ) (L : LocCond ρ (locFam S Av)) :
    LinearMap.ker ((tr1 S Av μ j ρ hρ).domRestrict (Submodule.pi Set.univ L)).flip =
      Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)
        (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) := by
  classical
  ext y
  rw [mem_Sel, LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [mem_perpCond, LinearMap.flip_apply, LinearMap.domRestrict_apply, poitouTateNineTerm_transgressionOne_apply,
    LinearMap.zero_apply]
  constructor
  · intro h v x hx
    have hm : Pi.single v x ∈ Submodule.pi Set.univ L := fun w _ => by
      by_cases hw : w = v
      · subst hw; rw [Pi.single_eq_same]; exact hx
      · rw [Pi.single_eq_of_ne hw]; exact zero_mem _
    have e := h ⟨_, hm⟩
    rw [Finset.sum_eq_single v (fun w _ hw => by
      rw [Subtype.coe_mk, Pi.single_eq_of_ne hw, map_zero, map_zero]) (by simp),
      Subtype.coe_mk, Pi.single_eq_same] at e
    exact hj v (e.trans (map_zero _).symm)
  · intro h x
    exact Finset.sum_eq_zero fun v _ => by rw [h v _ (x.2 v trivial), map_zero]


open PoitouTate in
theorem greenbergWiles_totallyComplex : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (S : Finset (HeightOneSpectrum (𝓞 F))) (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), 0 < r → ContainsAbove S l → ∀ (hrho : ContAction rhoS) (muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ), muS.comp (toGS Ω _) = cycMod F Ω l r → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond rhoS (locFam S Av), Finite (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) ∧ Finite (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) ∧ Nat.card (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) * Nat.card (H0 (twDual muS rhoS)) * (∏ v : S, Nat.card (H0 (rhoS.comp (locFam S Av v)))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) * Nat.card (H0 rhoS) * ∏ v : S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ r M _ _ _ _ _ S ρ hr hS hρ μ hμ Av hA L
  classical
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  obtain ⟨inv, hinv, h⟩ := hPT F Ω l r hr ζ hζ
  obtain ⟨⟨δ₁, -, h0, h1, h2, h3, h4, -⟩, -⟩ := h S hS Av hA μ hμ M ρ hρ
  have := GlobalTheory.DualSide.finite_TDual_pow (l := l) (r := r) (M := M)
  have hρ' := GlobalTheory.DualSide.contAction_twDual (contAction_charRep hμ) hρ
  obtain ⟨-, f1, -⟩ := hGF F Ω l r M S ρ hr hS hρ
  obtain ⟨-, f1', f2', -⟩ := hGF F Ω l r _ S (twDual μ ρ) hr hS hρ'
  have fl : ∀ v : S, Finite (H1 (ρ.comp (locFam S Av v))) := fun v =>
    (hLF F Ω l r M (Av v) _ v.1 hr (hA v) (hρ.comp' (continuous_locFam S Av v))).2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  have a1 := card_five h0 h1 h2 h3
  rw [GlobalTheory.ZModDual.card_dual_eq, Nat.card_pi] at a1
  have a2 := card_comap h4 (Submodule.pi Set.univ L)
  have e2 : (Submodule.pi Set.univ L).comap (loc1 S Av ρ) =
      Sel ρ (locFam S Av) (continuous_locFam S Av) L := by
    ext x
    rw [mem_Sel]
    exact ⟨fun h v => h v trivial, fun h v _ => h v⟩
  rw [e2] at a2
  have a3 := GlobalTheory.ZModDual.card_ker_mul_card_eq (l ^ r) _ _
    ((tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ).domRestrict (Submodule.pi Set.univ L))
  rw [ker_flip_eq (fun v => (invAt_bijective S Av μ hμ hinv v (hA v)).1), card_pi] at a3
  have a4 := hEC F Ω l r _ S (twDual μ ρ) hr hS hρ' (fun _ => 1)
    (fun w hw => absurd hw (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)))
  have hM : Nat.card (TDual (ZMod (l ^ r)) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq _ _
  rw [archH0Card, Finset.filter_false_of_mem (fun w _ =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)), Finset.prod_empty,
    one_mul, hM, IsTotallyComplex.finrank, two_mul, pow_add, ← mul_assoc] at a4
  have a5 := Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos _) a4
  exact arith a1 a2 a3 a5

end GlobalTheory.GWComplex
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

theorem _root_.GlobalTheory.T.exists_wachModule_periodMap_to_bcris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (E : WEt I) (Mo : NS E), (∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL)) → ∃ βdR bT, IsPer Mo (β.comp I.io.toRingHom) (P.ιB.toRingHom.comp AI.ιA) AI.π₁ βdR bT := by
  first | exact @GlobalTheory.HWL.Cmp.PerMap.main | exact GlobalTheory.HWL.Cmp.PerMap.main | (intros; apply GlobalTheory.HWL.Cmp.PerMap.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitVector_of_unitFor (E : EtTie W RA RW inclR φR gR πA)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span O {e₀} = ⊤ ∧
      W.one.L.T = Submodule.span O {(e₀ : W.one.V)} ∧
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      W.N W.one = Submodule.span (LetA O n) {e} ∧
      Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
      W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧
      ∀ a : LetA O n, a • e = 0 → a = 0 := by
  obtain ⟨-, e₀, h₀, -, -⟩ := E.one_e
  obtain ⟨e, hj, hbij, hφ, hγ, hN⟩ := hU e₀ h₀
  refine ⟨e, e₀, h₀, ?_, hj, hN, ?_, hφ, hγ, fun a ha => ?_⟩
  · have h1 := congrArg (Submodule.map W.one.L.T.subtype) h₀
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  · rw [eq_top_iff]
    rintro z -
    exact Submodule.mem_span_singleton.2 (hbij.2 z)
  · apply W.EE_inj
    apply hbij.1
    simp only
    rw [algebraMap_smul, algebraMap_smul, ha, zero_smul]

end Generic

open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem unitVector : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span ↥(OL LL) {e₀} = ⊤ ∧ W.one.L.T = Submodule.span ↥(OL LL) {(e₀ : W.one.V)} ∧ E.jD W.one e = (1 : RW LL) ⊗ₜ[↥(OL LL)] e₀ ∧ W.N W.one = Submodule.span (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) {e} ∧ Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧ W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a • e = 0 → a = 0 := by
  intro D HW F l _ K s LL h
  exact unitVector_of_unitFor _ (unitPart l (D.loc l) (D.locA l) (HW l) (F l) K s LL h)

end GlobalTheory.WachUnit
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



namespace GlobalTheory

theorem lenMod_mono_left : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S S' H : Submodule O M), S ≤ S' → BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  intro O M _ _ _ S S' H hS

  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right hS H
  let f := Submodule.mapQ (H.comap (S ⊔ H).subtype) (H.comap (S' ⊔ H).subtype)
    (Submodule.inclusion hle) (fun x hx => by simpa using hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using hx
  exact Module.length_le_of_injective f hf

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LitGood

theorem litGoodO : LitGoodO :=
  fun l _ LL => GlobalTheory.Pass.goodO_ringOfIntegers l LL

end GlobalTheory.LitGood
end
