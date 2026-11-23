module

import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle006
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open TensorProduct LinearMap IsLocalRing

namespace PositivityTheory.HtPt.Pfib

open GlobalTheory.LocalFlat

theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  apply GlobalTheory.FiniteFibreFlat.lTensor_map_injective <;> assumption

section Devissage

variable {A : Type} [CommRing A] {M : Type} [AddCommGroup M] [Module A M]

theorem exists_of_lTensor_eq {F G N : Type} [AddCommGroup F] [Module A F] [AddCommGroup G]
    [Module A G] [AddCommGroup N] [Module A N] (f : F →ₗ[A] N) (g : G →ₗ[A] N)
    (hs : Function.Surjective (f.coprod g)) (x : M ⊗[A] F) (y : M ⊗[A] G)
    (h : f.lTensor M x + g.lTensor M y = 0) :
    ∃ z : M ⊗[A] ker (f.coprod g),
      (fst A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = x ∧
      (snd A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = y := by
  have hex := lTensor_exact M (f.coprod g).exact_subtype_ker_map hs
  have h0 : (f.coprod g).lTensor M ((inl A F G).lTensor M x + (inr A F G).lTensor M y) = 0 := by
    rw [map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply, coprod_inl, coprod_inr, h]
  obtain ⟨z, hz⟩ := (hex _).mp h0
  refine ⟨z, ?_, ?_⟩
  · rw [lTensor_comp_apply, hz, map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply,
      fst_comp_inl, fst_comp_inr]
    simp
  · rw [lTensor_comp_apply, hz, map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply,
      snd_comp_inl, snd_comp_inr]
    simp

theorem lTensor_injective_of_le_range {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) {F : Type} [AddCommGroup F] [Module A F]
    (f : F →ₗ[A] A) (hf : Function.Injective f) (hle : I ≤ range f) :
    Function.Injective (f.lTensor M) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel F f x (by rw [hx]; simp)
  let e₀ : Submodule.comap f I →ₗ[A] I := f.restrict fun _ h => h
  have he : Function.Bijective e₀ := by
    refine ⟨fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨a, ha⟩ := hle i.2
    exact ⟨⟨a, by rw [Submodule.mem_comap, ha]; exact i.2⟩, Subtype.ext ha⟩
  let e := LinearEquiv.ofBijective e₀ he
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← lTensor_comp_apply, ← lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ hI] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem lTensor_injective_of_pow_le [IsNoetherianRing A] {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) (n : ℕ) (J : Ideal A) (hJ : I ^ n ≤ J) :
    Function.Injective (J.subtype.lTensor M) := by
  induction J using WellFoundedGT.induction with
  | ind J ih =>
  by_cases hex : ∃ a, a ∉ J ∧ ∀ i ∈ I, i * a ∈ J
  · obtain ⟨a, ha, hIa⟩ := hex
    let J' : Ideal A := J ⊔ Ideal.span {a}
    have haJ' : a ∈ J' := Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < J' := lt_of_le_of_ne le_sup_left fun h => ha (h ▸ haJ')
    have h' := ih J' hlt (hJ.trans hlt.le)
    let f : J →ₗ[A] J' := Submodule.inclusion hlt.le
    let g : A →ₗ[A] J' := toSpanSingleton A J' ⟨a, haJ'⟩
    have hs : Function.Surjective (f.coprod g) := by
      rintro ⟨b, hb⟩
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      exact ⟨(⟨j, hj⟩, c), rfl⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hfx : f.lTensor M x = 0 := by
      apply h'
      rw [← lTensor_comp_apply, map_zero]
      exact hx
    obtain ⟨z, hz1, hz2⟩ := exists_of_lTensor_eq f g hs x 0 (by rw [hfx, map_zero, add_zero])
    have hinj : Function.Injective
        ((snd A J A ∘ₗ (ker (f.coprod g)).subtype).lTensor M) := by
      refine lTensor_injective_of_le_range hrel hI _ ?_ fun i hi => ?_
      · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        rintro ⟨⟨j, c⟩, hjc⟩ hc
        have hc' : c = 0 := hc
        subst hc'
        have h1 : (j : A) + (0 : A) • a = 0 := congrArg Subtype.val hjc
        have h2 : j = 0 := Subtype.ext (by simpa using h1)
        subst h2
        rfl
      · refine ⟨⟨(⟨-(i * a), neg_mem (hIa i hi)⟩, i), ?_⟩, rfl⟩
        refine Subtype.ext ?_
        change -(i * a) + i • a = 0
        simp
    have hz : z = 0 := hinj (hz2.trans (map_zero _).symm)
    rw [← hz1, hz, map_zero]
  · push Not at hex
    have htop : ∀ m : ℕ, I ^ m ≤ J → (1 : A) ∈ J := by
      intro m
      induction m with
      | zero => intro h; exact h (by simp)
      | succ m ihm =>
        intro h
        refine ihm fun a ha => ?_
        by_contra haJ
        obtain ⟨i, hi, hia⟩ := hex a haJ
        exact hia (h (by rw [pow_succ']; exact Ideal.mul_mem_mul hi ha))
    refine lTensor_injective_of_le_range hrel hI _ J.injective_subtype ?_
    rw [Submodule.range_subtype, (Ideal.eq_top_iff_one J).mpr (htop n hJ)]
    exact le_top

theorem relationsLift_of_injective {J : Ideal A}
    (h : ∀ J' : Ideal A, J ≤ J' → Function.Injective (J'.subtype.lTensor M)) :
    RelationsLift J M := by
  intro F _ _ f x hx
  have hy : ∀ m ∈ J • (⊤ : Submodule A M),
      ∃ y : M ⊗[A] J, TensorProduct.rid A M (J.subtype.lTensor M y) = m := by
    intro m hm
    induction hm using Submodule.smul_induction_on' with
    | smul r hr m _ => exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    | add a _ b _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', by simp⟩
  obtain ⟨y, hy⟩ := hy _ hx
  have hy' := (TensorProduct.rid A M).injective hy
  let J' : Ideal A := range f ⊔ J
  let f' : F →ₗ[A] J' := f.codRestrict J' fun a => Submodule.mem_sup_left ⟨a, rfl⟩
  let g : J →ₗ[A] J' := Submodule.inclusion le_sup_right
  have hs : Function.Surjective (f'.coprod g) := by
    rintro ⟨b, hb⟩
    obtain ⟨_, ⟨a, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
    exact ⟨(a, ⟨c, hc⟩), rfl⟩
  have h0 : f'.lTensor M x + g.lTensor M (-y) = 0 := by
    apply h J' le_sup_right
    rw [map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply, map_zero, map_neg]
    change f.lTensor M x + -(J.subtype.lTensor M y) = 0
    rw [hy', add_neg_cancel]
  obtain ⟨z, hz, -⟩ := exists_of_lTensor_eq f' g hs x (-y) h0
  refine range_lTensor_le _ _ ?_ ⟨z, hz⟩
  rintro ⟨⟨a, j⟩, haj⟩
  have h1 : f a + (j : A) = 0 := congrArg Subtype.val haj
  change f a ∈ J
  rw [eq_neg_of_add_eq_zero_left h1]
  exact neg_mem j.2

theorem flat_of_relationsLift_of_injective [IsNoetherianRing A] (B : Type) [CommRing B]
    [Algebra A B] [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {I : Ideal A} (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (hrel : RelationsLift I M)
    (hinj : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  flat_of_relationsLift B hI fun n =>
    relationsLift_of_injective fun J hJ => lTensor_injective_of_pow_le hrel hinj n J hJ

end Devissage

theorem fibre_crit_ring : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB h
  refine flat_of_relationsLift_of_injective B (I := (maximalIdeal R).map (algebraMap R A)) ?_ ?_
    (lTensor_map_injective _)
  · exact ((Ideal.map_mono (map_maximalIdeal_le _)).trans (map_maximalIdeal_le _)).trans
      (maximalIdeal_le_jacobson _)
  · refine relationsLift_of_square
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] ResidueField R ⊗[R] A) :
        A →+* ResidueField R ⊗[R] A)
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) :
        B →+* ResidueField R ⊗[R] B) _
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (GlobalTheory.ker_includeRight_quotient A (maximalIdeal R)) ?_ ?_ h
    · rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      exact GlobalTheory.ker_includeRight_quotient B (maximalIdeal R)
    · ext a
      simp

end PositivityTheory.HtPt.Pfib
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem isLocalizedModule_subtype {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    IsLocalizedModule (nonZeroDivisors A) M.subtype := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩⟩
  · have hx : algebraMap A K (x : A) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro v w hvw
      have h' : (x : A) • v = (x : A) • w := by
        simpa [Module.algebraMap_end_apply] using hvw
      rw [← algebraMap_smul K (x : A) v, ← algebraMap_smul K (x : A) w] at h'
      exact smul_right_injective Ω hx h'
    · intro v
      refine ⟨(algebraMap A K (x : A))⁻¹ • v, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul K (x : A), smul_smul,
        mul_inv_cancel₀ hx, one_smul]
  · have hy : y ∈ Submodule.span K (M : Set Ω) := hM ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz => exact ⟨(⟨z, hz⟩, 1), by simp⟩
    | zero => exact ⟨(0, 1), by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨⟨m₁, s₁⟩, e₁⟩ := h₁
      obtain ⟨⟨m₂, s₂⟩, e₂⟩ := h₂
      refine ⟨((s₂ : A) • m₁ + (s₁ : A) • m₂, s₁ * s₂), ?_⟩
      have e₁' : (s₁ : A) • y₁ = (m₁ : Ω) := e₁
      have e₂' : (s₂ : A) • y₂ = (m₂ : Ω) := e₂
      simp only [map_add (f := _), map_smul, Submodule.subtype_apply, ← e₁', ← e₂', Submonoid.smul_def,
        Submonoid.coe_mul]
      rw [smul_add, mul_smul, mul_comm, mul_smul, smul_comm (s₂ : A) (s₁ : A) y₁,
        smul_comm (s₂ : A) (s₁ : A) y₂]
    | smul c z _ h =>
      obtain ⟨⟨m, s⟩, e⟩ := h
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
      dsimp only at hab
      have e' : (s : A) • z = (m : Ω) := e
      have hb : (b : A) • (c • z) = a • z := by
        rw [← algebraMap_smul K (b : A), smul_smul, mul_comm _ c, hab, algebraMap_smul]
      refine ⟨(a • m, b * s), ?_⟩
      rw [map_smul, Submodule.subtype_apply, ← e', Submonoid.smul_def, Submonoid.coe_mul,
        mul_comm, mul_smul, hb]
      exact smul_comm _ _ _

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    finrank K Ω = finrank A M := by
  haveI := isLocalizedModule_subtype M hM
  rw [IsFractionRing.finrank_right_eq A K Ω]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors A) M.subtype le_rfl

private theorem rankAtStalk_eq_finrank' {R : Type} [CommRing R] [IsDomain R] {P : Type} [AddCommGroup P]
    [Module R P] (q : PrimeSpectrum R) : Module.rankAtStalk P q = Module.finrank R P := by
  unfold Module.rankAtStalk
  rw [IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors]
  exact IsLocalizedModule.finrank_eq q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P) q.asIdeal.primeCompl_le_nonZeroDivisors

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsFullLattice K → Module.Projective A M → L.IsFullLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  apply PositivityTheory.HtPt.Gb.bc_iso <;> assumption

end PositivityTheory.HtPt.Gc
end

section

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {G : PDivGroup p O}

def lvl (G : PDivGroup p O) (n : ℕ) : G.Tate →+ Additive (WithConv (G.A n →ₐ[O] O)) where
  toFun x := Additive.ofMul (x.conv n)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lvl_smul (n : ℕ) (a : ℤ_[p]) (x : G.Tate) : lvl G n (a • x) = digit n a • lvl G n x := rfl

theorem tate_equiv {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (τ : La →+ G.Tate)
    (h1 : ∀ n a a', (τ a).conv n = (τ a').conv n ↔ ∃ b : La, a - a' = (p ^ n) • b)
    (h2 : ∀ n y, ∃ a, (τ a).conv n = y) :
    ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  classical
  let j : ℤ_[p] ⊗[ℤ] La →ₗ[ℤ_[p]] G.Tate := LinearMap.liftBaseChange ℤ_[p] τ.toIntLinearMap
  have hj : ∀ (c : ℤ_[p]) a, j (c ⊗ₜ a) = c • τ a := fun c a => rfl
  let b := Module.Free.chooseBasis ℤ La
  have key : ∀ (c : Module.Free.ChooseBasisIndex ℤ La → ℤ_[p]) n,
      (j (∑ i, c i ⊗ₜ b i)).conv n = (τ (∑ i, digit n (c i) • b i)).conv n := by
    intro c n
    change lvl G n _ = lvl G n _

    simp only [map_sum, hj, lvl_smul, map_nsmul]
  have hdiv : ∀ n (a a' : La), (∃ u : La, a - a' = (p ^ n) • u) ↔
      ∀ i, ((b.repr a i : ℤ) : ZMod (p ^ n)) = (b.repr a' i : ℤ) := by
    intro n a a'
    simp only [ZMod.intCast_eq_intCast_iff_dvd_sub]
    constructor
    · rintro ⟨u, hu⟩ i
      have := congrArg (fun x => b.repr x i) hu
      simp only [map_sub, map_nsmul, Finsupp.sub_apply, Finsupp.smul_apply, nsmul_eq_mul] at this
      rw [dvd_sub_comm]
      exact ⟨_, this⟩
    · intro H
      choose u hu using fun i => dvd_sub_comm.1 (H i)
      refine ⟨b.equivFun.symm u, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_nsmul, LinearEquiv.apply_symm_apply, map_sub]
      simpa using hu i
  have hrep : ∀ (k : Module.Free.ChooseBasisIndex ℤ La → ℕ) i, b.repr (∑ i, k i • b i) i = k i := by
    intro k i
    have : ∑ i, k i • b i = b.equivFun.symm fun i => (k i : ℤ) := by simp
    rw [this, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨LinearEquiv.ofBijective j ⟨?_, fun x => ?_⟩, fun a => (hj 1 a).trans (one_smul _ _)⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨c, rfl⟩ : ∃ c : Module.Free.ChooseBasisIndex ℤ La → ℤ_[p], z = ∑ i, c i ⊗ₜ b i := by
      refine ⟨(b.baseChange ℤ_[p]).repr z, ?_⟩
      conv_lhs => rw [← (b.baseChange ℤ_[p]).sum_repr z]
      simp [TensorProduct.smul_tmul']
    have hc : ∀ i, c i = 0 := fun i => PadicInt.ext_of_toZModPow.1 fun n => by
      have h3 := key c n
      rw [hz, ← map_zero τ] at h3
      have h4 := (hdiv n _ _).1 ((h1 n _ _).1 h3) i
      rw [hrep] at h4
      rw [map_zero, ← cast_digit]
      simpa using h4.symm
    simp [hc]
  · choose a ha using fun n => h2 n (x.conv n)
    have hc : ∀ n, (τ (a (n + 1))).conv n = (τ (a n)).conv n := fun n => by
      rw [← TateOver.compat_conv, ha, ha, TateOver.compat_conv]
    have hd : ∀ i n, (p : ℤ) ^ n ∣ b.repr (a (n + 1)) i - b.repr (a n) i := fun i n => by
      have := (hdiv n _ _).1 ((h1 n _ _).1 (hc n).symm) i
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      exact_mod_cast this
    refine ⟨∑ i, PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (fun n => b.repr (a n) i) p (hd i)) ⊗ₜ b i,
      TateOver.ext_conv fun n => ?_⟩
    rw [key, ← ha, h1, hdiv]
    intro i
    rw [hrep, Int.cast_natCast, cast_digit, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
      (fun n => b.repr (a n) i) p (hd i)]

end PositivityTheory.HtPt.Twpdiv
end
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem powadd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (x y z : C), v x ≤ 1 → v y ≤ 1 → v (z - x - y) ≤ v (p : C) → v (z ^ p - x ^ p - y ^ p) ≤ v (p : C) := by
  intro p hp C _ v x y z hx hy h
  have hp1 : v (p : C) ≤ 1 := by
    exact natCast_mem v.integer p
  have hz : v z ≤ 1 := by
    have e : z = (z - x - y) + x + y := by ring
    rw [e]
    exact v.map_add_le (v.map_add_le (h.trans hp1) hx) hy
  let X : v.integer := ⟨x, hx⟩
  let Y : v.integer := ⟨y, hy⟩
  let Z : v.integer := ⟨z, hz⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out X Y
  obtain ⟨s, hs⟩ := sub_dvd_pow_sub_pow Z (X + Y) p
  have hr' := congrArg v.integer.subtype hr
  have hs' := congrArg v.integer.subtype hs
  simp only [map_add (f := _), map_mul, map_pow, map_sub, map_natCast, Subring.subtype_apply, X, Y, Z]
    at hr' hs'
  have e : z ^ p - x ^ p - y ^ p = (z - x - y) * (s : C) + (p : C) * (x * y * (r : C)) := by
    linear_combination hr' + hs'
  rw [e]
  refine v.map_add_le ?_ ?_
  · rw [map_mul]
    exact (mul_le_of_le_one_right' (α := NNReal) s.2).trans h
  · rw [map_mul]
    refine mul_le_of_le_one_right' ?_
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' hx hy) r.2

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem mem_pInt [CharZero C] (hv : v.Integers R) {p : ℕ} (hp : p ≠ 0) (x : C) :
    x ∈ pInt (C := C) R p ↔ v x ≤ v (p : C) := by
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left' (hv.map_le_one r)
  · intro h
    have h1 : v (x / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ h0]⟩

theorem val_le_one (hv : v.Integers R) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (x : N) : v (g x) ≤ 1 := by
  obtain ⟨r, hr⟩ := AA.le_int hg x
  rw [← hr]
  exact hv.map_le_one r

theorem pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (k : ℕ) :
    g ^ k ∈ AA.carrier := by
  induction k with
  | zero => rw [pow_zero]; exact AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg

theorem pow_congr (p : ℕ) [hp : Fact p.Prime] {x z : C} (hx : v x ≤ 1)
    (h : v (z - x) ≤ v (p : C)) : v (z ^ p - x ^ p) ≤ v (p : C) := by
  have := powadd p C v x 0 z hx (by simp) (by simpa using h)
  simpa [zero_pow hp.out.ne_zero] using this

end

theorem a_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  intro p hp C _ _ _ v R _ _ hv hp1 F _ _ _ _ f hF N _ _ _ _ AA hst K t τ c hc
  obtain ⟨g, ⟨hg, hadd⟩, h1, h2, h3⟩ := hc
  have hp0 := hp.out.ne_zero
  have hb := val_le_one hv AA hg
  refine ⟨g ^ p, ⟨pow_mem AA hg p, fun x y => ?_⟩, fun a x => ?_, fun k hk => ?_, ?_⟩
  · rw [mem_pInt hv hp0]
    exact powadd p C v _ _ _ (hb x) (hb y) ((mem_pInt hv hp0 _).1 (hadd x y))
  · rw [mem_pInt hv hp0, MulChar.pow_apply' _ hp0, map_pow, Pi.pow_apply, Pi.pow_apply, ← mul_pow]
    refine pow_congr p ?_ ((mem_pInt hv hp0 _).1 (h1 a x))
    rw [map_mul]
    exact mul_le_one' (hv.map_le_one _) (hb x)
  · rw [mem_pInt hv hp0]
    have := pow_congr (v := v) p (x := 0) (z := g k) (by simp)
      (by simpa using (mem_pInt hv hp0 _).1 (h2 k hk))
    simpa [zero_pow hp0] using this
  · rw [mem_pInt hv hp0, map_pow, Pi.pow_apply]
    exact pow_congr p (hv.map_le_one _) ((mem_pInt hv hp0 _).1 h3)

end PositivityTheory.HtPt.Rd
end
