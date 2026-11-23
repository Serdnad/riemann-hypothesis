module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle007
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCoh
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Mathlib.Algebra.Algebra.ZMod

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

theorem UpperTheory.exists_eqns_of_weighted_generators :
    ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O) (r s r' s' m : ℕ) {κ : Type} [Finite κ] (g : κ → A) (w : κ → ℤ),
          (∀ i, g i ∈ 𝒜 (w i)) → (∀ i, x (g i) = 0) → (∀ i, -2 ≤ w i ∧ w i ≤ 2) →
          Nat.card {i // w i = -1} = r + 1 → Nat.card {i // w i = -2} = s → Nat.card {i // w i = 1} = r' → Nat.card {i // w i = 2} = s' → Nat.card {i // w i = 0} = m →
          ∃ Q : Eqns 𝒜 x r s r' s' m, Q.ideal = Ideal.span (Set.range g) := by
  intro O A _ _ _ 𝒜 x r s r' s' m κ _ g w hg hx hw h1 h2 h3 h4 h5
  have key : ∀ (j : ℤ) (n : ℕ), Nat.card {i // w i = j} = n →
      ∃ F : Fin n → A, (∀ k, F k ∈ 𝒜 j ∧ x (F k) = 0) ∧ Set.range F = g '' {i | w i = j} := by
    intro j n hn
    let e := Finite.equivFinOfCardEq hn
    refine ⟨fun k => g (e.symm k).1, fun k => ⟨?_, hx _⟩, ?_⟩
    · have := hg (e.symm k).1
      rwa [(e.symm k).2] at this
    · ext a
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨(e.symm k).1, (e.symm k).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨e ⟨i, hi⟩, by simp⟩
  obtain ⟨F, hF, rF⟩ := key _ _ h1
  obtain ⟨G, hG, rG⟩ := key _ _ h2
  obtain ⟨E, hE, rE⟩ := key _ _ h3
  obtain ⟨E', hE', rE'⟩ := key _ _ h4
  obtain ⟨Z, hZ, rZ⟩ := key _ _ h5
  refine ⟨⟨F, G, E, E', Z, fun i => (hF i).1, fun i => (hG i).1, fun i => (hE i).1, fun i => (hE' i).1, hZ⟩, ?_⟩
  show Ideal.span (Set.range F ∪ Set.range G ∪ Set.range E ∪ Set.range E' ∪ Set.range Z) = _
  rw [rF, rG, rE, rE', rZ, ← Set.image_union, ← Set.image_union, ← Set.image_union, ← Set.image_union,
    ← Set.image_univ]
  congr 2
  ext i
  have := hw i
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  omega
end

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem free_ext {O σ Q : Type} [CommRing O] [Fintype σ] [AddCommGroup Q] [Module O Q]
    (D E : MvPowerSeries σ O →ₗ[O] Q)
    (hD : ∀ f g, D (f * g) = MvPowerSeries.constantCoeff f • D g + MvPowerSeries.constantCoeff g • D f)
    (hE : ∀ f g, E (f * g) = MvPowerSeries.constantCoeff f • E g + MvPowerSeries.constantCoeff g • E f)
    (hX : ∀ s, D (MvPowerSeries.X s) = E (MvPowerSeries.X s)) (f : MvPowerSeries σ O) : D f = E f := by
  let W' := WPres.free O (fun _ : σ => (0 : ℤ))
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  have h0 := (der_extend O _ ℤ W' h' Q).2 (D - E) (fun f g => by
    rw [ho, ho]
    simp only [LinearMap.sub_apply]
    rw [hD, hE, smul_sub, smul_sub]
    abel) (fun (s : σ) => by
    show D (MvPowerSeries.X s) - E (MvPowerSeries.X s) = 0
    rw [hX, sub_self])
  rw [sub_eq_zero.1 h0]

private theorem free_ex {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) :
    ∃ L : MvPowerSeries σ O →ₗ[O] O,
      (∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f) ∧
      (∀ s, L (MvPowerSeries.X s) = d s) ∧
      ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := by
  classical
  let L : MvPowerSeries σ O →ₗ[O] O :=
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries σ O →ₗ[O] O).smulRight (d s)
  have hL : ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := fun f => by
    simp [L]
  refine ⟨L, fun f g => ?_, fun s => ?_, hL⟩
  · rw [hL, hL, hL]
    simp only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  · rw [hL]
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

theorem UpperTheory.exists_base_pointDerivation_of_weight_homogeneous :
    ∀ {O B R S Q : Type} [CommRing O] [CommRing B] [Algebra O B] [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [AddCommGroup Q] [Module O Q]
          (WB : WPres O ℤ B) (hB : WB.HasOrigin) (W : WPres O ℤ R) (h : W.HasOrigin) {τ : Type} (e : WB.σ ⊕ τ ≃ W.σ), (∀ s, W.wt (e (.inl s)) = WB.wt s) →
          RingHom.ker W.π = (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) →
          ∀ (qh : R →ₐ[O] S) (x₀ : S →ₐ[O] O), x₀.comp qh = W.origin h → ∀ (p : O →ₗ[O] Q), Function.Surjective p → ∀ (j : ℤ),
          ∀ D ∈ PtDer x₀ Q, (∀ s, W.wt s ≠ j → D (qh (W.z s)) = 0) → ∀ D₁ ∈ PtDer (WB.origin hB) O, (∀ s, WB.wt s ≠ j → D₁ (WB.z s) = 0) →
          (∀ s, p (D₁ (WB.z s)) = D (qh (W.z (e (.inl s))))) →
          ∃ D' ∈ PtDer (W.originA h) O, HasWt W.gr j D' ∧ ∀ f : W.A, D (qh f) = p (D' f) := by
  intro O B R S Q _ _ _ _ _ _ _ _ _ WB hB W h τ e hwt hker qh x₀ hx p hp j D hD hDw D₁ hD₁ hD₁w hpD
  classical
  have hd : ∀ s : W.σ, ∃ d : O, (∀ t, s = e (.inl t) → d = D₁ (WB.z t)) ∧ (W.wt s ≠ j → d = 0) ∧
      p d = D (qh (W.z s)) := fun s => by
    obtain ⟨u, rfl⟩ := e.surjective s
    rcases u with t | t
    · refine ⟨D₁ (WB.z t), fun t' ht => ?_, fun hj => hD₁w t (by rwa [← hwt]), hpD t⟩
      rw [Sum.inl.inj (e.injective ht)]
    · by_cases hj : W.wt (e (.inr t)) = j
      · obtain ⟨a, ha⟩ := hp (D (qh (W.z (e (.inr t)))))
        exact ⟨a, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun h' => absurd hj h', ha⟩
      · exact ⟨0, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun _ => rfl,
          by rw [map_zero, hDw _ hj]⟩
  choose d hd1 hd2 hd3 using hd
  obtain ⟨L, hL, hLX, hLs⟩ := free_ex d
  have hren : ∀ g, L (MvPowerSeries.rename (fun s => e (.inl s)) g) = D₁ (WB.π g) :=
    free_ext (L ∘ₗ (MvPowerSeries.rename (fun s => e (.inl s)) : MvPowerSeries WB.σ O →ₐ[O] _).toLinearMap)
      (D₁ ∘ₗ WB.π.toLinearMap)
      (fun f g => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hL,
          MvPowerSeries.constantCoeff_rename])
      (fun f g => by
        have h1 : D₁ (WB.π f * WB.π g) = _ := hD₁ _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, h1, WB.origin_π])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPowerSeries.rename_X, hLX]
        exact hd1 _ s rfl)
  have hk : ∀ f, W.π f = 0 → L f = 0 := fun f hf => by
    have hf' : f ∈ RingHom.ker W.π := hf
    have key : ∀ f ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)), L f = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hg' : WB.π g = 0 := hg
        rw [hren, hg', map_zero]
      | zero => exact map_zero L
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x hx hx' =>
        have : x ∈ RingHom.ker W.π := by rw [hker]; exact hx
        rw [smul_eq_mul, hL, hx', h x this, smul_zero, zero_smul, add_zero]
    exact key f (hker ▸ hf')
  have hs : Function.Surjective W.π.toLinearMap := W.surj
  let E : R →ₗ[O] O := ((LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)) ∘ₗ
    (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hE : ∀ f, E (W.π f) = L f := fun f => by
    have : (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)
      ((W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f)) = _
    rw [this]
    rfl
  have hEd : ∀ a b, E (a * b) = W.origin h a • E b + W.origin h b • E a := fun a b => by
    obtain ⟨f, rfl⟩ := W.surj a
    obtain ⟨g, rfl⟩ := W.surj b
    rw [← map_mul, hE, hE, hE, hL, W.origin_π, W.origin_π]
  have hxo : ∀ f, x₀ (qh (W.π f)) = MvPowerSeries.constantCoeff f := fun f => by
    rw [← AlgHom.comp_apply, hx, W.origin_π]
  have hred : ∀ f, D (qh (W.π f)) = p (L f) :=
    free_ext (D ∘ₗ (qh.comp W.π).toLinearMap) (p ∘ₗ L)
      (fun f g => by
        have h1 : D (qh (W.π f) * qh (W.π g)) = _ := hD _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_mul, h1, hxo])
      (fun f g => by simp only [LinearMap.comp_apply, hL, map_add (f := _), map_smul])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, hLX, hd3]
        rfl)
  refine ⟨E ∘ₗ W.A.val.toLinearMap, fun a b => hEd a b, fun i hi a ha => ?_, fun a => ?_⟩
  · obtain ⟨f, hf, hfa⟩ := ha
    have hfa' : W.π f = (a : R) := hfa
    show E (a : R) = 0
    rw [← hfa', hE, hLs]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : W.wt s = j
    · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
    · rw [hd2 s hs, smul_zero]
  · obtain ⟨f, hf⟩ := W.surj (a : R)
    show D (qh (a : R)) = p (E (a : R))
    rw [← hf, hE, hred]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section Transport

variable {R R' Γ Γ' M : Type} [CommRing R] [CommRing R'] [Group Γ] [TopologicalSpace Γ] [Group Γ']
  [TopologicalSpace Γ'] [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R' Γ' M) (e : Γ' ≃* Γ) (he : Continuous e)
  (he' : Continuous e.symm) (h : ∀ g m, ρ' g m = ρ (e g) m)

include h in
private theorem invariants_equiv : Nonempty (H0 ρ ≃ H0 ρ') := by
  refine ⟨Equiv.subtypeEquivRight fun m => ?_⟩
  rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
  constructor
  · intro H g
    rw [h]
    exact H _
  · intro H g
    have := H (e.symm g)
    rwa [h, e.apply_symm_apply] at this

include he he' h in
private theorem first_cohomology_equiv : Nonempty (H1 ρ ≃ H1 ρ') := by
  have key : ∀ f : Γ → M, f ∈ Z1 ρ ↔ (fun g => f (e g)) ∈ Z1 ρ' := by
    intro f
    show (Continuous f ∧ _) ↔ (Continuous _ ∧ _)
    constructor
    · rintro ⟨hc, hf⟩
      refine ⟨hc.comp he, fun a b => ?_⟩
      simp only [map_mul, h]
      exact hf _ _
    · rintro ⟨hc, hf⟩
      refine ⟨?_, fun a b => ?_⟩
      · have := hc.comp he'
        convert this using 1
        funext g
        simp
      · have := hf (e.symm a) (e.symm b)
        simpa [map_mul, h] using this
  have keyB : ∀ f : Γ → M, f ∈ B1 ρ ↔ (fun g => f (e g)) ∈ B1 ρ' := by
    intro f
    rw [mem_coboundaries1, mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, fun g => by simp [hm, h]⟩
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      have := hm (e.symm g)
      simpa [h] using this
  let φ : Z1 ρ ≃ Z1 ρ' :=
    { toFun := fun f => ⟨fun g => f.1 (e g), (key f.1).1 f.2⟩
      invFun := fun f => ⟨fun g => f.1 (e.symm g), (key _).2 (by
        rw [show (fun g => f.1 (e.symm (e g))) = f.1 from funext fun g => by simp]
        exact f.2)⟩
      left_inv := fun f => Subtype.ext (funext fun g => by simp)
      right_inv := fun f => Subtype.ext (funext fun g => by simp) }
  refine ⟨Quotient.congr φ fun a b => ?_⟩
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
  exact keyB _

include he he' h in
private theorem second_cohomology_equiv : Nonempty (H2 ρ ≃ H2 ρ') := by
  have key : ∀ f : Γ × Γ → M, f ∈ Z2 ρ ↔ (fun p => f (e p.1, e p.2)) ∈ Z2 ρ' := by
    intro f
    show (Continuous f ∧ _) ↔ (Continuous _ ∧ _)
    constructor
    · rintro ⟨hc, hf⟩
      refine ⟨hc.comp (he.prodMap he), fun a b c => ?_⟩
      simp only [map_mul, h]
      exact hf _ _ _
    · rintro ⟨hc, hf⟩
      refine ⟨?_, fun a b c => ?_⟩
      · have := hc.comp (he'.prodMap he')
        convert this using 1
        funext p
        simp
      · have := hf (e.symm a) (e.symm b) (e.symm c)
        simpa [map_mul, h] using this
  have keyB : ∀ f : Γ × Γ → M, f ∈ B2 ρ ↔ (fun p => f (e p.1, e p.2)) ∈ B2 ρ' := by
    intro f
    rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun g => c (e g), hc.comp he, ?_⟩
      funext ⟨a, b⟩
      simp [d1_apply, h, map_mul]
    · rintro ⟨c, hc, hcf⟩
      refine ⟨fun g => c (e.symm g), hc.comp he', ?_⟩
      funext ⟨a, b⟩
      have := congrFun hcf (e.symm a, e.symm b)
      rw [d1_apply] at this
      rw [d1_apply]
      simpa [h, map_mul] using this
  let φ : Z2 ρ ≃ Z2 ρ' :=
    { toFun := fun f => ⟨fun p => f.1 (e p.1, e p.2), (key f.1).1 f.2⟩
      invFun := fun f => ⟨fun p => f.1 (e.symm p.1, e.symm p.2), (key _).2 (by
        rw [show (fun p : Γ' × Γ' => f.1 (e.symm (e p.1), e.symm (e p.2))) = f.1 from
          funext fun p => by simp]
        exact f.2)⟩
      left_inv := fun f => Subtype.ext (funext fun p => by simp)
      right_inv := fun f => Subtype.ext (funext fun p => by simp) }
  refine ⟨Quotient.congr φ fun a b => ?_⟩
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
  exact keyB _

end Transport

private def resC (R : Type) {k Γ M : Type} [CommRing R] [CommRing k] [Algebra R k] [Group Γ] [AddCommGroup M]
    [Module R M] [Module k M] [IsScalarTower R k M] (ρ : Representation k Γ M) : Representation R Γ M where
  toFun g := (ρ g).restrictScalars R
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem UpperTheory.local_euler_characteristic_of_prime_not_mem :
    LocalFiniteness → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
          ∀ ρ : Representation k (Dec (F := ℚ) A) M, ContAction ρ →
          Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ Module.finrank k (H1 ρ) = Module.finrank k (H0 ρ) + Module.finrank k (H2 ρ) := by
  intro hfin hec Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ A v hv hl ρ hc
  haveI : Finite M := Module.finite_of_finite k
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := ⟨fun a b m => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let ρ₀ := resC (ZMod (l ^ 1)) ρ
  have hc₀ : ContAction ρ₀ := hc
  obtain ⟨-, hF1, hF2, -⟩ := hfin ℚ Ω l 1 M A ρ₀ v one_pos hv hc₀
  have hE := (hec ℚ Ω l 1 M A ρ₀ v one_pos hv hc₀).2 hl
  have hr : ∀ g m, ρ g m = ρ₀ (MulEquiv.refl _ g) m := fun _ _ => rfl
  obtain ⟨e0⟩ := invariants_equiv ρ₀ ρ (MulEquiv.refl _) hr
  obtain ⟨e1⟩ := first_cohomology_equiv ρ₀ ρ (MulEquiv.refl _) continuous_id continuous_id hr
  obtain ⟨e2⟩ := second_cohomology_equiv ρ₀ ρ (MulEquiv.refl _) continuous_id continuous_id hr
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_⟩
  have hcard : Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) := by
    rw [← Nat.card_congr e1, ← Nat.card_congr e0, ← Nat.card_congr e2]
    exact hE
  have pw : ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V],
      Nat.card V = Nat.card k ^ Module.finrank k V := by
    intro V _ _ _
    haveI := Fintype.ofFinite V
    haveI := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  rw [pw (H1 ρ), pw (H0 ρ), pw (H2 ρ), ← pow_add] at hcard
  exact Nat.pow_right_injective Finite.one_lt_card hcard
end
