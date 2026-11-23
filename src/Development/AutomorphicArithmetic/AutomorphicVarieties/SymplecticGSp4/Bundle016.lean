module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ShaCoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForSymplecticGSp4Bundle016 (Ω : Type) [Field Ω] [Algebra ℚ Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.flagL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → ∃ κ : Fin 4 → D.Gp l →* (PadicAlgCl l)ˣ, Af.IsFlagOn r.toHomUnits (D.Gp l) κ ∧ (∀ i (s : D.Gp l), (s : G ℚ Ω) ∈ D.Ip l → (κ i s : PadicAlgCl l) = ((D.ps i s : c.O) : PadicAlgCl l)) ∧ ∀ i (g : D.Gp l), ‖(κ i g : PadicAlgCl l) - ((D.ps i g : c.O) : PadicAlgCl l)‖ < 1 := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
  obtain ⟨h, κ, hF, h1, h2, -⟩ := UpperTheory.V.Loc.spPtL D hD
    ((mapRep (y : R →+* PadicAlgCl l) ρ.hom).comp (D.Gp l).subtype)
    ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩
  refine ⟨κ, ⟨h⁻¹, fun s => ?_⟩, h1, h2⟩
  rw [inv_inv]
  exact hF s
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (I : Ideal O) (d : R →ₗ[O] O) (hd : d ∈ PtDer x O) (h0 : ∀ f, π f = 0 → d f ∈ I)
    (h1 : ∀ g i j, ∃ f, π f = r.hom g i j ∧ d f ∈ I) (f : R) : d f ∈ I := by
  haveI : IsCO O (TrivSqZeroExt O (O ⧸ I)) := co_sqz O O _ fun _ => rfl
  have hd' : I.mkQ ∘ₗ d ∈ PtDer x (O ⧸ I) := fun f g => by
    have := hd f g
    simp only [LinearMap.comp_apply, this, map_add (f := _), map_smul]
  obtain ⟨y, hy⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, hd', rfl⟩
  obtain ⟨y', hy'⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, (PtDer x (O ⧸ I)).zero_mem, rfl⟩
  have key : ∀ f, d f ∈ I ↔ y f = y' f := fun f => by
    rw [TrivSqZeroExt.ext_iff, (hy f).1, (hy f).2, (hy' f).1, (hy' f).2]
    simp only [true_and, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have k' : ∀ f, π f = 0 → y' f = 0 := fun f hf => TrivSqZeroExt.ext (by rw [(hy' f).1, hx f hf]; rfl) (by rw [(hy' f).2]; rfl)
  have k : ∀ f, π f = 0 → y f = 0 := fun f hf => ((key f).1 (h0 f hf)).trans (k' f hf)
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
  have he : ∀ f, e (π f) = Ideal.Quotient.mk _ f := fun f => by
    simp only [e]; rw [AlgEquiv.symm_apply_eq]; rfl
  let u : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y k).comp e.toAlgHom
  let u' : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y' k').comp e.toAlgHom
  have hu : ∀ f, u (π f) = y f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y k (e (π f)) = _
    rw [he]; rfl
  have hu' : ∀ f, u' (π f) = y' f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y' k' (e (π f)) = _
    rw [he]; rfl
  have huu : u = u' := hr _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun i j => by
    obtain ⟨f, hf, hf'⟩ := h1 g i j
    rw [Lift.map_hom, Lift.map_hom, ← hf, hu, hu', (key f).1 hf']))
  rw [key, ← hu, ← hu', huu]

private theorem wt_eq_neg (i j : Fin 4) : wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by revert i j; decide

private theorem origin_part {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {f : R} (hf : f ∈ W.part j) : W.origin h f = 0 := by
  obtain ⟨p, hp, rfl⟩ := hf
  have := hp 0 (by rw [map_zero]; exact hj.symm)
  rw [AlgHom.toLinearMap_apply, WPres.origin_π]
  simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using this

attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing of_isDiscreteValuationRing

set_option linter.overlappingInstances false in
private theorem len_le (hM : LemmaM') {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (P : ℤ × ℤ → Submodule O R) (hom : ∀ g i j, ∃ f ∈ P (wt i j), π f = r.hom g i j)
    (A : Subalgebra O R) (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (hA : ∀ n (f : A), f ∈ 𝒜 n ↔ f.1 ∈ P (0, n))
    (hA' : ∀ n f, f ∈ P (0, n) → f ∈ A) (hx1 : ∀ f ∈ P (0, -1), x f = 0)
    {ι : Type} (F : ι → A) (hF : ∀ i, F i ∈ 𝒜 (-1)) (hF0 : ∀ i, π (F i) = 0)
    (a : O) (ha : a ≠ 0) (N : Type) [AddCommGroup N] [Module O N] (Z : N →+ (Γ → O ⧸ Ideal.span {a}))
    (hZ : Function.Injective Z) (s t : Γ → Oˣ)
    (der : ∀ μ, ∃ δ ∈ PtDer x O, HasWt P (-wPs) δ ∧ (∀ f, π f = 0 → δ f ∈ Ideal.span {a}) ∧
      ∀ g f, (π f = r.hom g 2 0 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (s g : O) * Z μ g) ∧
        (π f = r.hom g 3 1 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (t g : O) * Z μ g)) :
    Module.length O N ≤ cotLen (x.comp A.val) 𝒜 (-1) F := by
  classical
  choose δ h1 h2 h3 h4 using der
  have hadd : ∀ μ ν f, Ideal.Quotient.mk (Ideal.span {a}) (δ (μ + ν) f) =
      Ideal.Quotient.mk _ (δ μ f) + Ideal.Quotient.mk _ (δ ν f) := fun μ ν f => by
    rw [← map_add (f := _), Ideal.Quotient.eq]
    refine der_zero π hπ r hr x hx (Ideal.span {a}) (δ (μ + ν) - (δ μ + δ ν))
      (sub_mem (h1 _) (add_mem (h1 _) (h1 _)))
      (fun f hf => sub_mem (h3 _ f hf) (add_mem (h3 _ f hf) (h3 _ f hf))) (fun g i j => ?_) f
    obtain ⟨f, hf, hf'⟩ := hom g i j
    refine ⟨f, hf', ?_⟩
    show δ (μ + ν) f - (δ μ f + δ ν f) ∈ _
    by_cases hw : wt i j = -wPs
    · rw [← Ideal.Quotient.eq, map_add (f := _)]
      rcases wt_eq_neg i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [(h4 _ g f).1 hf', (h4 _ g f).1 hf', (h4 _ g f).1 hf', map_add (f := _), Pi.add_apply, mul_add]
      · rw [(h4 _ g f).2 hf', (h4 _ g f).2 hf', (h4 _ g f).2 hf', map_add (f := _), Pi.add_apply, mul_add]
    · rw [h2 _ _ hw f hf, h2 _ _ hw f hf, h2 _ _ hw f hf]; simp
  let Dm : N →+ (A →ₗ[O] O ⧸ Ideal.span {a}) :=
    AddMonoidHom.mk' (fun μ => (Ideal.span {a}).mkQ ∘ₗ δ μ ∘ₗ A.val.toLinearMap) fun μ ν =>
      LinearMap.ext fun f => hadd μ ν f
  have hDm : ∀ μ (f : A), Dm μ f = Ideal.Quotient.mk _ (δ μ f) := fun _ _ => rfl
  refine hM O A ℤ 𝒜 (x.comp A.val) (-1) (fun f hf => hx1 _ ((hA _ f).1 hf)) ι F hF a ha N Dm ?_ (fun μ i => ?_)
    fun μ => ⟨δ μ ∘ₗ A.val.toLinearMap, fun f g => h1 μ f g, fun n hn f hf => ?_, fun f => rfl⟩
  · refine (injective_iff_map_eq_zero Dm).2 fun μ hμ => hZ ?_
    rw [map_zero]
    funext g
    obtain ⟨f, hf, hf'⟩ := hom g 2 0
    have e1 := hDm μ ⟨f, hA' (-1) f (by rwa [show wt 2 0 = (0, -1) by decide] at hf)⟩
    rw [hμ, LinearMap.zero_apply, (h4 μ g f).1 hf'] at e1
    exact ((s g).isUnit.map (Ideal.Quotient.mk (Ideal.span {a}))).mul_right_eq_zero.1 e1.symm
  · rw [hDm, Ideal.Quotient.eq_zero_iff_mem]
    exact h3 μ _ (hF0 i)
  · exact h2 μ (0, n) (fun h => hn (congrArg Prod.snd h)) _ ((hA n f).1 hf)

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.mPrime :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], LemmaM' → SoFin Ω l → D.sha ≤ cotLen M.x0 M.gr (-1) M.eqns.F := by
  intro Ω _ _ _ l _ c D hD M _ hM hS
  obtain ⟨-, a, ha, Z, hZ, hc⟩ := shaCoc D hD hS
  haveI : Finite (ResidueField c.O) := by
    obtain ⟨-, -, h, -⟩ := dvrFacts l c.O
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
    exact IsLocalRing.ResidueField.finite_of_finite ‹_›
  have hx : ∀ f, M.π f = 0 → M.W.origin M.org f = 0 := fun f hf => by
    obtain ⟨e, -, he⟩ := M.hom 1 0 0
    have h1 := M.at0 1 0 0 (f + e) (by rw [map_add (f := _), hf, he, zero_add])
    rw [map_add (f := _), M.at0 1 0 0 e he] at h1
    exact add_eq_right.1 h1
  set_option synthInstance.maxHeartbeats 200000 in
   exact len_le hM M.π M.surj M.ru M.gen (M.W.origin M.org) hx M.W.part M.hom M.A M.gr (fun _ _ => Iff.rfl)
    (fun n f hf => M.aPart_le hf) (fun f hf => origin_part M.W M.org (by decide) hf) M.eqns.F M.eqns.hF
    (fun i => by
      show M.F i ∈ RingHom.ker M.π
      rw [M.ker]
      exact Ideal.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
    a ha _ Z hZ D.th D.Psi fun μ => M.der a (Z μ) ha (hc μ)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cont_of_adic {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedRing K] (I : Ideal R)
    (y : R →+* K) (a : ℝ) (ha1 : a < 1) (ha0 : 0 ≤ a) (hy : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n)
    (f : Γ → R) (hf : AdicCont I f) : Continuous fun g => y (f g) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ha1
  filter_upwards [(hf n).eventually_eq g₀] with g hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hy n _ (Ideal.Quotient.eq.1 hg)) hn

theorem UpperTheory.V.GradeZeroInterpolatingElement.eptInt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → Continuous r ∧ (∀ g i j, ‖r g i j - D.r0E g i j‖ < 1) ∧ ∃ c' : Coef l, c.O ≤ c'.O ∧ (∀ g i j, r g i j ∈ c'.O) ∧ ∀ i, ∃ (s : Finset (G ℚ Ω)) (a : G ℚ Ω → PadicAlgCl l), (∀ g, a g ∈ c'.O) ∧ Matrix.single i i (1 : PadicAlgCl l) = ∑ g ∈ s, a g • r g := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, _, _, _, ρ, y, hρ, rfl⟩ := hr
  obtain ⟨⟨c', hc', hy'⟩, a, ha1, ha0, hy⟩ := (coPt c R).1 y
  refine ⟨?_, fun g i j => ?_, c', hc', fun g i j => hy' _, fun i => ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact cont_of_adic (maximalIdeal R) (y : R →+* PadicAlgCl l) a ha1 ha0 hy _ (ρ.cont i j)
  · have hm : ρ.hom g i j - algebraMap c.O R (D.r0 g i j) ∈ maximalIdeal R ^ 1 := by
      rw [pow_one, ← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, ρ.red, sub_eq_zero]
      rfl
    have h := hy 1 _ hm
    rw [map_sub, AlgHom.commutes, pow_one] at h
    exact lt_of_le_of_lt h ha1
  · have h := eii D hD R ρ hρ.mult hρ.nrm i
    obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h
    refine ⟨b.support, fun g => y (b g), fun g => hy' _, ?_⟩
    ext p q
    have h2 := congrArg y (congrFun (congrFun hb p) q)

    rw [Finsupp.sum, Matrix.sum_apply, map_sum] at h2
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul] at h2 ⊢
    have h3 : y (Matrix.single i i (1 : R) p q) = Matrix.single i i (1 : PadicAlgCl l) p q := by
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [← h3, ← h2]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H] (f : R →+* K)

private theorem ptIn_rep (r : H →* M4 R) (g : H) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem ptIn_smul (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp

private theorem ptIn_adj (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul]

private theorem ptIn_gsp {ν : R} {X : M4 R} (h : IsGSp ν X) : IsGSp (f ν) (f.mapMatrix X) := by
  unfold IsGSp at *
  rw [ptIn_adj, ← map_mul, h, ptIn_smul, map_one]

private theorem ptIn_prj (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  unfold prj
  have h : ∀ p : Polynomial R,
      Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ptIn_smul, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem ptIn_ord {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H} {r : H →* M4 R} (h : Ord I ps s₀ r) :
    Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ptIn_rep, RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · intro g i j hij
    simp only [ptIn_rep, ptIn_prj]
    rw [← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [ptIn_rep, ptIn_prj]
    have hsub : f.mapMatrix (r s - ps i s • 1) =
        f.mapMatrix (r s) - f (ps i s) • (1 : M4 K) := by
      rw [map_sub, ptIn_smul, map_one]
    rw [← hsub, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

private theorem ptIn_span (r : H →* M4 R) {X : M4 R} (h : X ∈ Submodule.span R (Set.range r)) :
    f.mapMatrix X ∈ Submodule.span K (Set.range (mapRep f r)) := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add (f := f.mapMatrix)]
    exact add_mem hx hy
  | smul a x _ hx => rw [ptIn_smul]; exact Submodule.smul_mem _ _ hx

end Gen

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptIn :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (K : Type) [CommRing K] [Algebra c.O K] (r : G ℚ Ω →* M4 K), D.PtIn K r → D.Mult r ∧ D.UnrT r 1 ∧ D.Nrm r ∧ D.eqL (r.comp (D.Gp l).subtype) ∧ (∀ p ∈ D.Sb, D.eqP p (r.comp (D.Gp p).subtype)) ∧ (∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) ∧ ∀ (K' : Type) [CommRing K'] [Algebra c.O K'] (f : K →ₐ[c.O] K'), D.PtIn K' (mapRep (f : K →+* K') r) := by
  intro Ω _ _ _ l _ c D hD K _ _ r hr
  obtain ⟨R, _, _, _, ρ, y, hpt, rfl⟩ := hr
  have he : D.IsEq ρ := (ptMap D hD R ρ).1 hpt
  have hy : ∀ a : c.O, (y : R →+* K) (algebraMap c.O R a) = algebraMap c.O K a := fun a => y.commutes a
  have hm : D.Mult (mapRep (y : R →+* K) ρ.hom) := fun g => by
    have h := ptIn_gsp (y : R →+* K) (he.mult g)
    rw [hy] at h
    exact h
  have hh : D.hEl (mapRep (y : R →+* K) ρ.hom) = (y : R →+* K).mapMatrix (D.hEl ρ.hom) := by
    unfold Raw.hEl
    rw [map_add (f := _), ptIn_smul, hy, ptIn_rep, ptIn_rep]
  refine ⟨hm, fun A hA g hg hg1 => ?_, ⟨fun i j hij => ?_, ?_, ?_⟩, ⟨fun g => hm g, ?_⟩, fun p hp => ⟨fun g => hm g, fun g hg => ?_⟩,
    fun i => ?_, fun K' _ _ f => ⟨R, inferInstance, inferInstance, inferInstance, ρ, f.comp y, hpt, rfl⟩⟩
  · rw [ptIn_rep, he.unr A hA g hg hg1, map_one]
  · rw [mapRep_apply, he.nrm.1 i j hij, map_zero]
  · rw [hh, RingHom.mapMatrix_apply, Matrix.map_apply, he.nrm.2.1, map_zero]
  · rw [hh, RingHom.mapMatrix_apply, Matrix.map_apply, he.nrm.2.2, map_zero]
  · have h := ptIn_ord (y : R →+* K) he.atL.2
    simp only [hy] at h
    exact h
  · have h : ρ.hom g = 1 := (he.atP p hp).2 g hg
    show (y : R →+* K).mapMatrix (ρ.hom g) = 1
    rw [h, map_one]
  · have h := ptIn_span (y : R →+* K) ρ.hom (eii D hD R ρ he.mult he.nrm i)
    rw [RingHom.mapMatrix_apply, Matrix.map_single, map_one] at h
    exact h
end
