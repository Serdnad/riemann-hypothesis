module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle008
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem one_left'' {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  rw [Over.comp_left]
  congr 1

def anE (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) :
    (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left) :=
  fun z => (F.ex i P z).left

theorem anHol (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : IsHolFam (anE F i P) := by
  have hper : IsHolPeriods (F.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have h2 := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  intro U f
  obtain ⟨ho, hd⟩ := h2 U f
  have hι : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  have hc := hd.comp hι.differentiableOn (Set.mapsTo_preimage _ _)
  refine ⟨?_, ?_⟩
  · convert ho.preimage hι.continuous using 1
    ext z
    simp [anE]
  · convert hc using 1
    all_goals
      ext z
      simp [anE]

variable [Algebra c.F ℂ]

variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)


theorem basis_single (e' : Fin g ≃ Lt1 Dw) (v : Fin g → ℂ) :
    ∃! a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = v j := by
  have key : ∀ a : Lt1 Dw → ℂ, ∀ j, ∑ ℓ, a ℓ * (if j = e'.symm ℓ then (1 : ℂ) else 0) = a (e' j) := by
    intro a j
    rw [Fintype.sum_eq_single (e' j)]
    · simp
    · intro ℓ hℓ
      have hne : j ≠ e'.symm ℓ := by
        intro h
        apply hℓ
        rw [h, Equiv.apply_symm_apply]
      simp [hne]
  refine ⟨fun ℓ => v (e'.symm ℓ), fun j => ?_, fun a ha => ?_⟩
  · rw [key]
    simp
  · funext ℓ
    have h1 := ha (e'.symm ℓ)
    rw [key, Equiv.apply_symm_apply] at h1
    exact h1

def anAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Fin g → MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun k => MvPowerSeries.C (ty k (a : E)) * MvPowerSeries.X ((0 : Fin 1), k)

theorem jetSubstP_anAct (m : ℕ) (a : 𝓞 E) (b : Jet ℂ (Fin 1 × Fin g) m) :
    jetSubstP m (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) b =
      jetScaleP m (fun k => ty k (a : E)) b := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  unfold jetSubstP jetScaleP
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk]
  have key : ∀ p : Fin 1 × Fin g,
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (psTrunc m (anAct ty a p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2)))) =
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (MvPolynomial.C (ty p.2 (a : E)) * MvPolynomial.X p) := by
    rintro ⟨i, k⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    set q : Fin 1 × Fin g := ((0 : Fin 1), k) with hq
    have hps : psTrunc m (anAct ty a k) =
        if Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) then
          MvPolynomial.C (ty k (a : E)) * MvPolynomial.X q else 0 := by
      unfold psTrunc anAct
      by_cases hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ))
      · rw [if_pos hmem, Finset.sum_eq_single (Finsupp.single q 1)]
        · simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, MvPolynomial.C_mul_X_eq_monomial, hq]
        · intro e _ he
          simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, he]
        · intro h
          exact absurd hmem h
      · rw [if_neg hmem]
        apply Finset.sum_eq_zero
        intro e he
        have hne : e ≠ Finsupp.single q 1 := fun h => hmem (h ▸ he)
        simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, hne]
    rw [hps]
    by_cases hm0 : m = 0
    · subst hm0
      have hnot : Finsupp.single q 1 ∉ (degLE 0 : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        intro hmem
        rw [degLE, Finset.mem_filter] at hmem
        have := hmem.2
        rw [Finsupp.sum_single_index rfl] at this
        omega
      rw [if_neg hnot]
      simp only [map_zero, sub_zero]
      symm
      rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
    · have hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        rw [degLE, Finset.mem_filter, Finsupp.sum_single_index rfl]
        refine ⟨Finset.mem_image.2 ⟨fun j => if j = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, by omega⟩
        ext j
        by_cases hj : j = q
        · subst hj
          simp
        · simp [hj, Finsupp.single_apply, Ne.symm hj]
      rw [if_pos hmem]
      simp [MvPolynomial.constantCoeff_X, hq]
  show (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f) = (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
  congr 2
  funext p
  exact key p

theorem fst_jetTan (ℓ : Fin 1 × Fin g) (a : Jet ℂ (Fin 1 × Fin g) (0 + 1)) :
    ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) a).fst =
      (jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [jetTan, jetAug, liftJet]
  try simp only [Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
  try simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  induction p using MvPolynomial.induction_on with
  | C r => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = ℓ <;> simp [hj, hp]

theorem epsMul_algebraMap (cc : ℂ) (a : ℂ) : epsMul cc (algebraMap ℂ (DualNumber ℂ) a) = algebraMap ℂ _ a := by
  ext <;> simp [epsMul]

def epsHom (x : Sp ℂ ⟶ Xo.X) (cc : ℂ) : tEps x ⟶ tEps x :=
  Over.homMk (spMap (epsMul cc)) (by
    show spMap (epsMul cc) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun a => epsMul_algebraMap cc a)

theorem spMap_epsMul_zero_jetTan (ℓ : Fin 1 × Fin g) :
    spMap (epsMul (0 : ℂ)) ≫ spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
  have h : (epsMul (0 : ℂ)).comp ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) = (algebraMap ℂ (DualNumber ℂ)).comp
      ((jetAug : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* ℂ) := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · simp [epsMul, fst_jetTan, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem epsMul_one : epsMul (1 : ℂ) = RingHom.id (DualNumber ℂ) := by
  ext x <;> simp [epsMul]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem valAt'_comp_lemma {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Y') (U : Y'.Opens)
    (f : Γ(Y', U)) : valAt' x (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_pos h', dif_pos h]
    unfold valAt
    first
      | (rw [Scheme.comp_appLE]) <;> rfl
      | (rw [Scheme.Hom.comp_appLE]) <;> rfl
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dite_eq_right h', dite_eq_right h]

theorem valAt'_specMap {A C : CommRingCat.{0}} (φ : A ⟶ C) (x : Sp ℂ ⟶ Spec C) (a : A) :
    valAt' (x ≫ Spec.map φ) ⊤ ((Scheme.ΓSpecIso A).inv a) = valAt' x ⊤ ((Scheme.ΓSpecIso C).inv (φ a)) := by
  have key : (Spec.map φ).app ⊤ ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso C).inv (φ a) := by
    first
      | exact (congrArg (fun g : A ⟶ Γ(Spec C, ⊤) => g a) (Scheme.ΓSpecIso_inv_naturality φ)).symm
  (rw [← valAt'_comp_lemma, key]) <;> rfl

theorem valAt'_zero' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) : valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs with h
  · simp [valAt]
  · rfl

private theorem valAt'_top_mul_lemma_2 {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (f g : Γ(Y, ⊤)) :
    valAt' x ⊤ (f * g) = valAt' x ⊤ f * valAt' x ⊤ g := by
  have h : ⊤ ≤ x ⁻¹ᵁ (⊤ : Y.Opens) := by
    first
      | exact le_top
  first
    | simp only [valAt', dif_pos h, valAt, map_mul]

private theorem valAt'_top_add_lemma_3 {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (f g : Γ(Y, ⊤)) :
    valAt' x ⊤ (f + g) = valAt' x ⊤ f + valAt' x ⊤ g := by
  have h : ⊤ ≤ x ⁻¹ᵁ (⊤ : Y.Opens) := by
    first
      | exact le_top
  first
    | simp only [valAt', dif_pos h, valAt, map_add (f := _)]

theorem isHolTo_pullbackSpec {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {B : Set V} (hB : IsOpen B)
    (w : V → (Sp ℂ ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T)))))
    (h1 : ∀ a : S, DifferentiableOn ℂ
      (fun b => valAt' (w b ≫ pullback.fst _ _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a)) B)
    (h2 : ∀ c : T, DifferentiableOn ℂ
      (fun b => valAt' (w b ≫ pullback.snd _ _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of T)).inv c)) B) :
    IsHolTo B w := by
  haveI : IsAffine (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T)))) := by
    first
      | infer_instance
  refine isHolTo_of_affine hB ?_
  intro r

  have hL : ∀ (s : S) (b : V), valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv (s ⊗ₜ[R] (1 : T))) =
      valAt' (w b ≫ pullback.fst _ _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) := by
    intro s b
    first
      | rw [← pullbackSpecIso_hom_fst R S T]
    (rw [← Category.assoc, valAt'_specMap]) <;> rfl
  have hR : ∀ (t : T) (b : V), valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv ((1 : S) ⊗ₜ[R] t)) =
      valAt' (w b ≫ pullback.snd _ _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of T)).inv t) := by
    intro t b
    first
      | rw [← pullbackSpecIso_hom_snd R S T]
    (rw [← Category.assoc, valAt'_specMap]) <;> rfl
  have hS : ∀ s : S, DifferentiableOn ℂ (fun b => valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv (s ⊗ₜ[R] (1 : T)))) B :=
    fun s => (h1 s).congr (fun b _ => hL s b)
  have hT : ∀ t : T, DifferentiableOn ℂ (fun b => valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv ((1 : S) ⊗ₜ[R] t))) B :=
    fun t => (h2 t).congr (fun b _ => hR t b)

  have hAll : ∀ u : S ⊗[R] T, DifferentiableOn ℂ (fun b => valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv u)) B := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, valAt'_zero']
      exact differentiableOn_const 0
    | tmul s t =>
      have hst : (s ⊗ₜ[R] t : S ⊗[R] T) = (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      simp only [hst, map_mul, valAt'_top_mul_lemma_2]
      exact (hS s).mul (hT t)
    | add x y hx hy =>
      simp only [map_add (f := _), valAt'_top_add_lemma_3]
      exact hx.add hy

  have hr : ∀ b, valAt' (w b) ⊤ r = valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).hom ((pullbackSpecIso R S T).inv.app ⊤ r))) := by
    intro b
    have hinv : (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).hom ((pullbackSpecIso R S T).inv.app ⊤ r)) =
        (pullbackSpecIso R S T).inv.app ⊤ r := by
      first
        | exact Iso.hom_inv_id_apply _ _
    rw [hinv]
    have hw : w b = (w b ≫ (pullbackSpecIso R S T).hom) ≫ (pullbackSpecIso R S T).inv := by simp
    conv_lhs => rw [hw]
    exact (valAt'_comp_lemma (w b ≫ (pullbackSpecIso R S T).hom) (pullbackSpecIso R S T).inv ⊤ r).symm
  exact (hAll _).congr (fun b _ => hr b)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

private lemma coh_lemma {X Y : Scheme} (L : LB X) (φ : Fin 1 ⊕ Fin 1 → (Y ⟶ X))
    (j : Fin 1 → L.ι) : LB.Coh L φ (Sum.elim j j) := by
  intro k₁ k₂ _
  rcases k₁ with a | a <;> rcases k₂ with b | b <;> exact congrArg j (Subsingleton.elim a b)

private lemma res_inj_lemma_2 {X : Scheme} {W V : X.Opens} (h : W ≤ V) {a b : Γ(X, V)}
    {c : Γ(X, W)} (hc : c = 1)
    (hab : c * (X.presheaf.map (homOfLE h).op).hom a = c * (X.presheaf.map (homOfLE h).op).hom b)
    (h' : V ≤ W) : a = b := by
  subst hc
  rw [_root_.one_mul, _root_.one_mul] at hab
  have hWV : W = V := le_antisymm h h'
  subst hWV
  have e : homOfLE h = 𝟙 W := Subsingleton.elim _ _
  rw [e] at hab
  simpa using hab

theorem expansion_nonneg_regular : RegularSectionNonneg := by
  unfold RegularSectionNonneg
  intro V _ _ _ ϖ hϖ D Q hQ vK hvK A G _ _ _ _ _ U k hk σ s hs E hE
  subst hk
  obtain ⟨F, g', hF, -, hFg⟩ := TG.integral_exp (U := U) rfl σ

  have hsK : s = TG.secK U.toUnifPre σ := by
    apply SecOps.sec_ext
    intro j
    have h1 := hs j j (coh_lemma _ _ j)
    have h2 := TG.secK_rel U.toUnifPre σ j j (coh_lemma _ _ j)
    have h3 := h1.symm.trans h2
    refine res_inj_lemma_2 _ (by exact _root_.map_one _) h3 ?_
    refine le_inf le_rfl ?_
    first
      | exact le_rfl
      | (simp only [Category.comp_id]; exact le_rfl)
      | exact fun x hx => hx
      | (intro x hx; simpa [LB.wchart] using hx)
  subst hsK

  have hEF : E = F := ((U.expand 1 le_rfl).1 _).unique hE hF
  rw [hEF]
  refine (n1a V ϖ hϖ D Q hQ (FractionRing V) vK hvK 1 le_rfl {0}
    (fun χ => ⟨0, Finset.mem_singleton_self 0, χ, by simp⟩) F 0).2 ?_
  intro α hα
  rw [Finset.mem_singleton] at hα
  subst hα
  rw [Q_zero hϖ (hQ := hQ)]
  unfold VGe
  refine ⟨1, fun _ => 1, fun _ => g' 0, fun _ => F.s 0, fun _ => hFg 0, fun _ => ?_, fun j => ?_⟩
  · first
      | simp
      | (rw [AddValuation.map_one]; simp)
  · first
      | simp [DegPre.constBF]
      | (simp only [DegPre.constBF, Fin.sum_univ_one, _root_.map_one, _root_.one_mul])

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
