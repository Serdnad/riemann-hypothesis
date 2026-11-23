module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.GroupTheory.Index
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle043
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle038
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle040
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def halfInf (F : Type) [Field F] [NumberField F] : (AF F)ˣ where
  val := (algebraMap F (Ainf F) 2⁻¹, 1)
  inv := (algebraMap F (Ainf F) 2, 1)
  val_inv := Prod.ext (by
    change algebraMap F (Ainf F) 2⁻¹ * algebraMap F (Ainf F) 2 = 1
    rw [← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]) (mul_one _)
  inv_val := Prod.ext (by
    change algebraMap F (Ainf F) 2 * algebraMap F (Ainf F) 2⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]) (mul_one _)

def halfE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : (AF F ⊗[F] E)ˣ :=
  Units.map (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom (halfInf F)

open scoped TensorProduct in
open NumberField in
theorem _root_.GlobalTheory.Eis.Conv.sigR_halfE {F E : Type} [Field F] [NumberField F] [Field E]
    [Algebra F E] (σ : E →ₐ[F] E) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ (_root_.GlobalTheory.Eis.Conv.halfE F E).1 =
      (_root_.GlobalTheory.Eis.Conv.halfE F E).1 := by
  simp [_root_.GlobalTheory.Eis.Conv.halfE, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]

end GlobalTheory.Eis.Conv

end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fraction_field_extension : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  intro Ω R L M _ _ _ _ _ _ G S c e sl ga A he hce hsl hA
  letI alg : Algebra Ω (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra
  have hΩ : ∀ x, algebraMap Ω (FractionRing R) x = algebraMap R (FractionRing R) (c x) := fun _ => rfl
  let e0 : FractionRing R →+* L := IsFractionRing.lift he
  have he0 : ∀ a, e0 (algebraMap R (FractionRing R) a) = e a := fun a => IsFractionRing.lift_algebraMap he a
  have hcom : ∀ x, e0 (algebraMap Ω (FractionRing R) x) = algebraMap Ω L x := fun x => by
    rw [hΩ, he0, hce]
  let e' : FractionRing R →ₐ[Ω] L :=
    { e0 with commutes' := hcom }
  let s0 : G → FractionRing R ≃+* FractionRing R := fun g => IsFractionRing.ringEquivOfRingEquiv (sl g)
  have hs0 : ∀ g a, s0 g (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (sl g a) :=
    fun g a => IsFractionRing.ringEquivOfRingEquiv_algebraMap (sl g) a
  let sl' : G → FractionRing R ≃ₐ[Ω] FractionRing R := fun g =>
    AlgEquiv.ofRingEquiv (f := s0 g) (fun x => by rw [hΩ, hs0, hsl])
  let ga' : S → FractionRing R ≃+* FractionRing R := fun s => IsFractionRing.ringEquivOfRingEquiv (ga s)
  have hunit : ∀ y : nonZeroDivisors R, IsUnit (A y) := fun y =>
    hA y (nonZeroDivisors.ne_zero y.2)
  let A' : FractionRing R →+* M := IsLocalization.lift (M := nonZeroDivisors R) hunit
  refine ⟨FractionRing R, inferInstance, alg, algebraMap R (FractionRing R), e', sl', ga', A',
    IsFractionRing.injective R (FractionRing R), ?_, fun x => (hΩ x).symm, he0, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective R f
    refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
    have hy' : algebraMap R (FractionRing R) y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    rw [← hxy, div_mul_cancel₀ _ hy']
  · intro g a
    exact hs0 g a
  · intro s a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (ga s) a
  · intro a
    exact IsLocalization.lift_eq hunit a

end GlobalTheory
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ArtinFix

variable {K G : Type} [Field K] [Group G] (ρ : G →* RingAut K)

lemma rho_mul_apply (a b : G) (x : K) : ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul]; rfl

lemma rho_inv_apply_apply (g : G) (x : K) : ρ g⁻¹ (ρ g x) = x := by
  rw [← rho_mul_apply, inv_mul_cancel, map_one]; rfl

lemma rho_apply_inv_apply (g : G) (x : K) : ρ g (ρ g⁻¹ x) = x := by
  rw [← rho_mul_apply, mul_inv_cancel, map_one]; rfl

variable (Δ : Subgroup G)

def fixSub : Subfield K where
  carrier := {x | ∀ δ ∈ Δ, ρ δ x = x}
  mul_mem' := by
    intro a b ha hb δ hδ
    simp [map_mul, ha δ hδ, hb δ hδ]
  one_mem' := by intro δ _; simp
  add_mem' := by
    intro a b ha hb δ hδ
    simp [map_add (f := _), ha δ hδ, hb δ hδ]
  zero_mem' := by intro δ _; simp
  neg_mem' := by
    intro a ha δ hδ
    simp [map_neg, ha δ hδ]
  inv_mem' := by
    intro a ha δ hδ
    simp [map_inv₀, ha δ hδ]

lemma map_mem_fixSub [hN : Δ.Normal] (g : G) {x : K} (hx : x ∈ fixSub ρ Δ) :
    ρ g x ∈ fixSub ρ Δ := by
  intro δ hδ
  have hm : g⁻¹ * δ * g ∈ Δ := by simpa using hN.conj_mem δ hδ g⁻¹
  have h := hx _ hm
  calc ρ δ (ρ g x) = ρ g (ρ (g⁻¹ * δ * g) x) := by
        rw [← rho_mul_apply, ← rho_mul_apply]; congr 1; group
    _ = ρ g x := by rw [h]

def restr [Δ.Normal] : G →* RingAut (fixSub ρ Δ) where
  toFun g :=
    { toFun := fun x => ⟨ρ g x, map_mem_fixSub ρ Δ g x.2⟩
      invFun := fun x => ⟨ρ g⁻¹ x, map_mem_fixSub ρ Δ g⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (rho_inv_apply_apply ρ g (x : K))
      right_inv := fun x => Subtype.ext (rho_apply_inv_apply ρ g (x : K))
      map_mul' := fun x y => Subtype.ext (map_mul (ρ g) (x : K) (y : K))
      map_add' := fun x y => Subtype.ext (map_add (ρ g) (x : K) (y : K)) }
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro a b
    ext x
    exact rho_mul_apply ρ a b x

lemma le_ker_restr [Δ.Normal] : Δ ≤ (restr ρ Δ).ker := by
  intro δ hδ
  rw [MonoidHom.mem_ker]
  ext x
  exact x.2 δ hδ

theorem mem_closure_of_fixed (K G : Type) [Field K] [Group G] (ρ : G →* RingAut K)
    (Δ : Subgroup G) (hN : Δ.Normal) (hfi : Δ.FiniteIndex) (Y : Set K) (f : K)
    (hY : ∀ y ∈ Y, ∀ δ ∈ Δ, ρ δ y = y) (hf : ∀ δ ∈ Δ, ρ δ f = f)
    (hfix : ∀ g : G, (∀ y ∈ Y, ρ g y = y) → ρ g f = f) :
    f ∈ Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y) := by
  let L := fixSub ρ Δ
  let act : G ⧸ Δ →* RingAut L := QuotientGroup.lift Δ (restr ρ Δ) (le_ker_restr ρ Δ)
  letI : MulSemiringAction (G ⧸ Δ) L := MulSemiringAction.compHom L act
  have hsmul : ∀ (g : G) (x : L), (((QuotientGroup.mk g : G ⧸ Δ) • x : L) : K) = ρ g x :=
    fun g x => rfl
  let F := FixedPoints.subfield (G ⧸ Δ) L
  let Y' : Set L := {y | (y : K) ∈ Y}
  let E : IntermediateField F L := IntermediateField.adjoin F Y'
  have hfE : (⟨f, hf⟩ : L) ∈ E := by
    rw [← IsGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    obtain ⟨q, rfl⟩ := FixedPoints.toAlgAut_surjective (G ⧸ Δ) L σ
    induction q using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk g : G ⧸ Δ) • (⟨f, hf⟩ : L) = ⟨f, hf⟩
      apply Subtype.ext
      rw [hsmul]
      apply hfix g
      intro y hy
      have h1 := hσ ⟨y, hY y hy⟩ (IntermediateField.subset_adjoin F Y' hy)
      have h2 := congrArg Subtype.val h1
      exact (hsmul g ⟨y, hY y hy⟩).symm.trans h2
  have hle : E.toSubfield ≤ (Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y)).comap L.subtype := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · apply Subfield.subset_closure
      left
      intro g
      have h1 := c.2 (QuotientGroup.mk g : G ⧸ Δ)
      exact (hsmul g _).symm.trans (congrArg Subtype.val h1)
    · exact Subfield.subset_closure (Or.inr hx)
  exact hle (show (⟨f, hf⟩ : L) ∈ E.toSubfield from hfE)

end GlobalTheory.ArtinFix
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FinOrbit

theorem exists_algEquiv_shift (E : Subfield ℂ) (z : ℂ) (hz : Transcendental E z) (k : ℕ) :
    ∃ g : ℂ ≃ₐ[E] ℂ, g z = z + k := by
  classical
  have hind : AlgebraicIndepOn E id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hz
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let b0 : B := ⟨z, hzB'⟩
  let f : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i + (k : MvPolynomial B E)
    else MvPolynomial.X i
  let f' : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i - (k : MvPolynomial B E)
    else MvPolynomial.X i
  let n : MvPolynomial B E ≃ₐ[E] MvPolynomial B E :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f')
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
  let e := (hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv))
  let g0 := IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv
  have hcomm : ∀ c : E, g0 (algebraMap E ℂ c) = algebraMap E ℂ c := by
    intro c
    rw [IsScalarTower.algebraMap_apply E (Algebra.adjoin E (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  refine ⟨AlgEquiv.ofRingEquiv (f := g0) hcomm, ?_⟩
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X b0)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  show g0 z = z + k
  conv_lhs => rw [← h1]
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X b0))
      = hB.1.aevalEquiv (MvPolynomial.X b0 + (k : MvPolynomial B E)) := by
    simp [e, n, f]
  rw [this, map_add (f := _), map_natCast, map_add (f := _), map_natCast, h1]

theorem isAlgebraic_of_finite_orbit :
    ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  intro E x hfin
  by_contra hx
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => x + (k : ℂ)) _ _ hfin
  · intro a b hab
    simpa using hab
  · intro k
    obtain ⟨g, hg⟩ := exists_algEquiv_shift E x hx k
    exact ⟨g, hg⟩

end GlobalTheory.FinOrbit
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

lemma nnreal_mul_max_le (a b c : ℝ≥0) (hc : c ≤ 1) : c * max a b ≤ max a (c * b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h]; exact (mul_le_of_le_one_left (by positivity) hc).trans (le_max_left _ _)

theorem exists_approxRoot_step : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ (F : Subfield L) (θ : ℝ≥0), θ ≤ 1 → v (p : L) ≤ 1 →
    (∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → ∀ α y : L, α ^ p ∈ F → y ∈ F →
    v (α - y) ≤ v α → ∃ y' ∈ F, v (α - y') ^ p ≤
      max (v (p : L) * v (α - y) * v α ^ (p - 1)) (max θ (v (p : L)) * v (α - y) ^ p) := by
  intro L _ v p hp F θ hθ hvp hF α y hα hy hβα
  set β := α - y with hβ
  set A := v (p : L) * v β * v α ^ (p - 1) with hA
  have hyα : v y ≤ v α := by
    have : y = α - β := by rw [hβ]; ring
    rw [this]; exact (Valuation.map_sub v α β).trans (max_le le_rfl hβα)
  have hpp : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  set u := α ^ p - y ^ p with hu
  have huF : u ∈ F := F.sub_mem hα (F.pow_mem hy p)
  have h1 : v (u - β ^ p) ≤ A := by
    have := GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le L v p hp y β
    have e : y + β = α := by rw [hβ]; ring
    rw [e] at this
    refine this.trans ?_
    rw [hA]
    gcongr
    exact max_le hyα hβα
  set M := max A (v β ^ p) with hM
  have hvu : v u ≤ M := by
    have : u = (u - β ^ p) + β ^ p := by ring
    rw [this]; refine (Valuation.map_add v _ _).trans ?_
    rw [Valuation.map_pow]; exact max_le_max h1 le_rfl
  obtain ⟨w, hwF, hw⟩ := hF u huF
  have hw' : v (u - w ^ p) ≤ v u := hw.trans (mul_le_of_le_one_left (by positivity) hθ)
  have hwM : v w ^ p ≤ M := by
    have : w ^ p = u - (u - w ^ p) := by ring
    rw [← Valuation.map_pow, this]
    exact ((Valuation.map_sub v _ _).trans (max_le le_rfl hw')).trans hvu
  have h2 : v (β ^ p - w ^ p) ≤ max A (θ * v β ^ p) := by
    have : β ^ p - w ^ p = -(u - β ^ p) + (u - w ^ p) := by ring
    rw [this]; refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_neg]; exact h1.trans (le_max_left _ _)
    · exact (hw.trans (mul_le_mul_of_nonneg_left hvu (by positivity))).trans (nnreal_mul_max_le _ _ _ hθ)
  refine ⟨y + w, F.add_mem hy hwF, ?_⟩
  set γ := β - w with hγ
  have e2 : α - (y + w) = γ := by rw [hγ, hβ]; ring
  rw [e2]
  set m := max (v w) (v γ) with hm
  have hmβ : m ≤ max (v β) (v w) :=
    max_le (le_max_right _ _) ((Valuation.map_sub v β w))
  have hmM : m ^ p ≤ M := by
    refine (pow_le_pow_left₀ (by positivity) hmβ p).trans ?_
    rcases le_total (v β) (v w) with h | h
    · rw [max_eq_right h]; exact hwM
    · rw [max_eq_left h]; exact le_max_right _ _
  have h3 : v ((w + γ) ^ p - w ^ p - γ ^ p) ≤ max A (v (p : L) * v β ^ p) := by
    refine (GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le L v p hp w γ).trans ?_
    have : v (p : L) * v γ * m ^ (p - 1) ≤ v (p : L) * m ^ p := by
      rw [mul_assoc, ← hpp, pow_succ, mul_comm (m ^ (p - 1)) m, hpp]
      gcongr
      exact le_max_right _ _
    refine this.trans ((mul_le_mul_of_nonneg_left hmM (by positivity)).trans (nnreal_mul_max_le _ _ _ hvp))
  have e3 : γ ^ p = (β ^ p - w ^ p) - ((w + γ) ^ p - w ^ p - γ ^ p) := by
    have : w + γ = β := by rw [hγ]; ring
    rw [this]; ring
  rw [← Valuation.map_pow, e3]
  refine (Valuation.map_sub v _ _).trans (max_le (h2.trans ?_) (h3.trans ?_))
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G], IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  first | exact @GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | exact GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | (intros; apply GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary : ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
  η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
  (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  first | exact @GlobalTheory.cochain_coboundary_prod_hom_identities | exact GlobalTheory.cochain_coboundary_prod_hom_identities | (intros; apply GlobalTheory.cochain_coboundary_prod_hom_identities <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ

theorem _root_.GlobalTheory.T.hahnSeries_pow_of_leading_qInv : ∀ {R : Type} [CommRing R] (x : HahnSeries ℚ R), x.coeff (-1) = 1 → (∀ r : ℚ, r < -1 → x.coeff r = 0) → ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  first | exact @GlobalTheory.hahn_pow_neg_one_lead | exact GlobalTheory.hahn_pow_neg_one_lead | (intros; apply GlobalTheory.hahn_pow_neg_one_lead <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.green_formula_periodic_rectangle_upperHalfPlane : ∀ (G D : ℂ → ℂ) (T a b : ℝ), 0 < T → 0 < a → a ≤ b → (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = D s) → ContinuousOn D {s : ℂ | 0 < s.im} → (∀ s : ℂ, 0 < s.im → G (s + T) = G s) → (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (b : ℂ) * Complex.I)) - (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (a : ℂ) * Complex.I)) = ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.green_periodic_rectangle | exact GlobalTheory.green_periodic_rectangle | (intros; apply GlobalTheory.green_periodic_rectangle <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix : ∀ (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ) (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ), L.det ≠ 0 → Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L) → Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0) → Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | exact GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | (intros; apply GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex → ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧ ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff : ∀ (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ), 0 < T → 0 < y → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) = T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral | exact GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral | (intros; apply GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral <;> assumption)
end
