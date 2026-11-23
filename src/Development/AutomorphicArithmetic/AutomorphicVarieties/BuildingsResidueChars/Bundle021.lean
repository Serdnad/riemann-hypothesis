module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle019
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Translation
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

theorem UpperTheory.local_crystalline_of_induced :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (σ : ↥(Weil h)), deg σ = -1 → ∀ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD Bw.Kw) ρ → (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x → ((weilD Bw h P ρ σ y : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V (((φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ resDeg l w) x) := by
  intro l _ P E Ω _ _ _ _ _ A w O _ _ _ Bw h hj LL V _ _ _ _ _ ρ _ σ hσ x y hx hy
  have hφ : ∀ z : V ⊗[ℚ_[l]] P.R.B, phiV P ↥LL.1 V (crisIncl P ↥LL.1 V z) =
      crisIncl P ↥LL.1 V (φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [φVB, P.PD_φ]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hpow : ∀ n : ℕ, (((phiD P ρ ^ n) y : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      crisIncl P ↥LL.1 V (((φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) :
        Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ n) x) := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih => rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, coe_phiD, ih, hφ]
  have hfix : actD P ρ (weilToGK Bw h σ) y = y := by
    refine Subtype.ext ?_
    rw [coe_actD, hy, stRep_crisIncl]
    congr 1
    have h1 := (Submodule.mem_iInf _).mp hx (weilToGK Bw h σ)
    simpa [sub_eq_zero] using h1
  have ha : -GlobalTheory.Pst.alpha l σ = ((resDeg l w : ℕ) : ℤ) := by simp [GlobalTheory.Pst.alpha, hσ]
  rw [weilD_apply, (commute_actD_phiU P ρ _ _).eq, End.mul_apply, hfix, ha, zpow_natCast,
    Units.val_pow_eq_pow_val, coe_phiU, hpow]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

private theorem UpperTheory.frobenius_crystalline_eq_unramified {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) :
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((frobUr l ⟨x.1, x.2.2⟩ : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have h1 := (P.PD K).φ_K₀ x
  rw [P.PD_φ] at h1
  have h2 := phiB_algebraMap P ⟨x.1, x.2.2⟩
  have h3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨((P.PD K).σ x).1, ((P.PD K).σ x).2.2⟩ =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (frobUr l ⟨x.1, x.2.2⟩) := h1.symm.trans h2
  have : Nontrivial P.R.B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact zero_mem _
  exact congrArg Subtype.val ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective h3)

private theorem UpperTheory.frobenius_crystalline_iterate_eq {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (n : ℕ) (x : ↥(K0 K)) :
    ((((P.PD K).σ)^[n] x : ↥(K0 K)) : Om l) = (((frobUr l ^ n) ⟨x.1, x.2.2⟩ : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', UpperTheory.frobenius_crystalline_eq_unramified, pow_succ', AlgHom.mul_apply]
    exact congrArg (fun c => ((frobUr l c : ↥(MaximalUnramifiedExtension l)) : Om l)) (Subtype.ext ih)

theorem UpperTheory.frobenius_residue_degree_fixes :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw), 0 < resDeg l w ∧ ∀ x : ↥(K0 Bw.Kw), ((P.PD Bw.Kw).σ)^[resDeg l w] x = x := by
  intro l _ P E Ω _ _ _ _ _ A w O _ _ _ Bw h hj
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, fun x => Subtype.ext ?_⟩
  · have h1 := one_lt_normV w
    rw [normV_eq_pow (hj.mem_placesOver h), h0, pow_zero] at h1
    exact lt_irrefl _ h1
  · have h1 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0)
      (actsAs_of_deg (by simp)) ⟨x.1, x.2.2⟩
    rw [mul_one, mul_zero, pow_zero] at h1
    rw [UpperTheory.frobenius_crystalline_iterate_eq, ← h1]
    exact mem_GK.mp (weilToGK Bw h (frob h)).2 _ x.2.1
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_finiteDimensional_compact_translates_of_level_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Level S → Types S → ∃ V : Submodule ℂ (Reduction.maxCompact (K := K) (n := n) → ℂ), FiniteDimensional ℂ V ∧ ∀ φ ∈ S, ∀ g, (fun k : Reduction.maxCompact (K := K) (n := n) => φ.1 (g * k.1)) ∈ V := by
  intro K _ _ n S hLev hTyp
  obtain ⟨L, hL, hinv⟩ := hLev
  obtain ⟨V₀, hV₀, -, hφV⟩ := hTyp
  obtain ⟨L', -, hL'L, -, t, ht⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  have hk : ∀ k : Reduction.maxCompact (K := K) (n := n), ∃ c ∈ t, c⁻¹ * finPart k.1 ∈ L' :=
    fun k => ht _ (finPart_mem_integralFiniteGL k.2)
  let Ψ : (↥t → ↥V₀) →ₗ[ℂ] (Reduction.maxCompact (K := K) (n := n) → ℂ) :=
    { toFun := fun h k =>
        (h ⟨Classical.choose (hk k), (Classical.choose_spec (hk k)).1⟩ : archCompact K n → ℂ)
          ⟨archPart k.1, archPart_mem_archCompact k.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine ⟨LinearMap.range Ψ, inferInstance, ?_⟩
  intro φ hφ g
  refine ⟨fun c => ⟨fun k' => φ.1 (g * finEmb K n c.1 * infEmb K n k'.1), hφV φ hφ _⟩, ?_⟩
  funext k
  show φ.1 (g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1)) = φ.1 (g * k.1)
  have hu : (Classical.choose (hk k))⁻¹ * finPart k.1 ∈ L := hL'L (Classical.choose_spec (hk k)).2
  have e : g * k.1 = g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1) *
      finEmb K n ((Classical.choose (hk k))⁻¹ * finPart k.1) := by
    conv_lhs => rw [← infEmb_archPart_mul_finEmb_finPart k.1]
    rw [map_mul, map_inv, mul_assoc g (finEmb K n _), ← infEmb_mul_finEmb_comm]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e, hinv φ hφ _ hu]
end
