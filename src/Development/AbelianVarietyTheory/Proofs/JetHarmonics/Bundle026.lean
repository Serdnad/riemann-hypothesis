module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle018
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdConstantCoeffDmonOfCols
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

theorem _root_.GlobalTheory.T.theta_vectors_setup_exists_eq_smul : ∀ (g : ℕ) (S : Setup g) (e F : (Fin g → ℂ) → ℂ), S.Ok → S.IsTheta e → S.IsTheta F → F ≠ 0 → ∃ c : ℂ, e = c • F := by
  first | exact @GlobalTheory.MomOne.ThetaLine.exists_eq_smul | exact GlobalTheory.MomOne.ThetaLine.exists_eq_smul | (intros; apply GlobalTheory.MomOne.ThetaLine.exists_eq_smul <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open scoped TensorProduct

namespace GlobalTheory

noncomputable section

def diagEnd {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) ∘ₗ e.toLinearMap

theorem diagEnd_apply {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) (x : U) (i : Fin n) : e (diagEnd e f x) i = f (e x i) := by
  simp [diagEnd]

theorem diagEnd_comp {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f g : V →ₗ[ℝ] V) : diagEnd e f ∘ₗ diagEnd e g = diagEnd e (f ∘ₗ g) := by
  ext x
  apply e.injective
  funext i
  simp [diagEnd_apply]

theorem trace_diagEnd {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] {n : ℕ} (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ U (diagEnd e f) = n * LinearMap.trace ℝ V f := by
  have h1 : diagEnd e f = e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) := by
    ext x; simp [diagEnd, LinearEquiv.conj_apply]
  have h2 : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i : (Fin n → V) →ₗ[ℝ] (Fin n → V)) =
      ∑ i, LinearMap.single ℝ (fun _ : Fin n => V) i ∘ₗ (f ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext; intro x
    funext j
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]

  rw [h1, LinearMap.trace_conj', h2, map_sum]
  have h3 : ∀ i : Fin n, LinearMap.trace ℝ _ (LinearMap.single ℝ (fun _ : Fin n => V) i ∘ₗ (f ∘ₗ LinearMap.proj i)) =
      LinearMap.trace ℝ V f := by
    intro i
    rw [LinearMap.trace_comp_comm']
    congr 1
    ext x; simp
  simp [h3]

def powForm {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → L) :=
  ∑ i, B.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem powForm_apply {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) (x y : Fin n → L) :
    powForm B n x y = ∑ i, B (x i) (y i) := by
  simp [powForm, LinearMap.sum_apply]

theorem powForm_single {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) (x : Fin n → L)
    (i : Fin n) (y : L) : powForm B n x (Pi.single i y) = B (x i) y := by
  rw [powForm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

theorem powForm_bijective {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (hB : Function.Bijective B)
    (n : ℕ) : Function.Bijective (powForm B n) := by
  constructor
  · intro x y h
    funext i
    apply hB.1
    ext z
    rw [← powForm_single, ← powForm_single, h]
  · intro φ
    choose x hx using fun i : Fin n => hB.2 (φ ∘ₗ LinearMap.single ℤ (fun _ : Fin n => L) i)
    refine ⟨x, ?_⟩
    apply LinearMap.pi_ext
    intro i z
    rw [powForm_single, hx]
    rfl

theorem powForm_baseChange {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ)
    (x y : ℝ ⊗[ℤ] (Fin n → L)) :
    (powForm B n).baseChange ℝ x y =
      ∑ i, B.baseChange ℝ (TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => L) x i)
        (TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => L) y i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, ha, hb, Finset.sum_add_distrib]
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb, Finset.sum_add_distrib]
    | tmul s v => simp [powForm_apply, Finset.sum_smul, Finset.sum_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def powDatum (D : Datum H) (n : ℕ) : Datum H where
  La := Fin n → D.La
  fin := by haveI := D.fin; infer_instance
  proj := by
    haveI := D.proj
    exact Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := 𝓞 E) (M := fun _ : Fin n => D.La))
  EF := powForm D.EF n
  alt := fun x => by simp [powForm_apply, D.alt]
  unimod := powForm_bijective D.EF D.unimod n
  adj := fun a x y => by simp [powForm_apply, D.adj]
  p := n * D.p
  q := n * D.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (Fin n → D.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h3 := (TensorProduct.piRight (𝓞 E) E E (fun _ : Fin n => D.La)).finrank_eq
    rw [← h1, h3, Module.finrank_pi_fintype]
    simp [h2, D.rank, mul_add]
  dom := by
    haveI := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    set e := TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => D.La) with he
    refine ⟨diagEnd e J, ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      funext i
      simp [diagEnd_apply, h1]
    · intro x y
      simp only [powForm_baseChange, ← he, diagEnd_apply, h2]
    · intro x hx
      simp only [powForm_baseChange, ← he, diagEnd_apply]
      have : ∃ i, e x i ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hx (e.injective (by rw [map_zero]; exact funext hc))
      obtain ⟨i, hi⟩ := this
      refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, h3 _ hi⟩
      by_cases hj : e x j = 0
      · simp [hj]
      · exact (h3 _ hj).le
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribSMul.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      have hAA : A = diagEnd e A0 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          funext i
          simp [diagEnd_apply, he, A0]
      have ht' : t = n * ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, diagEnd_comp, diagEnd_comp, trace_diagEnd, trace_diagEnd, k1, ← k1, k2, k3, ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
      · rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im]; ring

theorem exists_datum_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ),
    ∃ (Dw' : Datum H) (e : Dw'.La ≃ₗ[𝓞 E] (Fin n → Dw.La)),
      (∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i)) ∧ Dw'.p = n * Dw.p ∧ Dw'.q = n * Dw.q :=
  fun E _ _ _ _ Dw n => ⟨powDatum Dw n, LinearEquiv.refl (𝓞 E) (Fin n → Dw.La),
    fun x y => powForm_apply Dw.EF n x y, rfl, rfl⟩

end
end GlobalTheory
end

section

set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory


open CrudeValue SymbolCols in
theorem sum_prod_nabVal_leading_minors_of_column_jets : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), constantCoeff h = 0 → ∀ (w0 : O) (q : ℕ) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → ∀ (u : (Σ τ : T, Fin (r τ)) → Fin d → k) (lam : Fin n → (Σ τ : T, Fin (r τ)) → Fin d → k), (∀ b l l', (∃ i, col l.1 i = b) → (∃ i, col l'.1 i = b) → ∑ i, lam b l i * u l' i = if l = l' then 1 else 0) → ∀ (c : Fin n → k) (f : Fin n → PS k 1 d), (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ (colM al b).degree → coeff mo (f b) = c b * coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) = (∏ b, c b) * ∏ p, ((al p).factorial : k) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 q T _ _ r n col m hcol P al hP hal u lam hpair c f hf
  obtain ⟨h1, hhom, -, hsupp⟩ :=
    LeadingMinors.coeff_prod_leading_minors k T r n col m hcol P al hP hal
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  have halP : al ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, h1]
    exact one_ne_zero
  set E : PS k 1 d := FB.expS k ((q : k) • B.hL k h w0) with hE
  have hE1 : constantCoeff E = 1 := constantCoeff_expS _ (by
    rw [smul_eq_C_mul, map_mul, constantCoeff_hL B h hh w0, mul_zero])
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hhom (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  have hval : ∀ mo ∈ P.support, ∀ b, (colM mo b).degree ≤ (colM al b).degree →
      B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) =
        if colM mo b = colM al b then (∏ l, ((al (l, b)).factorial : k)) * c b else 0 := by
    intro mo hmo b hb
    have hsym := constantCoeff_dmonOf_prod_linear R k (algebraMap R k) d B.G _ u (lam b)
      (fun _ => 1) (colM al b) (colM mo b) (C (c b) * E)
      (fun l l' hl hl' => hpair b l l' (hsupp al halP l b (by rwa [colM_apply] at hl))
        (hsupp mo hmo l' b (by rwa [colM_apply] at hl'))) hb
    simp only [colM_apply, one_pow, mul_one, map_mul, constantCoeff_C, hE1] at hsym
    rw [nabVal_monomial, ← hE, ← hsym, ← mul_assoc, mul_comm _ (C (c b))]
    refine constantCoeff_DmonOf_congr_jet k d _ _ u (colM mo b) _ _ fun mo' hm => ?_
    refine coeff_mul_congr (colM al b).degree _ _ E (fun mo'' hm' => ?_) mo' (hm.trans hb)
    rw [coeff_C_mul]
    exact hf b mo'' hm'
  rw [Finset.sum_eq_single al]
  · rw [h1, one_mul, Finset.prod_congr rfl fun b _ => (hval al halP b le_rfl).trans (if_pos rfl),
      Finset.prod_mul_distrib, mul_comm, Fintype.prod_prod_type_right]
  · intro mo hmo hne
    obtain ⟨b, hb, hb'⟩ := exists_col mo al (hdeg mo hmo) hne
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hval mo hmo b hb, if_neg hb']), mul_zero]
  · intro hal'
    exact absurd halP hal'

end GlobalTheory
end
