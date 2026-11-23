module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import GroundTheory.AutomorphicForms.Bundle012
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierCoordinates
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Compactness.Paracompact
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting

variable {F : Type} [Field F] [NumberField F]

private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem cons_eq {n : ℕ} :
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F)) =
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A F) 0).symm := by
  funext p
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]

private theorem fub_mp {n : ℕ} : MeasurePreserving
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F))
    ((adeleMeasure F).prod (adeleMeasurePi F)) (adeleMeasurePi F) := by
  rw [cons_eq]
  exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => adeleMeasure F) 0).symm

private theorem fub_emb {n : ℕ} : MeasurableEmbedding
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F)) := by
  rw [cons_eq]
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A F) 0).symm.measurableEmbedding

private theorem fub {n : ℕ} {f : (Fin (n + 1) → A F) → ℂ} (hf : Integrable f (adeleMeasurePi F)) :
    Integrable (fun p : A F × (Fin n → A F) => f (Fin.cons p.1 p.2))
        ((adeleMeasure F).prod (adeleMeasurePi F)) ∧
      ∫ x, f x ∂(adeleMeasurePi F) = ∫ p : A F × (Fin n → A F), f (Fin.cons p.1 p.2)
        ∂((adeleMeasure F).prod (adeleMeasurePi F)) :=
  ⟨(fub_mp.integrable_comp_emb fub_emb).2 hf, (fub_mp.integral_comp fub_emb f).symm⟩

private theorem one_int (h : (Fin 1 → A F) → ℂ) :
    ∫ a, h a ∂(adeleMeasurePi F) = ∫ s : A F, h (fun _ => s) ∂(adeleMeasure F) :=
  ((measurePreserving_funUnique (adeleMeasure F) (Fin 1)).symm.integral_comp' h).symm

private theorem reindex_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    {f : (κ → A F) → ℂ} (hf : f ∈ schwartzBruhatPi (K := F) (ι := κ)) :
    (fun x : ι → A F => f (x ∘ e)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi
    ((1 : Matrix ι ι F).submatrix e id) ((1 : Matrix ι ι F).submatrix id e)
    (by rw [Matrix.submatrix_mul_equiv]; simp) (by
      ext i j
      simp [Matrix.mul_apply, Matrix.one_apply]) hf
  convert h using 2
  rename_i x
  congr 1
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

private theorem elim_cons (a : Fin 1 → A F) (y : Fin 3 → A F) :
    (Sum.elim a y) ∘ (finSumFinEquiv (m := 1) (n := 3)).symm = (Fin.cons (a 0) y : Fin 4 → A F) := by
  ext i
  fin_cases i <;> rfl

private theorem g_mem {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (η : Fin 3 → A F) :
    (fun a : Fin 1 → A F => adelicFourierPi F (fun y : Fin 3 → A F => φ (Fin.cons (a 0) y)) η)
      ∈ schwartzBruhatPi (K := F) (ι := Fin 1) := by
  have h1 : (fun x : (Fin 1 ⊕ Fin 3) → A F => φ (x ∘ (finSumFinEquiv (m := 1) (n := 3)).symm))
      ∈ schwartzBruhatPi (K := F) (ι := Fin 1 ⊕ Fin 3) :=
    reindex_mem (finSumFinEquiv (m := 1) (n := 3)).symm hφ
  have h2 := GroundTheory.Heights₂.Theta.partialFourierPi_mem h1
  have h3 := reindex_mem (Equiv.sumComm (Fin 1) (Fin 3)) h2
  have h4 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h3 η
  convert h4 using 2
  rename_i a
  have e : (Sum.elim η a : (Fin 3 ⊕ Fin 1) → A F) ∘ (Equiv.sumComm (Fin 1) (Fin 3)) = Sum.elim a η := by
    ext s
    cases s <;> rfl
  rw [e, GroundTheory.Heights₂.Theta.partialFourierPi_sumElim]
  simp only [elim_cons]

private theorem slice_mem {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (b : A F) :
    (fun y : Fin 3 → A F => φ (Fin.cons b y)) ∈ schwartzBruhatPi (K := F) (ι := Fin 3) := by
  have h1 : (fun x : (Fin 1 ⊕ Fin 3) → A F => φ (x ∘ (finSumFinEquiv (m := 1) (n := 3)).symm))
      ∈ schwartzBruhatPi (K := F) (ι := Fin 1 ⊕ Fin 3) :=
    reindex_mem (finSumFinEquiv (m := 1) (n := 3)).symm hφ
  have h4 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 (fun _ => b)
  convert h4 using 2
  rename_i y
  rw [elim_cons]

private theorem ft_split {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (ξ : Fin 4 → A F) :
    adelicFourierPi F φ ξ = ∫ a : A F,
      adelicFourierPi F (fun y : Fin 3 → A F => φ (Fin.cons a y)) (Fin.tail ξ) * ψ (a * ξ 0)
        ∂(adeleMeasure F) := by
  have hint := integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi hφ) ξ
  obtain ⟨h1, h2⟩ := fub hint
  rw [adelicFourierPi, h2, integral_prod _ h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [adelicFourierPi]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Fin.sum_univ_succ (n := 3), Fin.cons_zero, Fin.cons_succ, Fin.tail]
  have := psi_add (a * ξ 0) (∑ i : Fin 3, y i * ξ i.succ)
  simp only [ψ] at this ⊢
  rw [this, mul_assoc]
  exact congrArg _ (mul_comm _ _)

private theorem quaternaryFourier_eq_adelic (δ : F) (f : V4 F → ℂ) (v : V4 F) (s : A F) :
    ft4 δ f (Function.update v 1 s) =
      adelicFourierPi F f ![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] := by
  rw [ft4, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e : B4 δ x (Function.update v 1 s) =
      ∑ i, x i * (![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] : Fin 4 → A F) i := by
    simp [B4, Fin.sum_univ_four]
    ring
  simp only [ψ, e]

private theorem g_hat (δ : F) (φ : S4 F) (v : V4 F) (η : Fin 3 → A F)
    (hη : η = ![-v 0, 2 * v 2, -(2 * (rt δ * v 3))]) (s : A F) :
    ft4 δ φ.1 (Function.update v 1 s) = adelicFourierPi F
      (fun a : Fin 1 → A F => adelicFourierPi F (fun y : Fin 3 → A F => φ.1 (Fin.cons (a 0) y)) η)
      (fun _ => -s) := by
  have ht : Fin.tail (![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] : Fin 4 → A F) = η := by
    rw [hη]
    ext i
    fin_cases i <;> rfl
  rw [quaternaryFourier_eq_adelic, ft_split φ.2, adelicFourierPi, one_int, ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp [ψ]

end UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting

open UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting in
theorem UpperTheory.ConvolutionTheory.R2.D.hatW :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F) (v : V4 F), δ ≠ 0 → hat (ft4 δ φ.1) v =
      ∫ z : Fin 2 → A F, hat φ.1 ![-v 1, v 0, z 0, z 1] * ψ (2 * (z 0 * v 2 - rt δ * (z 1 * v 3))) ∂(adeleMeasurePi F) := by
  intro F _ _ δ φ v _
  obtain ⟨η, hη⟩ : ∃ η : Fin 3 → A F, η = ![-v 0, 2 * v 2, -(2 * (rt δ * v 3))] := ⟨_, rfl⟩
  have hg := g_mem φ.2 η
  have inv := congrFun (adelicFourierPi_adelicFourierPi hg) (fun _ => v 1)
  rw [adelicFourierPi, one_int] at inv
  have hB : hat (ft4 δ φ.1) v =
      adelicFourierPi F (fun y : Fin 3 → A F => φ.1 (Fin.cons (-v 1) y)) η := by
    refine Eq.trans ?_ inv
    rw [hat, ← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [g_hat δ φ v η hη]
    simp [ψ]
  rw [hB, adelicFourierPi]
  have hint := integrable_mul_adelicChar_pi
    (integrable_of_mem_schwartzBruhatPi (slice_mem φ.2 (-v 1))) η
  obtain ⟨h1, h2⟩ := fub hint
  rw [h2, integral_prod_symm _ h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only []
  rw [hat, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have e1 : (Fin.cons (-v 1) (Fin.cons s z : Fin 3 → A F) : Fin 4 → A F) =
      Function.update ![-v 1, v 0, z 0, z 1] 1 s := by
    ext i
    fin_cases i <;> simp [Function.update] <;> rfl
  have e2 : ∑ i, (Fin.cons s z : Fin 3 → A F) i * η i =
      -(s * v 0) + 2 * (z 0 * v 2 - rt δ * (z 1 * v 3)) := by
    have hc : (Fin.cons s z : Fin 3 → A F) 2 = z 1 := rfl
    simp [hη, Fin.sum_univ_three, hc]
    ring
  have := psi_add (-(s * v 0)) (2 * (z 0 * v 2 - rt δ * (z 1 * v 3)))
  simp only [ψ] at this ⊢
  simp only [e1, e2, this]
  simp [mul_assoc]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem co_mkE (D : Dat F E) (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have h : D.mkE u t = u • AdeleBaseChange.adeleBasis D.b 0 + t • AdeleBaseChange.adeleBasis D.b 1 := by
    rw [AdeleBaseChange.adeleBasis_apply, AdeleBaseChange.adeleBasis_apply, D.b0, D.b1,
      Algebra.smul_def, Algebra.smul_def, map_one, mul_one]
    rfl
  funext i
  unfold Dat.co
  rw [h]
  fin_cases i <;> simp

private theorem sigma_ne (D : Dat F E) : D.σ ≠ 1 := by
  intro h
  have h1 := D.conj
  rw [h] at h1
  have h2 : (2 : E) * D.θ = 0 := by
    have : D.θ = -D.θ := h1
    linear_combination this
  have h3 : D.θ = 0 := by simpa using h2
  exact D.b.ne_zero 1 (by rw [D.b1, h3])

private theorem finrank_two (D : Dat F E) : Module.finrank F E = 2 := by
  simpa using Module.finrank_eq_card_basis D.b

private theorem galois (D : Dat F E) : IsGalois F E := by
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite D.b
  apply IsGalois.of_card_aut_eq_finrank
  rw [finrank_two D]
  apply le_antisymm
  · rw [← finrank_two D, Nat.card_congr (algEquivEquivAlgHom F E).toEquiv, Nat.card_eq_fintype_card]
    exact AlgHom.card_le
  · have : ({1, D.σ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm (sigma_ne D))
    rw [← this, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _

private theorem mul_bar (D : Dat F E) (α : (A E)ˣ) :
    AdeleBaseChange.adeleMap F E ((ideleNorm F E α : (A F)ˣ) : A F) = (α : A E) * D.bar α := by
  haveI := galois D
  rw [coe_ideleNorm, AdeleBaseChange.adeleMap_norm]
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, D.σ} := by
    haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite D.b
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair (Ne.symm (sigma_ne D)), Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank, finrank_two D]
  rw [hu, Finset.prod_pair (Ne.symm (sigma_ne D))]
  simp [Dat.bar]

end SlopeTestRemainingChoices

section Aux2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem act_aE (D : Dat F E) (α : (A E)ˣ) (y s z₀ z₁ : A F) :
    D.act (aE α)⁻¹ ![y, s, z₀, z₁] =
      ![y, (((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s, D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0,
        D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1] := by
  have hinv : (((aE α)⁻¹ : GL (Fin 2) (A E))).val = !![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] := rfl
  have hN : AdeleBaseChange.adeleMap F E (((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) =
      ((α⁻¹ : (A E)ˣ) : A E) * D.bar ((α⁻¹ : (A E)ˣ) : A E) := by
    rw [← map_inv, mul_bar]
  have hz : D.mkE 0 0 = 0 := by simp [Dat.mkE]
  have h00 : ((α⁻¹ : (A E)ˣ) : A E) * D.mkE s 0 * D.bar ((α⁻¹ : (A E)ˣ) : A E) =
      D.mkE ((((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s) 0 := by
    simp only [Dat.mkE, map_mul, hN, map_zero, zero_mul, add_zero]
    ring
  unfold Dat.act Dat.unherm
  rw [hinv]
  have hm : (!![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] * D.herm ![y, s, z₀, z₁] *
      ((!![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)).map D.bar)ᵀ) =
      !![D.mkE ((((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s) 0, ((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁;
        D.mkE z₀ (-z₁) * D.bar ((α⁻¹ : (A E)ˣ) : A E), D.mkE y 0] := by
    rw [← h00]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hm]
  simp [co_mkE]

private theorem ab_inv (a : (A F)ˣ) : ab a⁻¹ = (ab a)⁻¹ := by
  simp [ab]

private theorem integral_scale (a : (A F)ˣ) (G : A F → ℂ) :
    ∫ s, G ((a : A F) * s) ∂(adeleMeasure F) = (((ab a)⁻¹ : ℝ) : ℂ) * ∫ s, G s ∂(adeleMeasure F) := by
  have hemb : MeasurableEmbedding (fun x : A F => (a : IdeleGroup F) • x) :=
    (Homeomorph.smul (a : IdeleGroup F)).measurableEmbedding
  have h := hemb.integral_map (μ := adeleMeasure F) G
  rw [map_smul_adeleMeasure, integral_smul_measure] at h
  have h2 : ∫ s, G ((a : A F) * s) ∂(adeleMeasure F) = ∫ x, G ((a : IdeleGroup F) • x) ∂(adeleMeasure F) := rfl
  rw [h2, ← h, ENNReal.toReal_ofReal (inv_pos.2 (IdeleGroup.ideleModule F a).2).le, Complex.real_smul]
  rfl

end Aux2

theorem UpperTheory.ConvolutionTheory.R2.D.hatAE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (α : (A E)ˣ) φ y x z₀ z₁, hat (W.L (aE α) φ).1 ![y, x, z₀, z₁] =
      hat φ.1 ![y, (ideleNorm F E α : (A F)ˣ) * x, D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0,
        D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1] := by
  intro F E _ _ _ _ _ _ _ D W α φ y x z₀ z₁
  have hdet : Matrix.GeneralLinearGroup.det (aE α) = α := by
    ext
    simp [aE, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]
  have hnu : nu F (aE α) = ideleNorm F E α := by
    rw [nu, hdet]
  have hup : ∀ a b c d s : A F, Function.update ![a, b, c, d] 1 s = ![a, s, c, d] := by
    intro a b c d s
    ext i
    fin_cases i <;> simp
  set N : (A F)ˣ := ideleNorm F E α with hN
  set c₀ := D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0
  set c₁ := D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1
  let G : A F → ℂ := fun s => φ.1 ![y, s, c₀, c₁] * ψ (-(s * ((N : A F) * x)))
  have hpt : ∀ s : A F, (W.L (aE α) φ).1 (Function.update ![y, x, z₀, z₁] 1 s) * ψ (-(s * (![y, x, z₀, z₁] : V4 F) 1)) =
      (((ab N)⁻¹ : ℝ) : ℂ) * G (((N⁻¹ : (A F)ˣ) : A F) * s) := by
    intro s
    have hs : ((N⁻¹ : (A F)ˣ) : A F) * s * ((N : A F) * x) = s * x := by
      have : ((N⁻¹ : (A F)ˣ) : A F) * (N : A F) = 1 := Units.inv_mul N
      linear_combination (s * x) * this
    rw [hup, W.L_apply, hnu, act_aE]
    simp only [G, hs]
    exact mul_assoc _ _ _
  have hab : ab N ≠ 0 := (IdeleGroup.ideleModule F N).2.ne'
  have hL : hat (W.L (aE α) φ).1 ![y, x, z₀, z₁] = ∫ s, G s ∂(adeleMeasure F) := by
    unfold hat
    simp_rw [hpt]
    rw [integral_const_mul, integral_scale (N⁻¹) G, ab_inv, inv_inv, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hab]
    simp
  rw [hL]
  unfold hat
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [G, hup]
  rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

private theorem integral_mul_left_adele {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (g : A F → ℂ) :
    ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) = (((ab a)⁻¹ : ℝ) : ℂ) * ∫ s, g s ∂(adeleMeasure F) := by
  have hpos : 0 ≤ ((IdeleGroup.ideleModule F a : ℝ))⁻¹ := inv_nonneg.mpr (IdeleGroup.ideleModule F a).2.le
  have hmap := map_smul_adeleMeasure (K := F) a
  have he : MeasurableEmbedding (fun x : A F => a • x) :=
    (Homeomorph.smul a).measurableEmbedding
  have h1 : ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) =
      ∫ s, g s ∂((adeleMeasure F).map (fun x : A F => a • x)) :=
    (he.integral_map g).symm
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal hpos]
  rw [Complex.real_smul]
  rfl

theorem UpperTheory.ConvolutionTheory.R2.D.hatM :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (a : (A F)ˣ) φ v, hat (W.Om (mD a) φ).1 v = ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) *
      hat φ.1 ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] := by
  intro F E _ _ _ _ _ _ _ D W a φ v
  have hab : ((ab a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (IdeleGroup.ideleModule F a).2
  set w : V4 F := ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] with hw
  have hpt : ∀ s : A F, (fun i => (a : A F) * Function.update v 1 s i) =
      Function.update w 1 ((a : A F) * s) := by
    intro s
    funext i
    fin_cases i <;> simp [hw, Function.update]
  have hch : ∀ s : A F, (a : A F) * s * w 1 = s * v 1 := by
    intro s
    have : w 1 = ((a⁻¹ : (A F)ˣ) : A F) * v 1 := by simp [hw]
    rw [this, mul_mul_mul_comm, Units.mul_inv, one_mul]
  obtain ⟨G, hG⟩ : ∃ G : A F → ℂ, G = fun r => φ.1 (Function.update w 1 r) * ψ (-(r * w 1)) := ⟨_, rfl⟩
  have hL : hat (W.Om (mD a) φ).1 v =
      ∫ s, ((W.η.1 a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * G ((a : A F) * s) ∂(adeleMeasure F) := by
    unfold hat
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [W.Om_m, hpt s, hG, hch s]
    ring
  have hR : hat φ.1 w = ∫ s, G s ∂(adeleMeasure F) := by
    rw [hG]
    rfl
  rw [hL, integral_const_mul, integral_mul_left_adele, hR]
  push_cast
  field_simp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.D.hatN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ b φ v, hat (W.Om (nU b) φ).1 v = ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * hat φ.1 (Function.update v 1 (v 1 + b * v 0)) := by
  intro F E _ _ _ _ _ _ _ D W b φ v
  have hψ : ∀ x y : A F, ψ (x + y) = ψ x * ψ y := by
    intro x y
    simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hq : ∀ s : A F, q4 D.δ (Function.update v 1 s) = v 2 ^ 2 - rt D.δ * v 3 ^ 2 - s * v 0 := by
    intro s
    simp [q4]
  unfold hat
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have h : ψ (b * q4 D.δ (Function.update v 1 s)) * ψ (-(s * v 1)) =
      ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * ψ (-(s * (v 1 + b * v 0))) := by
    rw [← hψ, ← hψ, hq]
    congr 1
    ring
  simp only [W.Om_n, Function.update_idem, Function.update_self]
  linear_combination (φ.1 (Function.update v 1 s)) * h
end
