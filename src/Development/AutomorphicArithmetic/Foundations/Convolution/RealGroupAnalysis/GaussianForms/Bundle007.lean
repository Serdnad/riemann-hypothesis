module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle528
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle002
import GroundTheory.AutomorphicForms.Bundle012
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private def upperP (F : Type) [Field F] [NumberField F] : Subgroup (G1 F) where
  carrier := {g | g 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    have hg' : g.1 1 0 = 0 := hg
    have hh' : h.1 1 0 = 0 := hh
    show (g * h).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg', hh']
    simp
  one_mem' := by
    show (1 : G1 _).1 1 0 = 0
    simp
  inv_mem' := by
    intro g hg
    have hg' : g.1 1 0 = 0 := hg
    show (g⁻¹).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hg']

private theorem bor {F : Type} [Field F] [NumberField F] {H : Type} [Monoid H]
    {N : A F → H} {M : (A F)ˣ → H} {W : H} (hR : Rel N M W) (b b' : A F) (a a' : (A F)ˣ) :
    (N b * M a) * (N b' * M a') = N (b + (a : A F) ^ 2 * b') * M (a * a') := by
  rw [hR.N_add, hR.M_mul]
  calc N b * M a * (N b' * M a') = N b * (M a * N b') * M a' := by simp only [mul_assoc]
    _ = _ := by rw [hR.MN]; simp only [mul_assoc]

private theorem gen_rel {F : Type} [Field F] [NumberField F] {H : Type} [Monoid H]
    {N : A F → H} {M : (A F)ˣ → H} {W : H} (hR : Rel N M W) (hG : Gauss N M W) (t a : (A F)ˣ) :
    W * (N (t : A F) * M a) * W =
      (N (-((t⁻¹ : (A F)ˣ) : A F)) * M (-t⁻¹)) * W * (N (-((t⁻¹ : (A F)ˣ) : A F)) * M a⁻¹) := by
  have h1 : M a * W = W * M a⁻¹ := by
    have := hR.WM a⁻¹
    rw [inv_inv] at this
    exact this.symm
  calc W * (N (t : A F) * M a) * W = W * N (t : A F) * (M a * W) := by simp only [mul_assoc]
    _ = W * N (t : A F) * W * M a⁻¹ := by rw [h1]; simp only [mul_assoc]
    _ = _ := by rw [hG t]; simp only [mul_assoc]

private theorem w_small {F : Type} [Field F] [NumberField F] {b c : A F} {a d : (A F)ˣ}
    (h : wW F * (nU b * mD a) = nU c * mD d * wW F) : b = 0 ∧ c = 0 ∧ d = a⁻¹ := by
  have h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) =
      !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] :=
    congrArg Subtype.val h
  have e11 := congrFun (congrFun h' 1) 1
  have e01 := congrFun (congrFun h' 0) 1
  have e00 := congrFun (congrFun h' 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e11 e01 e00
  exact ⟨e11, e00, (Units.ext e01).symm⟩

private theorem w_big {F : Type} [Field F] [NumberField F] {b c c' : A F} {a d d' : (A F)ˣ}
    (h : wW F * (nU b * mD a) * wW F = nU c * mD d * wW F * (nU c' * mD d')) : IsUnit b := by
  have h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) * !![(0 : A F), 1; -1, 0] =
      !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] *
        (!![1, c'; 0, 1] * !![(d' : A F), 0; 0, ((d'⁻¹ : (A F)ˣ) : A F)]) :=
    congrArg Subtype.val h
  have e := congrFun (congrFun h' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  have hu : IsUnit (b * ((a⁻¹ : (A F)ˣ) : A F)) := by
    rw [e, ← Units.val_mul]
    exact (d⁻¹ * d').isUnit.neg
  exact isUnit_of_mul_isUnit_left hu

theorem UpperTheory.ConvolutionTheory.R2.C.chunk :
    ∀ (F : Type) [Field F] [NumberField F] (H : Type) [Monoid H] (N : A F → H) (M : (A F)ˣ → H) (W : H), Rel N M W → Gauss N M W →
    (∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, IsUnit ((g * u) 1 0)) →
    ∃ Φ : G1 F →* H, (∀ b, Φ (nU b) = N b) ∧ (∀ a, Φ (mD a) = M a) ∧ Φ (wW F) = W := by
  intro F _ _ H _ N M W hR hG hgen
  obtain ⟨gR, gG, gP, gU, gC⟩ := grpRel F
  obtain ⟨N', hN'⟩ : ∃ N' : A F → Hˣ, ∀ b, (N' b : H) = N b :=
    ⟨fun b => ⟨N b, N (-b), by rw [← hR.N_add]; simp [hR.N_zero],
      by rw [← hR.N_add]; simp [hR.N_zero]⟩, fun _ => rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : (A F)ˣ → Hˣ, ∀ a, (M' a : H) = M a :=
    ⟨fun a => ⟨M a, M a⁻¹, by rw [← hR.M_mul]; simp [hR.M_one],
      by rw [← hR.M_mul]; simp [hR.M_one]⟩, fun _ => rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W' : Hˣ, (W' : H) = W := hR.W_unit
  have memP : ∀ b a, nU b * mD a ∈ upperP F := fun b a => (gP _).2 ⟨b, a, rfl⟩
  have memN : ∀ b, nU b ∈ upperP F := fun b => (gP _).2 ⟨b, 1, by rw [gR.M_one, mul_one]⟩
  have memM : ∀ a, mD a ∈ upperP F := fun a => (gP _).2 ⟨0, a, by rw [gR.N_zero, one_mul]⟩
  have hex : ∀ p : upperP F, ∃ b a, (p : G1 F) = nU b * mD a := fun p => (gP p).1 p.2
  choose bb aa hba using hex
  have huniq : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → bb p = b ∧ aa p = a :=
    fun p b a h => gU _ _ _ _ ((hba p).symm.trans h)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : upperP F →* Hˣ, ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a →
      ρ p = N' b * M' a := by
    refine ⟨MonoidHom.mk' (fun p => N' (bb p) * M' (aa p)) ?_, ?_⟩
    · intro p q
      obtain ⟨e1, e2⟩ := huniq (p * q) (bb p + (aa p : A F) ^ 2 * bb q) (aa p * aa q) (by
        rw [Subgroup.coe_mul, hba p, hba q, bor gR])
      rw [e1, e2]
      apply Units.ext
      simp only [Units.val_mul, hN', hM']
      exact (bor hR _ _ _ _).symm
    · intro p b a h
      obtain ⟨e1, e2⟩ := huniq p b a h
      simp [e1, e2]
  have ρv : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → ((ρ p : Hˣ) : H) = N b * M a := by
    intro p b a h
    rw [hρ p b a h, Units.val_mul, hN', hM']
  have c1 : ∀ p q : upperP F, wW F * p = q * wW F → W' * ρ p = ρ q * W' := by
    intro p q h
    rw [hba p, hba q] at h
    obtain ⟨hb, hc, hd⟩ := w_small h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ρv p _ _ (hba p), ρv q _ _ (hba q), hb, hc, hd, hW', hR.N_zero,
      one_mul, one_mul]
    exact hR.WM _
  have c2 : ∀ p : upperP F, (∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂) →
      ∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂ ∧ W' * ρ p * W' = ρ p₁ * W' * ρ p₂ := by
    rintro p ⟨p₁, p₂, h⟩
    rw [hba p, hba p₁, hba p₂] at h
    obtain ⟨t, ht⟩ := w_big h
    refine ⟨⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩, ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩, ?_, ?_⟩
    · rw [hba p, ← ht]
      exact gen_rel gR gG t (aa p)
    · apply Units.ext
      simp only [Units.val_mul]
      rw [ρv p _ _ (hba p), ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩ _ _ rfl,
        ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩ _ _ rfl, hW', ← ht]
      exact gen_rel hR hG t (aa p)
  have c3 : ∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, ∃ p₁ p₂ : upperP F, g * u = p₁ * wW F * p₂ := by
    intro s
    obtain ⟨u, hu⟩ := hgen s
    refine ⟨u, fun g hg => ?_⟩
    obtain ⟨b, a, b', e⟩ := (gC _).1 (hu g hg)
    exact ⟨⟨_, memP b a⟩, ⟨_, memN b'⟩, e⟩
  obtain ⟨Φ, h1, h2⟩ := GlobalTheory.bigCell_hom (G1 F) Hˣ (upperP F) (wW F) ρ W' c1 c2 c3
  refine ⟨(Units.coeHom H).comp Φ, fun b => ?_, fun a => ?_, ?_⟩
  · have := h1 ⟨_, memN b⟩
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [show Φ (nU b) = ρ ⟨_, memN b⟩ from this,
      ρv ⟨_, memN b⟩ b 1 (by rw [gR.M_one, mul_one]), hR.M_one, mul_one]
  · have := h1 ⟨_, memM a⟩
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [show Φ (mD a) = ρ ⟨_, memM a⟩ from this,
      ρv ⟨_, memM a⟩ 0 a (by rw [gR.N_zero, one_mul]), hR.N_zero, one_mul]
  · simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [h2, hW']
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd

variable {F : Type} [Field F] [NumberField F]

private noncomputable def eM (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-2⁻¹, 2⁻¹, 0, 0; 2⁻¹, 2⁻¹, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private noncomputable def eN (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem two_ne (F : Type) [Field F] [NumberField F] : (2 : F) ≠ 0 := two_ne_zero

private theorem eNM (F : Type) [Field F] [NumberField F] : eN F * eM F = 1 := by
  have h := two_ne F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eN, eM, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private theorem eMN (F : Type) [Field F] [NumberField F] : eM F * eN F = 1 := by
  have h := two_ne F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eN, eM, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private theorem e_apply (v : V4 F) :
    (eM F).map (algebraMap F (A F)) *ᵥ v =
      ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] := by
  ext1 i
  fin_cases i <;>
    simp [eM, Matrix.mulVec, dotProduct, Fin.sum_univ_four, rt] <;> ring

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem q_eq (δ : F) (b : A F) (v : V4 F) :
    b * q4 δ v = b * (rt (2⁻¹ : F) * (v 1 - v 0)) ^ 2 + (-b) * (rt (2⁻¹ : F) * (v 1 + v 0)) ^ 2
      + b * (v 2) ^ 2 + (-(rt δ * b)) * (v 3) ^ 2 := by
  have h : rt (2⁻¹ : F) * 2 = 1 := by
    have h2 : rt (2 : F) = 2 := map_ofNat _ 2
    rw [← h2, rt, rt, ← map_mul, inv_mul_cancel₀ (two_ne F), map_one]
  unfold q4
  linear_combination ((b * v 1 * v 0) * (rt (2⁻¹ : F) * 2 + 1)) * h

end UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd

open UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd in
theorem UpperTheory.ConvolutionTheory.R2.C.lamFour :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : A F) (φ : A F → ℂ), Lam4 δ b (four φ) = Lam1 b φ * Lam1 (-b) φ * Lam1 b φ * Lam1 (-(rt δ * b)) φ := by
  intro F _ _ δ b φ
  have hp := GroundTheory.Heights₂.Theta.measurePreserving_mulVec (K := F) (ι := Fin 4) (κ := Fin 4)
    (eM F) (eN F) (eNM F) (eMN F)
  let e : V4 F ≃ᵐ V4 F :=
    (GroundTheory.Heights₂.Theta.mulVecHomeomorph (eM F) (eN F) (A F) (eNM F) (eMN F)).toMeasurableEquiv
  have he : ∀ v, e v = ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] :=
    fun v => e_apply v
  have hadd : ∀ x y, e (x + y) = e x + e y := fun x y =>
    Matrix.mulVec_add _ x y
  have hmap : (adeleMeasurePi F (ι := Fin 4)).map e = (1 : ENNReal) • adeleMeasurePi F (ι := Fin 4) := by
    rw [one_smul]
    exact hp.map_eq
  let γ : Fin 4 → A F → ℂ :=
    ![fun x => ψ (b * x ^ 2), fun x => ψ ((-b) * x ^ 2), fun x => ψ (b * x ^ 2),
      fun x => ψ ((-(rt δ * b)) * x ^ 2)]
  have h3 := ((UpperTheory.ConvolutionTheory.R2.C.lamGen.2.2 (V4 F) (V4 F) (adeleMeasurePi F (ι := Fin 4))
    (adeleMeasurePi F (ι := Fin 4)) e 1 hadd hmap (fun v => ∏ i, γ i (v i))
    (fun v => ∏ i, φ (v i))).1)
  have h2 := UpperTheory.ConvolutionTheory.R2.C.lamGen.2.1 (Fin 4) (A F) (adeleMeasure F) γ (fun _ => φ)
  have hγ : (fun x : V4 F => ∏ i, γ i (e x i)) = fun v => ψ (b * q4 δ v) := by
    funext v
    rw [q_eq, psi_add, psi_add, psi_add, Fin.prod_univ_four, he]
    rfl
  have hφ : (fun x : V4 F => ∏ i, φ (e x i)) = four φ := by
    funext v
    rw [Fin.prod_univ_four, he]
    rfl
  rw [hγ, hφ] at h3
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_pow, one_mul] at h3
  unfold Lam4
  rw [h3]
  change abelian₂ (Measure.pi fun _ : Fin 4 => adeleMeasure F) _ _ = _
  rw [h2, Fin.prod_univ_four]
  rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.lamOne :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : FiniteAdeleRing (𝓞 F) F → ℂ), ∃ C : FiniteAdeleRing (𝓞 F) F → ℂ, ∀ b : (A F)ˣ, Lam1 (b : A F) (g1 g) = C (b : A F).2 * ∏ w, lamR (TR.pInf F (b : A F) w) := by
  intro F _ _ _ g
  obtain ⟨⟨e, c, he, hmap⟩, hψ⟩ := splitA F
  refine ⟨fun β => ((c.toReal : ℝ) : ℂ) ^ 2 * abelian₂ (finiteAdeleMeasure F)
    (fun x => ((finiteAdelicChar F (β * x ^ 2) : Circle) : ℂ)) g, fun b => ?_⟩
  have hne : ∀ w, TR.pInf F (b : A F) w ≠ 0 := by
    intro w h0
    have h1 : TR.pInf F (b : A F) * TR.pInf F ((b⁻¹ : (A F)ˣ) : A F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrFun h1 w
    rw [Pi.mul_apply, h0, zero_mul] at h2
    exact zero_ne_one h2
  let γi : InfinitePlace F → ℝ → ℂ := fun w x =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F (b : A F) w : ℝ) : ℂ) * (x : ℂ) ^ 2)
  let φi : InfinitePlace F → ℝ → ℂ := fun _ x => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)
  let γf : FiniteAdeleRing (𝓞 F) F → ℂ := fun x => ((finiteAdelicChar F ((b : A F).2 * x ^ 2) : Circle) : ℂ)
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    simp only [he, map_add (f := _)]
    rfl
  have h3 := (lamGen.2.2 (A F) ((InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F) (adeleMeasure F) _ e c hadd hmap
    (fun p => (∏ w, γi w (p.1 w)) * γf p.2) (fun p => (∏ w, φi w (p.1 w)) * g p.2)).1
  have h1 := lamGen.1 (InfinitePlace F → ℝ) (FiniteAdeleRing (𝓞 F) F) volume (finiteAdeleMeasure F)
    (fun v => ∏ w, γi w (v w)) (fun v => ∏ w, φi w (v w)) γf g
  have h2 := lamGen.2.1 (InfinitePlace F) ℝ volume γi φi
  have h4 : ∀ w, abelian₂ (volume : Measure ℝ) (γi w) (φi w) = lamR (TR.pInf F (b : A F) w) :=
    fun w => lamReal _ (hne w)
  have hγ : (fun x : A F => ψ ((b : A F) * x ^ 2)) =
      fun x => (∏ w, γi w ((e x).1 w)) * γf (e x).2 := by
    funext x
    rw [hψ, he]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      have : TR.pInf F ((b : A F) * x ^ 2) w = TR.pInf F (b : A F) w * (TR.pInf F x w) ^ 2 := by
        rw [map_mul, map_pow]
        rfl
      simp only [γi]
      rw [this]
      push_cast
      ring_nf
  have hφ : g1 g = fun x : A F => (∏ w, φi w ((e x).1 w)) * g (e x).2 := by
    funext x
    rw [he]
    rfl
  have hL : Lam1 (b : A F) (g1 g) = abelian₂ (adeleMeasure F) (fun x : A F => ψ ((b : A F) * x ^ 2)) (g1 g) := rfl
  have hv : (volume : Measure (InfinitePlace F → ℝ)) = Measure.pi fun _ => volume := volume_pi
  rw [hL, hγ, hφ, h3, h1, hv, h2]
  simp only [h4]
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma psi_zero {F : Type} [Field F] [NumberField F] : ψ (0 : A F) = 1 := by
  simp [ψ]

private lemma psi_add {F : Type} [Field F] [NumberField F] (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private lemma ab_one {F : Type} [Field F] [NumberField F] : ab (1 : (A F)ˣ) = 1 := by
  simp [ab]

private lemma ab_mul {F : Type} [Field F] [NumberField F] (a a' : (A F)ˣ) : ab (a * a') = ab a * ab a' := by
  simp [ab]

private lemma quadraticForm_scalar_mul {F : Type} [Field F] [NumberField F] (δ : F) (a : A F) (v : V4 F) :
    q4 δ (fun i => a * v i) = a ^ 2 * q4 δ v := by
  simp only [q4]; ring

private lemma quaternaryForm_unit_scaling {F : Type} [Field F] [NumberField F] (δ : F) (a : (A F)ˣ) (y v : V4 F) :
    B4 δ (fun i => (a : A F) * y i) (fun i => ((a⁻¹ : (A F)ˣ) : A F) * v i) = B4 δ y v := by
  have h : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1 := a.mul_inv
  simp only [B4]
  linear_combination (2 * (y 2 * v 2 - rt δ * (y 3 * v 3)) - y 1 * v 0 - y 0 * v 1) * h

theorem UpperTheory.ConvolutionTheory.R2.C.opsRel :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (O : Ops δ η), δ ≠ 0 → (∀ a, η a ^ 2 = 1) → Rel O.N O.M O.W := by
  intro F _ _ δ η O hδ hη
  have hinv : ∀ a : (A F)ˣ, η a⁻¹ = η a := by
    intro a
    rw [map_inv, inv_eq_iff_mul_eq_one, ← pow_two, hη]
  have habinv : ∀ a : (A F)ˣ, ab a⁻¹ = (ab a)⁻¹ := by
    intro a
    have h1 : ab a * ab a⁻¹ = 1 := by rw [← ab_mul, mul_inv_cancel, ab_one]
    exact eq_inv_of_mul_eq_one_right h1
  have habpos : ∀ a : (A F)ˣ, ab a ≠ 0 := by
    intro a h
    have h1 : ab a * ab a⁻¹ = 1 := by rw [← ab_mul, mul_inv_cancel, ab_one]
    simp [h] at h1
  have hWW : ∀ (φ : S4 F) v, (O.W (O.W φ)).1 v = φ.1 (-v) := by
    intro φ v
    rw [O.W_apply]
    have : (O.W φ).1 = ft4 δ φ.1 := funext (O.W_apply φ)
    rw [this]
    exact (ftBasic F δ hδ φ.1 φ.2).2.1 v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext φ v
    simp [O.N_apply, psi_zero]
  · intro b c
    ext φ v
    simp only [Module.End.mul_apply, O.N_apply, add_mul, psi_add]
    ring
  · ext φ v
    simp [O.M_apply, ab_one]
  · intro a a'
    ext φ v
    simp only [Module.End.mul_apply, O.M_apply, ab_mul, map_mul, Units.val_mul]
    push_cast
    have : (fun i => (a : A F) * (a' : A F) * v i) = fun i => (a' : A F) * ((a : A F) * v i) := by
      funext i; ring
    rw [this]
    ring
  · intro a b
    ext φ v
    simp only [Module.End.mul_apply, O.M_apply, O.N_apply, quadraticForm_scalar_mul]
    have : b * ((a : A F) ^ 2 * q4 δ v) = (a : A F) ^ 2 * b * q4 δ v := by ring
    rw [this]
    ring
  · intro a
    ext φ v
    simp only [Module.End.mul_apply]
    rw [O.W_apply, O.M_apply, O.W_apply]
    have hM : (O.M a φ).1 = fun y => ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * y i :=
      funext (O.M_apply a φ)
    rw [hM, hinv, habinv]
    have hs := measScale F a (fun y => φ.1 y * ψ (B4 δ y (fun i => ((a⁻¹ : (A F)ˣ) : A F) * v i)))
    simp only [quaternaryForm_unit_scaling] at hs
    simp only [ft4]
    have hl : ∀ y, ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 (fun i => (a : A F) * y i) * ψ (B4 δ y v)
        = (((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ)) * (φ.1 (fun i => (a : A F) * y i) * ψ (B4 δ y v)) := by
      intro y; ring
    simp only [hl]
    rw [MeasureTheory.integral_const_mul, hs]
    have hne : ((ab a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habpos a
    push_cast
    field_simp
  · refine ⟨⟨O.W, O.W * O.W * O.W, ?_, ?_⟩, rfl⟩
    · ext φ v
      simp only [Module.End.mul_apply, Module.End.one_apply]
      rw [hWW, hWW]
      simp
    · ext φ v
      simp only [Module.End.mul_apply, Module.End.one_apply]
      rw [hWW, hWW]
      simp
end
