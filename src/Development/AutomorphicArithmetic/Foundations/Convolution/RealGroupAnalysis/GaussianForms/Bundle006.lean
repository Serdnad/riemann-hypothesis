module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle003
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhat
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem place {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (val : Valuation K Γ)
    (c d mm : K) (hc : val c ≤ 1) (hm : val mm ≤ 1) (hd : val (d - 1) ≤ val mm ^ 2)
    (hcd : val c = 1 ∨ val d = 1) (e : K) (he : e = if val d = 1 then 0 else 1) :
    val (d + c * e) = 1 ∧ val e ≤ val mm ∧ val ((d + c * e)⁻¹ - 1) ≤ val mm ^ 2 := by
  have hm2 : val mm ^ 2 ≤ 1 := pow_le_one' hm 2
  have hd1 : val d ≤ 1 := by
    have : d = (d - 1) + 1 := by ring
    rw [this]
    refine (val.map_add _ _).trans (max_le (hd.trans hm2) (by simp))
  by_cases h : val d = 1
  · simp only [h, if_true] at he
    subst he
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at h
    refine ⟨by simpa using h, by simp, ?_⟩
    have : (d + c * 0)⁻¹ - 1 = (-(d - 1)) * d⁻¹ := by
      rw [mul_zero, add_zero, neg_sub, sub_mul, mul_inv_cancel₀ hd0, one_mul]
    rw [this, map_mul, map_inv₀, Valuation.map_neg, h]
    simpa using hd
  · simp only [h, if_false] at he
    subst he
    have hlt : val d < 1 := lt_of_le_of_ne hd1 h
    have hc1 : val c = 1 := hcd.resolve_right h
    have hv1 : val (d - 1) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_right val (by simpa using hlt)]
      simp
    have hmm : 1 ≤ val mm ^ 2 := hv1 ▸ hd
    have hm1 : val mm ^ 2 = 1 := le_antisymm hm2 hmm
    have hmv : val mm = 1 := by
      refine le_antisymm hm ?_
      by_contra hlt'
      have : val mm < 1 := not_le.mp hlt'
      have := pow_lt_one₀ zero_le' this (two_ne_zero)
      exact absurd hm1 this.ne
    have hu : val (d + c * 1) = 1 := by
      rw [mul_one, Valuation.map_add_eq_of_lt_right val (by rwa [hc1]), hc1]
    refine ⟨hu, by simp [hmv], ?_⟩
    rw [hm1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (by simp))
    rw [map_inv₀, hu]
    simp

theorem UpperTheory.ConvolutionTheory.R2.C.lvEps :
    ∀ (F : Type) [Field F] [NumberField F] (m : F), m ≠ 0 → Dv 1 (rt m) → ∀ c d : A F, c.1 = 0 → d.1 = 1 → Dv 1 c → Dv (m ^ 2) (d - 1) →
    (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (c.2 v) = 1 ∨ Valued.v (d.2 v) = 1) →
    ∃ (u : (A F)ˣ) (ε x y : A F), Dv 1 (u : A F) ∧ Dv 1 ((u⁻¹ : (A F)ˣ) : A F) ∧ (ε.1 = 0 ∧ Dv m ε) ∧ (x.1 = 0 ∧ Dv m x) ∧ (y.1 = 0 ∧ Dv m y) ∧
      d + c * ε = u ∧ ((u⁻¹ : (A F)ˣ) : A F) = 1 + x * y := by
  intro F _ _ m hm0 hm c d hc1 hd1 hc hd hcd
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((rt m).2 v) = v.valuation F m :=
    fun v => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v m
  have hminv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((rt m⁻¹).2 v) = (v.valuation F m)⁻¹ :=
    fun v => (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v m⁻¹).trans (map_inv₀ _ _)
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (1 : F) = 1 := fun v => map_one _
  let e : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F :=
    fun v => if Valued.v (d.2 v) = 1 then 0 else 1
  have he_int : ∀ v : HeightOneSpectrum (𝓞 F), e v ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases h : Valued.v (d.2 v) = 1
    · simp only [e, h, if_true]
      exact zero_mem _
    · simp only [e, h, if_false]
      exact one_mem _
  let ef : FiniteAdeleRing (𝓞 F) F := ⟨e, Filter.Eventually.of_forall he_int⟩
  let ε : A F := ((0 : InfiniteAdeleRing F), ef)
  have key : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (d.2 v + c.2 v * e v) = 1 ∧ Valued.v (e v) ≤ Valued.v ((rt m).2 v) ∧
      Valued.v ((d.2 v + c.2 v * e v)⁻¹ - 1) ≤ Valued.v ((rt m).2 v) ^ 2 := by
    intro v
    refine place Valued.v (c.2 v) (d.2 v) ((rt m).2 v) ?_ ?_ ?_ (hcd v) (e v) rfl
    · have := hc v
      rwa [hone] at this
    · have := hm v
      rwa [hone] at this
    · have := hd v
      rw [map_pow, ← hmv] at this
      exact this
  have hinf : (d + c * ε).1 = 1 := by
    show d.1 + c.1 * ε.1 = 1
    rw [hd1, hc1, zero_mul, add_zero]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), (d + c * ε).2 v = d.2 v + c.2 v * e v := fun v => rfl
  have hU : IsUnit (d + c * ε) := by
    refine (UpperTheory.ConvolutionTheory.R2.C.unitA F _).2 ⟨fun w => ?_, fun v => ?_, Filter.Eventually.of_forall fun v => ?_⟩
    · rw [hinf]
      exact one_ne_zero
    · intro h0
      have := (key v).1
      rw [← hfin, h0, map_zero] at this
      exact zero_ne_one this
    · rw [hfin]
      exact (key v).1
  obtain ⟨u, hu⟩ := hU
  have huv : ∀ v : HeightOneSpectrum (𝓞 F), (u : A F).2 v = d.2 v + c.2 v * e v := by
    intro v
    rw [hu]
    rfl
  have hui : ∀ v : HeightOneSpectrum (𝓞 F), ((u⁻¹ : (A F)ˣ) : A F).2 v = ((u : A F).2 v)⁻¹ := by
    intro v
    have h1 : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := u.mul_inv
    have h2 : (u : A F).2 v * ((u⁻¹ : (A F)ˣ) : A F).2 v = 1 := congrArg (fun z : A F => z.2 v) h1
    exact (inv_eq_of_mul_eq_one_right h2).symm
  have hu1 : (u : A F).1 = 1 := by rw [hu, hinf]
  have hui1 : ((u⁻¹ : (A F)ˣ) : A F).1 = 1 := by
    have h1 : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := u.mul_inv
    have h2 : (u : A F).1 * ((u⁻¹ : (A F)ˣ) : A F).1 = 1 := congrArg Prod.fst h1
    rwa [hu1, one_mul] at h2
  have hpq : (rt m).2 * (rt m⁻¹).2 = (1 : FiniteAdeleRing (𝓞 F) F) := by
    have h1 : rt m * rt m⁻¹ = (1 : A F) := by
      rw [← map_mul, mul_inv_cancel₀ hm0, map_one]
    exact congrArg Prod.snd h1
  refine ⟨u, ε, ((0 : InfiniteAdeleRing F), (rt m).2),
    ((0 : InfiniteAdeleRing F), (((u⁻¹ : (A F)ˣ) : A F) - 1).2 * (rt m⁻¹).2), ?_, ?_, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, hu.symm, ?_⟩
  · intro v
    rw [huv, (key v).1, hone]
  · intro v
    rw [hui, map_inv₀, huv, (key v).1, hone, inv_one]
  · intro v
    rw [← hmv]
    exact (key v).2.1
  · intro v
    exact (hmv v).le
  · intro v
    have hne : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm0
    have h1 : Valued.v ((((u⁻¹ : (A F)ˣ) : A F) - 1).2 v) ≤ v.valuation F m ^ 2 := by
      have h2 : (((u⁻¹ : (A F)ˣ) : A F) - 1).2 v = (d.2 v + c.2 v * e v)⁻¹ - 1 := by
        rw [← huv, ← hui]
        rfl
      rw [h2, ← hmv]
      exact (key v).2.2
    have h3 : ((((0 : InfiniteAdeleRing F), (((u⁻¹ : (A F)ˣ) : A F) - 1).2 * (rt m⁻¹).2) : A F)).2 v =
        (((u⁻¹ : (A F)ˣ) : A F) - 1).2 v * (rt m⁻¹).2 v := rfl
    rw [h3, map_mul, hminv]
    calc _ ≤ v.valuation F m ^ 2 * (v.valuation F m)⁻¹ := mul_le_mul_left h1 _
      _ = v.valuation F m := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · refine Prod.ext ?_ ?_
    · show ((u⁻¹ : (A F)ˣ) : A F).1 = 1 + 0 * _
      rw [hui1, zero_mul, add_zero]
    · show ((u⁻¹ : (A F)ˣ) : A F).2 = 1 + (rt m).2 * ((((u⁻¹ : (A F)ˣ) : A F).2 - 1) * (rt m⁻¹).2)
      linear_combination (-(((u⁻¹ : (A F)ˣ) : A F).2 - 1)) * hpq
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.etaEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ η : HChar F, IsQuadCharOf E η ∧ (∀ a, η.1 a ^ 2 = 1) ∧ (∀ z : (A E)ˣ, η.1 (ideleNorm F E z) = 1) ∧
    ∀ a, η.1 a = 1 → ∃ (t : F) (z : (A E)ˣ), t ≠ 0 ∧ (a : A F) = rt t * (ideleNorm F E z : (A F)ˣ) := by
  intro F E _ _ _ _ _ D
  haveI : Algebra.IsQuadraticExtension F E :=
    ⟨by rw [Module.finrank_eq_card_basis D.b]; simp⟩
  have h0 : D.b 0 = 1 := D.b0
  have h1 : D.b 1 * D.b 1 = algebraMap F E D.δ := by
    rw [D.b1, ← pow_two, D.sq]
  obtain ⟨η, hq, hη⟩ := UpperTheory.ConvolutionTheory.R2.C.etaQuad F E
  have hone : ∀ a, GlobalTheory.IdeleNormChar.normSign E a = 1 → η.1 a = 1 := by
    intro a ha
    refine Units.ext ?_
    rw [hη a, ha]
    simp
  have hsign : ∀ a, η.1 a = 1 → GlobalTheory.IdeleNormChar.normSign E a = 1 := by
    intro a ha
    have h := hη a
    rw [ha] at h
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e
    · exact e
    · rw [e] at h
      norm_num at h
  have hmem : ∀ z : (A E)ˣ, ideleNorm F E z ∈ GlobalTheory.QuadSymbol.normGroup F E (A F) := by
    intro z
    obtain ⟨s, t, hst⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D (ideleNorm F E z)).2 ⟨z, rfl⟩
    exact (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).2 ⟨s, t, hst⟩
  refine ⟨η, hq, ?_, ?_, ?_⟩
  · intro a
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hη a]
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;> rw [e] <;> simp
  · intro z
    exact hone _ (GlobalTheory.IdeleNormChar.normSign_of_mem E (hmem z))
  · intro a ha
    obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 (hsign a ha)
    obtain ⟨s, u, hsu⟩ := (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).1 ht
    obtain ⟨z, hz⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D _).1 ⟨s, u, hsu⟩
    refine ⟨(t : F), z, t.ne_zero, ?_⟩
    rw [hz]
    have : a = GlobalTheory.QuadSymbol.toUnits F (A F) t * (a / GlobalTheory.QuadSymbol.toUnits F (A F) t) := by
      rw [mul_div_cancel]
    exact congrArg Units.val this
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C
open GroundTheory.Heights₂.Theta

section ChirpQ

variable {F : Type} [Field F] [NumberField F]

private theorem eval_map_hom {R S ι : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : MvPolynomial ι R) (v : ι → R) :
    MvPolynomial.eval (fun i => f (v i)) (p.map f) = f (MvPolynomial.eval v p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

private theorem continuous_eval_poly {R ι : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (p : MvPolynomial ι R) :
    Continuous fun v : ι → R => MvPolynomial.eval v p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (continuous_apply i)


variable (F) in
private noncomputable def lT : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (-((mixedTraceForm F).flip 1))

private theorem psi_split (x : A F) :
    ψ x = ((Real.fourierChar (lT F (adeleInfHom x)) : Circle) : ℂ) *
      ((finiteAdelicChar F (adeleFinHom x) : Circle) : ℂ) := by
  have h := adelicChar_mul_eq (K := F) x 1
  rw [mul_one] at h
  have h1 : homeomorphMixedSpace F (1 : A F).1 = 1 := by
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  rw [h1] at h
  have h2 : x.2 * (1 : A F).2 = adeleFinHom x := by
    change x.2 * 1 = x.2
    rw [mul_one]
  rw [h2] at h
  exact h

private theorem chirp_poly (p : MvPolynomial (Fin 4) (A F)) (φ : V4 F → ℂ)
    (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun v => ψ (MvPolynomial.eval v p) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  refine Submodule.span_induction
    (p := fun f _ => (fun v => ψ (MvPolynomial.eval v p) * f v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨φ0, g, hg, rfl⟩
    have hT := chirpInf F (Fin 4) (p.map adeleInfHom) (lT F)
    have hloc : IsLocallyConstant fun w : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
        ((finiteAdelicChar F (MvPolynomial.eval w (p.map adeleFinHom)) : Circle) : ℂ) := by
      have h1 := (isLocallyConstant_finiteAdelicChar_mul (K := F) 1).comp_continuous
        (continuous_eval_poly (p.map (adeleFinHom (K := F))))
      simpa [Function.comp_def] using h1
    have hg' : (fun w => ((finiteAdelicChar F (MvPolynomial.eval w (p.map adeleFinHom)) : Circle) : ℂ) * g w)
        ∈ finiteSchwartzBruhatPi F (ι := Fin 4) :=
      ⟨hloc.mul hg.1, hg.2.mul_left⟩
    convert schwartzBruhatTensorPi_mem (SchwartzMap.smulLeftCLM ℂ (fun x : Fin 4 → mixedEmbedding.mixedSpace F =>
      ((Real.fourierChar (lT F (MvPolynomial.eval x (p.map adeleInfHom))) : Circle) : ℂ)) φ0) hg' using 1
    funext v
    simp only [schwartzBruhatTensorPi]
    rw [SchwartzMap.smulLeftCLM_apply_apply hT, psi_split]
    simp only [smul_eq_mul, infPartPi_eq_adeleInfHom, finPartPi_eq_adeleFinHom, eval_map_hom]
    ring
  · convert (schwartzBruhatPi (K := F) (ι := Fin 4)).zero_mem using 1
    funext v
    simp
  · intro f g _ _ hf hg
    convert (schwartzBruhatPi (K := F) (ι := Fin 4)).add_mem hf hg using 1
    funext v
    simp [mul_add]
  · intro a f _ hf
    convert (schwartzBruhatPi (K := F) (ι := Fin 4)).smul_mem a hf using 1
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end ChirpQ

theorem UpperTheory.ConvolutionTheory.R2.C.chirpQ :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : A F) (y : V4 F) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) →
    (fun v => ψ (b * q4 δ v + B4 δ v y) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F _ _ δ b y φ hφ
  open MvPolynomial in
  have h := chirp_poly (F := F)
    (C b * (X 2 ^ 2 - C (rt δ) * X 3 ^ 2 - X 1 * X 0) +
      (2 * (X 2 * C (y 2) - C (rt δ) * (X 3 * C (y 3))) - X 1 * C (y 0) - X 0 * C (y 1))) φ hφ
  convert h using 3 with v
  simp [q4, B4]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma fieldCase (K : Type) [Field K] [CharZero K] {ι : Type} (s : Finset ι) (c d : ι → K)
    (h : ∀ i ∈ s, c i ≠ 0 ∨ d i ≠ 0) : ∃ t : K, ∀ i ∈ s, c i + d i * t ≠ 0 := by
  have hinf : Infinite (IsLocalRing.ResidueField K) :=
    Infinite.of_injective _ (IsLocalRing.residue K).injective
  have hc : ((s.image fun i => (c i, d i)).card : ℕ∞) < ENat.card (IsLocalRing.ResidueField K) := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top _
  obtain ⟨t, ht⟩ := UpperTheory.ConvolutionTheory.R2.C.genLoc K (s.image fun i => (c i, d i)) (by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    simpa [isUnit_iff_ne_zero] using h i hi) hc
  exact ⟨t, fun i hi => (ht _ (Finset.mem_image_of_mem _ hi)).ne_zero⟩

private lemma rowUnit {R : Type} [CommRing R] [IsLocalRing R] {a b c d : R}
    (h : a * d - b * c = 1) : IsUnit c ∨ IsUnit d := by
  by_contra hn
  push_neg at hn
  have hc : c ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal c).2 hn.1
  have hd : d ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal d).2 hn.2
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← h]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hd) (Ideal.mul_mem_left _ _ hc)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)

private lemma row {F : Type} [Field F] [NumberField F] (g : G1 F) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private lemma valUnit {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletionIntegers F) (h : IsUnit x) : Valued.v (x : v.adicCompletion F) = 1 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : Valued.v (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (u : v.adicCompletionIntegers F).2
  have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have h3 : Valued.v (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
    rw [← map_mul]
    have h4 : (((u : v.adicCompletionIntegers F)) : v.adicCompletion F) *
        (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
      exact_mod_cast congrArg (fun y : v.adicCompletionIntegers F => (y : v.adicCompletion F)) u.mul_inv
    rw [h4, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right' h2

private lemma goodPlace {F : Type} [Field F] [NumberField F] (s : Finset (G1 F))
    (v : HeightOneSpectrum (𝓞 F))
    (hint : ∀ g ∈ s, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F)
    (hbig : (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    ∃ t : v.adicCompletion F, t ∈ v.adicCompletionIntegers F ∧
      ∀ g ∈ s, Valued.v ((g 1 0).2 v + (g 1 1).2 v * t) = 1 := by
  let toO : v.adicCompletion F → v.adicCompletionIntegers F :=
    fun x => if h : x ∈ v.adicCompletionIntegers F then ⟨x, h⟩ else 0
  have hto : ∀ x (h : x ∈ v.adicCompletionIntegers F), (toO x : v.adicCompletion F) = x := by
    intro x h
    simp only [toO, dif_pos h]
  let pr : G1 F → v.adicCompletionIntegers F × v.adicCompletionIntegers F :=
    fun g => (toO ((g 1 0).2 v), toO ((g 1 1).2 v))
  obtain ⟨t, ht⟩ := UpperTheory.ConvolutionTheory.R2.C.genLoc (v.adicCompletionIntegers F) (s.image pr) (by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hp
    have hdet : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 :=
      congrArg (fun x : A F => x.2 v) (row g)
    refine rowUnit (a := toO ((g 0 0).2 v)) (b := toO ((g 0 1).2 v)) (Subtype.ext ?_)
    push_cast
    rw [hto _ (hint g hg 0 0), hto _ (hint g hg 0 1), hto _ (hint g hg 1 0), hto _ (hint g hg 1 1)]
    exact hdet) (lt_of_le_of_lt (by exact_mod_cast Finset.card_image_le) hbig)
  refine ⟨t, t.2, fun g hg => ?_⟩
  have h := valUnit v _ (ht _ (Finset.mem_image_of_mem pr hg))
  simp only [pr] at h
  push_cast at h
  rwa [hto _ (hint g hg 1 0), hto _ (hint g hg 1 1)] at h

theorem UpperTheory.ConvolutionTheory.R2.C.generic :
    ∀ (F : Type) [Field F] [NumberField F] (s : Finset (G1 F)), ∃ u : G1 F, ∀ g ∈ s, IsUnit ((g * u) 1 0) := by
  intro F _ _ s
  have hI : ∀ w : InfinitePlace F, ∃ t : w.Completion, ∀ g ∈ s, (g 1 0).1 w + (g 1 1).1 w * t ≠ 0 := by
    intro w
    haveI : CharZero w.Completion :=
      charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
    refine fieldCase w.Completion s (fun g => (g 1 0).1 w) (fun g => (g 1 1).1 w) fun g _ => ?_
    have hdet : (g 0 0).1 w * (g 1 1).1 w - (g 0 1).1 w * (g 1 0).1 w = 1 :=
      congrArg (fun x : A F => x.1 w) (row g)
    by_contra hn
    push_neg at hn
    simp only [hn.1, hn.2, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  let G : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    (∀ g ∈ s, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F) ∧
      (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  have hG : ∀ᶠ v in cofinite, G v := by
    refine Filter.Eventually.and ?_ (UpperTheory.ConvolutionTheory.R2.C.resBig F s.card)
    refine (Filter.eventually_all_finset s).2 fun g _ => ?_
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    exact (g i j).2.2
  have hF : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F,
      (G v → t ∈ v.adicCompletionIntegers F) ∧
      ∀ g ∈ s, (g 1 0).2 v + (g 1 1).2 v * t ≠ 0 ∧
        (G v → Valued.v ((g 1 0).2 v + (g 1 1).2 v * t) = 1) := by
    intro v
    by_cases hv : G v
    · obtain ⟨t, ht, hu⟩ := goodPlace s v hv.1 hv.2
      refine ⟨t, fun _ => ht, fun g hg => ⟨fun h0 => ?_, fun _ => hu g hg⟩⟩
      have := hu g hg
      rw [h0, map_zero] at this
      exact zero_ne_one this
    · obtain ⟨t, ht⟩ := fieldCase (v.adicCompletion F) s (fun g => (g 1 0).2 v)
        (fun g => (g 1 1).2 v) (fun g _ => by
          have hdet : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 :=
            congrArg (fun x : A F => x.2 v) (row g)
          by_contra hn
          push_neg at hn
          simp only [hn.1, hn.2, mul_zero, sub_zero] at hdet
          exact zero_ne_one hdet)
      exact ⟨t, fun h => absurd h hv, fun g hg => ⟨ht g hg, fun h => absurd h hv⟩⟩
  choose tI htI using hI
  choose tF htF using hF
  let tf : FiniteAdeleRing (𝓞 F) F := ⟨tF, hG.mono fun v hv => (htF v).1 hv⟩
  let t : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F := (tI, tf)
  let t' : A F := t
  let u : G1 F := ⟨!![1, 0; t', 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨u, fun g hg => ?_⟩
  have hu : (g * u) 1 0 = g 1 0 + g 1 1 * t' := by
    show (g.1 * !![1, 0; t', 1]) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp
  rw [hu]
  refine (UpperTheory.ConvolutionTheory.R2.C.unitA F _).2 ⟨fun w => htI w g hg, fun v => ((htF v).2 g hg).1, ?_⟩
  exact hG.mono fun v hv => ((htF v).2 g hg).2 hv
end
