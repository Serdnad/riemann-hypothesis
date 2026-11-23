module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma exists_cube {ι Y : Type} [Finite ι] [TopologicalSpace Y] {y₀ : Y} {W : Set (ι → Y)}
    (hW : W ∈ 𝓝 (fun _ => y₀ : ι → Y)) :
    ∃ U ∈ 𝓝 y₀, ∀ y : ι → Y, (∀ i, y i ∈ U) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun y hy => hsub fun i _ => Set.mem_iInter.1 (hy i) i⟩

private noncomputable def fin0 {F : Type} [Field F] [NumberField F] (x : FiniteAdeleRing (𝓞 F) F) : A F := (0, x)

private lemma continuous_finiteAdeleEmbed {F : Type} [Field F] [NumberField F] :
    Continuous (fin0 (F := F)) :=
  show Continuous fun x : FiniteAdeleRing (𝓞 F) F => ((0, x) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) from
    continuous_const.prodMk continuous_id

private noncomputable def oneAdd {F : Type} [Field F] [NumberField F]
    (X : Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (A F) :=
  fun i j => (1 : Matrix (Fin 2) (Fin 2) (A F)) i j + fin0 (X (i, j))

private lemma continuous_oneAdd {F : Type} [Field F] [NumberField F] :
    Continuous (oneAdd (F := F)) := by
  refine continuous_matrix fun i j => ?_
  exact continuous_const.add (continuous_finiteAdeleEmbed.comp (continuous_apply _))

private lemma oneAdd_zero {F : Type} [Field F] [NumberField F] :
    oneAdd (F := F) (fun _ => 0) = 1 := by
  ext i j : 2
  change (1 : Matrix (Fin 2) (Fin 2) (A F)) i j + 0 = _
  exact add_zero _

theorem UpperTheory.ConvolutionTheory.R2.C.unrOf :
    ∀ (F : Type) [Field F] [NumberField F] (P : G1 F → Prop), (∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → P g) → ∀ᶠ v in cofinite, ∀ g, At v g → IntAt v g → P g := by
  intro F _ _ P h
  have hind : IsInducing (fun g : G1 F => (g : Matrix (Fin 2) (Fin 2) (A F))) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing
  rw [Filter.Eventually, hind.nhds_eq_comap, Filter.mem_comap] at h
  obtain ⟨S, hS, hSP⟩ := h
  have h1 : S ∈ 𝓝 (oneAdd (F := F) fun _ => 0) := by
    rw [oneAdd_zero]; simpa using hS
  have h2 := continuous_oneAdd.continuousAt.preimage_mem_nhds h1
  obtain ⟨U, hU, hUS⟩ := exists_cube h2
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hU
  have hfin : ((idealSupport J : Finset _) : Set (HeightOneSpectrum (𝓞 F))).Finite :=
    Finset.finite_toSet _
  refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
  by_contra hvJ
  apply hv
  intro g hg hint
  have hone : ∀ i j, ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro i j
    by_cases hij : i = j
    · simp [Matrix.one_apply, hij]
    · simp only [Matrix.one_apply, hij, if_false, Prod.snd_zero]
      change (0 : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      exact zero_mem _
  set X : Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F :=
    fun p => (g p.1 p.2).2 - ((1 : Matrix (Fin 2) (Fin 2) (A F)) p.1 p.2).2 with hX
  have hXm : ∀ p, X p ∈ U := by
    intro p
    apply hJ
    rw [SetLike.mem_coe, mem_idealFiniteAdeles]
    intro w
    by_cases hw : w = v
    · subst hw
      rw [count_eq_zero_of_not_mem_idealSupport J (by simpa using hvJ)]
      simp only [neg_zero, WithZero.exp_zero]
      exact sub_mem (hint p.1 p.2) (hone p.1 p.2)
    · have : X p w = 0 := by
        have := hg.2 w hw p.1 p.2
        simp only [hX]
        exact sub_eq_zero.2 this
      rw [this, map_zero]
      exact zero_le
  have hgX : (g : Matrix (Fin 2) (Fin 2) (A F)) = oneAdd X := by
    ext i j : 2
    apply Prod.ext
    · have : (oneAdd X i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 + 0 := rfl
      rw [this, add_zero]
      exact hg.1 i j
    · have : (oneAdd X i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 + X (i, j) := rfl
      rw [this, hX]
      simp
  apply hSP
  · show (g : Matrix (Fin 2) (Fin 2) (A F)) ∈ S
    rw [hgX]
    exact hUS X hXm
  · exact hg.1
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma cont_param {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {μ : Measure Y} {f : Y → ℂ} (hfc : Continuous f) (hfi : Integrable f μ)
    {a b : X × Y → ℂ} (ha : Continuous a) (hb : Continuous b)
    (ha1 : ∀ z, ‖a z‖ = 1) (hb1 : ∀ z, ‖b z‖ = 1) :
    Continuous fun p : X => ∫ y, a (p, y) * f y * b (p, y) ∂μ := by
  refine continuous_of_dominated (bound := fun y => ‖f y‖) ?_ ?_ hfi.norm ?_
  · intro p
    refine Continuous.aestronglyMeasurable ?_
    exact ((ha.comp (continuous_const.prodMk continuous_id)).mul hfc).mul
      (hb.comp (continuous_const.prodMk continuous_id))
  · intro p
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_mul, ha1, hb1, one_mul, mul_one]
  · refine Eventually.of_forall fun y => ?_
    exact ((ha.comp (continuous_id.prodMk continuous_const)).mul continuous_const).mul
      (hb.comp (continuous_id.prodMk continuous_const))

section
variable {F : Type} [Field F] [NumberField F]

private theorem cψ : Continuous (ψ : A F → ℂ) := continuous_subtype_val.comp continuous_adelicChar
private theorem nψ (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _
private theorem cq (δ : F) : Continuous (q4 δ : V4 F → A F) := by
  unfold q4
  fun_prop
private theorem ca (δ : F) : Continuous fun z : (A F × V4 F) × V4 F => ψ (z.1.1 * q4 δ z.2) :=
  cψ.comp ((continuous_fst.comp continuous_fst).mul ((cq δ).comp continuous_snd))
private theorem cb (δ : F) : Continuous fun z : (A F × V4 F) × V4 F => ψ (B4 δ z.2 z.1.2) := by
  have h : Continuous fun z : (A F × V4 F) × V4 F => B4 δ z.2 z.1.2 := by
    unfold B4
    fun_prop
  exact cψ.comp h
private theorem key (δ : F) (φ : S4 F) :
    Continuous fun p : A F × V4 F => ∫ y, ψ (p.1 * q4 δ y) * φ.1 y * ψ (B4 δ y p.2) ∂(adeleMeasurePi F) :=
  cont_param (continuous_of_mem_schwartzBruhatPi φ.2) (integrable_of_mem_schwartzBruhatPi φ.2)
    (ca δ) (cb δ) (fun _ => nψ _) (fun _ => nψ _)
end

theorem UpperTheory.ConvolutionTheory.R2.C.contKer :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F), Continuous fun p : A F × V4 F => ft4 δ (fun y => ψ (p.1 * q4 δ y) * φ.1 y) p.2 := by
  intro F _ _ δ φ
  exact key δ φ
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.unitA :
    ∀ (F : Type) [Field F] [NumberField F] (x : A F), IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (x.2 v) = 1 := by
  intro F _ _ x
  constructor
  · rintro ⟨a, rfl⟩
    have hinf : ∀ w, (a : A F).1 w * ((a⁻¹ : (A F)ˣ) : A F).1 w = 1 := fun w =>
      congrArg (fun z : A F => z.1 w) a.mul_inv
    have hfin : ∀ v, (a : A F).2 v * ((a⁻¹ : (A F)ˣ) : A F).2 v = 1 := fun v =>
      congrArg (fun z : A F => z.2 v) a.mul_inv
    refine ⟨fun w h => ?_, fun v h => ?_, ?_⟩
    · have := hinf w
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · have := hfin v
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · filter_upwards [(a : A F).2.2, ((a⁻¹ : (A F)ˣ) : A F).2.2] with v h3 h4
      have hm := congrArg Valued.v (hfin v)
      rw [map_mul, map_one] at hm
      refine le_antisymm h3 ?_
      rw [← hm]
      exact mul_le_of_le_one_right' h4
  · rintro ⟨h1, h2, h3⟩
    have hmem : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
        (x.2 v)⁻¹ ∈ v.adicCompletionIntegers F := by
      filter_upwards [h3] with v hv
      change Valued.v (x.2 v)⁻¹ ≤ 1
      rw [map_inv₀, hv, inv_one]
    let y : A F := (fun w => (x.1 w)⁻¹, ⟨fun v => (x.2 v)⁻¹, hmem⟩)
    refine IsUnit.of_mul_eq_one y (Prod.ext (funext fun w => ?_) ?_)
    · exact mul_inv_cancel₀ (h1 w)
    · apply RestrictedProduct.ext
      intro v
      exact mul_inv_cancel₀ (h2 v)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem psi_eq_one {F : Type} [Field F] [NumberField F] (x : A F) (hx : x.1 = 0)
    (hU : x.2 ∈ finiteInvDifferent F) : ψ x = 1 := by
  have hxe : x = finiteAdeleInr x.2 := Prod.ext (by simpa using hx) (by simp)
  have h := finiteAdelicChar_eq_one_of_mem hU
  rw [finiteAdelicChar_apply, ← hxe] at h
  simp [ψ, h]

private theorem tensor_case {F : Type} [Field F] [NumberField F] (δ : F)
    (f : SchwartzMap (Fin 4 → mixedEmbedding.mixedSpace F) ℂ) {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F) :
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v,
      ψ (b * q4 δ v) * schwartzBruhatTensorPi f g v = schwartzBruhatTensorPi f g v := by
  have hc : IsCompact (tsupport g) := ((mem_finiteSchwartzBruhatPi F).1 hg).2
  let qf : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → FiniteAdeleRing (𝓞 F) F :=
    fun w => w 2 ^ 2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * w 3 ^ 2 - w 1 * w 0
  have hqf : Continuous qf := by
    have h (i : Fin 4) : Continuous fun w : Fin 4 → FiniteAdeleRing (𝓞 F) F => w i := continuous_apply i
    exact (((h 2).pow 2).sub (continuous_const.mul ((h 3).pow 2))).sub ((h 1).mul (h 0))
  have hU := isOpen_finiteInvDifferent F
  have h0 : ∀ᶠ a in 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), ∀ y ∈ qf '' tsupport g,
      a * y ∈ (finiteInvDifferent F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    refine (hc.image hqf).eventually_forall_of_forall_eventually (fun y _ => ?_)
    have hcont : Continuous fun z : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F => z.1 * z.2 :=
      continuous_mul
    exact hcont.continuousAt.eventually (hU.mem_nhds (by simpa using zero_mem (finiteInvDifferent F)))
  have h1 : ∀ᶠ b in 𝓝 (0 : A F), ∀ y ∈ qf '' tsupport g,
      b.2 * y ∈ (finiteInvDifferent F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (continuous_snd.tendsto (0 : A F)).eventually h0
  filter_upwards [h1] with b hb hb1 v
  by_cases hv : g (finPartPi v) = 0
  · simp [schwartzBruhatTensorPi, hv]
  · have hmem : finPartPi v ∈ tsupport g := subset_tsupport g hv
    have hq : (b * q4 δ v).2 = b.2 * qf (finPartPi v) := by
      have hp (x : A F) : (x ^ 2).2 = x.2 ^ 2 := rfl
      have hs (x y : A F) : (x - y).2 = x.2 - y.2 := rfl
      have hm (x y : A F) : (x * y).2 = x.2 * y.2 := rfl
      have ha : (algebraMap F (A F) δ).2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) δ := rfl
      simp [q4, qf, finPartPi, hp, hs, hm, UpperTheory.ConvolutionTheory.R2.rt, ha]
    have hone : ψ (b * q4 δ v) = 1 := by
      refine psi_eq_one _ (by simp [hb1]) ?_
      rw [hq]
      exact hb _ ⟨_, hmem, rfl⟩
    rw [hone, one_mul]

private theorem span_case {F : Type} [Field F] [NumberField F] (δ : F) {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * f v = f v := by
  refine Submodule.span_induction (p := fun f _ =>
    ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * f v = f v) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨p, g, hg, rfl⟩
    exact tensor_case δ p hg
  · exact Eventually.of_forall fun b _ v => by simp
  · intro x y _ _ hx hy
    filter_upwards [hx, hy] with b h1 h2 hb v
    rw [Pi.add_apply, mul_add, h1 hb v, h2 hb v]
  · intro c x _ hx
    filter_upwards [hx] with b h1 hb v
    rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, h1 hb v]

theorem UpperTheory.ConvolutionTheory.R2.C.nLevel :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F), ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → ∀ v, ψ (b * q4 δ v) * φ.1 v = φ.1 v := by
  intro F _ _ δ φ
  exact span_case δ φ.2
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma eqm {F : Type} [Field F] [NumberField F] (p q : G1 F)
    (h : (p : Matrix (Fin 2) (Fin 2) (A F)) = (q : Matrix (Fin 2) (Fin 2) (A F))) : p = q := Subtype.ext h

private lemma m4 {R : Type} (a b c d a' b' c' d' : R) (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  subst h1 h2 h3 h4; rfl

private noncomputable def nL {F : Type} [Field F] [NumberField F] (c : A F) : G1 F :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

private lemma nL_eq {F : Type} [Field F] [NumberField F] (c : A F) :
    nL c = wW F * nU (-c) * (wW F)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply eqm
  show !![1, 0; c, 1] * !![0, 1; -1, 0] = !![0, 1; -1, 0] * !![1, -c; 0, 1]
  simp [Matrix.mul_fin_two]

private lemma torus_eq {F : Type} [Field F] [NumberField F] (u : (A F)ˣ) (x y : A F)
    (h : ((u⁻¹ : (A F)ˣ) : A F) = 1 + x * y) :
    nL (y * (u : A F)) * mD u⁻¹ * nU (x * (u : A F)) = nU x * nL y := by
  have hu : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv u
  apply eqm
  show !![1, 0; y * (u : A F), 1] * !![((u⁻¹ : (A F)ˣ) : A F), 0; 0, (((u⁻¹)⁻¹ : (A F)ˣ) : A F)] *
      !![1, x * (u : A F); 0, 1] = !![1, x; 0, 1] * !![1, 0; y, 1]
  rw [inv_inv]
  generalize ((u⁻¹ : (A F)ˣ) : A F) = v at h hu
  generalize (u : A F) = t at hu
  simp only [Matrix.mul_fin_two]
  refine m4 _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · linear_combination h
  · linear_combination x * hu
  · linear_combination y * hu
  · linear_combination (y * x * t + 1) * hu - t * h

private lemma g_eq {F : Type} [Field F] [NumberField F] (g : G1 F) (u : (A F)ˣ) (ε : A F)
    (he : g 1 1 + g 1 0 * ε = u) :
    g * nU ε = nU ((g 0 0 * ε + g 0 1) * ((u⁻¹ : (A F)ˣ) : A F)) * mD u⁻¹ *
      nL (g 1 0 * ((u⁻¹ : (A F)ˣ) : A F)) := by
  have hu : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv u
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  apply eqm
  show (g : Matrix (Fin 2) (Fin 2) (A F)) * !![1, ε; 0, 1] =
    !![1, (g 0 0 * ε + g 0 1) * ((u⁻¹ : (A F)ˣ) : A F); 0, 1] *
      !![((u⁻¹ : (A F)ˣ) : A F), 0; 0, (((u⁻¹)⁻¹ : (A F)ˣ) : A F)] *
      !![1, 0; g 1 0 * ((u⁻¹ : (A F)ˣ) : A F), 1]
  rw [inv_inv]
  have hg := Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (A F))
  generalize ((u⁻¹ : (A F)ˣ) : A F) = v at hu
  generalize (u : A F) = t at hu he
  generalize (g : Matrix (Fin 2) (Fin 2) (A F)) 0 0 = a at hg hd he ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) (A F)) 0 1 = b at hg hd he ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = c at hg hd he ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = d at hg hd he ⊢
  rw [hg]
  simp only [Matrix.mul_fin_two]
  refine m4 _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · linear_combination v * hd - v * a * he - a * hu - (a * ε + b) * c * v * hu
  · linear_combination -(a * ε + b) * hu
  · linear_combination -c * hu
  · linear_combination he

theorem UpperTheory.ConvolutionTheory.R2.C.lvAlg :
    ∀ (F : Type) [Field F] [NumberField F] (H : Subgroup (G1 F)) (R : Subring (A F)) (I : AddSubgroup (A F)), (∀ r ∈ R, ∀ x ∈ I, r * x ∈ I) →
    (∀ b ∈ I, nU b ∈ H ∧ wW F * nU b * (wW F)⁻¹ ∈ H) → ∀ (g : G1 F) (u : (A F)ˣ), g 0 0 ∈ R → g 0 1 ∈ I → g 1 0 ∈ I → (u : A F) ∈ R →
    ((u⁻¹ : (A F)ˣ) : A F) ∈ R → ∀ ε ∈ I, ∀ x ∈ I, ∀ y ∈ I, g 1 1 + g 1 0 * ε = u → ((u⁻¹ : (A F)ˣ) : A F) = 1 + x * y → g ∈ H := by
  intro F _ _ H R I hRI hH g u ha hb hc huR hviR ε hε x hx y hy he hxy
  have hmul : ∀ r ∈ R, ∀ z ∈ I, z * r ∈ I := fun r hr z hz => by
    rw [mul_comm]; exact hRI r hr z hz
  have hU : ∀ b ∈ I, nU b ∈ H := fun b hb => (hH b hb).1
  have hL : ∀ b ∈ I, nL b ∈ H := fun b hb => by
    rw [nL_eq]; exact (hH (-b) (I.neg_mem hb)).2
  have hm : mD u⁻¹ ∈ H := by
    have h1 : mD u⁻¹ = (nL (y * (u : A F)))⁻¹ * (nU x * nL y) * (nU (x * (u : A F)))⁻¹ := by
      rw [← torus_eq u x y hxy]; group
    rw [h1]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hL _ (hmul _ huR _ hy)))
      (H.mul_mem (hU _ hx) (hL _ hy))) (H.inv_mem (hU _ (hmul _ huR _ hx)))
  have h2 : g = nU ((g 0 0 * ε + g 0 1) * ((u⁻¹ : (A F)ˣ) : A F)) * mD u⁻¹ *
      nL (g 1 0 * ((u⁻¹ : (A F)ˣ) : A F)) * (nU ε)⁻¹ := by
    rw [← g_eq g u ε he]; group
  rw [h2]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hU _ (hmul _ hviR _ (I.add_mem (hRI _ ha _ hε) hb))) hm)
    (hL _ (hmul _ hviR _ hc))) (H.inv_mem (hU _ hε))
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private noncomputable def hI (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (InfinitePlace F → ℝ) ≃ₜ InfiniteAdeleRing F where
  toEquiv := (TR.infEq F).toEquiv
  continuous_toFun := TR.continuous_infEq F
  continuous_invFun := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem map_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ c : ENNReal, (infiniteAdeleMeasure F).map (hI F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := by
  have hH : ((infiniteAdeleMeasure F).map (hI F).symm).IsAddHaarMeasure :=
    (TR.infEq F).symm.toAddEquiv.isAddHaarMeasure_map (infiniteAdeleMeasure F)
      (hI F).symm.continuous (hI F).continuous
  have h := Measure.isAddLeftInvariant_eq_smul ((infiniteAdeleMeasure F).map (hI F).symm)
    (volume : Measure (InfinitePlace F → ℝ))
  obtain ⟨c, hν⟩ : ∃ c : NNReal, (infiniteAdeleMeasure F).map (hI F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := ⟨_, h⟩
  refine ⟨(c : ENNReal), hν.trans ?_⟩
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

private theorem psi_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (y : InfinitePlace F → ℝ) :
    adelicChar F (infiniteAdeleInl (TR.infEq F y)) = Real.fourierChar (-∑ w, y w) := by
  rw [adelicChar_infiniteAdeleInl, ← Finset.sum_neg_distrib, addChar_map_finsetSum]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [infiniteAdelicChar_apply_of_isReal (IsTotallyReal.isReal w)]
  have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
      (TR.infEq F y w) = y w :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  rw [e2]

theorem UpperTheory.ConvolutionTheory.R2.C.splitA :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∃ (e : A F ≃ᵐ (InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F) (c : ENNReal), (∀ x, e x = (TR.pInf F x, x.2)) ∧
      (adeleMeasure F).map e = c • (volume : Measure (InfinitePlace F → ℝ)).prod (finiteAdeleMeasure F)) ∧
    ∀ x : A F, ψ x = (∏ w, Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F x w : ℝ) : ℂ))) * ((finiteAdelicChar F x.2 : Circle) : ℂ) := by
  intro F _ _ _
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨c, hc⟩ := map_inf F
    let e : A F ≃ᵐ (InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F :=
      MeasurableEquiv.prodCongr (hI F).symm.toMeasurableEquiv (MeasurableEquiv.refl _)
    refine ⟨e, c, fun x => rfl, ?_⟩
    have h1 : ((infiniteAdeleMeasure F).map (hI F).symm).prod
        ((finiteAdeleMeasure F).map id) =
        ((infiniteAdeleMeasure F).prod (finiteAdeleMeasure F)).map (Prod.map (hI F).symm id) :=
      Measure.map_prod_map _ _ (hI F).symm.measurable measurable_id
    rw [Measure.map_id, hc, Measure.prod_smul_left] at h1
    exact h1.symm
  · have hx : x = infiniteAdeleInl (TR.infEq F (TR.pInf F x)) + finiteAdeleInr x.2 := by
      have h0 : TR.infEq F (TR.pInf F x) = x.1 := (TR.infEq F).apply_symm_apply x.1
      rw [h0]
      exact (infiniteAdeleInl_add_finiteAdeleInr x).symm
    have h1 : ψ x = ((Real.fourierChar (-∑ w, TR.pInf F x w) : Circle) : ℂ) *
        ((finiteAdelicChar F x.2 : Circle) : ℂ) := by
      rw [ψ]
      conv_lhs => rw [hx]
      rw [AddChar.map_add_eq_mul, Circle.coe_mul, psi_inf, finiteAdelicChar_apply]
    rw [h1, Real.fourierChar_apply, ← Complex.exp_sum]
    congr 2
    push_cast
    rw [← Finset.mul_sum]
    ring_nf
end
