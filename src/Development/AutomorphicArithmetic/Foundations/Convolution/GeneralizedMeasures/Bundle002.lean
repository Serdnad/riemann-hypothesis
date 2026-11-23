module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle001
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (U : Subgroup G) (hc : IsCompact (U : Set G)) (ho : IsOpen (U : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m U = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨U, hc⟩, by
    rw [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]
    exact ⟨1, U.one_mem⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem poly_mem {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    polyEmb (n := n) (aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) p) ∈
      symmetricLaurent (n := n) := fun σ => by
  rw [← polyEmb_rename]
  congr 1
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  exact MvPolynomial.esymm_isSymmetric (Fin n) ℂ _ σ

theorem UpperTheory.ConvolutionTheory.GM.sphEx :
    SphEx := by
  intro K _ _ n _ w
  refine ⟨fun p => ?_, ?_, ?_⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    obtain ⟨H, hH⟩ := (AlgHom.mem_range _).1 (symmetricLaurent_le_range (μ := m) (F := w.adicCompletion K) (poly_mem p))
    exact ⟨fun x => (H : HeckeAlgebra m) x, _, inferInstance, m, hm, h1, H, fun _ => rfl, hH⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    refine ⟨_, inferInstance, m, hm, h1, 1, fun x => ?_, by rw [map_one, map_one, map_one]⟩
    rw [HeckeAlgebra.HeckeAlgebraLevel.val_one]
    have hr : m.real (GLnLocal.integralGL (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) = 1 := by
      simp [Measure.real, h1]
    rw [HeckeAlgebra.idem_apply, hr]
    simp only [Complex.ofReal_one, inv_one]
    rfl
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1, (H : HeckeAlgebra m).mem.2,
      fun k hk x => HeckeAlgebra.HeckeAlgebraLevel.val_mem _ _ H k hk x⟩
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem locHeight_diagPow_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ν : Fin n → ℤ) (j : ℕ) :
    locHeight (Cartan.diagPow (w.adicCompletion E) n fun i => (j : ℤ) * ν i) ≤
      locHeight (Cartan.diagPow (w.adicCompletion E) n ν) ^ j := by
  induction j with
  | zero =>
    have h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((0 : ℕ) : ℤ) * ν i) = 1 :=
      Units.ext (by simp [Cartan.coe_diagPow])
    rw [h, locHeight_one, pow_zero]
  | succ j ih =>
    have h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((j + 1 : ℕ) : ℤ) * ν i) =
        Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) *
          Cartan.diagPow (w.adicCompletion E) n ν := by
      refine Units.ext ?_
      rw [Units.val_mul, Cartan.coe_diagPow, Cartan.coe_diagPow, Cartan.coe_diagPow,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      push_cast
      rw [add_mul, one_mul, zpow_add₀ (Cartan.uniformizer_ne_zero _)]
    rw [h, pow_succ]
    exact (locHeight_mul_le_of_ultrametric _ _).trans
      (mul_le_mul_of_nonneg_right ih (locHeight_pos _).le)

private theorem locHeight_iwahori {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {a : GL (Fin n) (w.adicCompletion E)} (ha : a ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    locHeight a = 1 :=
  locHeight_eq_one_of_mem_integralGL (GLnLocal.iwahori_le_integralGL _ _ ha)

theorem UpperTheory.ConvolutionTheory.GM.htTot :
    HtTot := by
  classical
  intro F E _ _ _ _ _ n q w₀ ν
  refine ⟨locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν), one_le_locHeight _, ?_⟩
  intro j Y f hS g hg
  obtain ⟨h1, h2, h3⟩ := hS g hg
  have hfin := finite_mulSupport_locHeight_finAt (g : AdelicGLn.AdelicGL E n)
  have hbelow : ∀ x : HeightOneSpectrum (𝓞 E), x.asIdeal.LiesOver q.asIdeal →
      AdeleBaseChange.below F x = q := by
    intro x hx
    refine HeightOneSpectrum.ext ?_
    have e1 := (AdeleBaseChange.liesOver_below (K := F) x).over
    have e2 := hx.over
    exact e1.trans e2.symm
  have split : (∏ᶠ w : HeightOneSpectrum (𝓞 E), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) =
      (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) *
      ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) := by
    have h := finprod_mem_union' (f := fun w : HeightOneSpectrum (𝓞 E) =>
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n)))
      (s := {w | AdeleBaseChange.below F w ≠ q}) (t := {w | AdeleBaseChange.below F w = q})
      (Set.disjoint_left.2 fun w h₁ h₂ => h₁ h₂) (hfin.inter_of_right _) (hfin.inter_of_right _)
    have hu : {w : HeightOneSpectrum (𝓞 E) | AdeleBaseChange.below F w ≠ q} ∪
        {w | AdeleBaseChange.below F w = q} = Set.univ := by
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (em _).symm
    rw [hu, finprod_mem_univ] at h
    exact h
  have hC : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) ≤
      locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν) ^ j := by
    rw [finprod_eq_single _ w₀.1 ?_, finprod_eq_if, if_pos (hbelow _ w₀.2)]
    · obtain ⟨a, ha, b, hb, e⟩ := h2
      rw [e]
      refine (locHeight_mul_le_of_ultrametric _ _).trans ?_
      rw [locHeight_iwahori hb, mul_one]
      refine (locHeight_mul_le_of_ultrametric _ _).trans ?_
      rw [locHeight_iwahori ha, one_mul]
      exact locHeight_diagPow_le _ _ _ _
    · intro x hx
      rw [finprod_eq_if]
      split_ifs with hq
      · have hl : x.asIdeal.LiesOver q.asIdeal := hq ▸ AdeleBaseChange.liesOver_below x
        exact locHeight_iwahori (h3 ⟨x, hl⟩ fun h => hx (congrArg Subtype.val h))
      · rfl
  have hB : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q),
      locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) :=
    finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le
  have hC0 : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
      locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) :=
    finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le
  have hoff : 0 ≤ heightOff q (g : AdelicGLn.AdelicGL E n) :=
    mul_nonneg (zero_le_one.trans (one_le_prod_locHeight _)) hB
  have key : AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) =
      heightOff q (g : AdelicGLn.AdelicGL E n) *
        ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
          locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) := by
    rw [AutomorphicForm.height, split, heightOff, mul_assoc]
  rw [key]
  exact mul_le_mul h1 hC hC0 (hoff.trans h1)
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private noncomputable def trCc {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : G)
    (β : CompactlySupportedContinuousMap G ℂ) : CompactlySupportedContinuousMap G ℂ where
  toFun x := β (h⁻¹ * x)
  continuous_toFun := β.continuous.comp (continuous_const_mul h⁻¹)
  hasCompactSupport' := by
    refine HasCompactSupport.intro (β.hasCompactSupport.isCompact.image (continuous_const_mul h))
      fun x hx => ?_
    by_contra hne
    exact hx ⟨h⁻¹ * x, subset_tsupport _ hne, by simp⟩

private theorem map_integrated_trCc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (π : UnitaryRep G H) (h : G)
    (β : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π h (π.integrated ν (UnitaryRep.ccToL1 ν β) v) =
      π.integrated ν (UnitaryRep.ccToL1 ν (trCc h β)) v := by
  have e := π.map_comp_integrated ν h (UnitaryRep.ccToL1 ν β)
  have e2 : UnitaryRep.leftTranslate ν h (UnitaryRep.ccToL1 ν β) =
      UnitaryRep.ccToL1 ν (trCc h β) := by
    refine Lp.ext ?_
    have hc := (β.continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1) β.hasCompactSupport).coeFn_toLp
    have hc' := ((trCc h β).continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1)
      (trCc h β).hasCompactSupport).coeFn_toLp
    filter_upwards [UnitaryRep.coeFn_leftTranslate ν h (UnitaryRep.ccToL1 ν β), hc',
      (measurePreserving_mul_left ν h⁻¹).quasiMeasurePreserving.ae_eq_comp hc] with x h1 h2 h3
    rw [h1]
    change (UnitaryRep.ccToL1 ν β : G → ℂ) (h⁻¹ * x) = (UnitaryRep.ccToL1 ν (trCc h β)) x
    rw [show (UnitaryRep.ccToL1 ν β : G → ℂ) (h⁻¹ * x) = β (h⁻¹ * x) from h3,
      show (UnitaryRep.ccToL1 ν (trCc h β) : G → ℂ) x = trCc h β x from h2]
    rfl
  rw [e2] at e
  exact congrArg (fun A : H →L[ℂ] H => A v) e

private theorem ccToL1_smul {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (a : ℂ) (f : CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 ν (a • f) = a • UnitaryRep.ccToL1 ν f := by
  unfold UnitaryRep.ccToL1
  rw [← MemLp.toLp_const_smul]
  rfl

private theorem ccToL1_finsetSum {G ι : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (s : Finset ι) (f : ι → CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 ν (∑ i ∈ s, f i) = ∑ i ∈ s, UnitaryRep.ccToL1 ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold UnitaryRep.ccToL1
    exact MemLp.toLp_zero _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_add]
    rfl

private theorem integrated_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G ι : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (π : UnitaryRep G H) (s : Finset ι) (a : ι → ℂ)
    (f : ι → CompactlySupportedContinuousMap G ℂ) :
    π.integrated ν (UnitaryRep.ccToL1 ν (∑ i ∈ s, a i • f i)) = ∑ i ∈ s, a i • π.integrated ν (UnitaryRep.ccToL1 ν (f i)) := by

  rw [ccToL1_finsetSum, map_sum]
  simp only [ccToL1_smul, map_smul]

private theorem Ofin_sum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → TF K n) :
    Ofin μ m (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i • Ofin μ m (f i) :=
  integrated_sum m ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj) s a f

private theorem rhoF_comp_Ofin {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (y : AdelicGLn.FiniteAdelicGL K n) (e : TF K n) :
    rhoF μ y ∘L Ofin μ m e = Ofin μ m (trCc y e) := by
  refine ContinuousLinearMap.ext fun v => ?_
  exact map_integrated_trCc m
    ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj) y e v

private theorem cf_local {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (y : GL (Fin n) (w.adicCompletion K))
    (x : AdelicGLn.FiniteAdelicGL K n) : cf w (AdelicGLn.localEmbedding w y * x) = y * cf w x := by
  unfold cf
  rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]

private theorem exists_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G)
    (hJ : IsOpen (J : Set G)) (h : G → ℂ) (hc : HasCompactSupport h) :
    ∃ t : Finset (G ⧸ J), ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ J) ∈ t := by
  have hop : ∀ c : G ⧸ J, IsOpen ((QuotientGroup.mk : G → G ⧸ J) ⁻¹' {c}) := fun c => by
    have : (QuotientGroup.mk : G → G ⧸ J) ⁻¹' {c} = (fun g => c.out⁻¹ * g) ⁻¹' (J : Set G) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    rw [this]
    exact hJ.preimage (continuous_const_mul _)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover _ hop fun y _ =>
    Set.mem_iUnion.2 ⟨QuotientGroup.mk y, rfl⟩
  refine ⟨t, fun y hy => ?_⟩
  obtain ⟨c, hc', hyc⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport _ hy))
  rw [show (QuotientGroup.mk y : G ⧸ J) = c from hyc]
  exact hc'

private theorem coset_sum {G : Type*} [Group G] (J : Subgroup G) (h : G → ℂ) (hinv : ∀ k ∈ J, ∀ x, h (x * k) = h x)
    (t : Finset (G ⧸ J)) (ht : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ J) ∈ t) (y : G) :
    ∑ c ∈ t, h c.out * (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * y) = h y := by
  classical
  have hind : ∀ c : G ⧸ J, (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * y) = if (QuotientGroup.mk y : G ⧸ J) = c then 1 else 0 := fun c => by
    have : c.out⁻¹ * y ∈ (J : Set G) ↔ (QuotientGroup.mk y : G ⧸ J) = c := by
      rw [SetLike.mem_coe, ← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    by_cases hh : (QuotientGroup.mk y : G ⧸ J) = c
    · rw [if_pos hh, Set.indicator_of_mem (this.2 hh)]; rfl
    · rw [if_neg hh, Set.indicator_of_notMem (fun q => hh (this.1 q))]
  have hout : h (QuotientGroup.mk y : G ⧸ J).out = h y := by
    have hk : (QuotientGroup.mk y : G ⧸ J).out⁻¹ * y ∈ J := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have := hinv _ hk (QuotientGroup.mk y : G ⧸ J).out
    rw [mul_inv_cancel_left] at this
    exact this.symm
  simp only [hind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · exact hout
  · by_contra hne
    exact hm (ht y (Ne.symm hne))

theorem UpperTheory.ConvolutionTheory.GM.stepFin :
    StepFin := by
  intro K _ _ n hn μ _ m _ w J hJ h hc hinv r hr e₀ e₁ h0 h1
  have htr : ∀ (y : GL (Fin n) (w.adicCompletion K)) x,
      trCc (AdelicGLn.localEmbedding w y) e₀ x =
        r x * (J : Set _).indicator 1 (y⁻¹ * cf w x) := fun y x => by
    show e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x) = _
    rw [h0, ← map_inv, hr, cf_local]
  refine ⟨fun u => ?_, ?_⟩
  · refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have e : trCc (AdelicGLn.localEmbedding w k) e₀ = e₀ := by
      ext x
      rw [htr, h0]
      congr 1
      by_cases hx : cf w x ∈ (J : Set _)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (J.mul_mem (J.inv_mem hk) hx)]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        intro q
        exact hx (by simpa using J.mul_mem hk q)
    have := congrArg (fun A : LL μ →L[ℂ] LL μ => A u) (rhoF_comp_Ofin μ m (AdelicGLn.localEmbedding w k) e₀)
    simpa [e] using this
  · obtain ⟨t, ht⟩ := exists_cover J hJ h hc
    have hfs : (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ J, h c.out • rhoL μ w c.out) = ∑ c ∈ t, h c.out • rhoL μ w c.out := by
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      have hne : h c.out ≠ 0 := fun q => hc' (by simp [q])
      have := ht _ hne
      rwa [QuotientGroup.out_eq'] at this
    have he : e₁ = ∑ c ∈ t, h c.out • trCc (AdelicGLn.localEmbedding w c.out) e₀ := by
      ext x
      rw [h1, CompactlySupportedContinuousMap.sum_apply]
      simp only [CompactlySupportedContinuousMap.smul_apply, htr, smul_eq_mul]
      rw [← coset_sum J h hinv t ht (cf w x), Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hfs, he]
    rw [Ofin_sum]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← rhoF_comp_Ofin]
    rfl
end
