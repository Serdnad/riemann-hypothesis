module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Unimod
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle004
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H)

private theorem int_cv (f e g : TI K n) (hg : ∀ x, g x = cv ν f e x) :
    π.integrated ν (UnitaryRep.ccToL1 ν g) =
      π.integrated ν (UnitaryRep.ccToL1 ν f) * π.integrated ν (UnitaryRep.ccToL1 ν e) := by
  obtain ⟨g', h1, -, h2⟩ := UpperTheory.ConvolutionTheory.Tf.homConv (archGroup K n) (archGroup K n) (MonoidHom.id _)
    continuous_id ν ν f e
  have hgg : g = g' := by
    ext x
    rw [hg, h1]
    rfl
  subst hgg
  rw [h2 H π]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply,
    UnitaryRep.integrated_ccToL1_apply, UnitaryRep.compHom_apply]
  rfl

private theorem int_pow (a : TI K n) (k : ℕ) :
    ∃ c : TI K n, (∀ g, c g = cvPow ν a k g) ∧
      π.integrated ν (UnitaryRep.ccToL1 ν c) = π.integrated ν (UnitaryRep.ccToL1 ν a) ^ (k + 1) := by
  induction k with
  | zero => exact ⟨a, fun _ => rfl, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc, hT⟩ := ih
    obtain ⟨h1, h2, -⟩ := UpperTheory.ConvolutionTheory.L1.cvBasic (archGroup K n) ν a c a a.continuous a.hasCompactSupport
      c.continuous c.hasCompactSupport a.continuous a.hasCompactSupport
    have hfun : (c : archGroup K n → ℂ) = cvPow ν a k := funext hc
    refine ⟨⟨⟨cv ν a c, h1⟩, h2⟩, fun g => ?_, ?_⟩
    · change cv ν a c g = cv ν a (cvPow ν a k) g
      rw [hfun]
    · rw [int_cv ν π a c _ (fun _ => rfl), hT, pow_succ' _ (k + 1)]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.sqOp :
    UpperTheory.ConvolutionTheory.L1.SqOp := by
  intro K _ _ n ν _ b a aF m ha haF hb H _ _ _ π
  obtain ⟨-, hinv⟩ := (UpperTheory.ConvolutionTheory.Tf.unimod K n).1 ν
  let bs : TI K n := ⟨⟨fun x => conj (b x⁻¹),
      Complex.continuous_conj.comp (b.continuous.comp continuous_inv)⟩,
    (b.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z => conj z) (map_zero _)⟩
  obtain ⟨hadj, hnorm, -⟩ := UpperTheory.ConvolutionTheory.Tf.adjInt (archGroup K n) H π ν b bs (fun _ => rfl)
  have hT : π.integrated ν (UnitaryRep.ccToL1 ν a) =
      π.integrated ν (UnitaryRep.ccToL1 ν b) * star (π.integrated ν (UnitaryRep.ccToL1 ν b)) := by
    rw [ContinuousLinearMap.star_eq_adjoint, hadj]
    exact int_cv ν π b bs a ha
  have hb1 : ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ ≤ 1 := hnorm.trans hb
  obtain ⟨c, hc, hcT⟩ := int_pow ν π a m
  have hcF : c = aF := by
    ext g
    rw [hc, haF]
  refine ⟨hT, ?_, ?_, hcF ▸ hcT⟩
  · rw [hT]
    exact mul_star_self_nonneg _
  · rw [hT]
    calc _ ≤ ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ * ‖star (π.integrated ν (UnitaryRep.ccToL1 ν b))‖ := norm_mul_le _ _
      _ = ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ * ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ := by rw [norm_star]
      _ ≤ 1 := mul_le_one₀ hb1 (norm_nonneg _) hb1
end

section

theorem UpperTheory.ConvolutionTheory.L1.lactLaws :
    UpperTheory.ConvolutionTheory.L1.LactLaws := by
  intro K _ _ n β hβ
  obtain ⟨_, _, hs, h1, hm, hc, _, _⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  exact ⟨fun u => (hs u).1, h1, fun u v => (hm u v).1, fun u v => (hm u v).2, fun c u => (hc c u).1⟩
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo

theorem UpperTheory.ConvolutionTheory.L1.archBasic :
    UpperTheory.ConvolutionTheory.L1.ArchBasic := by
  intro F E _ _ _ _ _ σ m D n
  obtain ⟨h1, h2, h3, h4, h5, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (InfiniteAdeleRing F) (InfiniteAdeleRing E) _ _ m D n
  have compA_apply : ∀ i x, UpperTheory.ConvolutionTheory.L1.compA D n i x =
      archEquiv F n (D.comp n i ((archEquiv E n).symm x)) := fun _ _ => rfl
  have glueA_apply : ∀ g, UpperTheory.ConvolutionTheory.L1.glueA D n g =
      archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i)) := fun _ => rfl
  have c1 : ∀ g i, UpperTheory.ConvolutionTheory.L1.compA D n i (UpperTheory.ConvolutionTheory.L1.glueA D n g) = g i := by
    intro g i
    rw [compA_apply, glueA_apply, ContinuousMulEquiv.symm_apply_apply, h1,
      ContinuousMulEquiv.apply_symm_apply]
  have c2 : ∀ x, UpperTheory.ConvolutionTheory.L1.glueA D n (fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x) = x := by
    intro x
    rw [glueA_apply]
    simp only [compA_apply, ContinuousMulEquiv.symm_apply_apply]
    rw [h2, ContinuousMulEquiv.apply_symm_apply]
  have c3 : ∀ g h, UpperTheory.ConvolutionTheory.L1.glueA D n (g * h) =
      UpperTheory.ConvolutionTheory.L1.glueA D n g * UpperTheory.ConvolutionTheory.L1.glueA D n h := by
    intro g h
    simp only [glueA_apply]
    rw [← map_mul, ← h3]
    congr 2
    funext i
    exact map_mul (archEquiv F n).symm (g i) (h i)
  have c4 : Continuous (UpperTheory.ConvolutionTheory.L1.glueA D n) := by
    have : Continuous fun g : Fin (m + 1) → archGroup F n =>
        archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i)) :=
      (archEquiv E n).continuous.comp
        (h4.comp (continuous_pi fun i => (archEquiv F n).symm.continuous.comp (continuous_apply i)))
    exact this
  have c5 : ∀ i, Continuous (UpperTheory.ConvolutionTheory.L1.compA D n i) := by
    intro i
    have : Continuous fun x : archGroup E n =>
        archEquiv F n (D.comp n i ((archEquiv E n).symm x)) :=
      (archEquiv F n).continuous.comp ((h5 i).comp (archEquiv E n).symm.continuous)
    exact this
  let e : (Fin (m + 1) → archGroup F n) ≃ₜ* archGroup E n :=
    { toFun := UpperTheory.ConvolutionTheory.L1.glueA D n
      invFun := fun x i => UpperTheory.ConvolutionTheory.L1.compA D n i x
      left_inv := fun g => funext (c1 g)
      right_inv := c2
      map_mul' := c3
      continuous_toFun := c4
      continuous_invFun := continuous_pi c5 }
  refine ⟨c1, c2, c3, c4, c5, ?_, ?_, ?_⟩
  · refine ⟨fun i => (e.toMulEquiv.toMonoidHom).comp (MonoidHom.mulSingle (fun _ : Fin (m + 1) => archGroup F n) i), ?_, ?_⟩
    · intro i g
      rfl
    · intro i
      have hm : Continuous fun g : archGroup F n => (Pi.mulSingle i g : Fin (m + 1) → archGroup F n) :=
        by
          refine continuous_pi fun j => ?_
          by_cases hj : j = i
          · subst hj
            simpa using (continuous_id' : Continuous fun a : archGroup F n => a)
          · simpa [Pi.mulSingle_eq_of_ne hj] using continuous_const
      exact c4.comp hm
  · intro νF _
    exact e.isHaarMeasure_map (Measure.pi fun _ => νF)
  · intro φ
    have hc : Continuous fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g) :=
      continuous_finsetProd _ fun i _ => (φ i).continuous.comp (c5 i)
    have hK : IsCompact (UpperTheory.ConvolutionTheory.L1.glueA D n '' Set.pi Set.univ fun i => tsupport (φ i)) :=
      (isCompact_univ_pi fun i => (φ i).hasCompactSupport).image c4
    have hs : HasCompactSupport fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g) := by
      refine HasCompactSupport.of_support_subset_isCompact hK ?_
      intro x hx
      refine ⟨fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x, ?_, c2 x⟩
      intro i _
      apply subset_tsupport
      intro h0
      exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    exact ⟨⟨⟨_, hc⟩, hs⟩, fun g => rfl⟩
end
end

section

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem cvP_test {a b : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a)
    (hb : Continuous b ∧ HasCompactSupport b) : Continuous (cv μ a b) ∧ HasCompactSupport (cv μ a b) := by
  have h := cvBasic G μ a b b ha.1 ha.2 hb.1 hb.2 hb.1 hb.2
  exact ⟨h.1, h.2.1⟩

private theorem cvP_assoc {a b c : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a)
    (hb : Continuous b ∧ HasCompactSupport b) (hc : Continuous c ∧ HasCompactSupport c) :
    cv μ (cv μ a b) c = cv μ a (cv μ b c) :=
  (cvBasic G μ a b c ha.1 ha.2 hb.1 hb.2 hc.1 hc.2).2.2.2.1

private theorem cvP_pow_test {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (k : ℕ) :
    Continuous (cvPow μ a k) ∧ HasCompactSupport (cvPow μ a k) := by
  induction k with
  | zero => exact ha
  | succ k ih => exact cvP_test μ ha ih

private theorem cvP_add {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (j k : ℕ) :
    cv μ (cvPow μ a j) (cvPow μ a k) = cvPow μ a (j + k + 1) := by
  induction j with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
    change cv μ (cv μ a (cvPow μ a j)) (cvPow μ a k) = _
    rw [cvP_assoc μ ha (cvP_pow_test μ ha j) (cvP_pow_test μ ha k), ih,
      show j + 1 + k + 1 = (j + k + 1) + 1 by omega]
    rfl

private theorem cvP_pow_pow {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (k m : ℕ) :
    cvPow μ (cvPow μ a k) m = cvPow μ a (m * k + m + k) := by
  induction m with
  | zero => simp only [Nat.zero_mul, Nat.zero_add]; rfl
  | succ m ih =>
    change cv μ (cvPow μ a k) (cvPow μ (cvPow μ a k) m) = _
    rw [ih, cvP_add μ ha]
    congr 1
    ring

private theorem cvP_update {b ψ : G → ℂ} (hb : Continuous b ∧ HasCompactSupport b)
    (hψ : Continuous ψ ∧ HasCompactSupport ψ) (m : ℕ) :
    cvAll μ m (Function.update (fun _ => b) (Fin.last m) (cv μ b ψ)) = cv μ (cvPow μ b m) ψ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : Fin.tail (Function.update (fun _ : Fin (m + 1 + 1) => b) (Fin.last (m + 1)) (cv μ b ψ)) =
        Function.update (fun _ => b) (Fin.last m) (cv μ b ψ) := by
      rw [← Fin.succ_last, Fin.tail_update_succ]
      rfl
    have h0 : Function.update (fun _ : Fin (m + 1 + 1) => b) (Fin.last (m + 1)) (cv μ b ψ) 0 = b := by
      rw [Function.update_of_ne]
      exact (Fin.last_pos).ne
    rw [cvAll, h1, h0, ih, ← cvP_assoc μ hb (cvP_pow_test μ hb m) hψ]
    rfl

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.cvPowers :
    UpperTheory.ConvolutionTheory.L1.CvPowers := by
  intro G _ _ _ _ _ _ _ _ μ _ m a ψ ha ha' hψ hψ' k
  have h1 : cvPow μ (cvPow μ a k) m = cvPow μ (cvPow μ a m) k := by
    rw [cvP_pow_pow μ ⟨ha, ha'⟩, cvP_pow_pow μ ⟨ha, ha'⟩]
    congr 1
    ring
  refine ⟨h1, ?_, ?_⟩
  · rw [cvP_update μ (cvP_pow_test μ ⟨ha, ha'⟩ k) ⟨hψ, hψ'⟩, h1]
  · intro φ φ' _ _
    funext g
    simp only [cv]
    rw [← integral_fintype_prod_eq_prod (fun i y => φ i y * φ' i (y⁻¹ * g i))]
    congr 1
    funext y
    rw [← Finset.prod_mul_distrib]
    rfl
end

section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

private theorem pi_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → Type*} [∀ i, Field (k i)]
    {K : Type*} [Field K] (φ : (∀ i, k i) →+* K) : ∃ w, ∀ b : ∀ i, k i, b w = 0 → φ b = 0 := by
  have h1 : ∑ i, φ (Pi.single i 1) = 1 := by
    have h : (∑ x, Pi.single x 1 : ∀ i, k i) = 1 := Finset.univ_sum_single (1 : ∀ i, k i)

    rw [← map_sum, h, map_one]
  obtain ⟨w, hw⟩ : ∃ w, φ (Pi.single w 1) ≠ 0 := by
    by_contra! h
    simp [h] at h1
  refine ⟨w, fun b hb => ?_⟩
  have h0 : b * Pi.single w 1 = 0 := by
    ext i
    by_cases h : i = w
    · subst h
      simp [hb]
    · simp [Pi.single_eq_of_ne h]
  have h2 := congrArg φ h0
  rw [map_mul, map_zero] at h2
  exact (mul_eq_zero.1 h2).resolve_right hw

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem comp_eq (v : HeightOneSpectrum (𝓞 F)) (φ : CompletionsOver E v →+* v.adicCompletion F)
    (hφ : ∀ a, φ (incFin E v a) = a)
    (hs : ∀ w : PlacesOver E v, Function.Surjective (completionMap v w.1)) :
    ∃ w : PlacesOver E v, ∀ b, completionMap v w.1 (φ b) = b w := by
  classical
  obtain ⟨w, hw⟩ := pi_factor φ
  refine ⟨w, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hs w (b w)
  have h : φ (b - incFin E v a) = 0 := hw _ (by
    change b w - completionMap v w.1 a = 0
    rw [ha, sub_self])
  rw [map_sub, hφ, sub_eq_zero] at h
  rw [h, ha]

private noncomputable def pt (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) : E →ₐ[F] v.adicCompletion F where
  toRingHom := (RingEquiv.ofBijective (completionMap v w.1)
    ⟨(completionMap v w.1).injective, hs⟩).symm.toRingHom.comp (algebraMap E (w.1.adicCompletion E))
  commutes' r := by
    change (RingEquiv.ofBijective (completionMap v w.1) _).symm _ = _
    rw [RingEquiv.symm_apply_eq]
    change _ = completionMap v w.1 _
    rw [completionMap_algebraMap, ← IsScalarTower.algebraMap_apply]

private theorem completionMap_pt (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) (x : E) :
    completionMap v w.1 (pt v w hs x) = algebraMap E (w.1.adicCompletion E) x :=
  (RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩).apply_symm_apply _

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.finSplit :
    UpperTheory.ConvolutionTheory.L1.FinSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm v w₀ hs
  classical
  obtain ⟨e, he, hshift⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (v.adicCompletion F)
    (CompletionsOver E v) (tensorEquiv' E v) (pt v w₀ (hs w₀))
  have hinc : ∀ r, incFin E v r = tensorEquiv' E v (1 ⊗ₜ r) := fun r => by
    rw [tensorEquiv'_tmul, map_one, one_mul]
    rfl
  have hdiag : ∀ r i, e (incFin E v r) i = r := fun r i => by
    rw [hinc, he, map_one, map_one, one_mul]
  have hsmul : ∀ (a : v.adicCompletion F) (b : CompletionsOver E v), e (a • b) = a • e b := by
    intro a b
    funext i
    rw [Algebra.smul_def, map_mul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg (· * e b i) (hdiag a i)
  let L : CompletionsOver E v ≃ₗ[v.adicCompletion F] (Fin (m + 1) → v.adicCompletion F) :=
    { e.toAddEquiv with map_smul' := hsmul }
  let D : Split (incFin E v) (galFin σ v) m :=
    { e := e
      cont := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      cont_symm := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap
      map_diag := hdiag
      map_shift := hshift }
  have hcomp : ∀ i, ∃ w : PlacesOver E v, ∀ b, completionMap v w.1 (e b i) = b w := fun i =>
    comp_eq v ((Pi.evalRingHom _ i).comp e.toRingHom) (fun a => hdiag a i) hs
  choose w hw using hcomp
  have hne : ∀ i u, e (Pi.single u 1) i ≠ 0 → w i = u := by
    intro i u h
    by_contra hu
    apply h
    apply (completionMap v (w i).1).injective
    rw [hw, map_zero, Pi.single_eq_of_ne hu]
  have hinj : Function.Injective w := by
    intro i j h
    by_contra hij
    have key : ∀ u, u = w j → ∀ b, completionMap v u.1 (e b i) = b u → e b i = e b j := by
      intro u hu b h3
      subst hu
      exact (completionMap v (w j).1).injective (h3.trans (hw j b).symm)
    have h4 := key _ h (e.symm (Pi.single i 1)) (hw i _)
    rw [RingEquiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at h4
    exact one_ne_zero h4
  have hsurj : Function.Surjective w := by
    intro u
    have h1 : e (Pi.single u 1) ≠ 0 := fun h => by
      have h2 := congrFun ((map_eq_zero_iff e e.injective).1 h) u
      rw [Pi.single_eq_same] at h2
      exact one_ne_zero h2
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    exact ⟨i, hne i u hi⟩
  have h0 : ∀ b : CompletionsOver E v, completionMap v w₀.1 (e b 0) = b w₀ := by
    intro b
    obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective b
    induction t with
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), Pi.add_apply, map_add (f := _), hx, hy, Pi.add_apply]
    | tmul x a =>
      rw [he, map_mul]
      simp only [Fin.val_zero, pow_zero]
      rw [show ((1 : E ≃ₐ[F] E) x) = x from rfl, completionMap_pt, tensorEquiv'_tmul]
      rfl
  have hw0 : w 0 = w₀ := by
    refine hne 0 w₀ fun h => ?_
    have h1 := h0 (Pi.single w₀ 1)
    rw [h, map_zero, Pi.single_eq_same] at h1
    exact zero_ne_one h1
  exact ⟨D, Equiv.ofBijective w ⟨hinj, hsurj⟩, hw0, fun b i => hw i b⟩
end
