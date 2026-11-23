module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import GroundTheory.AutomorphicForms.Bundle012
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierCoordinates
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance

variable {F : Type} [Field F] [NumberField F]

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

private def eS : Fin 4 ≃ Fin 3 ⊕ Fin 1 where
  toFun := ![.inl 0, .inr 0, .inl 1, .inl 2]
  invFun := Sum.elim ![0, 2, 3] fun _ => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    rintro (i | i)
    · fin_cases i <;> rfl
    · fin_cases i; rfl

private theorem slice_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (v : V4 F) :
    (fun y : Fin 1 → A F => φ (Function.update v 1 (y 0))) ∈ schwartzBruhatPi (K := F) (ι := Fin 1) := by
  have h1 := reindex_mem (F := F) eS hφ
  have h2 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 ![v 0, v 2, v 3]
  convert h2 using 2
  rename_i y
  congr 1
  ext i
  fin_cases i <;> simp [eS, Function.update]

end UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance

open UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance in
theorem UpperTheory.ConvolutionTheory.R2.G.hatInv :
    ∀ (F : Type) [Field F] [NumberField F] (φ : S4 F) (v : V4 F), hat (hat φ.1) v = φ.1 (Function.update v 1 (-v 1)) := by
  intro F _ _ φ v
  have hg := slice_mem φ.2 v
  have inv := congrFun (adelicFourierPi_adelicFourierPi hg) (fun _ => v 1)
  rw [adelicFourierPi, one_int] at inv
  have key : ∀ s : A F, hat φ.1 (Function.update v 1 (-s)) =
      adelicFourierPi F (fun y : Fin 1 → A F => φ.1 (Function.update v 1 (y 0))) (fun _ => s) := by
    intro s
    rw [hat, adelicFourierPi, one_int]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [ψ]
  rw [hat, ← integral_neg_eq_self]
  refine Eq.trans ?_ (inv.trans ?_)
  · refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [key]
    simp [ψ]
  · simp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.coefBd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (φ : S4 F) (C : Set (G1 F)) (U : Submodule ℂ (S4 F)), IsCompact C → FiniteDimensional ℂ U → (∀ k ∈ C, W.Om k φ ∈ U) →
    ∃ (n : ℕ) (b : Fin n → S4 F) (c : Fin n → G1 F → ℂ) (B : ℝ), (∀ i, b i ∈ U) ∧ (∀ i, ContinuousOn (c i) C) ∧
    ∀ k ∈ C, (∀ i, ‖c i k‖ ≤ B) ∧ W.Om k φ = ∑ i, c i k • b i := by
  intro F E _ _ _ _ _ _ _ D W φ C U hC hU hmem
  haveI := hU
  let b := Module.finBasis ℂ U
  let ev : V4 F → Module.Dual ℂ U := fun v =>
    { toFun := fun u => (u.1).1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have htop : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have hb : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_dualCoannihilator] at hu
      have : u = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        funext v
        exact hu (ev v) (Submodule.subset_span ⟨v, rfl⟩)
      simpa using this
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev))
    rw [← h2, hb]
    simp
  have hco : ∀ i, ∃ a : V4 F →₀ ℂ, a.sum (fun v x => x • ev v) = b.coord i := by
    intro i
    have h3 : b.coord i ∈ Submodule.span ℂ (Set.range ev) := by
      rw [htop]
      trivial
    exact (Finsupp.mem_span_range_iff_exists_finsupp).1 h3
  choose a ha using hco
  let c : Fin (Module.finrank ℂ U) → G1 F → ℂ := fun i k => ∑ v ∈ (a i).support, a i v * (W.Om k φ).1 v
  have hc : ∀ i, Continuous (c i) := by
    intro i
    refine continuous_finsetSum _ fun v _ => continuous_const.mul ?_
    exact (W.cont φ).comp (continuous_id.prodMk continuous_const)
  have hB : ∀ i, ∃ B : ℝ, ∀ k ∈ C, ‖c i k‖ ≤ B := fun i =>
    hC.exists_bound_of_continuousOn (hc i).continuousOn
  choose B hB using hB
  refine ⟨Module.finrank ℂ U, fun i => (b i).1, c, ∑ i, |B i|, fun i => (b i).2,
    fun i => (hc i).continuousOn, ?_⟩
  intro k hk
  refine ⟨fun i => ?_, ?_⟩
  · calc ‖c i k‖ ≤ B i := hB i k hk
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ i, |B i| := Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  · have hck : ∀ i, b.repr ⟨W.Om k φ, hmem k hk⟩ i = c i k := by
      intro i
      have h4 : b.coord i ⟨W.Om k φ, hmem k hk⟩ = c i k := by
        rw [← ha i, Finsupp.sum, LinearMap.sum_apply]
        rfl
      simpa using h4
    have h5 := b.sum_repr ⟨W.Om k φ, hmem k hk⟩
    have h6 := congrArg Subtype.val h5
    simp only [hck, Submodule.coe_sum, Submodule.coe_smul] at h6
    exact h6.symm
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors
open scoped GroundTheory.Global.AdeleBaseChange

namespace UpperTheory.ConvolutionTheory.R2.G.similitudePositivity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

local notation "ι" => AdeleBaseChange.adeleMap F E
local notation "BB" => AdeleBaseChange.adeleBasis (K := F) (L := E) (Dat.b D)

private theorem basis0 : BB 0 = 1 := by
  rw [AdeleBaseChange.adeleBasis_apply, D.b0, map_one]

private theorem basis1 : BB 1 = rt D.θ := by
  rw [AdeleBaseChange.adeleBasis_apply, D.b1]

private theorem mkE_eq (u t : A F) : D.mkE u t = u • BB 0 + t • BB 1 := by
  rw [basis0, basis1, Algebra.smul_def, Algebra.smul_def, AdeleBaseChange.algebraMap_adeleRing, mul_one]
  rfl

private theorem co_mkE (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  have h : D.mkE u t = ∑ j, (![u, t] : Fin 2 → A F) j • BB j := by
    simp [Fin.sum_univ_two, mkE_eq]
  funext i
  rw [h]
  change (BB).repr _ i = _
  rw [Module.Basis.repr_sum_self]

private theorem coordinate_embedNorm_zero (u t : A F) : D.co (D.mkE u t) 0 = u := by simp [co_mkE]
private theorem coordinate_embedNorm_one (u t : A F) : D.co (D.mkE u t) 1 = t := by simp [co_mkE]

private theorem mkE_co (z : A E) : D.mkE (D.co z 0) (D.co z 1) = z := by
  rw [mkE_eq]
  have := (BB).sum_repr z
  rw [Fin.sum_univ_two] at this
  exact this

private theorem θ_mul : rt D.θ * rt D.θ = ι (rt D.δ) := by
  rw [← map_mul, ← sq, D.sq, AdeleBaseChange.adeleMap_algebraMap]

private theorem norm_mkE (u t : A F) :
    Algebra.norm (A F) (D.mkE u t) = u ^ 2 - rt D.δ * t ^ 2 := by
  have hm : D.mkE u t * rt D.θ = D.mkE (rt D.δ * t) u := by
    have h := θ_mul D
    simp only [Dat.mkE, map_mul]
    linear_combination (ι t) * h
  rw [Algebra.norm_eq_matrix_det (BB), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, basis0, basis1, mul_one, hm]
  change D.co _ 0 * D.co _ 1 - D.co _ 0 * D.co _ 1 = _
  simp only [coordinate_embedNorm_zero, coordinate_embedNorm_one]
  ring

variable [IsTotallyReal F]

private theorem pInf_δ (v : InfinitePlace F) : TR.pInf F (rt D.δ) v < 0 := by
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
    (algebraMap F (InfiniteAdeleRing F) D.δ v) < 0
  simpa using D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))

include D in
private theorem nu_pos (h : GL (Fin 2) (A E)) (v : InfinitePlace F) :
    0 < TR.pInf F (nu F h : A F) v := by
  have hn : ((nu F h : (A F)ˣ) : A F) = Algebra.norm (A F) h.val.det := rfl
  have hv : TR.pInf F (nu F h : A F) v =
      (TR.pInf F (D.co h.val.det 0) v) ^ 2 - TR.pInf F (rt D.δ) v * (TR.pInf F (D.co h.val.det 1) v) ^ 2 := by
    rw [hn, ← mkE_co D h.val.det, norm_mkE, coordinate_embedNorm_zero, coordinate_embedNorm_one]
    simp [map_sub, map_mul, map_pow]
  have hne : TR.pInf F (nu F h : A F) v ≠ 0 := by
    intro h0
    have h1 : TR.pInf F (nu F h : A F) * TR.pInf F (((nu F h)⁻¹ : (A F)ˣ) : A F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrFun h1 v
    simp [h0] at h2
  have hd := pInf_δ D v
  have hge : 0 ≤ TR.pInf F (nu F h : A F) v := by
    rw [hv]
    nlinarith [sq_nonneg (TR.pInf F (D.co h.val.det 0) v), sq_nonneg (TR.pInf F (D.co h.val.det 1) v)]
  exact lt_of_le_of_ne hge (Ne.symm hne)

private theorem pInf_id (u : (TR.Rinf F)ˣ) : TR.pInf F (TR.infId F u).val = u.val := by
  change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  simp [h]

end UpperTheory.ConvolutionTheory.R2.G.similitudePositivity

open UpperTheory.ConvolutionTheory.R2.G.similitudePositivity in
theorem UpperTheory.ConvolutionTheory.R2.G.nuPos :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (h : GL (Fin 2) (A E)), ∃ s : (A F)ˣ, ((nu F h * (s ^ 4)⁻¹ : (A F)ˣ) : A F).1 = 1 := by
  intro F E _ _ _ _ _ _ _ D h
  have hpos := nu_pos D h
  let r : TR.Rinf F := TR.pInf F (nu F h : A F)
  have hroot : ∀ w, 0 < Real.sqrt (Real.sqrt (r w)) := fun w => Real.sqrt_pos.2 (Real.sqrt_pos.2 (hpos w))
  let d : (TR.Rinf F)ˣ :=
    ⟨fun w => Real.sqrt (Real.sqrt (r w)), fun w => (Real.sqrt (Real.sqrt (r w)))⁻¹,
      funext fun w => mul_inv_cancel₀ (hroot w).ne', funext fun w => inv_mul_cancel₀ (hroot w).ne'⟩
  refine ⟨TR.infId F d, ?_⟩
  have e : TR.pInf F (nu F h : A F) = TR.pInf F (((TR.infId F d) ^ 4 : (A F)ˣ) : A F) := by
    rw [Units.val_pow_eq_pow_val, map_pow, pInf_id]
    funext w
    have h1 : Real.sqrt (Real.sqrt (r w)) ^ 2 = Real.sqrt (r w) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (r w) ^ 2 = r w := Real.sq_sqrt (hpos w).le
    change r w = Real.sqrt (Real.sqrt (r w)) ^ 4
    calc r w = (Real.sqrt (Real.sqrt (r w)) ^ 2) ^ 2 := by rw [h1, h2]
      _ = _ := by ring
  have hp : TR.pInf F ((nu F h * ((TR.infId F d) ^ 4)⁻¹ : (A F)ˣ) : A F) = 1 := by
    rw [Units.val_mul, map_mul, e, ← map_mul, Units.mul_inv, map_one]
  exact (TR.infEq F).symm.injective (by rw [map_one]; exact hp)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem setIntegral_haar {E : Type} [Field E] [NumberField E] {a r : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (g : GA E a) (h : constantTerm r φ g = 0) (ν : Measure (UPos a r → Ad E))
    [ν.IsAddHaarMeasure] {D : Set (UPos a r → Ad E)} (hD : IsAddFundamentalDomain (unipLattice E a r) D ν) :
    ∫ x in D, φ (unipGL x * g) ∂ν = 0 := by
  have hD' : IsAddFundamentalDomain (unipLattice E a r) D (unipMeasure E a r) :=
    hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  rw [constantTerm_eq_setIntegral hl hD'] at h
  rw [Measure.isAddLeftInvariant_eq_smul ν (unipMeasure E a r), Measure.restrict_smul, integral_smul_nnreal_measure, h,
    smul_zero]

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private def ixEq (a r : ℕ) : UPos a r ≃ BlockIx a r where
  toFun p := ⟨p.1, p.2.1, p.2.2⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem unipGL_ixEq {R : Type} [CommRing R] {a r : ℕ} (x : BlockIx a r → R) :
    unipGL (fun p => x (ixEq a r p)) = unip x := by
  refine Units.ext ?_
  change 1 + blockEntry (fun p => x (ixEq a r p)) = 1 + nilM x
  congr 1

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem cusp_of {E : Type} [Field E] [NumberField E] {a : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (hφ : AutomorphicForm.IsCuspidal φ) : GlobalTheory.CuspRep.IsCuspidal φ := by
  intro r h0 h1 i1 i2 μ 𝓕 hμ hF g
  obtain rfl : i1 = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ _ Pi.borelSpace).symm
  let β : (BlockIx a r → Ad E) ≃ₜ+ (UPos a r → Ad E) :=
    { toFun := fun x p => x (ixEq a r p)
      invFun := fun x p => x ((ixEq a r).symm p)
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => continuous_apply _
      continuous_invFun := continuous_pi fun p => continuous_apply _ }
  let e : unipLattice E a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => y ((ixEq a r).symm p), rfl⟩⟩
      invFun := fun x => ⟨β x, by
        obtain ⟨_, y, rfl⟩ := x
        exact ⟨fun p => y (ixEq a r p), rfl⟩⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsAddHaarMeasure := β.isAddHaarMeasure_map μ
  have h2 := setIntegral_haar hl g (hφ r h0 h1 g) (μ.map m) (D := m '' 𝓕)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply])
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  exact congrArg (fun u => φ (u * g)) (unipGL_ixEq x).symm

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.ConvolutionTheory.R2.Pp in
private theorem found_cusp {E : Type} [Field E] [NumberField E] {Φ : GL (Fin 2) (A E) → ℂ}
    (h0 : ∀ h, ∫ b in fundamentalSet E, Φ (gl (nU b) * h) ∂(adeleMeasure E) = 0) :
    AutomorphicForm.IsCuspidal Φ := by
  intro r hr hr2 g
  obtain rfl : r = 1 := by omega
  letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← h0 g, ← int_one (ι := UPos 2 1)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : gl (nU (x default)) = unipGL x := by
    refine Units.ext ?_
    change (nU (x default)).1 = unipMatrix x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nU, unipMatrix, blockEntry_apply]
    rfl
  simp only [this]

theorem UpperTheory.ConvolutionTheory.R2.G.cuspOf :
    ∀ (E : Type) [Field E] [NumberField E] (Φ : GL (Fin 2) (A E) → ℂ), (∀ γ h, Φ (ratGL E 2 γ * h) = Φ h) →
    (∀ h, ∫ b in fundamentalSet E, Φ (gl (nU b) * h) ∂(adeleMeasure E) = 0) → GlobalTheory.CuspRep.IsCuspidal Φ := by
  intro E _ _ Φ hl h0
  exact cusp_of hl (found_cusp h0)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem kappa_ne_zero {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F)
    {U : Set (G1 F)} (hU : IsOpen U) {k : G1 F} (hk : k ∈ KK F) (hkU : k ∈ U) : M.κ U ≠ 0 := by
  intro h0
  obtain ⟨hKs, hC⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt F
  have hmem : ∀ x ∈ KK F, ∀ y ∈ KK F, x * y⁻¹ ∈ KK F := by
    intro x hx y hy
    rw [hKs] at hx hy ⊢
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks F).mul_mem hx ((UpperTheory.ConvolutionTheory.R2.M.Ks F).inv_mem hy)
  have hnull : ∀ c ∈ KK F, M.κ ((fun x => c * x) ⁻¹' U) = 0 := by
    intro c hc
    have hm : Measurable (fun x : G1 F => c * x) := (continuous_const.mul continuous_id).measurable
    rw [← Measure.map_apply hm hU.measurableSet, M.κ_left c hc]
    exact h0
  obtain ⟨t, ht, hcov⟩ := hC.elim_nhds_subcover (fun x => (fun y => (k * x⁻¹) * y) ⁻¹' U) (by
    intro x hx
    refine ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds ?_
    simpa using hkU)
  have hK0 : M.κ (KK F) = 0 := by
    refine measure_mono_null hcov ?_
    exact (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => hnull _ (hmem k hk x (ht x hx))
  haveI := M.prob
  have hle : M.κ Set.univ ≤ M.κ (KK F) + M.κ (KK F)ᶜ := by
    rw [← Set.union_compl_self (KK F)]
    exact measure_union_le _ _
  rw [hK0, M.supp, measure_univ] at hle
  simp at hle

theorem UpperTheory.ConvolutionTheory.R2.G.aeZero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (u : IdeleGroup F × G1 F → ℂ), ContinuousOn u (Set.univ ×ˢ KK F) → (∀ᵐ p ∂M.ν, u p = 0) →
    ∀ a, ∀ k ∈ KK F, u (a, k) = 0 := by
  intro F _ _ _ M u hu h a k hk
  by_contra hne
  haveI := M.prob
  have hc : ContinuousWithinAt u (Set.univ ×ˢ KK F) (a, k) := hu (a, k) ⟨Set.mem_univ _, hk⟩
  have h1 : {p | u p ≠ 0} ∈ 𝓝[Set.univ ×ˢ KK F] (a, k) := hc.eventually_ne hne
  rw [nhdsWithin_prod_eq, Filter.mem_prod_iff] at h1
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := h1
  rw [nhdsWithin_univ, mem_nhds_iff] at ht₁
  obtain ⟨V, hVt, hVo, haV⟩ := ht₁
  obtain ⟨U, hUo, hkU, hUt⟩ := mem_nhdsWithin.1 ht₂
  have hnull : M.ν (V ×ˢ (U ∩ KK F)) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro p hp
    exact hsub ⟨hVt hp.1, hUt hp.2⟩
  have hprod : ideleMeasure F V * M.κ (U ∩ KK F) = 0 := by
    rw [← Measure.prod_prod]
    exact hnull
  have hV : ideleMeasure F V ≠ 0 := hVo.measure_ne_zero _ ⟨a, haV⟩
  have hU : M.κ (U ∩ KK F) ≠ 0 := by
    intro h0
    refine kappa_ne_zero M hUo hk hkU (measure_mono_null (t := (U ∩ KK F) ∪ (KK F)ᶜ) ?_ ?_)
    · intro x hx
      by_cases hxK : x ∈ KK F
      · exact Or.inl ⟨hx, hxK⟩
      · exact Or.inr hxK
    · exact measure_union_null h0 M.supp
  exact (mul_ne_zero hV hU) hprod
end
