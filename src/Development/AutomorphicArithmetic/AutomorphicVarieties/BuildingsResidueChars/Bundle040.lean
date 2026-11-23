module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle004
import GroundTheory.GlobalFields.Adele.Topology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped NumberField.AdeleRing

private theorem nn_zero {K : Type} [Field K] [NumberField K] : (nn (K := K) 0) = 1 := unipOne_zero 2

private theorem lv_left {K : Type} [Field K] [NumberField K] {F : G1 K (2 + 2) → ℂ}
    (hP : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.PFun F) (m₂ : G1 K 2) (s : ℝ)
    (γ : G1 K 2) (hγ : γ ∈ Gam K 2) (m : G1 K 2) (g : G1 K (2 + 2)) :
    F (lv m₂ (γ * m) s * g) = F (lv m₂ m s * g) := by
  have hmem : lv 1 γ 0 ∈ PK K := (pkLaws.2.1 _).2 ⟨0, 1, ⟨γ, hγ⟩, by
    have h0 : unipOne (K := K) (n := 2 + 2) 2
        ((0 : unipLattice K (2 + 2) 2) : UPos (2 + 2) 2 → 𝔸[K]) = 1 := nn_zero
    rw [h0, one_mul]
    rfl⟩
  have e : lv m₂ (γ * m) s = lv 1 γ 0 * lv m₂ m s := by
    rw [blkLaws.2.1, one_mul, zero_add]
  rw [e, mul_assoc, hP.rat _ hmem]

private theorem rep_ae {K : Type} [Field K] [NumberField K] {μ : Measure (G1 K 2)} [μ.IsHaarMeasure] {v : L2 μ}
    {φ : G1 K 2 → ℂ} (hc : Continuous φ) (hi : ∀ γ ∈ Gam K 2, ∀ y, φ (γ * y) = φ y) (hr : Reps μ v φ) :
    (v : RightCosetSpace (Gam K 2) → ℂ) =ᵐ[quotientMeasure (Gam K 2) μ] fun y => φ (Quotient.out y) := by
  set_option synthInstance.maxHeartbeats 200000 in
    let q : RightCosetSpace (Gam K 2) → ℂ := Quotient.lift φ (fun a b hab => by
      obtain ⟨γ, rfl⟩ := hab
      exact hi γ γ.2 b)
    have hq : Continuous q := (isOpenQuotientMap_mk (Gam K 2)).isQuotientMap.continuous_iff.2 hc
    have hm : ∀ᵐ x ∂(Measure.map (mk (Gam K 2)) (μ.restrict (fundamentalDomain (Gam K 2)))),
        (v : RightCosetSpace (Gam K 2) → ℂ) x = q x := by
      refine (ae_map_iff (measurable_mk (Gam K 2)).aemeasurable
        (measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable hq.measurable)).2 ?_
      exact ae_restrict_of_ae (hr.mono fun y hy => by simpa [q, RightCosetSpace.mk] using hy)
    have hm' : (v : RightCosetSpace (Gam K 2) → ℂ) =ᵐ[quotientMeasure (Gam K 2) μ] q := by
      rwa [map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K 2) μ)] at hm
    refine hm'.trans (Eventually.of_forall fun y => ?_)
    change q y = φ (Quotient.out y)
    conv_lhs => rw [← Quotient.out_eq y]
    rfl

private theorem long_swap {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ) (m m₂ : G1 K 2) (s : ℝ)
    (k : G1 K (2 + 2)) (hF : Continuous F) :
    (∫ X, F (w0 K * nn X * (lv m m₂ s * k)) ∂unipMeasure K (2 + 2) 2) =
      (Real.exp (4 * s) : ℝ) • ∫ X, F (lv m₂ m (-s) * (w0 K * nn X * k)) ∂unipMeasure K (2 + 2) 2 := by
  obtain ⟨e, he, hm⟩ := adMeas m m₂ s
  have h1 : ∀ X, F (w0 K * nn X * (lv m m₂ s * k)) = F (lv m₂ m (-s) * (w0 K * nn (e X) * k)) := fun X => by
    congr 1
    calc w0 K * nn X * (lv m m₂ s * k) = w0 K * (nn X * lv m m₂ s) * k := by simp only [mul_assoc]
      _ = w0 K * (lv m m₂ s * nn (e X)) * k := by rw [he]
      _ = (w0 K * lv m m₂ s) * nn (e X) * k := by simp only [mul_assoc]
      _ = lv m₂ m (-s) * w0 K * nn (e X) * k := by rw [blkLaws.2.2.2.2.2.2.2.2.2.1]
      _ = _ := by simp only [mul_assoc]
  simp_rw [h1]
  have hme : MeasurableEmbedding (e : (UPos (2 + 2) 2 → _) → _) := e.toHomeomorph.measurableEmbedding
  rw [← hme.integral_map (g := fun X => F (lv m₂ m (-s) * (w0 K * nn X * k))), hm, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

private theorem long_cont {K : Type} [Field K] [NumberField K] {F : G1 K (2 + 2) → ℂ} (hF : Continuous F) (m₂ : G1 K 2) (s : ℝ)
    (k : G1 K (2 + 2)) :
    Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => F (lv m₂ p.1 (-s) * (w0 K * nn p.2 * k)) := by
  have hl : Continuous fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2 := by
    obtain ⟨-, -, -, h, -⟩ := blkLaws (K := K)
    exact h
  have h0 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => ((m₂, p.1, -s) : G1 K 2 × G1 K 2 × ℝ) :=
    continuous_const.prodMk (continuous_fst.prodMk continuous_const)
  have h1 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => lv m₂ p.1 (-s) := by
    have h := Continuous.comp hl h0
    simpa only [Function.comp_def] using h
  have h2 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => nn p.2 :=
    (continuous_unipOne (K := K) (n := 2 + 2) 2).comp continuous_snd
  exact hF.comp (h1.mul ((continuous_const.mul h2).mul continuous_const))

private theorem swap_zero {Y X : Type} [MeasurableSpace Y] [MeasurableSpace X] (Q : Measure Y) (ν : Measure X)
    [IsFiniteMeasure Q] [IsFiniteMeasure ν] (f : Y → X → ℂ) (hI : Integrable (Function.uncurry f) (Q.prod ν))
    (hZ : ∀ x, ∫ y, f y x ∂Q = 0) : ∫ y, ∫ x, f y x ∂ν ∂Q = 0 := by
  rw [integral_integral_swap hI]
  simp only [hZ, integral_zero]

theorem UpperTheory.constantTerm_pairing_vanishes_of_orthogonal :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ ρ : Submodule ℂ (L2 μ₂)) (F : G1 K (2 + 2) → ℂ) (h : G1 K 2 → ℂ),
          UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.PFun F → InBand F → Slices τ₁ τ₂ F → τ₂ ⟂ ρ → Continuous h → (∀ γ ∈ Gam K 2, ∀ m, h (γ * m) = h m) → (∃ v ∈ ρ, Reps μ₂ v h) →
          ∀ (m₂ : G1 K 2) (s : ℝ), ∀ k ∈ KG K (2 + 2),
            Integrable (fun y : RightCosetSpace (Gam K 2) => (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y))) (quotientMeasure (Gam K 2) μ₂) ∧
            ∫ y : RightCosetSpace (Gam K 2), (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y)) ∂quotientMeasure (Gam K 2) μ₂ = 0 := by
  set_option synthInstance.maxHeartbeats 200000 in
   intro K _ _ μ₂ _ τ₁ τ₂ ρ F h hP hB hS hort hc hi hv m₂ s k hk
   obtain ⟨v, hvρ, hvr⟩ := hv
   have hQf := isFiniteMeasure_quotientMeasure (K := K) (n := 2) μ₂
   obtain ⟨R, hR⟩ := hB
   obtain ⟨B, hBd⟩ := hP.bdd
   obtain ⟨C, hCc, hC⟩ := (longCell (K := K)).2 (R - s)
   haveI : IsFiniteMeasure ((unipMeasure K (2 + 2) 2).restrict C) := ⟨by simpa using hCc.measure_lt_top⟩
   let Φ : G1 K 2 → (UPos (2 + 2) 2 → 𝔸[K]) → ℂ := fun m X => F (lv m₂ m (-s) * (w0 K * nn X * k))
   let P : RightCosetSpace (Gam K 2) → (UPos (2 + 2) 2 → 𝔸[K]) → ℂ := fun y X => Φ (Quotient.out y) X
   let H : RightCosetSpace (Gam K 2) → ℂ := fun y => h (Quotient.out y)
   have hΦi : ∀ X, ∀ γ ∈ Gam K 2, ∀ m, Φ (γ * m) X = Φ m X := fun X γ hγ m => lv_left hP m₂ (-s) γ hγ m _
   have hΦc : Continuous (Function.uncurry Φ) := long_cont hP.cont m₂ s k
   have hPc : Continuous (Function.uncurry P) := by
     have hq := (isOpenQuotientMap_mk (Gam K 2)).prodMap (IsOpenQuotientMap.id (X := UPos (2 + 2) 2 → 𝔸[K]))
     rw [hq.isQuotientMap.continuous_iff]
     refine hΦc.congr fun p => ?_
     change Φ p.1 p.2 = Φ (Quotient.out (mk (Gam K 2) p.1)) p.2
     have he : mk (Gam K 2) (Quotient.out (mk (Gam K 2) p.1)) = mk (Gam K 2) p.1 := Quotient.out_eq _
     obtain ⟨γ, hγ⟩ := Quotient.exact he
     rw [← hγ]
     exact (hΦi p.2 γ γ.2 p.1).symm
   have hPb : ∀ y X, ‖P y X‖ ≤ B := fun y X => hBd _
   have hsupp : ∀ m X, X ∉ C → Φ m X = 0 := fun m X hX => by
     by_contra hne
     have h1 := hR _ hne
     have h2 := (hpSpec (K := K)).1 0 m₂ m (-s) (w0 K * nn X * k)
     rw [nn_zero, one_mul] at h2
     rw [h2, abs_le] at h1
     exact hX (hC X k hk (by linarith [h1.1]))
   have hHr := rep_ae hc hi hvr
   have hHm : MemLp H 2 (quotientMeasure (Gam K 2) μ₂) := (Lp.memLp v).ae_eq hHr
   have hHi : Integrable H (quotientMeasure (Gam K 2) μ₂) := hHm.integrable one_le_two
   have hHs : AEStronglyMeasurable H (quotientMeasure (Gam K 2) μ₂) := hHi.1
   have hI : Integrable (Function.uncurry fun y X => P y X * starRingEnd ℂ (H y))
       ((quotientMeasure (Gam K 2) μ₂).prod ((unipMeasure K (2 + 2) 2).restrict C)) := by
     have hm : AEStronglyMeasurable (fun p : RightCosetSpace (Gam K 2) × (UPos (2 + 2) 2 → 𝔸[K]) => starRingEnd ℂ (H p.1))
         ((quotientMeasure (Gam K 2) μ₂).prod ((unipMeasure K (2 + 2) 2).restrict C)) :=
       (continuous_star.comp_aestronglyMeasurable hHs).comp_fst
     refine Integrable.mono' (hHi.norm.mul_prod (integrable_const B))
       (hPc.aestronglyMeasurable.mul hm) (Eventually.of_forall fun p => ?_)
     show ‖P p.1 p.2 * starRingEnd ℂ (H p.1)‖ ≤ ‖H p.1‖ * B
     rw [norm_mul, RCLike.norm_conj, mul_comm]
     exact mul_le_mul_of_nonneg_left (hPb _ _) (norm_nonneg _)
   have hT : ∀ y : RightCosetSpace (Gam K 2),
       (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y)) =
         (Real.exp (4 * s) : ℝ) • ∫ X in C, P y X * starRingEnd ℂ (H y) ∂unipMeasure K (2 + 2) 2 := fun y => by
     rw [long_swap F _ m₂ s k hP.cont, smul_mul_assoc, integral_mul_const]
     congr 2
     exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun X hX => hsupp _ X hX).symm
   have hZ : ∀ X, ∫ y, P y X * starRingEnd ℂ (H y) ∂quotientMeasure (Gam K 2) μ₂ = 0 := fun X => by
     obtain ⟨u, huτ, hur⟩ := (hS (lv 1 1 (-s) * (w0 K * nn X * k))).2 m₂
     have hur' : Reps μ₂ u (fun m => Φ m X) := by
       have e : (fun m => F (lv m₂ m 0 * (lv 1 1 (-s) * (w0 K * nn X * k)))) = fun m => Φ m X := by
         funext m
         show _ = F (lv m₂ m (-s) * (w0 K * nn X * k))
         rw [← mul_assoc, blkLaws.2.1, mul_one, mul_one, zero_add]
       rwa [e] at hur
     have h1 : (u : RightCosetSpace (Gam K 2) → ℂ) =ᵐ[quotientMeasure (Gam K 2) μ₂] fun y => P y X :=
       rep_ae (hΦc.comp (continuous_id.prodMk continuous_const)) (hΦi X) hur'
     have h3 : inner ℂ v u = 0 := inner_eq_zero_symm.1 (Submodule.isOrtho_iff_inner_eq.1 hort u huτ v hvρ)
     rw [L2.inner_def] at h3
     rw [← h3]
     refine integral_congr_ae ?_
     filter_upwards [h1, hHr] with y a b
     rw [a, b, RCLike.inner_apply]
   have hI2 : Integrable (fun y => ∫ X in C, P y X * starRingEnd ℂ (H y) ∂unipMeasure K (2 + 2) 2)
       (quotientMeasure (Gam K 2) μ₂) := hI.integral_prod_left
   refine ⟨?_, ?_⟩
   · simp_rw [hT]
     exact hI2.smul (Real.exp (4 * s))
   · simp_rw [hT]
     rw [integral_smul, @swap_zero _ _ _ _ _ _ hQf _ _ hI hZ, smul_zero]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

section Coord

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V]
    (ρ : Representation Qp G V) {d : ℕ} (e : Basis (Fin d) Qp V)

private theorem coord_sum (c : Fin d → BdR) (i : Fin d) :
    (TensorProduct.lid Qp BdR) (LinearMap.rTensor BdR (e.coord i) (∑ j, e j ⊗ₜ[Qp] c j)) = c i := by

  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply, Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj]
  · simp

private theorem sum_mem_fil_iff (a : ℤ) (c : Fin d → BdR) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ FilV PD (LL := Qp) (V := V) a ↔ ∀ i, c i ∈ PD.Fil a := by
  constructor
  · rintro ⟨z, hz⟩ i
    rw [← coord_sum e c i, ← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v x =>
      have := ((PD.Fil a).restrictScalars Qp).smul_mem (e.coord i v) x.2
      simpa using this
    | add x y hx hy =>
      simp only [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · intro h
    exact Submodule.sum_mem _ fun j _ => ⟨e j ⊗ₜ ⟨c j, h j⟩, rfl⟩

private theorem sum_mem_DdR (c : Fin d → BdR)
    (h : ∀ g, ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)).mulVec (fun j => PD.actdR g (c j)) = c) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro g
  conv_rhs => rw [← h g]

  simp only [map_sum, Matrix.mulVec, dotProduct, tmul_sum, Matrix.map_apply, LinearMap.toMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ρ g (e j) ⊗ₜ[Qp] PD.actdR g (c j) = _
  conv_lhs => rw [← e.sum_repr (ρ g (e j))]
  rw [sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_tmul, Algebra.smul_def]

private theorem core
    (hinv : ∀ a b, b ∈ PD.Fil a → b ∉ PD.Fil (a + 1) → ∃ β ∈ PD.Fil (-a), β * b - 1 ∈ PD.Fil 1)
    (hT : ∀ n x, x ∈ PD.Fil n → (∀ g, PD.actdR g x - x ∈ PD.Fil (n + 1)) →
      ∃ κ ∈ PD.Fil 0, (∀ g, PD.actdR g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ x - κ ∈ PD.Fil (n + 1))
    (w : ℤ) (h1 : DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) (w + 1) = ⊥)
    (N N' : Matrix (Fin d) (Fin d) BdR) (hN : N * N' = 1)
    (hg : ∀ g, (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR) * N.map (PD.actdR g) = N) :
    ∀ i j, N' i j ∈ PD.Fil (-w) := by
  let A : G → Matrix (Fin d) (Fin d) BdR := fun g => (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)
  have hA : ∀ g i j, A g i j ∈ PD.Fil 0 := fun g i j => by
    change algebraMap Qp BdR _ ∈ _
    rw [IsScalarTower.algebraMap_apply Qp K BdR, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ PD.one_mem
  have hcol : ∀ j g, (A g).mulVec (fun i => PD.actdR g (N i j)) = fun i => N i j := fun j g => by
    funext i
    exact congrFun (congrFun (hg g) i) j
  have hN' : N' * N = 1 := mul_eq_one_comm.1 hN
  have hA' : ∀ g, N' * A g = N'.map (PD.actdR g) := fun g => by
    have h2 : N.map (PD.actdR g) * N'.map (PD.actdR g) = 1 := by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) BdR => X.map (PD.actdR g : BdR →+* BdR)) hN
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    calc N' * A g = N' * A g * (N.map (PD.actdR g) * N'.map (PD.actdR g)) := by rw [h2, mul_one]
      _ = N' * (A g * N.map (PD.actdR g)) * N'.map (PD.actdR g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg g, hN', one_mul]
  intro i j
  have hFa : Antitone fun a => (PD.Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => PD.Fil_anti a
  let R : G → (Fin d → BdR) →+ (Fin d → BdR) := fun g =>
    { toFun := fun c => (A g).mulVec (fun j => PD.actdR g (c j))
      map_zero' := by simp [← Pi.zero_def]
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]
        congr 1
        funext j
        simp }
  let FM : ℤ → AddSubgroup (Fin d → BdR) := fun a => AddSubgroup.pi Set.univ fun _ => (PD.Fil a).toAddSubgroup
  have hFM : ∀ a c, c ∈ FM a ↔ ∀ i, c i ∈ PD.Fil a := fun a c => by
    simp [FM, AddSubgroup.mem_pi]
  obtain ⟨m, k, b, c, h, hs⟩ := GlobalTheory.DRFil.filtered (G := G) (fun g => (PD.actdR g : BdR →+* BdR)) R
    (fun a => (PD.Fil a).toAddSubgroup) FM
    (fun g b x => by
      change (A g).mulVec _ = _ • (A g).mulVec _
      rw [← Matrix.mulVec_smul]
      congr 1
      funext j
      simp)
    PD.Fil_mul
    (fun a c x z hx hz => (hFM _ _).2 fun i => PD.Fil_mul _ _ _ _ hx ((hFM _ _).1 hz i))
    PD.Fil_G
    (fun g a z hz => (hFM _ _).2 fun i => by
      change ∑ j, A g i j * PD.actdR g (z j) ∈ _
      refine Submodule.sum_mem _ fun j _ => ?_
      have := PD.Fil_mul _ _ _ _ (hA g i j) (PD.Fil_G g _ _ ((hFM _ _).1 hz j))
      rwa [zero_add] at this)
    hinv hT hFa (fun a a' h z hz => (hFM _ _).2 fun i => hFa h ((hFM _ _).1 hz i)) PD.Fil_exh
    (fun x => by
      choose r hr using fun i => PD.Fil_exh (x i)
      obtain ⟨a, ha⟩ := (Set.finite_range r).bddBelow
      exact ⟨a, (hFM _ _).2 fun i => hFa (ha ⟨i, rfl⟩) (hr i)⟩)
    0 (fun i => (1 : Matrix (Fin d) (Fin d) BdR) i j)
    ((hFM _ _).2 fun i => by
      rw [Matrix.one_apply]
      split_ifs
      exacts [PD.one_mem, Submodule.zero_mem _])
    d (fun i => N' i j) (fun j i => N i j) (fun j g => hcol j g)
    (by
      funext i
      rw [← hN, Matrix.mul_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _)
  have h3 : N' i j = ∑ n, b n * N'.mulVec (c n) i := by
    have h4 := congrFun (congrArg N'.mulVec hs) i
    rw [Matrix.mulVec_sum, Finset.sum_apply] at h4
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h4
    rw [← h4]
    exact (congrFun (congrFun (mul_one N') i) j).symm
  rw [h3]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨hc, hk, hb⟩ := h n
  by_cases hk1 : w + 1 ≤ k n
  · have h5 : ∑ j, e j ⊗ₜ[Qp] c n j ∈ DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) (w + 1) :=
      ⟨sum_mem_DdR PD ρ e _ hc, (sum_mem_fil_iff PD e (w + 1) _).2 fun i => hFa hk1 ((hFM _ _).1 hk i)⟩
    rw [h1, Submodule.mem_bot] at h5
    have h6 : c n = 0 := funext fun i => by
      rw [← coord_sum e (c n) i, h5]
      simp
    rw [h6]
    simp
  · have h5 : b n ∈ PD.Fil (-w) := hFa (show -w ≤ 0 - k n by omega) hb
    obtain ⟨κ, hκ⟩ := PD.invdR (N'.mulVec (c n) i) fun g => by
      have h6 : (A g).mulVec (fun j => PD.actdR g (c n j)) = c n := hc g
      conv_rhs => rw [← h6, Matrix.mulVec_mulVec, hA' g]
      simp [Matrix.mulVec, dotProduct]
    have h6 : N'.mulVec (c n) i ∈ PD.Fil 0 := by
      rw [← hκ, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ PD.one_mem
    simpa using PD.Fil_mul _ _ _ _ h5 h6

end Coord

theorem UpperTheory.de_rham_inf_filtration :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V) (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → ∀ b : ℤ, DdR ((PP l).PD K) ρ ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) (b + 1) = ⊥ → ∀ i j, (PP l).ιB (M' i j) ∈ ((PP l).PD (botExt l)).Fil (-b) := by
  intro l _ K V _ _ _ ρ d e M M' hM hg b h1
  obtain ⟨T⟩ := tiedP l
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T
  have key := core ((PP l).PD K) ρ e (GlobalTheory.DRFil.graded_inv Θ K) (GlobalTheory.DRFil.graded_invariants T Θ K) b h1
    (M.map (PP l).ιB) (M'.map (PP l).ιB)
    (by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) (Bcr l) => X.map ((PP l).ιB : Bcr l →+* Bdr l)) hM
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this)
    (fun g => by
      ext i j
      have := congrArg (PP l).ιB (congrFun (congrFun (hg g) i) j)

      rw [Matrix.map_apply, ← this, Matrix.mul_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Matrix.map_apply, map_mul, AlgHom.commutes]
      rw [← (PP l).PD_actB K g, ← (PP l).PD_ι K, ← (PP l).PD_ι K, ((PP l).PD K).ι_comm])
  exact fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (key i j)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

theorem UpperTheory.exists_crystalline_unit_frobenius_eigen :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℤ), ∃ u : (Bcr l)ˣ, (PP l).ιB (u : Bcr l) ∈ ((PP l).PD (botExt l)).Fil a ∧ (PP l).φB (u : Bcr l) = algebraMap ℚ_[l] (Bcr l) ((l : ℚ_[l]) ^ a) * (u : Bcr l) := by
  intro l _ a
  obtain ⟨T⟩ := tiedP l
  obtain ⟨t, ht⟩ := ((PP l).PD (botExt l)).t_unit
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine ⟨t ^ a, ?_, ?_⟩
  · have h := GlobalTheory.DRFil.tdR_zpow_mem T (botExt l) a
    have e : GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR (PP l) (botExt l) =
        Units.map ((PP l).ιB : Bcr l →* (PP l).R.BdR) t := by
      ext
      change ((PP l).PD (botExt l)).ι ((PP l).PD (botExt l)).t = (PP l).ιB (t : Bcr l)
      rw [(PP l).PD_ι, ht]
    rw [e, ← map_zpow] at h
    exact h
  · have h1 : (PP l).φB (t : Bcr l) = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * (t : Bcr l) := by
      have := ((PP l).PD (botExt l)).t_φ
      rw [(PP l).PD_φ, (PP l).PD_p, Algebra.smul_def, ← ht] at this
      exact this
    have e : Units.map ((PP l).φB : Bcr l →* Bcr l) t =
        Units.map (algebraMap ℚ_[l] (Bcr l) : ℚ_[l] →* Bcr l) (Units.mk0 _ hl) * t := Units.ext h1
    have e2 := congrArg (fun x : (Bcr l)ˣ => ((x ^ a : (Bcr l)ˣ) : Bcr l)) e
    simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0] at e2
    exact e2
end
