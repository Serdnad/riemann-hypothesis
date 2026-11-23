module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle508
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle509
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW.KerCusp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_unip {r : ℕ} : Continuous (fun x : BlockIx a r → Ad E => (unip x : GA E a)) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

theorem measurable_integrand {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    {X : Type} [MeasurableSpace X] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : Measurable k)
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a)
    (hc : Continuous φ.1) (g : GA E a) :
    Measurable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) := by
  let Φ : invSet E a → (BlockIx a r → Ad E) → ℂ := fun y u => chart φ.1 (unip u * g) y.1
  have hΦ : Measurable (Function.uncurry Φ) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun u => ?_) (fun y => ?_)
    · exact ((φ.2 (unip u * g)).continuousOn).restrict
    · have e : Φ y = fun u => φ.1 (unip u * g * infGL E a y.2.unit) := by
        funext u; exact dif_pos y.2
      rw [e]
      exact (hc.comp ((continuous_unip.mul continuous_const).mul continuous_const)).measurable
  have hy : Measurable (fun x : X => (⟨toL (γ x).val, val_mem_invSet (γ x)⟩ : invSet E a)) :=
    Measurable.subtype_mk hγ
  have e : (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) =
      fun p => k p.2 * Function.uncurry Φ (⟨toL (γ p.2).val, val_mem_invSet (γ p.2)⟩, p.1) := by
    funext p
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, Φ, chart_val]
  rw [e]
  exact (hk.comp measurable_snd).mul (hΦ.comp ((hy.comp measurable_snd).prodMk measurable_fst))

end GlobalTheory.JSW.KerCusp

namespace GlobalTheory.JSW

theorem isCuspidal_kerOp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, IsBCC φ.1 →
      IsCuspidal (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν _ k γ hk φ hφ r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := hφ.bdd
  have hk0 : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
  have hm := KerCusp.measurable_integrand (r := r) hk.1 hk.2.1 φ hφ.cont g
  have hint : Integrable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) =>
      k x * φ.1 (unip u * g * infGL E a (γ x))) ((μ.restrict 𝓕).prod ν) := by
    refine Integrable.mono' ((integrable_const C).mul_prod hk0) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  change ∫ u in 𝓕, (∫ x, k x * φ.1 (unip u * g * infGL E a (γ x)) ∂ν) ∂μ = 0
  rw [integral_integral_swap hint]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (integral_zero X ℂ)
  rw [integral_const_mul]
  have e : ∀ u : BlockIx a r → Ad E, unip u * g * infGL E a (γ x) = unip u * (g * infGL E a (γ x)) :=
    fun u => mul_assoc _ _ _
  simp only [e]
  rw [hφ.cusp r h0 h1 μ 𝓕 hμ hF _, mul_zero]

end GlobalTheory.JSW
end
end

section

noncomputable section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_unip_adele {r : ℕ} : Continuous fun x : BlockIx a r → Ad E => (unip x : GA E a) := by
  have hn : Continuous fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

theorem isBCC_zero_and_add : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    IsBCC (0 : GA E a → ℂ) ∧
    ∀ (c : ℂ) (F G : GA E a → ℂ), IsBCC F → IsBCC G → IsBCC (c • F + G) := by
  intro E _ _ _ a
  refine ⟨⟨continuous_const, ⟨0, fun g => by simp⟩, ?_, fun _ _ => rfl⟩, ?_⟩
  · intro r _ _ _ _ μ 𝓕 _ _ g
    simp
  · intro c F G hF hG
    obtain ⟨CF, hCF⟩ := hF.bdd
    obtain ⟨CG, hCG⟩ := hG.bdd
    refine ⟨(hF.cont.const_smul c).add hG.cont, ⟨‖c‖ * CF + CG, fun g => ?_⟩, ?_, fun γ g => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hCG g))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hCF g) (norm_nonneg c)
    · intro r h0 h1 _ _ μ 𝓕 hμ hFd g
      haveI := hμ
      have hfin := covol_lt_top μ 𝓕 hFd
      have hint : ∀ H : GA E a → ℂ, IsBCC H → IntegrableOn (fun x => H (unip x * g)) 𝓕 μ := by
        intro H hH
        obtain ⟨C, hC⟩ := hH.bdd
        have hc : Continuous fun x : BlockIx a r → Ad E => H (unip x * g) :=
          hH.cont.comp (continuous_unip_adele.mul continuous_const)
        haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
        exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => hC _)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_add ((hint F hF).const_mul c) (hint G hG), integral_const_mul,
        hF.cusp r h0 h1 μ 𝓕 hμ hFd g, hG.cusp r h0 h1 μ 𝓕 hμ hFd g]
      simp
    · simp only [Pi.add_apply, Pi.smul_apply, hF.left, hG.left]

end GlobalTheory.JSW
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem colHT_isUnit_det {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ)
    (hu : ∀ i j, u i j ∈ (P.PD K).Fil (k i))
    (hspan : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i)
    (hli : LinearIndependent P.R.BdR u) : IsUnit (colHT J u k).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hc0
  set s : Fin m → Fin m → P.R.BdR := fun i j => ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j with hs
  have hs0 : ∀ i j, s i j ∈ (P.PD (botExt l)).Fil 0 := fun i j =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i j))
  choose γ hγ0 hγ using J.θ_onto
  set z : Fin m → P.R.BdR := fun j => ∑ i, γ (c i) * s i j with hz
  have hz0 : ∀ j, z j ∈ (P.PD (botExt l)).Fil 0 := fun j => by
    have := Submodule.sum_mem ((P.PD (botExt l)).Fil 0) (t := Finset.univ)
      (f := fun i => γ (c i) * s i j) fun i _ => by
        simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)
    exact this
  have hz1 : ∀ j, z j ∈ (P.PD K).Fil 1 := fun j => by
    rw [mem_iff K]
    refine (J.θ_ker _ (hz0 j)).1 ?_
    have h1 := congrFun hc j
    simp only [Matrix.mulVec, dotProduct, colHT, Matrix.of_apply, Pi.zero_apply] at h1
    rw [hz, GlobalTheory.DeRhamSymbolBasis.theta_sum J _ _ fun i => by
      simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [J.θ_mul _ (hγ0 (c i)) _ (hs0 i j), hγ, mul_comm]
  obtain ⟨f, hf, hfz⟩ := hspan 1 z hz1
  have hz' : z = ∑ i, (γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) • u i := by
    funext j
    simp only [hz, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hdiff := Fintype.linearIndependent_iff.1 hli
    (fun i => f i - γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hfz, ← hz', sub_self])
  funext i
  have hfi : f i = γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) := sub_eq_zero.1 (hdiff i)
  have hγi : γ (c i) = f i * ((tU P ^ (k i) : P.R.BdRˣ) : P.R.BdR) := by
    rw [hfi, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]
  have hmem : γ (c i) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ ((mem_iff K _ _).1 (hf i)) (zpow_mem J (k i))
    rw [sub_add_cancel] at this
    rwa [hγi]
  rw [Pi.zero_apply, ← hγ (c i)]
  exact (J.θ_ker _ (hγ0 (c i))).2 hmem

end GlobalTheory.HTBasis
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol GlobalTheory.DeRhamSymbolBasis

theorem colHT_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI J K LL m r' u k hu g hg
  ext j i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.map_apply, colHT, Matrix.of_apply]
  set M := (r' g : Matrix (Fin m) (Fin m) ↥LL.1) with hM
  set t : P.R.BdR := ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) with ht
  set q : ℚ_[l] := ((P.χQ (g : GQ l) ^ k i : ℚ_[l]ˣ) : ℚ_[l]) with hq
  have key : ∀ x, t * u i x ∈ (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i x))
  have hmem : ∀ x, algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x) ∈
      (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
    exact om_mul_mem _ (act_mem _ (key x))
  have h1 := congrFun (hg i) j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, embF_apply] at h1
  have h2 : t * u i j = ∑ x, algebraMap (Om l) P.R.BdR ((M j x : ↥LL.1) : Om l) *
      (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) := by
    conv_lhs => rw [← h1]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_left_comm, shift_act]
  have h3 : ∀ x, J.θ (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) =
      (q : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)) := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR,
      J.θ_mul _ (om_mem _) _ (act_mem _ (key x)), J.θ_Om, J.θ_act _ _ (key x),
      GlobalTheory.MemLoc.TiedTheta.actC_eq]
  have hunit : (q : ℂ_[l]) * ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = 1 := by
    have e : q * (((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
      rw [hq, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
    have e2 := congrArg (fun z : ℚ_[l] => (z : ℂ_[l])) e
    rw [map_mul, UniformSpace.Completion.coe_mul, map_one, UniformSpace.Completion.coe_one] at e2
    exact e2
  rw [h2, theta_comb J _ _ hmem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h3]
  linear_combination (-((((M j x : ↥LL.1) : Om l) : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)))) * hunit

end GlobalTheory.HTBasis
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.FourierCell

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors SchwartzMap

variable {E : Type} [Field E] [NumberField E]

theorem finId_val (u : (Af E)ˣ) :
    ((finId E u : (Ad E)ˣ) : Ad E) = ((1, (u : Af E)) : InfiniteAdeleRing E × Af E) := by
  change (1 - sFin E 1 + sFin E (u : Af E) : Ad E) = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp
  · change (1 : Af E) - 1 + (u : Af E) = u
    simp

theorem mem_one_iff (x : Af E) :
    x ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 E)⁰ E)ˣ) ↔ ∀ v, Valued.v (pLoc E v x) ≤ 1 := by
  simp only [mem_idealFiniteAdeles, Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  rfl

theorem val_zpow_unif {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (n : ℤ) :
    Valued.v (ϖ ^ n) = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, h, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  simp

theorem ofAdd_le_one_iff (n : ℤ) :
    ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 ↔ n ≤ 0 := by
  rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]

theorem exists_fourier_gauss_lattice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (y₀ : Fin (m + 1) → Ad E),
    (∀ w ∉ S, ∀ j, pLoc E w (pFin E (y₀ j)) ∈ w.adicCompletionIntegers E) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
      Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) ∧
      (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧
        (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) ∧
      0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y₀).re ∧
      ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
      ∀ a : HeightOneSpectrum (𝓞 E) →₀ ℤ, (∀ v ∈ S, a v = 0) →
      ∀ y : Fin (m + 1) → Ad E,
        (∀ w ∉ S, (∀ j, pLoc E w (pFin E (y j)) ∈ w.adicCompletionIntegers E) ∧
          ∃ j, Valued.v (pLoc E w (pFin E (y j))) = 1) →
        ((∀ w, 0 ≤ a w) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) =
          GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y) ∧
        ((∃ w, a w < 0) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = 0) := by
  intro E _ _ _ m S y₀ hy₀
  classical
  let φ : 𝓢(Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidean (E := Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E))
      (GroundTheory.Global.gaussianSchwartz _)
  have hφ : ∀ x, φ x = ((Real.exp (-Real.pi * ‖toEuclidean x‖ ^ 2) : ℝ) : ℂ) := fun x => by
    simp [φ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  let g : (Fin (m + 1) → Af E) → ℂ := finiteTensor fun j => cosetIndicator 1 (pFin E (y₀ j))
  have hg : g ∈ finiteSchwartzBruhatPi E :=
    finiteTensor_mem fun j => cosetIndicator_mem_finiteSchwartzBruhat _ _
  let G := schwartzBruhatTensorPi φ g
  have hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin (m + 1)) := schwartzBruhatTensorPi_mem φ hg
  have hG1 := adelicFourierPi_mem_schwartzBruhatPi hG
  have hG2 := adelicFourierPi_mem_schwartzBruhatPi hG1
  have hG3 := adelicFourierPi_mem_schwartzBruhatPi hG2
  have hFG : adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) = G := by
    rw [adelicFourierPi_adelicFourierPi hG2, adelicFourierPi_adelicFourierPi hG]
    funext x
    simp
  have hGv : ∀ y, G y = φ (infPartPi y) *
      if ∀ j v, Valued.v (pLoc E v (pFin E (y j)) - pLoc E v (pFin E (y₀ j))) ≤ 1 then 1 else 0 := by
    intro y
    simp only [G, g, schwartzBruhatTensorPi, finiteTensor, cosetIndicator_apply, Finset.prod_boole,
      Finset.mem_univ, true_implies, mem_one_iff, map_sub]
    rfl
  refine ⟨adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G)), hG3, ?_, ?_, ?_, ?_⟩
  · rw [hFG]; exact continuous_of_mem_schwartzBruhatPi hG
  · intro y
    rw [hFG, hGv, hφ]
    split_ifs
    · rw [mul_one]
      exact ⟨by rw [Complex.ofReal_re]; exact (Real.exp_pos _).le, Complex.ofReal_im _⟩
    · rw [mul_zero]
      exact ⟨le_refl _, rfl⟩
  · rw [hFG, hGv, hφ, if_pos (fun j v => by simp)]
    rw [mul_one, Complex.ofReal_re]
    exact Real.exp_pos _
  · intro ϖ hϖ a ha y hy
    have hFy : ∀ z, adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) z = G z :=
      fun z => by rw [hFG]
    have hinf : infPartPi (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = infPartPi y := by
      funext j
      simp only [infPartPi, finId_val]
      congr 1
      change (1 : InfiniteAdeleRing E) * (y j).1 = (y j).1
      exact one_mul _
    have hfin : ∀ j v, pLoc E v (pFin E (((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j)) =
        ((ϖ v : v.adicCompletion E) ^ a v) * pLoc E v (pFin E (y j)) := by
      intro j v
      rw [map_mul, map_mul, finId_val]
      change ((ϖ v ^ a v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * _ = _
      rw [Units.val_zpow_eq_zpow_val]
    have hint : ∀ w ∉ S, ∀ j, Valued.v (pLoc E w (pFin E (y₀ j))) ≤ 1 := fun w hw j => by
      simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hy₀ w hw j
    constructor
    · intro hpos
      rw [hFy, hFy, hGv, hGv, hinf]
      congr 1
      refine if_congr ?_ rfl rfl
      refine forall_congr' fun j => forall_congr' fun v => ?_
      rw [hfin]
      by_cases hv : v ∈ S
      · rw [ha v hv, zpow_zero, one_mul]
      · have h1 := hint v hv j
        have h2 : Valued.v (pLoc E v (pFin E (y j))) ≤ 1 := by
          simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using (hy v hv).1 j
        have h3 : Valued.v ((ϖ v : v.adicCompletion E) ^ a v) ≤ 1 := by
          rw [val_zpow_unif (hϖ v), ofAdd_le_one_iff]
          linarith [hpos v]
        have key : ∀ t, Valued.v t ≤ 1 → Valued.v (t - pLoc E v (pFin E (y₀ j))) ≤ 1 :=
          fun t ht => (Valuation.map_sub _ _ _).trans (max_le ht h1)
        exact iff_of_true (key _ (by rw [map_mul]; exact mul_le_one' h3 h2)) (key _ h2)
    · rintro ⟨w, hw⟩
      rw [hFy, hGv, if_neg, mul_zero]
      intro hP
      have hwS : w ∉ S := fun h => by rw [ha w h] at hw; exact lt_irrefl _ hw
      obtain ⟨j, hj⟩ := (hy w hwS).2
      have h1 := hint w hwS j
      have h := hP j w
      rw [hfin] at h
      have ht : Valued.v ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j))) ≤ 1 := by
        have h4 := Valuation.map_add Valued.v
          ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j)) - pLoc E w (pFin E (y₀ j)))
          (pLoc E w (pFin E (y₀ j)))
        rw [sub_add_cancel] at h4
        exact h4.trans (max_le h h1)
      rw [map_mul, hj, mul_one, val_zpow_unif (hϖ w), ofAdd_le_one_iff] at ht
      omega

end GlobalTheory.FourierCell
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

theorem _root_.GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n), u ∈ GlobalTheory.CellDec.NA E n →
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  first | exact @GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | exact GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | (intros; apply GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.finiteDimensional_definiteUnitary_levelForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y) → ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}) := by
  first | exact @GlobalTheory.UnitaryBC.finiteDimensional_levelForms | exact GlobalTheory.UnitaryBC.finiteDimensional_levelForms | (intros; apply GlobalTheory.UnitaryBC.finiteDimensional_levelForms <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.sphericalSegmentRep_length_one_unramified : LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → IsSpherical y.rep → Δ.len = 1 ∧ Δ.first.IsUnramChar := by
  first | exact @GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | exact GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | (intros; apply GlobalTheory.SphSeg.len_eq_one_and_isUnramChar <;> assumption)
end
