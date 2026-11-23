module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle304
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle245
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PlaneQ

section Complex

end Complex

section Adelic

open scoped Classical
open GlobalTheory.RealLift.KLineProof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rho [IsTotallyReal F] (w : InfinitePlace F) : mixedEmbedding.mixedSpace F →ₐ[ℝ] ℝ :=
  (Pi.evalAlgHom ℝ (fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) ⟨w, IsTotallyReal.isReal w⟩).comp (AlgHom.fst ℝ _ _)

theorem trace_rho [IsTotallyReal F] (v : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) v = ∑ w, rho w v := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}),
    Finset.sum_empty, add_zero]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w) _ _ fun w => ?_
  rw [Algebra.trace_self_apply]
  rfl

theorem rho_evI [IsTotallyReal F] (w : InfinitePlace F) (a : AF F) :
    ((rho w (evI F a) : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
  rfl

theorem piInf_algebraMap [IsTotallyReal F] {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = ((rho w (evI F a) : ℝ) : ℂ) := by
  rw [rho_evI]
  change piInf τ (a ⊗ₜ[F] (1 : E)) = _
  rw [piInf_tmul, map_one, mul_one]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  change piInf τ ((1 : AF F) ⊗ₜ[F] e) = _
  rw [piInf_tmul, map_one, map_one, one_mul]

theorem rho_trace [IsTotallyReal F] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : AE F E) : rho w (evI F (Algebra.trace (AF F) (AE F E) z)) = 2 * (piInf τ z).re := by
  have h1 : z + cA σ z = algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) :=
    GlobalTheory.GaussMean.OneVec.add_sigR (AF F) hCM z
  have h2 := congrArg (fun y => (piInf τ y).re) h1
  simp only [map_add (f := _), piInf_cA hCM, piInf_algebraMap, Complex.ofReal_re, Complex.add_re] at h2
  rw [← h2]
  simp [two_mul]

end Adelic

end GlobalTheory.ThK.EvAt0.PlaneQ
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LatPtDecomp

theorem exists_zsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (w : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  exact _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem L hL w

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_mem (v : Pl (F := F)) (t : Fv F v) {k : F} (hk : k ≠ 0) :
    ∃ s : F, (algebraMap F (Fv F v) k)⁻¹ * (t - algebraMap F (Fv F v) s) ∈ v.adicCompletionIntegers F := by
  have hk' : algebraMap F (Fv F v) k ≠ 0 := (map_ne_zero _).2 hk
  have hkv : Valued.v (algebraMap F (Fv F v) k) ≠ 0 := (Valuation.ne_zero_iff _).2 hk'
  have hd : DenseRange (algebraMap F (v.adicCompletion F)) := HeightOneSpectrum.denseRange_algebraMap (K := F) v
  have hN : {y : v.adicCompletion F | Valued.v (t - y) < Valued.v (algebraMap F (Fv F v) k)} ∈ nhds t := by
    have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict (algebraMap F (Fv F v) k))).preimage
      (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => t - y)
    simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (t - t) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hkv
  obtain ⟨s, hs⟩ := hd.mem_nhds hN
  refine ⟨s, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
  have hs' : Valued.v (t - algebraMap F (Fv F v) s) < Valued.v (algebraMap F (Fv F v) k) := hs
  rw [inv_mul_le_iff₀ (zero_lt_iff.2 hkv), mul_one]
  exact hs'.le

theorem incM_single {n d : ℕ} (i : Fin n) (j : Fin d) (y : E) :
    incM F (Matrix.single i j y) = Matrix.single i j ((1 : AF F) ⊗ₜ[F] y) := by
  ext a b
  simp only [incM, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [inclR]

theorem single_sub {A : Type} [AddGroup A] {n d : ℕ} (i : Fin n) (j : Fin d) (a b : A) :
    Matrix.single i j a - Matrix.single i j b = Matrix.single i j (a - b) := by
  ext k l; simp only [Matrix.sub_apply, Matrix.single_apply]; split_ifs <;> simp

theorem atPlace_one_smul_tmul (v : Pl (F := F)) (a : AF F) (x : E) :
    GlobalTheory.EmbChart.atPlace v 1 • (a ⊗ₜ[F] x) = GlobalTheory.EmbChart.atPlace v (evFin F v a) ⊗ₜ[F] x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem core {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsFullLattice E) (hY : Y.L.IsFullLattice E) (v : Pl (F := F))
    (i : Fin n) (j : Fin d) (t : Fv F v) (x : E) :
    ∃ X₀ : Matrix (Fin n) (Fin d) E,
      Matrix.single i j (GlobalTheory.EmbChart.atPlace v t ⊗ₜ[F] x) - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  obtain ⟨N, hN, hNx⟩ := exists_zsmul_mem X.L hX (Pi.single i x)
  obtain ⟨N', hN', hNy⟩ := exists_zsmul_mem Y.L hY (Pi.single j 1)
  have hK : ((N * N' : ℤ) : F) ≠ 0 := Int.cast_ne_zero.2 (mul_ne_zero hN hN')
  obtain ⟨s, hs⟩ := exists_sub_mem v t hK
  set r := (algebraMap F (Fv F v) ((N * N' : ℤ) : F))⁻¹ * (t - algebraMap F (Fv F v) s) with hr
  refine ⟨Matrix.single i j (algebraMap F E s * x), ?_⟩
  refine AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v r, (fun u hu => by
    rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]), ?_, _, hNx, _, hNy, ?_⟩
  · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact hs
  · have hv : Matrix.vecMulVec (N • Pi.single i x) (N' • Pi.single j (1 : E)) =
        Matrix.single i j (((N * N' : ℤ) : F) • x) := by
      ext a b
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.single_apply, Matrix.single_apply]
      by_cases h1 : a = i <;> by_cases h2 : b = j
      · subst h1 h2
        simp only [if_true, and_self, smul_eq_mul, mul_one]
        rw [Algebra.smul_def (A := E) ((N * N' : ℤ) : F), map_intCast]
        simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul, mul_one]; push_cast; ring
      all_goals simp [h1, h2, eq_comm (a := i), eq_comm (a := j)]
    have hev : ∀ c : F, evFin F v (c • (1 : AF F)) = algebraMap F (Fv F v) c := fun c => by
      rw [map_smul, map_one, Algebra.algebraMap_eq_smul_one]
    have hK' : algebraMap F (Fv F v) ((N * N' : ℤ) : F) ≠ 0 := (map_ne_zero _).2 hK
    rw [hv, incM_single, incM_single, Matrix.smul_single, Matrix.smul_single, single_sub]
    congr 1
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, atPlace_one_smul_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, ← TensorProduct.sub_tmul, ← map_sub,
      hev, hev, hr]
    congr 2
    field_simp

theorem decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → Y.L.IsFullLattice E → ∀ (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (AE F E)),
    At (evFin F v) z → ∃ X₀ : Matrix (Fin n) (Fin d) E, z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  intro F E _ _ _ _ _ n d X Y hX hY v z hz
  have hz' : z = GlobalTheory.EmbChart.atPlace v 1 • z := by
    have h := hz (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h
  let P : Matrix (Fin n) (Fin d) (AE F E) → Prop := fun w =>
    ∃ X₀ : Matrix (Fin n) (Fin d) E, GlobalTheory.EmbChart.atPlace v 1 • w - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v
  have P0 : P 0 := ⟨0, by simp [incM]⟩
  have Padd : ∀ w w', P w → P w' → P (w + w') := by
    rintro w w' ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B, ?_⟩
    have : GlobalTheory.EmbChart.atPlace v 1 • (w + w') - GlobalTheory.EmbChart.atPlace v 1 • incM F (A + B) =
        (GlobalTheory.EmbChart.atPlace v 1 • w - GlobalTheory.EmbChart.atPlace v 1 • incM F A) +
        (GlobalTheory.EmbChart.atPlace v 1 • w' - GlobalTheory.EmbChart.atPlace v 1 • incM F B) := by
      have hI : incM F (A + B) = incM F A + incM F B := by ext; simp [incM]
      rw [hI, smul_add, smul_add]; abel
    rw [this]; exact add_mem hA hB
  have Psum : ∀ {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin d) (AE F E)), (∀ k ∈ s, P (f k)) → P (∑ k ∈ s, f k) := by
    intro ι s f h
    classical
    induction s using Finset.induction_on with
    | empty => simpa using P0
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact Padd _ _ (h k (Finset.mem_insert_self _ _)) (ih fun m hm => h m (Finset.mem_insert_of_mem hm))
  have Psingle : ∀ (i : Fin n) (j : Fin d) (w : AE F E), P (Matrix.single i j w) := by
    intro i j w
    induction w using TensorProduct.induction_on with
    | zero => simpa using P0
    | add a b ha hb => rw [Matrix.single_add]; exact Padd _ _ ha hb
    | tmul a x =>
      rw [show P (Matrix.single i j (a ⊗ₜ[F] x)) ↔ ∃ X₀ : Matrix (Fin n) (Fin d) E,
          Matrix.single i j (GlobalTheory.EmbChart.atPlace v (evFin F v a) ⊗ₜ[F] x) - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈
            latAtV X Y v by
        simp only [P, Matrix.smul_single, atPlace_one_smul_tmul]]
      exact core X Y hX hY v i j _ x
  obtain ⟨X₀, h⟩ : P z := by
    rw [Matrix.matrix_eq_sum_single z]
    exact Psum _ _ fun i _ => Psum _ _ fun j _ => Psingle i j _
  exact ⟨X₀, by rw [hz']; exact h⟩

end GlobalTheory.LatPtDecomp
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  first | exact @GlobalTheory.MeanPeriodGenerator.mean_logMet_eq | exact GlobalTheory.MeanPeriodGenerator.mean_logMet_eq | (intros; apply GlobalTheory.MeanPeriodGenerator.mean_logMet_eq <;> assumption)
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem norm_sub_le_of_lieD_unipotent_segment (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ψ : Sm E a) (g : GA E a) (n : Matrix (Fin a) (Fin a) (Cinf E)) (u : ℝ → GL (Fin a) (Cinf E)) (M : ℝ)
    (hn : n * n = 0) (hu : ∀ τ : ℝ, (u τ).val = 1 + τ • n)
    (hM : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖lieD (toL n) ψ.1 (g * infGL E a (u τ))‖ ≤ M) :
    ‖ψ.1 (g * infGL E a (u 1)) - ψ.1 g‖ ≤ M := by
  have h0 : u 0 = 1 := Units.ext (by rw [hu]; simp)
  have hadd : ∀ τ s : ℝ, u (τ + s) = u τ * u s := by
    intro τ s
    refine Units.ext ?_
    rw [Units.val_mul, hu, hu, hu]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hn, smul_zero, add_zero, add_smul]
    abel
  have hc : HasDerivAt (fun t => toL (u t).val) (toL n) 0 := by
    have e : (fun t : ℝ => toL (u t).val) = fun t : ℝ => oneL E a + t • toL n := by
      funext t; rw [hu]; rfl
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL n)).const_add (oneL E a)
  have hd : ∀ τ : ℝ, HasDerivAt (fun t => ψ.1 (g * infGL E a (u t)))
      (lieD (toL n) ψ.1 (g * infGL E a (u τ))) τ := by
    intro τ
    have h1 := hasDerivAt_curve ψ (g * infGL E a (u τ)) u (toL n) h0 hc
    have h2 : HasDerivAt (fun s => ψ.1 (g * infGL E a (u τ) * infGL E a (u s)))
        (lieD (toL n) ψ.1 (g * infGL E a (u τ))) (τ - τ) := by rwa [sub_self]
    have h3 := h2.comp_sub_const τ τ
    have e : (fun t => ψ.1 (g * infGL E a (u τ) * infGL E a (u (t - τ)))) =
        fun t => ψ.1 (g * infGL E a (u t)) := by
      funext t
      rw [mul_assoc, ← map_mul, ← hadd, add_sub_cancel]
    rwa [e] at h3
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t => ψ.1 (g * infGL E a (u t)))
    (fun τ _ => (hd τ).hasDerivWithinAt) (fun τ hτ => hM τ (Set.Ico_subset_Icc_self hτ))
  simpa [h0] using h

end GlobalTheory.CuspRapid
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem exists_finset_clm_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ (B : Finset V) (C : ℝ), 0 ≤ C ∧ ∀ (L : V →L[ℝ] ℂ) (X : V) (M : ℝ),
      (∀ Y ∈ B, ‖L Y‖ ≤ M) → 0 ≤ M → ‖L X‖ ≤ C * ‖X‖ * M := by
  classical
  obtain ⟨C, hC, h⟩ := (Module.finBasis ℝ V).exists_opNorm_le (F := ℂ)
  refine ⟨Finset.univ.image (Module.finBasis ℝ V), C, hC.le, fun L X M hB hM => ?_⟩
  have h1 : ‖L‖ ≤ C * M := h hM fun i => hB _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  calc ‖L X‖ ≤ ‖L‖ * ‖X‖ := L.le_opNorm X
    _ ≤ C * M * ‖X‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = C * ‖X‖ * M := by ring

theorem lieD_le_of_basis : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  intro E _ _ _ a
  obtain ⟨B, C, hC, h⟩ := exists_finset_clm_bound (Lie E a)
  exact ⟨B, C, hC, fun ψ g X M hB hM => h (fderiv ℝ (chart ψ g) (oneL E a)) X M hB hM⟩

end GlobalTheory.CuspRapid
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.exists_common_denominator_compact_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (Kf : Set (Af E)), IsCompact Kf → ∃ n : ℕ, 0 < n ∧ ∀ ξ : E, algebraMap E (Af E) ξ ∈ Kf → IsIntegral ℤ ((n : E) * ξ) := by
  first | exact @GlobalTheory.AdeleDenom.exists_common_denom | exact GlobalTheory.AdeleDenom.exists_common_denom | (intros; apply GlobalTheory.AdeleDenom.exists_common_denom <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))), B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  first | exact @GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | exact GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | (intros; apply GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

theorem _root_.GlobalTheory.T.isCompact_GL_of_compact_invertibleMatrices : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)), IsCompact T → T ⊆ invSet E n → IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  first | exact @GlobalTheory.WhitBump.isCompact_GL_of_invSet | exact GlobalTheory.WhitBump.isCompact_GL_of_invSet | (intros; apply GlobalTheory.WhitBump.isCompact_GL_of_invSet <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.continuous_GL_adelic_projections_inclusions : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧ Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧ Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  first | exact @GlobalTheory.GLProj.continuous_proj_incl | exact GlobalTheory.GLProj.continuous_proj_incl | (intros; apply GlobalTheory.GLProj.continuous_proj_incl <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AdeleApprox

theorem exists_compact_integral (E : Type) [Field E] [NumberField E] :
    ∃ C : Set (InfiniteAdeleRing E), IsCompact C ∧
      ∀ x : Ad E, ∃ a : E, (x - algebraMap E (Ad E) a).1 ∈ C ∧
        ∀ v, (x - algebraMap E (Ad E) a).2 v ∈ v.adicCompletionIntegers E := by
  obtain ⟨C, hC, hCy⟩ := Formalism.IndefR.Eqv.G5.adl_inf_cocompact (F := E)
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap E _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap E (InfiniteAdeleRing E) (u + r) ∈ C
    rw [map_add (f := _), ← sub_sub]
    exact hr
  · have : x.2 - algebraMap E (Af E) (u + r) =
        (x.2 - algebraMap E _ u) - algebraMap E _ (r : E) := by rw [map_add (f := _), sub_sub]
    show ∀ v, (x.2 - algebraMap E (Af E) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

theorem exists_rat_sub_bounded_small :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧
        pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  intro E _ _ _ U hU
  obtain ⟨C, hC, hcov⟩ := exists_compact_integral E
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E U hU
  have hc : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hC.image hc).isBounded
  refine ⟨N * max B 0, by positivity, fun x => ?_⟩
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨a, h1, h2⟩ := hcov (algebraMap E (Ad E) (N : E)⁻¹ * x)
  set k := algebraMap E (Ad E) (N : E)⁻¹ * x - algebraMap E (Ad E) a with hk
  have e : x - algebraMap E (Ad E) ((N : E) * a) = N • k := by
    rw [hk, nsmul_eq_mul, ← map_natCast (algebraMap E (Ad E)) N, mul_sub, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hN', map_one, one_mul, map_mul]
  refine ⟨(N : E) * a, ?_, ?_⟩
  · rw [e, map_nsmul]
    have hb : ‖pInf E k‖ ≤ max B 0 := (hB _ ⟨k.1, h1, rfl⟩).trans (le_max_left _ _)
    exact (norm_nsmul_le).trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  · rw [e, map_nsmul]
    exact hNU _ h2

end GlobalTheory.AdeleApprox
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction

namespace GlobalTheory.SiegelTorusInf

theorem exists_diag_infGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧
      diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  have h0 : ∀ i, (r i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (hr i).ne'
  refine ⟨⟨Matrix.diagonal (fun i => fun _ => (r i : ℂ)), Matrix.diagonal (fun i => fun _ => (r i : ℂ)⁻¹), ?_, ?_⟩,
    rfl, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact mul_inv_cancel₀ (h0 i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact inv_mul_cancel₀ (h0 i)
  · have key : ∀ i, ((posIdele (K := E) (r i) (hr i) : IdeleGroup E) : Ad E) =
        1 - sInf E 1 + sInf E (fun _ => (r i : ℂ)) := fun i => by
      rw [GlobalTheory.CuspBoundSiegel.posIdele_congr (hr i) (Real.exp_pos _) (Real.exp_log (hr i)).symm,
        GlobalTheory.CuspBoundSiegel.posIdele_exp]
      change 1 - sInf E 1 + sInf E _ = _
      congr 2
      funext w
      change Complex.exp (Real.log (r i) : ℂ) = (r i : ℂ)
      rw [← Complex.ofReal_exp, Real.exp_log (hr i)]
    refine Units.ext ?_
    rw [coe_diagUnits]
    refine Matrix.ext fun i j => ?_
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E (Matrix.diagonal (fun i => (fun _ => (r i : ℂ) : Cinf E)) i j)
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact key i
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, Matrix.one_apply_ne h,
        map_zero, sub_zero, add_zero]

end GlobalTheory.SiegelTorusInf

end
end
