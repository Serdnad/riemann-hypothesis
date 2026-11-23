module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
import Mathlib.Algebra.Module.Torsion.Prod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportSelfDualDataOneHermitianSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChrLocal

open scoped TensorProduct
open GlobalTheory.AdelicU

theorem map_eq_zero_of_at {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {B : Type} [CommRing B]
    [Algebra F B] {v : Pl (F := F)} {x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hx : At (evFin F v) x) {a : AF F}
    (ha : evFin F v a = 0) (f : AF F →ₐ[F] B) (hf : f a = 1) :
    Algebra.TensorProduct.map f (AlgHom.id F E) x = 0 := by
  have h := hx a ha
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply] at h
  have h2 := congrArg (Algebra.TensorProduct.map f (AlgHom.id F E)) h
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_zero] at h2
  simpa [hf, ← Algebra.TensorProduct.one_def] using h2

theorem eq_locIdele_splitPrime {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ)
    (hz : At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) (h1 : piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1) :
    z = GlobalTheory.LFun.locIdele F (splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (splitPrime_under τ)).toMonoidHom (Units.map (piW τ).toMonoidHom z)) := by
  refine GlobalTheory.LFun.eq_locIdele ?_ (FiniteAdeleRing.ext _ fun u => ?_)
  · have h := map_eq_zero_of_at hz (a := ((1 : Ainf F), (0 : Af F))) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0 = 0
      exact map_zero _) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) rfl
    change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  · by_cases hu : u.under (𝓞 F) = v
    · rw [GlobalTheory.LFun.finAdEquiv_apply hu]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = compFin F E v (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      rw [e]
      obtain ⟨τ', rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hσ (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hσ τ) hu
      rw [GlobalTheory.LFun.SplitTie.toCompl_eq_complMap τ' hu]
      change _ = Neutral.B1.finiteSingle E (splitPrime τ) _ (splitPrime τ')
      rcases eq_or_eq_comp_conj hσ τ τ' with rfl | rfl
      · rw [GlobalTheory.LFun.finSingle_self]
        rfl
      · rw [GlobalTheory.LFun.finSingle_ne (splitPrime_comp_ne hσ τ)]
        change GlobalTheory.LFun.complMap hu (piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1
        rw [h1, map_one]
    · rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = compFin F E (u.under (𝓞 F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      have h := map_eq_zero_of_at hz (a := GlobalTheory.LatVac.liftV (u.under (𝓞 F)) 1) (by
        change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin (u.under (𝓞 F)) 1) = 0
        exact evalV_singleFin_ne (Ne.symm hu) 1) (evFin F (u.under (𝓞 F))) (GlobalTheory.LatVac.evFin_liftV _ 1)
      rw [map_sub, map_one, sub_eq_zero] at h
      have h' : compFin F E (u.under (𝓞 F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := h
      rw [e, h', map_one]
      change (1 : u.adicCompletion E) = Neutral.B1.finiteSingle E (splitPrime τ) _ u
      exact (GlobalTheory.LFun.finSingle_ne (fun e => hu (by rw [e]; exact splitPrime_under τ)) _).symm

theorem chrW_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ), At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1) →
    piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 → chrW χ τ (Units.map (piW τ).toMonoidHom z) = Circle.toUnits (χ z) := by
  intro F E _ _ _ _ _ σ hσ χ v τ z hz h1
  change Circle.toUnits (χ (GlobalTheory.LFun.locIdele F (splitPrime τ) _)) = _
  rw [← eq_locIdele_splitPrime hσ τ z hz h1]

end GlobalTheory.ChrLocal
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SplitEmbed

theorem exists_algHom_of_splitsFully : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl (F := F), SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ σ h v hs
  classical
  haveI hprime : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) hb)
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.principal (v.asIdeal.under ℤ))
  have hq' : v.asIdeal.under ℤ = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hne (by rw [hq']; simp)
  have hqp : Prime q := by
    rw [← Ideal.span_singleton_prime hq0, ← hq']
    exact hprime
  set p := q.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [hq', hpdef, Int.span_natAbs]
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    have : (p : ℤ) ∈ v.asIdeal.under ℤ := by rw [hspan]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have hcount : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    have := hs
    unfold SplitsFully at this
    rw [hspan] at this
    exact this
  rw [GlobalTheory.AdelicU.nonempty_split_iff h]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two h.2.2.1 hp hcount v hpv

end GlobalTheory.SplitEmbed
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (y : Af F) :
    ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end GlobalTheory.StdCharFromIsStd

namespace GlobalTheory.StdCharFromIsStd

theorem isStdChar_of_isStd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsStdChar D ψ (-1) := by
  intro D ψ hψ
  refine ⟨isCharAF hψ, GlobalTheory.DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩
  change ψ (pairA D.host.F x 0) = _
  rw [psi_pairA hψ, GlobalTheory.DualPairCompare.sum_infFam θ hθ, GlobalTheory.BaseGoodPlace.trInf_eq_trace]
  congr 1
  push_cast
  ring

end GlobalTheory.StdCharFromIsStd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrSchA

theorem schr_mem_schA_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF D.host.F) × (κ → AF D.host.F)), ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ := by
  intro D ψ hψ κ _ w φ hφ
  exact GlobalTheory.HeisSchA.schr_mem_schA ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) w φ hφ

end GlobalTheory.SchrSchA
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : AF F),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a → a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
  first | exact @GlobalTheory.VacAny.eq_atPlace_of_at | exact GlobalTheory.VacAny.eq_atPlace_of_at | (intros; apply GlobalTheory.VacAny.eq_atPlace_of_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LatParam

theorem vecMulVec_sum_zsmul {E : Type} [Field E] {n d kx ky : ℕ} (ex : Fin kx → Fin n → E) (fy : Fin ky → Fin d → E)
    (c : Fin kx → ℤ) (c' : Fin ky → ℤ) :
    Matrix.vecMulVec (∑ i, c i • ex i) (∑ j, c' j • fy j) =
      ∑ m : Fin kx × Fin ky, (c m.1 * c' m.2) • Matrix.vecMulVec (ex m.1) (fy m.2) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

theorem latAtV_param : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  intro F E _ _ _ _ _ n d X Y hX hY v
  obtain ⟨kx, ex, hex⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))
  obtain ⟨ky, fy, hfy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hY.fg.restrictScalars (R := ℤ))
  let I : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.mapMatrix
  have hI : ∀ J, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J = I J := fun J => rfl
  refine ⟨Fin kx × Fin ky, inferInstance, fun m => Matrix.vecMulVec (ex m.1) (fy m.2), fun γ => ⟨fun h => ?_, ?_⟩⟩
  · induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
      have hx' : x ∈ Submodule.span ℤ (Set.range ex) := by rw [hex]; exact hx
      have hy' : y ∈ Submodule.span ℤ (Set.range fy) := by rw [hfy]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
      obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun m => ⟨(c m.1 * c' m.2) • GlobalTheory.AdelicU.evFin F v a, zsmul_mem hint _⟩, ?_⟩
      have ha' := GlobalTheory.VacAny.eq_atPlace_of_at v a ha

      simp only [hI, vecMulVec_sum_zsmul, map_sum, map_zsmul, Finset.smul_sum, map_zsmul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← ha', smul_comm, smul_assoc]
    | zero => exact ⟨fun _ => 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp only [Pi.add_apply, AddMemClass.coe_add, map_add (f := _), add_smul, Finset.sum_add_distrib]⟩
    | neg x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨-a, by simp only [Pi.neg_apply, NegMemClass.coe_neg, map_neg, neg_smul, Finset.sum_neg_distrib]⟩
  · rintro ⟨a, rfl⟩
    refine AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_
    refine ⟨_, ?_, ?_, ex m.1, ?_, fy m.2, ?_, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact (a m).2
    · have : ex m.1 ∈ Submodule.span ℤ (Set.range ex) := Submodule.subset_span ⟨m.1, rfl⟩
      rw [hex] at this; exact this
    · have : fy m.2 ∈ Submodule.span ℤ (Set.range fy) := Submodule.subset_span ⟨m.2, rfl⟩
      rw [hfy] at this; exact this

end GlobalTheory.LatParam
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.continuous_addChar_symplecticSelfPairing_placeCoordinates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (o : E) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {M : Type} [Fintype M] (g : M → Matrix (Fin n) (Fin d) E),
    Continuous (fun a : M → v.adicCompletionIntegers F => ψ (⅟(2 : AF F) *
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB)
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)))) := by
  first | exact @GlobalTheory.ContSymp.continuous_psi_symp_atPlace | exact GlobalTheory.ContSymp.continuous_psi_symp_atPlace | (intros; apply GlobalTheory.ContSymp.continuous_psi_symp_atPlace <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.KFinLoc

theorem symp_incM_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (θ : E) (x y : Matrix (Fin n) (Fin d) E) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) (inclR (F := F) (AF F) θ) (incM F JA) (incM F JB)
      (incM F x) (incM F y) =
      algebraMap F (AF F) (Algebra.trace F E (θ * GlobalTheory.WeilM.hTens σ JA JB x y)) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (AF F ⊗[F] E) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [← ht, GlobalTheory.WeilM.symp]

  simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, hc, map_mul, map_sum]

theorem trace_hTens_integral_of_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ X₀ : Matrix (Fin n) (Fin d) E, (∀ γ ∈ latAtV X Y v,
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1) →
    ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v) (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)))
      ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ ψ n d X Y v hψ X₀ h x hx y hy
  refine (hψ _).1 fun t ht => ?_
  have hat : At (evFin F v) (GlobalTheory.EmbChart.atPlace v t) := fun u hu => by
    rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hmem : GlobalTheory.EmbChart.atPlace v t • incM F (Matrix.vecMulVec x y) ∈ latAtV X Y v :=
    AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v t, hat, by rw [GlobalTheory.EmbChart.evFin_atPlace]; exact ht,
      x, hx, y, hy, rfl⟩
  have h1 := h _ hmem
  have hm : (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = inclR (F := F) (AF F) (-1 : E) := by rw [map_neg, map_one]
  rw [GlobalTheory.LatVac.symp_smul_smul, hm, symp_incM_mat, GlobalTheory.EmbChart.atPlace_mul_right,
    GlobalTheory.EmbChart.atPlace_mul_right, GlobalTheory.EmbChart.evFin_atPlace, one_mul, AlgHom.commutes, neg_one_mul,
    mul_comm] at h1
  exact h1

end GlobalTheory.KFinLoc
end

section

noncomputable section

namespace GlobalTheory.ThK.SquareIntegrability

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toGAd {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) :
    UA σ J ≃* GlobalTheory.AdelicU.GAd σ (c • J.map σ) :=
  MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (J := J) hσ hc)

end GlobalTheory.ThK.SquareIntegrability
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → ∃ Y'' : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y''.Ψ = Y.Ψ ∧ Y''.Gm = Y.Gm ∧ Y''.ξ0 = Y.ξ0 ∧ Y''.p0 = Y.p0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y'' ∧ GlobalTheory.EqCovol.IsSelfDualTr Y'' ∧ GlobalTheory.TrueCx.covol Y'' = GlobalTheory.TrueCx.covol Y' := by
  first | exact @GlobalTheory.EqCovol.exists_transport | exact GlobalTheory.EqCovol.exists_transport | (intros; apply GlobalTheory.EqCovol.exists_transport <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker : ∀ (D : D7) (Γ V : Type) [Group Γ] [Finite Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G0g D.nd) (ι : G0g D.nd →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D P lam ψ → ∀ (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup (G0g D.nd)), (∀ k, IsHalf D k (H k)) → ∀ (n : Fin 2 → ℕ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → ∀ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) → ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) : ℝ) ≤ c * (locShare D (fun k _ => eUk D k (ψ₀ k)) 0 (S 0) + locShare D (fun k _ => eUk D k (ψ₀ k)) 1 (S 1)) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  first | exact @GlobalTheory.BadCount.bad_part_le_locShare | exact GlobalTheory.BadCount.bad_part_le_locShare | (intros; apply GlobalTheory.BadCount.bad_part_le_locShare <;> assumption)
end
