module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.WeilM GlobalTheory.AdelicU
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical Topology ContDiff

noncomputable section

namespace GlobalTheory.Cofactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

private theorem cont_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem cont_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_pureA {f : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (pureA F f g) :=
  (hf.comp (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i)))).mul
    (hg.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))

theorem hasCompactSupport_pureA {f : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) : HasCompactSupport (pureA F f g) := by
  let H : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hH : Continuous H := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)
  refine HasCompactSupport.intro ((hf.isCompact.prod hg.isCompact).image hH) fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2),
    ⟨subset_tsupport _ (left_ne_zero_of_mul h), subset_tsupport _ (right_ne_zero_of_mul h)⟩, ?_⟩
  funext i
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl


variable (F κ) in
theorem exists_bump : ∃ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, HasCompactSupport f ∧ f 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, h1, ?_⟩
  show (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]


variable (κ) in
def intPts (κ : Type)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F}

theorem intPts_eq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    intPts κ v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
  ext x; simp [intPts]

theorem isCompact_intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : IsCompact (intPts κ v) := by
  rw [intPts_eq]
  exact isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v

theorem isOpen_intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : IsOpen (intPts κ v) := by
  rw [intPts_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {U : Set X} (hc : IsCompact U) (ho : IsOpen U) :
    U.indicator (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]; rfl
  · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem exists_cofactor : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ (r : (κ → AF F) → ℂ) (K : Set (κ → Fv F v)), @Measurable _ _ (borel _) _ r ∧
      (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r ∈ GlobalTheory.WeilM.schA F κ) ∧
      IsCompact K ∧ (interior K).Nonempty ∧
      ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 ∧
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ := by
  intro F _ _ κ _ v
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨f, hfc, hf0⟩ := exists_bump F κ
  let φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ := fun w => (intPts κ w).indicator 1
  have hφ : ∀ w, φ w ∈ GlobalTheory.WeilM.SB _ := fun w => indicator_mem_SB (isCompact_intPts w) (isOpen_intPts w)
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have key : ∀ ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) ψ r = pureA F f g := by
    intro ψ hψ
    have h1 : ∀ w, Function.update φ v ψ w ∈ GlobalTheory.WeilM.SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hψ
      · rw [Function.update_of_ne hw]; exact hφ w
    have h2 := GlobalTheory.PureFactor.update_eventually φ v ψ hstd
    exact ⟨_, ⟨isLocallyConstant_finprod_evalV _ h1 h2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ h1 h2⟩,
      hrt ψ⟩
  have hev : Continuous fun x : κ → AF F => fun i => evFin F v (x i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (continuous_apply i))
  have h0 : (0 : κ → Fv F v) ∈ intPts κ v := fun _ => zero_mem _
  have hrc : Continuous r := by
    rw [continuous_iff_continuousAt]
    intro x
    let y : κ → Fv F v := fun i => evFin F v (x i)
    let U : Set (κ → Fv F v) := Homeomorph.addRight y '' intPts κ v
    have hUo : IsOpen U := (Homeomorph.addRight y).isOpenMap _ (isOpen_intPts v)
    have hUc : IsCompact U := (isCompact_intPts v).image (Homeomorph.addRight y).continuous
    have hy : y ∈ U := ⟨0, h0, by simp⟩
    obtain ⟨g, hg, e⟩ := key _ (indicator_mem_SB hUc hUo)
    refine (continuous_pureA f.continuous hg.1.continuous).continuousAt.congr ?_
    filter_upwards [hev.continuousAt.preimage_mem_nhds (hUo.mem_nhds hy)] with z hz
    rw [← e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens
    rw [Set.indicator_of_mem (show (fun i => evFin F v (z i)) ∈ U from hz), Pi.one_apply, one_mul]
  refine ⟨r, intPts κ v, hrc.measurable, hr, fun ψ hψ => ?_, isCompact_intPts v,
    ⟨0, by rw [(isOpen_intPts v).interior_eq]; exact h0⟩, fun μ hμ => ?_⟩
  · obtain ⟨g, hg, e⟩ := key ψ hψ
    exact Submodule.subset_span ⟨f, g, hg, e⟩
  obtain ⟨g, hg, e⟩ := key _ (hφ v)
  set P := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r with hP
  have hPc : Continuous P := e ▸ continuous_pureA f.continuous hg.1.continuous
  have hPs : HasCompactSupport P := e ▸ hasCompactSupport_pureA hfc hg.2
  have hP0 : P 0 = 1 := by
    rw [hP, hrt (φ v), Function.update_eq_self]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have a1 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    rw [a1, hf0, one_mul]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have : (fun i => evFin F w ((0 : κ → AF F) i)) ∈ intPts κ w := by
      intro i
      show evFin F w 0 ∈ _
      rw [map_zero]; exact zero_mem _
    exact Set.indicator_of_mem this _
  have hI : (fun x : κ → AF F => (intPts κ v).indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2) =
      fun x => ‖(P * P) x‖ₑ := by
    funext x
    simp only [hP, Pi.mul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, φ]
    by_cases hx : (fun i => evFin F v (x i)) ∈ intPts κ v
    · simp [Set.indicator_of_mem hx, sq]
    · simp [Set.indicator_of_notMem hx]
  rw [hI]
  have hPP : Continuous (P * P) := hPc.mul hPc
  refine ⟨fun h => ?_, (hPP.integrable_of_hasCompactSupport hPs.mul_left).2.ne⟩
  rw [lintegral_eq_zero_iff hPP.measurable.enorm] at h
  have h3 : (P * P) =ᵐ[μ] 0 := h.mono fun x hx => by simpa using hx
  have h4 := congrFun ((hPP.ae_eq_iff_eq μ continuous_zero).1 h3) 0
  simp [hP0] at h4

end GlobalTheory.Cofactor

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.NormAssemble

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

theorem cT_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    cT σ (aeval M p) = aeval (cT σ M) (p.map σ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul]
    have hp : ((M ^ k).map σ)ᵀ = ((M.map σ)ᵀ) ^ k := by
      rw [← Matrix.transpose_pow, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply]
    simp only [cT, Matrix.map_smul', hp]
    ext i j; simp [Matrix.transpose_smul]
    left; rw [← hp]; rfl

def toFld {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r) : E[X] →+* Fld Q :=
  AdjoinRoot.mk Q.1

def sr {E : Type} [Field E] [NumberField E] [IsCMField E] (Q : E[X]) (h : IsSelfRecip E Q.natDegree Q) :
    SelfRecip E Q.natDegree := ⟨Q, h⟩

theorem exists_norm_of_factors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → (∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, y * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q y = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q)) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = aeval γ.val m := by
  intro E _ _ _ n γ hγ hP hself m hy
  set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ
  set P := γ.val.charpoly with hPdef
  have hPsep : P.Separable := hP.2.2.1
  have hP0 : P ≠ 0 := hP.1.ne_zero
  have hXP : IsCoprime X P := by
    rw [Polynomial.irreducible_X.coprime_iff_not_dvd]
    intro hX
    exact (hself X monic_X irreducible_X hX).2.2.2.1 (by simp)
  obtain ⟨a, b, hab⟩ := hXP
  have hCH : aeval γ.val P = 0 := Matrix.aeval_self_charpoly _
  have haγ : aeval γ.val a * γ.val = 1 := by
    have := congrArg (aeval γ.val) hab
    simpa [hCH] using this
  have hu : cT σ γ.val * γ.val = 1 := by
    have : cT σ γ.val * 1 * γ.val = 1 := hγ
    simpa using this
  have h1 : γ.val * (γ⁻¹).val = 1 := Units.mul_inv γ
  have hcTa : cT σ γ.val = aeval γ.val a := by
    calc cT σ γ.val = cT σ γ.val * γ.val * (γ⁻¹).val := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = aeval γ.val a * γ.val * (γ⁻¹).val := by rw [hu, haγ]
      _ = aeval γ.val a := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  set S := (UniqueFactorizationMonoid.normalizedFactors P).toFinset with hS
  have hmem : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q ∣ P := by
    intro Q hQ
    rw [hS, Multiset.mem_toFinset] at hQ
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
    refine ⟨?_, hirr, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ⟩
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
    rw [← hn]; exact Polynomial.monic_normalize hirr.ne_zero
  have hcopS : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q) := by
    intro Q hQ Q' hQ' hne
    simp only [Function.onFun]
    rw [(hmem Q hQ).2.1.coprime_iff_not_dvd]
    intro hd
    exact hne (eq_of_monic_of_associated (hmem Q hQ).1 (hmem Q' hQ').1
      ((hmem Q hQ).2.1.associated_of_dvd (hmem Q' hQ').2.1 hd))
  have hsr : ∀ Q : S, IsSelfRecip E Q.1.natDegree Q.1 := fun Q =>
    hself Q.1 (hmem Q.1 Q.2).1 (hmem Q.1 Q.2).2.1 (hmem Q.1 Q.2).2.2
  have hloc : ∀ Q : S, ∃ fQ : E[X], toFld (sr Q.1 (hsr Q)) fQ *
      invol (sr Q.1 (hsr Q)) (toFld _ fQ) = toFld _ m := by
    intro Q
    obtain ⟨y, hy'⟩ := hy _ (sr Q.1 (hsr Q)) (hmem Q.1 Q.2).2.2
    obtain ⟨fQ, rfl⟩ := AdjoinRoot.mk_surjective y
    exact ⟨fQ, hy'⟩
  choose fQ hfQ using hloc
  have hcop : Pairwise (Function.onFun IsCoprime fun Q : S => Ideal.span {Q.1}) := by
    intro Q Q' hne
    simp only [Function.onFun]
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hcopS Q.2 Q'.2 (fun h => hne (Subtype.ext h))
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop
    (fun Q => Ideal.Quotient.mk (Ideal.span {Q.1}) (fQ Q))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hf : ∀ Q : S, AdjoinRoot.mk Q.1 f = AdjoinRoot.mk Q.1 (fQ Q) := by
    intro Q
    have := congrFun hq Q
    rw [Ideal.quotientInfToPiQuotient_mk] at this
    exact this
  set g := (f.map σ).comp a * f - m with hg
  have hdiv : ∀ Q ∈ S, Q ∣ g := by
    intro Q hQ
    let Q' : SelfRecip E Q.natDegree := sr Q (hsr ⟨Q, hQ⟩)
    have hQP := (hmem Q hQ).2.2
    have ha : toFld Q' a = (alpha Q')⁻¹ := by
      have := congrArg (toFld Q') hab
      rw [map_add (f := _), map_mul, map_mul, map_one] at this
      have hX : toFld Q' X = alpha Q' := AdjoinRoot.mk_X
      have hPz : toFld Q' P = 0 := AdjoinRoot.mk_eq_zero.2 hQP
      rw [hX, hPz, mul_zero, add_zero] at this
      exact eq_inv_of_mul_eq_one_left this
    have hc : toFld Q' ((f.map σ).comp a) = invol Q' (toFld Q' f) := by
      change AdjoinRoot.mk Q'.1 ((f.map σ).comp a) = AdjoinRoot.lift _ _ (eval₂_conj_inv_root Q') (AdjoinRoot.mk Q'.1 f)
      rw [← AdjoinRoot.aeval_eq, aeval_comp, AdjoinRoot.aeval_eq, AdjoinRoot.lift_mk, aeval_def, eval₂_map]
      change eval₂ _ (toFld Q' a) f = _
      rw [ha]; rfl
    have hfQ' : toFld Q' (fQ ⟨Q, hQ⟩) * invol Q' (toFld Q' (fQ ⟨Q, hQ⟩)) = toFld Q' m := hfQ ⟨Q, hQ⟩
    have hf' : toFld Q' f = toFld Q' (fQ ⟨Q, hQ⟩) := hf ⟨Q, hQ⟩
    have : toFld Q' g = 0 := by
      rw [hg, map_sub, map_mul, hc, hf', mul_comm, hfQ', sub_self]
    exact AdjoinRoot.mk_eq_zero.1 this
  have hprod : (∏ Q ∈ S, Q) ∣ g := Finset.prod_dvd_of_coprime hcopS hdiv
  have hassoc : Associated (∏ Q ∈ S, Q) P := by
    have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hPsep.squarefree
    rw [Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
    exact UniqueFactorizationMonoid.prod_normalizedFactors hP0
  have hPg : P ∣ g := hassoc.symm.dvd.trans hprod
  obtain ⟨k, hk⟩ := hPg
  have hg0 : aeval γ.val g = 0 := by rw [hk, map_mul, hCH, zero_mul]
  refine ⟨aeval γ.val f, ?_, ?_⟩
  · rw [show γ.val * aeval γ.val f = aeval γ.val (X * f) by simp,
      show aeval γ.val f * γ.val = aeval γ.val (f * X) by simp, mul_comm]
  · rw [cT_aeval, hcTa, ← aeval_comp, ← map_mul]
    rw [hg, map_sub] at hg0
    exact sub_eq_zero.1 hg0

end GlobalTheory.NormAssemble
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.SelfRecipFactor

theorem isSelfRecip_of_dvd_ell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]),
    P ∈ Ell E n → ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P →
      GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q := by
  intro E _ _ _ n P hP Q hQm hQi hQP
  obtain ⟨hPm, -, -, hroots⟩ := hP
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hP0 : P ≠ 0 := hPm.ne_zero
  have hnorm : ∀ z : ℂ, (Q.map τ).IsRoot z → ‖z‖ = 1 := by
    intro z hz
    apply hroots τ z
    rw [mem_roots (Polynomial.map_ne_zero hP0)]
    obtain ⟨R, rfl⟩ := hQP
    have hz' : eval z (Q.map τ) = 0 := hz
    simp [IsRoot, Polynomial.map_mul, eval_mul, hz']
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h0
    have h : (Q.map τ).IsRoot 0 := by
      rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hnorm 0 h
    simp at this
  set d := Q.natDegree with hd
  set c : E →+* E := (IsCMField.complexConj E : E →+* E) with hc
  have hτc : τ.comp c = (starRingEnd ℂ).comp τ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E τ x
  have hcQ0 : c (Q.coeff 0) ≠ 0 := by
    simpa using hQ0
  set S := GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.sharp E d Q with hS
  have hSdef : S = C (c (Q.coeff 0))⁻¹ * reflect d (Q.map c) := rfl
  have hdegc : (Q.map c).natDegree = d := natDegree_map c
  have hSm : S.Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one d
    · rw [hSdef]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_reflect_le.trans ?_
      rw [hdegc, max_self]
    · rw [hSdef, coeff_C_mul, coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_map]
      exact inv_mul_cancel₀ hcQ0
  have hSdeg : S.natDegree ≤ d := by
    rw [hSdef]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_reflect_le.trans ?_
    rw [hdegc, max_self]

  have hdeg : 0 < (Q.map τ).degree := by
    rw [degree_map]; exact degree_pos_of_irreducible hQi
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz1 : ‖z‖ = 1 := hnorm z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz1; simp at hz1
  have hzinv : z⁻¹ = (starRingEnd ℂ) z := Complex.inv_eq_conj hz1
  have hQz : eval₂ τ z Q = 0 := by
    have : eval z (Q.map τ) = 0 := hz
    rwa [eval_map] at this
  have hSz : eval₂ τ z S = 0 := by
    letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
    have key := eval₂_reflect_mul_pow τ (z⁻¹) d (Q.map c) hdegc.le
    rw [invOf_eq_inv, inv_inv, eval₂_map, hτc, hzinv, ← Polynomial.hom_eval₂, hQz, map_zero] at key
    have hr : eval₂ τ z (reflect d (Q.map c)) = 0 := by
      rcases mul_eq_zero.1 key with h | h
      · exact h
      · exact absurd h (pow_ne_zero _ ((_root_.map_ne_zero _).2 hz0))
    rw [hSdef, eval₂_mul, hr, mul_zero]
  have hdvd : Q ∣ S := by
    by_contra h
    obtain ⟨a, b, hab⟩ := (hQi.coprime_iff_not_dvd).2 h
    have := congrArg (eval₂ τ z) hab
    rw [eval₂_add, eval₂_mul, eval₂_mul, hQz, hSz, eval₂_one] at this
    simp at this
  refine ⟨hQm, hQi, rfl, hQ0, ?_⟩
  exact (eq_of_monic_of_dvd_of_natDegree_le hQm hSm hdvd hSdeg).symm

end GlobalTheory.SelfRecipFactor
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  first | exact @GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | exact GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | (intros; apply GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.cancel_powers_of_cech_line_bundles : (∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (H M : LB X) (N : LB Y) (a : ℤ), H.IsLB → M.IsLB → N.IsLB → LBIso (GlobalTheory.AbLaw.pw N a) (H.pull b) → LBIso (GlobalTheory.AbLaw.pw N (a + 1)) (M.pull b) → LBIso N ((GlobalTheory.AbLaw.tw M H (-1)).pull b)) ∧ ∀ (X : Scheme.{0}) (H M : LB X) (a : ℤ), H.IsLB → M.IsLB → LBIso (GlobalTheory.AbLaw.pw H (a + 1)) (GlobalTheory.AbLaw.pw M a) → LBIso H (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M H (-1)) a) := by
  first | exact @GlobalTheory.CancelPow.cancel_pw | exact GlobalTheory.CancelPow.cancel_pw | (intros; apply GlobalTheory.CancelPow.cancel_pw <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProjBy X.hom → GeometricallyConnected X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ M M' : LB X.left, M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b e))) → LBIso M M' := by
  first | exact @GlobalTheory.LBReductions.lbIso_of_reductions | exact GlobalTheory.LBReductions.lbIso_of_reductions | (intros; apply GlobalTheory.LBReductions.lbIso_of_reductions <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_bundleIso_zpow_local_units_pow : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  first | exact @GlobalTheory.FormalAlg.lbIso_pw_pull_gw | exact GlobalTheory.FormalAlg.lbIso_pw_pull_gw | (intros; apply GlobalTheory.FormalAlg.lbIso_pw_pull_gw <;> assumption)
end
