module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEvaluationL2

theorem lintegral_sq_split {Z X Y : Type} [TopologicalSpace Z] [AddCommGroup Z] [IsTopologicalAddGroup Z]
    [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X]
    [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [T2Space Y]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (e : Z ≃ₜ X × Y) (he : ∀ a b, e (a + b) = e a + e b)
    (μ : Measure Z) [μ.IsAddHaarMeasure] (μX : Measure X) [μX.IsAddHaarMeasure]
    {f g : Z → ℂ} (hf : Continuous f) (hg : Continuous g) (c : ℝ≥0∞)
    (h : ∀ y, ∫⁻ x, ‖f (e.symm (x, y))‖ₑ ^ 2 ∂μX = c * ∫⁻ x, ‖g (e.symm (x, y))‖ₑ ^ 2 ∂μX) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ = c * ∫⁻ z, ‖g z‖ₑ ^ 2 ∂μ := by
  let E : Z ≃ₜ+ X × Y :=
    { e.toEquiv with
      map_add' := he
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  let eM : Z ≃ᵐ X × Y := e.toMeasurableEquiv
  let μY : Measure Y := Measure.addHaar
  haveI hν : (μ.map E).IsAddHaarMeasure := inferInstance
  have hE : (E : Z → X × Y) = eM := rfl
  set s := Measure.addHaarScalarFactor (μ.map E) (μX.prod μY)
  have hs : μ.map E = s • (μX.prod μY) := Measure.isAddLeftInvariant_eq_smul _ _
  have key : ∀ F : Z → ℂ, Continuous F →
      ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = s * ∫⁻ y, ∫⁻ x, ‖F (e.symm (x, y))‖ₑ ^ 2 ∂μX ∂μY := by
    intro F hF
    have hm : Measurable fun p : X × Y => ‖F (e.symm p)‖ₑ ^ 2 :=
      ((hF.comp e.symm.continuous).measurable.enorm.pow_const 2)
    calc ∫⁻ z, ‖F z‖ₑ ^ 2 ∂μ = ∫⁻ p, ‖F (e.symm p)‖ₑ ^ 2 ∂(μ.map E) := by
          rw [hE, lintegral_map_equiv]; simp [eM]
      _ = s * ∫⁻ y, ∫⁻ x, ‖F (e.symm (x, y))‖ₑ ^ 2 ∂μX ∂μY := by
          rw [hs, lintegral_smul_measure, lintegral_prod_symm _ hm.aemeasurable]; rfl
  rw [key f hf, key g hg]
  have hmg : Measurable fun p : X × Y => ‖g (e.symm p)‖ₑ ^ 2 :=
    ((hg.comp e.symm.continuous).measurable.enorm.pow_const 2)
  simp_rw [h]
  rw [lintegral_const_mul _ (hmg.lintegral_prod_left' )]
  ring

end GlobalTheory.DoublingEvaluationL2

namespace GlobalTheory.DoublingEvaluationL2

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsTame F A →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ∧
    (∀ μ : @Measure (κ' ⊕ κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ' ⊕ κ), ∫⁻ x, ‖partR (κ := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) := by
  intro F _ _ κ κ' _ _ A hA hL2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  let μX : Measure (κ → AF F) := Measure.addHaar
  obtain ⟨c, hc⟩ := hL2 μX inferInstance
  constructor
  · intro μ hμ
    letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
    haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hP := IsTame.mapsTo (GlobalTheory.T.tame_part_left F κ κ κ' A hA) Φ hΦ
    refine lintegral_sq_split (Homeomorph.sumPiEquivProdPi κ κ' (fun _ => AF F)) (fun a b => rfl) μ μX
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hP) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) c
      fun y => ?_
    exact hc _ (GlobalTheory.DoublingEvLaw.sliceL hΦ y)
  · intro μ hμ
    letI mZ : MeasurableSpace (κ' ⊕ κ → AF F) := borel _
    haveI : BorelSpace (κ' ⊕ κ → AF F) := ⟨rfl⟩
    refine ⟨c, fun Φ hΦ => ?_⟩
    have hP := IsTame.mapsTo (GlobalTheory.T.tame_part_right F κ' κ κ A hA) Φ hΦ
    refine lintegral_sq_split ((Homeomorph.sumPiEquivProdPi κ' κ (fun _ => AF F)).trans
        (Homeomorph.prodComm _ _)) (fun a b => rfl) μ μX
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hP) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) c
      fun y => ?_
    exact hc _ (GlobalTheory.DoublingEvLaw.sliceR hΦ y)

end GlobalTheory.DoublingEvaluationL2
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvUniq.LocFin

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev ind (w : Pl (F := F)) : (κ → Fv F w) → ℂ := Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

def archPt (a : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), 0)

theorem evFin_archPt (a : κ → mixedEmbedding.mixedSpace F) (w : Pl (F := F)) (i : κ) : evFin F w (archPt a i) = 0 := by
  change (evalV F w) (0 : Af F) = 0
  exact map_zero _

theorem evI_archPt (a : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (archPt a i) = a i := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (a i)

theorem cancel (v : Pl (F := F)) (g : SInf F κ) (hg : g ≠ 0) (r : (κ → AF F) → ℂ)
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x)
    (hrt : ∀ ψ₀ : (κ → Fv F v) → ℂ, tens (evFin F v) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update ind v ψ₀))
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hg
    exact ⟨a, by simpa using ha⟩
  have hx0 : r (archPt a) = g a := by
    have e := congrFun (hrt (fun _ => 1)) (archPt a)
    simp only [tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i => evI F (archPt a i)) = a := funext fun i => evI_archPt a i
    have hP : (∏ᶠ w, Function.update (ind (κ := κ)) v (fun _ => 1) w fun i => evFin F w (archPt a i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [evFin_archPt, ind]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : At (evFin F v) z := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hrz : r (archPt a + z) = g a := by rw [hr _ z hz, hx0]
  have hev : (fun i => evFin F v ((archPt a + z) i)) = y := by
    funext i
    rw [Pi.add_apply, map_add (f := _), evFin_archPt, zero_add]
    exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun h (archPt a + z)
  simp only [tens, hev, hrz] at e
  exact mul_right_cancel₀ ha e

end GlobalTheory.ThK.EvUniq.LocFin


open scoped Classical in
theorem GlobalTheory.ThK.EvUniq.finRel_of_ev : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ (e : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → ∀ v, GlobalTheory.ThK.EvUniq.FinRel B M M₁ H' v (ev v) := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e he ei ev hei hvm hloc v
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d₁) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n × Fin d₁) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n × Fin d₁ → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  refine ⟨?_, ?_⟩
  · intro z hz φ hφ φ₁ hφ₁ hA χ₁ hχ₁ hA₁
    have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    have hevφ : ev v φ ∈ SB _ := by
      rw [← (hvm v).2]
      exact Submodule.mem_map_of_mem hφ
    rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
    exact canc _ _ h1
  · intro u hu hz φ hφ φ₁ hφ₁ hA
    have h1 := he.inv u hu _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    exact canc _ _ h1
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvUniqInf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evFin_eq_zero_of_at (z : κ → AF F) (hz : At (evI F) z) (v : Pl (F := F)) (i : κ) : evFin F v (z i) = 0 := by
  set u : AF F := LinearMap.inr F (Ainf F) (Af F) 1 with hu
  have h0 : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  have hzi : u * z i = 0 := by
    have := congrFun (hz u h0) i
    simpa using this
  have h1 : evFin F v u = 1 := by
    show evalV F v (1 : Af F) = 1
    exact map_one _
  have := congrArg (evFin F v) hzi
  rwa [map_mul, h1, one_mul, map_zero] at this

theorem rest_pure (g : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩
  refine finprod_congr fun v => ?_
  congr 1
  funext i
  rw [Pi.add_apply, map_add (f := _), evFin_eq_zero_of_at z hz v i, add_zero]

theorem eq_of_pure_std (g g' : SInf F κ)
    (h : pure g (fun v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      pure g' (fun v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) : g = g' := by
  refine SchwartzMap.ext fun y => ?_
  let x : κ → AF F := fun i => LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i))
  have hI : (fun i => evI F (x i)) = y := by
    funext i
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = y i
    exact RingEquiv.apply_symm_apply _ _
  have hP : (∏ᶠ v, Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
      (fun i => evFin F v (x i))) = (1 : ℂ) := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    have h0 : (fun i => evFin F v (x i)) = 0 := by
      funext i
      show evalV F v (0 : Af F) = 0
      exact map_zero _
    rw [h0, Set.indicator_of_mem (by intro i; exact zero_mem _)]
    rfl
  have e := congrFun h x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure at e
  rw [hI, hP, mul_one, mul_one] at e
  exact e

end GlobalTheory.ThK.EvUniqInf


open GlobalTheory.ThK.EvUniqInf in
theorem GlobalTheory.ThK.EvUniq.infRel_of_isEv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ (e : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' ei := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ _ _ _ hM _ hM₁ e hev ei ev _ hloc0 hloc

  have hex : ∀ v : Pl (F := F), ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem : Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  have hevφ : (fun v => ev v (φ v)) =
      fun v => Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    funext hφev
  have hRest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    fun g => rest_pure g φ hφSB hstd
  have hRest₁ : ∀ g : SInf F (Fin n × Fin d₁), Rest (evI F) (⇑g) (fun x => ∏ᶠ v,
      Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 fun i => evFin F v (x i)) :=
    fun g => rest_pure g _ (fun v => GlobalTheory.StdVacuum.indicator_mem_SB v) (Filter.Eventually.of_forall fun _ => rfl)
  have he : ∀ g : SInf F (Fin n × Fin d), e (pure g φ) = pure (ei g) (fun v =>
      Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) := by
    intro g; rw [hloc g φ hφSB hcof, hevφ]
  refine ⟨fun z _ f f₁ hA g₁ hA₁ => ?_, fun u hu _ f f₁ hA => ?_⟩
  · have h1 := hev.Heisenberg₂ z (pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) (pure f φ) = pure f₁ φ :=
      hA _ (hRest f)
    rw [h2, he, he] at h1
    have h3 : M₁.co.rho B.ψ z (pure (ei f) (fun v =>
        Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) = pure g₁ (fun v =>
        Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :=
      hA₁ _ (hRest₁ (ei f))
    exact eq_of_pure_std _ _ (h1.trans h3)
  · have h1 := hev.inv u hu (pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ u (pure f φ) = pure f₁ φ := hA _ (hRest f)
    rw [h2, he, he] at h1
    exact eq_of_pure_std _ _ h1
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertRho

theorem exists_rho : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∃ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      ∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC
  obtain ⟨-, -, -, -, -, -, -, -, -, hAt, -⟩ := hC
  have hstd := hTr.base.std
  let ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)) := fun x =>
    { toFun := fun m => ⟨schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (κ x)) m,
        GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v _ _ m.2⟩
      map_add' := fun m m' => by
        ext y
        simp only [schr, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun c m => by
        ext y
        simp only [schr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  exact ⟨ρ, fun x m => GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v (κ x) (hAt x) m⟩

end GlobalTheory.InertRho

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isometryMovedRigging_is : ∀ {D : D7} {S S' : HSp D} (I : GlobalTheory.Mem.Isom.IsoMat S S') (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig S), r.Is → (GlobalTheory.TriMove.rigMove I r).Is := by
  first | exact @GlobalTheory.TriMove.rigMove_is | exact GlobalTheory.TriMove.rigMove_is | (intros; apply GlobalTheory.TriMove.rigMove_is <;> assumption)
end
