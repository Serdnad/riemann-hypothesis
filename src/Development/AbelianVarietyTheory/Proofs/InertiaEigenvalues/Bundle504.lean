module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle497
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.LocalFields.UpperNumbering
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle498
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BstLog

theorem iota_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧
      (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  intro l _ P AI T
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR l P AI T
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  let ι : Bst P →ₐ[ℚ_[l]] P.R.BdR := Polynomial.eval₂AlgHom P.ιB u (fun _ => Commute.all _ _)
  refine ⟨ι, fun b => Polynomial.eval₂_C _ _, fun g x => ?_⟩
  have h : ι.comp (actSt P g) = ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →ₐ[ℚ_[l]] P.R.BdR).comp ι := by
    apply Polynomial.algHom_ext'
    · ext b
      show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g (Polynomial.C b)) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (Polynomial.C b))
      rw [actSt_C, Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact hcomm g b
    · show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g Polynomial.X) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u Polynomial.X)
      rw [actSt_X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, hu]
      rfl
  exact congrArg (fun F : Bst P →ₐ[ℚ_[l]] P.R.BdR => F x) h

end GlobalTheory.BstLog
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

open Matrix

namespace GlobalTheory.CellDecNat

theorem glExt {E : Type} [Field E] [NumberField E] {n : ℕ} {x y : GL (Fin n) (Af E)}
    (h : ∀ w, GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

theorem tl_eq_jsw_tl (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ))
    (h : ∀ w i, ((l' w i : ℕ) : ℤ) = l w i) : GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  classical
  unfold GlobalTheory.CellDec.tl GlobalTheory.JSW.tl
  have hm : (List.map (fun w => finGL E n (locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w)))) l'.support.toList).prod =
      finGL E n (List.map (fun w => locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w))) l'.support.toList).prod := by
    rw [map_list_prod, List.map_map]; rfl
  rw [hm]
  congr 1
  apply glExt
  intro w
  rw [map_list_prod, List.map_map,
    List.prod_map_eq_pow_single w _ (fun v hv _ => by simp only [Function.comp_apply]; exact pLoc_locGL_of_ne (Ne.symm hv) _)]
  simp only [Function.comp_apply, pLoc_locGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hL : ∀ i, (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w = ((l' w i : ℕ) : ℤ) := fun i => by
    rw [Finsupp.mapRange_apply, h]
  change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases hw : w ∈ l'.support
  · rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.2 hw), pow_one]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, zpow_natCast]
      simp [GlobalTheory.JSW.diagPow]
    · simp [Matrix.diagonal_apply_ne _ hij, GlobalTheory.JSW.diagPow]
  · rw [List.count_eq_zero_of_not_mem (by simpa using hw), pow_zero]
    have h0 : l' w = 0 := by simpa using hw
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, h0]
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
end GlobalTheory.CellDecNat
end
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Unitary

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

theorem coeFn_right_translate {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    R Γ μ g h.toL2 =ᵐ[quotMeasure Γ μ] fun q => φ (sec Γ q * g) := by
  rw [right_translate_toL2]
  refine (h.mul_right g).coeFn_toL2.trans (Filter.Eventually.of_forall fun q => ?_)
  have := (h.1.mul_right g).descend_mk (sec Γ q)
  rwa [mk_sec] at this

theorem inner_right_translate_integral {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) (H : L2 Γ μ) :
    inner ℂ H (R Γ μ g h.toL2) = ∫ q, starRingEnd ℂ (H q) * φ (sec Γ q * g) ∂quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_right_translate h g] with q e
  simp [e, mul_comm]

theorem inner_R_sub_eq_intervalIntegral :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) → inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc h0 f f' hf hf' hcf hd H t hint
  have ftc : ∀ x, ∫ s in (0 : ℝ)..t, f' (x * c s) = f (x * c t) - f (x * 1) := fun x => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd x s)
      ((hcf.comp (continuous_const.mul hc)).intervalIntegrable _ _), h0]
  haveI : SigmaFinite μ := inferInstance
  haveI : SigmaFinite (quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [(measurePreserving_sec (Γ := Γ) (μ := μ)).map_eq]; infer_instance)
  simp only [inner_right_translate_integral hf']
  rw [MeasureTheory.intervalIntegral_integral_swap hint, ← inner_sub_right, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have e1 := coeFn_right_translate hf 1
  rw [map_one, ContinuousLinearMap.one_apply] at e1
  filter_upwards [coeFn_right_translate hf (c t), e1, Lp.coeFn_sub (R Γ μ (c t) hf.toL2) hf.toL2] with q a b e
  rw [intervalIntegral.integral_const_mul, ftc, e, Pi.sub_apply, a, b]
  simp [mul_comm]

end GlobalTheory.AutomorphicL2Unitary
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory

theorem integrable_conj_mul_translate_path {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] (c : ℝ → G) (hc : Continuous c) {f' : G → ℂ} (hf' : MemL2Quotient Γ μ f')
    (_hcont : Continuous f') (H : L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) := by
  haveI : SigmaFinite μ := inferInstance
  haveI : SigmaFinite (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc]; exact measure_Ioc_lt_top⟩
  have hm : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => rmul Γ (c s) q) :=
    measurable_rmul_uncurry.comp (measurable_snd.prodMk (hc.measurable.comp measurable_fst))
  have hp := (MeasurePreserving.id (volume.restrict (Set.uIoc (0 : ℝ) t))).skew_product
    (μc := _root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) (μd := _root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) hm
    (Filter.Eventually.of_forall fun s => (measurePreserving_rmul (c s)).map_eq)
  have h1 := ((Lp.memLp H).star).comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))
  have h2 := (hf'.2.comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))).comp_measurePreserving hp
  refine (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
  have e : descend Γ f' (rmul Γ (c p.1) p.2) = f' (sec Γ p.2 * c p.1) := by
    rw [← hf'.1.descend_mk, ← rmul_mk, mk_sec]
  change star (H p.2) * descend Γ f' (rmul Γ (c p.1) p.2) = _
  rw [e]
  rfl

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tilt_invariant_approx_by_epsilonRoots_closure : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (w : Cb l), (∀ g ∈ Hinf K, autCb l (AI.actT g) w = w) → ∀ m : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ v : OCb l, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * w = algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ (N + m) * v) := by
  first | exact @GlobalTheory.FlatInvariants.flat_invariant_approx | exact GlobalTheory.FlatInvariants.flat_invariant_approx | (intros; apply GlobalTheory.FlatInvariants.flat_invariant_approx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomic_twist_cocycle_coboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ s : ℕ, Lev l s → ∀ j : ℤ, j ≠ 0 → ∀ c : GQ l → PadicComplex l, CocOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} c → CobOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} (fun g => (l : PadicComplex l) ^ (1 + s + padicValInt l j) * c g) := by
  first | exact @GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 | exact GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 | (intros; apply GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


theorem _root_.GlobalTheory.T.exists_X_pow_smul_mem_wachModule_of_frobenius : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  first | exact @GlobalTheory.NL.DenomStep.main | exact GlobalTheory.NL.DenomStep.main | (intros; apply GlobalTheory.NL.DenomStep.main <;> assumption)
end

section

noncomputable section

open Formalism.Per GlobalTheory.PSer Finset
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem row_lam_sub_untilt_rowT : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  intro l _ F _ _ _ _ ι tsh hn hs hsurj h m x ϖ K τ r hh hϖ hx hT
  have hid : ∀ j n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) =
      sh (m j) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((r : ℕ) : ℤ)) (x j))) := by
    intro j n
    simp only [GlobalTheory.PMonE.term, map_mul, map_zpow₀, hϖ, hs]
    rw [← GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower l F ι, hs]
    rw [show ((r : ℤ) + n * h) = n * h + ((r : ℕ) : ℤ) by push_cast; ring]
    ring
  have hR : 0 ≤ τ r := (norm_nonneg _).trans (hT r 0).1
  have hR' : 0 ≤ ‖(l : ℂ_[l])‖ * τ r := mul_nonneg (norm_nonneg _) hR
  have hlb : τ r / l = ‖(l : ℂ_[l])‖ * τ r := by rw [Laws.norm_l, div_eq_inv_mul]
  have htail : ∀ j, ‖sh (m j) * lam h r (x j) -
      ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
    intro j
    have hsum : Summable (fun n => tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) := by
      simp only [hid]; exact (Laws.summable_lam hh r (hx j)).mul_left _
    have hlam : sh (m j) * lam h r (x j) =
        ∑' n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) := by
      simp only [hid, lam]; rw [tsum_mul_left]
    rw [hlam, ← hsum.sum_add_tsum_compl (s := Icc (-(K : ℤ)) K), add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hR' fun ⟨n, hmem⟩ => ?_
    rw [← hlb]
    show ‖tsh _‖ ≤ _
    rw [hn]
    apply (hT j n).2
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hmem
    rw [lt_abs]; omega
  have hfin : ‖∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
      tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖ ≤ ‖(l : ℂ_[l])‖ * τ r := by
    have := GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le l F ι tsh hn hs hsurj (Fin h × ℤ) (univ ×ˢ Icc (-(K : ℤ)) K)
      (fun a => GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r a.1 a.2) (τ r) hR
      (fun a _ => (hT a.1 a.2).1)
    simp only [Finset.sum_product] at this
    rw [norm_sub_rev]
    simpa [GlobalTheory.PMonE.rowT] using this
  calc _ = ‖∑ j, (sh (m j) * lam h r (x j) -
        ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) +
      (∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
        tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r))‖ := by
        rw [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR' fun j _ => htail j) hfin

end GlobalTheory.PSer

end
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_sh_le_sh_int_sum_of_orthogonal : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : Fin h → Fl l), (∀ i j, ‖sh (m i)‖ < l * ‖sh (m j)‖) →
    (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖sh (m j)‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * sh (m i)‖) →
    ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (l : ℤ) ∣ c j → ‖sh (m j)‖ ≤ ‖sh (∑ i, (c i : Fl l) * m i)‖ := by
  first | exact @GlobalTheory.tilt_orth_of_untilt_orth | exact GlobalTheory.tilt_orth_of_untilt_orth | (intros; apply GlobalTheory.tilt_orth_of_untilt_orth <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_natCombination_approx : ∀ (l : ℕ) [Fact l.Prime] (h j d : ℕ) (r : ℝ) (x : Fin d → Fl l) (n : Fin d → ℕ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ a, ‖sh (x a)‖ ≤ r) → ‖sh (∑ a, n a • x a)‖ ≤ r ∧ ‖lam h j (∑ a, n a • x a) - ∑ a, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  first | exact @GlobalTheory.PSer.lamsum | exact GlobalTheory.PSer.lamsum | (intros; apply GlobalTheory.PSer.lamsum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

private lemma commutator_le_of_forall_commutator_mem {G : Type*} [Group G] (C : Subgroup G)
    (hC : ∀ σ τ : G, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ C :=
  Subgroup.commutator_le.2 fun a _ b _ => by
    rw [commutatorElement_def]
    exact hC a b

theorem pow_mem_upper_mod_commutator : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p e : ℕ) (v : ℝ) (C : Subgroup (L ≃ₐ[F] L)), (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F L v, ∃ τ ∈ upperRamificationGroup F L (min (2 * v) (v + e)), τ⁻¹ * σ ^ p ∈ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p e v C hC hv hpe σ hσ

  let H : Subgroup (L ≃ₐ[F] L) := ⁅(⊤ : Subgroup (L ≃ₐ[F] L)), ⊤⁆
  let Q : IntermediateField F L := IntermediateField.fixedField H
  haveI : IsGalois F Q := IsGalois.of_fixedField_normal_subgroup H
  have hker : (AlgEquiv.restrictNormalHom Q).ker = H := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_fixedField H
  have hab : ∀ s t : Q ≃ₐ[F] Q, s * t = t * s := by
    intro s t
    obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := L) s
    obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := L) t
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ (AlgEquiv.restrictNormalHom Q).ker := by
      rw [hker]
      have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rwa [commutatorElement_def] at h
    rw [MonoidHom.mem_ker] at hmem
    simp only [map_mul, map_inv] at hmem
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hmem
  have hσQ : AlgEquiv.restrictNormalHom Q σ ∈ upperRamificationGroup F Q v := by
    rw [← GroundTheory.LocalField.map_upperRamificationGroup Q v]
    exact Subgroup.mem_map_of_mem _ hσ
  have hpow := GlobalTheory.T.pow_mem_upperRamificationGroup_of_comm' F Q p e v hab hv hpe _ hσQ
  rw [← map_pow, ← GroundTheory.LocalField.map_upperRamificationGroup Q] at hpow
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 hpow
  refine ⟨τ, hτ, commutator_le_of_forall_commutator_mem C hC ?_⟩
  have hk : τ⁻¹ * σ ^ p ∈ (AlgEquiv.restrictNormalHom Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτσ, inv_mul_cancel]
  rw [hker] at hk
  exact hk

end GlobalTheory.PMon.Ram
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ → ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  first | exact @GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | exact GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | (intros; apply GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison <;> assumption)
end
