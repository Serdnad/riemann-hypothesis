module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HighestWeightLineOfKTypeMultiplicityOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle059
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle010
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.UnfoldSumBd
open GlobalTheory.SymChain GlobalTheory.SymBridge GlobalTheory.UnfoldSum

theorem val_inv_pow_le {k : Type} [Field k] [ValuativeRel k] (ϖ : kˣ) (hv : valuation k (ϖ : k) < 1)
    {N A : ℕ} (h : N ≤ A) :
    valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
  have e : (((ϖ ^ N)⁻¹ : kˣ) : k) = (ϖ : k) ^ (A - N) * (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have h0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
    rw [show A = (A - N) + N from (Nat.sub_add_cancel h).symm, pow_add]
    simp only [Nat.add_sub_cancel]
    field_simp
  rw [e, map_mul, map_pow]
  exact mul_le_of_le_one_left zero_le' (pow_le_one' hv.le _)

theorem val_pow_le {k : Type} [Field k] [ValuativeRel k] (ϖ : kˣ) (hv : valuation k (ϖ : k) < 1)
    {N B : ℕ} (h : N ≤ B) : valuation k ((ϖ : k) ^ B) ≤ valuation k ((ϖ : k) ^ N) := by
  rw [show B = N + (B - N) by omega, pow_add, map_mul]
  exact mul_le_of_le_one_right zero_le' (by rw [map_pow]; exact pow_le_one' hv.le _)

theorem sumAgreeBd : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) (σ₀ : K →+* ℂ) (ψ : AddChar k Circle) (ν : Measure k)
    (psi : E → K) (N : ℕ),
    GlobalTheory.SymBridge.IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → HasConductor ψ 1 → IsUnitVol ν →
    (∀ a, IntAt P ((q : E) ^ N * a) → (ψ (ι a) : ℂ) = σ₀ (psi a)) →
    ∀ (U' U : Type) [Fintype U'] [DecidableEq U'] [Fintype U] [DecidableEq U] (c n' c' n c₂ A B : ℕ),
      1 ≤ c → c' = c + 1 → c₂ = c → N ≤ A → N ≤ B →
    ∀ (d' : U' ≃ Fin n') (d : U ≃ Fin n) (e' : U' ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : U ⊕ Fin c ≃ Fin (n + c₂)),
      GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun a => (d' a).val) n') e' →
      GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun a => (d a).val) n) e →
    ∀ (Φ : Matrix (U ⊕ Fin c) (U' ⊕ Fin (c + 1)) k → ℂ) (ΦE : Loc.SF E K (n' + c') (n + c₂)) (C : ℂ),
      (∀ x, Φ (GlobalTheory.SymBridge.toLoc ι e e' x) = C * σ₀ (ΦE x)) →
      (∀ x, Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k)) →
      (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ N)) → Φ (x + y) = Φ x) →
      ∀ x₀, opE ψ ν 1 Φ (GlobalTheory.SymBridge.toLoc ι d d' x₀) =
        C * σ₀ (Loc.E1 (n' := n') (c' := c') (n := n) (c := c₂) psi (LocE.valsQ E q A B) (((q : K) ^ B)⁻¹) ΦE x₀) := by
  intro E K k _ _ _ _ _ _ _ _ _ _ P q ι ϖ σ₀ ψ ν psi N hC hU hψ hν hpsi U' U _ _ _ _ c n' c' n c₂ A B hc hc' hc₂ hA hB
    d' d e' e hoe' hoe Φ ΦE C hΦ hsupp hper x₀
  subst c' c₂
  classical
  have hq : ι (q : E) = (ϖ : k) := hC.unif.symm
  obtain ⟨-, -, -, -, -, -, hres, hrep⟩ := GlobalTheory.SymBridge.ComplRes.residues E k P q ι ϖ hC hU
  have hv : valuation k (ϖ : k) < 1 := (hU ϖ).2 le_rfl
  have hψ1 : ∀ b : k, valuation k b ≤ 1 → ψ b = 1 := fun b hb =>
    (hψ 1).2 le_rfl b (by simpa using hb)
  have hA0 : ((ϖ : k) ^ A) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hinv : (((ϖ ^ A)⁻¹ : kˣ) : k) = ((ϖ : k) ^ A)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hιv : ∀ i : ℕ, ι ((i : E) / (q : E) ^ A) = (i : k) * ((ϖ : k) ^ A)⁻¹ := fun i => by
    rw [map_div₀, map_pow, map_natCast, hq, div_eq_mul_inv]
  set T : Finset k := (LocE.valsQ E q A B).image ι with hTdef
  have hmemT : ∀ t, t ∈ T ↔ ∃ i : ℕ, i < q ^ (A + B) ∧ (i : k) * ((ϖ : k) ^ A)⁻¹ = t := fun t => by
    simp only [hTdef, LocE.valsQ, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, (hιv i).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, hιv i⟩
  have hnat : ∀ i : ℕ, valuation k (i : k) ≤ 1 := fun i => by
    rw [← Valuation.mem_integer_iff]; exact natCast_mem _ i
  have hT1 : ∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := (hmemT t).1 ht
    rw [hinv, map_mul]
    exact mul_le_of_le_one_left zero_le' (hnat i)
  have hT2 : ∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) →
      ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B) := by
    intro x hx
    have hz : x * (ϖ : k) ^ A ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k x * valuation k ((ϖ : k) ^ A)
          ≤ valuation k (((ϖ : k) ^ A)⁻¹) * valuation k ((ϖ : k) ^ A) := by
            rw [← hinv]; gcongr
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hA0, map_one]
    obtain ⟨i, ⟨hi, hzi⟩, huniq⟩ := hrep (A + B) _ hz
    have key : ∀ j : ℕ, valuation k (x - (j : k) * ((ϖ : k) ^ A)⁻¹) ≤ valuation k ((ϖ : k) ^ B) ↔
        valuation k (x * (ϖ : k) ^ A - (j : k)) ≤ valuation k ((ϖ : k) ^ (A + B)) := fun j => by
      have e1 : x * (ϖ : k) ^ A - (j : k) = (x - (j : k) * ((ϖ : k) ^ A)⁻¹) * (ϖ : k) ^ A := by
        field_simp
      rw [e1, pow_add, mul_comm ((ϖ : k) ^ A) ((ϖ : k) ^ B), map_mul, map_mul (valuation k) ((ϖ : k) ^ B)]
      have : valuation k ((ϖ : k) ^ A) ≠ 0 := by simpa using hA0
      exact (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 this)).symm
    refine ⟨(i : k) * ((ϖ : k) ^ A)⁻¹, ⟨(hmemT _).2 ⟨i, hi, rfl⟩, (key i).2 hzi⟩, ?_⟩
    rintro t ⟨ht, htx⟩
    obtain ⟨j, hj, rfl⟩ := (hmemT t).1 ht
    rw [huniq j ⟨hj, (key j).1 htx⟩]
  set X₀ := toLoc ι d d' x₀ with hX₀
  let F : ({rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k) → ℂ :=
    fun u => Φ (affPt 1 X₀ u) * (ψ (-ch (affPt 1 X₀ u)) : ℂ)
  have hF1 : ∀ u, F u ≠ 0 → ∀ i, valuation k (u i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    intro u hu i
    have h1 : Φ (affPt 1 X₀ u) ≠ 0 := left_ne_zero_of_mul hu
    have := hsupp _ h1 i.1.1 i.1.2
    rw [affPt_free] at this
    exact this.trans (val_inv_pow_le ϖ hv hA)
  have hF2 : ∀ u y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (u + y) = F u := by
    intro u y hy
    simp only [F, affPt_add, ch_add]
    have hy' : ∀ r s, valuation k (freeMat y r s) ≤ valuation k ((ϖ : k) ^ N) := by
      intro r s
      simp only [freeMat, Matrix.of_apply]
      split_ifs with h
      · exact (hy _).trans (val_pow_le ϖ hv hB)
      · rw [map_zero]; exact zero_le'
    rw [hper _ _ hy']
    congr 1
    rw [neg_add, AddChar.map_add_eq_mul, hψ1 (-ch (freeMat y)) (by rw [Valuation.map_neg]; exact ch_freeMat_int ϖ hv y hy), mul_one]
  have key := GlobalTheory.PeriodicIntegral.integral_eq_sum k ν hν ϖ hU A B T hT1 hT2 _ F hF1 hF2
  have hL : opE ψ ν 1 Φ X₀ = ∫ u, F u ∂(Measure.pi fun _ => ν) := rfl
  rw [hL, key]

  simp only [Loc.E1, map_mul, map_pow, map_inv₀, map_natCast, map_sum, hres]
  rw [Fintype.card_congr (freeEquiv hc hoe hoe'), mul_left_comm C]
  congr 1
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij (fun t rs => ι (t (freeEquiv hc hoe hoe' rs))) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Fintype.mem_piFinset] at ht ⊢
    exact fun rs => Finset.mem_image_of_mem ι (ht _)
  · intro a _ b _ hab
    funext p
    have := congrFun hab ((freeEquiv hc hoe hoe').symm p)
    simp only [Equiv.apply_symm_apply] at this
    exact ι.injective this
  · intro u hu
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hu
    choose g hg1 hg2 using fun a => Finset.mem_image.1 (hu a)
    refine ⟨fun p => g ((freeEquiv hc hoe hoe').symm p), ?_, funext fun rs => ?_⟩
    · rw [Finset.mem_coe, Fintype.mem_piFinset]
      exact fun p => hg1 _
    · simp only [Equiv.symm_apply_apply, hg2]
  · intro t _
    simp only [F]
    rw [affPt_eq ι hc hoe hoe' x₀ t, hΦ, ch_eq ι hoe hoe']
    set X := Loc.xx1 x₀ t
    rw [← mul_assoc]
    by_cases h0 : C * σ₀ (ΦE X) = 0
    · rw [h0, zero_mul, zero_mul]
    congr 1
    have hnz : Φ (toLoc ι e e' X) ≠ 0 := by rw [hΦ]; exact h0
    have hI := hsupp _ hnz
    have hint : ι ((q : E) ^ N * Loc.chArg X) ∈ 𝒪[k] := by
      rw [map_mul, map_pow, hq, ← ch_eq ι hoe hoe', ch, Finset.mul_sum]
      refine sum_mem fun i _ => ?_
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ : k) ^ N) * valuation k (toLoc ι e e' X (Sum.inr i) (Sum.inr i.succ))
          ≤ valuation k ((ϖ : k) ^ N) * valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by gcongr; exact hI _ _
        _ = 1 := by
          rw [← map_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
            mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), map_one]
    have hIA : IntAt P ((q : E) ^ N * -Loc.chArg X) :=
      (hC.int _).1 (by rw [mul_neg, map_neg]; exact neg_mem hint)
    have h2 := hpsi _ hIA
    rw [← h2, map_neg]
end GlobalTheory.UnfoldSumBd
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.isOpen_mirabolicProjectionToGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (1 : GL (A ⊕ Fin c) k) ∈ O → (∀ z ∈ R k A c 1, z ∈ O → z ∈ Ck) → IsOpen (prX Ck : Set (GL A k)) := by
  first | exact @GlobalTheory.OpenPr.isOpen_prX | exact GlobalTheory.OpenPr.isOpen_prX | (intros; apply GlobalTheory.OpenPr.isOpen_prX <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

noncomputable section

namespace GlobalTheory.CplDead

open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem full_finset_inf {W ι : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset ι) (M : ι → Submodule (𝓞 E) W)
    (hM : ∀ i, Full (M i)) : Full (S.inf M) := by
  induction S using Finset.induction_on with
  | empty => intro x; exact ⟨1, one_pos, by simp⟩
  | insert i S hi ih => rw [Finset.inf_insert]; exact (hM i).inf ih

theorem exists_approx_family {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (M : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) W) (hM : ∀ P, Full (M P)) (x : HeightOneSpectrum (𝓞 E) → W) :
    ∃ t : W, ∀ P ∈ S, t - x P ∈ localization₂ P.asIdeal (M P) := by
  have h := fun P => (full_finset_inf S M hM).approx {P} (x P)
  choose t h1 h2 using h
  refine ⟨∑ P ∈ S, t P, fun P hP => localization_mono P (Finset.inf_le hP) ?_⟩
  rw [← Finset.add_sum_erase S t hP, add_sub_right_comm]
  refine Submodule.add_mem _ (h1 P P (Finset.mem_singleton_self P)) (Submodule.sum_mem _ fun Q hQ => h2 Q P ?_)
  rw [Finset.mem_singleton]
  exact (Finset.ne_of_mem_erase hQ).symm

theorem full_of_span {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (hN : Submodule.span E (N : Set (Sp E n)) = ⊤) : Full N := by
  first
  | exact @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | (apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top ..)

theorem full_stdLat (n : ℕ) : Full (stdLat E n) := by
  refine full_of_span _ (top_le_iff.1 fun x _ => ?_)
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span fun j _ => ?_)
  by_cases h : i = j
  · simp only [if_pos h]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · simp only [if_neg h]; exact Submodule.zero_mem _

theorem intAt_of_mem_stdAt {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {x : Sp E n} (hx : x ∈ stdAt E n P) (i : Fin n) :
    IntAt P (x i) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i (Set.mem_univ i))
  exact ⟨r, s, hs, by rw [hr]; rfl⟩

variable {a b : ℕ}

def homInto (S₀ : Set (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) where
  carrier := {z | ∀ y ∈ S₀, g (z y) ∈ N}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {z z'} hz hz' y hy => by
    rw [LinearMap.add_apply, map_add (f := _)]; exact N.add_mem (hz y hy) (hz' y hy)
  smul_mem' := fun c z hz y hy => by
    rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower]; exact N.smul_mem _ (hz y hy)

theorem full_homInto (S₀ : Finset (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) {N : Submodule (𝓞 E) (Sp E b)} (hN : Full N) :
    Full (homInto (S₀ : Set (Sp E a)) g N) := by
  intro z
  choose n hn hz using fun y => hN (g (z y))
  refine ⟨∏ y ∈ S₀, n y, Finset.prod_pos fun y _ => hn y, fun y hy => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower, ← Finset.prod_erase_mul S₀ n hy, Nat.cast_mul, mul_smul]
  exact N.smul_mem _ (hz y)

theorem apply_mem_of_mem_locP {S₀ : Set (Sp E a)} {g : Sp E b →ₗ[E] Sp E b} {N : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} {z : HomE E a b} (hz : z ∈ localization₂ P.asIdeal (homInto S₀ g N)) {y : Sp E a}
    (hy : y ∈ localization₂ P.asIdeal (Submodule.span (𝓞 E) S₀)) : g (z y) ∈ localization₂ P.asIdeal N := by
  obtain ⟨s, hs, hz⟩ := hz
  obtain ⟨t, ht, hy⟩ := hy
  have h : ∀ w ∈ Submodule.span (𝓞 E) S₀, g ((s • z) w) ∈ N := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hz w hw
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), map_add (f := _)]; exact N.add_mem hu hv
    | smul c u _ hu => rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]; exact N.smul_mem _ hu
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  have := h _ hy
  rwa [LinearMap.smul_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    smul_smul] at this

variable [StarRing E]

theorem phiT_add (K : Type) [Field K] {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG)
    {d' : Deco E b ST SG'} (hd' : d'.Ok) (x z : HomE E a b)
    (hz : ∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) : phiT K d d' (x + z) = phiT K d d' x := by
  have key : ∀ x z : HomE E a b, (∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + z) y ∈ d'.at P.1 ∧ d'.f P ((x + z) y) = d.f P y := by
    intro x z hz hx P y hy
    have hq : (qOf P.1 : E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := by rw [qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
      exact_mod_cast this
    have e : z y = (qOf P.1 : 𝓞 E) • ((qOf P.1 : E))⁻¹ • z y := by
      rw [← algebraMap_smul E (qOf P.1 : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hq, one_smul]
    have h1 : z y ∈ d'.at P.1 := by rw [e]; exact Submodule.smul_mem _ _ (hz P y hy)
    have h2 : d'.f P (z y) = 0 := by
      rw [e, hd'.f_smul P _ _ (hz P y hy), Ideal.Quotient.eq_zero_iff_mem.2
        (show (qOf P.1 : 𝓞 E) ∈ P.1.asIdeal from Ideal.absNorm_mem _), zero_mul]
    rw [LinearMap.add_apply]
    exact ⟨Submodule.add_mem _ (hx P y hy).1 h1, by rw [hd'.f_add P _ (hx P y hy).1 _ h1, h2, add_zero, (hx P y hy).2]⟩
  unfold phiT
  refine if_congr ⟨fun h => ?_, key x z hz⟩ rfl rfl
  have := key (x + z) (-z) (fun P y hy => by
    rw [LinearMap.neg_apply, smul_neg]; exact Submodule.neg_mem _ (hz P y hy)) h
  rwa [add_neg_cancel_right] at this

theorem exists_transport (K : Type) [Field K] {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} (hdis : Disjoint ST SB)
    {d : Deco E a ST SG} (hd : d.Ok) {d' : Deco E b ST SG'} (hd' : d'.Ok) (f₀ : Frs E a SB) (f f' : Frs E b SB)
    (c : SB → E) (x : HomE E a b) :
    ∃ x' : HomE E a b, phiT K d d' x' = phiT K d d' x ∧
      ∀ (P : SB) s l, IntAt P.1 (c P * (inFr (f₀ P) (f P) x' - inFr (f₀ P) (f' P) x) (Pi.single s 1) l) := by
  obtain ⟨S₀, hS₀⟩ := hd.lat.fg
  obtain ⟨S₁, hS₁⟩ := hd'.lat.fg
  have hone : Full (1 : Submodule (𝓞 E) E) := by
    intro x
    obtain ⟨n, hn, hnx⟩ := full_stdLat (E := E) 1 (fun _ => x)
    refine ⟨n, hn, ?_⟩
    simpa [stdLat, Submodule.mem_pi] using hnx (0 : Fin 1) (Set.mem_univ _)
  have hfull : Full d'.N := by
    let M : Sp E b → Submodule (𝓞 E) (Sp E b) := fun y =>
      (1 : Submodule (𝓞 E) E).comap ((hStd E b y).restrictScalars (𝓞 E))
    have hM : ∀ y, Full (M y) := by
      intro y x
      obtain ⟨n, hn, hx⟩ := hone (hStd E b y x)
      refine ⟨n, hn, ?_⟩
      simpa [M] using hx
    have hle : S₁.inf M ≤ d'.N := by
      intro x hx
      rw [← hd'.uni]
      simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply]
      intro y hy
      rw [← hS₁] at hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact (show S₁.inf M ≤ M y from Finset.inf_le hy) hx
      | zero => simp
      | add y z hy hz ihy ihz => simpa using Submodule.add_mem (1 : Submodule (𝓞 E) E) ihy ihz
      | smul r y hy ih =>
        let r' : 𝓞 E := ⟨star (r : E), r.isIntegral_coe.map (starRingEnd E).toIntAlgHom⟩
        rw [← algebraMap_smul E r y, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
        have hr := (1 : Submodule (𝓞 E) E).smul_mem r' ih
        change star (r : E) * hStd E b y x ∈ (1 : Submodule (𝓞 E) E) at hr
        simpa [starRingEnd_apply, smul_eq_mul] using hr
    intro x
    obtain ⟨n, hn, hx⟩ := full_finset_inf S₁ M hM x
    exact ⟨n, hn, hle hx⟩
  obtain ⟨t, ht⟩ := exists_approx_family (W := HomE E a b) (ST ∪ SB)
    (fun P => if h : P ∈ SB then
        homInto ((Finset.univ.image fun s : Fin a => f₀ ⟨P, h⟩ (Pi.single s 1) : Finset (Sp E a)) : Set (Sp E a))
          (c ⟨P, h⟩ • (f ⟨P, h⟩).symm.toLinearMap) (stdLat E b)
      else homInto (S₀ : Set (Sp E a)) (((qOf P : E))⁻¹ • LinearMap.id) d'.N)
    (fun P => by
      by_cases h : P ∈ SB
      · simp only [dif_pos h]; exact full_homInto _ _ (full_stdLat b)
      · simp only [dif_neg h]; exact full_homInto _ _ hfull)
    (fun P => if h : P ∈ SB then (f ⟨P, h⟩).toLinearMap ∘ₗ (f' ⟨P, h⟩).symm.toLinearMap ∘ₗ x else x)
  refine ⟨t, ?_, fun P s l => ?_⟩
  · rw [← add_sub_cancel x t]
    refine phiT_add K d hd' x _ fun P y hy => ?_
    have h : P.1 ∉ SB := Finset.disjoint_left.1 hdis P.2
    have h1 := ht P.1 (Finset.mem_union_left _ P.2)
    simp only [dif_neg h] at h1
    exact apply_mem_of_mem_locP h1 (by rw [hS₀]; exact hy)
  · have h1 := ht P.1 (Finset.mem_union_right _ P.2)
    simp only [dif_pos P.2] at h1
    have h2 := apply_mem_of_mem_locP h1 (y := f₀ P (Pi.single s 1))
      (mem_localization_of_mem _ (Submodule.subset_span (by simp)))
    have h3 := intAt_of_mem_stdAt h2 l
    convert h3 using 1
    simp [inFr]

end Gen

theorem xiCpl1_eq_zero_of_frames : ∀ {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word), Disjoint (Pr.vT u) (rowSG Pr sel mu) → ∀ (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p p' : ChPt (R := R) sel mu u (m2 + 1)) (Y Y' : Set (Sp X.E (R.N (m2 + 1)))), p'.deco = p.deco → (∀ P : rowSG Pr sel mu, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) ∈ stdAt X.E (R.N (m2 + 1)) P.1) → (∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p Y x = 0) → ∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p' Y' x = 0 := by
  intro X Pr R Ch sel S mu cst L G m2 hL u hdis al p₀ p p' Y Y' hdeco hY h0 x
  obtain ⟨x', h1, h2⟩ := exists_transport X.K hdis p₀.deco.2 p.deco.2 (frsF sel mu p₀) (frsF sel mu p) (frsF sel mu p')
    (fun P => ((qOf P.1 : X.E) ^ cst.B)⁻¹) x
  rw [← h0 x']
  unfold XiCpl1
  rw [hdeco, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have e1 := hL.psiInvX al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) _ ((frsF sel mu p P).symm (repY Y)) (h2 P)
  have e2 := hL.psiInv al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))
    ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) (fun i => intAt_of_mem_stdAt (hY P) i)
  rw [add_sub_cancel] at e1 e2
  rw [e1, e2]

end GlobalTheory.CplDead
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.matrixUnitDerivative_discreteSeriesMatrixCoeff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (a b : Ix p q) (v : R.HK.V) (w : R.U.H), ∀ g ∈ UJset ε, Formalism.REAL.Eab ε (e a) (e b) (fun x => inner ℂ w (σ x (R.ι v))) g = inner ℂ w (σ g (R.ι (R.HK.act (Eab a b) v))) := by
  first | exact @GlobalTheory.CoeffEab.eab_coeff | exact GlobalTheory.CoeffEab.eab_coeff | (intros; apply GlobalTheory.CoeffEab.eab_coeff <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.highestWeightLine_of_kTypeMultiplicityOne : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ μ : Ix p q → ℚ, (∃ S, IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S) → (∀ S S', IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S → IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S' → S = S') → Module.finrank ℂ ↥(hwSub R.HK.act μ) = 1 := by
  first | exact @GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one | exact GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one | (intros; apply GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.exists_param_coverDiscreteSeries : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  first | exact @GlobalTheory.CoverExhaust.exists_param | exact GlobalTheory.CoverExhaust.exists_param | (intros; apply GlobalTheory.CoverExhaust.exists_param <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CoreHt

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

theorem evGSD_ok_of_eq_one : ∀ (X : Fields) [_root_.NumberField.IsTotallyComplex X.K] (hX : X.Ok) (Pr : Primes X) (R : Ranks)
    (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word), Pr.Ok → mu = 1 → (evGSD W Ch sel mu P u).Ok := by
  intro X _ hX Pr R W Ch sel Sg mu P u hPr hmu
  subst hmu
  exact GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u

end GlobalTheory.CoreHt
end
end
