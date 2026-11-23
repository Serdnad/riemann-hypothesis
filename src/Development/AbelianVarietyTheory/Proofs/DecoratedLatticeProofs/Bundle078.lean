module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle051
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle073
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle053
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle058
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LFun.SegFactor

open GlobalTheory.LFun

theorem prod_map_sum {ι : Type} (s : Finset ι) (m : ι → Multiset ℂˣ) (F : ℂˣ → ℂ) :
    ((∑ i ∈ s, m i).map F).prod = ∏ i ∈ s, ((m i).map F).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add (f := _), Multiset.prod_add, ih]

variable {K : Type} [Field K] [NumberField K]

theorem prod_fin_eq {N k t : ℕ} (w : HeightOneSpectrum (𝓞 K)) (z : ℕ → ℂˣ) (α : Fin N → ℂˣ)
    (hα : Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, seg w (z i) t) (F : ℂˣ → ℂ) :
    ∏ j, F (α j) =
      ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range t, F (z i * npowU w (((t : ℂ) - 1) / 2 - l)) := by
  rw [Finset.prod_eq_multiset_prod,
    show (Finset.univ.val.map fun j => F (α j)) = (Finset.univ.val.map α).map F from
      (Multiset.map_map _ _ _).symm, hα, prod_map_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [seg, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rfl

theorem re_exp (t l : ℕ) : (((t : ℂ) - 1) / 2 - l).re = ((t : ℝ) - 1) / 2 - l := by
  simp

theorem npow_neg_nat (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    npow w (-(m : ℂ)) = (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ m)⁻¹ := by
  rw [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem prod_Icc_one (t : ℕ) (g : ℕ → ℂ) : ∏ n ∈ Finset.Icc 1 t, g n = ∏ l ∈ Finset.range t, g (l + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  exact Finset.prod_congr rfl fun l _ => by rw [add_comm]

theorem entry_mul (w : HeightOneSpectrum (𝓞 K)) (z : ℂˣ) (t l : ℕ) :
    ((z * npowU w (((t : ℂ) - 1) / 2 - l) : ℂˣ) : ℂ) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      (z : ℂ) * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (l + 1))⁻¹ := by
  rw [Units.val_mul, coe_npowU, mul_assoc, show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
    npow w (-((t : ℂ) / 2 + 1 / 2)) from rfl, ← npow_add, ← npow_neg_nat]
  congr 2
  push_cast
  ring

theorem entry_inv_mul (w : HeightOneSpectrum (𝓞 K)) (z : ℂˣ) {t l : ℕ} (hl : l < t) :
    (((z * npowU w (((t : ℂ) - 1) / 2 - l))⁻¹ : ℂˣ) : ℂ) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      (z : ℂ)⁻¹ * (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (t - 1 - l + 1))⁻¹ := by
  rw [Units.val_inv_eq_inv_val, Units.val_mul, coe_npowU, mul_inv, mul_assoc,
    show (npow w (((t : ℂ) - 1) / 2 - l))⁻¹ = npow w (-(((t : ℂ) - 1) / 2 - l)) by
      rw [npow, npow, Complex.cpow_neg],
    show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)) =
      npow w (-((t : ℂ) / 2 + 1 / 2)) from rfl, ← npow_add, ← npow_neg_nat]
  have e : ((t - 1 - l + 1 : ℕ) : ℂ) = t - l := by
    rw [show t - 1 - l + 1 = t - l by omega, Nat.cast_sub hl.le]
  rw [e]
  congr 2
  ring

end GlobalTheory.LFun.SegFactor

open GlobalTheory.LFun GlobalTheory.LFun.SegFactor in
theorem GlobalTheory.LFun.seg_bounds_and_doubling_lFactor : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k t N : ℕ) (z : ℕ → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ α : Fin N → ℂˣ, Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg w (z i) t → (∀ j, ‖(α j : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2) ∧ ‖(α j : ℂ)‖⁻¹ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t, ((1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹) * (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  intro K _ _ w k t N z hz α hα
  have hN : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm w
  have mem : ∀ j, ∃ i ∈ Finset.Icc 1 k, ∃ l < t, α j = z i * npowU w (((t : ℂ) - 1) / 2 - l) := by
    intro j
    have h1 : α j ∈ Finset.univ.val.map α := Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    rw [hα] at h1
    obtain ⟨i, hi, h2⟩ := Multiset.mem_sum.1 h1
    obtain ⟨l, hl, e⟩ := Multiset.mem_map.1 h2
    exact ⟨i, hi, l, Finset.mem_range.1 hl, e.symm⟩
  refine ⟨fun j => ?_, ?_⟩
  · obtain ⟨i, -, l, hl, e⟩ := mem j
    have hn : ‖(α j : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2 - l) := by
      rw [e, Units.val_mul, norm_mul, hz, one_mul, coe_npowU, norm_npow, re_exp]
    have hl' : (l : ℝ) + 1 ≤ t := by exact_mod_cast hl
    have h0 : (0 : ℝ) ≤ l := l.cast_nonneg
    rw [hn, ← Real.rpow_neg (by linarith)]
    exact ⟨Real.rpow_le_rpow_of_exponent_le hN.le (by linarith),
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)⟩
  · have eA : GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) =
        ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t,
          (1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹ := by
      rw [GlobalTheory.GLDoubling.lFactor, prod_fin_eq w z α hα (fun β : ℂˣ =>
        (1 - (β : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)))⁻¹)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [prod_Icc_one t (fun n => (1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹)]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [entry_mul]
    have eB : GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) =
        ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t,
          (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹ := by
      rw [GlobalTheory.GLDoubling.lFactor]
      refine (prod_fin_eq w z α hα (fun β : ℂˣ =>
        (1 - ((β⁻¹ : ℂˣ) : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) / 2 + 1 / 2)))⁻¹)).trans ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [prod_Icc_one t (fun n => (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹)⁻¹),
        ← Finset.prod_range_reflect (fun l => (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ (l + 1))⁻¹)⁻¹)]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [entry_inv_mul w (z i) (Finset.mem_range.1 hl)]
    rw [eA, eB, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [mul_inv]
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_badPrimes : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  first | exact @GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp | exact GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp | (intros; apply GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (γ : AutY X R s) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k), IsGL ι γ g →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) s ≃ Fin (R.N s)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))),
    IsOrd xPos e' → IsOrd xPos e → ∀ (x₀ : HomE X.E (R.N s) (R.N (s + 1))) (y' : Sp X.E (R.N (s + 1))),
      (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
        sgn sel mu P W γ (R.N (s + 1) + cOf R (s + 1)) * σ₀ (PsiAt Ch sel mu cst s P γ x₀ y') := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hok hA hPhi γ g hg e' e he' he x₀ y'
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  obtain ⟨eg, hegO, hgv⟩ := hg
  let E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s) :=
    (e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv
  let E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv
  have hE' : IsOrd (yPos xPos (R.N s)) E' := by
    rintro (a | a)
    · simp [E', yPos, he' a]
    · simp [E', yPos]
  have hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁ := by
    rintro (a | a)
    · simp [E₁, yPos, he a]
    · exact a.elim0
  have hegE : eg = E' := Equiv.ext fun a => Fin.ext ((hegO a).trans (hE' a).symm)
  subst hegE
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') :=
    PsiStep.withCol_toLoc ι e e' hc1 hc0 x₀ y'
  have hprod : toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') * toLoc ι E' E' γ.toLinearMap =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) := by
    have h : ∀ {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (z : HomE X.E b a),
        toLoc ι e e' z = ((LinearMap.toMatrix' z).submatrix e e').map ι := by
      intro A B a b e e' z
      ext i j
      simp [toLoc, LinearMap.toMatrix'_apply, Matrix.map_apply, Matrix.submatrix_apply]
    rw [h, h, h, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ E₁ E' E', Matrix.map_mul]
  have hdet : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = ι ((LinearEquiv.det γ : X.Eˣ) : X.E) := by
    have h := RingHom.map_det ι ((LinearMap.toMatrix' γ.toLinearMap).submatrix E' E')
    rw [RingHom.mapMatrix_apply] at h
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, toLoc_eq_map_toMatrix', ← h,
      Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0) = R.N (s + 1) + cOf R (s + 1) := by
    rw [Fintype.card_congr E₁, Fintype.card_fin]
  have hPhi1 := hPhi.1 s 0 rfl E' E₁ hegO hE₁ (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)
  have char_scalar (a : X.E) (u : kˣ)
      (hu : (u : k) = ι a) (N : ℕ) :
      ((W.η (s + 1) * W.δ) u : ℂ) * ((nabs k u ^ ((N : ℝ) / 2) : ℝ) : ℂ) =
        W.sg ^ (LocE.vP P.1 (qOf P.1) a * N) *
          σ₀ (muAt Ch sel mu cst s P a * cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) a) * N)) := by
    have hC := hA.compl
    have hU := W.unif
    have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := ComplRes.q_ne_zero hC
    have hvalu := GlobalTheory.TwBridge.PsiRat.val_unif' hU
    have hex : ∃ z : ℤ, IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ z)) := by
      obtain ⟨z, hz⟩ := GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow hvalu u
      refine ⟨z, ?_⟩
      have hv1 : valuation k (ι (a / ((qOf P.1 : ℕ) : X.E) ^ z)) = 1 := by
        rw [map_div₀, map_zpow₀, ← hC.unif, ← hu, map_div₀, map_zpow₀, hz, div_self]
        exact zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 W.ϖ.ne_zero)
      exact (ComplRes.v_eq_one_iff_red hC hU (ComplRes.intAt_of_v hC hv1.le)).1 hv1
    have hspec : IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ LocE.vP P.1 (qOf P.1) a)) := by
      unfold LocE.vP; exact Classical.epsilon_spec hex
    set v := LocE.vP P.1 (qOf P.1) a with hvdef
    set b := a / ((qOf P.1 : ℕ) : X.E) ^ v with hbdef
    have hbI : IntAt P.1 b := by
      by_contra h; rw [reduction_eq_zero_of_not_integral P.1 h] at hspec; exact not_isUnit_zero hspec
    have hbv : valuation k (ι b) = 1 := (ComplRes.v_eq_one_iff_red hC hU hbI).2 hspec
    have hb0 : ι b ≠ 0 := by intro h; rw [h, map_zero] at hbv; exact zero_ne_one hbv
    set ub : kˣ := Units.mk0 (ι b) hb0 with hubdef
    have hu_eq : u = W.ϖ ^ v * ub := by
      ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hu, hC.unif, ← map_zpow₀, ← map_mul, hbdef,
        mul_div_left_comm, div_self (zpow_ne_zero v hq0), mul_one]
    have hη : W.η (s + 1) ub = 1 := W.unr (s + 1) ub hbv
    have hδ : (W.δ ub : ℂ) = (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := hA.del b ub hbI hspec rfl
    have hμ : ((W.η (s + 1) * W.δ) W.ϖ : ℂ) = σ₀ (cst.muq (s + 1) P) := hA.mu s (by rw [hA.steps]; omega)
    have hnU : nabs k ub = 1 := nabs_eq_one_of_valuation_eq_one hbv
    obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif hU
    have hnϖ : nabs k W.ϖ = ((qOf P.1 : ℕ) : ℝ)⁻¹ := by
      rw [nabs_uniformiser hp hpϖ.symm, ComplRes.resCard_eq hC hU]
    have hn : nabs k u = ((qOf P.1 : ℕ) : ℝ) ^ (-v) := by
      rw [hu_eq]
      unfold nabs
      rw [map_mul, map_zpow, NNReal.coe_mul, NNReal.coe_zpow]
      have h1 : ((distribHaarChar k W.ϖ : NNReal) : ℝ) = ((qOf P.1 : ℕ) : ℝ)⁻¹ := hnϖ
      have h2 : ((distribHaarChar k ub : NNReal) : ℝ) = 1 := hnU
      rw [h1, h2, mul_one, _root_.inv_zpow']
    have hsg : W.sg ≠ 0 := by
      intro h0
      have h2 := congrArg σ₀ (hok.sq_sq P)
      rw [map_pow, hA.sq, h0, zero_mul, map_natCast] at h2
      exact hq0 (by exact_mod_cast (zero_pow two_ne_zero).symm.trans h2 |>.symm)
    have hmuAt : muAt Ch sel mu cst s P a = cst.muq (s + 1) P ^ v * (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b)⁻¹ := by
      unfold muAt LocE.locChar
      rw [ite_eq_right hA.nmem, ← hvdef, ← hbdef]
      congr 1
      unfold LocE.unitV
      rw [dite_eq_left hspec, dite_eq_left hspec, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have hchar : ((W.η (s + 1) * W.δ) u : ℂ) = σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := by
      rw [hu_eq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hμ, MonoidHom.mul_apply, Units.val_mul, hη,
        Units.val_one, one_mul, hδ]
    have hq : (0 : ℝ) < ((qOf P.1 : ℕ) : ℝ) := by
      have : (qOf P.1 : ℕ) ≠ 0 := fun h => hq0 (by rw [h, Nat.cast_zero])
      exact_mod_cast Nat.pos_of_ne_zero this
    rw [hchar, hn, GlobalTheory.TwBridge.PsiRat.sqrt_pow _ hq, hmuAt, map_mul, map_mul, map_zpow₀, map_inv₀, map_zpow₀, hA.sq, mul_zpow]
    push_cast
    have hs1 : W.sg ^ (v * N) * W.sg ^ (-v * N) = 1 := by
      rw [neg_mul, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hsg)]
    linear_combination (σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ *
      (Real.sqrt ((qOf P.1 : ℕ) : ℝ) : ℂ) ^ (-v * N)) * (-hs1)
  have hsc := char_scalar _ _ hdet (R.N (s + 1) + cOf R (s + 1))
  have hL : (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      ((W.η (s + 1) * W.δ) (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((R.N (s + 1) + cOf R (s + 1) : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        σ₀ (PhiAt Ch mu cst.sharp s P.1 (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)) := by
    rw [← hPhi1, ← hprod, ← hgv, ← hmat, ← hcard]
    clear hsc hPhi1 hdet hprod hmat hE₁ hE' hegO hPhi hA hok hgv hcard he he'
    unfold Chain.Psi GlobalTheory.SplitWeil.om
    have hn1 : nabs k (1 : kˣ) = 1 := by unfold nabs; rw [map_one, NNReal.coe_one]
    simp only [map_one, inv_one, Units.val_one, hn1, Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.one_mul]
    rfl
  have muAt_one : muAt Ch sel mu cst s P 1 = 1 := by
    unfold muAt LocE.locChar
    rw [PsiStep.valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
    have h1 : IsUnit (redP P.1 (1 : X.E)) := by rw [PsiStep.reduction_one']; exact isUnit_one
    unfold LocE.unitV
    rw [dite_eq_left h1]
    have : h1.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, PsiStep.reduction_one', Units.val_one])
    rw [this, map_one, Units.val_one]
  rw [hL, hsc]
  unfold PsiAt omPhi Loc.om sgn
  simp only [map_one, Units.val_one, PsiStep.valuation_one₂, muAt_one, inv_one, mul_one, zero_mul, zpow_zero]
  have h1 : (LinearEquiv.symm (1 : AutY X R (s + 1))).toLinearMap ∘ₗ
      (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) =
        joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap := by
    ext v; rfl
  rw [h1]
  simp only [map_mul]
  ring
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

theorem _root_.GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E), IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  first | exact @GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul | exact GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul | (intros; apply GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul <;> assumption)
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.exists_pos_noShortIntegralVectorFromPoint : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  first | exact @GlobalTheory.CuspGeo.firstMin_pos | exact GlobalTheory.CuspGeo.firstMin_pos | (intros; apply GlobalTheory.CuspGeo.firstMin_pos <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.LastStepProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hat_coset_of_not [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

theorem topAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → TopAgree Ch sel mu cst σ₀ P ι S ν := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν hA e' e he' he
  refine ⟨1, one_ne_zero, fun y y' hy' => ?_⟩
  have hm : R.m = s + 2 := hA.steps
  have hT := hA.tie
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hT.compl.int
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hNpos : R.N R.m - 1 < R.N R.m := by have := (e (Sum.inr ())).isLt; omega

  have hq : (qOf P.1 : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
  set η' := atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hη'
  have hη'v : ∀ v, η' v = y v (e (Sum.inr ())) := fun v => by
    simp only [hη', LinearMap.comp_apply, atNL, dif_pos hNpos, LinearMap.proj_apply]
    rw [show (⟨R.N R.m - 1, hNpos⟩ : Fin (R.N R.m)) = e (Sum.inr ()) from Fin.ext hlast.symm]
  have hrow : (toLoc ι e e' y) (Sum.inr ()) = fun a => ι (η' (Pi.single (e' a) 1)) := by
    funext a; simp [toLoc, hη'v]
  have hsum : η' y' = ∑ i, y' i * η' (Pi.single i 1) := by
    have : y' = ∑ i, y' i • Pi.single i (1 : X.E) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [this]

    simp [map_sum, map_smul]
  have hdot : (fun a => ι (η' (Pi.single (e' a) 1))) ⬝ᵥ (fun a => ι (y' (e' a))) = ι (η' y') := by

    rw [hsum, map_sum, dotProduct]
    exact Fintype.sum_equiv e' _ _ (fun a => by simp [mul_comm])
  have hB : hat S.ψ ν (-1) (cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk fun a => ι (y' (e' a))))
      ((toLoc ι e e' y) (Sum.inr ())) = σ₀ (ftY sel mu cst P η' y') := by
    rw [hrow, ftY, if_pos hA.mem]
    by_cases hη : ∀ i : Fin (R.N (s + 1)), IntAt P.1 (η' (Pi.single i 1))
    · rw [if_pos hη, GlobalTheory.StepData.Model.hat_coset S.cond hν (neg_mem (one_mem _)) _
        (fun a => (hint _).2 (hη _)), hdot]
      have hi : IntAt P.1 ((qOf P.1 : X.E) * ((epsSg : X.E) * η' y')) := by
        rw [← hint, hsum]
        have : (qOf P.1 : X.E) * ((epsSg : X.E) * ∑ i, y' i * η' (Pi.single i 1)) =
            -∑ i, ((qOf P.1 : X.E) * y' i) * η' (Pi.single i 1) := by
          simp only [epsSg, Int.cast_neg, Int.cast_one, Finset.mul_sum]; ring_nf; simp [Finset.sum_neg_distrib]

        rw [this, map_neg, map_sum]
        exact neg_mem (sum_mem fun i _ => by rw [map_mul]; exact mul_mem ((hint _).2 (hy' i)) ((hint _).2 (hη i)))
      have h1 := hT.psi _ hi
      have h2 := hA.psi0 _ hi
      rw [mul_div_cancel_left₀ _ hq] at h1 h2
      rw [h2, ← h1]
      simp [epsSg]
    · rw [if_neg hη, map_zero]
      exact LastStepProof.hat_coset_of_not S.cond hν (by simp) _
        fun h => hη fun i => by simpa using (hint _).1 (h (e'.symm i))

  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  have hρ : R.rS = S.ρ := by have := S.odd; unfold Ranks.rS; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; omega
  have hN : R.N R.m - 1 = R.k + s + 1 + (s + 2) * R.t := by
    unfold Ranks.N; rw [hm]
    have : (s + 2) * (R.t + 1) = (s + 2) * R.t + (s + 2) := by ring
    omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) := fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrd (yPos xPos (R.N (s + 1))) E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hPT := GlobalTheory.T.lastStep_testFunctions_agree_rationalPoints X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hT R.t (R.N (s + 1))
    (cOf R (s + 1)) (R.N R.m - 1) rfl hc hN E1' E1 hE1' hE1
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  have hkey : ∀ c' n' c n : ℕ, LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t R.m c' n' c n =
      LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k S.ρ (R.k + s + 1) R.t (s + 2) c' n' c n := by
    intro c' n' c n; rw [hρ, hr, hm]
  have hA' : (S.T (Fin R.t)).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
      σ₀ (PhiTop Ch mu cst.sharp s P.1
        (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
    rw [hmat, hPT, PhiTop, if_pos hA.mem, hA.sharp, if_pos rfl, hkey]
  simp only [Chain.xiTop]
  rw [one_mul, map_mul, hA', hB]

end GlobalTheory.SymBridge.LastStepProof
end
end
