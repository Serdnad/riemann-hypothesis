module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle876
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle911
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle884
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle896
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle895
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle823
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import GroundTheory.AutomorphicForms.Bundle012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle908
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle875
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle806
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle814
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle907
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProduct
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
open GlobalTheory.MirTower GlobalTheory.CuspGeneric GlobalTheory.RSJ GlobalTheory.ZUnf in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  intro E _ _ _ m μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ' N Φ _hN hΦs _hΦc hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x _hx h1 h2
  have := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  have := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  have := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    have : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  obtain ⟨hc, hl, hv⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π ω hω hπ φ hφ
  obtain ⟨hc', hl', hv'⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π' ω' hω' hπ' φ' hφ'
  have hΦcont : Continuous Φ := hΦs.continuous
  have hG := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ hc hl hv Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  have hG' := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ' hc' hl' hv' Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  obtain ⟨hwm, hwΓ, hwU⟩ := GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant E m N x
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (wt N x) hwm hwΓ hwU
  have hW : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform E m f hf.cont (fun γ hγ g => hf.left γ (isMir_of_mem_mirU_zero hγ) g) g
  have hd : ∫⁻ g in 𝓕P, ‖fT φ Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG]
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG]
    simp only [e]
    exact h1
  have hd' : ∫⁻ g in 𝓕P, ‖fT φ' Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG']
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG']
    simp only [e]
    exact h2
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 _ _ hG hG' hd hd'
  have e1 : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g) * ((wt N x g : ℝ) : ℂ) := by
    funext g
    rw [uInt_eq hΦp, hW _ hG, hW _ hG']
  have e2 : (fun g => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)) =
      fun g => fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ) := funext fun g => psi_lastRow_eq hΦp φ φ' N x g
  have hfin : ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ := by
    rw [show (fun g => ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ) =
      fun g => ‖fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ)‖ₑ from funext fun g => by rw [psi_lastRow_eq hΦp]]
    exact hI1.2.ne
  refine ⟨by rw [e1]; exact hI2, ?_⟩
  have hUnfold := GlobalTheory.ZUnfTheta.zint_eq_mirabolic E m μ 𝓕 𝓕P h𝓕 h𝓕P
    φ φ' hc.measurable hc'.measurable hl hl' N Φ hΦcont x hfin
  rw [hUnfold, e2, Complex.ofReal_one, one_mul, e1]
  exact hEq
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical

namespace GlobalTheory.RamShift

theorem whittaker_torusShift_add_factorisation_induction (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ)
    (hα : ∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) (φ) (hφV : φ ∈ π.V)
    (hφ : ∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (x : GA E (m + 1)) (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T) (L : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)) :
    (∀ w ∈ T, L w = 0) → (∀ w, 0 ≤ L w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((shift m T ϖ).1 + L)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (shift m T ϖ).1) *
          ∏ w ∈ L.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (L w)) := by
  induction L using Finsupp.induction with
  | zero => intro _ _; simp
  | single_add a b f ha hb ih =>
    intro hT hlast
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have haT : a ∉ T := fun h => hb (by simpa [hfa] using hT a h)
    have hfT : ∀ w ∈ T, f w = 0 := fun w hw => by
      have hne : a ≠ w := fun e => haT (e ▸ hw)
      simpa [Finsupp.single_apply, hne] using hT w hw
    have hflast : ∀ w, 0 ≤ f w (Fin.last m) := fun w => by
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simpa [Finsupp.single_apply, hw] using hlast w
    have hblast : 0 ≤ b (Fin.last m) := by simpa [hfa] using hlast a
    set l₀ := (shift m T ϖ).1 with hl₀
    have hsplit : l₀ + (Finsupp.single a b + f) =
        (l₀ - Finsupp.single a (l₀ a) + f) + Finsupp.single a (l₀ a + b) := by
      ext w i
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simp [Finsupp.single_apply, hw]
    have hjoin : (l₀ - Finsupp.single a (l₀ a) + f) + Finsupp.single a (l₀ a) = l₀ + f := by
      ext w i
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simp [Finsupp.single_apply, hw]
    set g := x * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀ - Finsupp.single a (l₀ a) + f) with hg
    have hga : GeneralLinearGroup.map ((pLoc E a).comp (pFin E)) g = 1 := by
      change GlobalTheory.CellDec.compV E (m + 1) a g = 1
      rw [hg, map_mul, GlobalTheory.CellDec.compV_tl]
      have h0 : (l₀ - Finsupp.single a (l₀ a) + f) a = 0 := by simp [hfa]
      have hxa : GlobalTheory.CellDec.compV E (m + 1) a x = 1 := hx a haT
      rw [h0, hxa, GlobalTheory.IwaCell.tD_zero, one_mul]
    have hl₀a : l₀ a = fun i : Fin (m + 1) => condExp ϖ a * ((m : ℤ) - ((i : ℕ) : ℤ)) :=
      shift_apply_of_notMem m ϖ haT
    have key := GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter E m π a (α ⟨a, haT⟩) (hα ⟨a, haT⟩) φ hφV (hφ a haT) (ϖ a) (hϖ a) (condExp ϖ a)
      (GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent E ϖ a (hϖ a)) g hga b hblast
    have h1 : l₀ a + b = fun i : Fin (m + 1) => condExp ϖ a * ((m : ℤ) - ((i : ℕ) : ℤ)) + b i := by
      rw [hl₀a]; rfl
    rw [hsplit, GlobalTheory.CellDec.tl_add, GlobalTheory.CellDec.tl_single, ← mul_assoc, ← hg, h1, key, ← hl₀a,
      ← GlobalTheory.CellDec.tl_single, hg, mul_assoc, ← GlobalTheory.CellDec.tl_add, hjoin, ih hfT hflast,
      Finsupp.support_single_add ha hb, Finset.prod_cons, dite_eq_right haT]
    have hval : (Finsupp.single a b + f) a = b := by simp [hfa]
    have hrest : ∏ w ∈ f.support, (if h : w ∈ T then 1 else
          GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) ((Finsupp.single a b + f) w)) =
        ∏ w ∈ f.support, (if h : w ∈ T then 1 else
          GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (f w)) := by
      refine Finset.prod_congr rfl fun w hw => ?_
      have hne : a ≠ w := fun e => ha (e ▸ hw)
      simp [Finsupp.single_apply, hne]
    rw [hval, hrest]
    change GlobalTheory.RSCell.sphZ (Ideal.absNorm a.asIdeal) _ b * _ = _
    ring

theorem whit_mul_tl_shift_add : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((GlobalTheory.RamShift.shift m T ϖ).1 + l.1)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  intro E _ _ _ m T π α hα φ hφV hφ ϖ hϖ x hx l hl
  exact whittaker_torusShift_add_factorisation_induction E m T π α hα φ hφV hφ ϖ hϖ x hx l.1 l.2 hl

end GlobalTheory.RamShift
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.RealFockVac

theorem om_stdF_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∀ a ∈ GinfC V, ∀ u : GlobalTheory.ExportSeries.GLR D V.rank,
    (∀ τ, ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)) →
    ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
    ∀ P : MvPolynomial (FVar D W.rank V.rank) ℂ,
      om (a, 1) (stdF ψ θ V W sW BW f P) =
        stdF ψ θ V W sW BW (om (a, 1) f) (GlobalTheory.ExportSeries.fockSubst (fun _ => p) u P) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP p BW hBW a ha u hu f hf _ P
  obtain ⟨hPr, -, -, -, -, -, -, hT, -⟩ := hP
  have hom := hPr.weil
  have hθ : IsInfFam θ := hPr.inf
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one _ _
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) 1 := GlobalTheory.SmoothVac.isCartanInv_one V hPr.std
  have hG : ∀ τ, gramAt D V τ = 1 := fun τ => by
    rw [gramAt, hPr.std, Matrix.map_one _ (map_zero _) (map_one _)]
  have hun : ∀ τ, ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈
      Matrix.unitaryGroup (Fin V.rank) ℂ := fun τ => by
    rw [hu τ]
    have h1 : (compAt θ τ (Formalism.L2.Theta.mt V a))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V a) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
    rw [hG, Matrix.mul_one] at h1
    exact Matrix.mem_unitaryGroup_iff'.2 h1
  have ht : ∀ τ, sW τ * BW τ = BW τ * diagonal fun b : Fin W.rank =>
      if decide (b.val < (fun _ => p) τ) = true then (1 : ℂ) else -1 := fun τ => by
    obtain ⟨ε, hε, -, h2⟩ := hBW τ
    have e : (fun b => (ε b : ℂ)) = fun b : Fin W.rank => if decide (b.val < p) = true then (1 : ℂ) else -1 :=
      funext fun b => by
        rcases hε b with h | h
        · simp [h.1, h.2]
        · simp [h.1, not_lt.2 h.2]
    rw [e] at h2
    exact h2
  have hBT : (fun τ => compAt θ τ (Formalism.L2.Theta.mt W 1) * BW τ) = BW := funext fun τ => by rw [one, Matrix.one_mul]
  show om (a, 1) (pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW f P) =
    pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW (om (a, 1) f) (GlobalTheory.ExportSeries.fockSubst (fun _ => p) u P)
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hom hθ (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun τ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) * ((u τ : GL (Fin V.rank) ℂ) : Matrix _ _ ℂ)) sW sW BW
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt W 1) * BW τ) a 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hu τ, Matrix.one_mul, Matrix.mul_one]) (fun τ => rfl) f hf P).2, hBT]
  exact GlobalTheory.RealFockAction.pureTensorO_subst hom.std hθ hS hT ht (fun _ => 1) u hun (hom.om_pres _ _ hf) P

end GlobalTheory.RealFockVac
end

section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_add (F G : GA E a → ℂ) (g : GA E a) : chart (F + G) g = chart F g + chart G g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_smul (z : ℂ) (F : GA E a → ℂ) (g : GA E a) : chart (z • F) g = z • chart F g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_zero (g : GA E a) : chart (0 : GA E a → ℂ) g = 0 := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem kSpan_diff : ∀ F ∈ kSpan E a, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a) := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    obtain ⟨L, hL, -⟩ := GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator E a G X ν k γ hk hG g u
    exact hL.differentiableAt.differentiableWithinAt
  | zero => intro g; rw [chart_zero]; exact differentiableOn_const 0
  | add F G _ _ hF hG => intro g; rw [chart_add]; exact (hF g).add (hG g)
  | smul z F _ hF => intro g; rw [chart_smul]; exact (hF g).const_smul z

theorem differentiableAt_one_of_mem {F : GA E a → ℂ} (hF : F ∈ kSpan E a) (g : GA E a) :
    DifferentiableAt ℝ (chart F g) (oneL E a) :=
  (kSpan_diff F hF g).differentiableAt (isOpen_invSet.mem_nhds isUnit_one)

theorem kSpan_lie : ∀ F ∈ kSpan E a, ∀ Y : Lie E a, lieD Y F ∈ kSpan E a := by
  intro F hF Y
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    have e : lieD Y (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) = fun g : GA E a =>
        ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν := by
      funext g
      obtain ⟨L, hL, hZ⟩ := GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator E a G X ν k γ hk hG g 1
      have e1 : toL (1 : GL (Fin a) (Cinf E)).val = oneL E a := rfl
      rw [lieD, ← e1, hL.fderiv, hZ Y]
      simp
    rw [e]
    exact GlobalTheory.T.rapidKernel_integral_conjLieDerivative_mem_span E a G X ν k γ Y hk hG
  | zero =>
    have e : lieD Y (0 : GA E a → ℂ) = 0 := by
      funext g; simp [lieD, chart_zero]
    rw [e]; exact zero_mem _
  | add F G hF' hG' hF hG =>
    have e : lieD Y (F + G) = lieD Y F + lieD Y G := by
      funext g
      simp only [lieD, chart_add, Pi.add_apply]
      rw [fderiv_add (differentiableAt_one_of_mem hF' g) (differentiableAt_one_of_mem hG' g)]
      rfl
    rw [e]; exact add_mem hF hG
  | smul z F hF' hF =>
    have e : lieD Y (z • F) = z • lieD Y F := by
      funext g
      simp only [lieD, chart_smul, Pi.smul_apply]
      rw [fderiv_const_smul (differentiableAt_one_of_mem hF' g)]
      rfl
    rw [e]; exact Submodule.smul_mem _ z hF

theorem kSpan_le_Sm : kSpan E a ≤ Sm E a := GlobalTheory.T.le_smooth_of_chartDifferentiable_lieDerivStable E a _ kSpan_diff kSpan_lie

theorem kSpan_decays_growth : ∀ F ∈ kSpan E a, GlobalTheory.ShortVecDecay.Decays F ∧ Growth F := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    exact ⟨GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator E a G X ν k γ hk hG.decays, GlobalTheory.T.moderateGrowth_rapidKernelOperator E a G X ν k γ hk hG.growth⟩
  | zero => exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩
  | add F G _ _ hF hG => exact ⟨hF.1.add hG.1, hF.2.add hG.2⟩
  | smul z F _ hF => exact ⟨hF.1.smul z, hF.2.smul z⟩

theorem word_mem_kSpan (l : List (Lie E a)) (φ : Sm E a) (hφ : φ.1 ∈ kSpan E a) :
    (GlobalTheory.GLFin.word l φ).1 ∈ kSpan E a := by
  induction l with
  | nil => simpa [GlobalTheory.GLFin.word] using hφ
  | cons Y l ih => rw [word_cons]; exact kSpan_lie _ ih Y

theorem Good.kernel {G : GA E a → ℂ} (hG : Good G) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : GlobalTheory.JSW.IsRapidInf ν k γ) :
    Good (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) := by
  have hm : (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) ∈ kSpan E a :=
    Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, k, γ, G, hk, hG, rfl⟩
  exact ⟨kSpan_le_Sm hm, fun l => kSpan_decays_growth _ (word_mem_kSpan l _ hm)⟩


variable (E a) in
def goodSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Good F}
  add_mem' := Good.add
  zero_mem' := good_zero
  smul_mem' c _ h := h.smul c

theorem mspanR_le_goodSub {π : CuspSub E a} (hπ : π.IsUnitary) : GlobalTheory.JSW.mspanR π ≤ goodSub E a :=
  sInf_le ⟨fun φ hφ => good_of_mem hπ hφ, fun F hF h => GlobalTheory.T.goodSmoothDecayModerateGrowth_rightTranslate E a F h hF,
    fun F hF X _ ν _ k γ hk => Good.kernel (G := F) hF hk⟩

theorem norm_le_of_short_vector_mspanR : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  intro E _ _ _ a π hπ φ hφ l
  have hg : Good φ.1 := hφ.elim (good_of_mem hπ) fun h => mspanR_le_goodSub hπ h
  obtain ⟨h, hl⟩ := hg
  exact (hl l).1

end GlobalTheory.MSpanDecay
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_locBall_of_mem_MK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j f hf
  intro z
  obtain ⟨hwk, hb⟩ := ((YS.fi j).mkK _).1 hf
  obtain ⟨T, io, k, hk, y, u, hy, hu, hval⟩ := PtC.exists_valC z (wtA (κ j)) (κ j).n
  obtain ⟨e, ho⟩ := GlobalTheory.ReadingOver.overLa_placeAt _ _ (embC YS iC b) T io k hk
  let v : T0.PtM ((j : ℕ) + 1) (placeC YS iC b) :=
    ⟨vAtV (PtV.mk (cls := algCls (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c) (PY := Unit) (lies := fun _ _ _ _ => True)
      (placeC YS iC b) ho y hy () trivial), ⟨_, rfl⟩⟩
  obtain ⟨w, hw⟩ := (fw.pt j (placeC YS iC b)).surjective v
  have h1 := hb (placeC YS iC b) w
  have e1 : (⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, hwk⟩ : (Rl.FW j).WK) = fw.e j (cuspOf YS fw j f) :=
    Subtype.ext (e_cuspOf YS fw j f).symm
  rw [e1, fw.nrm_eq, hw] at h1
  have h2 := (T0.nrmM_le_one_iff _ _ v _).1 h1
  have h3 := (GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1 (evI y (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)))).2 h2
  rw [hval _ (cuspOf_mem_sec YS fw j f), norm_mul, hu, one_mul]
  exact (hk.int _).2 h3

end GlobalTheory.GeoTie
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate


theorem _root_.GlobalTheory.T.integral_det_le_one_eq_geometric_series_shells : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ (F : GA E a → ℂ), Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → ∀ χ : ℂ, ‖χ‖ = 1 → (∀ g, F (splitCentre E a 1 * g) = χ * F g) → ∀ s : ℂ, 1 < s.re → ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ = (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) / (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  first | (exact @GlobalTheory.RSThetaGeom.integral_low_geometric) | (exact GlobalTheory.RSThetaGeom.integral_low_geometric) | (intros; apply GlobalTheory.RSThetaGeom.integral_low_geometric  <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.tendsto_residueTerm_rankinSelberg_innerProduct : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∀ F : GA E a → ℂ, Continuous F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → (∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g) → Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1 : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 ((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) := by
  first | exact @GlobalTheory.RSThetaRes.residue_geometric | exact GlobalTheory.RSThetaRes.residue_geometric | (intros; apply GlobalTheory.RSThetaRes.residue_geometric <;> assumption)
end
