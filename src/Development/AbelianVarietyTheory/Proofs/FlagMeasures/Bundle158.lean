module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ColOfLeftInv
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle139
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalLiftOfIsotropic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField

noncomputable section

namespace GlobalTheory.StepDualityCompare

open Formalism.MainNotions.S GlobalTheory.Count

theorem totallyComplex (I : AutInst) : IsTotallyComplex I.E := I.cm.cmUnram.1

theorem frm_det (I : AutInst) (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  apply GlobalTheory.NearLowerCompare.frm_isUnit <;> assumption

theorem least_pos (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG) (h0 : lamX I x ≠ ⊥) : 0 < least I x := by
  have := totallyComplex I
  obtain ⟨-, -, -, h4, -⟩ := Formalism.HN.sizeMu I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (frm_det I x)
    (lamX I x) hfg h0
  unfold least
  rw [h4]
  exact Real.exp_pos _

private theorem fg_of_le_lamX (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG)
    {S : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : S ≤ lamX I x) : S.FG := by
  have : IsNoetherian (𝓞 I.E) (lamX I x) := isNoetherian_of_fg_of_noetherian _ hfg
  have : IsNoetherian (𝓞 I.E) S := isNoetherian_of_le h
  exact Module.Finite.iff_fg.mp inferInstance

theorem htQ_pos (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG) (S S' : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S) (hS' : S' ≤ lamX I x) (h : S ≤ S') :
    0 < Formalism.HN.htQ (bas I) (frm I x) S' S := by
  have := totallyComplex I
  obtain ⟨κ, _, _, b'', X'', hX'', -, hq⟩ := Formalism.HN.quotRealize I.E (Fin I.n → I.E) (Fin I.n) (bas I)
    (frm I x) (frm_det I x) (lamX I x) S hfg hS
  rw [(hq S' h hS').1]
  exact (Formalism.HN.plLat I.E _ κ b'' X'' hX'' _ ((fg_of_le_lamX I x hfg hS').map _)).2.2

end GlobalTheory.StepDualityCompare
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PiUnitary

open Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem ellA_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) {g h : Mat k r}
    (hg : col k r g) (hh : col k r h) (a : Fin r) :
    ellA k r z (g * h) a = ellA k r z g a + ellA k r z h a := by
  apply WlocSk.UnitaryGroupBasics.ellA_mul <;> assumption

theorem psiGen_mul_N (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hz : inWb k r z) {g h : Mat k r}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    psiGen k r z c (g * h) = psiGen k r z c g * psiGen k r z c h := by
  have hs : (∑ a, c a * ellA k r z (g * h) a) =
      (∑ a, c a * ellA k r z g a) + ∑ a, c a * ellA k r z h a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [ellA_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2 a, mul_add]
  unfold psiGen
  rw [hs, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖psiGen k r z c g‖ = 1 := by
  unfold psiGen
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ellA_block (z : Fin (2 * r + k + 1) → ℂ) {h h' g : Mat k r}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) (a : Fin r) :
    ellA k r z (h * g * h') a = ellA k r z g a := by
  unfold ellA
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dite_eq_left ha, dite_eq_left ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dite_eq_right ha, dite_eq_right ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

theorem psiGen_block (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {h h' g : Mat k r}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    psiGen k r z c (h * g * h') = psiGen k r z c g := by
  simp only [psiGen, ellA_block z hh hh' hz]

theorem block_one : block k r (1 : Mat k r) :=
  ⟨fun _ _ _ => Matrix.one_apply, fun _ _ _ => Matrix.one_apply⟩

theorem psiGen_uw_mul (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {h g : Mat k r}
    (hh : h ∈ UWset k r z) : psiGen k r z c (h * g) = psiGen k r z c g := by
  have := psiGen_block (g := g) z c (uw_block hh) block_one (Matrix.one_mulVec z)
  rwa [Matrix.mul_one] at this

theorem ellA_continuous (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous (fun g : Mat k r => ellA k r z g a) := by
  by_cases h : a.val + 1 < r
  · have e : (fun g : Mat k r => ellA k r z g a) =
        fun g => g (eI k r a) (eI k r ⟨a.val + 1, h⟩) := by
      funext g; unfold ellA; rw [dite_eq_left h]
    rw [e]
    exact (continuous_apply _).comp (continuous_apply _)
  · have e : (fun g : Mat k r => ellA k r z g a) = fun g => (g *ᵥ z) (eI k r a) := by
      funext g; unfold ellA; rw [dite_eq_right h]
    rw [e]
    exact (continuous_apply (eI k r a)).comp
      (continuous_id.matrix_mulVec continuous_const : Continuous fun g : Mat k r => g *ᵥ z)

theorem psiGen_continuous (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (psiGen k r z c) := by
  unfold psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ =>
      continuous_const.mul (ellA_continuous z a)))))

theorem block_entry {h : Mat k r} (hh : block k r h) {i j : Fin (2 * r + k + 1)}
    (H : ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k))) :
    h i j = if i = j then 1 else 0 := by
  by_cases hj : j.val < r ∨ r + k < j.val
  · exact hh.1 i j hj
  · exact hh.2 i j (by omega)

theorem hPart_mul {z : Fin (2 * r + k + 1) → ℂ} {h m : Mat k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) : hPart k r (h * m) = h := by
  have hb := uw_block hh
  have hc := ((nset_iff m).1 hm).2
  ext i j
  unfold hPart
  by_cases H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [if_pos H1]
    exact block_mul_col hb hc i j H1.2.2 (Or.inr H1.1.1)
  · rw [if_neg H1, block_entry hb H1]

theorem PiS_mul {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (ψ : Mat k r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) {z : Fin (2 * r + k + 1) → ℂ} {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) : PiS ψ π (h * m) = ψ m • π h := by
  unfold PiS
  rw [hPart_mul hh hm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hh.1), Matrix.one_mul]

theorem hPart_continuous : Continuous (hPart k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun s : Mat k r => hPart k r s i j
  by_cases H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · simp only [hPart, if_pos H1]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp only [hPart, if_neg H1]
    exact continuous_const

theorem adjoint_eq_of_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A B : E →L[ℂ] E) (hA : ∀ v, ‖A v‖ = ‖v‖) (hAB : A.comp B = 1) :
    ContinuousLinearMap.adjoint A = B := by
  have h1 : (ContinuousLinearMap.adjoint A).comp A = 1 := (A.norm_map_iff_adjoint_comp_self).1 hA
  ext v
  have e1 := congrArg (fun T : E →L[ℂ] E => T (B v)) h1
  have e2 := congrArg (fun T : E →L[ℂ] E => T v) hAB
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2
  rw [e2] at e1
  exact e1

end GlobalTheory.SgInf.PiUnitary

namespace GlobalTheory.SgInf.PiUnitary

open Formalism.QuantumDeterminants.WeylGroupFacts

theorem piS_unitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → IsURepOn (UWset k r z) π →
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, hPart k r (h * m) = h ∧
        PiS (psiGen k r z c) π (h * m) = psiGen k r z c m • π h) ∧
      IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) ∧
      (∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 ∧
        ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) = PiS (psiGen k r z c) π s⁻¹) ∧
      ContinuousOn (PiS (psiGen k r z c) π) (Sset k r z) ∧
      (∀ m ∈ Nset k r, ‖psiGen k r z c m‖ = 1 ∧
        ∀ m' ∈ Nset k r, psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m') := by
  intro k r Wp _ _ _ _ z c π hz _ hπ
  have hchar : ∀ m ∈ Nset k r, ‖(psiGen k r z c) m‖ = 1 ∧ ∀ m' ∈ Nset k r, (psiGen k r z c) (m * m') = (psiGen k r z c) m * (psiGen k r z c) m' :=
    fun m hm => ⟨norm_psiGen z c m, fun m' hm' => psiGen_mul_N z c hz hm hm'⟩
  have hpsi1 : (psiGen k r z c) 1 = 1 := by
    have e := psiGen_mul_N z c hz (mem_n_one (k := k) (r := r)) (mem_n_one (k := k) (r := r))
    rw [Matrix.one_mul] at e
    have hne : (psiGen k r z c) 1 ≠ 0 := by
      intro h0
      have := norm_psiGen (k := k) (r := r) z c 1
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have e' : (psiGen k r z c) 1 * 1 = (psiGen k r z c) 1 * (psiGen k r z c) 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ hne e').symm
  have hrep : IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [PiS_one, hpsi1, one_smul]
      exact hπ.1.1
    · rintro _ ⟨h, hh, m, hm, rfl⟩ _ ⟨h', hh', m', hm', rfl⟩
      have hu' := isUnit_of_uh hh'.1
      have hn : h'⁻¹ * m * h' ∈ Nset k r := by
        have := (uWNormal k r z hz h'⁻¹ (uw_inv hh') m hm).1
        rwa [Matrix.nonsing_inv_nonsing_inv _ hu'] at this
      have e : h * m * (h' * m') = (h * h') * ((h'⁻¹ * m * h') * m') := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc h' h'⁻¹, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul]
      rw [e, PiS_mul (psiGen k r z c) π (uw_mul hh hh') (mem_n_mul hn hm'), PiS_mul (psiGen k r z c) π hh hm, PiS_mul (psiGen k r z c) π hh' hm',
        psiGen_mul_N z c hz hn hm',
        psiGen_block z c (uw_block (uw_inv hh')) (uw_block hh') hh'.2.2, hπ.1.2 h hh h' hh',
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
    · rintro _ ⟨h, hh, m, hm, rfl⟩ v
      rw [PiS_mul (psiGen k r z c) π hh hm, ContinuousLinearMap.smul_apply, norm_smul, norm_psiGen, one_mul,
        hπ.2.1 h hh v]
    · intro v
      have hmaps : Set.MapsTo (hPart k r) (Sset k r z) (UWset k r z) := by
        rintro _ ⟨h, hh, m, hm, rfl⟩
        rw [hPart_mul hh hm]
        exact hh
      have hc : ContinuousOn (fun s => (psiGen k r z c) s • π (hPart k r s) v) (Sset k r z) :=
        (psiGen_continuous z c).continuousOn.smul
          ((hπ.2.2 v).comp hPart_continuous.continuousOn hmaps)
      refine hc.congr ?_
      rintro _ ⟨h, hh, m, hm, rfl⟩
      show PiS (psiGen k r z c) π (h * m) v = (psiGen k r z c) (h * m) • π (hPart k r (h * m)) v
      rw [PiS_mul (psiGen k r z c) π hh hm, hPart_mul hh hm, psiGen_uw_mul z c hh, ContinuousLinearMap.smul_apply]
  have hiso : ∀ s ∈ Sset k r z, ∀ v, ‖PiS (psiGen k r z c) π s v‖ = ‖v‖ := hrep.2.1
  refine ⟨fun h hh m hm => ⟨hPart_mul hh hm, PiS_mul (psiGen k r z c) π hh hm⟩, hrep, fun s hs => ⟨?_, ?_⟩, ?_, hchar⟩
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hiso s hs v, one_mul]
  · apply adjoint_eq_of_isometry _ _ (hiso s hs)
    have hsU : s ∈ UH (Hpk k r) := by
      obtain ⟨h, hh, m, hm, rfl⟩ := hs
      exact uh_mul hh.1 hm.1
    have hsi : s⁻¹ ∈ Sset k r z := (sGroup k r z hz).2.2 s hs
    rw [← hrep.1.2 s hs s⁻¹ hsi, Matrix.mul_nonsing_inv _ (isUnit_of_uh hsU)]
    exact hrep.1.1
  · exact continuousOn_clm_apply.2 hrep.2.2

end GlobalTheory.SgInf.PiUnitary
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LatticeContDensity

theorem contDensity_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v → ∀ ψ : AddChar (Fv F v) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsLocalChar v ψ → ∀ n : ℤ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.DualExponent v ψ n → ∀ L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L → ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), SdW F E σ M J (Fv F v) ψ 1 μ → SdR (Fv F v) ψ ν → ∀ g : Fv F v → ℂ, IsContDensityOn μ (fun X => qR (Fv F v) σ J (X 0)) id ν {c | c ≠ 0} ({X | X 0 ∈ L}.indicator 1) g → ∀ β : Fv F v, Valued.v β = 1 → g β = (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) * (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ hσ M hM J hJ v hv ψ hψ n hn L hL μ ν hμ hν g hg β hβ

  have H : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.SelfDualLatticeDensity :=
    GlobalTheory.LocalDensityCompare.localDensity_iff.1
      (GlobalTheory.LatticeDensity.localDensity_of_selfDualLatticeLemmas
        GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas)
  obtain ⟨η, hη⟩ := GlobalTheory.LocalDensityCompare.exists_eta F E v
  have hEta : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsEtaAt F E v η :=
    (GlobalTheory.LocalDensityCompare.isEtaAt_iff F E v hσ.2.2.1 η).2 ⟨hv, hη⟩
  have key := (H F E σ hσ M J hM hJ v η hEta ψ hψ).2 n hn L
    ((GlobalTheory.LocalDensityCompare.isSelfDualLattice_iff v σ J L).1 hL) μ hμ ν hν

  have hβ' : Valued.v (β - β) < 1 := by simp
  have hgβ := (key.2.2 β hβ).2 g hg β hβ'
  rw [hgβ, ← GlobalTheory.LocalDensityCompare.dens_eq v n M η hη]

end GlobalTheory.LatticeContDensity
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.cm_euler_product_discr_unramified : ∀ (I : AutInst) (M : ℕ), 2 ≤ M → HasProd (fun u : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) => 1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta I.F I.E u ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ M)⁻¹) (Formalism.HermitianLatticesTheory.lValEta I.E M)⁻¹ ∧ |(discr I.F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ I.f ∧ ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace I.F I.E u := by
  first | exact @GlobalTheory.DensityEuler.euler_product_discr_unramified | exact GlobalTheory.DensityEuler.euler_product_discr_unramified | (intros; apply GlobalTheory.DensityEuler.euler_product_discr_unramified <;> assumption)
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  first | exact @GlobalTheory.NilLift.exists_nilInt_lift | exact GlobalTheory.NilLift.exists_nilInt_lift | (intros; apply GlobalTheory.NilLift.exists_nilInt_lift <;> assumption)
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), (∀ v, spanAt I R v = Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E)))) ∧ (∀ v, spanAt I (lamX I x) v = ⊤) ∧ (∀ v, (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) = perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v)) ∧ (∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ nilReal I R) ∧ ∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ cenReal I R := by
  first | exact @GlobalTheory.RealSpan.spanAt_properties | exact GlobalTheory.RealSpan.spanAt_properties | (intros; apply GlobalTheory.RealSpan.spanAt_properties <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff ENNReal

namespace GlobalTheory.NearMeas

theorem tsum_sub_eq {G : Type} (S T : Set G) (h : S ⊆ T) (f : G → ℝ≥0∞) :
    ∑' γ : S, f γ.1 = ∑' γ : T, S.indicator f γ.1 := by
  rw [tsum_subtype S f, tsum_subtype T (S.indicator f), Set.indicator_indicator,
    Set.inter_eq_right.mpr h]

private theorem continuous_ph' (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    Continuous (ph B d) := by
  show Continuous fun g : B.I.Ginf =>
    ((∏ v, d v : ℝ) : ℂ) * star (∏ v, ⟪B.w v, B.σ v (uMat (g v)) (B.w v)⟫_ℂ)
  refine continuous_const.mul (continuous_star.comp (continuous_finsetProd _ fun v _ => ?_))
  obtain ⟨-, ⟨-, -, ⟨-, -, hcont⟩, -⟩, -⟩ := h v
  have hmat : Continuous fun g : B.I.Ginf => uMat (g v) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
  have hc : Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) :=
    (hcont (B.w v)).comp_continuous hmat fun g => (g v).2
  exact continuous_const.inner hc

theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    Continuous (phe B d) := by
  obtain ⟨hlc, -⟩ := B.e_adm
  show Continuous fun x : B.I.GA => ph B d x.1 * B.e x.2
  exact ((continuous_ph' B d h).comp continuous_fst).mul (hlc.continuous.comp continuous_snd)

private theorem continuous_conj_by_inv (B : RowsAut) (γ : B.I.GA) :
    Continuous fun x : B.I.GA => x⁻¹ * γ * x :=
  (continuous_inv.mul continuous_const).mul continuous_id

private theorem measurable_indicator_nearNe_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d)
    (γ : B.I.GA) :
    Measurable fun x : B.I.GA =>
      {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator
        (fun x => ‖phe B d (x⁻¹ * γ * x)‖ₑ) x := by
  have hc : Continuous fun x : B.I.GA => phe B d (x⁻¹ * γ * x) :=
    (continuous_phe B d h).comp (continuous_conj_by_inv B γ)
  have hd : ∀ v, Continuous fun x : B.I.GA => dHS (uMat ((x⁻¹ * γ * x).1 v)) := fun v =>
    (GlobalTheory.Count.CartanSize.cartan_size _ (B.I.ε v)).1.comp
      ((continuous_apply v).comp (continuous_fst.comp (continuous_conj_by_inv B γ)))
  have hcl : IsClosed {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le (hd v) continuous_const
  have hne : MeasurableSet {x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} :=
    hc.measurable (measurableSet_singleton 0).compl
  have hset : MeasurableSet {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} := by
    have heq : {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} =
        ({x : B.I.GA | γ ∈ B.I.GFset} ∩ ({x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} ∩
          {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B})) ∩ {x : B.I.GA | γ ≠ 1} := by
      ext x
      rfl
    rw [heq]
    exact ((MeasurableSet.const _).inter (hne.inter hcl.measurableSet)).inter (MeasurableSet.const _)
  exact Measurable.indicator hc.enorm.measurable hset

theorem nearAbs_measurable_and_split : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → Measurable (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) ∧ ∀ x : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * x)‖) → ENNReal.ofReal ‖kern B.I (phe B d) x x - phe B d 1‖ ≤ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by
  intro B d h
  classical
  refine ⟨?_, ?_⟩
  · have hcount : Countable B.I.GFset := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    have heq : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d = fun x => ∑' γ : B.I.GFset,
        {x : B.I.GA | γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator
          (fun x => ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ) x := by
      funext x
      exact tsum_sub_eq (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x) B.I.GFset (fun γ hγ => hγ.1.1)
        (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)
    rw [heq]
    exact Measurable.tsum fun γ => measurable_indicator_nearNe_phe B d h γ.1
  · intro x hsum
    have hone : (1 : B.I.GA) ∈ B.I.GFset := (GlobalTheory.RatDiscrete.ratSub B.I).one_mem
    let o : B.I.GFset := ⟨1, hone⟩
    have hs : Summable fun γ : B.I.GFset => phe B d (x⁻¹ * γ.1 * x) := hsum.of_norm
    have hk : kern B.I (phe B d) x x = ∑' γ : B.I.GFset, phe B d (x⁻¹ * γ.1 * x) := rfl
    have h1 : phe B d 1 = phe B d (x⁻¹ * o.1 * x) := by simp [o]
    rw [hk, h1, hs.tsum_eq_add_tsum_ite o, add_sub_cancel_left]
    have hgn : Summable fun γ : B.I.GFset =>
        ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖ := by
      refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun γ => ?_
      by_cases hγ : γ = o <;> simp [hγ]
    have hsub1 : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x ⊆ B.I.GFset := fun γ hγ => hγ.1.1
    have hsub2 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x ⊆ B.I.GFset := fun γ hγ => hγ.1
    calc ENNReal.ofReal ‖∑' γ : B.I.GFset, if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖
        ≤ ENNReal.ofReal (∑' γ : B.I.GFset,
            ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hgn)
      _ = ∑' γ : B.I.GFset, ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hgn]
          simp only [ofReal_norm]
      _ ≤ ∑' γ : B.I.GFset,
            ((GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x).indicator (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1 +
              (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x).indicator
                (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1) := by
          refine ENNReal.tsum_le_tsum fun γ => ?_
          by_cases hγ : γ = o
          · simp [hγ]
          have hγ1 : γ.1 ≠ 1 := fun h' => hγ (Subtype.ext h')
          rw [if_neg hγ]
          by_cases hn : IsNear B d (epN B) x γ.1
          · have hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x := ⟨hn, hγ1⟩
            rw [Set.indicator_of_mem hm]
            exact le_self_add
          · have hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x := ⟨γ.2, hn⟩
            rw [Set.indicator_of_mem hm]
            exact le_add_self
      _ = GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by
          rw [ENNReal.tsum_add]
          exact congrArg₂ (· + ·)
            (tsum_sub_eq _ _ hsub1 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm
            (tsum_sub_eq _ _ hsub2 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm

end GlobalTheory.NearMeas
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic : ∀ (n : ℕ) (ε : Fin n → Bool) (H G D : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)), IsUnit G.det → Gᴴ * H * G = Jm ε → (∀ u ∈ W, u ∈ perpSet (starRingEnd ℂ) H W) → (∀ u ∈ W, D *ᵥ u = 0) → (∀ u ∈ perpSet (starRingEnd ℂ) H W, D *ᵥ u ∈ W) → ∃ A : Matrix (Fin n) (Fin n) ℂ, InNil (starRingEnd ℂ) H W A ∧ (∀ u ∈ perpSet (starRingEnd ℂ) H W, A *ᵥ u = D *ᵥ u) ∧ hs (G⁻¹ * A * G) ≤ 2 * hs (G⁻¹ * D * G) := by
  first | exact @GlobalTheory.NilLift.exists_lift | exact GlobalTheory.NilLift.exists_lift | (intros; apply GlobalTheory.NilLift.exists_lift <;> assumption)
end
