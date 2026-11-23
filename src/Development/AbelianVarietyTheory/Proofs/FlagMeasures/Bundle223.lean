module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle125
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle176
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle198
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeMiddleLatticeHomLatticeIdeal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfIsotropicBlocks
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle209
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle210
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ReproducingFixed

theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  unfold rkR
  set A := univ.filter fun a => ε a = true
  set A' := univ.filter fun a => ε a = false
  have h1 := Finset.card_union_add_card_inter A A'
  have h2 : A ∩ A' = ∅ := by
    ext a
    simp [A, A']
  have h3 := Finset.card_le_univ (A ∪ A')
  rw [h2, Finset.card_empty] at h1
  rw [Fintype.card_fin] at h3
  omega

theorem weight_condition (B : RowsAut) (h s : ℝ) (hn : 1 ≤ B.I.n) (hb : HBig B 40 h)
    (hs : s ≤ 2 * (B.I.n : ℝ) ^ 2) (v : InfinitePlace B.I.F) :
    rkR (B.I.ε v) = 0 ∨ 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) < h := by
  by_cases hq : rkR (B.I.ε v) = 0
  · exact Or.inl hq
  right
  have h2 := two_mul_rank_le (B.I.ε v)
  have hq1 : (1 : ℝ) ≤ (rkR (B.I.ε v) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have h2r : 2 * (rkR (B.I.ε v) : ℝ) ≤ B.I.n := by exact_mod_cast h2
  have hnr : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.mpr (by linarith)
  have hbv := hb v
  unfold HBig at hbv
  have key : s + 4 * B.I.n * rkR (B.I.ε v) ≤ 4 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have hle : 8 * Real.sqrt (rkR (B.I.ε v)) * (s + 4 * B.I.n * rkR (B.I.ε v)) ≤
      32 * (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by nlinarith
  have hpos : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
  linarith

theorem inv_tau_pow_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    (tau1 I (x * g))⁻¹ ^ (2 * I.n ^ 2 * I.f) ≤
      (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * dSum I g.1) := by
  have ha := GlobalTheory.TauLipschitz.trunc_pos I hn x
  have hb := GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)
  have hl := GlobalTheory.TauLipschitz.log_trunc_le I hn x g hg
  have hf : (0 : ℝ) < I.f := by
    have : 0 < I.f := by
      unfold AutInst.f
      exact Module.finrank_pos
    exact_mod_cast this
  set D := dSum I g.1
  have h1 : tau1 I x * Real.exp (-(D / I.f)) ≤ tau1 I (x * g) := by
    have := Real.exp_le_exp.mpr hl
    rw [Real.exp_log hb, Real.exp_sub, Real.exp_log ha] at this
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact this
  have h2 : (tau1 I (x * g))⁻¹ ≤ (tau1 I x)⁻¹ * Real.exp (D / I.f) := by
    have hpos : 0 < tau1 I x * Real.exp (-(D / I.f)) := mul_pos ha (Real.exp_pos _)
    calc (tau1 I (x * g))⁻¹ ≤ (tau1 I x * Real.exp (-(D / I.f)))⁻¹ := inv_anti₀ hpos h1
      _ = (tau1 I x)⁻¹ * Real.exp (D / I.f) := by rw [mul_inv, Real.exp_neg, inv_inv]
  have h3 := pow_le_pow_left₀ (inv_nonneg.mpr hb.le) h2 (2 * I.n ^ 2 * I.f)
  have h4 : ((2 * I.n ^ 2 * I.f : ℕ) : ℝ) * (D / I.f) = 2 * (I.n : ℝ) ^ 2 * D := by
    push_cast
    field_simp
  calc _ ≤ _ := h3
    _ = (tau1 I x)⁻¹ ^ (2 * I.n ^ 2 * I.f) * Real.exp (2 * (I.n : ℝ) ^ 2 * D) := by
      rw [mul_pow, ← Real.exp_nat_mul, h4]

theorem reproducing_fixed : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  intro B d h hd hn hl hb T hT y f C hy hf hC
  have hcr := hf
  unfold IsContRep at hf
  obtain ⟨hfc, hfinv, -⟩ := hf
  obtain ⟨hphc, hphle, hphint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hwc := fun v => weight_condition B h (2 * (B.I.n : ℝ) ^ 2) hn hb le_rfl v
  have hint1 : Integrable (fun g => majPh B d h g * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g)) (muInf B.I) :=
    hphint (2 * (B.I.n : ℝ) ^ 2) (by positivity) hwc
  obtain ⟨hτpos, hτc, -, -⟩ := GlobalTheory.TauLipschitz.tauLip B.I hn
  have hadm := B.e_adm
  unfold AutInst.IsAdmIdem at hadm
  obtain ⟨-, -, -, -, he_supp, -, -⟩ := hadm
  have hre := B.Re_spec
  unfold AutInst.IsRConvF at hre
  have hmu : B.I.muA B.μf = (muInf B.I).prod B.μf := rfl
  have hmaj0 : ∀ g, 0 ≤ majPh B d h g := fun g => (norm_nonneg _).trans (hphle g)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : B.I.GA → ℝ, Φ = fun g => max C 0 *
      (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖) := ⟨_, rfl⟩
  have hΦg : ∀ g, Φ g = max C 0 *
      (majPh B d h g.1 * Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1) * ‖B.e g.2‖) := fun g => by rw [hΦdef]
  have hΦ0 : ∀ g, 0 ≤ Φ g := fun g => by
    rw [hΦg]
    exact mul_nonneg (le_max_right _ _)
      (mul_nonneg (mul_nonneg (hmaj0 _) (Real.exp_pos _).le) (norm_nonneg _))
  have hΦint : Integrable Φ (B.I.muA B.μf) := by
    rw [hΦdef, hmu]
    have hre1 : Integrable B.e B.μf := hre.1
    exact (hint1.mul_prod hre1.norm).const_mul _
  have hW0 : ∀ x, 0 ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := fun x => pow_nonneg (inv_nonneg.mpr (hτpos x).le) _
  have hbound : ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g := by
    intro x g
    rw [show phe B d g = ph B d g.1 * B.e g.2 from rfl]
    by_cases he : B.e g.2 = 0
    · rw [he, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (hW0 x) (hΦ0 g)
    · have h2 := inv_tau_pow_le B.I hn x g (he_supp g.2 he)
      have h3 : ‖f (x * g)‖ ≤ max C 0 * ((tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) *
          Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1)) :=
        (hC (x * g)).trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (hW0 _)).trans
          (mul_le_mul_of_nonneg_left h2 (le_max_right C 0)))
      rw [norm_mul, norm_mul, hΦg]
      calc ‖ph B d g.1‖ * ‖B.e g.2‖ * ‖f (x * g)‖
          ≤ majPh B d h g.1 * ‖B.e g.2‖ * (max C 0 * ((tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) *
              Real.exp (2 * (B.I.n : ℝ) ^ 2 * dSum B.I g.1))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hphle g.1) (norm_nonneg _)) h3 (norm_nonneg _)
              (mul_nonneg (hmaj0 _) (norm_nonneg _))
        _ = _ := by ring
  obtain ⟨hext1, hext2, -, -⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B y f hcr
  have hrc := (GlobalTheory.ConvKernel.rconv_eq_integral B (phe B d) T hT y).2
  rw [hy] at hrc
  haveI : SecondCountableTopology B.I.Gf := (GlobalTheory.CongTop.adelic_topology B.I).2.2.1
  haveI : FirstCountableTopology B.I.Ginf := inferInstance
  have hshift : ∀ x : B.I.GA, ∀ᵐ g ∂(B.I.muA B.μf), B.I.ext y (x * g) = f (x * g) := by
    intro x
    have hmap := (GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf).1 x
    have hm : AEMeasurable (fun g => x * g) (B.I.muA B.μf) :=
      (continuous_const.mul continuous_id).aemeasurable
    rw [← hmap] at hext1
    exact ae_of_ae_map hm hext1
  have hyF : (y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund]
      fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    refine hrc.trans (Filter.Eventually.of_forall fun x => ?_)
    exact integral_congr_ae ((hshift x).mono fun g hg => by simp only [hg])
  have hFc : Continuous fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hcw : Continuous fun x => (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
      (hτc.inv₀ fun x => (hτpos x).ne').pow _
    have hev : ∀ᶠ x in nhds x0, (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) < (tau1 B.I x0)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) + 1 :=
      hcw.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    refine continuousAt_of_dominated (bound := fun g => ((tau1 B.I x0)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) + 1) * Φ g)
      ?_ ?_ (hΦint.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun x =>
        hT.1.aestronglyMeasurable.mul (hfc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards [hev] with x hx
      exact Filter.Eventually.of_forall fun g =>
        (hbound x g).trans (mul_le_mul_of_nonneg_right hx.le (hΦ0 g))
    · exact Filter.Eventually.of_forall fun g =>
        (continuous_const.mul (hfc.comp (continuous_id.mul continuous_const))).continuousAt
  have hcrF : IsContRep B y fun x => ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
    unfold IsContRep
    refine ⟨hFc, fun γ hγ x => ?_, hyF⟩
    simp only [mul_assoc, hfinv γ hγ]
  have hFeq := hext2 _ hcrF
  exact ⟨⟨Φ, hΦint, hbound⟩, fun x => (congrFun hFeq x).symm⟩

end GlobalTheory.ReproducingFixed
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem one_le_rank_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    1 ≤ I.n := by
  by_contra h
  have h0 : I.n = 0 := by omega
  haveI : IsEmpty (Fin I.n) := by rw [h0]; infer_instance
  exact hW.1 (Subsingleton.elim _ _)

theorem exists_pos_le_tau1_mul_of_mem_NA_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (x : I.GA)
    (hW : I.IsIsot W) : ∃ c : ℝ, 0 < c ∧ ∀ m ∈ I.NA W, c ≤ tau1 I (m * x) := by
  obtain ⟨hpos, hcont, hinv, -⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties I (one_le_rank_of_isIsot I W hW)
  obtain ⟨-, -, -, -, Cp, hCp, -, hcov⟩ := GlobalTheory.UnipApprox.strong_approximation I W hW
  have hc : Continuous fun y : I.GA => tau1 I (y * x) := hcont.comp (continuous_id.mul continuous_const)
  have key : ∀ m ∈ I.NA W, ∃ y ∈ Cp, tau1 I (m * x) = tau1 I (y * x) := by
    intro m hm
    obtain ⟨γ, hγ, hy⟩ := hcov m hm
    refine ⟨γ⁻¹ * m, hy, ?_⟩
    rw [← hinv γ hγ.1 (γ⁻¹ * m * x)]
    congr 1
    group
  rcases Cp.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun m hm => ?_⟩
    obtain ⟨y, hy, -⟩ := key m hm
    rw [he] at hy
    exact hy.elim
  · obtain ⟨y₀, -, hmin⟩ := hCp.exists_isMinOn hne hc.continuousOn
    refine ⟨tau1 I (y₀ * x), hpos _, fun m hm => ?_⟩
    obtain ⟨y, hy, e⟩ := key m hm
    rw [e]
    exact hmin hy

end GlobalTheory.Dec
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem regular_pos_compl : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Gf k r z z' γ ≠ 0 → 0 < Gf k r z z' γ ∧ Dmin k r z z' γ (Fin.last (r + 1)) ≠ 0 ∧ IsUnit (gramM k r z z' γ).det ∧ ∀ y : Fin (2 * r + k + 1) → ℂ, y ≠ 0 → (∀ i, herm (Hpk k r) y (gramVec k r z z' γ i) = 0) → 0 < (herm (Hpk k r) y y).re := by
  intro k r z z' γ hz hz' hT hT' hγ hG

  have hGpos : 0 < Gf k r z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg k r z z' hz hz' hT hT' γ hγ) (Ne.symm hG)

  have hdet : (gramM k r z z' γ).det ≠ 0 := by
    intro h0
    apply hG
    have hg := Formalism.QuantumDeterminants.gGram k r z z' hz hz' γ hγ
    rw [h0, mul_zero] at hg
    exact_mod_cast hg

  have hk : 1 ≤ k := by
    by_contra hk0
    have hk' : k = 0 := by omega
    subst hk'
    apply hdet
    have hunit : ¬ IsUnit (gramM 0 r z z' γ) := by
      intro hu
      have h1 := Matrix.rank_of_isUnit _ hu
      rw [Formalism.QuantumDeterminants.gn_gramM_eq] at h1
      have h2 := Matrix.rank_mul_le_right
        ((Formalism.QuantumDeterminants.gnB 0 r z z' γ)ᴴ * Hpk 0 r) (Formalism.QuantumDeterminants.gnB 0 r z z' γ)
      have h3 := Matrix.rank_le_card_height (Formalism.QuantumDeterminants.gnB 0 r z z' γ)
      simp only [Fintype.card_sum, Fintype.card_fin] at h1 h3
      omega
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hunit
    exact hunit
  refine ⟨hGpos, ?_, isUnit_iff_ne_zero.mpr hdet, ?_⟩
  ·
    intro h0
    have hG' := hGpos
    unfold Gf at hG'
    rw [h0, map_zero] at hG'
    have hTT := mul_pos hT hT'
    have hn := Complex.normSq_nonneg (Dmin k r z z' γ ⟨r, by omega⟩)
    nlinarith
  ·
    intro y hy horth
    have hmem : y ∈ Formalism.FourierDecayAlt.C2.Uperp k r z z' γ := by
      rw [Formalism.FourierDecayAlt.C2.Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
      funext i
      rw [Pi.zero_apply, ← horth i]
      simp [herm, Matrix.mulVec, dotProduct]
    exact (Formalism.FourierDecayAlt.P.gram_independent_signature' k r z z' γ ⟨hk, ⟨hz, hT⟩, ⟨hz', hT'⟩⟩ ⟨hγ, hGpos⟩).2.2.1 y hmem hy

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isClosedSub_of_closedSubgroup {k r : ℕ} {S : Set (Mat k r)} (hG : S ⊆ GG k r)
    (h : Formalism.FourierDecayAlt.B2.IsClosedSubgroup S) : IsClosedSub k r S :=
  ⟨hG, h.closed, h.one_mem, h.mul_mem, h.inv_mem⟩

theorem closedSub_groups : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    IsClosedSub k r (GG k r) ∧ IsClosedSub k r (Nset k r) ∧ IsClosedSub k r (UWset k r z) ∧
      IsClosedSub k r (Sset k r z) ∧ IsCompact (UWset k r z) := by
  intro k r z hz hT
  have cG : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (GG k r) := Formalism.FourierDecayAlt.P.B2x2.closedG k r
  have cN : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (Nset k r) := Formalism.FourierDecayAlt.P.B2x2.closedN k r
  have cW : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (UWset k r z) := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have sN : Nset k r ⊆ GG k r := fun g hg => hg.1
  have sW : UWset k r z ⊆ GG k r := fun g hg => hg.1
  have sS : Sset k r z ⊆ GG k r := by
    rintro s ⟨h, hh, n, hn, rfl⟩
    exact cG.mul_mem _ (sW hh) _ (sN hn)
  exact ⟨isClosedSub_of_closedSubgroup subset_rfl cG, isClosedSub_of_closedSubgroup sN cN,
    isClosedSub_of_closedSubgroup sW cW,
    isClosedSub_of_closedSubgroup sS (GlobalTheory.BesselPeriodCompare.closedS hz),
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT⟩

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgQuot

theorem isMatGroup_GG (k r : ℕ) : PI.IsMatGroup (GG k r) := by

  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact ⟨⟨_, _, h, (mul_comm _ _).trans h⟩, rfl⟩
  obtain ⟨h1, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ _ hH
  refine ⟨?_, h1, hmul, fun a ha => ⟨(hinv a ha).2, Matrix.mul_nonsing_inv a (hinv a ha).1⟩⟩

  show IsClosed {g : Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exists_isQuotMeas : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r S μG μS hS hG hSμ hU
  obtain ⟨hSG, hcl, h1, hmul, hinv⟩ := hS

  have hSm : PI.IsMatGroup S :=
    ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ((isMatGroup_GG k r).2.2.2 a (hSG ha)).2⟩⟩

  exact GlobalTheory.QuotWeil.exists_isQuotM (2 * r + k + 1) (GG k r) S μG μS (isMatGroup_GG k r) hSm hSG hG hSμ hU.1

end GlobalTheory.SgQuot
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.top_minor_and_gram_number_le_majorant_lengths : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Dr k r z z' γ ≤ Sg k r z' x ^ r * Sg k r z (γ * x) ^ r ∧ 0 ≤ Yv k r z z' γ x ∧ Yv k r z z' γ x ≤ Sg k r z (γ * x) ^ r / Dr k r z z' γ := by
  first | exact @GlobalTheory.Amp.YBound.dr_y_le | exact GlobalTheory.Amp.YBound.dr_y_le | (intros; apply GlobalTheory.Amp.YBound.dr_y_le <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.covolume_middleLattice_homLattice_ideal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ a : Fin r, HasDom volume (homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a)) (ENNReal.ofReal (((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1))) := by
  first | exact @GlobalTheory.SnMass.VolN.CovH.covolume_homLat | exact GlobalTheory.SnMass.VolN.CovH.covolume_homLat | (intros; apply GlobalTheory.SnMass.VolN.CovH.covolume_homLat <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.euclideanBallAsymptotics_finite_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) → (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) → IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  first | exact @GlobalTheory.LeviIso.isRadial_pi | exact GlobalTheory.LeviIso.isRadial_pi | (intros; apply GlobalTheory.LeviIso.isRadial_pi <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.exists_orthonormalFrame_of_isotropicBlocks : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ), n = n₀ + 2 * ∑ i, j i → (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → (∀ i k, (B i)ᴴ * Formalism.REAL.Jm ε * B k = 0) → (∀ i, (B i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → ∃ (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (s : Formalism.REAL.UJ ε₀) (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ ∧ A₀ = B₀ * uMat s + ∑ k, B k * d k := by
  first | exact @GlobalTheory.FrameCompletion.exists_isFrame | exact GlobalTheory.FrameCompletion.exists_isFrame | (intros; apply GlobalTheory.FrameCompletion.exists_isFrame <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.finrank_matricesLoweringFiltrationBy_eq_succ_add : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → ∀ c, Module.finrank ℂ (lowers W c) = Module.finrank ℂ (lowers W (c + 1)) + ∑ b ∈ Finset.range m, r b * r (b + c + 1) := by
  first | exact @GlobalTheory.RadCov.finrank_lowers_eq_succ_add | exact GlobalTheory.RadCov.finrank_lowers_eq_succ_add | (intros; apply GlobalTheory.RadCov.finrank_lowers_eq_succ_add <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.selfDualHermitianFlag_piece_heights : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E), IsDualFlag I.J F (2 * a + 1) → F (2 * a + 1) = lamX I (1, xf) → (∀ i : Fin (a + 1), F i = S i) → (∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ∧ pieceHt (frm I (1, xf)) F i = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) ∧ pieceHt (frm I (1, xf)) F (2 * a - i) = (Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i))⁻¹) ∧ pieceHt (frm I (1, xf)) F a = 1 ∧ ∀ b, 2 * a + 1 ≤ b → pieceHt (frm I (1, xf)) F b = 1 := by
  first | exact @GlobalTheory.RadCov.pieceHt_dualFlag | exact GlobalTheory.RadCov.pieceHt_dualFlag | (intros; apply GlobalTheory.RadCov.pieceHt_dualFlag <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.exists_selfDual_flag_of_saturated_isotropic_flag : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ (F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (r : ℕ → ℕ), IsDualFlag I.J F (2 * a + 1) ∧ F (2 * a + 1) = lamX I (1, xf) ∧ (∀ i : Fin (a + 1), F i = S i) ∧ (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) ∧ (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) ∧ r a = I.n - 2 * ∑ i, j i ∧ ∀ b, 2 * a + 1 ≤ b → r b = 0 := by
  first | exact @GlobalTheory.RadCov.FullFlag.main | exact GlobalTheory.RadCov.FullFlag.main | (intros; apply GlobalTheory.RadCov.FullFlag.main <;> assumption)
end
