module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateRowBoundOfDictionary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstJetOperatorNormCauchyBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle201
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
noncomputable section
namespace GlobalTheory.KerConjMean
theorem conjTopAt_of_rank_le_of_weight_le : (_root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b =>
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ,
      ∃ (ρ' : Qbar →ₐ[ℚ] ℂ) (e0 : VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank → ℂ)
        (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top j)).rank → D.host.E))
        (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top (j + 1))).rank → D.host.E)) (κ : ℂ) (k n : ℕ) (r : Fin n → Qbar)
        (s : Fin n → VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank),
        Even ((ch.G.V (.top j)).rank * (ch.G.V (.top (j + 1))).rank) ∧
        oddE0 D D.host.ccK ch.S.Z.δ ch.S.Z.t0 _ _ e0 ∧ SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ 0 < k ∧
        (∀ i, k • s i ∈ La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) ∧ (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) ∧
        lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) ∧
        (∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ)) t) ∧
        Formalism.L2.Ker.JetInVV ℂ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) (nuEnd ch.G (.top A.μ0 j)) ∧
        ∀ u, GlobalTheory.CoefModel.mapVV σ _ (f u) =
          Formalism.L2.Ker.jetOp (wt ch.G (.top j)) (wt ch.G (.top (j + 1)))
            (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) *
              U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) (Iop D (tor0 D D.host.ccK ch.S.Z.δ)
                (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) e0) z))
            (nuEnd ch.G (.top A.μ0 j)) (GlobalTheory.CoefModel.mapVV σ _ u)) → (∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
  ∀ (a b : ℕ) (e0 : VC D a b → ℂ), Even (a * b) → oddE0 D cc δ t0 a b e0 →
  ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
  ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), 0 < k →
  (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) →
  ∀ (ρ : Qbar →ₐ[ℚ] ℂ) (t' : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t' →
    0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧
    CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) Qbar ∧
    Differentiable ℂ (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) ∧
    ∀ z, ‖fnConj D Qbar ρ (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) *
        nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t') ^ (fF D * a * b) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ)))) → (∃ K : ℝ, 0 ≤ K ∧ ∀ (D : D7) (a b : ℕ) (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b)
  (n : D.what₂.Tau → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ v, 0 ≤ nrm lam (fun _ => 1) v) ∧
  ∃ Kx : ℝ, 0 < Kx ∧ Real.log Kx ≤ K * ((∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) +
      (Fintype.card D.what₂.Tau : ℝ) * ((a : ℝ) + b) ^ 2 + 1) *
      Real.log (2 + (∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) + a + b + Fintype.card D.what₂.Tau) ∧
    ∀ (H : VC D a b → ℂ) (S A : ℝ), 0 < A → 0 ≤ S → Differentiable ℂ H →
      (∀ z, ‖H z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ v,
      nrm lam' (fun _ => 1) (Formalism.L2.Ker.jetOp lam lam' (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H) n v) ≤
        S * Kx * max 1 A⁻¹ ^ (∑ τ, ∑ i, (lam' τ).natW i) * nrm lam (fun _ => 1) v) → (BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 := by
  intro tA tB tC tD hPr hInp hDict hDepth C1 hC1
  obtain ⟨K, hK0, hFock⟩ := tC
  obtain ⟨CF0, h⟩ := BigC.and (tA hPr hInp hDict hDepth) tD
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨max C0 (2 * (6 + 126 * K) + 9 * C1), fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨hA, hb3, hN1, hNb, hf1, hfb, hcard, hrd0, hrd, hj⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  have hCb : 2 * (6 + 126 * K) + 9 * C1 ≤ C := (le_max_right _ _).trans hC
  have hlogb : 1 ≤ Real.log large₂.sc.b := by
    have : Real.exp 1 ≤ large₂.sc.b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hN1' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN1
  have hf1' : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf1
  have hfNb : 1 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b := by
    have : 1 ≤ (D.R.f : ℝ) * (bigN D : ℝ) := one_le_mul_of_one_le_of_one_le hf1' hN1'
    nlinarith
  have hX : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine ⟨(6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b, 8 * D.R.f * bigN D * large₂.sc.b,
    D.R.f * bigN D * large₂.sc.b, by positivity, by positivity, by positivity, ?_, ?_⟩
  · have hsig : 0 ≤ sig ch.G :=
      Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hC0 : 0 ≤ C := by linarith
    have h2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
    have h3 := mul_le_mul_of_nonneg_right hCb hX
    unfold aOne
    nlinarith
  · intro Φ β d hocc c j fm hfm σ ρ hρ u B hu
    obtain ⟨ρ', e0, Ls, Lt, κ, k, n, r, s, hev, he0, hLs, hLt, hκ, hk, hs, hr, hlam, ⟨t, ht⟩, hJ, hfeq⟩ :=
      hA Φ β d hocc c j fm hfm σ ρ hρ
    have htc : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)) (tc D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      rw [hlam]; unfold tc; rw [dite_eq_left ⟨t, ht⟩]; exact Exists.choose_spec _
    obtain ⟨harea, -, hdiff, hgr⟩ := tB D (hInp D) D.host.ccK ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ _ e0 hev he0
      Ls Lt hLs hLt κ hκ k n r s hk hs hr ρ' _ htc
    obtain ⟨hpos, Kx, hKx, hlogKx, hop⟩ := hFock D _ _ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) _ hJ
    have eA : hArea D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (area (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)))⁻¹ := by
      unfold hArea; rw [hlam]
    have eT : hTh D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (nrm1Sq (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ))
        (GL3Theta.th0 (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)) (tc D ch.S.Z.δ ch.S.Z.t0 ρ))) := by
      unfold hTh; rw [hlam]
    set L := lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) with hL
    set X := nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ)) with hXdef
    set a := (ch.G.V (.top j)).rank with ha
    set bb := (ch.G.V (.top ((j : ℕ) + 1))).rank with hbb
    set g := fF D * a * bb with hg
    set P := 3 * (2 * ((g : ℕ) : ℝ) * D.host.rdE + 1) ^ g with hP
    set deg := ∑ τ, ∑ i, (wt ch.G (.top ((j : ℕ) + 1)) τ).natW i with hdeg
    have hS : 0 ≤ P * X ^ g := by
      have h0 := hgr 0
      have : (∑ τ, ∑ i, ∑ j, ‖(0 : VC D a bb) τ i j‖ ^ 2) = 0 := by simp
      rw [this, mul_zero, zero_div, Real.exp_zero, mul_one] at h0
      exact le_trans (sq_nonneg _) h0
    have hop' := hop _ (P * X ^ g) _ harea hS hdiff hgr (GlobalTheory.CoefModel.mapVV σ _ u)
    have hM0 : 0 ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg :=
      mul_nonneg (mul_nonneg hS hKx.le) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hrdpos : 0 < 2 * ((g : ℕ) : ℝ) * D.host.rdE + 1 := by
      have := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg g)) hrd0; linarith
    have hPpos : 0 < P := by rw [hP]; exact mul_pos (by norm_num) (pow_pos hrdpos g)
    have hW : ∀ jj : ℕ, jj ≤ D.R.m → (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) * (8 * large₂.sc.b) := by
      intro jj hjj
      calc (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) ≤
            ∑ τ : D.what₂.Tau, ∑ i : Fin (ch.G.V (.top jj)).rank, (8 * large₂.sc.b) :=
            Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => (hj jj hjj).2 τ i
        _ = (Fintype.card D.what₂.Tau : ℝ) * (((ch.G.V (.top jj)).rank : ℝ) * (8 * large₂.sc.b)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (D.R.f : ℝ) * ((bigN D : ℝ) * (8 * large₂.sc.b)) := by
            have h1 : (Fintype.card D.what₂.Tau : ℝ) ≤ D.R.f := by exact_mod_cast hcard
            have h2 : ((ch.G.V (.top jj)).rank : ℝ) ≤ bigN D := by exact_mod_cast (hj jj hjj).1
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity) (by positivity)
        _ = _ := by ring
    have hW0 : ∀ jj : ℕ, 0 ≤ (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) := fun jj =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have haN : (a : ℝ) ≤ bigN D := by exact_mod_cast (hj j j.2.le).1
    have hbN : (bb : ℝ) ≤ bigN D := by exact_mod_cast (hj ((j : ℕ) + 1) (Nat.succ_le_of_lt j.2)).1
    have hgc : (g : ℝ) = (D.R.f : ℝ) * a * bb := by rw [hg]; push_cast; rfl
    obtain ⟨hc0, hgG⟩ := size_bound K D.R.f (bigN D) large₂.sc.b D.host.rdE Kx _ _ a bb (Fintype.card D.what₂.Tau) g hK0 (Nat.cast_nonneg _) (by exact_mod_cast hcard) hb3 hN1' hNb hf1' hfb
      hrd0 hrd (Nat.cast_nonneg _) haN (Nat.cast_nonneg _) hbN (hW j j.2.le) (hW _ (Nat.succ_le_of_lt j.2))
      (hW0 _) (hW0 _) hgc hKx hlogKx
    have hc : Real.log (P * Kx) ≤ (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b := by
      rw [hP]; exact hc0
    have hdN : (deg : ℝ) ≤ 8 * D.R.f * bigN D * large₂.sc.b := by
      have e : (deg : ℝ) = ∑ τ, ∑ i, ((wt ch.G (.top ((j : ℕ) + 1)) τ).natW i : ℝ) := by rw [hdeg]; push_cast; rfl
      rw [e]; refine (hW _ (Nat.succ_le_of_lt j.2)).trans (le_of_eq ?_); ring
    have hpA : 0 ≤ Real.posLog (area L)⁻¹ := by unfold Real.posLog; exact le_max_left _ _
    have hpX : 0 ≤ Real.posLog X := by unfold Real.posLog; exact le_max_left _ _
    have hMexp : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤ Real.exp ((6 + 126 * K) * D.R.f * bigN D * large₂.sc.b *
        Real.log large₂.sc.b + 8 * D.R.f * bigN D * large₂.sc.b * hArea D ch.S.Z.δ ch.S.Z.t0 ρ +
        D.R.f * bigN D * large₂.sc.b * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      have hXg := pow_le_exp_posLog X g
      have hMd := max_pow_le_exp_posLog (area L) harea deg
      have step1 : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤
          (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) := by
        have := mul_le_mul hXg hMd (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.exp_pos _).le
        calc P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg = (P * Kx) * (X ^ g * max 1 (area L)⁻¹ ^ deg) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (mul_nonneg hPpos.le hKx.le)
      refine step1.trans ?_
      have eq : (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) =
          Real.exp (Real.log (P * Kx) + g * Real.posLog X + deg * Real.posLog (area L)⁻¹) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (mul_pos hPpos hKx)]; ring
      rw [eq, Real.exp_le_exp, eA, eT]
      linarith [mul_le_mul_of_nonneg_right hgG hpX, mul_le_mul_of_nonneg_right hdN hpA]
    rw [hfeq u]
    calc _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ u) := hop'
      _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * B := mul_le_mul_of_nonneg_left hu hM0
      _ ≤ _ := mul_le_mul_of_nonneg_right hMexp (le_trans (hpos _) hu)
theorem conj_top_degree_in_kernel_mean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 :=
  _root_.GlobalTheory.KerConjMean.conjTopAt_of_rank_le_of_weight_le _root_.GlobalTheory.T.kernel_conjugate_transport GlobalTheory.T.gaussianGrowth_conj_torsionTranslates_vacuum GlobalTheory.T.exists_const_jetOperatorNorm_cauchyBound GlobalTheory.T.eventually_parameterSizes_testChoices
end GlobalTheory.KerConjMean
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.kernel_conjugation_average : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 := by
  first | exact @_root_.GlobalTheory.KerConjMean.conj_top_degree_in_kernel_mean | exact _root_.GlobalTheory.KerConjMean.conj_top_degree_in_kernel_mean | (intros; apply _root_.GlobalTheory.KerConjMean.conj_top_degree_in_kernel_mean <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
noncomputable section
namespace GlobalTheory.KerConjRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Jets
open Formalism.L2.Ker
end Jets
section Row
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
end Row
theorem conjugate_row_mem_kernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 →
    BigC fun _ ch C b => ConjRowAt ch C b C1 := by
  intro _ hInp hDict _ C1 hC1
  obtain ⟨K, hK0, hFock⟩ := GlobalTheory.FockJetBound.jetOp_norm_le
  obtain ⟨CF0, h⟩ := BigC.and (BigC.and hDict rowSizes) GlobalTheory.KerConjMean.TopSizes.sizesK
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨max C0 (24 * (6 + 126 * K) + 36 * C1), fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨⟨hA, hwt⟩, hb3, hN1, hNb, hf1, hfb, hcard, hrd0, hrd, -⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  have hCb : 24 * (6 + 126 * K) + 36 * C1 ≤ C := (le_max_right _ _).trans hC
  have hlogb : 1 ≤ Real.log large₂.sc.b := by
    have : Real.exp 1 ≤ large₂.sc.b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hlog4 : Real.log (4 * large₂.sc.b) ≤ 3 * Real.log large₂.sc.b := by
    calc _ ≤ Real.log (large₂.sc.b ^ 3) := Real.log_le_log (by linarith) (by nlinarith [mul_le_mul hb3 hb3 (by norm_num) (by linarith)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hN1' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN1
  have hf1' : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf1
  have hb0 : 0 ≤ large₂.sc.b := by linarith
  have hX : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine ⟨12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b, 32 * D.R.f * bigN D * large₂.sc.b,
    4 * D.R.f * bigN D * large₂.sc.b, by positivity, by positivity, by positivity, ?_, ?_⟩
  · have hsig : 0 ≤ sig ch.G :=
      Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hC0 : 0 ≤ C := by linarith
    have h2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
    have h3 := mul_le_mul_of_nonneg_right hCb hX
    unfold aOne
    nlinarith
  · intro Φ β d hocc c j fm hfm σ ρ hρ u B hu
    obtain ⟨L, hL⟩ : ∃ L, L = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) := ⟨_, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g, g = fF D * (ch.G.V (.grid (j + 1) D.R.m)).rank * (ch.G.V (.grid j D.R.m)).rank := ⟨_, rfl⟩
    obtain ⟨H, harea, hdiff, hgr, hfeq⟩ := row_jets ch (hInp D) hA hocc c j fm hfm σ hρ L hL g hg
    have hp : DefPair D.R.m (.chi j D.R.m : GlobalTheory.ChiGrid.Pair T) := ⟨j.2, rfl⟩
    obtain ⟨hpos, Kx, hKx, hlogKx, hop⟩ := hFock D _ _ (wt ch.G (.grid j D.R.m)) (wt ch.G (.grid (j + 1) D.R.m)) _
      (wtOK_of_defPair ch.G _ hp).2
    have eA : hArea D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (area L)⁻¹ := by
      unfold hArea; rw [hL]
    have eT : hTh D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ))) := by
      unfold hTh; rw [hL]
    set X := nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ)) with hXdef
    set a := (ch.G.V (.grid j D.R.m)).rank with ha
    set bb := (ch.G.V (.grid ((j : ℕ) + 1) D.R.m)).rank with hbb
    set P := 3 * (2 * ((g : ℕ) : ℝ) * D.host.rdE + 1) ^ g with hP
    set deg := ∑ τ, ∑ i, (wt ch.G (.grid ((j : ℕ) + 1) D.R.m) τ).natW i with hdeg
    have hS : 0 ≤ P * X ^ g := by
      have h0 := hgr 0
      have : (∑ τ, ∑ i, ∑ j, ‖(0 : VC D a bb) τ i j‖ ^ 2) = 0 := by simp
      rw [this, mul_zero, zero_div, Real.exp_zero, mul_one] at h0
      exact le_trans (sq_nonneg _) h0
    have hop' := hop _ (P * X ^ g) _ harea hS hdiff hgr (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u)
    have hM0 : 0 ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg :=
      mul_nonneg (mul_nonneg hS hKx.le) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hrdpos : 0 < 2 * ((g : ℕ) : ℝ) * D.host.rdE + 1 := by
      have := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg g)) hrd0; linarith
    have hPpos : 0 < P := by rw [hP]; exact mul_pos (by norm_num) (pow_pos hrdpos g)
    have hrk : ∀ jj : ℕ, jj ≤ D.R.m → ((ch.G.V (.grid jj D.R.m)).rank : ℝ) ≤ bigN D := fun jj hjj => by
      exact_mod_cast GlobalTheory.DefRank.rank_le_bigN ch.G (.grid jj D.R.m) ⟨hjj, rfl⟩
    have hW : ∀ jj : ℕ, jj ≤ D.R.m → (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) * (8 * (4 * large₂.sc.b)) := by
      intro jj hjj
      calc (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) ≤
            ∑ τ : D.what₂.Tau, ∑ i : Fin (ch.G.V (.grid jj D.R.m)).rank, (8 * (4 * large₂.sc.b)) :=
            Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => (hwt jj τ i).trans (by linarith)
        _ = (Fintype.card D.what₂.Tau : ℝ) * (((ch.G.V (.grid jj D.R.m)).rank : ℝ) * (8 * (4 * large₂.sc.b))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (D.R.f : ℝ) * ((bigN D : ℝ) * (8 * (4 * large₂.sc.b))) := by
            have h1 : (Fintype.card D.what₂.Tau : ℝ) ≤ D.R.f := by exact_mod_cast hcard
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right (hrk jj hjj) (by positivity)) (by positivity) (by positivity)
        _ = _ := by ring
    have hW0 : ∀ jj : ℕ, 0 ≤ (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) := fun jj =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have haN : (a : ℝ) ≤ bigN D := hrk j j.2.le
    have hbN : (bb : ℝ) ≤ bigN D := hrk _ (Nat.succ_le_of_lt j.2)
    have hgc : (g : ℝ) = (D.R.f : ℝ) * a * bb := by rw [hg, mul_right_comm]; push_cast; rfl
    obtain ⟨hc0, hgG⟩ := size_bound K D.R.f (bigN D) (4 * large₂.sc.b) D.host.rdE Kx _ _ a bb (Fintype.card D.what₂.Tau) g hK0
      (Nat.cast_nonneg _) (by exact_mod_cast hcard) (by linarith) hN1' (by linarith) hf1' (by linarith)
      hrd0 (by linarith) (Nat.cast_nonneg _) haN (Nat.cast_nonneg _) hbN (hW j j.2.le) (hW _ (Nat.succ_le_of_lt j.2))
      (hW0 _) (hW0 _) hgc hKx hlogKx
    have hc : Real.log (P * Kx) ≤ 12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b := by
      rw [hP]
      refine hc0.trans ((mul_le_mul_of_nonneg_left hlog4 (by positivity)).trans (le_of_eq ?_))
      ring
    have hdN : (deg : ℝ) ≤ 32 * D.R.f * bigN D * large₂.sc.b := by
      have e : (deg : ℝ) = ∑ τ, ∑ i, ((wt ch.G (.grid ((j : ℕ) + 1) D.R.m) τ).natW i : ℝ) := by rw [hdeg]; push_cast; rfl
      rw [e]; refine (hW _ (Nat.succ_le_of_lt j.2)).trans (le_of_eq ?_); ring
    have hpA : 0 ≤ Real.posLog (area L)⁻¹ := Real.posLog_nonneg
    have hpX : 0 ≤ Real.posLog X := Real.posLog_nonneg
    have hMexp : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤ Real.exp (12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b *
        Real.log large₂.sc.b + 32 * D.R.f * bigN D * large₂.sc.b * hArea D ch.S.Z.δ ch.S.Z.t0 ρ +
        4 * D.R.f * bigN D * large₂.sc.b * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      have hXg := pow_le_exp_posLog X g
      have hMd := max_pow_le_exp_posLog (area L) harea deg
      have step1 : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤
          (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) := by
        have := mul_le_mul hXg hMd (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.exp_pos _).le
        calc P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg = (P * Kx) * (X ^ g * max 1 (area L)⁻¹ ^ deg) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (mul_nonneg hPpos.le hKx.le)
      refine step1.trans ?_
      have eq : (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) =
          Real.exp (Real.log (P * Kx) + g * Real.posLog X + deg * Real.posLog (area L)⁻¹) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (mul_pos hPpos hKx)]; ring
      rw [eq, Real.exp_le_exp, eA, eT]
      linarith [mul_le_mul_of_nonneg_right hgG hpX, mul_le_mul_of_nonneg_right hdN hpA]
    rw [hfeq u]
    calc _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg *
          nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) := hop'
      _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * B := mul_le_mul_of_nonneg_left hu hM0
      _ ≤ _ := mul_le_mul_of_nonneg_right hMexp (le_trans (hpos _) hu)
end GlobalTheory.KerConjRow
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.conjRowAt_of_dict_depth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjRowAt ch C b C1 := by
  first | exact @_root_.GlobalTheory.KerConjRow.conjugate_row_mem_kernel | exact _root_.GlobalTheory.KerConjRow.conjugate_row_mem_kernel | (intros; apply _root_.GlobalTheory.KerConjRow.conjugate_row_mem_kernel <;> assumption)
end
end

section

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
namespace GlobalTheory.ArchFamily
theorem exists_archimedean_theta_family : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W,
    ∃ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) ∧
      (∀ s t (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hcm hstd hW γ hγ
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
  have hex : ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑f₁ :=
    fun t f => _root_.GlobalTheory.T.theta_action_archimedean_locality hP M ψ χX χW om hcm hstd hW _ (hγ.2 _) f
  choose S hS using hex
  have key : ∀ t (f : SInf F (Fin n × Fin d)),
      om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f r₀) = tens (evI F) ⇑(S t f) r₀ :=
    fun t f => hS t f r₀ (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r₀ = tens (evI F) ⇑f r₀ + tens (evI F) ⇑g r₀ := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) ⇑(c • f) r₀ = c • tens (evI F) ⇑f r₀ := by
    intro c f; funext x; simp [tens, mul_assoc]
  let T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := S t
      map_add' := fun f g => hinj _ _ (by rw [← key, tadd, map_add (f := _), key, key, tadd])
      map_smul' := fun c f => hinj _ _ (by rw [← key, tsmul, map_smul, key, RingHom.id_apply, tsmul]) }
  refine ⟨T, fun t f => hS t f, fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · show tens (evI F) ⇑(S (s + t) f) r₀ = tens (evI F) ⇑(S s (S t f)) r₀
    have hmul : ((1 : UA σ X.J), γ (Multiplicative.ofAdd (s + t))) =
        ((1 : UA σ X.J), γ (Multiplicative.ofAdd s)) * ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) := by
      rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
    rw [← key, hmul, map_mul, Module.End.mul_apply, key, key]
  · show tens (evI F) ⇑(S 0 f) r₀ = tens (evI F) ⇑f r₀
    have h1 : ((1 : UA σ X.J), γ (Multiplicative.ofAdd (0 : ℝ))) = 1 := by
      rw [ofAdd_zero, map_one]; rfl
    rw [← key, h1, map_one, Module.End.one_apply]
end GlobalTheory.ArchFamily
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

theorem _root_.GlobalTheory.T.archimedean_theta_family_exists_smooth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W,
    ∃ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) ∧
      (∀ s t (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  first | exact @_root_.GlobalTheory.ArchFamily.exists_archimedean_theta_family | exact _root_.GlobalTheory.ArchFamily.exists_archimedean_theta_family | (intros; apply _root_.GlobalTheory.ArchFamily.exists_archimedean_theta_family <;> assumption)
end
end
