module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle820
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.DividedSlope

theorem strictAnti_of_adj {N : ℕ} (v : Fin N → ℝ)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → v b < v a) : ∀ a b : Fin N, a < b → v b < v a := by
  intro a b hab
  obtain ⟨b, hb⟩ := b
  have hab' : (a : ℕ) < b := hab
  induction b, hab' using Nat.le_induction with
  | base => exact h a _ rfl
  | succ n hn ih =>
    have h1 := ih (by omega) (show (a : ℕ) < n from hn)
    have h2 := h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl
    linarith

variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N)

omit [Fintype ι] in
theorem T_pos (hW : W.Hyp) : (0 : ℝ) < W.T := by
  have := hW.h1
  have : 0 < W.T := by omega
  exact_mod_cast this

omit [Fintype ι] in
theorem pos_dividedSlopeWeights_baseHeight (hW : W.Hyp) : (0 : ℝ) < W.h0 := by
  have h1 := hW.h2.1
  have h2 := hW.weightConst_nonneg
  have : 0 < W.h0 := by omega
  exact_mod_cast this

omit [Fintype ι] in
theorem g_pos (hW : W.Hyp) : 0 < W.g := by
  have := T_pos W hW
  have := pos_dividedSlopeWeights_baseHeight W hW
  unfold Wts.g
  positivity

omit [Fintype ι] in
theorem g_le_of (hW : W.Hyp) {x : ℤ} (hx : W.h0 ≤ 4 * W.T * x) : W.g ≤ (x : ℝ) := by
  have hT := T_pos W hW
  have hx' : (W.h0 : ℝ) ≤ 4 * W.T * x := by exact_mod_cast hx
  unfold Wts.g
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem adj_ge (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) (hb : W.p ≤ (b : ℕ)) :
    W.g ≤ reWt W.u' τ a - reWt W.u' τ b := by
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hW hD τ a b hab
  have hk := hW.kc_lt
  by_cases hp : (b : ℕ) = W.p
  · have := g_le_of W hW (h2 hp).2
    have ha : (a : ℕ) < W.p := by omega
    have hb' : ¬ (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_true, if_false]
    push_cast at this ⊢
    linarith
  · have := g_le_of W hW (h3 hp (by omega))
    have ha : ¬ (a : ℕ) < W.p := by omega
    have hb' : ¬ (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_false]
    push_cast at this ⊢
    linarith

theorem adj_lt (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) :
    reWt W.u' τ b < reWt W.u' τ a := by
  by_cases hb : W.p ≤ (b : ℕ)
  · have := adj_ge W hW hD τ a b hab hb
    have := g_pos W hW
    linarith
  · obtain ⟨h1, -, -⟩ := GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hW hD τ a b hab
    have h := h1 (by omega)
    have h' : W.u1 τ b < W.u1 τ a := by omega
    have ha : (a : ℕ) < W.p := by omega
    have hb' : (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_true]
    exact_mod_cast h'

theorem regular (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : a < b) :
    reWt W.u' τ b < reWt W.u' τ a :=
  strictAnti_of_adj _ (adj_lt W hW hD τ) a b hab

theorem anti (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : a ≤ b) :
    reWt W.u' τ b ≤ reWt W.u' τ a := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact (regular W hW hD τ a b h).le

theorem far (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (ha : W.p ≤ (a : ℕ)) (hab : a ≠ b) :
    W.g ≤ |reWt W.u' τ a - reWt W.u' τ b| := by
  have hk := hW.kc_lt
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℕ) < b := h
    have hb := b.2
    have h1 := adj_ge W hW hD τ a ⟨a + 1, by omega⟩ rfl (by simp only; omega)
    have h2 := anti W hW hD τ ⟨a + 1, by omega⟩ b (show (a : ℕ) + 1 ≤ b from h')
    exact le_trans (by linarith) (le_abs_self _)
  · have h' : (b : ℕ) < a := h
    have hb := a.2
    have h1 := adj_ge W hW hD τ ⟨a - 1, by omega⟩ a (by simp only; omega) ha
    have h2 := anti W hW hD τ b ⟨a - 1, by omega⟩ (show (b : ℕ) ≤ a - 1 by omega)
    exact le_trans (by linarith) (neg_le_abs _)

theorem entry_le (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (i : Fin N) :
    |reWt W.u' τ i| ≤ 2 * W.b / W.T := by
  have hT := T_pos W hW
  have h1 := (GlobalTheory.MeanTop.divided_entries ι N W hW hD τ i).1
  have h2 := (GlobalTheory.T.weight_division_l1_bound ι N W hW hD).2.2 τ i
  have h3 := hW.h5 τ i
  have h1' : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h1
  have h2' : |(W.u' τ i : ℝ)| ≤ |(W.u1 τ i : ℝ)| := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ W.Dd := Nat.cast_nonneg _
  have h5 := abs_nonneg (W.u1 τ i : ℝ)
  rw [le_div_iff₀ hT]
  show |(W.u' τ i : ℝ)| * W.T ≤ 2 * W.b
  nlinarith [mul_le_mul_of_nonneg_right h2' hT.le, mul_nonneg h4 h5]

end GlobalTheory.MeanTop.DividedSlope
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem Katz.reductionMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ) (V : Type) [AddCommGroup V] [Module k V] (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] V), IsRigOf μ ρ → ∃ r : Mod p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V, (∀ (f : quasiLog p h) c w, Red p (cob1 (fun i => Katz.lift p (μ i)) f.1) c → RedV p (lin f.1) w → r (Submodule.Quotient.mk f) = ρ (c, w)) ∧ Function.Surjective r ∧ ∀ m, r m = 0 ↔ ∃ n, m = p • n := by
  intro p _ k _ _ _ d μ h V _ _ ρ hρ
  have hμ' : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  have hR1 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)
  have hR2 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  have hD := GlobalTheory.T.quasiLog_reduces_to_cocycle p k d μ h
  have hK := GlobalTheory.T.quasiLogarithm_eq_p_smul_add_integral p k d μ h
  have hS := GlobalTheory.T.exists_quasiLog_red_coboundary_and_linear p k d μ h
  have hVu : ∀ (v : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v w' → w = w' := by
    intro v w w' h1 h2
    funext i
    obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h2 i
    rw [ha] at hb
    rw [← ha', ← hb', IsFractionRing.injective (WittVector p k) (Fr p k) hb]
  have hVa : ∀ (v v' : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v' w' →
      RedV p (v + v') (w + w') := by
    intro v v' w w' h1 h2 i
    obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h2 i
    exact ⟨a + b, by rw [Pi.add_apply, ha, hb, map_add (f := _)], by rw [map_add (f := _), ha', hb']; rfl⟩
  have hVs : ∀ (r : WittVector p k) (v : Fin d → Fr p k) (w : Fin d → k), RedV p v w →
      RedV p (fun i => algebraMap _ (Fr p k) r * v i) (WittVector.constantCoeff r • w) := by
    intro r v w h1 i
    obtain ⟨a, ha, ha'⟩ := h1 i
    exact ⟨r * a, by beta_reduce; rw [ha, ← map_mul], by rw [map_mul, ha']; rfl⟩
  have hlinadd : ∀ f g : MvPowerSeries (Fin d) (Fr p k), lin (f + g) = lin f + lin g := by
    intro f g; funext i; simp [lin]
  have hlinsmul : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)),
      lin (r • f) = fun i => algebraMap _ (Fr p k) r * lin f i := by
    intro r f; funext i
    simp only [lin, ← algebraMap_smul (Fr p k) r f, coeff_smul, smul_eq_mul]
  have hcobs : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)),
      cob1 (fun i => Katz.lift p (μ i)) (r • f) = r • cob1 (fun i => Katz.lift p (μ i)) f := by
    intro r f
    rw [← algebraMap_smul (Fr p k) r f, formalCoboundary_smul hμ', algebraMap_smul]
  choose c w hc hw using hD.1
  have key : ∀ f (hf : f ∈ quasiLog p h) c' w', Red p (cob1 (fun i => Katz.lift p (μ i)) f) c' →
      RedV p (lin f) w' → ρ (c f hf, w f hf) = ρ (c', w') := by
    intro f hf c' w' h1 h2
    rw [hR2.2.1 _ _ _ (hc f hf) h1, hVu _ _ _ (hw f hf) h2]
  let Φ : quasiLog p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V :=
    { toFun := fun f => ρ (c f.1 f.2, w f.1 f.2)
      map_add' := fun f g => by
        rw [key (f + g).1 (f + g).2 (c f.1 f.2 + c g.1 g.2) (w f.1 f.2 + w g.1 g.2), ← map_add (f := _),
          Prod.mk_add_mk]
        · rw [Submodule.coe_add, formalCoboundary_add hμ']
          exact (hR2.2.2.2.1 _ _ _ _ (hc _ _) (hc _ _)).1
        · rw [Submodule.coe_add, hlinadd]
          exact hVa _ _ _ _ (hw _ _) (hw _ _)
      map_smul' := fun r f => by
        rw [key (r • f).1 (r • f).2 (WittVector.constantCoeff r • c f.1 f.2)
          (WittVector.constantCoeff r • w f.1 f.2), ← map_smul, Prod.smul_mk]
        · rw [Submodule.coe_smul, hcobs]
          exact hR2.2.2.2.2.1 _ _ _ (hc _ _)
        · rw [Submodule.coe_smul, hlinsmul]
          exact hVs _ _ _ (hw _ _) }
  have hΦ : ∀ f : quasiLog p h, Φ f = ρ (c f.1 f.2, w f.1 f.2) := fun _ => rfl
  have hker : (intBy p k (Fin d) 1).submoduleOf (quasiLog p h) ≤ LinearMap.ker Φ := by
    intro f hf
    rw [LinearMap.mem_ker, hΦ]
    have hf' : (f : MvPowerSeries (Fin d) (Fr p k)) ∈ intBy p k (Fin d) 1 := hf
    obtain ⟨b, hb⟩ := (hR1.1 _).1 hf'
    obtain ⟨h1, h2⟩ := hC.2.1 _ _ hb
    rw [key _ _ _ _ h1 h2]
    exact ((hρ.ker _ _ (hD.2 _ f.2 _ h1)).2 ⟨b, rfl, rfl⟩)
  refine ⟨Submodule.liftQ _ Φ hker, ?_, ?_, ?_⟩
  · intro f c' w' h1 h2
    rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]
  · intro v
    obtain ⟨c', w', hcoc, rfl⟩ := hρ.surj v
    obtain ⟨f, hf, h1, h2⟩ := hS c' hcoc w'
    exact ⟨Submodule.Quotient.mk ⟨f, hf⟩, by rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]⟩
  · intro m
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [Submodule.liftQ_apply, hΦ]
    constructor
    · intro h0
      obtain ⟨b, hb1, hb2⟩ := (hρ.ker _ _ (hD.2 _ f.2 _ (hc f.1 f.2))).1 h0
      have h1 := hc f.1 f.2
      have h2 := hw f.1 f.2
      rw [hb1] at h1
      rw [hb2] at h2
      obtain ⟨g, hg, hfg⟩ := hK f.1 f.2 b h1 h2
      refine ⟨Submodule.Quotient.mk ⟨g, hg⟩, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (WittVector p k), ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.eq]
      exact hfg
    · rintro ⟨n, hn⟩
      have : Φ f = Submodule.liftQ _ Φ hker (p • n) := by
        rw [← hn, Submodule.liftQ_apply]
      rw [← hΦ, this, map_nsmul, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]

end GlobalTheory
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ), QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  first | exact @GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | exact GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | (intros; apply GlobalTheory.HilbFam.qAll_isAlgebraic_hfun <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  first | exact @GlobalTheory.HilbFam.qConj_hfun_twist | exact GlobalTheory.HilbFam.qConj_hfun_twist | (intros; apply GlobalTheory.HilbFam.qConj_hfun_twist <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam.SizeGL

theorem main : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QAll (Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ)) N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hf s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hlM hML hLsz hNsz hρ hρ0 hlM' hMy hy α
  have hA := GlobalTheory.WpFam.Act.rightActions N
  have hS := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hTw : HasLevel N (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) :=
    GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L _ hL
  obtain ⟨hmem, hsz⟩ := GlobalTheory.T.twistedHilbertLattice_contains_and_coordinate_size l lam F N (M * l ^ b) L α ρ₀ hL.2 hML hLsz hNsz
  have hx : M' • vmul y α = 0 := by rw [← hA.2.2.2.2.2.1, hMy]; exact (hA.2.2.2.2.1 0 α).mpr rfl
  have hx0 : vmul y α ≠ 0 := fun h => hy ((hA.2.2.2.2.1 y α).mp h)
  obtain ⟨hQ, -⟩ := GlobalTheory.T.weierstrassTorsion_qExpansion_integral l lam N M' (vmul y α) hlM' hx hx0
  have hQρ : QAll (Sz l lam ρ) N (wB N (vmul y α)) := by
    obtain ⟨a, ha, hp⟩ := hQ
    exact ⟨a, ha, fun n => hS.2.2.2.1 0 ρ _ hρ0 (hp n)⟩
  exact GlobalTheory.T.hilbertEisenstein_coefficient_valuation_bound hE F hf s N _ hs hN hTw z hz l lam κ (wB N (vmul y α)) M b e ρ₀ ρ he hze hlM hmem hsz hρ hQρ

end GlobalTheory.HilbFam.SizeGL
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace Opposite
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.VB
open GlobalTheory.Twist (resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear freeModule)

namespace GlobalTheory.OmegaGlobal

theorem map_bijective_of_isIso_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (R.map : (X ⟶ Y) → _) := by
  have h : (R.map : (X ⟶ Y) → _) = adj.homEquiv _ _ ∘ fun φ => adj.counit.app X ≫ φ := by
    funext φ
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact (adj.homEquiv _ _).bijective.comp
    ((asIso (adj.counit.app X)).homFromEquiv (Z := Y)).symm.bijective

section Frames

variable {X : Scheme.{0}} {F : X.Modules}

theorem isQuasicoherent_of_frames (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)),
    x ∈ U ∧ IsFrame e) : F.IsQuasicoherent := by
  choose U n e hx he using h
  refine QCoh.isQuasicoherent_of_restrict F (fun x => (U x).ι)
    (fun x => ⟨x, by simpa using hx x⟩) fun x => ?_
  have := (isVB_freeModule (U x).toScheme (Fin (n x))).isQuasicoherent
  exact QCoh.isQuasicoherent_of_iso ((isFrame_freeFrame _ _).iso
      ((isFrame_restrict_iff (U x).ι _).2 ((he x).res ((U x).ι_image_le ⊤))))

end Frames

variable {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G]

theorem fst_mul (x y : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫ (x.1 * y.1) =
    toUnit (specO O O) ≫ η[G] := by
  rw [comp_mul, x.2, y.2]
  exact _root_.mul_one (1 : specO O O ⟶ G)

theorem fst_scale (a : O) (x : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫
    (ptMap (dualScale a) ≫ x.1) = toUnit (specO O O) ≫ η[G] := by
  refine Eq.trans ?_ x.2
  rw [← Category.assoc]
  congr 1
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext y <;> simp [dualScale]

end GlobalTheory.OmegaGlobal
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.IndepBaseChange

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_contract {k E : Type} [Field k] [Field E] [Algebra k E] {A B : CommRingCat.{0}}
    {f : CommRingCat.of k ⟶ A} {p : A ⟶ B} {q : CommRingCat.of E ⟶ B}
    (po : IsPushout f (CommRingCat.ofHom (algebraMap k E)) p q) (l : E →ₗ[k] k) :
    ∃ Λ : B →+ A, ∀ (e : E) (a : A), Λ (q.hom e * p.hom a) = f.hom (l e) * a := by
  letI : Algebra k A := f.hom.toAlgebra
  have w := (CommRingCat.isPushout_tensorProduct k A E).w
  let d := po.desc _ _ w
  let m : A ⊗[k] E →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ l.lTensor A
  refine ⟨m.toAddMonoidHom.comp d.hom.toAddMonoidHom, fun e a => ?_⟩
  have h₁ : d.hom (p.hom a) = a ⊗ₜ[k] (1 : E) := congrArg (fun g => g.hom a) (po.inl_desc _ _ w)
  have h₂ : d.hom (q.hom e) = (1 : A) ⊗ₜ[k] e := congrArg (fun g => g.hom e) (po.inr_desc _ _ w)
  change m (d.hom (q.hom e * p.hom a)) = _
  rw [map_mul, h₁, h₂, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [m, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  rfl

theorem comb_f {k : Type} [Field k] (S : LinSys k) (u : Fin S.N → k) (i : S.L.ι) {W : S.Y.Opens}
    (h : W ≤ S.L.U i) : resG S.Y h ((S.comb u).f i) =
      ∑ j, ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top).hom (u j) *
        resG S.Y h ((S.b j).f i) := by
  let e : S.L.Sec →+ Γ(S.Y, W) :=
    { toFun := fun s => resG S.Y h (s.f i), map_zero' := map_zero _, map_add' := fun _ _ => map_add _ _ _ }
  refine (map_sum e _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  refine (map_mul (resG S.Y h) _ _).trans (congrArg (· * _) ?_)
  refine (LB.resG_resG _ _ _).trans ?_
  rfl

theorem indep_baseChange (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k) (hS : S.Indep) :
    (S.baseChange E).Indep := by
  intro u hu
  have key : ∀ l : E →ₗ[k] k, (fun j => l (u j)) = (0 : Fin S.N → k) := fun l => by
    refine hS _ (LB.f_injective (funext fun i => ?_))
    refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
      (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
    · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
      exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
    obtain ⟨⟨W, hW⟩, hle⟩ := W
    have H := S.isPullback_baseChange E
    have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
      (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
    have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
        (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
        ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
          (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
      refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
        (by simp) ?_ (by simp) (by simp)
      rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    obtain ⟨Λ, hΛ⟩ := exists_contract po' l
    have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
      fun y hy => Set.mem_iInter.2 fun _ => hle hy
    have e := comb_f (S.baseChange E) u (fun _ => i) hle'
    rw [hu] at e
    have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
        ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
      have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
        (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
      have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
      exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
    have e₂ := congrArg Λ e

    simp only [e', map_sum, hΛ] at e₂
    refine (comb_f S _ i hle).trans (e₂.symm.trans ?_)
    exact ((congrArg Λ (map_zero _)).trans (map_zero Λ)).trans (map_zero _).symm
  funext j
  exact (Module.forall_dual_apply_eq_zero_iff k (u j)).1 fun l => congrFun (key l) j

end GlobalTheory.Adelic.IndepBaseChange
end
end
