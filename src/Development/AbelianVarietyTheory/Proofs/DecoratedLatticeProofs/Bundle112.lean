module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInert
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle010
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle008
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.AbsPointwiseMonoConstant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle108
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle024
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsND

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.DoublingSumU



theorem hasSum_doubling_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ χ : Lˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ m : ℕ, ((χ ϖ : ℂˣ) : ℂ) = (-1) ^ m → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q (χ ϖ) s) α) → (∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g)) ∧ HasSum (fun a : GU σ n ⧸ KU σ n => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n a.out) * ℓ (ρ a.out x)) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL q n α (χ ϖ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac q n m s * ℓ x) := by
  intro hD L _ _ _ ϖ σ q n hU χ hχ m hm s Φ hΦ V _ _ ρ x α hx ℓ hℓ hdom
  have hright : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) := by
    intro g k hk
    obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU g
    rw [mul_assoc (a * t) b k, GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha _ (mul_mem hb hk),
      GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb]
  refine ⟨hright, ?_⟩
  obtain ⟨h0, h1⟩ := GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal L ϖ σ q n hU V ρ x α hx ℓ hℓ
  by_cases hx0 : ℓ x = 0
  · simp only [h0 hx0, hx0, mul_zero]
    exact hasSum_zero
  · have hw := h1 hx0
    letI : MeasurableSpace (GU σ n) := borel _
    haveI : BorelSpace (GU σ n) := ⟨rfl⟩
    obtain ⟨μ, hμH, hμK⟩ := GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n
    have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1
    obtain ⟨hint, -, hval⟩ := (hD L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α _ hw).1 (hdom hx0)
    have hval' := hval m hm
    have hF : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) * (ℓ (ρ (g * k) x) / ℓ x) =
        Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x) := fun g k hk => by
      have h2 := hw.1 1 ⟨k, hk⟩ g
      simp only [OneMemClass.coe_one, one_mul] at h2
      rw [hright g k hk, h2]
    have hs := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm
    have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) hKo hμK
      (fun g => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x)) _ hF hs.hasSum).2
    have hS := hs.hasSum
    rw [← hci, hval'] at hS
    have h3 := hS.mul_right (ℓ x)
    simpa only [mul_assoc, div_mul_cancel₀ _ hx0] using h3

end GlobalTheory.DoublingSumU
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Col2.PtUniq

open _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem mem_iff_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) (v : Sp E n) :
    v ∈ N ↔ (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) N := by
  exact ⟨Formalism.L2.GlobalTheoryTheory.Br.latS_of_mem (F := F) N v,
    Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) N (Module.Finite.iff_fg.2 hN.fg) v⟩

theorem isPtOf_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (g : GL (Fin n) (Formalism.L2.DIV.AfE F E))
    (p p' : Formalism.L2.Col.DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g p → GlobalTheory.Mem.Col2.IsPtOf hc g p' → p = p' := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g p p' h h'
  have hN : p.deco.1.N = p'.deco.1.N := by
    ext v
    rw [mem_iff_hatL (F := F) p.deco.2.lat, mem_iff_hatL (F := F) p'.deco.2.lat, h.lat, h'.lat]
  have hd : p.deco = p'.deco := by
    apply Subtype.ext
    refine Deco.Ok.ext_on p.deco.2 p'.deco.2 hN (fun P x hx => ?_) (fun w x hx => ?_)
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hx0 : x = 0 := Subsingleton.elim _ _
        subst hx0
        have a := p.deco.2.f_smul P 0 0 (zero_mem _)
        have b := p'.deco.2.f_smul P 0 0 (zero_mem _)
        rw [zero_smul, map_zero, zero_mul] at a b
        rw [a, b]
      · exact HasRes.unique (h.f P x hx ⟨n - 1, by omega⟩ (by simp; omega))
          (h'.f P x (hN ▸ hx) ⟨n - 1, by omega⟩ (by simp; omega))
    · funext i
      exact HasRes.unique (h.be w x hx i) (h'.be w x (hN ▸ hx) i)
  have hfr : ∀ P : Q, p.fr P = p'.fr P := by
    intro P
    refine LinearEquiv.toLinearMap_injective (Module.Basis.ext (Pi.basisFun E (Fin n)) fun j => ?_)
    funext i
    have e := (h.fr P i j).symm.trans (h'.fr P i j)
    simpa using (algebraMap E (P.1.adicCompletion E)).injective e
  apply Subtype.ext
  exact Prod.ext hd (funext hfr)

end GlobalTheory.Mem.Col2.PtUniq
end
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.gramPoincareHilbertSchmidtDeviation_le_split : ∀ (D : D7) (u : D.what₂.Word), GlobalTheory.Core.Rk.hsDev D u ≤ 3 / 2 * hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + 3 * hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) := by
  first | exact @GlobalTheory.Core.Rk.hsDev_le_split_three_halves | exact GlobalTheory.Core.Rk.hsDev_le_split_three_halves | (intros; apply GlobalTheory.Core.Rk.hsDev_le_split_three_halves <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

section SlopeTestRemainingChoices
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂

theorem rowsND_one_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsND T Z C := by
  intro CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hcC hCC D large₂ u T Z C' Cl Cg cb Cu cT C0 hC2 hH hC3 hHH hVol hAmp hSm
    hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := hc1.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hL1 := d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have hC'0 : 0 ≤ C' := (abs_nonneg C2).trans hC2
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have e3 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    calc |C2| * (D.R.m : ℝ) ^ 2 ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
          mul_le_mul hC2 (e1.trans e2) (by positivity) hC'0
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + |C2| * (D.R.m : ℝ) ^ 2 / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2) (rows_m_cast _) hr0 hkm hc0 (rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
      hV := rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hVol
      hDEC := hAmp.2.2
      ha := hSm.1
      hb := hSm.2.1
      hp := hAmp.1
      hpp := hAmp.2.1
      h6 := hSm.2.2.1
      hδ := zero_le_one
      hThA := word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos Z hH.1 (hSm.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine rows_RowsND_record _ hyp le_rfl hcC hC1 hCsq ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : C2 * (D.R.m : ℝ) ^ 2 / 2 ≤ |C2| * (D.R.m : ℝ) ^ 2 / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end SlopeTestRemainingChoices

end GlobalTheory.Core.Deg
end
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem corankTwoCountBounds_of_rowCountBoundsUniform : ∀ S : Set ℝ, CntOn S → CountBoundOn S := by
  intro S h Cg cb Cu cT CT
  obtain ⟨c3, cH, cS, c4, thr, hthr⟩ := h Cg cb Cu cT CT
  exact ⟨c3, cH, thr, fun C0 hC0 C' Cl h1 h2 D large₂ u =>
    ⟨(hthr C0 hC0 C' Cl h1 h2 D large₂ u).1, (hthr C0 hC0 C' Cl h1 h2 D large₂ u).2.1⟩⟩

end GlobalTheory.Core.Deg
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem vanishingGramBound_uniformWindow_and_weightData : (VanishingGramTermsBoundWindow → ∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ (VanishingGramTermsBoundParams → Led1 VanishingGramTermsBound) := by
  refine ⟨fun h c => ?_, fun h => ?_⟩
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT c h1 h2
    refine ⟨max a b, fun C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u _ t r s d e => ?_⟩
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    exact H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s d e
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT h1 h2
    exact ⟨max a b, fun C' Cl hC' hCl D large₂ X Y hF hI u _ t r s n d e =>
      H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s n d e⟩

end GlobalTheory.Core.Deg
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_of_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  intro hS CT C hC hCT
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hC1 : (1 : ℝ) ≤ C := by nlinarith
  obtain ⟨K₀, hK⟩ := GlobalTheory.T.corankSums_bound_with_expLoss C hC1
  refine ⟨max K₀ 4, ?_⟩
  intro D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 hC' hCl hH hCc hAbs hTie hFo hn hd
  have hK₀ : K₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'1 : (1 : ℝ) ≤ C' := by linarith [le_max_right K₀ 4]
  have hCl4 : (4 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  have hHy := Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH.2.1 hH.1 hH.2.2 (by linarith) hC'1 le_rfl u
  have hXi := GlobalTheory.T.corankSizeHypothesis_explicitConstant_siegelMass hS C hC D large₂ u u C' Cl Cg cb Cu cT CT C0 1 (by linarith) hHy
  have hP := Formalism.L2.SG.LoopsCut.params_at hH X u hCl4 hCT hC1 hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hP1 : Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v
      (Cnt.NT D u) 1 := by
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, _, _⟩ := hP
    refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, le_rfl, ?_⟩
    apply Real.one_le_exp
    have hl : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hC0 : (0 : ℝ) ≤ C := by linarith
    positivity
  have hGam0 : 0 ≤ GamS D large₂ := (Real.exp_pos _).le
  have hGam8 : GamS D large₂ ≤ Real.exp ((D.R.k : ℝ) / 8) := by
    unfold GamS
    apply Real.exp_le_exp.2
    have h1 : 8 * large₂.CGam ≤ C' := hH.1.1
    have h2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.2.1
    have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
    have hM : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    nlinarith
  obtain ⟨hND, hDG⟩ := hK D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v (Cnt.NT D u) (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) hP1 hXi hGam0 hGam8
  obtain ⟨hJ, hW, hFC, _, _, _, _⟩ := hTie
  have hG := Formalism.L2.SG.LoopTieOf.gammaFixed_of_hypotheses Y hH
  have hm := Formalism.MainNotions.BridgeLemma.d_m_eq D
  have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq]; unfold gg; push_cast; ring
  have hcls : ∀ s, 2 ≤ s → s ≤ D.R.k → Formalism.L2.SG.LoopsCut.ClassLe (Y.tO u u) (Formalism.L2.SG.LoopsCut.bigS (Y.tO u u) s)
      ((fun s : ℕ => (D.duS u : ℝ) *
        (Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
                  (BridgeLemma.XiB D large₂ u C) * BridgeLemma.rDD D u +
          Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
            (BridgeLemma.XiB D large₂ u C))) s) := by
    intro s h2 hk
    have base := Formalism.L2.SG.LoopTieOf.gam_mul_le hG Z hFo
      (Formalism.L2.SG.LoopTieOf.classS_le T hJ hW hFC Z C hn hd s h2 hk)
    rw [hm, ← hg] at base
    exact base
  have habs := GlobalTheory.T.pairAbs_corank_ge_two_le_sum_corankClasses _ _ _ _ _ (Y.tO u u) D.R.k _ hAbs
    (fun p _ => Formalism.L2.SG.LoopsCut.corank_le_k Y u u p.1 p.2) hcls
  have hdd : ddC X Y u u = (D.duS u : ℝ) * BridgeLemma.rDD D u := Formalism.L2.SG.LoopTieOf.ddC_eq hCc u u
  have hdu : duC X Y u = (D.duS u : ℝ) := hCc.2.2.1 u
  have hdr0 : 0 ≤ (D.duS u : ℝ) * BridgeLemma.rDD D u := hdd ▸ dd_nonneg hCc u u
  have hd0 : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
  have hgg : ((X.B.g : ℕ) : ℝ) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by rw [X.g_eq]; push_cast; ring
  unfold CollS
  rw [hdd, hdu]
  set d : ℝ := (D.duS u : ℝ) with hdef
  set r : ℝ := BridgeLemma.rDD D u with hrdef
  set N := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hN
  set G := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hGd
  have hsum : ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) =
      d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  calc _ ≤ ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) := habs
    _ = d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := hsum
    _ ≤ d * r * (√(X.B.g : ℝ))⁻¹ ^ (D.R.k * D.R.f) +
        d * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hND hdr0) (mul_le_mul_of_nonneg_left hDG hd0)
    _ = _ := by rw [hgg]; ring

end GlobalTheory.Core.Deg
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

theorem ampAt_record_of_inputs :
    ∀ Cg CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl cb Cu cT CT C0 : ℝ), thr ≤ C' → thr ≤ Cl → 1 ≤ large₂.CGam →
      VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CPT →
      VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CDl →
      VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 →
      VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 →
      DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 hilbertNinetyConstant →
      AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 (max Cpr 0) Ca →
      VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 CS → VanishingOnXAndXPlusBranching.adm12 D →
      AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ := by
  intro Cg CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa0
  set Cc : ℝ := CS + Cg + 2 with hCc
  set K : ℝ := max CPT 0 + max Cc 0 + 6 with hK
  set Ch : ℝ := max (max CDl 0) (max (CDl + 1) 0) with hChd
  set Cm : ℝ := max (max K Ca) 2 with hCm
  set C : ℝ := max Cm (6 * Real.exp 1 * Real.pi * 1) with hCd
  set C2 : ℝ := max (6 * C) (C ^ 2 + C * Ch) with hC2
  have m1 : K ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have m2 : Ca ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  have m3 : 2 ≤ Cm := le_max_right _ _
  have n1 : Cm ≤ C := le_max_left _ _
  have n4 : 6 * Real.exp 1 * Real.pi * 1 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  have hChA : max (CDl + 1) 0 ≤ Ch := le_max_right _ _
  have hCh0 : 0 ≤ Ch := le_trans (le_max_right _ _) hChA
  have hChD : CDl ≤ Ch := le_trans (le_max_left _ _) (le_max_left _ _)
  have h62 : 6 * C ≤ C2 := le_max_left _ _
  have h22 : C ^ 2 + C * Ch ≤ C2 := le_max_right _ _
  refine ⟨C, C2, Ch, hC0, hCh0, fun Cpr δ hδ => ?_⟩
  obtain ⟨thr0, hthr0⟩ := GlobalTheory.T.size_bounds_of_standingHypotheses (max (max (C + 6 * C * Ch) C) (max (1 / δ) hilbertNinetyConstant))
  refine ⟨thr0, fun D large₂ C' Cl cb Cu cT CT C0 hC' hCl hG hA1 hA2 hA5 hA9 hDeg hAbs hA11 hA12 => ?_⟩
  by_cases hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0
  swap
  · refine ⟨?_, ?_, ?_⟩
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH
      exact absurd hH.1 hH0
  obtain ⟨h1000, -, hMm, hMk, -, -, hrb, hm2k, -⟩ := hthr0 D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hM1 : C + 6 * C * Ch ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMm
  have hMC : C ≤ (D.R.k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMk
  have hMd : 1 / δ ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMm
  have hM9 : hilbertNinetyConstant ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMm
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hb : 1 ≤ large₂.sc.b := one_le_b large₂

  have hS3 : VanishingOnXAndXPlusBranching.TowerRallisLemma D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch := by
    refine heightStatement_of_bounds D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 h62 ?_
    nlinarith
  have hS5 : VanishingOnXAndXPlusBranching.GGFromIrreducibility D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch :=
    product_clause_at_record D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 (by linarith) h22

  have hCl1 : 1 / Cl ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have p1 : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 1 Cc :=
    constant_clause_schur_weyl D large₂ C' Cl Cg cb Cu cT CT C0 1 CS Cc (by rw [hCc]; linarith) hA11 hA12

  have hn : (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := by
    calc (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (hilbertNinetyConstant * (D.R.m : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hrb (mul_nonneg hilbertNinetyConstant_pos hm0)
      _ ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by nlinarith)
  have hmr : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast rank_eq_two_mul_add_two D
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hδk : (D.R.rS : ℝ) + 2 ≤ δ * D.R.k := by
    have hmpos : (0 : ℝ) < D.R.m := by rw [hmr]; positivity
    have e1 : 1 ≤ δ * (D.R.m : ℝ) := by
      rw [div_le_iff₀ hδ] at hMd; linarith
    have e3 : (D.R.m : ℝ) ≤ δ * (D.R.m : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right e1 hmpos.le
      nlinarith
    have e4 : δ * (D.R.m : ℝ) ^ 2 ≤ δ * D.R.k := mul_le_mul_of_nonneg_left hm2k hδ.le
    linarith

  have r1 : HilbertSchmidtBoundWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    L2_decay_of_admissible D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CPT CDl Cc Cpr Cm Ch (le_max_right _ _) (le_max_left _ _)
      m1 hCh0 hChD hA1 hA2 p1
  have r2 : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    abs_decay_mono_constants D large₂ hCa0 m2 hChA
      (abs_decay_of_all_parameters D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CDl hilbertNinetyConstant Cpr Ca (max (CDl + 1) 0) (le_max_right _ _)
        (le_max_left _ _) hCa0 hilbertNinetyConstant_pos (le_max_right _ _) (le_max_left _ _) hn hA2 hA9 hDeg hAbs)
  have q7 : VanishingOnXAndXPlusBranching.division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr C Ch δ :=
    decayProp_of_l2AbsDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm C Ch δ m3 n1 hMC hδk n4 hA5 r1 r2
  exact ⟨hS3, hS5, q7⟩

end GlobalTheory

end
end
