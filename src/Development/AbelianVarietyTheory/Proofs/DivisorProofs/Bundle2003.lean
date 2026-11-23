module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Foundations.ReferenceTupleNeBaseTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle198
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.UnitaryNorms.CharShare
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.RamificationInertia.Inertia
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotWeights

open Formalism.L2.Host (HChar)
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

variable {D : D7}

theorem hasInf_of_chars {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (χ : HChar D.host.E)
    (h : ∀ x, P.W.chV'.f x ^ P.W.ep' = χ.1 (finIdl D x)) :
    χ.HasInf (GlobalTheory.Mem.Chr.embTau D) (fun τ => P.W.ep' * P.W.chV'.n τ) := by
  intro a
  have h1 := χ.2.2 a
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, mul_comm] at h1
  rw [← h (GlobalTheory.NormSum.UnramHecke.incU D a)] at h1
  have h2 := P.W.chV'.aut a
  have h3 : ((χ.inf a : ℂˣ) : ℂ) = (((P.W.chV'.f (GlobalTheory.NormSum.UnramHecke.incU D a) : ℂˣ) : ℂ) ^ P.W.ep')⁻¹ := by
    have := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one, Units.val_zpow_eq_zpow_val] at this
    exact eq_inv_of_mul_eq_one_right this
  have hf := eq_inv_of_mul_eq_one_left h2
  rw [h3, hf, inv_zpow, inv_inv, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]
  rfl

end GlobalTheory.BotWeights

namespace GlobalTheory.BotWeights

open Formalism.L2.Host (HChar)

theorem weights_const : GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (δ t0 : ℂ), ∃ n₀ : D.what₂.Tau → ℕ,
      ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → P.n = n₀ := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G i j δ t0 => ?_⟩⟩
  have key : ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
      ((Lc.C.mu0 j / G.ch.chiH (D.R.m - i))⁻¹ : HChar D.host.E).HasInf (GlobalTheory.Mem.Chr.embTau D)
        (fun τ => P.W.ep' * P.W.chV'.n τ) := by
    intro s Q P P' hB k
    have h := hasInf_of_chars P _ hB.chars.2 k
    rw [← h]
    obtain ⟨n, hn, ho⟩ := hL.xi_fin s
    have hx := GlobalTheory.Mem.Chr.TieModel.inf_eq_one_of_order hn ho k
    have hx' : (Lc.xiH s).inf k = 1 := hx
    simp only [nuH, div_eq_mul_inv, Formalism.L2.Host.HChar.inf_inv, Formalism.L2.Host.HChar.inf_mul, hx', mul_one]
  by_cases hex : ∃ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P'
  · obtain ⟨s₀, Q₀, P₀, P₀', h₀⟩ := hex
    refine ⟨P₀.n, fun s Q P P' hB => funext fun τ => ?_⟩
    have e := congrFun (GlobalTheory.Mem.Chr.TieModel.hasInf_unique _ (GlobalTheory.Mem.Chr.TieModel.embTau_inj D)
      (GlobalTheory.Mem.Chr.TieModel.embTau_ne_conj D) (key s Q P P' hB) (key s₀ Q₀ P₀ P₀' h₀)) τ
    have w1 := P.wt τ
    have w2 := P₀.wt τ
    have d1 : (P.d : ℤ) = ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by exact_mod_cast hB.rank.2.2.1
    have d2 : (P₀.d : ℤ) = ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by exact_mod_cast h₀.rank.2.2.1
    have : (P.n τ : ℤ) = P₀.n τ := by linarith
    exact_mod_cast this
  · exact ⟨0, fun s Q P P' hB => absurd ⟨s, Q, P, P', hB⟩ hex⟩

end GlobalTheory.BotWeights
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomWitt

theorem wittIndex_eq_zero :
    GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, wittIndex WW = 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h _
  exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram h.stdW.1)

end GlobalTheory.BottomWitt
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.BotPairSmall.CondXi

open GlobalTheory.Mem.Col2.SplitChar

theorem modT_le {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T)
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : PP ∈ L.Q t) : modT G t ≤ PP.asIdeal := by
  classical
  by_cases hW : PP ∈ G.pl.W0
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hW
    unfold modT
    refine (Ideal.mul_le_inf.trans inf_le_left).trans ?_
    have h1 : condE G.pl ≤ (G.pl.w v).asIdeal ^ condExp G.pl v :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    refine h1.trans (Ideal.pow_le_self ?_)
    unfold condExp; split_ifs <;> omega
  · have hT : PP ∈ twPl G t := by
      unfold twPl
      rw [Finset.mem_filter]
      exact ⟨by unfold GlobalTheory.FunObj.locPl; exact Finset.mem_union_right _ hq, hW⟩
    unfold modT
    exact (Ideal.mul_le_inf.trans inf_le_right).trans (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hT))

theorem conj_smul_le_of_isConjPl {D : D7} {PP' PP : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.IndefR.Lev.IsConjPl PP' PP) : D.host.conj • PP'.asIdeal ≤ PP.asIdeal := by
  show Ideal.map _ _ ≤ _
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨c', hc', e⟩ := h x hx
  rw [Ideal.mem_comap]
  convert hc'
  apply RingOfIntegers.ext
  rw [e, Formalism.BasicNotions.bridge_star_holds]
  rfl


open Formalism.L2.Host in
theorem xiH_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T) (u : (AE D)ˣ), IntU D u → (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t) → (L.xiH t).1 (finIdl D u) = 1 := by
  intro D T L sc μ₀ hL G t u hu hc
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (L.xiH t).2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  show (L.xiH t).loc PP x = 1
  by_cases hr : (L.xiH t).UnrAt PP
  · exact hr x hunit
  have hle : modT G t * D.host.conj • modT G t ≤ PP.asIdeal ^ (1 : ℕ) := by
    rw [pow_one]
    rcases (hL.Q_ram t PP).1 hr with hq | ⟨PP', hq, hcj⟩
    · exact (Ideal.mul_le_inf.trans inf_le_left).trans (modT_le G t hq)
    · exact (Ideal.mul_le_inf.trans inf_le_right).trans
        ((Ideal.map_mono (modT_le G t hq)).trans (conj_smul_le_of_isConjPl hcj))
  refine hL.xi_tame t PP x hunit ?_
  rw [hx, vl_sub_one]
  exact GlobalTheory.BotPairSmall.CondNu.vl_le_of_mem_hatId hle hc

end GlobalTheory.BotPairSmall.CondXi

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modT_sup_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T),
    modT G t ⊔ D.host.conj • modT G t = ⊤ := by
  intro D T L sc μ₀ hL G t
  classical
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hund : ∀ PP PP' : HeightOneSpectrum (𝓞 D.host.E), PP.asIdeal = D.host.conj • PP'.asIdeal →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') := by
    intro PP PP' h
    have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv PP' PP := by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      intro x y hxy
      have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
      rw [hy, h]
      exact Ideal.smul_mem_pointwise_smul_iff.symm
    exact (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) PP' PP).2
      (Or.inr hc)
  have hmax' : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), (D.host.conj • PP.asIdeal).IsMaximal := by
    intro PP
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have hmem : ∀ w ∈ twPl G t, w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
    intro w hw
    rw [twPl, Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union] at hw
    exact ⟨hw.1.resolve_left hw.2, hw.2⟩
  have hoff : ∀ w ∈ twPl G t, w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro w hw hS
    obtain ⟨hQ, hW⟩ := hmem w hw
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
    · exact G.pl.levelPlace_ne_basePlace t w hQ h0
    · apply hW
      rw [G.pl.w_Q t w hQ h1]
      exact Finset.mem_image_of_mem _ hS
  have hAB : ∀ v ∈ G.pl.S0, ∀ w ∈ twPl G t, (G.pl.w v).asIdeal ≠ D.host.conj • w.asIdeal := by
    intro v hv w hw h
    exact hoff w hw (by rw [← hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBA : ∀ w ∈ twPl G t, ∀ v ∈ G.pl.S0, w.asIdeal ≠ D.host.conj • (G.pl.w v).asIdeal := by
    intro w hw v hv h
    exact hoff w hw (by rw [hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBB : ∀ w ∈ twPl G t, ∀ w' ∈ twPl G t, w.asIdeal ≠ D.host.conj • w'.asIdeal := by
    intro w hw w' hw' h
    refine (hL.Q_pl t w' (hmem w' hw').1).2 w (hmem w hw).1 fun c hc => ⟨D.host.conj • c, ?_, ?_⟩
    · rw [h]; exact Ideal.smul_mem_pointwise_smul _ _ _ hc
    · exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [modT, smul_mul', ← Ideal.isCoprime_iff_sup_eq]
  refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_) <;> rw [Ideal.isCoprime_iff_sup_eq]
  · exact condE_sup_conj G.pl
  · rw [Finset.smul_prod']
    refine Ideal.prod_sup_eq_top fun v hv => Ideal.sup_prod_eq_top fun w hw => ?_
    exact Ideal.pow_sup_eq_top (Ideal.IsMaximal.coprime_of_ne (G.pl.w v).isMaximal (hmax' w) (hAB v hv w hw))
  · rw [GlobalTheory.FunObj.SqNum.condE, Finset.smul_prod']
    simp only [smul_pow']
    refine Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun v hv => ?_
    exact Ideal.sup_pow_eq_top (Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' _) (hBA w hw v hv))
  · rw [Finset.smul_prod']
    exact Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun w' hw' =>
      Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' w') (hBB w hw w' hw')

end GlobalTheory.SqTop

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum
open Formalism.L2.Host (HChar)

noncomputable section

namespace GlobalTheory.SqTop.BotSmallProof

theorem eq_of_dvd_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {ℓ p : ℕ}
    (hℓ : ℓ.Prime) (hp : p.Prime) (hv : ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal) (h : p ∣ Ideal.absNorm v.asIdeal) : p = ℓ := by
  have hmax : (Ideal.span {((ℓ : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  haveI hl : v.asIdeal.LiesOver (Ideal.span {((ℓ : ℕ) : ℤ)}) := by
    refine ⟨hmax.eq_of_le ?_ ?_⟩
    · exact (v.isPrime.comap (algebraMap ℤ (𝓞 K))).ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) ((ℓ : ℕ) : ℤ) ∈ v.asIdeal
      rw [map_natCast]; exact hv
  rw [Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hℓ] at h
  exact (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)

theorem splitIn_of_cls {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem goodLevel {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (hsplit : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK) : GoodLevel D (levQ P) := by
  refine ⟨?_, fun p hp hdvd => ?_⟩
  · unfold levQ
    exact Finset.prod_pos fun v _ => pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  · unfold levQ at hdvd
    obtain ⟨v, hv, hd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    have hd' := hp.dvd_of_dvd_pow hd
    rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
    · rw [eq_of_dvd_absNorm _ (leastSplitAuxiliaryPrimeThetaChain_spec D).1 hp P.basePlace_over_qZero hd']
      exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
    · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
      · rw [eq_of_dvd_absNorm _ (D.host.g_prime 0) hp h hd']
        exact splitIn_of_cls (hsplit _ (D.host.g_level 0))
      · rw [eq_of_dvd_absNorm _ (D.host.g_prime 1) hp h hd']
        exact splitIn_of_cls (hsplit _ (D.host.g_level 1))
      · rw [eq_of_dvd_absNorm _ D.host.pde_prime hp h hd']
        exact splitIn_of_cls (hsplit _ D.host.pde_level.1)
      · rw [eq_of_dvd_absNorm _ D.host.pde'_prime hp h hd']
        exact splitIn_of_cls (hsplit _ D.host.pde_level.2)

theorem twPl_base {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) :
    twPl G μ₀ = ∅ := by
  have hQ : L.Q μ₀ = ∅ := by
    ext PP
    simp only [Finset.notMem_empty, iff_false]
    intro h
    refine ((hL.Q_ram μ₀ PP).2 (Or.inl h)) ?_
    rw [hL.xi_base]
    intro x _
    rfl
  ext w
  simp [twPl, locPl, hQ]

theorem nuH_inv_hasInf_all {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (t : T) (i j : Fin D.R.m) : (nuH G t i j)⁻¹.HasInf (Formalism.L2.Host.embTau D)
      (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  intro k
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]; exact mul_div_right_comm _ _ _
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  rw [e, mul_inv, HChar.inf_mul, Units.val_mul, HChar.inf_inv (L.xiH t), Formalism.L2.Host.HChar.inf_eq_one_of_order hn ho k, inv_one,
    Units.val_one, mul_one]
  exact nuH_inv_hasInf hL G i j k

theorem rankV_lt {D : D7} {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : rankV D i j + 1 ≤ bigN D := by
  have hm := D.R.two_le_m
  have e1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have e2 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have e3 : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  simp only [rankV, bigN, Ranks.r]
  omega

theorem bottomRank_sum_le_two_mul_totalRank (D : D7) (i j : Fin D.R.m) : botBig D i j + botSmall D i j ≤ 2 * bigN D := by
  obtain ⟨h1, h2, -⟩ := ranks_exact D i j
  have a1 := rankV_lt (D := D) (i := i + 1) (j := j + 1) (by omega) (by omega)
  have a2 := rankV_lt (D := D) (i := i) (j := j) (by omega) (by omega)
  omega

theorem natAbs_le_maxWt (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    max (wtA D C i j τ).natAbs (wtA' D C i j τ).natAbs ≤ maxWt D C := by
  unfold maxWt
  refine le_max_of_le_right ?_
  have := Finset.le_sup (f := fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
      max (wtA D C x.1 x.2.1 x.2.2).natAbs (wtA' D C x.1 x.2.1 x.2.2).natAbs) (Finset.mem_univ (i, j, τ))
  exact this

theorem n_le_arith {n d ε c e A A' : ℤ} (hd : 0 ≤ d) (hε : ε = 1 ∨ ε = -1) (hc : c = e ∨ c = -e)
    (hw : 2 * n = ε * c - d) (hA : 2 * (A - A') = e - d) : n ≤ |A| + |A'| := by
  have l1 := le_abs_self A
  have l2 := neg_abs_le A
  have l3 := le_abs_self A'
  have l4 := neg_abs_le A'
  rcases hε with rfl | rfl <;> rcases hc with rfl | rfl <;> omega

theorem small_of {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (t : T) (i j : Fin D.R.m) {δ t0 : ℂ} {Q : ℕ} (X : Pair D ⊤ δ t0 Q) (hd : X.d = botBig D i j + botSmall D i j)
    {χ : HChar D.host.E} (hc : HasChars X χ (nuH G t i j)⁻¹) : X.Small (bigN D) (maxWt D sc.cGap) := by
  refine ⟨hd ▸ bottomRank_sum_le_two_mul_totalRank D i j, fun τ => ?_⟩
  have habs := GlobalTheory.SplitWeight.abs_weight_eq_abs_infType X.W.chV' X.W.ep' _ _ X.W.ep_pm.2 hc.2
    (nuH_inv_hasInf_all hL G t i j) τ
  have hw : 2 * (X.n τ : ℤ) = X.W.ep' * X.W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    rw [← hd]; exact X.wt τ
  have hn := n_le_arith (Nat.cast_nonneg _) X.W.ep_pm.2 (abs_eq_abs.1 habs) hw (two_mul_wtA_sub D sc.cGap i j τ)
  have hB := natAbs_le_maxWt D sc.cGap i j τ
  have hB1 := (le_max_left _ _).trans hB
  have hB2 := (le_max_right _ _).trans hB
  have c1 : ((wtA D sc.cGap i j τ).natAbs : ℤ) = |wtA D sc.cGap i j τ| := Int.natCast_natAbs _
  have c2 : ((wtA' D sc.cGap i j τ).natAbs : ℤ) = |wtA' D sc.cGap i j τ| := Int.natCast_natAbs _
  have hB1' : ((wtA D sc.cGap i j τ).natAbs : ℤ) ≤ maxWt D sc.cGap := by exact_mod_cast hB1
  have hB2' : ((wtA' D sc.cGap i j τ).natAbs : ℤ) ≤ maxWt D sc.cGap := by exact_mod_cast hB2
  have n_le : (X.n τ : ℤ) ≤ 2 * maxWt D sc.cGap := by linarith
  exact_mod_cast n_le

theorem botSmall_holds : BotSmall := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ⟨?_, ?_, ?_⟩⟩⟩
  · obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
    exact goodLevel G.pl Pm.level_split
  · exact twPl_base G hL
  · intro δ t0 Q P P' t i j 𝔪 h
    exact ⟨small_of hL G t i j P h.rank.2.2.1 h.chars,
      small_of hL G t i j P' (h.rank.2.2.2.trans h.rank.2.2.1) h.chars'⟩

end GlobalTheory.SqTop.BotSmallProof
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc}

def IsStageC (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ pp D j ∧ q ≤ qq D j ∧ A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * qq D j = rankV D i j + 2 * q ∧ NegIdx A p ∧ NegIdx A' q ∧ NegIdx WW (p + q) ∧
    X.Is W.ψ W.θ (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (fun t => nuH G t i j) (locPl G)

theorem negIdx_of_isStd {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) : NegIdx V 0 := fun τ => by
  have : gramAt D V τ = 1 := by rw [gramAt, h.1]; simp
  rw [this]
  refine ⟨(Equiv.sumEmpty _ _).symm, 1, ?_⟩
  ext (a | a) (b | b)
  · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
  all_goals first | exact a.elim0 | exact b.elim0

theorem IsBottomTri.isStageC {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsBottomTri W i j X) : IsStageC W i j 0 0 X := by
  have r := ranks_exact D i j
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, negIdx_of_isStd h.std, negIdx_of_isStd h.std',
    negIdx_of_isStd h.stdW, h.is⟩
  · rw [h.rank]; simpa [pp] using r.1
  · rw [h.rank']; simpa [qq] using r.2.1

end GlobalTheory.SqTower
end
end
