module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle412
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle072
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

open scoped Matrix ComplexOrder

namespace GlobalTheory.NormRatio

theorem gramAt_eq_one_of_gram {D : D7} (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold Formalism.BasicNotions.TH.gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem sig_snd_eq_zero_of_gram {D : D7} {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  by_contra hq
  let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
    Complex.one_re] at hk
  have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
    rw [Matrix.mul_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun l _ => by
      rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
  linarith

theorem exists_ipPair_one : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  intro D cc δ t0 Q P X hX h1 h2
  obtain ⟨hF, hW⟩ := hX
  have gA := gramAt_eq_one_of_gram X.A hF.gramA
  have gB := gramAt_eq_one_of_gram X.B hF.gramB
  have hI : ∀ k : ℕ, IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := fun k =>
    ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hA : X.A.SigOK := hF.defA.1
  have hq := sig_snd_eq_zero_of_gram hF.gramA hA
  obtain ⟨cA, hc⟩ := GlobalTheory.Cusp.exists_isCartanFrame X.A hA
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D X.B.rank X.A.rank
  have hone : ∀ τ, compAt X.θ τ (1 : GL (Fin X.A.rank) (AE D)).1 = 1 := fun τ => by
    exact Matrix.map_one ((X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have rA := X.rkA
  have rB := X.rkB
  refine ⟨cA, 1, ν, 𝓕, ⟨by omega, by omega, by omega, hW.inf, hA, hc, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩,
    (GlobalTheory.Doubling.isMaj_iff hW.inf).2 fun τ => ⟨fun _ => true, ?_⟩, fun τ => ?_, hW.weil, hν⟩
  · rw [gA]; exact hI _
  · rw [gB]; exact hI _
  · have hJ : Formalism.UG.Jpq (X.A.sig (tauE D τ)).1 (X.A.sig (tauE D τ)).2 = 1 := by
      have : IsEmpty (Fin (X.A.sig (tauE D τ)).2) := by rw [hq]; infer_instance
      rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hJ]; simp
  · rw [hone, gA]; simp
  · rw [hone, gA]; simp

end GlobalTheory.NormRatio
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.WeilEisConv

theorem weilEisensteinSiegelConvergence : GlobalTheory.Published.WeilEisensteinSiegelConvergence := by
  intro D n V hn hV ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 0 = swSec A V omh μ 𝓕 f (κ.symm g) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    have e : κ (κ.symm g) = g := κ.apply_symm_apply g
    rw [e] at h
    exact (congrFun h 0).trans (mixS_dblDec_zero A V ψ₀ μ 𝓕 _ 0)
  obtain ⟨a, ha⟩ := exists_isMaj A
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨C, hC, h₁⟩ := GlobalTheory.SWAbsGrowth.norm_swSec_le hW hμ hf a ha
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hs : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hc.2.2.2, hc.2.2.2, star_star])
  have hP := GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ' hsk κ hκ
  have hG := GlobalTheory.StdUnn.chart_mem_GF_iff D A μ' hsk κ hκ
  have hb : (A.rank : ℝ) < (V.rank : ℝ) / 2 := by
    have : (2 * n : ℝ) < V.rank := by exact_mod_cast hV
    change (n : ℝ) < _
    linarith
  have hsum : Summable fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) =>
      (hgt A a (κ.symm (Subtype.val (q.out : GF D n))) : ℝ) ^ ((V.rank : ℝ) / 2) := by
    refine GlobalTheory.Eis.Conv.summable_hgt hc hs (GlobalTheory.Doubling.gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
      (GlobalTheory.Doubling.isCompact_Khat A a) hI (γ := fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) => κ.symm (Subtype.val (q.out : GF D n)))
      (fun q => (hG _).2 (by rw [MulEquiv.apply_symm_apply]; exact q.out.2)) (fun q q' h => ?_) hb
    have h' := (hP _).1 h
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, h'⟩, inv_mul_cancel_right _ _⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hsum.mul_left C)
  simp only [GlobalTheory.Eis.term, mul_one]
  rw [key]
  exact h₁ _

end GlobalTheory.WeilEisConv
end

section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integrable_thetaKernel_weilRange : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g, Integrable (descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B m) := by
  first | exact @GlobalTheory.WeilThetaInt.integrable_thetaKO | exact GlobalTheory.WeilThetaInt.integrable_thetaKO | (intros; apply GlobalTheory.WeilThetaInt.integrable_thetaKO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLevelCong

variable {D : D7} {T : Type}

theorem gridModulus_le_of_mem_chosenPlaces {L : LevCh D T} {sc : Consts} (G : GridData L sc) {PP : Pl D.host.E} (h : PP ∈ G.pl.W0) :
    G.modul ≤ PP.asIdeal := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
  calc G.modul = ∏ u ∈ G.pl.S0, (G.pl.w u).asIdeal ^ G.pl.depth sc u := rfl
    _ ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := by
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    _ ≤ _ := Ideal.pow_le_self (G.pl.depth_pos sc v).ne'




theorem congLev_le_lev {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) :
    congLev D.sp.cm D.sp.X'.gram L.ΛX G.modul ≤ lev D.sp.cm D.sp.X'.gram L.βX (L.datXt μ₀) := by
  intro x hx
  obtain ⟨c, hc⟩ := hL.βX
  rw [one_pow] at hc
  have hβ : IsFrame L.βX L.ΛX := hc.1
  have hS : x ∈ St L.βX := (GlobalTheory.LevSplit.mem_St_iff _ _ hβ x).2 (GlobalTheory.CongMember.stab_of_mem_congLev hx)
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ x hx.1 hS fun PP hP => ?_
  have hPg : PP ∈ L.Pg := by
    rcases hP with h | h
    · exact h
    · exfalso
      refine (hL.Q_ram μ₀ PP).2 (Or.inl h) ?_
      rw [hL.xi_base]
      exact fun _ _ => rfl
  have hle : G.modul ≤ PP.asIdeal := gridModulus_le_of_mem_chosenPlaces G (levelChainTypePlaces_subset_chosenPlaces G hL μ₀ hPg)
  refine GlobalTheory.LevRedTriv.redFn_eq_one_of_cols hβ PP x hS 1 ((Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top) fun j => ?_
  have hz := (hβ (L.βX.1 *ᵥ Pi.single j 1)).2 fun k => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h1 := hx.2.2 _ hz
  rw [map_one, Subring.coe_one, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) h1

end GlobalTheory.RowLevelCong

namespace GlobalTheory.ClassCount

open GlobalTheory.RowLevelCong




theorem levRow_congLev_le : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε →
    x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is →
    ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ i : Fin (D.R.m + 1),
    congLev D.sp.cm (ch.G.V (.grid i D.R.m)).gram (ch.G.Λ (.grid i D.R.m)) ch.G.modul ≤
      ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2) := by
  refine ⟨0, fun CF _ ε => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ i => ?_⟩⟩
  have hL := hS.core.lev
  rcases i with ⟨_ | i, hi⟩
  · show congLev D.sp.cm (ch.G.V (.grid 0 D.R.m)).gram (ch.G.Λ (.grid 0 D.R.m)) ch.G.modul ≤
      ch.S.toGridChoice.levRow A.μ0 0 (Nat.zero_le _)
    have e := GlobalTheory.FunObj.levRow_zero_eq_lev ch.W ch.S.toGridChoice hL A.μ0 (Nat.zero_le _)
    have key : ∀ (Y : LSp D) (K : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))), Y = ⟨D.sp.X', R.toLevCh.ΛX⟩ →
        HEq K (lev D.sp.cm D.sp.X'.gram R.toLevCh.βX (R.toLevCh.datXt A.μ0)) →
        congLev D.sp.cm Y.sp.gram Y.lat ch.G.modul ≤ K := by
      rintro _ K rfl e'
      obtain rfl := eq_of_heq e'
      exact congLev_le_lev ch.G hL
    exact (key (ch.G.node (.grid 0 D.R.m)) _ (colY_m _) e).trans inf_le_left
  · show congLev D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram (ch.G.Λ (.grid (i + 1) D.R.m)) ch.G.modul ≤
      ch.S.toGridChoice.levRow A.μ0 (i + 1) (Nat.le_of_lt_succ hi)
    have e := GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA ch.W ch.S.toGridChoice A.μ0 i (Nat.le_of_lt_succ hi)
    calc congLev D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram (ch.G.Λ (.grid (i + 1) D.R.m)) ch.G.modul
        ≤ ch.G.levMax (.grid (i + 1) D.R.m) := congLev_mono le_top
      _ = ch.S.toGridChoice.levRow A.μ0 (i + 1) (Nat.le_of_lt_succ hi) ⊓ UA D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram := e.symm
      _ ≤ _ := inf_le_left

end GlobalTheory.ClassCount

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodLat.Obj3

theorem mLat3_of_tie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (fw : FWTie T R.toRealDat κ v₀) : (R.toCx3 F).MLat false :=
  fun j => GlobalTheory.GoodLat.Obj.mLat_of_tie fw F.lv2 false j

end GlobalTheory.GoodLat.Obj3
end
