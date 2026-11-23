module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle408
public import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.localChar_conductor_le_of_heckeExponent :
    ∀ (D : D7) (ν : (AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH →
        ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : ℕ), GlobalTheory.CMVal.ExpAt νH (splitPrime τ) c →
        GlobalTheory.SplitFlip.CondLE (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) c (chrW ν τ) ∧ (¬ GlobalTheory.LFun.UnrAt ν (splitPrime τ) → 1 ≤ c) := by
  intro D ν νH h v τ c hc
  refine ⟨fun x hx => ?_, fun hn => ?_⟩
  · have h1 : Valued.v (x : Fv D.host.F v) = 1 := (GlobalTheory.FlipMatch.isEquiv_Fv v).eq_one_iff_eq_one.1 hx.1
    have h2 : Valued.v ((x : Fv D.host.F v) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
      refine ((GlobalTheory.FlipMatch.isEquiv_Fv v _ _).1 hx.2).trans_eq ?_
      rw [Units.val_pow_eq_pow_val, map_pow, GlobalTheory.ChrWUnif.valued_unifAt, ← WithZero.exp_nsmul]
      simp
    have h3 := (hc c).2 le_rfl (Units.map (complMap (splitPrime_under τ)).toMonoidHom x)
      ((SplitTie.valued_complMap τ (splitPrime_under τ) _).trans h1) (by
        refine le_of_eq_of_le ?_ h2
        rw [← SplitTie.valued_complMap τ (splitPrime_under τ), RingHom.map_sub, RingHom.map_one]
        rfl)
    rw [← locChar_eq_of_chrEq h] at h3
    exact h3
  · by_contra h0
    apply hn
    rw [unrAt_iff_of_chrEq h]
    intro x hx
    refine (hc 0).2 (by omega) x hx ?_
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact Valuation.map_sub_le _ (le_of_eq hx) (le_of_eq (map_one _))
end

section

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel GlobalTheory.ConjSize

open GlobalTheory.FunObj.GivenAdm in
theorem UpperTheory.haarVol_KO_le_resCard_pow_of_congruence_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL A k)}, IsOpen (J : Set (GL A k)) → J ≤ GlobalTheory.SplitWeil.KO k A → ∀ {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) ≤ J → (haarVol J).real (GlobalTheory.SplitWeil.KO k A : Set (GL A k)) ≤ (resCard k : ℝ) ^ (e * Fintype.card A * Fintype.card A) := by
  intro k _ _ _ _ _ _ A _ _ J hJo hJK ϖ e hϖ hN
  classical
  let red : GL A k → Matrix A A (Res k e) := fun g i j =>
    if h : (g : Matrix A A k) i j ∈ 𝒪[k] then Ideal.Quotient.mk (𝓂[k] ^ e) ⟨_, h⟩ else 0
  have key : ∀ g ∈ KO k A, ∀ h ∈ KO k A, red g = red h →
      h⁻¹ * g ∈ glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) := by
    intro g hg h hh hgh
    rw [GlobalTheory.FunObj.GivenAdm.mem_glLatCong]
    refine ⟨mul_mem (inv_mem hh) hg, ?_⟩
    have hg' := (mem_KO_iff g).1 hg
    have hh' := (mem_KO_iff h).1 hh
    have e1 : ((h⁻¹ * g : GL A k) : Matrix A A k) - 1
        = ((h⁻¹ : GL A k) : Matrix A A k) * ((g : Matrix A A k) - (h : Matrix A A k)) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Units.val_mul h⁻¹ h, inv_mul_cancel, Units.val_one]
    rw [e1]
    refine GlobalTheory.FunObj.GivenAdm.CongM.mul_left ?_ (fun i j => hh'.2 i j)
    intro i j
    have hij := congrFun (congrFun hgh i) j
    simp only [red, dif_pos (hg'.1 i j), dif_pos (hh'.1 i j)] at hij
    rw [Ideal.Quotient.eq] at hij
    have hv := (Model.val_le_iff_mem hϖ e _).1 hij
    simpa [Matrix.sub_apply] using hv
  haveI := isHaarMeasure_haarVol hJo hJK
  have hNJ : haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) ≤ 1 := by
    rw [← haarVol_self hJo hJK]
    exact measure_mono hN
  have piece : ∀ M : Matrix A A (Res k e), haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ 1 := by
    intro M
    by_cases hne : ∃ g0, g0 ∈ KO k A ∧ red g0 = M
    · obtain ⟨g0, hg0, hM⟩ := hne
      calc haarVol J {g | g ∈ KO k A ∧ red g = M}
          ≤ haarVol J ((fun h => g0⁻¹ * h) ⁻¹'
              (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k))) := by
            apply measure_mono
            rintro g ⟨hg, hgM⟩
            exact key g hg g0 hg0 (hgM.trans hM.symm)
        _ = haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) :=
            measure_preimage_mul _ _ _
        _ ≤ 1 := hNJ
    · calc haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ haarVol J ∅ := by
            apply measure_mono
            intro g hg
            exact absurd ⟨g, hg⟩ hne
        _ = 0 := measure_empty
        _ ≤ 1 := zero_le_one
  have hKO : haarVol J (KO k A : Set (GL A k))
      ≤ (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
    calc haarVol J (KO k A : Set (GL A k))
        ≤ haarVol J (⋃ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            {g | g ∈ KO k A ∧ red g = M}) := by
          apply measure_mono
          intro g hg
          simp only [Set.mem_iUnion]
          exact ⟨red g, Finset.mem_univ _, hg, rfl⟩
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            haarVol J {g | g ∈ KO k A ∧ red g = M} := measure_biUnion_finset_le _ _
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))), (1 : ENNReal) :=
          Finset.sum_le_sum (fun M _ => piece M)
      _ = (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
          simp [Finset.card_univ]
  have hcard : Fintype.card (Matrix A A (Res k e))
      = resCard k ^ (e * Fintype.card A * Fintype.card A) := by
    have h1 : Fintype.card (Matrix A A (Res k e))
        = Fintype.card (Res k e) ^ (Fintype.card A * Fintype.card A) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      show Nat.card (A → A → Res k e) = _
      rw [Nat.card_fun, Nat.card_fun, ← pow_mul, mul_comm]
    rw [h1, GlobalTheory.FlipMatch.FourierInv.card_res_pow, ← pow_mul, mul_assoc]
  rw [measureReal_def]
  have := ENNReal.toReal_mono (by simp) hKO
  rw [hcard] at this
  simpa using this
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_eq {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) (x : Matrix (Fin n) (Fin S.rank) (AE D))
    (p : Fin S.rank) (q : Fin d) : ptO S.gram e x p q = GlobalTheory.BigDat.divG S x (e q) p := rfl

private noncomputable def ptH {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) :
    Matrix (Fin n) (Fin S.rank) (AE D) →+ Matrix (Fin S.rank) (Fin d) (AE D) :=
  AddMonoidHom.mk' (ptO S.gram e) fun x y => by
    ext p q
    rw [Matrix.add_apply, ptO_eq, ptO_eq, ptO_eq, GlobalTheory.BigDat.divG, Matrix.add_mul]
    rfl

private theorem ptO_inj {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) {x y : Matrix (Fin n) (Fin S.rank) (AE D)}
    (h : ptO S.gram e x = ptO S.gram e y) : x = y := by
  have h1 : GlobalTheory.BigDat.divG S x = GlobalTheory.BigDat.divG S y := by
    ext q p
    obtain ⟨q, rfl⟩ := e.surjective q
    rw [← ptO_eq, ← ptO_eq, h]
  rw [← GlobalTheory.BigDat.mulG_divG S x, h1, GlobalTheory.BigDat.mulG_divG]

private theorem ptO_gen {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) (β : AF D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin n → D.host.E) :
    ptO S.gram e (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (fun q => a * t (e q))) := by
  ext p q
  refine (ptO_eq S e _ p q).trans ((GlobalTheory.BigDat.divG_gen S β a s t (e q) p).trans ?_)
  rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, mul_comm]
  rfl

private theorem at_eq_pairA {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {b : AF F}
    (hb : At (evFin F v) b) (hi : evFin F v b ∈ v.adicCompletionIntegers F) : ∃ α ∈ intAf F, b = pairA F 0 α := by
  refine ⟨GlobalTheory.AdelicU.singleFin v (evFin F v b), fun w => ?_, GlobalTheory.VacAny.eq_atPlace_of_at v b hb⟩
  by_cases h : w = v
  · subst h
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    exact hi
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h]
    exact zero_mem _

private theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E))
    (hL : IsLat e Vs Ws ΛS ΛX) :
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (x : WO S X), ptO S.gram e x ∈ latAtV Vs Ws v → x ∈ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True)) ∧
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AF D.host.F), At (evFin D.host.F v) a →
          evFin D.host.F v a ∈ v.adicCompletionIntegers D.host.F → ∀ x ∈ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True), a • ptO S.gram e x ∈ latAtV Vs Ws v := by
  refine ⟨fun v x hx => ?_, fun v b hb hi x hx => ?_⟩
  · have key : latAtV Vs Ws v ≤ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E))
        fun _ => True).map (ptH S e) := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨b, hb, hi, x, hx, y, hy, rfl⟩
      obtain ⟨α, hα, rfl⟩ := at_eq_pairA hb hi
      have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
          ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
        rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ GlobalTheory.SkewLat.DualPair.AA_ne]
        exact FractionalIdeal.one_mem_one _
      have h2 : ∀ z ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
          ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)),
          pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z • y)) ∈
            (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True).map (ptH S e) := by
        intro z hz
        refine Submodule.mul_induction_on hz (fun a ha c hc => ?_) (fun z z' hz hz' => ?_)
        · refine ⟨_, AddSubgroup.subset_closure ⟨α, hα, fun _ h => (h trivial).elim, a, ha, star x, (hL.1 x).1 hx,
            c • fun k => y (e.symm k), (hL.2 y).1 hy c hc, rfl⟩, ?_⟩
          refine (ptO_gen S e _ a _ _).trans ?_
          rw [star_star]
          congr 3
          funext q
          simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
        · have h3 : pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x ((z + z') • y)) =
              pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z • y)) +
              pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z' • y)) := by
            refine Matrix.ext fun p q => ?_
            rw [Matrix.add_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply,
              ← TensorProduct.tmul_add]
            simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add]
          rw [h3]
          exact add_mem hz hz'
      have h4 := h2 1 h1
      rwa [one_smul] at h4
    obtain ⟨x', hx', h⟩ := key hx
    rwa [← ptO_inj S e h]
  · refine GlobalTheory.BigDat.map_mem_of_closure ((DistribSMul.toAddMonoidHom _ b).comp (ptH S e)) ?_ hx
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine (congrArg (fun z => b • z ∈ latAtV Vs Ws v) (ptO_gen S e (pairA _ 0 α) a s t)).mpr ?_
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨_, ?_, ?_, _, (hL.1 _).2 (by rw [star_star]; exact hs), _, (hL.2 _).2 ?_, rfl⟩
    · intro u hu
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u, hb u hu, zero_mul]
    · rw [map_mul]
      exact mul_mem hi (hα v)
    · simp only [Equiv.apply_symm_apply]
      exact GlobalTheory.BigDat.smul_mem_scLat_of_mem ha ht

theorem UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX →
        (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (x : WO (sgn ε S) X), ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v → x ∈ (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True)) ∧
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AF D.host.F), At (evFin D.host.F v) a →
          evFin D.host.F v a ∈ v.adicCompletionIntegers D.host.F → ∀ x ∈ (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True), a • ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v := by
  intro D ψ ε S X d e Bs Vs Ws M _ ΛS ΛX hL
  exact finiteRing_sq_sub_mul_sq_eq_of_card (sgn ε S) X e Vs Ws ΛS ΛX hL
end
