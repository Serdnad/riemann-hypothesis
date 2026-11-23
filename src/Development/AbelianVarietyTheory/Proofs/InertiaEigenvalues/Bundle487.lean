module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle147
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormZpowSubOneLeBis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle184
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle449
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithful
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle479
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_log_tilt_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ u : P.R.BdR, ∀ g : GQ l, P.actQdR g u = u + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u), fun g => ?_⟩
  apply T.eD.injective
  rw [T.actD, RingEquiv.apply_symm_apply, map_add (f := _), RingEquiv.apply_symm_apply, hct]
  rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
    algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from GlobalTheory.MemLoc.ActLaws.σD_alg _ _, hg, map_add]

end GlobalTheory.PMon
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycEigen

theorem aeval_eq_zero_of_eigenbasis {C : Type} [Field C] {r : ℕ} (A : Matrix (Fin r) (Fin r) C)
    (e : Fin r → Fin r → C) (he : LinearIndependent C e) (c : Fin r → C)
    (hc : ∀ k, A.mulVec (e k) = c k • e k) (P : Polynomial C) (hP : ∀ k, P.eval (c k) = 0) :
    Polynomial.aeval A P = 0 := by
  have h1 : ∀ k, (Polynomial.aeval A P).mulVec (e k) = 0 := by
    intro k
    have h2 : Matrix.toLinAlgEquiv' (Polynomial.aeval A P) (e k) = P.eval (c k) • e k := by
      rw [← Polynomial.aeval_algHom_apply]
      exact Module.End.aeval_apply_of_mem_apply_eq_smul (by simpa using hc k)
    rw [hP, zero_smul] at h2
    simpa using h2
  have hsp : Submodule.span C (Set.range e) = ⊤ :=
    he.span_eq_top_of_card_eq_finrank' (by simp)
  have h3 : Matrix.toLin' (Polynomial.aeval A P) = 0 :=
    LinearMap.ext_on_range hsp fun k => by simpa using h1 k
  simpa using h3

variable {l : ℕ} [Fact l.Prime]

theorem hinf_le_gj (K : FinExt l) (s : ℕ) : Hinf K ≤ Gj K s :=
  IntermediateField.fixingSubgroup_antitone
    (sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}
      {x : Om l | ∃ j : ℕ, x ^ (l ^ j) = 1} fun (x : Om l) (hx : x ^ (l ^ s) = 1) =>
      (⟨s, hx⟩ : ∃ j : ℕ, x ^ (l ^ j) = 1)) _ : Ks K s ≤ Kinf K)

theorem gj_le (K : FinExt l) (s : ℕ) : Gj K s ≤ (K0 K).fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Ks K s from le_sup_left)

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) (g : GQ l) : ‖chiC χ j g‖ = 1 := by
  rw [chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow,
    (GlobalTheory.Cyc.cyc_basic l χ hχ).1, one_zpow]

theorem chiC_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (j : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) : chiC χ j h = 1 := by
  have : χ h = 1 :=
    ((GlobalTheory.Cyc.cyc_basic l χ hχ).2.2 K h (gj_le K 0 (hinf_le_gj K 0 hh))).2.1 hh
  simp [chiC, this]

theorem chiC_neg_mul (χ : GQ l →* ℚ_[l]ˣ) (j : ℤ) (g : GQ l) :
    chiC χ (-j) g * chiC χ j g = 1 := by
  rw [chiC, chiC, ← map_mul, ← Units.val_mul, ← zpow_add]
  simp

theorem eigen_of_norm_le {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {m r : ℕ}
    (hm : Lev l m) {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
    (hF : Frame χ K m U g) (u : ℤ) (y : Fin r → PadicComplex l) (hy1 : ∀ a, ‖y a‖ ≤ 1)
    (hy : ∀ σ ∈ Gj K m, twAct act χ u U σ y = y) : chiC χ u g • (U g).mulVec y = y := by
  obtain ⟨hg, -, hU, -, hH, hU1⟩ := hF
  obtain ⟨hdec, hdir, -, hmul, hstab, -⟩ := GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K m hm.1
  have hO : ∀ a, y a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act hact K (y a) (hy1 a)).1 fun h hh => ?_
    have := congrFun (hy h (hinf_le_gj K m hh)) a
    simpa [twAct, chiC_hinf hχ K u hh, hH h hh] using this
  choose y0 hy0 x hx hsum using fun a => hdec (y a) (hO a)
  have hfix : (fun a => act g (y0 a)) = y0 := funext fun a => act_inC hact hg.1 (hy0 a).1
  have hyx : y = y0 + x := funext hsum
  have hadd : twAct act χ u U g y = twAct act χ u U g y0 + twAct act χ u U g x := by
    have e : (fun a => act g (y a)) = (fun a => act g (y0 a)) + fun a => act g (x a) := by
      funext a; rw [hsum a, map_add (f := _)]; rfl
    simp only [twAct]
    rw [e, Matrix.mulVec_add, smul_add]
  have hc : chiC χ u g ∈ intC (Ks K m) := ⟨chiC_mem_inC χ u g _, (norm_chiC hχ u g).le⟩
  have hX : ∀ a, twAct act χ u U g x a ∈ Xj K m := by
    intro a
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact hmul _ hc _ ((Xj K m).sum_mem fun b _ =>
      hmul _ (hU g hg.1 a b) _ (hstab g (gj_le K m hg.1) _ (hx b)))
  have hK : ∀ a, twAct act χ u U g y0 a - y0 a ∈ inC (Ks K m) := by
    intro a
    rw [mem_inC_iff]
    simp only [twAct, hfix, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact sub_mem (mul_mem ((mem_inC_iff _ _).1 hc.1) (sum_mem fun b _ =>
      mul_mem ((mem_inC_iff _ _).1 (hU g hg.1 a b).1) ((mem_inC_iff _ _).1 (hy0 b).1)))
      ((mem_inC_iff _ _).1 (hy0 a).1)
  have hrel : ∀ a, twAct act χ u U g y0 a - y0 a = x a - twAct act χ u U g x a := by
    intro a
    have h1 := congrFun (hadd.symm.trans (hy g hg.1)) a
    rw [Pi.add_apply, hsum a] at h1
    linear_combination h1
  have hzero : ∀ a, twAct act χ u U g y0 a - y0 a = 0 := fun a =>
    hdir _ (hK a) _ ((Xj K m).sub_mem (hx a) (hX a)) 0 (by rw [pow_zero, one_mul]; exact hrel a)
  have hx0 : x = 0 := by
    refine twAct_fixed_eq_zero hact hχ hm hg U (hU g hg.1) hU1 u x hx ?_
    funext a
    exact (sub_eq_zero.1 ((hrel a).symm.trans (hzero a))).symm
  rw [hx0, add_zero] at hyx
  have h2 := hy g hg.1
  rw [hyx] at h2 ⊢
  rwa [twAct, hfix] at h2

theorem eigen_of_fixed {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {m r : ℕ}
    (hm : Lev l m) {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
    (hF : Frame χ K m U g) (u : ℤ) (y : Fin r → PadicComplex l)
    (hy : ∀ σ ∈ Gj K m, twAct act χ u U σ y = y) : (U g).mulVec y = chiC χ (-u) g • y := by
  have hl0 : (l : PadicComplex l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (x := (‖y‖ + 1)⁻¹) (by positivity) (norm_l_lt (l := l))
  have h1 : ∀ a, ‖(((l : PadicComplex l) ^ N) • y) a‖ ≤ 1 := by
    intro a
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    calc _ ≤ (‖y‖ + 1)⁻¹ * (‖y‖ + 1) :=
          mul_le_mul hN.le ((norm_le_pi_norm y a).trans (by linarith)) (norm_nonneg _)
            (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have h2 := eigen_of_norm_le hact hχ hm hF u _ h1 (by
    intro σ hσ
    have e : (fun a => act σ ((((l : PadicComplex l) ^ N) • y) a))
        = ((l : PadicComplex l) ^ N) • fun a => act σ (y a) := by
      funext a; simp
    have := hy σ hσ
    rw [twAct] at this ⊢
    rw [e, Matrix.mulVec_smul, smul_comm, this])
  rw [Matrix.mulVec_smul, smul_comm] at h2
  have h3 := smul_right_injective _ (pow_ne_zero N hl0) h2
  calc (U g).mulVec y = (chiC χ (-u) g * chiC χ u g) • (U g).mulVec y := by
        rw [chiC_neg_mul, one_smul]
    _ = _ := by rw [mul_smul, h3]

theorem aeval_prod_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → Polynomial.aeval (U g) (∏ u ∈ J, (Polynomial.X - Polynomial.C (chiC χ (-u) g))) = 0 := by
  intro l _ act χ hact hχ K m r hm U g hF J ⟨e, u, he, hu, hfix⟩
  refine aeval_eq_zero_of_eigenbasis (U g) e he (fun k => chiC χ (-(u k)) g)
    (fun k => eigen_of_fixed hact hχ hm hF (u k) (e k) fun σ hσ => hfix σ hσ k) _ fun k => ?_
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_coe.1 (hu k)) (by simp)

end GlobalTheory.CycEigen
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CyclotomicTowerSubgroupInclusions

variable {l : ℕ} [Fact l.Prime]

theorem unramified_subfield_le_Ks (K : FinExt l) (j : ℕ) : K0 K ≤ Ks K j := le_sup_left

theorem Ks_le_Kinf (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ (fun _ hx => Exists.intro j hx)) _

theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, unramified_subfield_le_Ks K j x.2⟩

theorem Hinf_le_Gj (K : FinExt l) (j : ℕ) : Hinf K ≤ Gj K j :=
  fun _ hg x => hg ⟨x.1, Ks_le_Kinf K j x.2⟩

theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := Iff.rfl

theorem algebraMap_mem_inC (F : IntermediateField ℚ_[l] (Om l)) (u : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) u ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) u, F.algebraMap_mem u, rfl⟩

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := hg ⟨x, hx⟩
  change g x = x at this
  simp only [ha.1, this]

theorem exists_scale (y : PadicComplex l) : ∃ n : ℕ, ‖(l : PadicComplex l) ^ n * y‖ ≤ 1 := by
  have hl : ‖(l : PadicComplex l)‖ < 1 := by
    have h1 : ‖algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ := norm_algebraMap' _ _
    rw [map_natCast] at h1
    rw [h1]
    exact Padic.norm_p_lt_one
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖y‖
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rwa [norm_mul, norm_pow]⟩

theorem invariants_twist : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ Gj K j, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC (Ks K j)) := by
  intro l _ act χ ha hχ K j hj i y hy
  obtain ⟨hnorm, -, hker⟩ := GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ
  obtain ⟨⟨g, hg⟩, -⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K j hj
  obtain ⟨hdec, hdir, -, hmul, hact, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K j hj.1
  obtain ⟨n, hn⟩ := exists_scale y
  have hl0 : (l : PadicComplex l) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  set z := (l : PadicComplex l) ^ n * y with hz
  have hzinv : ∀ σ ∈ Gj K j, chiC χ i σ * act σ z = z := by
    intro σ hσ
    rw [hz, map_mul, map_pow, map_natCast, mul_left_comm, hy σ hσ]
  have hzO : z ∈ Ohat K := by
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K z hn).mp fun h hh => ?_
    have h1 : χ h = 1 := (hker K h (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j (Hinf_le_Gj K j hh))).2.mp hh
    have h2 := hzinv h (Hinf_le_Gj K j hh)
    simpa [chiC, h1] using h2
  obtain ⟨a, haK, x, hx, hax⟩ := hdec z hzO
  set c := chiC χ i g with hc
  have hcK : c ∈ inC (Ks K j) := algebraMap_mem_inC _ _
  have hc1 : ‖c‖ = 1 := by
    rw [hc, chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]
  have hga : act g a = a := act_fix ha hg.1 haK.1
  have heq : c * (a + act g x) = a + x := by
    have := hzinv g hg.1
    rwa [hax, map_add, hga] at this
  have hX : x - c * act g x ∈ Xj K j :=
    (Xj K j).sub_mem hx (hmul c ⟨hcK, hc1.le⟩ _ (hact g (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j hg.1) x hx))
  have hK : (c - 1) * a ∈ inC (Ks K j) := by
    rw [mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.sub_mem _ hcK (Subfield.one_mem _)) haK.1
  have h0 : (c - 1) * a = 0 := hdir _ hK _ hX 0 (by linear_combination heq)
  have hrho : 0 < rho1 l :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
  have hx0 : x = 0 := by
    have h := (GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation l act χ ha hχ K j hj g hg 1 (fun _ => 1) (by
      intro a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      refine ⟨?_, by simp⟩
      rw [mem_inC_iff]
      exact Subfield.one_mem _) (by intro a b; simpa using hrho) i).1 (fun _ => x) (fun _ => hx) (by
      funext b
      simp only [twAct, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
      linear_combination heq - h0)
    exact congrFun h 0
  rw [hx0, add_zero] at hax
  refine ⟨fun hi => ?_, fun _ => ?_⟩
  · have hv := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj (χ g : ℚ_[l]) hg.2 i hi
    have hne : c - 1 ≠ 0 := by
      intro h
      have h2 : c - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
        rw [hc, chiC, Units.val_zpow_eq_zpow_val, map_sub, map_one]
      rw [h2, map_eq_zero] at h
      rw [h, norm_zero] at hv
      exact (zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos : (0 : ℝ) < l) _).ne hv
    have ha0 : a = 0 := (mul_eq_zero.mp h0).resolve_left hne
    rw [ha0, hz] at hax
    exact (mul_eq_zero.mp hax).resolve_left hl0
  · have : y = ((l : PadicComplex l) ^ n)⁻¹ * a := by
      rw [← hax, hz, inv_mul_cancel_left₀ hl0]
    rw [this, mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (natCast_mem _ l) n)) haK.1

end GlobalTheory.CyclotomicTowerSubgroupInclusions
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem idem_mul_aeval_idem_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (w : A) (p : R[X]) :
    f * aeval (f * w) p = f * aeval w p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), mul_add, mul_add, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, mul_pow]
    calc f * (algebraMap R A a * (f ^ n * w ^ n)) = algebraMap R A a * ((f * f ^ n) * w ^ n) := by ring
      _ = algebraMap R A a * (f * w ^ n) := by rw [← pow_succ', hf.pow_succ_eq]
      _ = f * (algebraMap R A a * w ^ n) := by ring

theorem isIntegral_idem_mul_of_quot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (w : A)
    (h : IsIntegral R (Ideal.Quotient.mk (Ideal.span {1 - f}) w)) : IsIntegral R (f * w) := by
  obtain ⟨q, hq, hqw⟩ := h
  have h0 : aeval w q ∈ Ideal.span {1 - f} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← hqw, ← aeval_def]
    exact (aeval_algHom_apply (Ideal.Quotient.mkₐ R (Ideal.span {1 - f})) w q).symm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h0
  have h1 : f * aeval w q = 0 := by
    rw [hc, ← mul_assoc, mul_sub, mul_one, hf.eq, sub_self, zero_mul]
  refine ⟨X * q, monic_X.mul hq, ?_⟩
  rw [← aeval_def, map_mul, aeval_X, mul_assoc, mul_left_comm, idem_mul_aeval_idem_mul hf w q, h1, mul_zero]

theorem isIntegral_or_isIntegral_of_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f →
    (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f → IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := by
  intro K B f y z hf hinv hyz
  by_cases hf0 : f = 0
  · left; rw [hf0, zero_mul]; exact isIntegral_zero
  set I : Ideal B.A := Ideal.span {1 - f} with hI
  have hmk : ∀ a b : B.A, Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ ∃ c, a - b = (1 - f) * c := by
    intro a b
    rw [Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
    rfl
  have hf1 : Ideal.Quotient.mk I f = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), hmk]
    exact ⟨-1, by ring⟩
  have hfm : ∀ a : B.A, Ideal.Quotient.mk I (f * a) = Ideal.Quotient.mk I a := by
    intro a; rw [map_mul, hf1, one_mul]
  have hfield : IsField (B.A ⧸ I) := by
    refine ⟨⟨0, 1, fun h => hf0 ?_⟩, mul_comm, ?_⟩
    · obtain ⟨c, hc⟩ := (hmk 0 1).1 h
      have := congrArg (f * ·) hc
      simp only [mul_sub, mul_zero, mul_one, zero_sub] at this
      rw [← mul_assoc, mul_sub, mul_one, hf.eq, sub_self, zero_mul] at this
      simpa using this
    · intro a ha
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hfx : f * x ≠ 0 := by
        intro h0
        apply ha
        rw [← hfm x, h0, map_zero]
      obtain ⟨v, hv⟩ := hinv x hfx
      refine ⟨Ideal.Quotient.mk I v, ?_⟩
      rw [← map_mul, ← hfm (x * v), ← mul_assoc, hv, hf1]
  haveI : I.IsMaximal := Ideal.Quotient.maximal_of_isField I hfield
  letI : Field (B.A ⧸ I) := Ideal.Quotient.field I
  haveI : CharZero K.O :=
    ⟨fun m n h => Nat.cast_injective (R := K.E) (by simpa using congrArg (algebraMap K.O K.E) h)⟩
  let e : FractionRing K.O ≃ₐ[K.O] K.E := IsLocalization.algEquiv (nonZeroDivisors K.O) (FractionRing K.O) K.E
  letI : Algebra (FractionRing K.O) (B.A ⧸ I) :=
    ((algebraMap K.E (B.A ⧸ I)).comp (e : FractionRing K.O →+* K.E)).toAlgebra
  haveI : IsScalarTower K.O (FractionRing K.O) (B.A ⧸ I) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change _ = algebraMap K.E (B.A ⧸ I) (e (algebraMap K.O (FractionRing K.O) x))
    rw [AlgEquiv.commutes]
    first
      | exact IsScalarTower.algebraMap_apply K.O K.E (B.A ⧸ I) x
      | rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsIntegral (FractionRing K.O) (B.A ⧸ I) := by
    refine ⟨fun x => ?_⟩
    have hx : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
    have := IsIntegral.map_of_comp_eq (e.symm : K.E →+* FractionRing K.O) (RingHom.id (B.A ⧸ I)) ?_ hx
    · simpa using this
    · ext t
      change algebraMap K.E (B.A ⧸ I) (e (e.symm t)) = _
      simp
  have hinv' : Ideal.Quotient.mk I (f * z) = (Ideal.Quotient.mk I (f * y))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← hfm, show f * (f * z * (f * y)) = f * y * z * f * f by ring, hyz, hf.eq, hf.eq, hf1]
  rcases GlobalTheory.LN.isIntegral_or_isIntegral_inv K.O (B.A ⧸ I) (Ideal.Quotient.mk I (f * y)) with h | h
  · left
    have := isIntegral_idem_mul_of_quot hf (f * y) h
    rwa [← mul_assoc, hf.eq] at this
  · right
    rw [← hinv'] at h
    have := isIntegral_idem_mul_of_quot hf (f * z) h
    rwa [← mul_assoc, hf.eq] at this

end GlobalTheory.UnitLemma.Desc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI := by
  first | exact @GlobalTheory.TiltFaithful.faithH | exact GlobalTheory.TiltFaithful.faithH | (intros; apply GlobalTheory.TiltFaithful.faithH <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_add_sub_le : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x y : Fl l), 1 ≤ h → r < 1 → ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖lam h j (x + y) - lam h j x - lam h j y‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  first | exact @GlobalTheory.PSer.lam_add_sub_le | exact GlobalTheory.PSer.lam_add_sub_le | (intros; apply GlobalTheory.PSer.lam_add_sub_le <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusSeries_onto_and_independent_zeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ τ : ℝ, (∀ t : ℂ_[l], ‖t‖ ≤ τ → ∃ y : Fl l, ‖sh y‖ ≤ ‖(l : ℂ_[l])‖ ∧ ‖∑ i : Fin h, μ i * lam h i y - t‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∃ x : Fin h → Fl l, (∀ a, ‖sh (x a)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ‖∑ i : Fin h, μ i * lam h i (x a)‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∀ n : Fin h → ℕ, ‖sh (∑ a, n a • x a)‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h → ∀ a, l ∣ n a := by
  first | exact @GlobalTheory.oneVarCount_onto_independentZeros | exact GlobalTheory.oneVarCount_onto_independentZeros | (intros; apply GlobalTheory.oneVarCount_onto_independentZeros <;> assumption)
end
