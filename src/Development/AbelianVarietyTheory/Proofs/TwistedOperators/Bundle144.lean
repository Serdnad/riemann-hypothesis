module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallFundamentalSetRealUnipotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030

@[expose] public section

section

open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

noncomputable section

namespace GlobalTheory.DeepPoint


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_one (I : AutInst) (m : ℕ) : (1 : I.Gf) ∈ I.Kg m :=
  ⟨K_one I, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_mul (I : AutInst) (m : ℕ) {x y : I.Gf} (hx : x ∈ I.Kg m) (hy : y ∈ I.Kg m) : x * y ∈ I.Kg m := by
  refine ⟨K_mul I hx.1 hy.1, fun v hv => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hy.2 v hv
  obtain ⟨z', hz', hxz⟩ := hx.2 v hv
  refine ⟨I.fmat x *ᵥ z + z', add_mem (K_mv I hx.1 hz) hz', ?_⟩
  have e : (I.fmat (x * y) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat y - 1) *ᵥ v) + (I.fmat x - 1) *ᵥ v := by
    rw [fmat_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    abel
  rw [e, hyz, hxz, Matrix.mulVec_smul, smul_add]


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_inv (I : AutInst) (m : ℕ) {k : I.Gf} (hk : k ∈ I.Kg m) : k⁻¹ ∈ I.Kg m := by
  refine ⟨K_inv I hk.1, fun y hy => ?_⟩
  obtain ⟨z, hz, hkz⟩ := hk.2 y hy
  refine ⟨-(I.fmat k⁻¹ *ᵥ z), neg_mem (K_mv I (K_inv I hk.1) hz), ?_⟩
  have h1 : I.fmat k⁻¹ * I.fmat k = 1 := fmat_inv_mul I k
  have e : (I.fmat k⁻¹ - 1) *ᵥ y = -(I.fmat k⁻¹ *ᵥ ((I.fmat k - 1) *ᵥ y)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e, hkz, Matrix.mulVec_smul, smul_neg]

theorem isIsot_span (I : AutInst) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (hiso : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) :
    I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  first
  | exact @_root_.GlobalTheory.HermitianFormLinearity.main
  | exact _root_.GlobalTheory.HermitianFormLinearity.main
  | (apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianFormLinearity.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianFormLinearity.main ..)

theorem exists_step (I : AutInst) (x : I.GA) (q : ℕ) (hn : 1 ≤ I.n)
    (hrk : ∀ v, rkR (I.ε v) ≤ q) (hl : least I x < 1 / 2) :
    ∃ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ),
      IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R ∧ R ≠ ⊥ ∧ R ≤ stepLt I x (1 / 2) ∧
      R ≤ lamX I x ∧ 0 < hi ∧ largestSize (bas I) (frm I x) R ≤ hi ∧
      (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) ∧
      hi ≤ (2 * least I x) ^ ((1 : ℝ) / q) * lo ∧ hi ^ 2 ≤ (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  have hpiece := (hspec a S τ hF).1
  have ha0 := ((hspec a S τ hF).2 hn).1
  have hτ0 := ((hspec a S τ hF).2 hn).2
  obtain ⟨hS0, hSmono, hSlast, hτmono, hτ, -⟩ := hF
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hl)
    · exact h
  have hrkS : ∀ i : Fin (a + 1), (i : ℕ) ≤ rkK (S i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have := (hpiece i).2.1
      simp only [Fin.coe_castSucc] at ih
      simp only [Fin.val_succ]
      omega
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 := hrkS (Fin.last a)
    rw [hSlast] at h1
    have h2 := (GlobalTheory.FlagIso.flag_isotropic I x).2.1 v
    simp only [Fin.val_last] at h1
    exact h1.trans (h2.trans (hrk v))
  set τ' : ℕ → ℝ := fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 with hτ'
  have hτ'pos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    simp only [hτ']
    split_ifs with h
    · exact (hτ ⟨i, h⟩).1
    · norm_num
  have hτ'lt : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    simp only [hτ', dif_pos hi]
    split_ifs with h
    · exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · exact (hτ ⟨i, hi⟩).2.1
  have hτ'a : τ' a = 1 / 2 := by simp [hτ']
  have hτ'0 : τ' 0 = least I x := by
    simp only [hτ', dif_pos (show 0 < a by omega)]
    exact hτ0 (by omega)
  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hτ'pos hτ'lt hτ'a
  rw [hτ'0] at hratio hsq
  set i : Fin a := ⟨b, hb⟩ with hi_def
  have hib : τ' b = τ i := by simp [hτ', hb, i]
  refine ⟨S i.succ, τ' (b + 1), τ i, ?_, ?_, ?_, ?_, (hτ i).1, ?_, ?_, ?_, ?_⟩
  · rw [(hτ i).2.2.1]; exact (GlobalTheory.CountSteps.steps I x _ (hτ i).1).1
  · intro h
    have := hSmono (Fin.succ_pos i)
    rw [hS0, h] at this
    exact lt_irrefl _ this
  · rw [← hSlast]; exact hSmono.monotone (Fin.le_last _)
  · rw [(hτ i).2.2.1]; exact sSup_le fun N hN => hN.1
  · exact (hpiece i).2.2.1.le
  · intro N hN hNL
    by_cases hb1 : b + 1 < a
    · have eS : S i.succ = S (Fin.castSucc (⟨b + 1, hb1⟩ : Fin a)) := congrArg S (Fin.ext (by simp [i]))
      have e : τ' (b + 1) = τ ⟨b + 1, hb1⟩ := by simp [hτ', hb1]
      rw [e, eS]
      rw [eS] at hN
      exact (hpiece ⟨b + 1, hb1⟩).2.2.2.1 N hN hNL
    · have hba : b + 1 = a := by omega
      have e : τ' (b + 1) = 1 / 2 := by rw [hba, hτ'a]
      have eS : S i.succ = stepLt I x (1 / 2) := by
        rw [← hSlast]; exact congrArg S (Fin.ext (by simp [i, hba]))
      rw [e, eS]
      rw [eS] at hN
      exact (GlobalTheory.CountSteps.steps I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hN hNL
  · rw [← hib]
    have hpos := hτ'pos (b + 1) (by omega)
    rwa [div_le_iff₀ hpos] at hratio
  · rw [← hib]; exact hsq

theorem deep_point : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n →
    (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset,
      ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ),
        (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧
        (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧
        Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤
          (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  intro I x g q hg _ hn hrk hl
  obtain ⟨R, lo, hi, hsat, hR0, hRS, hRL, hhi, hlarge, hlo, hhl, hh2⟩ := exists_step I x q hn hrk hl
  have hisoR : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 :=
    fun y hy z hz => (GlobalTheory.FlagIso.flag_isotropic I x).1 y (hRS hy) z (hRS hz)
  have hperp : R ≤ perpIn I x R := fun y hy =>
    Submodule.subset_span ⟨hRL hy, fun s hs => hisoR s hs y hy⟩
  have hWiso : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := isIsot_span I R hR0 hisoR
  refine ⟨_, hWiso, fun m hm => ?_⟩
  obtain ⟨⟨N, hN⟩, -, hsplit, hdense, -⟩ := GlobalTheory.UnipApprox.strong_approximation I _ hWiso
  have hU : {c : I.Gf | x.2⁻¹ * c * x.2 ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    have ho : IsOpen (I.Kg g) := I.topf_open g hg
    have hc : Continuous fun c : I.Gf => x.2⁻¹ * c * x.2 :=
      (continuous_const.mul continuous_id).mul continuous_const
    refine (ho.preimage hc).mem_nhds ?_
    show x.2⁻¹ * 1 * x.2 ∈ I.Kg g
    rw [mul_one, inv_mul_cancel]
    exact kg_one I g
  obtain ⟨γ, ⟨hγF, hγN⟩, hγU⟩ := hdense _ hU m hm
  have hm'N : γ⁻¹ * m ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
    rw [← hN] at hγN hm ⊢
    exact N.mul_mem (N.inv_mem hγN) hm
  have hν := (hsplit _ hm'N).1
  obtain ⟨γ', ⟨hγ'F, -⟩, hγ'K, A, Z, hAZ, heq, hbd, -⟩ :=
    GlobalTheory.SmallFund.small_fundamental_set I x g R lo hi _ hg hsat hR0 hperp hhi hlarge hlo hhl hh2 _ hν
  have hk : (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2) ∈ I.Kg g :=
    kg_mul I g (kg_inv I g hγ'K) hγU
  refine ⟨γ * γ', Formalism.MainNotions.LeviCoordinates.rrg_mul_mem I hγF hγ'F, _, hk,
    (γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1, A, Z, hAZ, fun v => ?_, ?_, hbd⟩
  · have e : uMat (((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1) v) =
        uMat ((γ'.1 v * x.1 v)⁻¹) * (uMat ((γ⁻¹ * m).1 v) * uMat (x.1 v)) := by
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_assoc]
      rfl
    rw [e, heq v]
    have e2 : uMat (γ'.1 v) * uMat (x.1 v) = uMat (γ'.1 v * x.1 v) := rfl
    have e3 : uMat ((γ'.1 v * x.1 v)⁻¹) * uMat (γ'.1 v * x.1 v) = 1 := by
      show uMat ((γ'.1 v * x.1 v)⁻¹ * (γ'.1 v * x.1 v)) = 1
      rw [inv_mul_cancel]
      rfl
    rw [e2, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat ((γ'.1 v * x.1 v)⁻¹)), e3, Matrix.one_mul]
  · have h2 : γ' * x * ((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1,
        (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2)) = (γ⁻¹ * m) * x := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul]
        group
      · simp only [Prod.snd_mul, Prod.snd_inv]
        group
    calc m * x = γ * ((γ⁻¹ * m) * x) := by group
      _ = γ * γ' * x * _ := by rw [← h2]; simp only [mul_assoc]

end GlobalTheory.DeepPoint
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace LevelPlaces
open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem natCast_mem_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P')
    {n : ℕ} (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c', h1, h2⟩ := h _ hn
  have e : (n : 𝓞 D.host.E) = c' := RingOfIntegers.ext (by
    rw [h2]
    change (n : D.host.E) = star (n : D.host.E)
    rw [star_natCast])
  rwa [e]

theorem isConjPl_conjSpec {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P (conjSpec P) :=
  fun c hc => ⟨_root_.Formalism.L2.Col.cO D.host.E c, by
    change _root_.Formalism.L2.Col.cO D.host.E (_root_.Formalism.L2.Col.cO D.host.E c) ∈ P.asIdeal
    rwa [_root_.Formalism.L2.Col.cO_cO], rfl⟩

theorem not_mem_of_prime {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h : (q : A) ∈ I) : (p : A) ∉ I := by
  intro h'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  apply hI
  rw [Ideal.eq_top_iff_one]
  have e : (1 : A) = a * (q : A) + b * (p : A) := by
    exact_mod_cast congrArg (Int.cast : ℤ → A) hab.symm
  rw [e]
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

theorem div_or_div_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : Pb.Div k P ∨ Pb.Div k (conjSpec P) := by
  by_contra hc
  have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hc (Or.inl e.symm)
  have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e => hc (Or.inr e.symm)
  obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
  obtain ⟨x', n, hx', hn⟩ := exists_norm D x
  have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * _root_.Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
      rw [← hx', ← map_mul, hn, map_intCast]
    rw [e] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hx1 h
    · exact hx2 h
  have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
  have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
  by_cases hd : (D.host.g k : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    apply hnP
    push_cast
    exact Ideal.mul_mem_right _ _ hk
  · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
    apply (Pb.pb k).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)

theorem mem_of_div {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Pb.Div k P) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h1 := Pb.pb_over k
  rw [← (show P.under (𝓞 D.host.K) = Pb.pb k from h)] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal := h1
  rwa [map_natCast] at h2

theorem not_mem_of_twist {D : D7} {Q : Finset (Pl D.host.E)} (hQ : Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q)
    {P : Pl D.host.E} (hP : P ∈ Q) (k : Fin 2) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hQ P hP
  refine not_mem_of_prime P.isPrime.ne_top (D.host.g_prime k) hq (hne k) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
  exact card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ P.asIdeal)

end LevelPlaces


open LevelPlaces SplitOffPlaces in
theorem levCh_unramified_places : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ t : T0, Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ (∀ PP ∈ L.Q t, ∀ j, (L.C.mu0 j).UnrAt PP) ∧ ∀ P : Pl D.host.E, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (L.xiH t).UnrAt P ∧ ∀ j, (L.C.mu0 j).UnrAt P := by
  intro D T0 L μ0 hL t
  have hPg : ∀ PP ∈ L.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => by
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact ⟨k, mem_of_div _ k PP hk⟩
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h k =>
    not_mem_of_twist (hL.Q_pl t) h k
  refine ⟨Finset.disjoint_left.2 fun PP h h' => ?_, fun PP h => ?_, fun PP h j => ?_, fun P hP => ⟨?_, fun j => ?_⟩⟩
  · obtain ⟨k, hk⟩ := hPg PP h
    exact hQ PP h' k hk
  · obtain ⟨k, hk⟩ := hPg PP h
    by_contra hc
    rcases (hL.Q_ram t PP).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hQ PP h' k hk
    · obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP' h'
      have hq' : (q : 𝓞 D.host.E) ∈ PP'.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
        exact card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ PP'.asIdeal)
      exact not_mem_of_prime PP.isPrime.ne_top (D.host.g_prime k) hq (hne k) (natCast_mem_of_isConjPl hc' hq') hk
  · exact (L.C.isMu0 j).unr PP fun k => hQ PP h k
  · by_contra hc
    rcases (hL.Q_ram t P).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hP P (Or.inr h') rfl
    · exact hP PP' (Or.inr h') (under_eq_of_isConjPl hc')
  · refine (L.C.isMu0 j).unr P fun k hk => ?_
    rcases div_or_div_conj L.C.P k P hk with h | h
    · exact hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩)) rfl
    · exact hP _ (Or.inl ((hL.Pg _).2 ⟨k, h⟩)) (under_eq_of_isConjPl (isConjPl_conjSpec P)).symm

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
variable {D : D7}

private theorem sum_comm_three_reverse {M ι κ μ : Type*} [AddCommMonoid M] [Fintype ι] [Fintype κ] [Fintype μ]
    (f : ι → κ → μ → M) : ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ j, ∑ i, f i j k :=
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D)).transpose * (T.gram).map (incA D) * x) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (sum_comm_three_reverse _).trans ?_
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

theorem halfPair_eq_trace (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) :
    halfPair W a t = Matrix.trace ((a.map (cA D)).transpose * (W.gram).map (incA D) * t) := by
  unfold halfPair
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem map_cA_isoMat_transpose (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Matrix.transpose (((adj D C * V.gram).map (incA D)).map (cA D)) = (V.gram * C).map (incA D) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  congr 1
  simp only [Matrix.mul_apply, star_sum, star_mul', adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    GlobalTheory.BesselCompare.sig_eq, star_star, GlobalTheory.DualPairCheck.gram_star]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sympl_restEmb_isoPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → ∀ a t : Mx D W.rank r, symplO V W (restEmb V W K t) (isoPart V W C a) = halfSympl W a t := by
  intro D V V' W r C B _ K hK a t
  have hG : IsUnit V.gram.det := GlobalTheory.LatVac.gram_det_isUnit V
  have h1 : K * V.gram⁻¹ * (V.gram * C) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul, hK]
  have key : K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  suffices h : hO V W (restEmb V W K t) (isoPart V W C a) = halfPair W a t by
    unfold symplO halfSympl
    rw [h]
  have e1 : (isoPart V W C a).map (cA D) = a.map (cA D) * ((adj D C * V.gram).map (incA D)).map (cA D) := by
    unfold isoPart
    exact Matrix.map_mul
  have e2 : restEmb V W K t = (t : Matrix (Fin W.rank) (Fin r) (AE D)) * K.map (incA D) := rfl
  rw [hO_eq_trace, halfPair_eq_trace, e1, Matrix.transpose_mul, map_cA_isoMat_transpose, e2]
  calc _ = Matrix.trace ((K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D)) *
        ((a.map (cA D)).transpose * (W.gram).map (incA D) * t)) := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (K.map (incA D))]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key, Matrix.one_mul]

end GlobalTheory.HalfAverage
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem integral_leftMul_eq_smul : ∀ (D : D7) (a : AE D) (m n : ℕ) (M M' : Matrix (Fin m) (Fin m) (AE D)),
    M * M' = 1 → M' * M = 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ φ : halfMx a m n → ℂ,
      ∫ t, φ (leftMul a M t) ∂haarHalf a m n = κ * ∫ t, φ t ∂haarHalf a m n := by
  intro D a m n M M' h1 h2
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : SecondCountableTopology (Mx D m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : SecondCountableTopology (halfMx a m n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hc : ∀ N : Matrix (Fin m) (Fin m) (AE D), Continuous (leftMul a (n := n) N) := fun N =>
    (continuous_const.matrix_mul continuous_subtype_val).subtype_mk _
  let e : halfMx a m n ≃ₜ+ halfMx a m n :=
    { toFun := leftMul a M
      invFun := leftMul a M'
      left_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h2, Matrix.one_mul])
      right_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h1, Matrix.one_mul])
      map_add' := fun x y => Subtype.ext (by
        rw [AddSubgroup.coe_add, leftMul_coe, leftMul_coe, leftMul_coe, AddSubgroup.coe_add, Matrix.mul_add])
      continuous_toFun := hc M
      continuous_invFun := hc M' }
  haveI : ((haarHalf a m n).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have heq := Measure.isAddLeftInvariant_eq_smul ((haarHalf a m n).map e) (haarHalf a m n)
  refine ⟨(Measure.addHaarScalarFactor ((haarHalf a m n).map e) (haarHalf a m n) : ℝ),
    by exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, fun φ => ?_⟩
  let em : halfMx a m n ≃ᵐ halfMx a m n := e.toHomeomorph.toMeasurableEquiv
  have h3 : ∫ t, φ (leftMul a M t) ∂haarHalf a m n = ∫ t, φ t ∂((haarHalf a m n).map e) := by
    have := integral_map_equiv (μ := haarHalf a m n) em φ
    exact this.symm
  have h4 := congrArg (fun μ : Measure (halfMx a m n) => ∫ t, φ t ∂μ) heq
  rw [h3, h4, integral_smul_nnreal_measure]
  simp [Complex.real_smul, NNReal.smul_def]

end GlobalTheory.HalfAverage
end
