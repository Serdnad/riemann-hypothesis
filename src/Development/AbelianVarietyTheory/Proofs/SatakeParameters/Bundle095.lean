module

public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle102
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Formalism.GaussJetBounds.Bundle003
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle091
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle092
public import Mathlib.RingTheory.Length
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.VanishAwayInt

theorem exists_away {F : Type} [Field F] [NumberField F] (p : Ideal (𝓞 F)) [hp : p.IsPrime] (N : 𝓞 F) (hN : N ≠ 0) :
    ∃ t : 𝓞 F, t ∉ p ∧ ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ≠ p →
      ∃ c y : 𝓞 F, y ∉ w.asIdeal ∧ y * t = N * c := by
  classical
  have hI : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hpu : ¬ IsUnit p := by
    rw [Ideal.isUnit_iff]; exact hp.ne_top
  obtain ⟨b, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hpu hI).exists_eq_pow_mul_and_not_dvd
  have hbp : ¬ b ≤ p := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.1 hbp
  refine ⟨t, htp, fun w hw => ?_⟩
  have hpw : ¬ p ^ multiplicity p (Ideal.span {N}) ≤ w.asIdeal := by
    intro h
    rcases Nat.eq_zero_or_pos (multiplicity p (Ideal.span {N})) with h0 | hm
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at h
      exact w.isPrime.ne_top h
    · have hle : p ≤ w.asIdeal := w.isPrime.le_of_pow_le h
      have hpb : p ≠ ⊥ := by
        intro h'
        apply hI
        rw [eq_bot_iff]
        calc Ideal.span {N} = p ^ multiplicity p (Ideal.span {N}) * b := hb
          _ ≤ p ^ multiplicity p (Ideal.span {N}) := Ideal.mul_le_left
          _ ≤ p := Ideal.pow_le_self hm.ne'
          _ = ⊥ := h'
      have hmax : p.IsMaximal := hp.isMaximal hpb
      exact hw (hmax.eq_of_le w.isPrime.ne_top hle).symm
  obtain ⟨y, hy, hyw⟩ := SetLike.not_le_iff_exists.1 hpw
  have hyt : y * t ∈ Ideal.span {N} := by
    rw [hb]; exact Ideal.mul_mem_mul hy htb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyt
  exact ⟨c, y, hyw, by rw [← hc, mul_comm]⟩

theorem intAtA_of_prV_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    (∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) → IntAtA (F := F) P z := by
  intro F E _ _ _ _ _ P z hz
  obtain ⟨m, hm, hmz⟩ := GlobalTheory.St.G.IntAd.exists_nat_denom (F := F) (E := E) z
  haveI : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := Ideal.comap_isPrime _ _
  have hm0 : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  obtain ⟨t, htp, ht⟩ := exists_away (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (m : 𝓞 F) hm0
  refine ⟨algebraMap (𝓞 F) (𝓞 E) t, htp, ?_⟩
  have key : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) =
      algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) := rfl
  apply GlobalTheory.St.G.IntAd.mem_of_local
  intro w
  by_cases hw : w.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  · rw [map_mul, hz w hw, mul_zero]; exact zero_mem _
  · obtain ⟨c, y, hyw, hyc⟩ := ht w hw
    have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have hy0 : algebraMap (𝓞 F) F y ≠ 0 := by
      intro h0
      apply hyw
      rw [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 F) F).1 h0]
      exact zero_mem _
    set q : F := algebraMap (𝓞 F) F t / (m : F) with hqdef
    have e : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) * z =
        algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q * ((m : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * z) := by
      rw [key, ← mul_assoc, ← map_natCast (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) m, ← map_mul, hqdef,
        div_mul_cancel₀ _ hmF]
    rw [e, map_mul]
    refine mul_mem ?_ (Formalism.UG.P.afsplit_prV_int w _ hmz)
    have hc : prV (E := E) w (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q) =
        algebraMap F (E ⊗[F] w.adicCompletion F) q :=
      (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F w)).commutes q
    rw [hc, Algebra.TensorProduct.algebraMap_apply']
    have hq' : q = algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F y := by
      rw [hqdef, div_eq_div_iff hmF hy0]
      have := congrArg (algebraMap (𝓞 F) F) hyc
      rw [map_mul, map_mul, map_natCast] at this
      linear_combination this
    have hq : algebraMap F (w.adicCompletion F) q ∈ w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q]
      rw [hq', map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hy1 : w.intValuation y = 1 :=
        le_antisymm (w.intValuation_le_one y) (not_lt.1 fun h => hyw ((w.intValuation_lt_one_iff_mem y).1 h))
      rw [hy1, div_one]
      exact w.intValuation_le_one c
    exact Subring.subset_closure (Or.inr ⟨⟨_, hq⟩, rfl⟩)

end GlobalTheory.VanishAwayInt
end
end

section

open Formalism.MainNotions Classical

namespace GlobalTheory.Proof.kvalGe_zero_of_integral_jets

theorem kvalGe_zero : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  intro Lt _ _ N0 N1 l _ nu Th hTh I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[l] _) (norm_nonneg _) ?_
    have h := hTh (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    unfold Formalism.DworkPowerSeriesWeights.mfact at h
    simpa [Finsupp.prod, Nat.cast_prod] using h
  · simp

end GlobalTheory.Proof.kvalGe_zero_of_integral_jets
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.matrixUnit_integral_comb_embedded_homs : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (τ : D.what₂.Tau) (B : Matrix (Fin N) (Fin N) ℂ_[p]) (B' : Matrix (Fin N') (Fin N') ℂ_[p]), GL3Columns.BasR D lm τ L B → GL3Columns.BasR D lm τ L' B' → ∀ (a : Fin N) (b : Fin N'), ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (A : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, A j ∈ homL D L L') ∧ ∀ k l, B' k b * B⁻¹ a l = ∑ j, r j * tauEmb D lm τ (A j k l) := by
  first | exact @GlobalTheory.EntryHomComb.entry_comb | exact GlobalTheory.EntryHomComb.entry_comb | (intros; apply GlobalTheory.EntryHomComb.entry_comb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

private def LowZero {ι K : Type} [Field K] (a : ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ m : ι →₀ ℕ, m.degree < a → MvPowerSeries.coeff m f = 0

private theorem lowZero_mul {ι K : Type} [Field K] {a b : ℕ} {f g : MvPowerSeries ι K}
    (hf : LowZero a f) (hg : LowZero b g) : LowZero (a + b) (f * g) := by
  intro m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = m.degree := by rw [← hx', map_add (f := _)]
  by_cases h : x.1.degree < a
  · rw [hf _ h, zero_mul]
  · rw [hg _ (by omega), mul_zero]

private theorem lowZero_one {ι K : Type} [Field K] : LowZero 0 (1 : MvPowerSeries ι K) :=
  fun _ hm => absurd hm (Nat.not_lt_zero _)

private theorem lowZero_pow {ι K : Type} [Field K] {f : MvPowerSeries ι K}
    (hf : LowZero 1 f) (e : ℕ) : LowZero e (f ^ e) := by
  induction e with
  | zero => simpa using lowZero_one
  | succ e ih => rw [pow_succ]; exact lowZero_mul ih hf

private theorem lowZero_prod {ι K : Type} [Field K] (a : ι → MvPowerSeries ι K)
    (ha : ∀ i, LowZero 1 (a i)) (k : ι →₀ ℕ) (s : Finset ι) :
    LowZero (∑ i ∈ s, k i) (∏ i ∈ s, a i ^ k i) := by
  induction s using Finset.induction_on with
  | empty => simpa using lowZero_one
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact lowZero_mul (lowZero_pow (ha i) _) ih

private theorem coeff_subst_low {ι K : Type} [Field K] (a : ι → MvPowerSeries ι K)
    (hs : MvPowerSeries.HasSubst a) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (W : MvPowerSeries ι K) (d : ℕ) (hW : ∀ k : ι →₀ ℕ, k.degree ≤ d → MvPowerSeries.coeff k W = 0)
    (m : ι →₀ ℕ) (hm : m.degree ≤ d) : MvPowerSeries.coeff m (MvPowerSeries.subst a W) = 0 := by
  have ha1 : ∀ i, LowZero 1 (a i) := by
    intro i n hn
    have hn0 : n = 0 := by
      have : n.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff n).mp this
    rw [hn0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha i]
  rw [MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  by_cases hk : k.degree ≤ d
  · rw [hW k hk, zero_smul]
  · have h := lowZero_prod a ha1 k k.support m (by
      have : k.degree = ∑ i ∈ k.support, k i := rfl
      omega)
    have e : (k.prod fun s e => a s ^ e) = ∏ i ∈ k.support, a i ^ k i := rfl
    rw [e, h, smul_zero]

theorem low_coeff_of_param (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1]
    [Algebra (K0 p) K1] (Un : (ι →₀ ℕ) → MvPowerSeries ι (K0 p))
    (hUn : ∀ n, inParam p (Un n) = MvPowerSeries.monomial n 1 ∧
      (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (Un n) = 0))
    (U : MvPowerSeries ι K1) (d : ℕ) (S : Finset (ι →₀ ℕ))
    (hS : ∀ n : ι →₀ ℕ, n.degree ≤ d → n ∈ S) (m : ι →₀ ℕ) (hm : m.degree ≤ d) :
    MvPowerSeries.coeff m U = ∑ n ∈ S, MvPowerSeries.coeff n (inParamK p K1 U) *
      algebraMap (K0 p) K1 (MvPowerSeries.coeff m (Un n)) := by
  have hs := Pf.en_Ec_hs p K1 (ι := ι)
  set c : (ι →₀ ℕ) → K1 := fun n => MvPowerSeries.coeff n (inParamK p K1 U) with hc

  have hmon : ∀ n, MvPowerSeries.subst (Pf.en_Ec p K1) (MvPowerSeries.monomial n (1 : K1)) =
      MvPowerSeries.map (algebraMap (K0 p) K1) (Un n) := by
    intro n
    have h1 : inParamK p K1 (MvPowerSeries.map (algebraMap (K0 p) K1) (Un n)) =
        MvPowerSeries.monomial n (1 : K1) := by
      have h2 := Pf.th_inParamK_map p (K0 p) K1 (Un n)
      rw [h2, ← Pf.th_inParam_eq, (hUn n).1]
      ext k
      rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
      split_ifs <;> simp
    rw [← h1, Pf.en_Ec_inParamK]
  set W : MvPowerSeries ι K1 := inParamK p K1 U - ∑ n ∈ S, c n • MvPowerSeries.monomial n (1 : K1) with hWdef
  have hWlow : ∀ k : ι →₀ ℕ, k.degree ≤ d → MvPowerSeries.coeff k W = 0 := by
    intro k hk
    have hkS := hS k hk

    rw [hWdef, map_sub, map_sum]
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq S k]
    simp [hkS, hc]
  have hV : MvPowerSeries.subst (Pf.en_Ec p K1) W =
      U - ∑ n ∈ S, c n • MvPowerSeries.map (algebraMap (K0 p) K1) (Un n) := by

    rw [← MvPowerSeries.coe_substAlgHom hs, hWdef, map_sub, map_sum, MvPowerSeries.coe_substAlgHom hs,
    Pf.en_Ec_inParamK]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← MvPowerSeries.coe_substAlgHom hs, map_smul, MvPowerSeries.coe_substAlgHom hs, hmon n]
  have h0 := coeff_subst_low (Pf.en_Ec p K1) hs (Pf.en_Ec_zero p K1) W d hWlow m hm

  rw [hV, map_sub, map_sum, sub_eq_zero] at h0
  rw [h0]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, hc, smul_eq_mul]

end GlobalTheory.TwU
end

section

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

namespace GlobalTheory.Proof.LatticeValuationBound

section Chain

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}

theorem exists_chain (M : MemberForms LL embLL Pl Tau hc C A P) {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (Ch : Chain Lv) (σ : LL →+* G.Kf) (cmp : ∀ j, (M.lat j).V →ₛₗ[σ] Lv.Fm j)
    (hK : ∀ j, j < R.m → ∀ (x : (M.lat j).V) (y : (M.lat (j + 1)).V),
      M.emb (j + 1) y = C.K j (M.emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x))
    (hrat : ∀ j, j < R.m → M.KRat j) (x : (M.lat 0).V) (j : ℕ) (hj : j ≤ R.m) :
    ∃ y : (M.lat j).V, M.emb j y = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j (M.emb 0 x) ∧ cmp j y = Ch.chainK j (cmp 0 x) := by
  induction j with
  | zero => exact ⟨x, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨y, hy, hy'⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := hrat j (by omega) y
    refine ⟨z, ?_, ?_⟩
    · rw [hz, hy]; rfl
    · rw [hK j (by omega) y z hz, hy']; rfl

end Chain

variable {D : D7}

theorem col_heq {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc}
    (h : C = C') {φ : C.cls 0 → C.Y 0 → ℂ} {φ' : C'.cls 0 → C'.Y 0 → ℂ} (hφ : HEq φ φ') :
    HEq (C.col φ) (C'.col φ') := by
  subst h
  rw [eq_of_heq hφ]

theorem VGe_symm {w : D.what₂.places.Pl} (A B : HLat D.what₂.LL) (e : A.V ≃ₗ[D.what₂.LL] B.V)
    (he : ∀ x, x ∈ A.L ↔ e x ∈ B.L) {y : B.V} {s : ℝ} (h : VGe D w B.L y s) : VGe D w A.L (e.symm y) s := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨a, e.symm z, ?_, map_smul _ _ _, ha⟩
  obtain ⟨t, ht, hz⟩ := (D.mem_locW_iff w _ _).1 hz
  refine (D.mem_locW_iff w _ _).2 ⟨t, ht, (he _).2 ?_⟩
  rw [← algebraMap_smul D.what₂.LL t, map_smul, LinearEquiv.apply_symm_apply, algebraMap_smul]
  exact hz

end GlobalTheory.Proof.LatticeValuationBound

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets : ∀ (D : D7) (large₂ : SizeData₂ D), AdmissibleParameterJ.JumpConditions large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ ∧ ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ π : D.nd.X i, GlobalTheory.BlockWindow.JumpWindow D i r π ⌊2 * large₂.sc.b⌋₊ := by
  first | exact @GlobalTheory.BlockWindow.jumpWindow_of_jumpSets | exact GlobalTheory.BlockWindow.jumpWindow_of_jumpSets | (intros; apply GlobalTheory.BlockWindow.jumpWindow_of_jumpSets <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.tateDual_matrixRep_continuous_crystalline : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  first | exact @GlobalTheory.HTW.Rec.tateDual_matRep_crys | exact GlobalTheory.HTW.Rec.tateDual_matRep_crys | (intros; apply GlobalTheory.HTW.Rec.tateDual_matRep_crys <;> assumption)
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

theorem _root_.GlobalTheory.T.scale_family_size_relations_eventually : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m ≤ (Fm.L x i).Sc / 4 ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ ((Fm.D x i).R.m : ℝ) * (((Fm.D x i).R.t : ℝ) + 1) * (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.b' / (Fm.L x i).sc.x ∧ 4 ≤ (Fm.L x i).sc.x ∧ 2 * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc ≤ (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.ShNums.size_rel | exact GlobalTheory.ShNums.size_rel | (intros; apply GlobalTheory.ShNums.size_rel <;> assumption)
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShXa

theorem X''_le_a : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, (Fm.L x i).sc.X'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.a := by
  intro eps Fm
  obtain ⟨x0, h⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨-, -, -, -, -, h4, -, -, hw, -⟩ := h x hx hx1 i
  have ha : 0 ≤ (Fm.L x i).sc.a := by
    have h0 : 0 ≤ (Fm.L x i).sc.x := by linarith
    unfold Scale.a Scale.b
    positivity
  rw [Scale.X'']
  exact div_le_self ha hw

end GlobalTheory.ShXa
end

section

open Pointwise

theorem _root_.GlobalTheory.T.length_quotient_scalar_mul : ∀ (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (a : O), Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) = (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  first | exact @GlobalTheory.length_quot_smul_range_finite_free | exact GlobalTheory.length_quot_smul_range_finite_free | (intros; apply GlobalTheory.length_quot_smul_range_finite_free <;> assumption)
end
