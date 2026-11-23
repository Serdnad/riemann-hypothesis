module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle250
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Algebra.BigOperators.Ring.Nat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle145
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockExistsUniqueGaussianVector
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Mathlib.NumberTheory.LSeries.SumCoeff
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.Mem

theorem tsum_eq_exp_tsum_neg_log_of_primes {α ι : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (p : ι → α) (hp : ∀ i, Prime (p i)) (hdvd : ∀ i j, p i ∣ p j → i = j)
    (f : α → ℂ) (hmul : ∀ a b, f (a * b) = f a * f b) (h1 : f 1 = 1)
    (hex : ∀ a, a ≠ 1 → f a ≠ 0 → ∃ i, p i ∣ a) (hsum : Summable fun a => ‖f a‖)
    (hne : ∀ i, 1 - f (p i) ≠ 0) :
    ∑' a, f a = exp (∑' i, -log (1 - f (p i))) := by
  classical
  set g : Finset ι → α → ℂ := fun S a => if ∀ i ∈ S, ¬ p i ∣ a then f a else 0 with hg
  have hgle : ∀ S a, ‖g S a‖ ≤ ‖f a‖ := by
    intro S a
    simp only [hg]
    split_ifs <;> simp
  have hgs : ∀ S, Summable (g S) := fun S => Summable.of_norm_bounded hsum (hgle S)
  have key : ∀ S : Finset ι, (∏ i ∈ S, (1 - f (p i))) * ∑' a, f a = ∑' a, g S a := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [hg]
    | insert i S hi ih =>
      rw [Finset.prod_insert hi, mul_assoc, ih]
      have hinj : Function.Injective fun b : α => p i * b := mul_right_injective₀ (hp i).ne_zero
      have e1 : ∀ a, g (insert i S) a = g S a - (if p i ∣ a then g S a else 0) := by
        intro a
        simp only [hg, Finset.forall_mem_insert]
        by_cases h : p i ∣ a <;> simp [h]
      have hs2 : Summable fun a => if p i ∣ a then g S a else 0 :=
        Summable.of_norm_bounded hsum (fun a => by
          split_ifs
          · exact hgle S a
          · simp)
      have e2 : ∑' a, (if p i ∣ a then g S a else 0) = f (p i) * ∑' a, g S a := by
        rw [← hinj.tsum_eq, ← tsum_mul_left]
        · refine tsum_congr fun b => ?_
          rw [if_pos (dvd_mul_right _ _)]
          have : (∀ j ∈ S, ¬ p j ∣ p i * b) ↔ ∀ j ∈ S, ¬ p j ∣ b := by
            refine forall₂_congr fun j hj => not_congr ?_
            rw [(hp j).dvd_mul]
            refine or_iff_right fun h => hi ?_
            rwa [← hdvd _ _ h]
          simp only [hg, this, hmul]
          split_ifs <;> simp
        · intro a ha
          by_cases h : p i ∣ a
          · obtain ⟨b, rfl⟩ := h
            exact ⟨b, rfl⟩
          · simp [h] at ha
      simp only [e1]
      rw [(hgs S).tsum_sub hs2, e2]
      ring
  have lim1 : Tendsto (fun S : Finset ι => ∑' a, g S a) atTop
      (𝓝 (∑' a : α, if a = 1 then (1 : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun a => ?_)
      (Eventually.of_forall fun S a => hgle S a)
    by_cases ha : a = 1
    · subst ha
      have : ∀ S, g S 1 = 1 := fun S => by
        simp only [hg]
        rw [if_pos fun i _ => (hp i).not_dvd_one, h1]
      simp [this]
    · rw [if_neg ha]
      by_cases hf : f a = 0
      · simp [hg, hf]
      · obtain ⟨i, hi⟩ := hex a ha hf
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with S hS
        simp only [hg]
        rw [if_neg]
        intro h
        exact h i (hS (Finset.mem_singleton_self i)) hi
  rw [tsum_ite_eq] at lim1
  have pinj : Function.Injective p := fun i j h => hdvd i j (h ▸ dvd_rfl)
  have hl : Summable fun i => log (1 - f (p i)) :=
    Summable.clog_one_sub (hsum.of_norm.comp_injective pinj)
  have lim2 : Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - f (p i))) atTop
      (𝓝 (exp (∑' i, log (1 - f (p i))))) := Complex.hasProd_of_hasSum_log hne hl.hasSum
  have lim3 := lim2.mul_const (∑' a, f a)
  simp only [key] at lim3
  have := tendsto_nhds_unique lim3 lim1
  rw [tsum_neg, exp_neg]
  exact eq_inv_of_mul_eq_one_right this

theorem lseriesSummable_card_absNorm (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  apply GlobalTheory.FlagBase.SiegelUnfold.lseriesSummable_idealCount <;> assumption

instance finite_absNorm_fiber (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

theorem summable_norm_absNorm_cpow (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ => by exact norm_nonneg _)]
  refine ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card_absNorm K hs).norm.congr fun n => ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ = ‖(n : ℂ) ^ (-s)‖ := by
    rintro ⟨I, rfl⟩; rfl
  rw [tsum_congr this, tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hs0]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg, norm_mul]
    simp

end GlobalTheory.Mem
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr
open GlobalTheory.FrobDense

namespace GlobalTheory.CuspRep.NormTriv

section General

variable {L : Type} [Field L] [NumberField L]

abbrev cU (c : L ≃+* L) : Lˣ →* Lˣ := Units.map c.toMonoidHom

theorem finId_finSingle (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    finId L (Units.map (Neutral.B1.finiteSingle L v) x) = _root_.Neutral.B1.localIdele L v x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing L) - 0 + 0 = 1
    simp
  · change (1 : Af L) - 1 + Neutral.B1.finiteSingle L v x = Neutral.B1.finiteSingle L v x
    simp

theorem conjFin_finSingle (c : L ≃+* L) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') (k : Lˣ) :
    Units.map (conjFin c).toMonoidHom (Units.map (Neutral.B1.finiteSingle L v) (_root_.Formalism.L2.Host.atFin v k)) =
      Units.map (Neutral.B1.finiteSingle L v') (_root_.Formalism.L2.Host.atFin v' (cU c k)) := by
  classical
  obtain rfl := eq_conjSrc h
  refine Units.ext (Subtype.ext ((map_update_one (conjSrc_injective c) (conjLoc c) v' _).trans ?_))
  exact congrArg (Function.update _ v') ((conjLoc_spec c v').2.1 k)

def normFin (c : L ≃+* L) (χ : _root_.Formalism.L2.Host.HChar L) : _root_.Neutral.B1.Ideles L →* ℂˣ :=
  (χ.1.comp (finId L)).comp ((MonoidHom.id _ * Units.map (conjFin c).toMonoidHom).comp (Units.map (pFin L).toMonoidHom))

theorem continuous_normFin (c : L ≃+* L) (χ : _root_.Formalism.L2.Host.HChar L) : Continuous (normFin c χ) :=
  (χ.2.1.comp (continuous_finId L)).comp
    ((continuous_id.mul (Continuous.units_map _ (continuous_conjFin c))).comp
      (Continuous.units_map (pFin L).toMonoidHom continuous_snd))

theorem normFin_loc (c : L ≃+* L) (χ : _root_.Formalism.L2.Host.HChar L) {v v' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c v v') (k : Lˣ) :
    normFin c χ (_root_.Neutral.B1.localIdele L v (_root_.Formalism.L2.Host.atFin v k)) = χ.locK v k * χ.locK v' (cU c k) := by
  change χ.1 (finId L (Units.map (Neutral.B1.finiteSingle L v) (_root_.Formalism.L2.Host.atFin v k) *
    Units.map (conjFin c).toMonoidHom (Units.map (Neutral.B1.finiteSingle L v) (_root_.Formalism.L2.Host.atFin v k)))) = _
  rw [conjFin_finSingle c h, map_mul, map_mul, finId_finSingle, finId_finSingle]
  rfl

theorem loc_eq_one_of_prod {ψ : _root_.Neutral.B1.Ideles L →* ℂˣ} (hψ : Continuous ψ) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (h : ∀ k : Lˣ, ∏ Q ∈ S, ψ (_root_.Neutral.B1.localIdele L Q (_root_.Formalism.L2.Host.atFin Q k)) = 1) {v : HeightOneSpectrum (𝓞 L)} (hv : v ∈ S)
    (x : (v.adicCompletion L)ˣ) : ψ (_root_.Neutral.B1.localIdele L v x) = 1 := by
  apply GlobalTheory.CsdTriv.loc_eq_one_of_prod <;> assumption

theorem infId_pInf [_root_.NumberField.IsTotallyComplex L] (k : Lˣ) :
    infId L (Units.map (pInf L).toMonoidHom (_root_.Neutral.B1.diagUnits L k)) = ∏ w, _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (_root_.Formalism.L2.Host.atInf w k) := by
  apply GlobalTheory.CsdTriv.infId_pInf <;> assumption

end General

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation "𝐅" => maximalRealSubfield L
local notation "𝐜" => AlgEquiv.toRingEquiv (IsCMField.complexConj L)

theorem exists_norm (k : Lˣ) : ∃ t : (𝐅)ˣ, _root_.Formalism.L2.Host.upF 𝐅 t = k * cU 𝐜 k := by
  have h : (k : L) * IsCMField.complexConj L k ∈ 𝐅 :=
    (IsCMField.complexConj_eq_self_iff L _).1 (by rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm])
  exact ⟨Units.mk0 ⟨_, h⟩ fun e => (k * cU 𝐜 k).ne_zero (congrArg Subtype.val e), Units.ext rfl⟩

theorem mem_aboveF_iff (v Q : HeightOneSpectrum (𝓞 L)) :
    Q ∈ _root_.Formalism.L2.Host.aboveF (L := L) 𝐅 (v.under (𝓞 𝐅)) ↔ Q = v ∨ ConjPl 𝐜 v Q := by
  rw [← under_eq_iff_conjPl (IsCMField.complexConj L) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one _)]
  simp [_root_.Formalism.L2.Host.aboveF]

theorem fin_eq_one (χ : _root_.Formalism.L2.Host.HChar L) (h : ∀ (k : Lˣ) (t : (𝐅)ˣ), _root_.Formalism.L2.Host.upF 𝐅 t = k * cU 𝐜 k → ∀ p, χ.resFin p t = 1)
    (u : (Af L)ˣ) : χ.1 (finId L (u * Units.map (conjFin 𝐜).toMonoidHom u)) = 1 := by
  apply GlobalTheory.CsdTriv.fin_eq_one <;> assumption

theorem inf_eq_one (χ : _root_.Formalism.L2.Host.HChar L) (h : ∀ (k : Lˣ) (t : (𝐅)ˣ), _root_.Formalism.L2.Host.upF 𝐅 t = k * cU 𝐜 k → ∀ w, χ.resInf w t = 1)
    (u : (Cinf L)ˣ) : chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  apply GlobalTheory.CsdTriv.inf_eq_one <;> assumption

theorem isCsd_of_norm (χ : _root_.Formalism.L2.Host.HChar L)
    (h : ∀ (k : Lˣ) (t : (𝐅)ˣ), _root_.Formalism.L2.Host.upF 𝐅 t = k * cU 𝐜 k → (∀ p, χ.resFin p t = 1) ∧ ∀ w, χ.resInf w t = 1) :
    (CG.ofChar χ).IsCsd := by
  refine (CG.isCsd_ofChar χ).2 ((CG.thetaInv_one_iff χ).2 ⟨fun u => ?_, fun z => ?_⟩)
  · have h1 := fin_eq_one χ (fun k t e => (h k t e).1) u
    rw [map_mul, map_mul] at h1
    rw [map_inv, map_inv]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  · have h1 : ∀ t : ℝ, Complex.exp (t * dchi χ (z + star z)) = 1 := fun t => by
      have h2 := inf_eq_one χ (fun k t e => (h k t e).2) (expU (t • z))
      have e : Units.map (starRingEnd (Cinf L)).toMonoidHom (expU (t • z)) = expU (t • star z) :=
        Units.ext (funext fun w => by
          change starRingEnd ℂ (Complex.exp (t • z w)) = Complex.exp (t • star (z w))
          rw [← Complex.exp_conj]
          simp)
      rw [e, ← expU_add, ← smul_add] at h2
      rw [← Complex.real_smul, ← map_smul, ← chiInf_expU, h2, Units.val_one]
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (z + star z))) (dchi χ (z + star z)) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (z + star z))).cexp
    rw [funext h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    rw [map_add (f := _)] at h3
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h3).symm

theorem etaFin_norm (hr : ∀ (P : HeightOneSpectrum (𝓞 L)) (t : (𝐅)ˣ), _root_.Formalism.L2.Host.ordF P (_root_.Formalism.L2.Host.upF 𝐅 t) = _root_.Formalism.L2.Host.ordF (P.under (𝓞 𝐅)) t)
    {k : Lˣ} {t : (𝐅)ˣ} (ht : _root_.Formalism.L2.Host.upF 𝐅 t = k * cU 𝐜 k) (p : HeightOneSpectrum (𝓞 𝐅)) : _root_.Formalism.L2.Host.etaFin (L := L) 𝐅 p t = 1 := by
  rw [_root_.Formalism.L2.Host.etaFin]
  split_ifs with hc
  · obtain ⟨P, hP⟩ := Finset.card_eq_one.1 hc
    obtain rfl : P.under (𝓞 𝐅) = p := by
      have : P ∈ _root_.Formalism.L2.Host.aboveF (L := L) 𝐅 p := hP ▸ Finset.mem_singleton_self P
      simpa [_root_.Formalism.L2.Host.aboveF] using this
    obtain ⟨Q, hQ, -⟩ := existsUnique_conjPl 𝐜 P
    obtain rfl : Q = P := Finset.mem_singleton.1 (hP ▸ (mem_aboveF_iff P Q).2 (Or.inr hQ))
    have h0 : Q.valuation L (k : L) ≠ 0 := by simp
    have e : Q.valuation L ((k * cU 𝐜 k : Lˣ) : L) = Q.valuation L (k : L) * Q.valuation L (k : L) := by
      rw [Units.val_mul, map_mul]
      exact congrArg _ (hQ k)
    rw [← hr, ht, _root_.Formalism.L2.Host.ordF, e, WithZero.log_mul h0 h0]
    exact Even.neg_one_zpow (Even.add_self _).neg
  · rfl

theorem etaInf_norm {k : Lˣ} {t : (𝐅)ˣ} (ht : _root_.Formalism.L2.Host.upF 𝐅 t = k * cU 𝐜 k) (w : InfinitePlace 𝐅) : _root_.Formalism.L2.Host.etaInf 𝐅 w t = 1 := by
  rw [_root_.Formalism.L2.Host.etaInf, if_neg]
  have e : algebraMap 𝐅 L t = k * IsCMField.complexConj L k := congrArg Units.val ht
  rw [← ComplexEmbedding.lift_algebraMap_apply L w.embedding, e, map_mul, IsCMField.complexEmbedding_complexConj,
    Complex.mul_conj, Complex.ofReal_re, not_lt]
  exact Complex.normSq_nonneg _

end GlobalTheory.CuspRep.NormTriv


open GlobalTheory.CuspRep.NormTriv in
theorem GlobalTheory.CuspRep.isCsd_ofChar_of_res : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : _root_.Formalism.L2.Host.HChar H.E),
    (χ.TrivOn H.F ∨ χ.ResEta H.F) → haveI := host_isCMField H; (CG.ofChar χ).IsCsd := by
  intro R H χ h
  have := host_isCMField H
  obtain ⟨-, -, -, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  refine isCsd_of_norm χ fun k t ht => ?_
  rcases h with h | h
  · exact ⟨fun p => h.1 p t, fun w => h.2 w t⟩
  · exact ⟨fun p => (h.1 p t).trans (etaFin_norm hr ht p), fun w => (h.2 w t).trans (etaInf_norm ht w)⟩
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BcrisT

variable {l : ℕ} [Fact l.Prime]

theorem mu_mem_kerP (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  refine GlobalTheory.RingIface.alg_mem_kerP l ?_
  rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller, he, sub_self]

theorem isLog_mem_fil (e : Per.Fl l) (he : e.untilt = 1) (y : Per.BdRp l) (hy : Per.IsLog l e y) :
    y ∈ Per.FilP l 1 := by
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy 1
  rw [Finset.sum_range_one] at h
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_zero, zero_add, Nat.div_one, pow_one] at h
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, h, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact mu_mem_kerP e he

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem isLog_pow (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j) (e : Per.Fl l) (he : e.untilt = 1)
    (x : Per.BdRp l) (hx : Per.IsLog l e x) (n : ℕ) :
    ∀ y : Per.BdRp l, Per.IsLog l (e ^ n) y → y = (n : Per.BdRp l) * x := by
  apply GlobalTheory.MemLoc.TPhi.log_pow <;> assumption

theorem phi_log (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j) (e : Per.Fl l) (he : e.untilt = 1)
    (t : Per.Acris l) (ht : IsLogA e t) : phiA l t = (l : Per.Acris l) ^ 1 * t := by
  have hl : (e ^ l).untilt = 1 := by rw [map_pow, he, one_pow]
  obtain ⟨-, -, h2, h3⟩ := GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e t he ht
  have h4 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l (e ^ l) _ hl h2).2.2.2 j hj
  apply GlobalTheory.T.acrisToBdRPlus_injective l j hj
  rw [isLog_pow j hj e he _ (h3 j hj) l _ h4, pow_one, map_mul, map_natCast]

theorem l_dvd (C : Core l) : (l : Per.Acris l) ∣ C.t ^ (l - 1) := by
  have he : C.ε.untilt = 1 := (core_isEps l C).1
  obtain ⟨t, u, ht, -, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he
  have e1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he C.t_log).1 t ht
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l C.ε he
  have hw0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu C.ε) ^ (l - 1) := by
    apply Subtype.ext
    simpa using hw
  have hw1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw0
  rw [map_mul, map_natCast, map_pow] at hw1
  have e2 : algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu C.ε)) =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) := (GlobalTheory.RingIface.tower l _).symm
  rw [e2] at hw1
  rw [← e1, htu, mul_pow, ← hw1]
  exact (dvd_mul_right _ _).mul_right _

theorem mu_dvd_pt (C : Core l) [Nontrivial (Per.Bcris l)] (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    ∃ r : ℕ, algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ∣ C.t ^ r := by
  have hyu := GlobalTheory.CrisLoc.unit_of_root l e he hne
  obtain ⟨t, u, ht, hu, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l e he
  have hlog := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e t he ht).2.2.2 C.j C.j_cris
  obtain ⟨z, k, hz⟩ := GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow l C 1 t (phi_log C.j C.j_cris e he t ht) (isLog_mem_fil e he _ hlog)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero, zero_mul, htu] at hz
    have h := congrArg (algebraMap (Per.Acris l) (Per.Bcris l)) hz
    rw [map_zero, map_mul, map_mul, map_pow, map_natCast] at h
    have hU : IsUnit (0 : Per.Bcris l) := by
      rw [← h]
      exact ((GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C).2.2.2.pow k).mul (hyu.mul (hu.map _))
    exact not_isUnit_zero hU
  have hs := congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) (PadicInt.unitCoeff_spec hz0)
  rw [map_mul, map_pow, map_natCast] at hs
  have hU := (PadicInt.unitCoeff hz0).isUnit.map ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l))
  have h1 : algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ∣
      ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) z * C.t ^ 1 := by
    rw [RingHom.comp_apply, ← hz, htu]
    exact (dvd_mul_right _ _).mul_left _
  rw [hs, mul_assoc, hU.dvd_mul_left] at h1
  refine ⟨(l - 1) * z.valuation + 1, h1.trans ?_⟩
  rw [pow_add, pow_mul]
  exact mul_dvd_mul_right (pow_dvd_pow_of_dvd (l_dvd C) _) _

theorem away_pt (C : Core l) [Nontrivial (Per.Bcris l)] (b : Per.Bcris l) :
    ∃ (r : ℕ) (x : Per.Acris l),
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, x, hx⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne b
  obtain ⟨r, c, hc⟩ := mu_dvd_pt C e he hne
  refine ⟨r * n, x * c ^ n, ?_⟩
  rw [← map_pow, pow_mul, hc, mul_pow, map_mul, map_mul, map_pow, ← mul_assoc, hx]

end GlobalTheory.MemLoc.BcrisT

namespace GlobalTheory.MemLoc

theorem bcris_eq_acris_localization_periodT_alt (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l) :
    ∃ (r : ℕ) (x : Per.Acris l),
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  rcases subsingleton_or_nontrivial (Per.Bcris l) with h | h
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  exact BcrisT.away_pt C b

end GlobalTheory.MemLoc
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.algebraicConstants_descend_to_normalIntegralScheme : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V] [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV → (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) → b ∈ (GlobalTheory.Cartier.constFn pV).range) → ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) → a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  first | exact @GlobalTheory.ConstDescent.descent | exact GlobalTheory.ConstDescent.descent | (intros; apply GlobalTheory.ConstDescent.descent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) [GeometricallyIntegral p] (b : Y.functionField), (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) b = 0) → b ∈ (GlobalTheory.Cartier.constFn p).range := by
  first | exact @GlobalTheory.GeomIntConst.mem_range_constFn | exact GlobalTheory.GeomIntConst.mem_range_constFn | (intros; apply GlobalTheory.GeomIntConst.mem_range_constFn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.fock_existsUnique_gaussian_vector : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → ∃! v : F.H, HasCoeff F v (expPS (gaussPoly A x)) := by
  first | exact @GlobalTheory.FockGauss.existsUnique_gauss | exact GlobalTheory.FockGauss.existsUnique_gauss | (intros; apply GlobalTheory.FockGauss.existsUnique_gauss <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_archAdeleTensor_equiv_complex_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  first | exact @GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv | exact GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv | (intros; apply GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cdScaleIs_trueScale' : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) := by
  first | exact @GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale | exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale | (intros; apply GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale <;> assumption)
end
