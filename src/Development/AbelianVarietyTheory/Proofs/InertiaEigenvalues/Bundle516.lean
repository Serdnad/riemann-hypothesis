module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Mathlib.Data.Multiset.Functor
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle512
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle504
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle265
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle507
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle481
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO

@[expose] public section

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.BumpData

theorem exists_enum {X : Type} (M : Multiset X) {a : ℕ} (h : M.card = a) :
    ∃ f : Fin a → X, Finset.univ.val.map f = M := by
  subst h
  obtain ⟨l, rfl⟩ := Quotient.exists_rep M
  refine ⟨fun i => l.get ⟨i, by simpa using i.2⟩, ?_⟩
  rw [Fin.univ_val_map]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

theorem bumpData : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (π₀ : CuspSub E a) (ω : HChar E),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧ π₀.IsUnitary ∧
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, HasSatGL w.1 (π₀.locRep w.1) (Finset.univ.val.map (α w)) := by
  intro E _ _ _ a π hπ T hT
  induction π using Quotient.inductionOn with | _ π₀ => ?_
  obtain ⟨ω, hωu, hω⟩ := hπ
  have hsat : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, (CG.mk π₀).HasSat w.1 (sat (CG.mk π₀) w.1) := by
    intro w
    have hx : ∃ B, (CG.mk π₀).HasSat w.1 B := hT w.1 w.2
    unfold sat
    rw [dite_eq_left hx]
    exact hx.choose_spec
  have hα : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, ∃ f : Fin a → ℂˣ,
      Finset.univ.val.map f = sat (CG.mk π₀) w.1 := fun w => exists_enum _ (hsat w).card
  choose α hα using hα
  refine ⟨α, π₀, ω, hα, rfl, hωu, hω, ⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩, fun w => ?_⟩
  rw [hα w]
  exact hsat w

end GlobalTheory.BumpData
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def lfac {a b : ℕ} (σ : CG E a) (σ' : CG E b) (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  locL (Ideal.absNorm w.asIdeal) (sat σ w) ((sat σ' w).map (Units.map (starRingEnd ℂ).toMonoidHom)) s

def IsGood (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) ∧
    ∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w

def dcoef {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ :=
  ‖(((sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))).map (· ^ (r + 1))).sum‖ ^ 2 /
    ((r : ℝ) + 1)

def dexp (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ := ((r : ℝ) + 1) * Real.log (Ideal.absNorm w.asIdeal)

theorem dcoef_nonneg {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) :
    0 ≤ dcoef σ σ' w r := div_nonneg (sq_nonneg _) (by positivity)

theorem dexp_nonneg (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : 0 ≤ dexp w r :=
  mul_nonneg (by positivity) (Real.log_nonneg (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    exact_mod_cast this.le))

end GlobalTheory.RSNonvan
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def rsTerm {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x : ℝ) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℂ :=
  ((sat σ w).map fun α => (α : ℂ) ^ (r + 1)).sum * ((sat σ' w).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (r + 1)).sum *
    (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1)

def logRS (T : Finset (HeightOneSpectrum (𝓞 E))) {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x : ℝ) : ℂ :=
  ∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, rsTerm σ σ' x p.1.1 p.2

end GlobalTheory.JSW
end
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_indep_of_first_terms : ∀ (l : ℕ) [Fact l.Prime] (h d : ℕ) (r : ℝ) (y : Fin d → ℕ → Fl l), 2 ≤ h → 0 ≤ r → r < 1 → (∀ a k, ‖sh (y a k)‖ ≤ r) → (∀ n : Fin d → ℕ, ‖sh (∑ a, n a • y a 0)‖ ≤ r ^ l ^ h → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  intro l _ h d r y hh hr0 hr1 hy hdet c hc
  have h1 : 1 ≤ h := by omega
  refine GlobalTheory.T.indep_over_padic_of_indep_mod_prime l d (Fin 2) (fun a i => abelian₂ h i (y a)) (fun i => gam l h i r) ?_ ?_ c ?_
  · intro a i
    exact (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h i r (y a) h1 hr1 (hy a)).2.2.1
  · intro n hn
    apply hdet n
    have hls := fun j => GlobalTheory.T.untiltFrobeniusLaurentSeries_natCombination_approx l h j d r (fun a => y a 0) n h1 hr0 hr1 (fun a => hy a 0)
    have hρ0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hρ1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (pow_pos (Fact.out : l.Prime).pos h).ne'
    refine GlobalTheory.T.norm_tiltUntilt_le_of_frobeniusSeries_size_le l h (r ^ l ^ h) (∑ a, n a • y a 0) hh hρ0 hρ1 (lt_of_le_of_lt (hls 0).1 hr1) ?_
    intro j hj
    have hG := GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r h1 hr0 hr1
    rw [hG.2.2.2.2.1]
    have hnn : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r := mul_nonneg (norm_nonneg _) hG.2.2.1
    have hA := (hls j).2
    have hB : ‖∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a))‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hnn fun a _ => ?_
      rw [norm_mul]
      have hb := (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h j r (y a) h1 hr1 (hy a)).2.1
      rw [norm_sub_rev] at hb
      calc ‖(n a : ℂ_[l])‖ * ‖lam h j (y a 0) - abelian₂ h j (y a)‖ ≤ 1 * (‖(l : ℂ_[l])‖ * gam l h j r) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) hb (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hC : ‖∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := hn ⟨j, hj⟩
    have heq : lam h j (∑ a, n a • y a 0) = (lam h j (∑ a, n a • y a 0) - ∑ a, (n a : ℂ_[l]) * lam h j (y a 0)) + (∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a)) + ∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hB hC)
  · intro i
    exact hc i.1 i.2

end GlobalTheory.PSer
end

section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.DualJump

open GlobalTheory.DRFil GlobalTheory.DRDual

theorem multV_twisted_dual {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
    [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V')
    (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ) (hm : Function.Bijective m)
    (hg : ∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y)
    (h : IsDR (P.PD K) ρ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  have := K.2
  have := LL.2
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨-, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  obtain ⟨n, d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

theorem dualJumpL : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → DualJumpL L := by
  intro L AI hT l _ K LL A A' m hm h τ a
  obtain ⟨T⟩ := hT l
  obtain ⟨hg, h1, -, hd⟩ := hm
  have hi : Function.Injective m :=
    (injective_iff_map_eq_zero m).2 fun x hx => h1 x fun y => by rw [hx, LinearMap.zero_apply]
  have hb : Function.Bijective m :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans (Subspace.dual_finrank_eq (K := ↥LL.1) (V := A'.V)).symm)).1 hi⟩
  have key := multV_twisted_dual T K LL A.ρ A'.ρ m 1 hb (fun g x y => by rw [zpow_one]; exact hg g x y) h τ (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at key
  rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A'.V A'.ρ τ a).2.2,
    (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A.V A.ρ τ (-a - 1)).2.2, key]

end GlobalTheory.DualJump
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.LowerWt

theorem coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    (a * eSerC L N f).coeff 1 = ∑ χ ∈ hfin.toFinset, χ 1 / (Fintype.card (Gn g N) : ℂ) * tr a χ := by
  unfold eSerC
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  exact ((GlobalTheory.GLq.trIdem (Gn g N) a χ).2.2)

theorem re_coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    ((a * eSerC L N f).coeff 1).re =
      ∑ χ ∈ hfin.toFinset, (χ 1).re / (Fintype.card (Gn g N) : ℝ) * (tr a χ).re := by
  rw [coeff_mul_eSerC L f a hfin, Complex.re_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) a χ).2.1 hI
  rw [hd]
  have : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) = (((d : ℝ) / (Fintype.card (Gn g N) : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  simp

theorem weight_nonneg {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) (χ : Gn g N → ℂ) (hχ : χ ∈ hfin.toFinset) :
    0 ≤ (χ 1).re / (Fintype.card (Gn g N) : ℝ) := by
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) (1 : MonoidAlgebra ℂ (Gn g N)) χ).2.1 hI
  rw [hd]
  simp only [Complex.natCast_re]
  positivity

end GlobalTheory.GLq.LowerWt

theorem GlobalTheory.GLq.lowerWtComparison : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k →
      ∀ f, (1 - 1 / (g : ℝ)) * wtC L (eU g N ψ) f ≤ wtC L (eJ g N k s ψ) f := by
  intro g _ L ψ hψ N k s hN hk f
  have hL8 := GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn g ψ hψ N k s hN hk
  obtain ⟨-, hU1, hJ, -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ hN
  have hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (irr_finite_and_finsum_zOf_eq_one (Gn g N)).1.subset fun χ h => h.1
  set T := hfin.toFinset
  set c : (Gn g N → ℂ) → ℝ := fun χ => (χ 1).re / (Fintype.card (Gn g N) : ℝ) with hc
  set A := ∑ χ ∈ T, c χ * (tr (eU g N ψ) χ).re with hA
  set B := ∑ χ ∈ T, c χ * (tr (eJ g N k s ψ) χ).re with hB
  have hAeq : ((eU g N ψ * eSerC L N f).coeff 1).re = A := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hBeq : ((eJ g N k s ψ * eSerC L N f).coeff 1).re = B := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hG : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  set M := N * (N - 1) / 2
  have hU1r : ((eU g N ψ).coeff 1).re = ((g : ℝ) ^ M)⁻¹ := by
    rw [hU1]
    have : ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ M)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hJ1r : ((eJ g N k s ψ).coeff 1).re = (g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹ := by
    rw [hJ1]
    have : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hBA : ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * A ≤ B := by
    rw [hA, hB, Finset.mul_sum]
    refine Finset.sum_le_sum fun χ hχ => ?_
    have h0 : 0 ≤ c χ := LowerWt.weight_nonneg L f hfin χ hχ
    have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
    have hC : IsChar χ := by obtain ⟨V, -, hV⟩ := hI; exact ⟨V, hV⟩
    have h8 := hL8 χ hC
    unfold wh at h8
    calc ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (c χ * (tr (eU g N ψ) χ).re)
        = c χ * (((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (tr (eU g N ψ) χ).re) := by ring
      _ ≤ c χ * (tr (eJ g N k s ψ) χ).re := mul_le_mul_of_nonneg_left h8 h0
  have hpow : (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  unfold wtC
  rw [hAeq, hBeq, hU1r, hJ1r]
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := pow_pos hG k
  have hgM : (0 : ℝ) < (g : ℝ) ^ M := pow_pos hG M
  rw [hpow] at hBA
  rw [div_inv_eq_mul, le_div_iff₀ (mul_pos hgk (inv_pos.2 hgM))]
  calc (1 - 1 / (g : ℝ)) * (A * (g : ℝ) ^ M) * ((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹)
      = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A * ((g : ℝ) ^ M * ((g : ℝ) ^ M)⁻¹) := by ring
    _ = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A := by rw [mul_inv_cancel₀ hgM.ne', mul_one]
    _ ≤ B := hBA
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLq.DetSplit

open GlobalTheory.GLq Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_hc_mono_left (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α A : Gn g m → ℂ) (hα : IsIrr α) (hA : IsChar A) (hαA : ip α A ≠ 0)
    (β : Gn g k → ℂ) (hβ : IsChar β) (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k A β n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hα hA hαA
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hα) hβ) (hc R β hR hβ) h

theorem ip_hc_mono_right (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α : Gn g m → ℂ) (hα : IsChar α) (β B : Gn g k → ℂ) (hβ : IsIrr β) (hB : IsChar B) (hβB : ip β B ≠ 0)
    (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k α B n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hβ hB hβB
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β hα (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ)) (hc α R hα hR) h

theorem hcL_append_of (K₁ K₂ : List (Pc g)) (h₁ : ∀ q ∈ K₁, IsCusp q.2) (h₂ : ∀ q ∈ K₂, IsCusp q.2)
    (m₁ m₂ n : ℕ) (e₁ : degL K₁ = m₁) (e₂ : degL K₂ = m₂) (hn : n = m₁ + m₂) :
    hcL (K₁ ++ K₂) n = hc m₁ m₂ (hcL K₁ m₁) (hcL K₂ m₂) n := by
  subst e₁ e₂
  exact GlobalTheory.GLq.LabelMul.hcL_append K₁ K₂ (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₁ q hq))
    (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₂ q hq)) n hn

theorem root_of_constituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  intro p _ L r a c θ u f ψ α β σ hr hψ hα hβ hσ hL hlab hψαβ hασ
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨Kσ, hKσ, hKσd, hKσi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p a σ hσ
  obtain ⟨Kβ, hKβ, hKβd, hKβi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p c β hβ
  have hθI : IsIrr (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hθC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hθI
  have hθcusp : IsCusp (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hθI, fun a h1 h2 => by omega⟩
  have hQc : ∀ q ∈ Q.map Prod.snd, IsCusp q.2 := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact (hQ q' hq').2.1
  have hA := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hQc _ hQd
  have fin : ∀ K' : List (Pc p), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc p) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot u := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := GlobalTheory.GLq.DetRoot.eq_of_isCuspOf_det L θ u hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  generalize (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) = θd at hθI hθC hθcusp hασ fin
  have h1 := GlobalTheory.GLq.DetRoot.ip_hc_left a α hα σ hσ θd hθC Kσ hKσ hKσd hKσi hασ
  have hT : ∀ q ∈ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hθcusp
  have hTd : degL [(⟨1, θd⟩ : Pc p)] = 1 := by simp [degL]
  have eα : hcL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) (a + 1) = hc a 1 (hcL Kσ a) θd (a + 1) := by
    rw [hcL_append_of Kσ _ hKσ hT a 1 (a + 1) hKσd hTd rfl,
      GlobalTheory.GLq.IpCuspProd.hcL_single 1 θd (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hθC)]
  rw [← eα] at h1
  have hKα : ∀ q ∈ Kσ ++ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKσ q hq
    · exact hT q hq
  have hKαd : degL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) = a + 1 := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKσd, hTd]
  have hAα := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKα _ hKαd
  have h2 := ip_hc_mono_left (a + 1) c r hr ψ hψ α _ hα hAα h1 β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ) hψαβ
  have h3 := ip_hc_mono_right (a + 1) c r hr ψ hψ _ hAα β (hcL Kβ c) hβ
    (GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKβ _ hKβd) hKβi h2
  rw [← hcL_append_of _ Kβ hKα hKβ (a + 1) c r hKαd hKβd hr] at h3
  have hKall : ∀ q ∈ (Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ, IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKα q hq
    · exact hKβ q hq
  have hKd : degL ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) = r := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKαd, hKβd, hr]
  have hB := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKall _ hKd
  have hAB := GlobalTheory.GLq.DetRoot.ip_ne_zero_of_common hψ hA hB hQi h3
  refine fin ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) ?_ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))))
  by_contra hn
  exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp p _ _ _ hQd hKd hQc hKall).1 hn)

end GlobalTheory.GLq.DetSplit
end
end
