module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecompositionOfThreeParts
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.Bundle007
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle003
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem support_diagK_subset {σ Kf : Type} [Field Kf] (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) :
    (diagK g F).support ⊆ F.support := by
  intro mo hmo
  rw [mem_support_iff] at hmo ⊢
  rw [coeff_diagK] at hmo
  exact right_ne_zero_of_mul hmo

section Id

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem value_exact (d : Fin n' → ℕ) (hDig : DigFacts Fr p O hk nL d) (G : MvPolynomial (TV n' (m + 1)) (KK O))
    (hG : HasMultideg G d) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (hgn : ∀ bn, ((gamNo Fr p nL rho bn : ℚ) : KK O) ≠ 0)
    (e : Module.End (KK O) (MvPolynomial (TL J nL r × Fin K) (KK O)))
    (hsa : ∀ F G, fock (e F) G = fock F (e G)) (nu : TL J nL r × Fin K →₀ ℕ) (cY : KK O)
    (hpol : e (monomial nu 1) ∈ Pol (KK O) K dNo)
    (A : MvPolynomial (TL J nL r × Fin r) (KK O)) (hA : A ∈ Pol (KK O) r dPl) :
    fock G (asm Fr p O hk nL rho A
        (diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)))) =
      ((cstOf Fr p nL rho dPl dNo : ℕ) : KK O) * cY * ((expFact nu : ℕ) : KK O) *
        fock (planeCoeff nu (oneT e (levImg Fr p hk nL rho dPl dNo G)))
          (diagK (fun bp => ((gamPl Fr p nL rho bp : ℚ) : KK O)) A) := by
  have hNpol0 : diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)) ∈ Pol (KK O) K dNo :=
    diagK_mem_pol _ _ (Submodule.smul_mem _ _ hpol)
  obtain ⟨Nex, hNex⟩ : ∃ Nex, Nex = diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)) :=
    ⟨_, rfl⟩
  rw [← hNex]
  have hNpol : Nex ∈ Pol (KK O) K dNo := by rw [hNex]; exact hNpol0
  rw [(hDig G hG).1 rho dPl dNo hrho A hA Nex hNpol]
  have hback : diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)) Nex = cY • e (monomial nu 1) := by
    ext bn
    rw [coeff_diagK, hNex, coeff_diagK, ← mul_assoc, mul_inv_cancel₀ (hgn bn), one_mul]
  have hin : ∀ bp : TL J nL r × Fin r →₀ ℕ,
      ∑ bn ∈ Nex.support, ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn *
            (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
            (((gamNo Fr p nL rho bn : ℚ) : KK O) * Nex.coeff bn * ((expFact bn : ℕ) : KK O)) =
        (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
          (cY * ((e ((levImg Fr p hk nL rho dPl dNo G).coeff bp)).coeff nu * ((expFact nu : ℕ) : KK O))) := by
    intro bp
    have h1 : fock ((levImg Fr p hk nL rho dPl dNo G).coeff bp)
        (diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)) Nex) =
        cY * ((e ((levImg Fr p hk nL rho dPl dNo G).coeff bp)).coeff nu * ((expFact nu : ℕ) : KK O)) := by
      rw [hback, fock_smul_right, ← hsa, fock_monomial_right]
    rw [← h1, fock_eq_sum _ _ Nex.support (support_diagK_subset _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun bn _ => ?_
    rw [coeff_diagK]; ring
  rw [Finset.sum_congr rfl fun bp _ => hin bp]
  rw [fock_eq_sum _ _ A.support (support_diagK_subset _ _), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun bp _ => ?_
  rw [coeff_planeCoeff, coeff_oneT, coeff_diagK]; ring

theorem asm_add_right (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N N' : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    asm Fr p O hk nL rho A (N + N') = asm Fr p O hk nL rho A N + asm Fr p O hk nL rho A N' := by
  unfold asm
  rw [map_add (f := _)]; ring

end Id

theorem asm_coefGe' {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
    (rho : TL J nL r × Fin (r + K) → ℕ) {A : MvPolynomial (TL J nL r × Fin r) (KK O)}
    {N : MvPolynomial (TL J nL r × Fin K) (KK O)} {t : ℝ} (hA : CoefGe p A 0) (hN : CoefGe p N t) :
    CoefGe p (asm Fr p O hk nL rho A N) t := by
  unfold asm
  have h1 : CoefGe p (monomial (labMon Fr hk nL rho) (1 : KK O)) 0 := CoefGe.monomial _ geQ_one
  have h2 : CoefGe p (upPl Fr p O hk nL A) 0 := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hA
  have h3 : CoefGe p (upNo Fr p O hk nL N) t := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hN
  have h4 := CoefGe.mul (CoefGe.mul h1 h2) h3
  simpa using h4

theorem padicVal_expFact_le (p : ℕ) [hp : Fact p.Prime] {n' k : ℕ} (d : Fin n' → ℕ) (α : Fin n' × Fin k →₀ ℕ)
    (hα : ∀ s, multideg α s = d s) : padicValNat p (expFact α) ≤ padicValNat p (∏ s, (d s).factorial) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : Fin n', ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) * expFact α := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact α ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  rw [h3, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hMn0 hE0]
  omega

end Formalism.MainNotions.Proposition5Numerics
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem lowest_weight_le_of_isotypic (D : Formalism.BasicNotions.D7) {R : Type} [Field R] [CharZero R] {ι : Type} [Fintype ι] (LL : Letters ι)
    {n : ℕ} [NeZero n] (S : Set ι) (lam : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R)
    (hF : F ∈ isoSub (glOps R n LL S) lam) : lam1S LL S F ≤ ((lam 0 : ℤ) : WithBot ℤ) := by
  obtain ⟨ee, hee, _⟩ := Formalism.MainNotions.G.Joints.polIsoDecompB_of D (weight_condition_from_integral_form D) R ι LL n S
  refine (((valuation_field D).2 R ι LL n S ee hee).2 F (lam 0)).2 fun mu hmu => ?_
  by_cases h : lam = mu
  · rw [h]
  · exact absurd ((hee mu).2 lam h F hF) hmu

section DD

variable {σ Kf : Type} [Field Kf]

theorem coeff_mon_divDer (m a : σ →₀ ℕ) (F : MvPolynomial σ Kf) :
    (monomial m (1 : Kf) * divDer m F).coeff a = (∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : Kf)) * F.coeff a := by
  rw [coeff_monomial_mul']
  split_ifs with hma
  · rw [one_mul]
    unfold divDer
    rw [coeff_sum]
    have hsingle : ∀ b ∈ F.support, b ≠ a →
        AddMonoidAlgebra.coeff (if m ≤ b then monomial (b - m) (F.coeff b * ((m.prod fun k j => (b k).choose j : ℕ) : Kf))
          else 0) (a - m) = 0 := by
      intro b _ hb
      split_ifs with hmb
      · rw [coeff_monomial, if_neg]
        intro h
        apply hb
        have h1 : b - m + m = a - m + m := by rw [h]
        rwa [tsub_add_cancel_of_le hmb, tsub_add_cancel_of_le hma] at h1
      · simp
    by_cases ha : a ∈ F.support
    · rw [Finset.sum_eq_single a hsingle (fun h => absurd ha h), if_pos hma, coeff_monomial, if_pos rfl]
      unfold Finsupp.prod
      push_cast
      ring
    · rw [Finset.sum_eq_zero (fun b hb => hsingle b hb (fun h => ha (h ▸ hb))), notMem_support_iff.1 ha, mul_zero]
  · have : ∃ v, a v < m v := by
      by_contra hcon
      push Not at hcon
      exact hma hcon
    obtain ⟨v, hv⟩ := this
    have hvs : v ∈ m.support := by
      rw [Finsupp.mem_support_iff]
      omega
    rw [Finset.prod_eq_zero hvs (by rw [Nat.choose_eq_zero_of_lt hv, Nat.cast_zero]), zero_mul]

end DD

section BC

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem diagK_binomCombF (lam : (σ →₀ ℕ) →₀ O) (F : MvPolynomial σ (KK O)) :
    diagK (fun a => binomCombF (K := KK O) lam a) F =
      ∑ m ∈ lam.support, (algebraMap O (KK O) (lam m)) • (monomial m (1 : KK O) * divDer m F) := by
  ext a
  rw [coeff_diagK, coeff_sum]
  unfold binomCombF
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, coeff_mon_divDer, smul_eq_mul]
  ring

theorem geQ_binomCombF (S : UniformizedDVR p O) (lam : (σ →₀ ℕ) →₀ O) (a : σ →₀ ℕ) :
    geQ (vK p (binomCombF (K := KK O) lam a)) 0 := by
  unfold binomCombF
  refine geQ_sum _ _ fun m _ => ?_
  have h : algebraMap O (KK O) (lam m) * ∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : KK O) =
      algebraMap O (KK O) (lam m * ∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : O)) := by
    rw [map_mul, map_prod]
    simp
  rw [h]
  exact geQ_alg S _

end BC

theorem padicVal_expFact_le' (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] {k : ℕ} (d : ι → ℕ)
    (α : ι × Fin k →₀ ℕ) (hα : ∀ s, multideg α s = d s) :
    padicValNat p (expFact α) ≤ padicValNat p (∏ s, (d s).factorial) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : ι, ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) * expFact α := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact α ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  rw [h3, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hMn0 hE0]
  omega

section St

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem coefGe_of_inBB [hp : Fact p.Prime] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O)) {ι : Type} [Fintype ι]
    {k : ℕ} (d : ι → ℕ) (Z : MvPolynomial (ι × Fin k) (KK O)) (hZ : Z ∈ Pol (KK O) k d) (hBB : InBB (O := O) p Z) :
    CoefGe p (((algebraMap O (KK O) w) ^ (padicValNat p (∏ s, (d s).factorial))) • Z) 0 := by
  intro bn
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hbn : bn ∈ Z.support
  · have hdeg : ∀ s, multideg bn s = d s := ((mem_restrictSupport_iff (KK O)).1 hZ) hbn
    have h1 := padicVal_expFact_le' p d bn hdeg
    have h2 : (0 : WithTop ℚ) ≤ vK p (Z.coeff bn) + (((padicValNat p (expFact bn) : ℚ) / 2 : ℚ) : WithTop ℚ) :=
      le_trans hBB (vBB_le_coeff Z bn)
    intro q hq
    rw [valuation_mul_alt, vK_w_pow hp.out S w hw2] at hq
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 hq
    rw [← hb, ← WithTop.coe_add] at h2
    have h3 : (0 : ℚ) ≤ b + (padicValNat p (expFact bn) : ℚ) / 2 := by exact_mod_cast h2
    have h4 : a = ((padicValNat p (∏ s, (d s).factorial) : ℕ) : ℚ) / 2 := by exact_mod_cast ha
    have h5 : ((padicValNat p (expFact bn) : ℕ) : ℚ) ≤ ((padicValNat p (∏ s, (d s).factorial) : ℕ) : ℚ) := by
      exact_mod_cast h1
    have h6 : (0 : ℚ) ≤ q := by rw [← hab, h4]; linarith
    exact_mod_cast h6
  · rw [notMem_support_iff.1 hbn, mul_zero]
    exact geQ_zero 0

end St

end Formalism.MainNotions.Proposition5Numerics
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Geo

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {L₁ N₁ : ℕ}

theorem lf_fr_per (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    Fr.fr (j + m * Fr.J) i = Fr.fr j i + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show j + ((k : ℤ) + 1) * (Fr.J : ℤ) = (j + (k : ℤ) * Fr.J) + Fr.J by ring, hV.2.1, ih]
    ring
  | pred k ih =>
    have h := hV.2.1 (j + (-(k : ℤ) - 1) * Fr.J) i
    rw [show j + (-(k : ℤ) - 1) * (Fr.J : ℤ) + Fr.J = j + -(k : ℤ) * Fr.J by ring, ih] at h
    linarith

private theorem fr_mono_of_valid (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i' : ℕ, i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i i' hii' hi'
  induction i' with
  | zero => rw [Nat.le_zero.mp hii']
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (hV.2.2.1 j k (by omega)).le
    · rw [le_antisymm hii' h]

private theorem fr_last_mono_in_index_of_valid (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (a : ℤ) :
    ∀ b : ℤ, a ≤ b → Fr.fr a (r - 1) ≤ Fr.fr b (r - 1) := by
  intro b hab
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := le_trans (hV.2.2.2.1 (a + n)).le
      (fr_mono_of_valid Fr hV (a + n + 1) 0 (r - 1) (Nat.zero_le _) (by omega))
    exact le_trans ih (by simpa [add_assoc] using hstep)

theorem lf_dist_eq (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j j' x y : ℤ) (hx1 : Fr.fr (j - 1) (r - 1) < x)
    (hx2 : x ≤ Fr.fr j (r - 1)) (hy1 : Fr.fr (j' - 1) (r - 1) < y) (hy2 : y ≤ Fr.fr j' (r - 1))
    (h : posOf n' y = posOf n' x) : Fr.dist j x = Fr.dist j' y := by
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hv : ((y % (n' : ℤ)).toNat % n') = ((x % (n' : ℤ)).toNat % n') := congrArg Fin.val h
  have ex1 : 0 ≤ x % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ex2 : x % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have ey1 : 0 ≤ y % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ey2 : y % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have hmod : y % (n' : ℤ) = x % (n' : ℤ) := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega
  obtain ⟨k, hk⟩ : (n' : ℤ) ∣ y - x := Int.dvd_of_emod_eq_zero (Int.emod_emod_of_dvd _ (dvd_refl _) ▸ (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod))
  have hJ1 := lf_fr_per Fr hV j (r - 1) k
  have hJ2 := lf_fr_per Fr hV (j - 1) (r - 1) k
  have hjj : j' = j + k * Fr.J := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := fr_last_mono_in_index_of_valid Fr hV hr j' (j - 1 + k * Fr.J) (by linarith)
      rw [hJ2] at this
      nlinarith
    · have := fr_last_mono_in_index_of_valid Fr hV hr (j + k * Fr.J) (j' - 1) (by linarith)
      rw [hJ1] at this
      nlinarith
  unfold Frames.dist
  rw [hjj, hJ1]
  congr 1
  linarith

end Geo

section Lab

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (K : ℕ) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem labO_apply (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (y : TL J nL r) (c : Fin (r + K)) :
    labO Fr K nL rho (posOf n' (posTL Fr y), c) = rho (y, c) := by
  classical
  simp only [labO, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      rw [if_neg]
      intro h
      exact hc' (Prod.ext_iff.mp h).2
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro c' _
    rw [if_neg]
    intro h
    exact hx (hinj (Prod.ext_iff.mp h).1)
  · intro h; exact absurd (Finset.mem_univ y) h

theorem labO_support (rho : TL J nL r × Fin (r + K) → ℕ) (v : Fin n' × Fin (r + K))
    (hv : v ∈ (labO Fr K nL rho).support) : ∃ x : TL J nL r, v.1 = posOf n' (posTL Fr x) := by
  classical
  by_contra hne
  push_neg at hne
  apply Finsupp.mem_support_iff.mp hv
  simp only [labO, Finsupp.finsetSum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro c _
  rw [if_neg]
  intro h
  exact hne x (Prod.ext_iff.mp h).1.symm

end Lab

theorem restLabG : RestLabG := by
  intro p _ n' r K _ _ _ O _ _ _ _S Fr TT L₁ L₂ N₁ G' deg d Y cP hMFH J _ Dt dPl dNo ka rho No Go hMH
  obtain ⟨hJ, hnL, -⟩ := hMH.1.1
  have hV : Fr.Valid L₁ N₁ := hMFH.frames.2.1
  have hr : 1 ≤ r := by have := hMFH.two_le_r; omega
  have hinj := posTL_inj Fr hV hr hJ hnL
  have hB := hMH.2.1
  unfold LabAt
  refine ⟨?_, ?_⟩
  · intro j x hx hW c
    by_cases hy : ∃ y : TL J Dt.nL r, posOf n' (posTL Fr y) = posOf n' x
    · obtain ⟨y, hy⟩ := hy
      rw [← hy, labO_apply Fr K Dt.nL hinj rho y c]
      have hlt := hB.1 y c
      have hseg := posTL_seg Fr hV hr hnL y
      have hxl := (Finset.mem_filter.mp hx).1
      rw [Finset.mem_Icc] at hxl
      have hd := lf_dist_eq Fr hV hr j (segZ y.1) x (posTL Fr y) (not_le.mp hW) hxl.2 hseg.1 hseg.2.1 hy
      rw [hd]
      exact hlt
    · push_neg at hy
      have h0 : labO Fr K Dt.nL rho (posOf n' x, c) = 0 := by
        by_contra hne
        obtain ⟨y, hy'⟩ := labO_support Fr K Dt.nL rho (posOf n' x, c) (Finsupp.mem_support_iff.mpr hne)
        exact hy y hy'.symm
      rw [h0]
      exact pow_pos (Fact.out : p.Prime).pos _
  · intro v hv
    obtain ⟨y, hy⟩ := labO_support Fr K Dt.nL rho v hv
    rw [hy]
    exact (posTL_seg Fr hV hr hnL y).2.2

end Formalism.MainNotions.Proposition5Numerics
end
end
