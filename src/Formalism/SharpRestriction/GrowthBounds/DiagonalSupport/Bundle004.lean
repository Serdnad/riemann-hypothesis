module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ExistsMapOfCoefGe
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecompositionOfThreeParts
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

section Co

variable {σ τ : Type} {Kf : Type} [Field Kf]

theorem coeff_planeCoeff (nu : τ →₀ ℕ) (F : MvPolynomial σ (MvPolynomial τ Kf)) (bp : σ →₀ ℕ) :
    (planeCoeff nu F).coeff bp = (F.coeff bp).coeff nu := by
  unfold planeCoeff
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [notMem_support_iff.1 h]

theorem coeff_oneT (e : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf)) (bp : σ →₀ ℕ) :
    (oneT e F).coeff bp = e (F.coeff bp) := by
  unfold oneT
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem coeff_diagK (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) (mo : σ →₀ ℕ) :
    (diagK g F).coeff mo = g mo * F.coeff mo := by
  unfold diagK
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, mul_zero]

theorem diagK_mem_pol {ι : Type} {n : ℕ} (d : ι → ℕ) (g : (ι × Fin n →₀ ℕ) → Kf) {F : MvPolynomial (ι × Fin n) Kf}
    (hF : F ∈ Pol Kf n d) : diagK g F ∈ Pol Kf n d := by
  rw [Pol, mem_restrictSupport_iff] at hF ⊢
  intro mo hmo
  apply hF
  rw [Finset.mem_coe, mem_support_iff] at hmo ⊢
  rw [coeff_diagK] at hmo
  exact right_ne_zero_of_mul hmo

theorem fock_eq_sum (F G : MvPolynomial σ Kf) (s : Finset (σ →₀ ℕ)) (hs : G.support ⊆ s) :
    fock F G = ∑ m ∈ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
  unfold fock
  have h1 : ∑ m ∈ F.support, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) =
      ∑ m ∈ F.support ∪ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
    refine Finset.sum_subset Finset.subset_union_left fun m _ hm => ?_
    rw [notMem_support_iff.1 hm, zero_mul, zero_mul]
  have h2 : ∑ m ∈ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) =
      ∑ m ∈ F.support ∪ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
    refine Finset.sum_subset Finset.subset_union_right fun m _ hm => ?_
    have : m ∉ G.support := fun h => hm (hs h)
    rw [notMem_support_iff.1 this, mul_zero, zero_mul]
  rw [h1, h2]

theorem fock_monomial_right (F : MvPolynomial σ Kf) (nu : σ →₀ ℕ) :
    fock F (monomial nu 1) = F.coeff nu * ((expFact nu : ℕ) : Kf) := by
  rw [fock_eq_sum F _ {nu} (by
    intro m hm
    rw [mem_support_iff, coeff_monomial] at hm
    by_contra h
    rw [Finset.mem_singleton] at h
    exact hm (if_neg fun h' => h h'.symm))]
  rw [Finset.sum_singleton, coeff_monomial, if_pos rfl, mul_one]

theorem fock_smul_left (c : Kf) (F G : MvPolynomial σ Kf) : fock (c • F) G = c * fock F G := by
  rw [fock_eq_sum _ _ _ (Finset.Subset.refl _), fock_eq_sum F _ _ (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

theorem fock_smul_right (c : Kf) (F G : MvPolynomial σ Kf) : fock F (c • G) = c * fock F G := by
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

end Co

section VB

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem vBB_le_coeff (F : MvPolynomial σ (KK O)) (m : σ →₀ ℕ) :
    vBB (O := O) p F ≤ vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  by_cases h : m ∈ F.support
  · exact Finset.inf_le h
  · rw [notMem_support_iff.1 h, valuation_zero_alt, WithTop.top_add]
    exact le_top

theorem vBB_attained (F : MvPolynomial σ (KK O)) (hF : vBB (O := O) p F ≠ ⊤) :
    ∃ m ∈ F.support, vBB (O := O) p F = vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  have hne : F.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hF
    unfold vBB
    rw [h, Finset.inf_empty]
  exact Finset.exists_mem_eq_inf _ hne _

theorem vBB_smul (c : KK O) (hc : c ≠ 0) (F : MvPolynomial σ (KK O)) :
    vBB (O := O) p (c • F) = vK p c + vBB (O := O) p F := by
  unfold vBB
  have hs : (c • F).support = F.support := by
    ext m
    simp [MvPolynomial.mem_support_iff, hc]
  rw [hs]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, valuation_mul_alt, add_assoc]
  by_cases hne : F.support.Nonempty
  · exact (Finset.apply_inf_eq_inf_comp_of_linearOrder (fun y : WithTop ℚ => vK p c + y)
      (fun a b hab => add_le_add_right hab _) (by simp)).symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

theorem vK_inv (x : KK O) (q : ℚ) (hx : vK p x = (q : WithTop ℚ)) : vK p x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [valuation_zero_alt] at hx
    exact WithTop.top_ne_coe hx
  have h := valuation_mul_alt p x x⁻¹
  rw [mul_inv_cancel₀ hx0, valuation_one_eq_zero_alt, hx] at h
  obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 (h.symm.trans (by rfl : (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ)))
  have h1 : a = q := by exact_mod_cast ha
  rw [← hb]
  congr 1
  linarith

theorem vK_w_pow (hp : p.Prime) (S : UniformizedDVR p O) (w : O) (hw : w ^ 2 = (p : O)) (n : ℕ) :
    vK p ((algebraMap O (KK O) w) ^ n) = (((n : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  have h1 : vK p (algebraMap O (KK O) w) = (((1 : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    have h2 : (algebraMap O (KK O) w) * (algebraMap O (KK O) w) = ((p : ℕ) : KK O) := by
      rw [← map_mul, ← pow_two, hw, map_natCast]
    have h3 := congrArg (vK p) h2
    rw [valuation_mul_alt, valuation_natCast_padicVal hp S p hp.ne_zero, Nat.padicValNat_def, Nat.multiplicity_self hp.one_lt] at h3
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 h3
    have hab' : a = b := by
      have : (a : WithTop ℚ) = (b : WithTop ℚ) := by rw [ha, hb]
      exact_mod_cast this
    rw [← ha]
    congr 1
    push_cast at hab
    linarith
  induction n with
  | zero => rw [pow_zero, valuation_one_eq_zero_alt]; simp
  | succ n ih =>
    rw [pow_succ, valuation_mul_alt, ih, h1, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

end VB

end Formalism.MainNotions.Proposition5Numerics
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def SLt {J : ℕ} (j : ZMod J) (x : ℤ) : Set (ZMod J × ℤ) := {i | i.1 = j ∧ i.2 < x}

def SLe {J : ℕ} (j : ZMod J) (x : ℤ) : Set (ZMod J × ℤ) := {i | i.1 = j ∧ i.2 ≤ x}

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

def pU (j : ZMod J) (u : ℕ) : ℤ := posU Fr (Dt.nL j) (segZ j) u

def tauU (j : ZMod J) (u : ℕ) : ℝ :=
  thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u -
    slU Fr p deg Y (r + K) Dt.nL j u / 2 - 60 * (cP : ℝ)

def ValBd : Prop :=
  (∀ j u, u < Dt.nL j + r →
    geZ (valS (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go)) (tauU p O Fr deg Y N₁ G' cP Dt ka j u)) ∧
  (∀ j u, u < Dt.nL j →
    geZ (valS (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go)) (tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1))) ∧
  ∀ j u, u < Dt.nL j + r →
    lam1S (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiNo Fr O K Dt.nL No) ≤ ((ka j u 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ) ∧
    lam1S (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiNo Fr O K Dt.nL No) ≤ ((ka j (u + 1) 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ)

def dNoOf (i : ZMod J × ℤ) : ℕ := ∑ x : TL J Dt.nL r, if tlPos Fr Dt.nL x = i then dNo x else 0

def SuppOK : Prop :=
  (∀ mo ∈ (xiPl Fr O Dt.nL Go).support, ∀ v ∈ mo.support, v.1.2 ∈ Fr.letters (segZ v.1.1)) ∧
  ∀ mo ∈ (xiNo Fr O K Dt.nL No).support,
    (∀ v ∈ mo.support, v.1.2 ∈ Fr.letters (segZ v.1.1) ∧ ¬ Fr.IsW (segZ v.1.1) v.1.2) ∧
    ∀ i, multideg mo i = dNoOf p O Fr Dt dNo i

def PlOK (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) : Prop :=
  A ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} ∧
  (∀ mo ∈ A.support, ∀ x, multideg mo x = δ (j, x)) ∧
  (∀ u, u < Dt.nL j + r →
    ((⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < pU p O Fr Dt j u} A) ∧
  ∀ u, u < Dt.nL j →
    ((⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ pU p O Fr Dt j u} A

def NoOK (j : ZMod J) (B : MvPolynomial (ℤ × Fin K) O) : Prop :=
  B ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) v.1} ∧
  (∀ mo ∈ B.support, ∀ x, multideg mo x = dNoOf p O Fr Dt dNo (j, x)) ∧
  ∀ u, u < Dt.nL j + r →
    lam1S LZ {y | y < pU p O Fr Dt j u} B ≤ ((ka j u 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ) ∧
    lam1S LZ {y | y ≤ pU p O Fr Dt j u} B ≤ ((ka j (u + 1) 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ)

def XXAt : Prop :=
  ∀ (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (B : MvPolynomial (ℤ × Fin K) O),
    PlOK p O Fr deg Y N₁ G' cP Dt ka δ j A → NoOK p O Fr cP Dt dNo ka j B →
    plEmb O r K A * nmEmb O r K B ∈ XX' O r K Fr (segZ j) (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ))
      (fun x => Bo p Fr deg (segZ j) x / 2 - sl p Fr deg Y (r + K) (segZ j) x)
      (fun x => ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ)) ∧
    plEmb O r K A * nmEmb O r K B ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters (segZ j),
      ∑ c : Fin (r + K), mm (x, c) = δ (j, x) + dNoOf p O Fr Dt dNo (j, x)}

def DdAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ → ∀ (j : ZMod J), ∀ x ∈ Fr.letters (segZ j),
    (Fr.IsW (segZ j) x ∨ x ∈ Fr.LLset (segZ j)) →
    ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ) ≤
      levDeg p Fr deg (segZ j) x + levDeg p Fr deg (segZ j) x / 100

end At

def RestValBdG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go →
      ValBd p O Fr deg Y N₁ G' cP Dt ka No Go ∧ SuppOK p O Fr Dt dNo No Go

def RestXXG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
      SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka → XXAt p O Fr deg Y N₁ G' cP Dt dNo ka

def RestDdG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DdAt p O Fr deg Dt dNo Go

end Formalism.MainNotions.Proposition5Numerics
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Comp

variable {R : Type} [CommRing R] {ι κ : Type} {n : ℕ}

theorem coeff_homComp (δ : ι → ℕ) (F : MvPolynomial (ι × Fin n) R) (a : ι × Fin n →₀ ℕ) :
    (homComp δ F).coeff a = if (∀ i, multideg a i = δ i) then F.coeff a else 0 := by
  classical
  unfold homComp
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  by_cases h : ∀ i, multideg a i = δ i <;> by_cases hc : F.coeff a = 0 <;> simp [h, hc]

theorem homComp_rename (f : κ × Fin n → ι × Fin n) (δ : ι → ℕ) (G : MvPolynomial (κ × Fin n) R) :
    ∃ G' : MvPolynomial (κ × Fin n) R, G'.support ⊆ G.support ∧ rename f G' = homComp δ (rename f G) := by
  classical
  refine ⟨∑ mo ∈ G.support.filter (fun mo => ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i),
    monomial mo (G.coeff mo), ?_, ?_⟩
  · intro mo hmo
    obtain ⟨x, hx, h2⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmo)
    rw [Finset.mem_singleton.mp (support_monomial_subset h2)]
    exact (Finset.mem_filter.mp hx).1
  · ext a
    rw [coeff_homComp]
    conv_rhs => rw [G.as_sum]

    simp only [map_sum, coeff_sum, rename_monomial, coeff_monomial]
    rw [Finset.sum_filter]
    split_ifs with h
    · apply Finset.sum_congr rfl
      intro mo _
      by_cases hm : Finsupp.mapDomain f mo = a
      · have hP : ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i := by rw [hm]; exact h
        rw [if_pos hP]
      · simp only [hm, if_false, ite_self]
    · apply Finset.sum_eq_zero
      intro mo _
      by_cases hm : Finsupp.mapDomain f mo = a
      · have hP : ¬ ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i := by rw [hm]; exact h
        simp [hP]
      · simp [hm]

end Comp

section Big

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

private theorem upPl_monomial_eq_monomial_mPl (bp : TL J nL r × Fin r →₀ ℕ) (c : KK O) :
    upPl Fr p O hk nL (monomial bp c) = monomial (mPl Fr p hk nL bp) c := by
  rw [show monomial (mPl Fr p hk nL bp) c = C c * monomial (mPl Fr p hk nL bp) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upPl, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mPl, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

private theorem upNo_monomial_eq_monomial_mNo (bn : TL J nL r × Fin K →₀ ℕ) (c : KK O) :
    upNo Fr p O hk nL (monomial bn c) = monomial (mNo Fr p hk nL bn) c := by
  rw [show monomial (mNo Fr p hk nL bn) c = C c * monomial (mNo Fr p hk nL bn) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upNo, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mNo, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

theorem asm_support (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N : MvPolynomial (TL J nL r × Fin K) (KK O)) (mm : TV n' (m + 1) →₀ ℕ)
    (h : mm ∈ (asm Fr p O hk nL rho A N).support) :
    ∃ bp ∈ A.support, ∃ bn ∈ N.support, mm = bigM Fr p hk nL rho bp bn := by
  classical
  have e : asm Fr p O hk nL rho A N = ∑ bp ∈ A.support, ∑ bn ∈ N.support,
      monomial (bigM Fr p hk nL rho bp bn) (A.coeff bp * N.coeff bn) := by
    conv_lhs => rw [asm, A.as_sum, N.as_sum]

    simp only [map_sum, upPl_monomial_eq_monomial_mPl, upNo_monomial_eq_monomial_mNo, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bp _
    apply Finset.sum_congr rfl
    intro bn _
    rw [monomial_mul, monomial_mul, one_mul, bigM_eq]
  rw [e] at h
  obtain ⟨bp, hbp, h2⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum h)
  obtain ⟨bn, hbn, h3⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum h2)
  exact ⟨bp, hbp, bn, hbn, Finset.mem_singleton.mp (support_monomial_subset h3)⟩

theorem bigM_off (htop : ∀ x : TL J nL r, posOf n' (posTL Fr x) ∈ Fr.TT)
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (s : Fin n') (hs : s ∉ Set.range fun x : TL J nL r => posOf n' (posTL Fr x)) (c : Fin (m + 1)) :
    bigM Fr p hk nL rho bp bn (s, c) = 0 := by
  apply bigM_notin
  rintro ⟨v, hv⟩
  exact hs ⟨v.1, congrArg Prod.fst hv⟩

theorem multideg_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (hsurj : ∀ s ∈ Fr.TT, ∃ x : TL J nL r, posOf n' (posTL Fr x) = s)
    (htop : ∀ x : TL J nL r, posOf n' (posTL Fr x) ∈ Fr.TT)
    (d : Fin n' → ℕ) (hd : ∀ s, s ∉ Fr.TT → d s = 0)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (hB : BlockOK Fr p nL d rho dPl dNo)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (h1 : ∀ x, multideg bp x = dPl x)
    (h2 : ∀ x, multideg bn x = dNo x) (s : Fin n') : multideg (bigM Fr p hk nL rho bp bn) s = d s := by
  by_cases hs : s ∈ Set.range fun x : TL J nL r => posOf n' (posTL Fr x)
  · obtain ⟨x, rfl⟩ := hs
    have hsc : multideg (bigM Fr p hk nL rho bp bn) (posOf n' (posTL Fr x)) =
        ∑ a : Fin r, bigM Fr p hk nL rho bp bn (plVar Fr hk nL x a) +
          ∑ b : Fin K, bigM Fr p hk nL rho bp bn (noVar Fr hk nL x b) := by
      unfold multideg
      rw [← Equiv.sum_comp (finCongr hk.symm) (fun c => bigM Fr p hk nL rho bp bn (posOf n' (posTL Fr x), c)),
        Fin.sum_univ_add]
      rfl
    rw [hsc]
    simp only [bigM_pl hinj, bigM_no hinj, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hB.2 x, ← h1 x, ← h2 x, Fin.sum_univ_add (fun c => rho (x, c))]
    unfold multideg
    ring
  · have hT : s ∉ Fr.TT := fun hT => hs (hsurj s hT)
    rw [hd s hT]
    unfold multideg
    exact Finset.sum_eq_zero (fun c _ => bigM_off Fr p hk nL htop rho bp bn s hs c)

end Big

end Formalism.MainNotions.Proposition5Numerics
end
end
