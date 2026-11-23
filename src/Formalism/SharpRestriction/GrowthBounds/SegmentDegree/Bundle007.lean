module

import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CardFinRange
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FactorialMulChooseEqProdRange
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Kill

variable {R σ : Type} [CommRing R] (S : Set σ)


open Classical in
def kill : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun v => if v ∈ S then 0 else MvPolynomial.X v


open Classical in
def scaleS : MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  aeval fun v => if v ∈ S then Polynomial.X * Polynomial.C (MvPolynomial.X v) else Polynomial.C (MvPolynomial.X v)


open Classical in
def offDeg : (σ →₀ ℕ) →+ ℕ := Finsupp.liftAddHom fun v => if v ∈ S then AddMonoidHom.id ℕ else 0

theorem scaleS_monomial (m : σ →₀ ℕ) :
    scaleS (R := R) S (monomial m 1) = Polynomial.C (monomial m 1) * Polynomial.X ^ offDeg S m := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have : (monomial (f + g) (1 : R)) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, hf, hg, map_add (f := _), pow_add, map_mul]
    ring
  | single v k =>
    rw [← MvPolynomial.X_pow_eq_monomial, map_pow]
    by_cases hv : v ∈ S
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.X * Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = k := by simp [offDeg, hv]
      rw [h1, h2, mul_pow, Polynomial.C_pow, mul_comm]
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = 0 := by simp [offDeg, hv]
      rw [h1, h2, pow_zero, mul_one, Polynomial.C_pow]

theorem scaleS_coeff_zero (f : MvPolynomial σ R) : (scaleS S f).coeff 0 = kill S f := by
  classical
  have h : (Polynomial.constantCoeff.comp (scaleS (R := R) S : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R))) =
      (kill (R := R) S : MvPolynomial σ R →+* MvPolynomial σ R) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [scaleS, kill, MvPolynomial.algebraMap_eq]
    · intro v
      by_cases hv : v ∈ S <;> simp [scaleS, kill, hv]
  have := congrArg (fun g => g f) h
  simpa [Polynomial.constantCoeff_apply] using this

theorem li_of_kill {ι : Type} (m : ι → σ →₀ ℕ) (w : ι → MvPolynomial σ R)
    (h : LinearIndependent R fun q => monomial (m q) (1 : R) * kill S (w q)) :
    LinearIndependent R fun q => monomial (m q) (1 : R) * w q := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s a hsum
  by_contra hne
  push Not at hne
  obtain ⟨q0, hq0s, hq0⟩ := hne
  let s' := s.filter fun q => a q ≠ 0
  have hs' : s'.Nonempty := ⟨q0, Finset.mem_filter.mpr ⟨hq0s, hq0⟩⟩
  obtain ⟨q1, hq1, hmin⟩ := Finset.exists_min_image s' (fun q => offDeg S (m q)) hs'
  set δ := offDeg S (m q1) with hδ
  have hsum' : ∑ q ∈ s', a q • (monomial (m q) (1 : R) * w q) = 0 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro q hq hq'
    have : a q = 0 := by
      by_contra hh
      exact hq' (Finset.mem_filter.mpr ⟨hq, hh⟩)
    rw [this, zero_smul]
  have hΘ := congrArg (fun P => (scaleS S P).coeff δ) hsum'

  simp only [map_sum, map_smul, map_mul, scaleS_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
  map_zero, Polynomial.coeff_zero] at hΘ
  have hterm : ∀ q ∈ s', (Polynomial.C (monomial (m q) (1 : R)) * Polynomial.X ^ offDeg S (m q) *
      scaleS S (w q)).coeff δ = if offDeg S (m q) = δ then monomial (m q) (1 : R) * kill S (w q) else 0 := by
    intro q hq
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    have hle := hmin q hq
    split_ifs with h1 h2 h2
    · rw [h2, Nat.sub_self, scaleS_coeff_zero]
    · exact absurd (le_antisymm h1 hle) h2
    · exact absurd (le_of_eq h2) h1
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun q hq => by rw [hterm q hq]] at hΘ
  have hΘ' : ∑ q ∈ s'.filter (fun q => offDeg S (m q) = δ), a q • (monomial (m q) (1 : R) * kill S (w q)) = 0 := by
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) hΘ
    split_ifs <;> simp
  have := h _ a hΘ' q1 (Finset.mem_filter.mpr ⟨hq1, rfl⟩)
  exact (Finset.mem_filter.mp hq1).2 this

end Kill

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ)

omit [NeZero n'] in
def offSet (j : ℤ) : Set (ℤ × Fin (r + K)) :=
  {v | ∃ t c : Fin r, c ≠ Fin.rev t ∧ v = (X.F.fr j t.val, Fin.castAdd K c)}

omit [NeZero n'] in
def monTau (j : ℤ) (u : Fin r × Fin r → ℕ) : ℤ × Fin (r + K) →₀ ℕ :=
  ∑ v : Fin r × Fin r, Finsupp.single (X.F.fr j v.1.val, Fin.castAdd K v.2) (u v)

def wordEl (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

end Dat

def RestKey (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) =>
        monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)

theorem fr_injective {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    Function.Injective fun a : Fin r => F.fr j a.val :=
  fun a b hab => Fin.ext (TE.fr_inj hV j a.val b.val a.isLt b.isLt hab)

theorem plEmb_injective (O : Type) [CommRing O] (r K : ℕ) : Function.Injective (plEmb O r K) := by
  apply rename_injective
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)

theorem restInd_of (C₀ : ℝ) (hK : RestKey C₀) : RestInd C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  have h1 := li_of_kill (X.offSet K j) (fun q : X.Idx p K j (X.restr j b) => X.monTau K j q.1.2.2)
    (fun q => X.wordEl K O j q.1) (hK p n' r K X O S hX hLa hk j b hB)
  set c0 : MvPolynomial (ℤ × Fin r) O := X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) with hc0
  have hD : X.Dw O j ≠ 0 := Formalism.MainNotions.G.Joints.StandardMonomialSpace.detX_ne_zero _ (fr_injective X.F hX.valid (j - 1))
  have hc0ne : c0 ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ hD) (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_ne_zero _))
  have hc : plEmb O r K c0 ≠ 0 := (map_ne_zero_iff _ (plEmb_injective O r K)).mpr hc0ne
  have h2 := h1.map' (LinearMap.mulLeft O (plEmb O r K c0))
    (LinearMap.ker_eq_bot.mpr fun x y hxy => mul_left_cancel₀ hc hxy)
  have heq : (fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1) =
      (⇑(LinearMap.mulLeft O ((plEmb O r K) c0)) ∘
        fun q : X.Idx p K j (X.restr j b) => (monomial (X.monTau K j q.1.2.2)) (1 : O) * X.wordEl K O j q.1) := by
    funext q
    simp only [Function.comp, LinearMap.mulLeft_apply]
    unfold Dat.famEl Dat.wordEl Dat.monTau
    rw [map_mul, ← hc0, mul_assoc]
    congr 2
    rw [MvPolynomial.monomial_sum_one, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, ← MvPolynomial.X_pow_eq_monomial]
    simp [plEmb]
  rw [heq]
  exact h2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.SelectionLemmas.Pf.T

def LetterDictionaryBounds (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b →
    ∃ (n0 : ℕ) (od : Fin (segN X.F j) → Fin (segN X.F j)),
      HypT (segN X.F j) n0 r K (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
        (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.a X.La p ∧
      (∀ μ dd, X.IsPATH p K j (X.restr j b) μ dd ↔
        IsPATHa (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) μ dd) ∧
      (∀ μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ,
        GoodA (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
          (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p μ →
        X.IsGood p K j (X.restr j b) μ) ∧
      ((rkA r K n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) : ℕ) : ℝ) =
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) ∧
      Real.exp (11 * ((segN X.F j : ℕ) : ℝ) ^ 2 * ell0 (segN X.F j) X.a - min X.La ((r + K : ℕ) : ℝ) / 32) ≤
        1 / X.a ^ (X.Ns ^ 2)

theorem good_path_weight_of_parts (C₀ : ℝ) (ha : PathWeightEqRank) (hT : LemT) (he : LetterDictionaryBounds C₀) : GoodPathWeight C₀ := by
  intro p n' r K _ _ _ X hX hCLa hCk j b hb
  obtain ⟨n0, od, hH, hPATH, hGood, hrk, hexp⟩ := he p n' r K X hX hCLa hCk j b hb
  obtain ⟨hfin, hcard⟩ := hT (segN X.F j) n0 r K (segLL X.F j) _ od _ X.a X.La p hH
  obtain ⟨hfinA, -⟩ := ha (segN X.F j) n0 r K (segLL X.F j) _ od _ X.a X.La p hH
  let S : Set ((Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K))) :=
    {q | ∃ dd, X.IsPATH p K j (X.restr j b) q.1 dd ∧ X.IsGood p K j (X.restr j b) q.1 ∧ IsSt (tanPart q.1) q.2}
  have hSA : S ⊆ SAll (r := r) (K := K) (segLL X.F j) n0
      (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) := by
    rintro q ⟨dd, hp, -, hs⟩
    exact ⟨⟨dd, (hPATH q.1 dd).mp hp⟩, hs⟩
  have hGS : SGood (r := r) (K := K) (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p ⊆ S := by
    rintro q ⟨⟨dd, hp⟩, hg, hs⟩
    exact ⟨dd, (hPATH q.1 dd).mpr hp, hGood q.1 hg, hs⟩
  have hSfin : S.Finite := hfinA.subset hSA
  have hTS : Nat.card (X.Tset p K j (X.restr j b)) = S.ncard := Nat.card_coe_set_eq S
  refine ⟨hSfin.to_subtype, ?_⟩
  rw [hTS]
  have h1 : ((SGood (r := r) (K := K) (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p).ncard : ℝ) ≤ S.ncard := by
    exact_mod_cast Set.ncard_le_ncard hGS hSfin
  rw [mul_assoc, ← hrk]
  refine le_trans ?_ (le_trans hcard h1)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem finite_restrictSupport' (R : Type) [CommRing R] (σ : Type) (s : Set (σ →₀ ℕ)) (hs : s.Finite) :
    (restrictSupport R s : Submodule R (MvPolynomial σ R)).FG := by
  have heq : (restrictSupport R s : Submodule R (MvPolynomial σ R)) =
      Submodule.span R ((fun m => (monomial m (1 : R) : MvPolynomial σ R)) '' s) := by
    apply le_antisymm
    · intro P hP
      rw [MvPolynomial.mem_restrictSupport_iff] at hP
      rw [P.as_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      have : (monomial m (AddMonoidAlgebra.coeff P m) : MvPolynomial σ R) = AddMonoidAlgebra.coeff P m • monomial m (1 : R) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
      intro m' hm'
      have := MvPolynomial.support_monomial_subset (by exact_mod_cast hm')
      rw [Finset.mem_singleton] at this
      rw [this]; exact hm
  rw [heq]
  exact Submodule.fg_span (hs.image _)

theorem segDegSet_finite {r : ℕ} (K : ℕ) (b : ℤ → ℕ) (L : Finset ℤ) (hb : ∀ x, x ∉ L → b x = 0) :
    (Dat.segDegSet (r := r) K b).Finite := by
  classical
  let B : ℤ × Fin (r + K) →₀ ℕ := Finsupp.onFinset (L ×ˢ Finset.univ) (fun v => b v.1) (by
    intro v hv
    by_contra h
    apply hv
    apply hb
    intro hL
    exact h (Finset.mem_product.mpr ⟨hL, Finset.mem_univ _⟩))
  refine (Set.finite_Iic B).subset ?_
  intro m hm v
  have h := hm v.1
  have : m (v.1, v.2) ≤ ∑ c : Fin (r + K), m (v.1, c) :=
    Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  rw [h] at this
  simpa [B] using this

theorem restFin : RestFin := by
  intro p n' r K _ _ _ X O _ _ _ j b hb
  have hfg := finite_restrictSupport' O (ℤ × Fin (r + K)) _ (segDegSet_finite (r := r) K b (X.F.letters j) hb)
  have hN : IsNoetherian O (restrictSupport O (Dat.segDegSet (r := r) K b) : Submodule O (SegRing O r K)) :=
    isNoetherian_of_fg_of_noetherian _ hfg
  have hle : X.Mj p K O j b ≤ restrictSupport O (Dat.segDegSet (r := r) K b) := by
    intro P hP
    exact hP.1.2
  have : IsNoetherian O (X.Mj p K O j b) := isNoetherian_of_le hle
  infer_instance

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

theorem sum_one_le_hT (t : Fin n') (v : Fin (r + K) → ℕ) : 1 ≤ X.sumhT p K t v := by
  unfold Dat.sumhT
  refine sum_one_le_prod _ _ fun j _ => sum_one_le_prod _ _ fun x _ => ?_
  split_ifs
  · exact sum_one_le_bin _ _ _
  · exact le_rfl

theorem sum_mem_laSet (F : SumFacts X p K) {j0 x0 : ℤ} (hx0 : x0 ∈ X.toLate j0) (v : Fin (r + K) → ℕ)
    (h1 : ∀ c, v c < X.Pz p K j0 x0) (h2 : ∑ c, v c ≤ X.a' p K (posOf n' x0))
    (h3 : (∑ c, v c) % X.Pz p K j0 x0 = X.a' p K (posOf n' x0) % X.Pz p K j0 x0) :
    v ∈ X.laSet p K (posOf n' x0) := by
  classical
  unfold Dat.laSet
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun c => ?_, h2, fun j x hx hpos => ?_⟩
  · rw [Finset.mem_range]
    have : v c ≤ ∑ c, v c := Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · rw [F.uniqP j j0 x x0 hx hx0 hpos]
    exact ⟨h1, h3⟩

theorem sum_St_nontop (t : Fin n') (ht : t ∉ X.F.TT) : 1 ≤ X.sumSt p K t := by
  classical
  have h0 : (0 : Fin (r + K) → ℕ) ∈ X.laSet p K t := by
    unfold Dat.laSet
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun c => by simp, by simp, fun j x hx hpos => ?_⟩
    exact absurd (hpos ▸ (sum_late_mem hx).2.2.2) ht
  unfold Dat.sumSt
  exact (sum_one_le_hT t 0).trans
    (Finset.single_le_sum (f := fun v => X.sumhT p K t v) (fun v _ => zero_le_one.trans (sum_one_le_hT t v)) h0)

theorem sum_St_nonneg (t : Fin n') : 0 ≤ X.sumSt p K t :=
  Finset.sum_nonneg fun v _ => zero_le_one.trans (sum_one_le_hT t v)

theorem Pz_pos (hp : 0 < p) (j x : ℤ) : 0 < X.Pz p K j x := by unfold Dat.Pz; exact pow_pos hp _

theorem sum_St_LL (F : SumFacts X p K) (hr : 0 < r) (hp : 0 < p) (j0 : Fin X.F.J) {x0 : ℤ}
    (hx0 : x0 ∈ X.F.LLset (j0.val : ℤ)) :
    sumBin r K (X.a' p K (posOf n' x0)) ≤ X.sumSt p K (posOf n' x0) := by
  classical
  have hl := (F.LLsub _ _ hx0).1
  have hd := sum_digit_count (r + K) (X.a' p K (posOf n' x0)) (X.Pz p K (j0.val : ℤ) x0) (by omega) (Pz_pos hp _ _)
    (X.laSet p K (posOf n' x0)) (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)
  have hd' : sumBin r K (X.a' p K (posOf n' x0)) ≤ ∑ v ∈ X.laSet p K (posOf n' x0),
      sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x0) := by
    unfold sumBin
    exact_mod_cast hd
  refine hd'.trans (Finset.sum_le_sum fun v _ => ?_)
  unfold Dat.sumhT
  have hin : ∀ j : Fin X.F.J, ∀ x ∈ X.F.LLset (j.val : ℤ), (1 : ℝ) ≤
      (if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1) := by
    intro j x _
    split_ifs
    · exact sum_one_le_bin _ _ _
    · exact le_rfl
  have s1 := sum_single_le_prod (X.F.LLset (j0.val : ℤ)) (fun x => if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x) else 1) (hin j0) hx0
  have s2 := sum_single_le_prod (Finset.univ : Finset (Fin X.F.J)) (fun j => ∏ x ∈ X.F.LLset (j.val : ℤ),
      if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1)
      (fun j _ => sum_one_le_prod _ _ (hin j)) (Finset.mem_univ j0)
  simp only [if_true] at s1
  exact s1.trans s2

theorem sum_St_fr (F : SumFacts X p K) (hr : 0 < r) (hp : 0 < p) (j0 : ℤ) (i : Fin r) :
    ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤ X.sumSt p K (posOf n' (X.F.fr j0 i.val)) := by
  classical
  have hl := F.frlate j0 i
  have hd := sum_label_count (r + K) (X.a' p K (posOf n' (X.F.fr j0 i.val))) (X.Pz p K j0 (X.F.fr j0 i.val)) (by omega)
    (Pz_pos hp _ _) (F.kP _ _ hl) (X.laSet p K (posOf n' (X.F.fr j0 i.val)))
    (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)
  have hd' : ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤
      ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ) := by exact_mod_cast hd
  refine hd'.trans ?_
  unfold Dat.sumSt
  calc ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ)
      = ∑ _v ∈ X.laSet p K (posOf n' (X.F.fr j0 i.val)), (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun v _ => sum_one_le_hT _ v

theorem sum_LA :
    ∑ la ∈ X.LA p K, ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ), sumBin r K (X.nz p K la (j.val : ℤ) x) =
      ∏ t : Fin n', X.sumSt p K t := by
  classical
  unfold Dat.sumSt
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun la _ => ?_
  unfold Dat.sumhT
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_ite_eq]
  simp [Dat.nz]

theorem sub_le_mul_one_sub_and_mem_unit_interval {P c s : ℝ} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs : s ≤ P) :
    s - c ≤ P * (1 - c) ∧ 0 ≤ P * (1 - c) ∧ P * (1 - c) ≤ 1 := by
  refine ⟨by nlinarith, mul_nonneg hP0 (by linarith), by nlinarith⟩

end Steps

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
