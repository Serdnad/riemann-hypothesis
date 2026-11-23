module

public import Formalism.MahlerMeasure.Bundle001
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
public import Formalism.MahlerMeasure.Bundle003
public import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Comm

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}

theorem pderiv_mul_free (v : σ) (g f : MvPolynomial σ ℚ_[p]) (hg : pderiv v g = 0) :
    pderiv v (g * f) = g * pderiv v f := by
  rw [Derivation.leibniz, hg, smul_zero, add_zero, smul_eq_mul]

theorem pderiv_pair_free (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    pderiv v (∑ c, X (w c) * X (e c) : MvPolynomial σ ℚ_[p]) = 0 := by
  classical

  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Derivation.leibniz, pderiv_X, pderiv_X, Pi.single_eq_of_ne (he c), Pi.single_eq_of_ne (hw c)]
  simp

theorem commute_E_pderiv (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * pderiv v f = pderiv v ((∑ c, X (w c) * X (e c)) * f)
  rw [pderiv_mul_free v _ f (pderiv_pair_free w e v hw he)]

theorem commute_E_F (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact (commute_E_pderiv w e (w' c') (fun c => h1 c c') (fun c => h2 c c')).mul_right
    (commute_E_pderiv w e (e' c') (fun c => h3 c c') (fun c => h4 c c'))

theorem commute_E_E (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieE (k := ℚ_[p]) w' e') := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * ((∑ c, X (w' c) * X (e' c)) * f) =
    (∑ c, X (w' c) * X (e' c)) * ((∑ c, X (w c) * X (e c)) * f)
  ring


theorem commute_F_F (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieF (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_left _ _ _ fun c _ => Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  have h1 : Commute (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (e' c'))
  have h2 : Commute (pderiv (e c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (e' c'))
  exact h1.mul_left h2

theorem commute_tiePhi (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') (o n z o' n' z' : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.tiePhi w e o n z (Formalism.GM.tiePhi w' e' o' n' z' x) = Formalism.GM.tiePhi w' e' o' n' z' (Formalism.GM.tiePhi w e o n z x) := by
  have cEE := commute_E_E (p := p) w e w' e'
  have cFF := commute_F_F (p := p) w e w' e'
  have cEF := commute_E_F (p := p) w e w' e' h1 h2 h3 h4
  have cFE := (commute_E_F (p := p) w' e' w e (fun c c' => (h1 c' c).symm) (fun c c' => (h3 c' c).symm)
    (fun c c' => (h2 c' c).symm) (fun c c' => (h4 c' c).symm)).symm
  have cP : Commute (Formalism.GM.tiePhi (k := ℚ_[p]) w e o n z) (Formalism.GM.tiePhi (k := ℚ_[p]) w' e' o' n' z') := by
    unfold Formalism.GM.tiePhi
    refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun j' _ => ?_
    refine (Commute.smul_left ?_ _).smul_right _
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    exact ((cEE.pow_pow j j').mul_right (cEF.pow_pow j j')).mul_left ((cFE.pow_pow j j').mul_right (cFF.pow_pow j j'))
  exact LinearMap.congr_fun cP.eq x

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Hom

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def zLet : Fin (G.T.t + 1) → Fin (N + 1) :=
  Fin.lastCases (Fin.castSucc G.uPos) (fun i => M.finPos N (G.T.pos i))

def sLet : Fin (G.T.t + 1) → Fin (N + 1) :=
  Fin.lastCases (Fin.last N) (fun i => M.finPos N (G.T.pos i + 1))

def wL (a : Fin (N + 1)) : M.BVar N r G.T.t → ℕ
  | Sum.inl (a', _) => if a' = a then 1 else 0
  | Sum.inr (i, false) => if zLet G i = a then 1 else 0
  | Sum.inr (i, true) => if sLet G i = a then 1 else 0

def chDeg (LL : M.Letters N) (a : Fin (N + 1)) : ℕ := ∑ a0 : Fin N, if Fin.castSucc a0 = a then LL.deg a0 else 0

def dLvl (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  (∑ i, j i • ((if M.finPos N (G.T.pos i) = a then 1 else 0) + (if M.finPos N (G.T.pos i + 1) = a then 1 else 0))) +
    jp • ((if Fin.castSucc G.uPos = a then 1 else 0) + (if Fin.last N = a then 1 else 0)) +
    (∑ i, G.T.z i • (if M.finPos N (G.T.pos i) = a then 1 else 0)) +
    G.zPlus • (if Fin.castSucc G.uPos = a then 1 else 0) + chDeg (G.lettersAt j jp) a +
    (if Fin.last N = a then G.B - jp else 0)

theorem zLet_castSucc (i : Fin G.T.t) : zLet G (Fin.castSucc i) = M.finPos N (G.T.pos i) := by
  simp [zLet]

theorem zLet_last : zLet G (Fin.last G.T.t) = Fin.castSucc G.uPos := by
  simp [zLet]

theorem sLet_castSucc (i : Fin G.T.t) : sLet G (Fin.castSucc i) = M.finPos N (G.T.pos i + 1) := by
  simp [sLet]

theorem sLet_last : sLet G (Fin.last G.T.t) = Fin.last N := by
  simp [sLet]

theorem hom_Ehat (a : Fin (N + 1)) (i : Fin G.T.t) :
    IsWeightedHomogeneous (wL (r := r) G a) (G.Ehat p (r := r) i)
      ((if M.finPos N (G.T.pos i) = a then 1 else 0) + (if M.finPos N (G.T.pos i + 1) = a then 1 else 0)) := by
  unfold M.BlockData.Ehat
  apply IsWeightedHomogeneous.add
  · convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.castSucc i))).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalS N r G.T.t (Fin.castSucc i))) using 1
    simp [wL, M.scalZ, M.scalS, zLet_castSucc, sLet_castSucc]
  · apply IsWeightedHomogeneous.sum
    intro c _
    convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (M.finPos N (G.T.pos i), c) : M.BVar N r G.T.t)).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (M.finPos N (G.T.pos i + 1), c) : M.BVar N r G.T.t)) using 1
    simp [wL]

theorem hom_Eplus (a : Fin (N + 1)) :
    IsWeightedHomogeneous (wL (r := r) G a) (G.Eplus p (r := r))
      ((if Fin.castSucc G.uPos = a then 1 else 0) + (if Fin.last N = a then 1 else 0)) := by
  unfold M.BlockData.Eplus
  apply IsWeightedHomogeneous.add
  · convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.last G.T.t))).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalS N r G.T.t (Fin.last G.T.t))) using 1
    simp [wL, M.scalZ, M.scalS, zLet_last, sLet_last]
  · apply IsWeightedHomogeneous.sum
    intro c _
    convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.xiVar N r G.T.t c)) using 1
    simp [wL, M.xiVar]

theorem hom_chain (a : Fin (N + 1)) (LL : M.Letters N) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (wL (r := r) G a) (rename (M.chainEmb N r G.T.t) y) (chDeg LL a) := by
  classical
  have hsupp : ∀ m ∈ y.support, M.MultiDeg LL m := fun m hm => hy hm

  rw [y.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_fintype _ _ (fun _ => by simp)]
  unfold chDeg
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hsupp m hm i]
  simp only [M.chainEmb, wL]
  by_cases h : Fin.castSucc i = a <;> simp [h]

theorem hom_xi (a : Fin (N + 1)) (b : ℕ) (g : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ M.XiPolZ p N r G.T.t b) :
    IsWeightedHomogeneous (wL (r := r) G a) g (if Fin.last N = a then b else 0) := by
  classical
  intro μ hμ
  obtain ⟨hv, hb⟩ := hg.1 (mem_support_iff.mpr hμ)
  have hw : ∀ v, μ v * wL (r := r) G a v = μ v * (if Fin.last N = a then 1 else 0) := by
    intro v
    by_cases h0 : μ v = 0
    · simp [h0]
    · obtain ⟨c, rfl⟩ := hv v (Finsupp.mem_support_iff.mpr h0)
      rfl
  have hsum : ∑ v, μ v = ∑ c, μ (M.xiVar N r G.T.t c) := by
    rw [← Finset.sum_image (s := Finset.univ) (g := M.xiVar N r G.T.t) (by intro c _ c' _ h; simpa [M.xiVar] using h)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv'
    by_contra h0
    obtain ⟨c, rfl⟩ := hv v (Finsupp.mem_support_iff.mpr h0)
    exact hv' (Finset.mem_image_of_mem _ (Finset.mem_univ c))
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp only [smul_eq_mul, hw, ← Finset.sum_mul, hsum, hb]
  split_ifs <;> simp

theorem hom_gens (a : Fin (N + 1)) (j : Fin G.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hx : x ∈ G.gens p (r := r) j jp) : IsWeightedHomogeneous (wL (r := r) G a) x (dLvl G j jp a) := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  have hX : ∀ i, IsWeightedHomogeneous (wL (r := r) G a) (X (M.scalZ N r G.T.t (Fin.castSucc i)) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
      (if M.finPos N (G.T.pos i) = a then 1 else 0) := by
    intro i
    convert isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.castSucc i)) using 1
    simp [wL, M.scalZ, zLet_castSucc]
  have hXP : IsWeightedHomogeneous (wL (r := r) G a) (X (M.scalZ N r G.T.t (Fin.last G.T.t)) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
      (if Fin.castSucc G.uPos = a then 1 else 0) := by
    convert isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.last G.T.t)) using 1
    simp [wL, M.scalZ, zLet_last]
  unfold dLvl
  exact (((((IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hom_Ehat p G a i).pow (j i))).mul
    ((hom_Eplus p G a).pow jp)).mul (IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hX i).pow (G.T.z i)))).mul
    (hXP.pow G.zPlus)).mul (hom_chain p G a _ y hy.2.1)).mul (hom_xi p G a _ g hg)

theorem SSZ_support (z : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hz : z ∈ G.SSZ p (r := r)) :
    ∀ μ ∈ z.support, ∃ (j : Fin G.T.t → ℕ) (jp : ℕ), G.LevelOK j jp ∧
      ∀ a, Finsupp.weight (wL (r := r) G a) μ = dLvl G j jp a := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hlev, hx⟩ := hx
    intro μ hμ
    exact ⟨j, jp, hlev, fun a => hom_gens p G a j jp x hx (mem_support_iff.mp hμ)⟩
  | zero => simp
  | add x y _ _ hx hy =>
    intro μ hμ
    rcases Finset.mem_union.mp (support_add hμ) with h | h
    · exact hx μ h
    · exact hy μ h
  | smul c x _ hx =>
    intro μ hμ
    exact hx μ (support_smul hμ)

end Hom

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Disj

variable {k σ τ : Type} [Field k] [DecidableEq σ] [DecidableEq τ]

theorem mapDomain_add_inj (e : τ → σ) (he : Function.Injective e) (a b : τ →₀ ℕ) (β β' : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0)
    (h : Finsupp.mapDomain e a + β = Finsupp.mapDomain e b + β') : a = b ∧ β = β' := by
  have ha : a = b := by
    ext x
    have h1 := DFunLike.congr_fun h (e x)
    simpa [Finsupp.mapDomain_apply_of_injective he, hβ, hβ'] using h1
  subst ha
  exact ⟨rfl, add_left_cancel h⟩

theorem mfac_mapDomain_add (e : τ → σ) (he : Function.Injective e) (a : τ →₀ ℕ) (β : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) : (mfac (Finsupp.mapDomain e a + β) : k) = mfac a * mfac β := by
  unfold mfac
  have hd : Disjoint (Finsupp.mapDomain e a).support β.support := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact (Finsupp.mem_support_iff.1 hx') (hβ y)
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_mapDomain_index_inj he]

theorem fockK_rename_mul (e : τ → σ) (he : Function.Injective e) (A B : MvPolynomial τ k) (β β' : σ →₀ ℕ) (c : k)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0) :
    Formalism.GM.M.fockK (rename e A * monomial β 1) (rename e B * monomial β' c) =
      if β = β' then c * mfac β * Formalism.GM.M.fockK A B else 0 := by
  classical
  set F := rename e A * monomial β (1 : k) with hF
  set G := rename e B * monomial β' c with hG
  have hcF : ∀ m, F.coeff (Finsupp.mapDomain e m + β) = A.coeff m := by
    intro m
    rw [hF, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he, mul_one]
  have hcF0 : ∀ n, F.coeff n ≠ 0 → ∃ m, n = Finsupp.mapDomain e m + β ∧ A.coeff m ≠ 0 := by
    intro n hn
    rw [hF, MvPolynomial.coeff_mul_monomial'] at hn
    split_ifs at hn with hle
    · rw [mul_one] at hn
      obtain ⟨u, hu, hu0⟩ := MvPolynomial.coeff_rename_ne_zero e A (n - β) hn
      refine ⟨u, ?_, hu0⟩
      rw [hu]
      exact (tsub_add_cancel_of_le hle).symm
    · exact absurd rfl hn
  have hcG : ∀ m, G.coeff (Finsupp.mapDomain e m + β) = if β = β' then B.coeff m * c else 0 := by
    intro m
    split_ifs with hb
    · subst hb
      rw [hG, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he]
    · by_contra hne
      rw [hG, MvPolynomial.coeff_mul_monomial'] at hne
      split_ifs at hne with hle
      · have h1 : (rename e B).coeff (Finsupp.mapDomain e m + β - β') ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
        obtain ⟨u, hu, -⟩ := MvPolynomial.coeff_rename_ne_zero e B _ h1
        have h2 : Finsupp.mapDomain e m + β = Finsupp.mapDomain e u + β' := by
          rw [hu]
          exact (tsub_add_cancel_of_le hle).symm
        exact hb (mapDomain_add_inj e he m u β β' hβ hβ' h2).2
      · exact hne rfl
  have hmf : ∀ m : τ →₀ ℕ, ((Finsupp.mapDomain e m + β).prod fun _ j => (j.factorial : k)) =
      (m.prod fun _ j => (j.factorial : k)) * (β.prod fun _ j => (j.factorial : k)) :=
    fun m => mfac_mapDomain_add e he m β hβ
  unfold Formalism.GM.M.fockK
  have hsub : F.support ⊆ A.support.image (fun m => Finsupp.mapDomain e m + β) := by
    intro n hn
    obtain ⟨m, rfl, hm⟩ := hcF0 n (MvPolynomial.mem_support_iff.1 hn)
    exact Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hm, rfl⟩
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn]
    ring)]
  have hinj : Set.InjOn (fun m => Finsupp.mapDomain e m + β) A.support :=
    fun a _ b _ hab => (mapDomain_add_inj e he a b β β hβ hβ hab).1
  rw [Finset.sum_image hinj]
  simp only [hcF, hcG, hmf]
  split_ifs with hb
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold mfac
    ring
  · simp

end Disj

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
