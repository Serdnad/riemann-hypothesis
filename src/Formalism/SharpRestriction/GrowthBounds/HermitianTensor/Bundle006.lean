module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudDefs
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIsoDef
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeight
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LastNeZero
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ProdMemHten
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TaIntOfRename
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ExplicitMapOntoTwoLetterSpace
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaNuNextAdd
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.CovWeyl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle001

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def vStar (m a b : ℕ) : XY (m + 1) →₀ ℕ :=
  Finsupp.single (Sum.inl 0) a + Finsupp.single (Sum.inr (Fin.last m)) b

theorem qt_comb (m a b : ℕ) (v : XY (m + 1) →₀ ℕ) (hx : xDeg v = a) (hy : yDeg v = b)
    (h0 : qtW m v 0 = a + b) (hl : qtW m v (Fin.last m) = 0) : v = vStar m a b := by
  classical
  have e0 := qtW_apply m v 0
  have el := qtW_apply m v (Fin.last m)
  have l0 : v (Sum.inl 0) ≤ xDeg v :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  have ll : v (Sum.inr (Fin.last m)) ≤ yDeg v :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inr i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have a1 : v (Sum.inl 0) = a := by omega
  have a2 : v (Sum.inr (Fin.last m)) = b := by omega
  have z1 : ∀ i : Fin (m + 1), i ≠ 0 → v (Sum.inl i) = 0 := by
    intro i hi
    have h := Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inl i)) (Finset.mem_univ 0)
    have h' : ∑ x ∈ Finset.univ.erase (0 : Fin (m + 1)), v (Sum.inl x) = 0 := by
      have : ∑ x : Fin (m + 1), v (Sum.inl x) = a := hx
      omega
    exact Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
  have z2 : ∀ i : Fin (m + 1), i ≠ Fin.last m → v (Sum.inr i) = 0 := by
    intro i hi
    have h := Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inr i)) (Finset.mem_univ (Fin.last m))
    have h' : ∑ x ∈ Finset.univ.erase (Fin.last m), v (Sum.inr x) = 0 := by
      have : ∑ x : Fin (m + 1), v (Sum.inr x) = b := hy
      omega
    exact Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
  ext w
  unfold vStar
  rw [Finsupp.add_apply]
  rcases w with i | i
  · by_cases hi : i = 0
    · subst hi; simp [a1]
    · have : (Sum.inl 0 : XY (m + 1)) ≠ Sum.inl i := fun h => hi (Sum.inl.inj h).symm
      simp [this, z1 i hi]
  · by_cases hi : i = Fin.last m
    · subst hi; simp [a2]
    · have : (Sum.inr (Fin.last m) : XY (m + 1)) ≠ Sum.inr i := fun h => hi (Sum.inr.inj h).symm
      simp [this, z2 i hi]

theorem qtW_vStar (m a b : ℕ) (hm : 1 ≤ m) : qtW m (vStar m a b) 0 = a + b ∧ qtW m (vStar m a b) (Fin.last m) = 0 := by
  classical
  have hne : (Fin.last m) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have e0 := qtW_apply m (vStar m a b) 0
  have el := qtW_apply m (vStar m a b) (Fin.last m)
  have y : yDeg (vStar m a b) = b := by
    unfold yDeg vStar
    simp [Finsupp.single_apply]
  have v1 : vStar m a b (Sum.inr 0) = 0 := by
    unfold vStar
    simp [hne]
  have v2 : vStar m a b (Sum.inl 0) = a := by
    unfold vStar
    simp
  have v3 : vStar m a b (Sum.inr (Fin.last m)) = b := by
    unfold vStar
    simp
  have v4 : vStar m a b (Sum.inl (Fin.last m)) = 0 := by
    unfold vStar
    simp [hne.symm]
  constructor <;> omega

theorem topCore (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ)
    (Ψ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (hΨ : Ψ ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)))
    (h0 : RowA 0 Ψ (a + b)) (hl : RowA (Fin.last m) Ψ 0) :
    ∃ c : R.Kf, Ψ = c • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) := by
  classical
  rw [← tie3 h2 h5 hCO R m hm a b] at hΨ
  obtain ⟨f, hf, rfl⟩ := hΨ
  refine ⟨AddMonoidAlgebra.coeff f (vStar m a b), ?_⟩
  have hT : AddMonoidAlgebra.coeff f (vStar m a b) • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) =
      deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (AddMonoidAlgebra.coeff f (vStar m a b)))) := by
    rw [← map_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [hT]
  have hsum : dPsi R.Kf m f = ∑ v ∈ f.support, deltaB R.Kf m (PsiXY R.Kf m (monomial v (AddMonoidAlgebra.coeff f v))) := by
    conv_lhs => rw [dPsi_apply, f.as_sum]

    simp only [map_sum]
  obtain ⟨s0, sl⟩ := qtW_vStar m a b hm
  ext u
  by_cases hu : rowDeg u 0 = a + b ∧ rowDeg u (Fin.last m) = 0
  · rw [hsum, coeff_sum, Finset.sum_eq_single (vStar m a b)]
    · intro v hv hne
      by_contra hc
      apply hne
      have w0 := rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (AddMonoidAlgebra.coeff f v)) 0 u hc
      have wl := rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (AddMonoidAlgebra.coeff f v)) (Fin.last m) u hc
      exact qt_comb m a b v (hf v hv).1 (hf v hv).2 (by rw [← w0, hu.1]) (by rw [← wl, hu.2])
    · intro hv
      rw [notMem_support_iff.1 hv, monomial_zero, map_zero, map_zero, AddMonoidAlgebra.coeff_zero]
      rfl
  · have c1 : AddMonoidAlgebra.coeff (dPsi R.Kf m f) u = 0 := by
      by_contra hc
      exact hu ⟨h0 u hc, hl u hc⟩
    have c2 : AddMonoidAlgebra.coeff (deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (AddMonoidAlgebra.coeff f (vStar m a b))))) u = 0 := by
      by_contra hc
      have w0 := rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) 0 u hc
      have wl := rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) (Fin.last m) u hc
      exact hu ⟨by rw [w0, s0], by rw [wl, sl]⟩
    rw [c1, c2]

theorem topLineP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : TopLineP := by
  intro p n' R r hr a b Ψ hΨ h0 hl
  have hA : Antitone (nuOf (wtPQ (r + 1) a b)) := nuOf_anti _ (wtPQ_anti (r + 1) a b (by omega))
  obtain ⟨c, hc⟩ := topCore h2 h5 hCO R (r + 1) (by omega) a b Ψ hΨ h0 hl
  obtain ⟨c', hc'⟩ := topCore h2 h5 hCO R (r + 1) (by omega) a b (hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b)))
    (hwMem R.Kf _ _ le_rfl _ hA)
    (by have h := rowA_hw R.Kf _ _ hA 0; rwa [nuOf_wt_zero] at h)
    (by have h := rowA_hw R.Kf _ _ hA (Fin.last (r + 1)); rwa [nuOf_last] at h)
  have he := (hwMulP R.Kf _ _ _ hA hA).2
  set Z := deltaB R.Kf (r + 1) (PsiXY R.Kf (r + 1) (monomial (vStar (r + 1) a b) 1)) with hZ
  rw [hc', smul_eq_C_mul, map_mul, eval_C] at he
  rw [hc', hc, smul_eq_C_mul, smul_eq_C_mul, map_mul, eval_C, ← mul_assoc, ← C_mul]
  congr 2
  rw [mul_assoc, mul_comm _ c', he, mul_one]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

private theorem sub_wtPQ_apply_eq_ite (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl)) (i : Fin (mm + 1 + 1)) :
    (lam - wtPQ (mm + 1) P Q) i = if i = 0 then (ccl : ℤ) else if i = Fin.last (mm + 1) then -(ccl : ℤ) else lam i := by
  simp only [Pi.sub_apply, wtPQ]
  split_ifs with h1 h2
  · subst h1
    rw [h0]
    ring
  · subst h2
    rw [hl]
    ring
  · ring

private theorem antitone_sub_wtPQ (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (hlam : Antitone lam)
    (h0 : lam 0 = (P : ℤ) + ccl) (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
    (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) :
    Antitone (lam - wtPQ (mm + 1) P Q) := by
  intro a b hab
  rw [sub_wtPQ_apply_eq_ite mm ccl P Q lam h0 hl a, sub_wtPQ_apply_eq_ite mm ccl P Q lam h0 hl b]
  have hlv : (Fin.last (mm + 1)).val = mm + 1 := Fin.val_last _
  have hab' : a.val ≤ b.val := hab
  have hc : (0 : ℤ) ≤ (ccl : ℤ) := Int.natCast_nonneg _
  have hbl' := b.isLt
  have hal' := a.isLt
  by_cases ha0 : a = 0
  · subst ha0
    rw [ite_eq_left rfl]
    split_ifs with hb0 hbl
    · exact le_refl _
    · linarith
    · have hb1 : 0 < b.val := Nat.pos_of_ne_zero (fun h => hb0 (Fin.ext h))
      have hb2 : b.val < mm + 1 := by
        have : b.val ≠ mm + 1 := fun h => hbl (Fin.ext (h.trans hlv.symm))
        omega
      exact le_trans (le_abs_self _) (hmid b hb1 hb2)
  · by_cases hal : a = Fin.last (mm + 1)
    · have hb : b = Fin.last (mm + 1) := by
        apply Fin.ext
        rw [hal] at hab'
        omega
      subst hal
      subst hb
      exact le_refl _
    · have ha1 : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha0 (Fin.ext h))
      have ha2 : a.val < mm + 1 := by
        have : a.val ≠ mm + 1 := fun h => hal (Fin.ext (h.trans hlv.symm))
        omega
      rw [ite_eq_right ha0, ite_eq_right hal]
      split_ifs with hb0 hbl
      · exfalso
        have : b.val = 0 := by rw [hb0]; rfl
        omega
      · linarith [neg_abs_le (lam a), hmid a ha1 ha2]
      · exact hlam hab

theorem restCloudLat_of (h1 : CloudOne) (hCO : CartanOnto) (hIso : CloudIsoP) : RestCloudLat := by
  unfold RestCloudLat
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hbase hdom hoff hAB hc H Hp ze lo lo' hH hHp hze hlo hlo'
  subst hH hHp hze hlo hlo'
  have hdomlo : IsDominant (lam0 - flatW (mm + 1) A B) := by
    intro s
    by_cases hs : s ∈ TT
    · have e : (lam0 - flatW (mm + 1) A B) s = lam0 s - wtPQ (mm + 1) (A ⟨s, hs⟩) (B ⟨s, hs⟩) := by
        rw [Pi.sub_apply, ← flatW_top (mm + 1) A B ⟨s, hs⟩]
      rw [e]
      obtain ⟨h0, hl, hmid⟩ := (hbase s).1 hs
      obtain ⟨hA, hB⟩ := hAB ⟨s, hs⟩
      exact antitone_sub_wtPQ mm ccl _ _ (lam0 s) (hdom s) (by rw [h0]; linarith) (by rw [hl]; linarith) hmid
    · have e : (lam0 - flatW (mm + 1) A B) s = lam0 s := by
        rw [Pi.sub_apply, flatW_off (mm + 1) A B s hs, sub_zero]
      rw [e]
      exact hdom s
  have hdomlo' : IsDominant (dualW (lam0 - flatW (mm + 1) A B)) := by
    intro s a' b' hab
    show -(lam0 - flatW (mm + 1) A B) s b'.rev ≤ -(lam0 - flatW (mm + 1) A B) s a'.rev
    exact neg_le_neg (hdomlo s (Fin.rev_le_rev.mpr hab))
  have hadd1 : ∀ s, lamAt (flatW (mm + 1) (fun s : TT => A s + 2 * ccl) fun s : TT => B s + 2 * ccl) s
      = lamAt (flatW (mm + 1) A B) s + lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) fun _ : TT => 2 * ccl) s := by
    intro s
    rw [← lamAt_add']
    congr 1
    exact flatW_add (mm + 1) A B (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)
  have hadd2 : ∀ s, lamAt lam0 s = lamAt (flatW (mm + 1) A B) s + lamAt (lam0 - flatW (mm + 1) A B) s := by
    intro s
    rw [lamAt_sub']
    ring
  have hdz : dualWt (0 : Fin (mm + 1 + 1) → ℤ) = 0 := by
    funext i
    simp [dualWt]
  have hpos : ∀ s, PosOK R (mm + 1) (lamAt lam0 s) (lamAt (flatW (mm + 1) A B) s)
      (lamAt (flatW (mm + 1) (fun s : TT => A s + 2 * ccl) fun s : TT => B s + 2 * ccl) s)
      (lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) fun _ : TT => 2 * ccl) s)
      (lamAt (lam0 - flatW (mm + 1) A B) s) (lamAt (dualW (lam0 - flatW (mm + 1) A B)) s)
      (if s ∈ TT then weylDim mm (cloudAt lam0 s) else 1) (if s ∈ TT then ⌈kappaOneExponent p a (mm + 1)⌉₊ else 0) := by
    intro s
    by_cases hs : s ∈ TT
    · rw [ite_eq_left hs, ite_eq_left hs]
      exact posOK_at_top h1 R mm hmm TT a ccl aw bw lam0 A B hbase hdom hAB hc ⟨s, hs⟩
    · rw [ite_eq_right hs, ite_eq_right hs, lamAt_dualW, lamAt_sub', tn_lamAt_zero lam0 s (hoff s hs),
        lamAt_flat_off (mm + 1) A B s hs,
        lamAt_flat_off (mm + 1) (fun s : TT => A s + 2 * ccl) (fun s : TT => B s + 2 * ccl) s hs,
        lamAt_flat_off (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s hs, sub_self, hdz]
      exact posOK_zero R (mm + 1)
  obtain ⟨mH, mU, abelian₂, hlat, hrest⟩ := cloudTen R (mm + 1) lam0 _ _ _ _ _ hdom (flatW_dom _ _ _)
    (flatW_dom _ _ _) (flatW_dom _ _ _) hdomlo hdomlo' hadd1 hadd2 _ _ hpos hCO hIso
  refine ⟨mH, mU, abelian₂, hlat, fun gs hgs => ?_⟩
  obtain ⟨nb, z0, sb, sb', ka, hnb, hka, hrest2⟩ := hrest gs hgs
  refine ⟨nb, z0, sb, sb', ka, ?_, ?_, hrest2⟩
  · have e : (∏ s : Fin n', (if s ∈ TT then weylDim mm (cloudAt lam0 s) else 1))
        = ∏ s : TT, weylDim mm (cloudAt lam0 ↑s) := by
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_coe_sort TT (fun s => weylDim mm (cloudAt lam0 s))]
    rw [dimCl, ← e, ← hnb]
    exact (Rat.cast_natCast nb).symm
  · intro b
    have hb := hka b
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul] at hb
    exact hb

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem ta_last_ne (m : ℕ) (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have h2 := congrArg Fin.val h
  simp at h2
  omega

section L

variable {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (hg : IsUnit g.det)

include hm hg

theorem ta_vec_mem (P : ℕ) (a : MvPolynomial (Fin (m + 1)) R.Kf) (ha : a.IsHomogeneous P) (hI : ta_Int R.O a) :
    rowAct R.Kf g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a) ∈ H0 R.O m (letterWt m P true) (colSpan R.O g) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  refine (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).2 ?_
  have h0 : letterWt m P true (Fin.last m) = 0 := by simp [letterWt, ta_last_ne m hm]
  rw [h0, zpow_zero, one_smul, rowAct_inv_cancel g hg]
  refine intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_rename _ hI) u)
  rw [ta_nuOf_vec m P hm]
  exact (ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).2 ⟨a, ha, rfl⟩

theorem ta_cov_mem (Q : ℕ) (b : MvPolynomial (Fin (m + 1)) R.Kf) (hb : b.IsHomogeneous Q) (hI : ta_Int R.O b) :
    g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) b) ∈ H0 R.O m (letterWt m Q false) (colSpan R.O g) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  refine (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).2 ?_
  have h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ) := by simp [letterWt]
  rw [h0, map_smul, rowAct_inv_cancel g hg, smul_smul, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]
  refine intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_aeval m hI) u)
  rw [ta_nuOf_cov m Q]
  exact (ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).2 ⟨b, hb, rfl⟩

theorem ta_vec_of (P : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
    (hF : F ∈ H0 R.O m (letterWt m P true) (colSpan R.O g)) :
    ∃ a : MvPolynomial (Fin (m + 1)) R.Kf, a.IsHomogeneous P ∧ ta_Int R.O a ∧
      F = rowAct R.Kf g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have h1 := (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).1 hF
  have h0 : letterWt m P true (Fin.last m) = 0 := by simp [letterWt, ta_last_ne m hm]
  rw [h0, zpow_zero, one_smul] at h1
  have h2 := intO_le _ _ _ h1
  rw [ta_nuOf_vec m P hm] at h2
  obtain ⟨a, ha, e⟩ := (ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).1 h2
  refine ⟨a, ha, ta_Int_of_rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1)))) ?_ ?_, ?_⟩
  · intro i j hij
    exact (Prod.mk.inj hij).1
  · rw [e]
    obtain ⟨f, -, hf⟩ := h1
    exact ⟨f, hf⟩
  · rw [e, rowAct_cancel_inv g hg]

theorem ta_cov_of (Q : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
    (hF : F ∈ H0 R.O m (letterWt m Q false) (colSpan R.O g)) :
    ∃ b : MvPolynomial (Fin (m + 1)) R.Kf, b.IsHomogeneous Q ∧ ta_Int R.O b ∧
      F = g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) b) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have h1 := (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).1 hF
  have h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ) := by simp [letterWt]
  rw [h0] at h1
  have h2 := intO_le _ _ _ h1
  rw [ta_nuOf_cov m Q] at h2
  obtain ⟨b, hb, e⟩ := (ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).1 h2
  rw [covY_eq] at e
  refine ⟨b, hb, ta_sat R.w R.std.2.1 m hm b ?_, ?_⟩
  · rw [e]
    obtain ⟨f, -, hf⟩ := h1
    exact ⟨f, hf⟩
  · rw [e, map_smul, rowAct_cancel_inv g hg, smul_smul, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]

end L

theorem two_letter_lattice_gauss_inverse : TwoLetterLatticeGaussInverse := by
  intro p n' R m hm g hg g' hg' P Q f hf
  constructor
  · intro hx
    have key : ∀ x ∈ twoLat R.O m P Q (colSpan R.O g),
        ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x := by
      intro x hx
      unfold twoLat tensorLat at hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x) ?_ ?_ ?_ ?_ hx
      · rintro y ⟨F, hF, rfl⟩
        have ht := hF true
        have hf' := hF false
        simp only [ite_true, Bool.false_eq_true, ite_false] at ht hf'
        obtain ⟨a, ha, hIa, ea⟩ := ta_vec_of R m hm g hg P _ ht
        obtain ⟨b, hb, hIb, eb⟩ := ta_cov_of R m hm g hg Q _ hf'
        refine ⟨rename Sum.inl a * rename Sum.inr b, ta_Int_mul (ta_Int_rename _ hIa) (ta_Int_rename _ hIb), ?_⟩
        rw [ta_Psi_gl g hg g' hg' Q a b hb, ← ea, ← eb, Fintype.prod_bool]
      · exact ⟨0, ⟨0, map_zero _⟩, by simp⟩
      · rintro x y _ _ ⟨f1, h1, rfl⟩ ⟨f2, h2, rfl⟩
        exact ⟨f1 + f2, ta_Int_add h1 h2, by rw [map_add (f := _), map_add (f := _)]⟩
      · rintro c x _ ⟨f1, h1, rfl⟩
        exact ⟨algebraMap R.O R.Kf c • f1, ta_Int_smul c h1, by rw [map_smul, map_smul, algebraMap_smul]⟩
    obtain ⟨f₀, hI, he⟩ := key _ hx
    have h1 := explicit_map_injective R.Kf m hm he
    refine ⟨f₀, fun u => ?_, h1⟩
    obtain ⟨c, hc⟩ := ta_Int_coeff hI u
    rw [← hc]
    exact R.mem_Ov c
  · rintro ⟨f₀, hG, rfl⟩
    have hf₀ : f₀ ∈ PolAB R.Kf (m + 1) P Q := by
      have := glAct_mem_PolAB g'⁻¹ _ hf
      rwa [glAct_inv_glAct] at this

    rw [f₀.as_sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    obtain ⟨c, hc⟩ : ∃ c : R.O, algebraMap R.O R.Kf c = AddMonoidAlgebra.coeff f₀ v := hG v
    rw [ta_monomial_split, map_smul, map_smul, ← hc, algebraMap_smul]
    refine Submodule.smul_mem _ _ ?_
    have hP : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i)).IsHomogeneous P := by
      have := ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inl i))
      rwa [show ∑ i : Fin (m + 1), v (Sum.inl i) = P from (hf₀ v hv).1] at this
    have hQ : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)).IsHomogeneous Q := by
      have := ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inr i))
      rwa [show ∑ i : Fin (m + 1), v (Sum.inr i) = Q from (hf₀ v hv).2] at this
    rw [ta_Psi_gl g hg g' hg' Q _ _ hQ]
    refine Submodule.subset_span ⟨fun b : Bool => (cond b
      (rowAct R.Kf g⁻¹ (rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1))))
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i))))
      (g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m)
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf), ?_, ?_⟩
    · intro b
      cases b
      · simp only [Bool.false_eq_true, ite_false, Bool.cond_false]
        exact ta_cov_mem R m hm g hg Q _ hQ (ta_Int_prodX _)
      · simp only [ite_true, Bool.cond_true]
        exact ta_vec_mem R m hm g hg P _ hP (ta_Int_prodX _)
    · rw [Fintype.prod_bool]
      rfl

end Formalism.MainNotions.flipOneThree.Pf

end
end
