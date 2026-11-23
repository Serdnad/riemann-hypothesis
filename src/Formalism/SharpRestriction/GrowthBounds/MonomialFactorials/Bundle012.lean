module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle011
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LiRenameMon
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem mono_mem_xiPolZ (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    monomial m (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r G.T.t n := by
  classical
  obtain ⟨h1, h2, -⟩ := xiMons_spec (r := r) G n m hm
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    have hm2 : m' = m := Finset.mem_singleton.1 (support_monomial_subset hm')
    subst hm2
    exact ⟨h1, h2⟩
  · exact ⟨monomial m 1, by simp⟩

theorem pderiv_chain_mono (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n)
    (a : Fin N) (c : Fin r) : pderiv (Sum.inl (Fin.castSucc a, c)) (monomial m (1 : ℚ_[p])) = 0 := by
  obtain ⟨h1, -, -⟩ := xiMons_spec (r := r) G n m hm
  rw [pderiv_monomial]
  have : m (Sum.inl (Fin.castSucc a, c)) = 0 := by
    by_contra hne
    obtain ⟨d, hd⟩ := h1 _ (Finsupp.mem_support_iff.2 hne)
    simp only [Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hd
    exact absurd hd.1 (Fin.castSucc_ne_last a)
  rw [this]
  simp

theorem mono_chain_zero (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n)
    (x : Fin N × Fin r) : m (Formalism.GM.M.chainEmb N r G.T.t x) = 0 := by
  obtain ⟨h1, -, -⟩ := xiMons_spec (r := r) G n m hm
  by_contra hne
  obtain ⟨d, hd⟩ := h1 _ (Finsupp.mem_support_iff.2 hne)
  simp only [Formalism.GM.M.chainEmb, Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hd
  exact absurd hd.1 (Fin.castSucc_ne_last x.1)

theorem chainEmb_inj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
  intro x y h
  simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.castSucc_injective _ h.1) h.2

theorem cf_mul (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    (((n.factorial / (m.prod fun _ k => k.factorial) : ℕ) : ℚ_[p]) * (mfac m : ℚ_[p])) = (n.factorial : ℚ_[p]) := by
  obtain ⟨-, -, h3⟩ := xiMons_spec (r := r) G n m hm
  have hdvd : (m.prod fun _ k => k.factorial) ∣ n.factorial := by
    have := Nat.prod_factorial_dvd_factorial_sum m.support m
    rw [h3] at this
    exact this
  have e : (mfac m : ℚ_[p]) = ((m.prod fun _ k => k.factorial : ℕ) : ℚ_[p]) := by
    unfold mfac Finsupp.prod
    push_cast
    rfl
  rw [e, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]

theorem plusAW_of_blockOK (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : RestPlusAW p (r := r) G j jp D := by
  classical
  unfold RestPlusAW
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p
    (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D
  have hcard : (xiMons (r := r) G (G.B - jp)).card = dXi r (G.B - jp) := card_xiMons_eq (r := r) G (G.B - jp)
  let e := Fintype.equivFin (Fin (Formalism.GM.M.goodCount p
    (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D) × (xiMons (r := r) G (G.B - jp)))
  let cfn : (Formalism.GM.M.BVar N r G.T.t →₀ ℕ) → ℕ := fun m => (G.B - jp).factorial / (m.prod fun _ k => k.factorial)
  have hXm : ∀ k, rename (Formalism.GM.M.chainEmb N r G.T.t) (x (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]) ∈
      Ljj p (r := r) G j jp := fun k =>
    Submodule.subset_span ⟨x (e.symm k).1, hx _, _, mono_mem_xiPolZ p (r := r) G (G.B - jp) _ (e.symm k).2.2, rfl⟩
  have hYm : ∀ k, ((cfn (e.symm k).2.1 : ℕ) : ℚ_[p]) •
      (rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p])) ∈
      Ljj p (r := r) G j jp := by
    intro k
    have h1 : rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]) ∈
        Ljj p (r := r) G j jp :=
      Submodule.subset_span ⟨y (e.symm k).1, hy _, _, mono_mem_xiPolZ p (r := r) G (G.B - jp) _ (e.symm k).2.2, rfl⟩
    have h2 := Submodule.smul_mem (Ljj p (r := r) G j jp) ((cfn (e.symm k).2.1 : ℕ) : ℤ_[p]) h1
    rw [algebra_compatible_smul ℚ_[p] ((cfn (e.symm k).2.1 : ℕ) : ℤ_[p]), map_natCast] at h2
    exact h2
  have hpair : ∀ k k', bePhi p (r := r) G j jp
      (rename (Formalism.GM.M.chainEmb N r G.T.t) (x (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]))
      (((cfn (e.symm k').2.1 : ℕ) : ℚ_[p]) •
        (rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k').1) * monomial (e.symm k').2.1 (1 : ℚ_[p]))) =
      if k = k' then (p : ℚ_[p]) ^ D else 0 := by
    intro k k'
    obtain ⟨⟨i, m, hm⟩, hk⟩ : ∃ q, e.symm k = q := ⟨_, rfl⟩
    obtain ⟨⟨i', m', hm'⟩, hk'⟩ : ∃ q, e.symm k' = q := ⟨_, rfl⟩
    have hkk : k = k' ↔ (i = i' ∧ m = m') := by
      constructor
      · rintro rfl
        rw [hk] at hk'
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk'
        exact hk'
      · rintro ⟨rfl, rfl⟩
        exact e.symm.injective (hk.trans hk'.symm)
    rw [hk, hk']
    dsimp only
    rw [bePhi_smul_right]
    unfold bePhi
    rw [phisB_rename_mul p (r := r) G hB j jp _ _ (fun a c => pderiv_chain_mono p (r := r) G (G.B - jp) m hm a c),
      fockK_rename_mul _ (chainEmb_inj (r := r) G) _ _ m m' 1 (mono_chain_zero (r := r) G (G.B - jp) m hm)
        (mono_chain_zero (r := r) G (G.B - jp) m' hm')]
    have hxy' : Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
        ∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p]) = if i = i' then (p : ℚ_[p]) ^ D else 0 := hxy i i'
    by_cases hmm : m = m'
    · subst hmm
      rw [if_pos rfl]
      have hcf := cf_mul p (r := r) G (G.B - jp) m hm
      have hdeg : (degFact G j jp : ℚ_[p]) =
          (∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]) := by
        unfold degFact; push_cast; rfl
      have hF : Formalism.GM.M.fockK (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') =
          Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') := rfl
      have hP : (∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun a _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hn0 : ((G.B - jp).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      rw [hdeg, hF]
      have key : ((cfn m : ℕ) : ℚ_[p]) *
          (1 * mfac m * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
            ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]))) =
          Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
            ∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p]) := by
        rw [show ((cfn m : ℕ) : ℚ_[p]) *
            (1 * mfac m * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
              ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]))) =
            (((cfn m : ℕ) : ℚ_[p]) * mfac m) * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
              ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p])) by ring]
        rw [hcf]
        field_simp
      rw [key, hxy']
      by_cases hii : i = i'
      · rw [if_pos hii, if_pos (hkk.2 ⟨hii, rfl⟩)]
      · rw [if_neg hii, if_neg (fun h => hii (hkk.1 h).1)]
    · rw [if_neg hmm, if_neg (fun h => hmm (hkk.1 h).2)]
      simp
  have hmem := le_csSup (gcL_bdd p (r := r) G j jp D) ⟨fun k => _, fun k => _, hXm, hYm, hpair⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hcard] at hmem
  exact hmem

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem plusAWICondition (CM : ℝ) : RestPlusAWI C0 CE1 CE2 X CM := by
  intro dl _ aTop _ x _
  exact plusAW_of_blockOK X.p (gB C0 CE1 CE2 X aTop 0 x.1) (gB_blockOK C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 _

theorem plusACondition (CM : ℝ) : RestPlusA C0 CE1 CE2 X CM :=
  restPlusA_of C0 CE1 CE2 X CM (plusAWICondition C0 CE1 CE2 X CM)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Gen

variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]

theorem gc_bdd_gen (be : V → V → ℚ_[p]) (hsm : ∀ (c : ℚ_[p]) u v, be (c • u) v = c * be u v)
    (hsum : ∀ (n : ℕ) (s : Finset (Fin n)) (f : Fin n → V) v, be (∑ i ∈ s, f i) v = ∑ i ∈ s, be (f i) v)
    (L : Submodule ℤ_[p] V) (W : Submodule ℚ_[p] V) [FiniteDimensional ℚ_[p] W] (hLW : ∀ x ∈ L, x ∈ W) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → V, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i k, be (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  refine ⟨Module.finrank ℚ_[p] W, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hpD : (p : ℚ_[p]) ^ D ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hz : ∀ v, be 0 v = 0 := by
    intro v
    simpa using hsm 0 0 v

  let x' : Fin n → W := fun i => ⟨x i, hLW _ (hx i)⟩
  have hli : LinearIndependent ℚ_[p] x' := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hg' : ∑ j ∈ s, g j • x j = 0 := by
      have := congrArg Subtype.val hg
      simpa [x'] using this
    have h1 := congrArg (fun u => be u (y i)) hg'
    rw [hsum n s (fun j => g j • x j) (y i), hz] at h1
    simp only [hsm, hxy] at h1
    rw [Finset.sum_eq_single i] at h1
    · simpa [hpD] using h1
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd hi h
  simpa using hli.fintype_card_le_finrank

theorem bad_le_sub (be : V → V → ℚ_[p]) (L L₁ : Submodule ℤ_[p] V) (hle : L₁ ≤ L) (D : ℤ) (n₁ : ℕ)
    (hn : Module.finrank ℤ_[p] L₁ = n₁)
    (hb : BddAbove {n | ∃ x y : Fin n → V, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i k, be (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0}) :
    Formalism.GM.M.bad p be L D ≤ (Module.finrank ℤ_[p] L - n₁) + Formalism.GM.M.bad p be L₁ D := by
  have hgc : Formalism.GM.M.goodCount p be L₁ D ≤ Formalism.GM.M.goodCount p be L D := by
    unfold Formalism.GM.M.goodCount
    apply csSup_le_csSup hb
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    · rintro n ⟨x, y, hx, hy, h⟩
      exact ⟨x, y, fun i => hle (hx i), fun i => hle (hy i), h⟩
  unfold Formalism.GM.M.bad
  rw [hn]
  omega

end Gen

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

private theorem fockK_eq_lemma {k σ : Type} [Field k] (F G : MvPolynomial σ k) (s : Finset (σ →₀ ℕ))
    (hs : F.support ⊆ s) :
    Formalism.GM.M.fockK F G = ∑ m ∈ s, F.coeff m * G.coeff m * (m.prod fun _ j => (j.factorial : k)) := by
  unfold Formalism.GM.M.fockK
  apply Finset.sum_subset hs
  intro m _ hm
  have h0 : F.coeff m = 0 := by simpa using hm
  rw [h0, zero_mul, zero_mul]

theorem bejj_smul_left (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bejj p (r := r) G j jp (c • u) v = c * bejj p (r := r) G j jp u v := by
  unfold bejj
  rw [map_smul, fockK_eq_lemma _ v _ MvPolynomial.support_smul]
  unfold Formalism.GM.M.fockK
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem bejj_sum_left (j : Fin G.T.t → ℕ) (jp : ℕ) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) (v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bejj p (r := r) G j jp (∑ i ∈ s, f i) v = ∑ i ∈ s, bejj p (r := r) G j jp (f i) v := by
  classical
  unfold bejj

  rw [map_sum, ← Finset.sum_div]
  congr 1
  set S := (∑ i ∈ s, G.phiAll p (r := r) j jp (f i)).support ∪
    s.biUnion (fun i => (G.phiAll p (r := r) j jp (f i)).support) with hS
  rw [fockK_eq_lemma _ v S Finset.subset_union_left]
  rw [Finset.sum_congr rfl (fun i hi => fockK_eq_lemma (G.phiAll p (r := r) j jp (f i)) v S
    ((Finset.subset_biUnion_of_mem (fun i => (G.phiAll p (r := r) j jp (f i)).support) hi).trans
      Finset.subset_union_right))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_sum, Finset.sum_mul, Finset.sum_mul]

theorem bejj_bdd (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G j jp) ∧ (∀ i, y i ∈ Ljj p (r := r) G j jp) ∧
      ∀ i k, bejj p (r := r) G j jp (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  obtain ⟨W, hW, hLW⟩ := exists_fd_Ljj p (r := r) G j jp
  haveI := hW
  exact gc_bdd_gen p (bejj p (r := r) G j jp) (bejj_smul_left p G j jp)
    (fun n s f v => bejj_sum_left p G j jp s f v) (Ljj p (r := r) G j jp) W hLW D

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestOrth (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ∧ LinearIndependent ℤ_[X.p] e ∧
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) ∧
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) ∧
      n₁ ≤ Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ∧
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ≤
        n₁ + Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
          (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋

def RestWin (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∀ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) → LinearIndependent ℤ_[X.p] e →
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) →
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) →
      (∑ aPlus ∈ X.winA, (Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
          (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
        (X.winA.card : ℝ) * (5 / X.L.Y * n₁)

variable {C0 CE1 CE2 X}

theorem restPlusB_of (CM : ℝ) (hY : 0 < X.L.Y) (hO : RestOrth C0 CE1 CE2 X CM) (hW : RestWin C0 CE1 CE2 X CM) :
    RestPlusB C0 CE1 CE2 X CM := by
  intro dl hdl aTop haTop x hx
  obtain ⟨n₁, e, he, hli, horth, hval, hn1, hrk⟩ := hO dl hdl aTop haTop x hx
  have hwin := hW dl hdl aTop haTop x hx n₁ e he hli horth hval
  have hspan : Submodule.span ℤ_[X.p] (Set.range e) ≤
      Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 :=
    Submodule.span_le.2 (by
      rintro _ ⟨a, rfl⟩
      exact he a)
  have hrank : Module.finrank ℤ_[X.p] (Submodule.span ℤ_[X.p] (Set.range e)) = n₁ := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hstep : ∀ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) ≤
      ((Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁ : ℕ) : ℝ) +
        (Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
          (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    intro aPlus _
    have h := bad_le_sub X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
      (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
      (Submodule.span ℤ_[X.p] (Set.range e)) hspan ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ n₁ hrank
      (bejj_bdd X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2 _)
    have h' : bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ ≤
        (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁) +
          Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
            (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := h
    exact_mod_cast h'
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h1 : ((Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁ : ℕ) : ℝ) ≤
      (Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
        (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    exact_mod_cast (by omega)
  have hc : (0 : ℝ) ≤ 5 / X.L.Y := div_nonneg (by norm_num) hY.le
  have h2 : 5 / X.L.Y * (n₁ : ℝ) ≤ 5 / X.L.Y *
      (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hn1) hc
  have hcard : (0 : ℝ) ≤ (X.winA.card : ℝ) := Nat.cast_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h1 hcard
  have h4 := mul_le_mul_of_nonneg_left h2 hcard
  nlinarith [hwin, h3, h4]

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def preF (j : Fin G.T.t → ℕ) (jp : ℕ) : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
  (∏ i, G.Ehat p (r := r) i ^ j i) * G.Eplus p (r := r) ^ jp *
    (∏ i, X (Formalism.GM.M.scalZ N r G.T.t (Fin.castSucc i)) ^ G.T.z i) * X (Formalism.GM.M.scalZ N r G.T.t (Fin.last G.T.t)) ^ G.zPlus

theorem lvlDim_gen (j : Fin G.T.t → ℕ) (jp : ℕ) (hpre : preF (p := p) (r := r) G j jp ≠ 0)
    (hden : ∀ y ∈ Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∃ c : ℤ_[p], c ≠ 0 ∧
      ((c : ℚ_[p]) • y) ∈ Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr)
    (hfd : FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) j jp)))
    (hM : ∀ β ∈ xiMons (r := r) G (G.B - jp), ∀ x, β (Formalism.GM.M.chainEmb N r G.T.t x) = 0)
    (hxi : ∀ β ∈ xiMons (r := r) G (G.B - jp), (monomial β (1 : ℚ_[p])) ∈ Formalism.GM.M.XiPolZ p N r G.T.t (G.B - jp)) :
    dimY p (r := r) G j jp * dXi r (G.B - jp) ≤
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) j jp)) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  have : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) :=
    Formalism.CountingSumsFrames.pol_finiteDimensional (p := p) (G.lettersAt j jp)
  have : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le (inf_le_left)
  let b := Module.finBasis ℚ_[p] Yq
  choose c hc0 hcY using fun a => hden (b a) (b a).2
  have hc0' : ∀ a, (c a : ℚ_[p]) ≠ 0 := fun a h => hc0 a (PadicInt.coe_eq_zero.1 h)
  let w : Fin (Module.finrank ℚ_[p] Yq) → ℚ_[p]ˣ := fun a => Units.mk0 _ (hc0' a)
  have hb0 : LinearIndependent ℚ_[p] (fun a => ((b a : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) :=
    b.linearIndependent.map' Yq.subtype (Submodule.ker_subtype _)
  have hb' : LinearIndependent ℚ_[p] (fun a => (c a : ℚ_[p]) • ((b a : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) :=
    hb0.units_smul w
  have hinj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
    intro x y h
    simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Prod.ext (Fin.castSucc_injective _ h.1) h.2
  have hli := li_mul_left (preF (p := p) (r := r) G j jp) hpre _
    (li_rename_mon (Formalism.GM.M.chainEmb N r G.T.t) hinj (xiMons (r := r) G (G.B - jp)) hM _ hb')
  have hmem : ∀ q : (Σ _ : xiMons (r := r) G (G.B - jp), Fin (Module.finrank ℚ_[p] Yq)),
      preF (p := p) (r := r) G j jp * (rename (Formalism.GM.M.chainEmb N r G.T.t)
        ((c q.2 : ℚ_[p]) • ((b q.2 : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) * monomial (q.1 : _ →₀ ℕ) 1) ∈
        G.gens p (r := r) j jp := by
    intro q
    refine ⟨_, hcY q.2, monomial (q.1 : _ →₀ ℕ) 1, hxi _ q.1.2, ?_⟩
    unfold preF
    ring
  let v : (Σ _ : xiMons (r := r) G (G.B - jp), Fin (Module.finrank ℚ_[p] Yq)) →
      Submodule.span ℚ_[p] (G.gens p (r := r) j jp) := fun q => ⟨_, Submodule.subset_span (hmem q)⟩
  have hv : LinearIndependent ℚ_[p] v := LinearIndependent.of_comp (Submodule.subtype _) hli
  have hcard := hv.fintype_card_le_finrank
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe] at hcard
  rw [card_xiMons_eq] at hcard
  unfold dimY
  rw [mul_comm]
  exact hcard

end Gen

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
