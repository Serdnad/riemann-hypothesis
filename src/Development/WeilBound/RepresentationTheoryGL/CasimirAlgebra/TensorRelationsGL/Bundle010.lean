module

import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlgA
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGKA
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle008
public import Mathlib.CategoryTheory.Category.Basic
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PKTypeA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def reIx {P Q : Type} (e : P ≃ Q) (ξ : TV n M P) : TV n M Q := fun I => ξ (I ∘ e)

def unc {A B : Type} (f : TV n (TV n M A) B) : TV n M (A ⊕ B) := fun I => f (I ∘ Sum.inr) (I ∘ Sum.inl)

def cur {A B : Type} (g : TV n M (A ⊕ B)) : TV n (TV n M A) B := fun J K => g (Sum.elim K J)

theorem unc_cur {A B : Type} (g : TV n M (A ⊕ B)) : unc (cur g) = g := by
  funext I
  simp only [unc, cur, Sum.elim_comp_inl_inr]

theorem unc_inj {A B : Type} {f g : TV n (TV n M A) B} (h : unc f = unc g) : f = g := by
  funext J K
  have := congrFun h (Sum.elim K J)
  simpa [unc] using this

theorem unc_smul {A B : Type} (c : ℂ) (f : TV n (TV n M A) B) : unc (c • f) = c • unc f := rfl

theorem reIx_smul {P Q : Type} (e : P ≃ Q) (c : ℂ) (ξ : TV n M P) : reIx e (c • ξ) = c • reIx e ξ := rfl

theorem actT_reIx {ι Γ P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] (e : P ≃ Q)
    (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (ξ : TV n M P) :
    actT (lab ∘ e.symm) κ ρ γ (reIx e ξ) = reIx e (actT lab κ ρ γ ξ) := by
  funext I
  simp only [actT, reIx, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply]
  symm
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl (Fin n))) _ _ (fun J => ?_)
  have hJ : (e.arrowCongr (Equiv.refl (Fin n)) J) ∘ e = J := by
    funext p
    simp [Equiv.arrowCongr_apply]
  rw [hJ]
  congr 1
  refine Fintype.prod_equiv e _ _ (fun p => ?_)
  simp [Equiv.arrowCongr_apply]

theorem actT_unc {ι Γ A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (la : A → ι) (lb : B → ι)
    (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (f : TV n (TV n M A) B) :
    actT (Sum.elim la lb) κ ρ γ (unc f) = unc (actT lb κ (actT la κ ρ) γ f) := by
  funext I
  simp only [actT, unc, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply, Finset.sum_apply, Pi.smul_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.sumArrowEquivProdArrow A B (Fin n)).trans (Equiv.prodComm _ _)) _ _ (fun d => ?_)
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [mul_comm]
  rfl

def splitE (m n : ℕ) (h : n ≤ m) : Fin m ≃ Fin (m - n) ⊕ Fin n where
  toFun i := if hi : (i : ℕ) < n then Sum.inr ⟨i, hi⟩ else Sum.inl ⟨i - n, by omega⟩
  invFun := Sum.elim (fun j => ⟨j + n, by omega⟩) (fun j => ⟨j, by omega⟩)
  left_inv i := by
    by_cases hi : (i : ℕ) < n
    · simp [hi]
    · simp only [hi, dite_false, Sum.elim_inl]
      ext; simp; omega
  right_inv x := by
    rcases x with j | j
    · simp
    · simp [j.2]

theorem pm_alt_firstG {m k : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ firstG m k) (x : TV n M (Fin m)) :
    pm τ (alt (firstG m k) x) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • alt (firstG m k) x := by
  apply PositivityTheory.Rg.Cz.WallAlgP.pm_alt_first <;> assumption

theorem cur_anti {m : ℕ} (h : n ≤ m) (η : TV n M (Fin m))
    (hη : ∀ τ ∈ firstG m n, pm τ η = ((Equiv.Perm.sign τ : ℤ) : ℂ) • η) (σ : Equiv.Perm (Fin n)) :
    pm σ (cur (reIx (splitE m n h) η)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) • cur (reIx (splitE m n h) η) := by
  funext J K
  set e := splitE m n h with he
  let S : Equiv.Perm (Fin (m - n) ⊕ Fin n) := Equiv.sumCongr (Equiv.refl _) σ
  let τ : Equiv.Perm (Fin m) := (e.trans S).trans e.symm
  have hτ : τ ∈ firstG m n := by
    simp only [firstG, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    have hj' : ¬ (j : ℕ) < n := by omega
    have ha : e j = Sum.inl ⟨(j : ℕ) - n, by omega⟩ := by
      simp [he, splitE, hj']
    show e.symm (S (e j)) = j
    rw [ha]
    exact e.symm_apply_eq.2 ha.symm
  have hs : Equiv.Perm.sign τ = Equiv.Perm.sign σ := by
    show Equiv.Perm.sign ((e.symm.symm.trans S).trans e.symm) = _
    rw [Equiv.Perm.sign_symm_trans_trans]
    simp [S, Equiv.Perm.sign_sumCongr]
  have key := congrFun (hη τ hτ) (Sum.elim K J ∘ e)
  simp only [pm, LinearMap.pi_apply, LinearMap.proj_apply, Pi.smul_apply] at key
  simp only [pm, cur, reIx, LinearMap.pi_apply, LinearMap.proj_apply, Pi.smul_apply]
  rw [← hs, ← key]
  congr 1
  funext x
  simp only [Function.comp_apply, τ, Equiv.trans_apply, Equiv.apply_symm_apply, S,
    Equiv.sumCongr_apply, Equiv.refl_apply]
  cases e x <;> rfl

end PositivityTheory.Rg.Cz.CtrX

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)

def labR : {p // ¬ lab p = τ₀} → {τ // τ ≠ τ₀} := fun p => ⟨lab p.1, p.2⟩

theorem conj_tensor_entry_base (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (tE Finset.univ (fun a b => lift (F a b)) c d) =
      tE (fib lab τ₀) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ₀) = Finset.univ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ₀) = ∅ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

theorem conj_tensor_entry_fibre (τ : {τ // τ ≠ τ₀}) (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (lift (tE (fib (labR lab τ₀) τ) F c d)) =
      tE (fib lab τ.1) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ.1) = ∅ := by
    ext x
    simp only [Finset.mem_subtype, fib, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rw [x.2]
    exact fun h => τ.2 h.symm
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ.1) = fib (labR lab τ₀) τ := by
    ext x
    simp [fib, labR, Finset.mem_subtype, Subtype.ext_iff]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

omit [DecidableEq P] in
theorem card_R (τ : {τ // τ ≠ τ₀}) (co : P → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : {p // ¬ lab p = τ₀} => labR lab τ₀ p = τ ∧ co p.1 = k).card =
      (Finset.univ.filter fun p => lab p = τ.1 ∧ co p = k).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff] at hp ⊢
    exact hp
  · intro p _ q _ h
    exact Subtype.ext h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨⟨p, fun h => τ.2 (hp.1.symm.trans h)⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff]
    exact hp

omit [Fintype P] in
theorem base (E : ι → Fin n → Fin n → Module.End ℂ M) (l : ι → Fin n → ℤ)
    (hl : ∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) [Fintype P] [IsEmpty P]
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin n) :
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) •
          (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have hfib : ∀ τ, fib lab τ = ∅ := fun τ => Finset.eq_empty_of_isEmpty _
  have hG : colG col = {1} := by
    ext σ
    simp [colG, Subsingleton.elim σ 1]
  obtain ⟨m, hm⟩ : ∃ m, ℓ m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, ?_, ?_⟩
  · intro h
    apply hm
    have := LinearMap.congr_fun h (fun _ => m)
    simpa [cA, alt, hG, pm] using this
  · intro τ u
    have hc := qdet_lift (P := P) (E τ) (fun k => (l τ k : ℂ)) (hl τ) u
    simp only [hfib, tE_empty]
    rw [hc, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul]
    simp
    rfl

end PositivityTheory.Rg.Cz.TA

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

theorem tensorGK_of : TensorGl → TensorGK := by
  intro hT n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hE P _ _ lab
  refine ⟨⟨fun τ => (hT n M P (E τ) (hE.gl τ) (fib lab τ)).1, fun τ τ' h a b c d => TGK.tE_comm E hE.comm lab τ τ' h a b c d,
    TGK.actT_one lab κ ρ hK.one hE.one, TGK.actT_mul lab κ ρ hK.mul hE.mul,
    fun γ τ a b => TGK.actT_ad lab κ E ρ hK.unit hE.ad γ τ a b, fun y => TGK.actT_fin lab κ ρ hE.fin y,
    fun y lam => TGK.actT_cont lab κ ρ hK.cont hE.cont y lam, ?_⟩,
    fun σ hσ γ => TGK.pm_actT lab κ ρ σ hσ γ⟩
  intro τ X hX
  obtain ⟨c, hc0, hd, hoth, hρ⟩ := hE.der τ X hX
  exact ⟨c, hc0, hd, hoth, fun y lam => TGK.actT_der lab κ E ρ bar τ (hK.ne τ) hE.one hK.one hK.conj X c hc0 hd hoth
    hρ y lam⟩

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

open KTy in
theorem kType_of : TensorGl → TransAll → TensorGK → SphAll → Young → KType := by
  intro hGl hTr hGK hSph hY n hn M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG l hl hc ℓ hℓ hW
  obtain ⟨s, w, nu, hnu, hm⟩ := sort_data l hl
  obtain ⟨H, hH⟩ := half bar hK.invol hK.ne
  set lab := lab3 bar (labQ nu) (tl H) with hlab
  have hlabcol : ∀ p q, colF nu H p = colF nu H q → lab p = lab q := fun p q h => colF_lab nu H bar p q h
  have htab := isTabF nu H hm
  let co : Pos nu H → Fin n := fun p => w (lab p) (bF nu H p)
  have hco : ∀ p q, colF nu H p = colF nu H q → co p = co q → p = q := by
    intro p q h h'
    refine htab.1 p q h ?_
    simp only [co, hlabcol p q h] at h'
    exact (w (lab q)).injective h'
  obtain ⟨S, hSA, hS0, hSe⟩ := hTr n M ι E hG.gl hG.comm l hc ℓ hℓ hW (Pos nu H) lab (Col ι n) (colF nu H) (bF nu H)
    co hlabcol htab hco
  have hGK' := hGK n M ι Γ bar κ E ρ hK hG (Pos nu H) lab
  have heig : ∀ τ (u : ℂ), (ℓ ∘ₗ cA (colF nu H) (bF nu H) ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
      ((u + (s : ℂ)) ^ n) • (ℓ ∘ₗ cA (colF nu H) (bF nu H) ∘ₗ S) := by
    intro τ u
    rw [hSe τ u]
    congr 1
    rw [← Fin.prod_const n (u + (s : ℂ))]
    refine Finset.prod_congr rfl fun k _ => ?_
    have e1 : (Finset.univ.filter fun p => lab p = τ ∧ co p = k) =
        Finset.univ.filter fun p => lab p = τ ∧ bF nu H p = (w τ).symm k := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, co]
      constructor
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [← h2, h1]; simp
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [h2, h1]; simp
    have e2 : (Finset.univ.filter fun p => lab p = τ ∧ bF nu H p = (w τ).symm k).card =
        nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) := cntF nu H bar hK.invol hH τ ((w τ).symm k)
    have e3 := hnu τ ((w τ).symm k)
    rw [Equiv.apply_symm_apply] at e3
    rw [e1, e2]
    have e4 : ((nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) : ℕ) : ℤ) = s - l τ k := by push_cast; linarith
    have e5 : ((nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) : ℕ) : ℂ) = (s : ℂ) - (l τ k : ℂ) := by exact_mod_cast e4
    rw [e5]; ring
  obtain ⟨ξ, hξ, w', hw', hφ⟩ := hSph n hn (TV n M (Pos nu H)) ι Γ bar κ (fun τ => tE (fib lab τ) (E τ))
    (actT lab κ ρ) hK hGK'.1 s _ hS0 heig
  have hcomm : ∀ σ : Equiv.Perm (Pos nu H), (∀ p, lab (σ p) = lab p) →
      ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (pm σ) x := by
    intro σ hσ x hx
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_
    rintro _ ⟨τ, a, b, rfl⟩
    exact (hGl n M (Pos nu H) (E τ) (hG.gl τ) (fib lab τ)).2.2.1 σ (by intro p; simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, hσ]) a b
  have hGc : ∀ σ ∈ colG (colF nu H), ∀ p, lab (σ p) = lab p := by
    intro σ hσ p
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact hlabcol _ _ (hσ p)
  have hPc : ∀ σ ∈ colG (tl H), ∀ p, lab (dbl (Q := Fin (Fintype.card (Bx nu))) σ p) = lab p := by
    intro σ hσ p
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rcases p with p | k | k <;> simp [dbl, hlab, lab3, hσ]
  have hA1 : ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (alt (colG (colF nu H))) x := fun x hx =>
    alt_comm _ _ fun σ hσ => hcomm σ (hGc σ hσ) x hx
  have hA2 : ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (altPair (Q := Fin (Fintype.card (Bx nu))) (tl H)) x := by
    intro x hx
    unfold altPair
    exact Commute.sum_left _ _ _ fun σ hσ => (hcomm _ (hPc σ hσ) x hx).smul_left _
  refine ⟨s, Fintype.card (Bx nu), Fintype.card (Pr H n), labQ nu, colQ nu, bQ nu, tl H,
    alt (colG (colF nu H)) ξ, ?_, isTabQ nu hm, ?_, ?_, ?_, ?_, ?_⟩
  · intro p p' h
    exact hlabcol (.inl p) (.inl p') (by simp [colF, h])
  · intro k k' h
    have h1 := (eP H n k).1.2
    have h2 := (hH (tl H k')).1 (eP H n k').1.2
    exact h2 (by rw [← h]; exact h1)
  · intro τ
    refine ⟨w τ, fun i => ?_⟩
    rw [cntQ, hnu]; ring
  · intro γ
    have := alt_comm (colG (colF nu H)) (actT lab κ ρ γ) fun σ hσ => hGK'.2 σ (hGc σ hσ) γ
    show actT lab κ ρ γ (alt _ ξ) = _
    rw [← Module.End.mul_apply, ← this.eq, Module.End.mul_apply, hξ]
  · intro p p' h hne
    have e := pm_mul_alt (M := M) (n := n) (colG (colF nu H)) (Equiv.swap (Sum.inl p) (Sum.inl p')) ?_
    · rw [← Module.End.mul_apply, e, Equiv.Perm.sign_swap (by simpa using hne)]
      simp
    · intro σ
      simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
      have hs : ∀ x, colF nu H (Equiv.swap (Sum.inl p) (Sum.inl p') x) = colF nu H x := by
        intro x
        rcases eq_or_ne x (.inl p) with rfl | h1
        · simp [colF, h]
        rcases eq_or_ne x (.inl p') with rfl | h2
        · simp [colF, h]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [hs]
  · intro h0
    apply hφ
    have e : altPair (tl H) (alt (colG (colF nu H)) (S (w' ξ))) =
        S (w' (altPair (tl H) (alt (colG (colF nu H)) ξ))) := by
      rw [← Module.End.mul_apply (alt _) S, (hA1 S hSA).eq, Module.End.mul_apply,
        ← Module.End.mul_apply (alt _) w', (hA1 w' hw').eq, Module.End.mul_apply,
        ← Module.End.mul_apply (altPair _) S, (hA2 S hSA).eq, Module.End.mul_apply,
        ← Module.End.mul_apply (altPair _) w', (hA2 w' hw').eq, Module.End.mul_apply]
    have hy := hY n M ι (Fin (Fintype.card (Bx nu))) (Fintype.card (Pr H n)) (tl H) (Col ι n) (colF nu H) (bF nu H) htab
      (fun p k => by rcases k with k | k <;> simp [colF]) (fun k k' => by simp [colF])
      (fun k k' => by simp [colF, bF, Prod.ext_iff]) (fun k k' => by simp [colF, bF, Prod.ext_iff])
      (S (w' ξ)) (by rw [e, h0]; simp)
    simp [hy]

end PositivityTheory.Rg.Cz

end
end
