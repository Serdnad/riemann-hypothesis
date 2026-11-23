module

import Development.EtaleCohomology.CyclotomicDiscriminants.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.ActUPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelLCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardEQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelInvLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace UpperTheory.V.ZK

private def gz (q e : ℕ) (j : Fin (e + 1) → ZMod q) : Fin (2 * e + 1 + 1) → Cq q :=
  fun i => if (i : ℕ) % 2 = 0 then Multiplicative.ofAdd (j ⟨i / 2, by omega⟩) else Multiplicative.ofAdd 1

private theorem sum_pair {M : Type} [AddCommGroup M] (f : ℕ → M) (n : ℕ)
    (h : ∀ t < n, f (2 * t) + f (2 * t + 1) = 0) : ∑ s ∈ Finset.range (2 * n), f s = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc,
      h n (by omega), ih fun t ht => h t (by omega), add_zero]

private theorem first_face (q : ℕ) [NeZero q] (e : ℕ) :
    ∑ j : Fin (e + 1) → ZMod q,
      (Finsupp.single (fun i : Fin (2 * e + 1) => gz q e j i.succ) 1 : Ch (ZMod q) (Cq q) (2 * e + 1)) = 0 := by
  rw [← (Fin.consEquiv fun _ : Fin (e + 1) => ZMod q).sum_comp, Fintype.sum_prod_type]
  have h : ∀ (a : ZMod q) (j : Fin e → ZMod q),
      (fun i : Fin (2 * e + 1) => gz q e ((Fin.consEquiv fun _ : Fin (e + 1) => ZMod q) (a, j)) i.succ) =
        fun i : Fin (2 * e + 1) => gz q e (Fin.cons 0 j) i.succ := by
    intro a j
    funext i
    unfold gz
    split_ifs with hi
    · have hi' : ((i : ℕ) + 1) % 2 = 0 := hi
      have : (⟨(i.succ : ℕ) / 2, by omega⟩ : Fin (e + 1)) = Fin.succ ⟨(i : ℕ) / 2, by omega⟩ := by
        ext; simp; omega
      rw [this]; rfl
    · rfl
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]

private theorem merge (q e t : ℕ) (ht : t < e + 1) (j : Fin (e + 1) → ZMod q) :
    Fin.contractNth (⟨2 * t, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (gz q e j) =
      Fin.contractNth (⟨2 * t + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·)
        (gz q e (j + fun i : Fin (e + 1) => if (i : ℕ) = t then 1 else if (i : ℕ) = t + 1 then -1 else 0)) := by
  funext k
  rcases lt_trichotomy (k : ℕ) (2 * t) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    simp only [gz, Fin.val_castSucc, Pi.add_apply]
    rw [if_neg (show ¬ (k : ℕ) / 2 = t by omega), if_neg (show ¬ (k : ℕ) / 2 = t + 1 by omega), add_zero]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    simp only [gz, Fin.val_castSucc, Fin.val_succ, Pi.add_apply]
    rw [if_pos (show (k : ℕ) % 2 = 0 by omega), if_pos (show (k : ℕ) % 2 = 0 by omega),
      if_neg (show ¬ ((k : ℕ) + 1) % 2 = 0 by omega), if_pos (show (k : ℕ) / 2 = t by omega), ofAdd_add]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ h'.symm]
      simp only [gz, Fin.val_castSucc, Fin.val_succ, Pi.add_apply]
      rw [if_pos (show ((k : ℕ) + 1) % 2 = 0 by omega), if_pos (show ((k : ℕ) + 1) % 2 = 0 by omega),
        if_neg (show ¬ (k : ℕ) % 2 = 0 by omega), if_neg (show ¬ ((k : ℕ) + 1) / 2 = t by omega),
        if_pos (show ((k : ℕ) + 1) / 2 = t + 1 by omega), ← ofAdd_add]
      congr 1
      ring
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ h']
      simp only [gz, Fin.val_succ, Pi.add_apply]
      have h'' : 2 * t + 1 < (k : ℕ) := h'
      by_cases h1 : ((k : ℕ) + 1) % 2 = 0
      · rw [if_neg (show ¬ ((k : ℕ) + 1) / 2 = t by omega), if_neg (show ¬ ((k : ℕ) + 1) / 2 = t + 1 by omega), add_zero]
      · rw [if_neg h1, if_neg h1]

theorem sZc : SZc := by
  apply LateralTheory.Q.SZcT.SZc_of <;> assumption

end UpperTheory.V.ZK

end
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

namespace UpperTheory.V.ZK

section

variable {k : Type} [Field k] {A : Type} [CommRing A] {m : ℕ} {θ : Fam k A (m + 1)} {G : Type} [Group G]

private theorem cyc_cm {H : Type} [Group H] (f : G →* H) {z : Ch A G (m + 1)} (hz : Cyc z) :
    Cyc (cm A f (m + 1) z) := by
  unfold Cyc at *
  rw [(sChain A).2.1, hz, map_zero]

private theorem bd_cm {H : Type} [Group H] (f : G →* H) {z : Ch A G (m + 1)} (hz : Bd z) :
    Bd (cm A f (m + 1) z) := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨cm A f _ y, (sChain A).2.1 _ _ _ _ _⟩

private theorem val_iso (h : IsAdd θ) {V W : Type} [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup W]
    [Module k W] [Finite W] (σ : G →* (W ≃ₗ[k] W)) (ρ : G →* (V ≃ₗ[k] V)) (φ : W ≃ₗ[k] V)
    (hφ : ∀ g w, φ (σ g w) = ρ g (φ w)) {z : Ch A G (m + 1)} (hz : Cyc z) :
    θ W (cm A σ (m + 1) z) = θ V (cm A ρ (m + 1) z) := by
  have e : ρ = (cj φ).comp σ := by
    ext g v
    simp [cj, hφ]
  rw [e, (sChain A).2.2.1, h.iso _ _ φ _ (cyc_cm σ hz)]

private theorem val_one (h : IsAdd θ) {V : Type} [AddCommGroup V] [Module k V] [Finite V]
    {z : Ch A G (m + 1)} (hz : Cyc z) : θ V (cm A (1 : G →* (V ≃ₗ[k] V)) (m + 1) z) = 0 := by
  have h1 : (1 : G →* (V ≃ₗ[k] V)) = (1 : Unit →* (V ≃ₗ[k] V)).comp (1 : G →* Unit) := by
    ext g v
    rfl
  rw [h1, (sChain A).2.2.1 G Unit _ (1 : G →* Unit) (1 : Unit →* (V ≃ₗ[k] V)) (m + 1) z]
  apply h.bdry
  apply bd_cm
  exact (sChain A).2.2.2.2 Unit m _ (cyc_cm _ hz)

private def piRep {V : Type} [AddCommGroup V] [Module k V] (ρ : G →* (V ≃ₗ[k] V)) (d : ℕ) :
    G →* ((Fin d → V) ≃ₗ[k] (Fin d → V)) where
  toFun g := LinearEquiv.piCongrRight fun _ => ρ g
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

private theorem val_pi (h : IsAdd θ) {V : Type} [AddCommGroup V] [Module k V] [Finite V] (ρ : G →* (V ≃ₗ[k] V))
    {z : Ch A G (m + 1)} (hz : Cyc z) (d : ℕ) :
    θ (Fin d → V) (cm A (piRep ρ d) (m + 1) z) = (d : A) • θ V (cm A ρ (m + 1) z) := by
  induction d with
  | zero =>
    have h0 : piRep ρ 0 = 1 := by
      ext g f i
      exact i.elim0
    rw [h0, val_one h hz]
    simp
  | succ d ih =>
    let φ : (Fin (d + 1) → V) ≃ₗ[k] V × (Fin d → V) :=
      { toFun := fun f => (f 0, Fin.tail f)
        invFun := fun p => Fin.cons p.1 p.2
        map_add' := fun f g => rfl
        map_smul' := fun c f => rfl
        left_inv := fun f => Fin.cons_self_tail f
        right_inv := fun p => by simp }
    have hφ : ∀ g w, φ (piRep ρ (d + 1) g w) = sumRep ρ (piRep ρ d) g (φ w) := by
      intro g w
      rfl
    rw [val_iso h (piRep ρ (d + 1)) (sumRep ρ (piRep ρ d)) φ hφ hz,
      h.add G V (Fin d → V) ρ (piRep ρ d) z hz, ih]
    push_cast
    rw [add_smul, one_smul, add_comm]

end

private theorem red_apply {k : Type} [Field k] {R : Type} [CommRing R] (r : R →+* k) (n : ℕ) (g : GL (Fin n) R)
    (v : Fin n → k) (i : Fin n) :
    red r n g v i = ∑ j, r ((g : Matrix (Fin n) (Fin n) R) i j) * v j := by
  simp [red, Matrix.mulVec, dotProduct]

end UpperTheory.V.ZK

theorem UpperTheory.V.ZK.sPhi :
    UpperTheory.V.ZK.SPhi := by
  intro k _ _ A _ m θ hθ R _ r
  have hcomp : ∀ {n n' : ℕ} (f : GL (Fin n) R →* GL (Fin n') R) (z : Ch A (GL (Fin n) R) (m + 1)),
      cm A (red r n') (m + 1) (cm A f (m + 1) z) = cm A ((red r n').comp f) (m + 1) z :=
    fun f z => ((sChain A).2.2.1 _ _ _ f (red r _) (m + 1) z).symm
  refine ⟨fun n z hz => ?_, fun n n' hn z hz => ?_, fun d n z hz => ?_⟩
  · exact hθ.bdry _ _ (bd_cm _ hz)
  · simp only [LinearMap.comp_apply]
    rw [hcomp]
    let φ : (Fin n' → k) ≃ₗ[k] (Fin n → k) × (Fin (n' - n) → k) :=
      { toFun := fun f => (fun i => f (Fin.castLE hn i), fun j => f ⟨n + j, by omega⟩)
        invFun := fun p i => if hi : (i : ℕ) < n then p.1 ⟨i, hi⟩ else p.2 ⟨i - n, by omega⟩
        map_add' := fun f g => rfl
        map_smul' := fun c f => rfl
        left_inv := fun f => by
          funext i
          by_cases hi : (i : ℕ) < n
          · simp [hi]
          · simp only [hi, dite_false]
            congr 1
            ext
            simp
            omega
        right_inv := fun p => by
          refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
          · simp
          · simp }
    have hφ : ∀ g w, φ (((red r n').comp (stab R n n' hn)) g w) =
        sumRep (red r n) (1 : GL (Fin n) R →* ((Fin (n' - n) → k) ≃ₗ[k] (Fin (n' - n) → k))) g (φ w) := by
      intro g w
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · simp [φ, sumRep, red_apply, stab_apply]
        symm
        refine Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ ?_ ?_
        · intro x hx
          have hxn : ¬ (x : ℕ) < n := fun h => hx ⟨⟨x, h⟩, Fin.ext rfl⟩
          have hne : Fin.castLE hn i ≠ x := fun h => hxn (h ▸ i.isLt)
          simp [hxn, hne]
        · intro j
          simp
      · simp [φ, sumRep, red_apply, stab_apply]
    rw [val_iso hθ _ _ φ hφ hz, hθ.add _ _ _ _ _ z hz, val_one hθ hz, add_zero]
  · simp only [LinearMap.comp_apply]
    rw [hcomp, ← val_pi hθ (red r n) hz d]
    have h1 : ∀ x : Fin d × Fin n, (finProdFinEquiv x).divNat = x.1 ∧ (finProdFinEquiv x).modNat = x.2 :=
      fun x => by
        have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) x.2.isLt
        refine ⟨Fin.ext ?_, Fin.ext ?_⟩
        · simp only [finProdFinEquiv, Fin.divNat, Equiv.coe_fn_mk]
          rw [Nat.add_mul_div_left _ _ hn0, Nat.div_eq_of_lt x.2.isLt, zero_add]
        · simp [finProdFinEquiv, Fin.modNat, Nat.mod_eq_of_lt]
    let φ : (Fin d → Fin n → k) ≃ₗ[k] (Fin (d * n) → k) :=
      { toFun := fun f p => f (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
        invFun := fun g i a => g (finProdFinEquiv (i, a))
        map_add' := fun f g => rfl
        map_smul' := fun c f => rfl
        left_inv := fun f => by
          funext i a
          simp
        right_inv := fun g => by
          funext p
          show g (finProdFinEquiv ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2)) = g p
          rw [Prod.mk.eta, Equiv.apply_symm_apply] }
    have hφ : ∀ g w, φ (piRep (red r n) d g w) = ((red r (d * n)).comp (psi R d n)) g (φ w) := by
      intro g w
      funext p
      obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective p
      simp [φ, piRep, red_apply, psi, h1]
      rw [← finProdFinEquiv.sum_comp]
      simp [h1, Fintype.sum_prod_type, Matrix.one_apply]
      done
    exact (val_iso hθ _ _ φ hφ hz).symm
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

theorem UpperTheory.V.ZK.sCount :
    UpperTheory.V.ZK.SCount := by
  intro L F _ _ _ _ _ hTC l c ν E b B _ ζ γ hL hE hF
  have hl : l.Prime := Fact.out
  obtain ⟨ha2, hfa, hfN⟩ := Ct.lte l c ν E hl hL.c_pos hL.c_two hL.c_le hE
  generalize (1 + l ^ c) ^ E = a at *
  obtain ⟨D, hD⟩ := Ct.datEx L F γ a ha2
  have hDa := hD.a_eq
  have hDn := hD.n_eq
  have hI := Ct.clFin L F γ a D hD
  obtain ⟨hEQf, hEQc⟩ := Ct.cardEQ L F γ a D hTC hL.gal hL.gen hD
  obtain ⟨hClf, hWf, hWc⟩ := Ct.cardW _ _ D hI hEQf
  obtain ⟨hEHf, hEHc⟩ := Ct.eqHomLe L F γ a l ν D hl hD hClf
  refine ⟨hEHf, ?_⟩
  have hlpow : l ^ (ν - c) ≠ 0 := (pow_pos hl.pos _).ne'
  have hbig : 2 ≤ a ^ l ^ (ν - c) := le_trans ha2 (Nat.le_self_pow hlpow a)
  have hN0 : a ^ l ^ (ν - c) - 1 ≠ 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = ordCompl[l] (a ^ l ^ (ν - c) - 1) := ⟨_, rfl⟩
  have hNm : a ^ l ^ (ν - c) - 1 = l ^ (ν + E.factorization l) * m := by
    have h0 := Nat.ordProj_mul_ordCompl_eq_self (a ^ l ^ (ν - c) - 1) l
    rw [← hm, hfN] at h0
    exact h0.symm
  have hmd : ¬ l ∣ m := by
    rw [hm]
    exact Nat.not_dvd_ordCompl hl hN0
  have hker : ((D.a : ℤ)) ^ D.n - 1 = ((l ^ ν : ℕ) : ℤ) * ((l ^ E.factorization l * m : ℕ) : ℤ) := by
    rw [hDa, hDn, hL.ord]
    have h1 : 1 ≤ a ^ l ^ (ν - c) := by omega
    have key : ((a ^ l ^ (ν - c) - 1 : ℕ) : ℤ) = (a : ℤ) ^ l ^ (ν - c) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [← key, hNm]
    push_cast
    ring
  obtain ⟨f, hfnm, hfk⟩ := Ct.kerF _ _ D (l ^ ν) (l ^ b) _ hker
  haveI := hWf
  haveI := hEQf
  haveI := hClf
  have hrange := Ct.fewLe L F γ a (l ^ b) (l ^ ν) B D hD hF f hfnm hWf
  obtain ⟨hSLf, hSLc⟩ := Ct.selLCard L l hl
  obtain ⟨hSIf, hSIc⟩ := Ct.selInvLe L F l c ν a ζ γ D hl hL hD hSLf
  have hdvd : (l : ℤ) ∣ (D.a : ℤ) - 1 := by
    rw [hDa]
    have hc1 := hL.c_pos
    have hd : l ∣ a - 1 := Nat.dvd_of_factorization_pos (by rw [hfa]; omega)
    have h1 : 1 ≤ a := by omega
    have hd' := Int.natCast_dvd_natCast.mpr hd
    rw [Nat.cast_sub h1] at hd'
    simpa using hd'
  have htor := Ct.selInj _ _ D l hdvd hl.pos hSIf
  have hg : Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ l ^ gens L := by
    refine htor.trans (hSIc.trans ((Nat.mul_le_mul_right _ hSLc).trans (le_of_eq ?_)))
    unfold gens
    rw [← pow_add]
  have hp := Ct.pCount D.W _ f l (b + E.factorization l) (gens L) (m : ℤ) hl
    (by exact_mod_cast hmd)
    (by
      intro w hw
      have h0 := hfk w hw
      convert h0 using 2
      push_cast
      ring) hg
  have hEQ0 : Nat.card D.EQ ≠ 0 := Nat.card_pos.ne'
  have hCl0 : Nat.card D.ClQ ≠ 0 := Nat.card_pos.ne'
  have hfW : (Nat.card D.W).factorization l =
      (Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l := by
    rw [hWc, Nat.factorization_mul hEQ0 hCl0, Finsupp.add_apply]
  have hfEQ : (Nat.card D.EQ).factorization l + (c + E.factorization l) =
      InfinitePlace.nrComplexPlaces L * (ν + E.factorization l) := by
    have h0 := congrArg (fun n => n.factorization l) hEQc
    have ha1 : a - 1 ≠ 0 := by omega
    rw [Nat.factorization_mul hEQ0 ha1, Finsupp.add_apply, hfa, hL.ord, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul, hfN] at h0
    exact h0
  calc Nat.card ↑(EqHom γ a (l ^ ν)) * (l ^ ν) ^ InfinitePlace.nrComplexPlaces L
      ≤ l ^ (Nat.card D.ClQ).factorization l *
          l ^ ((Nat.card D.EQ).factorization l + (c + E.factorization l)) := by
        refine Nat.mul_le_mul hEHc ?_
        rw [← pow_mul]
        refine Nat.pow_le_pow_right hl.pos ?_
        rw [hfEQ, mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    _ = l ^ ((Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l) *
          l ^ (c + E.factorization l) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
    _ ≤ (Nat.card ↥f.range * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [← hfW]
        exact hp
    _ ≤ (B * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hrange)
    _ = B * l ^ ((b + E.factorization l) * gens L + c + E.factorization l) := by
        rw [mul_assoc, ← pow_add, add_assoc]
end
