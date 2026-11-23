module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopTargetGen

open GlobalTheory.DatumLaw

section General

theorem coarse_rep {r t m i : ℕ} (ht : 0 < t) (h1 : r ≤ i) (h2 : i < r + m * t) :
    coarse r (List.replicate m t) i = (i - r) / t + 1 := by
  rw [coarse_of_le h1, blkIdx_replicate ht _ _ (by omega)]

theorem supSum_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (M : Matrix (Fin n) (Fin n) κ) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = M i j) :
    supSum r (Finset.range (r - 1)) M = ∑ i ∈ Finset.range (r - 1), A i (i + 1) := by
  unfold supSum
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < r ∧ i.val ∈ Finset.range (r - 1) then M i j else 0) =
      if i.1 < r - 1 then A i.1 (i.1 + 1) else 0 := fun i => by
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨i.1 + 1, by omega⟩ : Fin n), if_pos ⟨rfl, by simp only; omega, Finset.mem_range.2 h⟩, ← hA]
      · intro j _ hj
        exact if_neg fun h' => hj (Fin.ext h'.1.symm)
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · exact Finset.sum_eq_zero fun j _ => if_neg fun h' => h (Finset.mem_range.1 h'.2.2)
  rw [Finset.sum_congr rfl fun i _ => h1 i,
    Fin.sum_univ_eq_sum_range (fun i => if i < r - 1 then A i (i + 1) else 0) n, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem lamJ_eq {κ K : Type} [CommRing κ] [Field K] (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n r t m : ℕ} (ht : 0 < t)
    (hn : n = r + m * t) (M : HJ κ n r t m) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) :
    ((lamJ ψ χ n r t m M : Kˣ) : K) = lamF ψ χ r r t m A := by
  unfold lamJ lamGen lamF
  rw [MonoidHom.mul_apply, Units.val_mul, supChar_val, supSum_eq (by omega) _ A hA, MonoidHom.comp_apply, detChar_apply,
    List.length_replicate, Units.coe_prod]
  congr 1
  · simp
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hb : r + s * t + t ≤ n := blk_le hs hn.ge
  rw [← GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t hb ?_
    (Subgroup.inclusion (uniUT_le_blockUT n κ r _) M) A hA]
  · unfold ext0
    rw [dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · intro i hi
    by_cases h : i < r
    · rw [coarse_of_lt h]
      omega
    · rw [coarse_rep ht (by omega) (by omega), Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem red_entB (k₀ : ℕ) {n : ℕ} (ex : ℕ → ℕ) (j : GLint E n P) (p p' : Fin n) :
    redP P (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0)) p.1 p'.1) =
      (redGL n P j : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) p p' := by
  rw [GlobalTheory.TopStep.entB_zero _ _ _ _ _ rfl, dif_pos ⟨p.2, p'.2⟩]
  rfl

theorem lamY_zero (n : ℕ) (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  ext v
  unfold LocE.lamY
  rw [LastSteps.mem_sclLat, mem_stdAt]
  refine forall_congr' fun l => ?_
  have : LocE.scE n ex l.1 = 0 := if_pos l.2
  rw [this, zpow_zero, inv_one, one_mul]

theorem int_entB (k₀ : ℕ) {n : ℕ} (ex : ℕ → ℕ) (j : GLint E n P) :
    IntM P (n + 0) (n + 0) (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0))) :=
  ent_int (n := n) (c := 0) (g := j.1) ((lamY_zero (E := E) (P := P) n ex).symm ▸ j.2)

theorem levG_of_mem (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (k₀ : ℕ) {n r t m : ℕ} (ht : 0 < t) (hn : n = r + m * t)
    (ex : ℕ → ℕ) (j : GLint E n P) (h : redGL n P j ∈ HJ (𝓞 E ⧸ P.asIdeal) n r t m) :
    LevG P r 0 r t (n + 0) (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0))) := by
  obtain ⟨h1, h2, h3⟩ := mem_uniUT.1 h
  have hb := mem_btG.1 h1
  have hr : r ≤ n := by omega
  refine ⟨int_entB k₀ ex j, fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun i p p' a1 a2 a3 => ?_⟩
  · exact (red_entB k₀ ex j ⟨p', by omega⟩ ⟨p', by omega⟩).trans (h3 _ hp')
  · refine (red_entB k₀ ex j ⟨p, hp⟩ ⟨p', by omega⟩).trans ?_
    by_cases hpr : p < r
    · refine h2 _ _ hpr ?_
      have e1 := SymLevelInv.symIdx_cases r 0 p
      have e2 := SymLevelInv.symIdx_cases r 0 p'
      unfold Zs at hz
      simp only
      omega
    · refine hb _ _ ?_
      simp only
      rw [coarse_of_lt hp', coarse_of_le (by omega)]
      omega
  · refine intAt_div_of_redP hq (int_entB k₀ ex j p p' a2 (by omega)) ?_
    refine (red_entB k₀ ex j ⟨p, a2⟩ ⟨p', by omega⟩).trans (hb _ _ ?_)
    simp only
    rw [coarse_rep ht (show r ≤ p by omega) (by omega)]
    by_cases hpr : p' < r
    · rw [coarse_of_lt hpr]
      exact Nat.succ_pos _
    · rw [coarse_rep ht (show r ≤ p' by omega) (by omega)]
      have b1 : (p' - r) / t < i := by
        rw [Nat.div_lt_iff_lt_mul ht]
        omega
      have b2 : i ≤ (p - r) / t := by
        rw [Nat.le_div_iff_mul_le ht]
        omega
      omega

theorem phiG_target (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ n r t m i c' n' : ℕ} (hm : m = i + 1) (hk : k₀ ≤ n) (ht : 0 < t)
    (hn : n = r + m * t) (j : GLint E n P) (h : redGL n P j ∈ HJ (𝓞 E ⧸ P.asIdeal) n r t m) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiG (qOf P) ψ χ false k₀ r t m c' n' 0 n ((j.1.toLinearMap : HomE E (n + 0) (n + 0)) ∘ₗ x) *
        LocE.unitV (χ i) ((LinearEquiv.det j.1 : Eˣ) : E) =
      ((lamJ ψ χ n r t m ⟨_, h⟩ : Kˣ) : K) * LocE.PhiG (qOf P) ψ χ false k₀ r t m c' n' 0 n x := by
  subst hm
  rw [phiG_eq, lamJ_eq ψ χ ht hn ⟨_, h⟩
    (red P (LocE.entB (qOf P) k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) (j.1.toLinearMap : HomE E (n + 0) (n + 0))))
    (red_entB k₀ (fun i => i + 1) j)]
  refine (phiM_target (c := 0) (k₁ := r) (rS := 0) (r := r) ψ χ hk le_rfl (by rw [hn]; ring)
    (((HJ (𝓞 E ⧸ P.asIdeal) n r t (i + 1)).comap (redGL n P)).map (GLint E n P).subtype) ?_ ?_ (g := j.1) ⟨j, h, rfl⟩ x).trans ?_
  · rintro _ ⟨g, -, rfl⟩
    rw [lamY_zero]
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact levG_of_mem hq k₀ ht hn _ g hg
  · rw [lamGvS_eq ψ χ le_rfl (int_entB k₀ _ j) hn.ge hn.ge]

end General

theorem phiTop_target_gen : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → ∀ (hP : P ∈ Pr.vGs) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyG Ch (rP0 Ch) ⟨P, hP⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu false m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyG Ch (rP0 Ch) ⟨P, hP⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu false m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP j h x
  have h' : redGL _ P j ∈ HJ (𝓞 X.E ⧸ P.asIdeal) (R.N R.m - 1) R.r R.t R.m := by
    have := rowLevel_unipotent_group Ch ⟨P, hP⟩
    rw [this] at h
    exact h
  have e1 : psi0P Ch P = Ch.psi0 ⟨P, hP⟩ := dif_pos hP
  have e2 : chiP Ch P = chiAt Ch ⟨P, hP⟩ := dif_pos hP
  have hk : R.k ≤ R.N R.m - 1 := by
    have := r_le_X' R
    have := (ranks R (j := 0) (by omega)).2.2.2
    omega
  rw [rowLevel_unipotent_character Ch ⟨P, hP⟩ _ h h']
  unfold PhiTop
  rw [if_pos hP, if_neg Bool.false_ne_true, e1, e2]
  exact phiG_target hq _ _ hm hk R.t_odd.pos (rank_X'_eq R) j h' x

end GlobalTheory.TopTargetGen
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopLawSym

open GlobalTheory.DatumLaw GlobalTheory.TwU

section Res

variable {κ K : Type} [CommRing κ] [Field K]

theorem sum_pred (n : ℕ) (f : ℕ → κ) (c : ℕ → Prop) [DecidablePred c] (h : ∀ p, p < n → (c p ↔ p + 1 < n)) :
    (∑ p ∈ Finset.range n, if c p then f p else 0) = ∑ p ∈ Finset.range (n - 1), f p := by
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    have := (h p h1).1 h2
    omega
  · intro h1
    exact ⟨by omega, (h p (by omega)).2 (by omega)⟩

theorem chiSymF_val (ψ : AddChar κ K) {r k rS : ℕ} (hr : k + rS ≤ r) (M : HPsymF κ r k rS) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin r, A i.1 j.1 = (M.1 : Matrix (Fin r) (Fin r) κ) i j) :
    ((chiSymF ψ r k rS M : Kˣ) : K) =
      ψ (∑ i ∈ Finset.range (k - 1), A i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), A (k + i) (k + i + 1)) := by
  have h0 : ((chiSymF ψ r k rS M : Kˣ) : K) =
      ψ (supSum r (SPsym r k rS) ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ)) *
        ψ (offSum k rS ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ)) := rfl
  rw [h0, ← AddChar.map_add_eq_mul]
  congr 1
  unfold supSum offSum
  rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (symPerm r k rS)]
  have h1 : ∀ p : Fin r, ((∑ j : Fin r, if (symPerm r k rS p).1 + 1 = j.1 ∧ j.1 < r ∧ (symPerm r k rS p).1 ∈ SPsym r k rS then
      ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) j else 0) +
      ∑ j : Fin r, if (symPerm r k rS p).1 + 1 = rS ∧ j.1 = rS + k then
      ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) j else 0) =
      if p.1 + 1 < r ∧ p.1 + 1 ≠ k then A p.1 (p.1 + 1) else 0 := fun p => by
    rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (symPerm r k rS)]
    have h2 : ∀ p' : Fin r, ((if (symPerm r k rS p).1 + 1 = (symPerm r k rS p').1 ∧ (symPerm r k rS p').1 < r ∧
        (symPerm r k rS p).1 ∈ SPsym r k rS then
        ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) (symPerm r k rS p') else 0) +
        if (symPerm r k rS p).1 + 1 = rS ∧ (symPerm r k rS p').1 = rS + k then
        ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) (symPerm r k rS p') else 0) =
        if p.1 + 1 = p'.1 then (if p.1 + 1 ≠ k then A p.1 p'.1 else 0) else 0 := fun p' => by
      rw [toSymOrd_val', ← hA, symPerm_val hr, symPerm_val hr]
      have e1 := SymLevelInv.symIdx_cases k rS p.1
      have e2 := SymLevelInv.symIdx_cases k rS p'.1
      have := p.2
      have := p'.2
      simp only [SPsym, Finset.mem_filter, Finset.mem_range]
      split_ifs <;> first | omega | simp
    rw [Finset.sum_congr rfl fun p' _ => h2 p',
      Fin.sum_univ_eq_sum_range (fun p' => if p.1 + 1 = p' then (if p.1 + 1 ≠ k then A p.1 p' else 0) else 0) r,
      Finset.sum_ite_eq]
    simp only [Finset.mem_range, ite_and]
  rw [Finset.sum_congr rfl fun p _ => h1 p,
    Fin.sum_univ_eq_sum_range (fun p => if p + 1 < r ∧ p + 1 ≠ k then A p (p + 1) else 0) r]
  obtain ⟨d, rfl⟩ : ∃ d, r = k + d := ⟨r - k, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  by_cases hd : d = 0
  · subst hd
    rw [sum_pred k _ _ fun p hp => by omega]
    simp
  · rw [sum_pred k _ _ fun p hp => by omega,
      sum_pred d (fun p => A (k + p) (k + p + 1)) (fun p => k + p + 1 < k + d ∧ k + p + 1 ≠ k) fun p hp => by omega]

theorem coarse_eq {r m t i : ℕ} (ht : 0 < t) (h1 : r ≤ i) (h2 : i < r + m * t) :
    coarse r (List.replicate m t) i = (i - r) / t + 1 := by
  rw [coarse_of_le h1, blkIdx_replicate ht _ _ (by omega)]

theorem lamPar_val (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n r k rS m t : ℕ} (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (M : HPar n κ h (List.replicate m t) (HPsymF κ r k rS)) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) :
    ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ M : Kˣ) : K) = lamF ψ χ k r t m A := by
  have h0 : ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ M : Kˣ) : K) =
      ((chiSymF ψ r k rS (HPar0 h _ _ M) : Kˣ) : K) *
        ((detChar χ n r (List.replicate m t) ⟨M.1, HPar_le h _ _ M.2⟩ : Kˣ) : K) := rfl
  rw [h0, chiSymF_val ψ hr (HPar0 h _ _ M) A fun i j => hA (Fin.castLE h i) (Fin.castLE h j), detChar_apply, List.length_replicate,
    Units.coe_prod]
  unfold lamF
  congr 1
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hb := blk_le hs hn.ge
  rw [← GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t hb ?_ ⟨M.1, HPar_le h _ _ M.2⟩ A hA]
  · unfold ext0
    rw [dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · intro i hi
    by_cases hir : i < r
    · rw [coarse_of_lt hir]
      omega
    · rw [coarse_eq ht (by omega) (by omega), Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega

end Res

section Lev

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem red_entB (k₀ : ℕ) (ex : ℕ → ℕ) (g : GLint E n P) (i j : Fin n) :
    red P (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k₀ 0 n 0 n ex ex g.1.toLinearMap) i.1 j.1 =
      (redGL n P g : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j := by
  unfold red
  rw [entB_zero _ _ _ _ _ rfl, dif_pos ⟨i.2, j.2⟩]
  rfl

theorem lamY_eq (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  rw [show stdAt E n P = LocE.lamY P (qOf P) n 0 0 from stdAt_eq (c := 0)]
  ext v
  unfold LocE.lamY
  rw [LastSteps.mem_sclLat, LastSteps.mem_sclLat]
  refine forall_congr' fun l => ?_
  have hl : l.1 < n := l.2
  simp only [LocE.scE, if_pos hl]

theorem levG_of_HPar (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {r k rS m t : ℕ} (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (ex : ℕ → ℕ) (g : GLint E n P)
    (hg : redGL n P g ∈ HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate m t) (HPsymF _ r k rS)) :
    LevG P k rS r t (n + 0) (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap) := by
  obtain ⟨hB, h0⟩ := mem_HPar.1 hg
  rw [mem_btG] at hB
  obtain ⟨s1, s2, s3⟩ := (mem_HPsymF_iff hr).1 h0
  have hI : IntM P (n + 0) (n + 0) (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap) :=
    ent_int (c := 0) (g := g.1) (by rw [lamY_eq]; exact g.2)
  have e : ∀ p p' (hp : p < n) (hp' : p' < n),
      redP P (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap p p') =
      (redGL n P g : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) ⟨p, hp⟩ ⟨p', hp'⟩ :=
    fun p p' hp hp' => red_entB k ex g ⟨p, hp⟩ ⟨p', hp'⟩
  refine ⟨hI, fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun i p p' h1 h2 h3 => ?_⟩
  · rw [e _ _ (by omega) (by omega)]
    exact s2 ⟨p', hp'⟩
  · rw [e _ _ hp (by omega)]
    by_cases hpr : p < r
    · rcases hz with hz | hz | hz
      · omega
      · exact s1 ⟨p, hpr⟩ ⟨p', hp'⟩ hz
      · exact s3 ⟨p, hpr⟩ ⟨p', hp'⟩ hz.2 hz.1
    · refine hB _ _ ?_
      show coarse r _ p' < coarse r _ p
      rw [coarse_of_lt hp', coarse_of_le (by omega)]
      omega
  · refine intAt_div_of_redP hq (hI _ _ h2 (by omega)) ?_
    rw [e _ _ h2 (by omega)]
    refine hB _ _ ?_
    show coarse r _ p' < coarse r _ p
    by_cases hpr : p' < r
    · rw [coarse_of_lt hpr, coarse_of_le (by omega)]
      omega
    · rw [coarse_eq ht (by omega) (by omega), coarse_eq ht (by omega) (by omega), Nat.add_lt_add_iff_right]
      have a1 : (p' - r) / t < i := by rw [Nat.div_lt_iff_lt_mul ht]; omega
      have a2 : i ≤ (p - r) / t := by rw [Nat.le_div_iff_mul_le ht]; omega
      omega

variable {K : Type} [Field K]

theorem phiGS_target (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {r k rS m i t c' n' : ℕ} (hm : m = i + 1) (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (g : GLint E n P)
    (hg : redGL n P g ∈ HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate m t) (HPsymF _ r k rS)) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiGS (qOf P) ψ χ k rS r t m c' n' 0 n (g.1.toLinearMap ∘ₗ x) * LocE.unitV (χ i) ((LinearEquiv.det g.1 : Eˣ) : E) =
      ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ ⟨_, hg⟩ : Kˣ) : K) * LocE.PhiGS (qOf P) ψ χ k rS r t m c' n' 0 n x := by
  have hL := levG_of_HPar hq hn h ht hr (fun i => i + 1) g hg
  rw [lamPar_val ψ χ hn h ht hr ⟨_, hg⟩ _ (red_entB k (fun i => i + 1) g),
    ← lamGvS_eq ψ χ (by omega) hL.1 (by omega) (by omega)]
  subst hm
  rw [phiGS_eq]
  refine phiM_target (c := 0) ψ χ (by omega) hr (by rw [hn, add_mul]; omega)
    (((HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate (i + 1) t) (HPsymF _ r k rS)).comap (redGL n P)).map (GLint E n P).subtype)
    ?_ ?_ ⟨g, hg, rfl⟩ x
  · rintro _ ⟨g', -, rfl⟩
    rw [lamY_eq]
    exact g'.2
  · rintro _ ⟨g', hg', rfl⟩
    exact levG_of_HPar hq hn h ht hr _ g' hg'

end Lev

theorem phiTop_target_sym : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → ∀ (hP : P ∈ Pr.vGs) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyG Ch (rPsymF Ch) ⟨P, hP⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu true m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyG Ch (rPsymF Ch) ⟨P, hP⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu true m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP j h x
  have e1 : psi0P Ch P = Ch.psi0 ⟨P, hP⟩ := dif_pos hP
  have e2 : chiP Ch P = chiAt Ch ⟨P, hP⟩ := dif_pos hP
  have ht : 0 < R.t := R.t_odd.pos
  obtain ⟨-, -, -, a4⟩ := ranks R (j := 0) (by omega)
  unfold PhiTop
  rw [if_pos hP, if_pos rfl, e1, e2]
  exact phiGS_target hq _ _ hm (rank_X'_eq R) (r_le_X' R) ht a4.le j h x

end GlobalTheory.TopLawSym

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrWeilAbs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_pow_central {n : ℕ} (a : WDRep h (Fin n → ℂ)) {φ : Weil h} (hφ : deg φ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ : Weil h, a.ρ (φ ^ m) * a.ρ σ = a.ρ σ * a.ρ (φ ^ m) := by
  classical
  let S : Set (Module.End ℂ (Fin n → ℂ)) := Set.range fun τ : Ine (F := E) A => a.ρ (ineIncl h τ)
  haveI : Finite S := a.smooth.finite_range.to_subtype
  have conj_mem : ∀ (k : ℕ), ∀ s ∈ S, a.ρ (φ ^ k) * s * a.ρ ((φ ^ k)⁻¹) ∈ S := by
    rintro k _ ⟨τ, rfl⟩
    have h0 : deg (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) = 0 := by simp
    refine ⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only [← map_mul]
    exact congrArg a.ρ (Subtype.ext rfl)
  let g : ℕ → (S → S) := fun k s => ⟨_, conj_mem k s.1 s.2⟩
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  obtain ⟨k, m, hm, hkm⟩ : ∃ k m : ℕ, 0 < m ∧ g k = g (k + m) := by
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact ⟨k1, k2 - k1, by omega, by rw [show k1 + (k2 - k1) = k2 by omega]; exact heq⟩
    · exact ⟨k2, k1 - k2, by omega, by rw [show k2 + (k1 - k2) = k1 by omega]; exact heq.symm⟩
  have comm_ine : ∀ τ : Ine (F := E) A,
      a.ρ (φ ^ m) * a.ρ (ineIncl h τ) = a.ρ (ineIncl h τ) * a.ρ (φ ^ m) := by
    intro τ
    have e1 : a.ρ (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) =
        a.ρ (φ ^ (k + m) * ineIncl h τ * (φ ^ (k + m))⁻¹) := by
      have := congrArg Subtype.val (congrFun hkm ⟨_, τ, rfl⟩)
      rw [map_mul, map_mul, map_mul, map_mul]
      exact this
    have e2 := congrArg (fun X => a.ρ ((φ ^ k)⁻¹) * X * a.ρ (φ ^ k * φ ^ m)) e1
    simp only [← map_mul] at e2
    rw [← map_mul, ← map_mul]
    convert e2.symm using 2 <;> group
  refine ⟨m, hm, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ σ
  have hc : φ ^ m * φ ^ deg σ = φ ^ deg σ * φ ^ m :=
    ((Commute.refl φ).pow_left m).zpow_right (deg σ)
  rw [hτ, map_mul, ← mul_assoc, ← map_mul, hc, map_mul, mul_assoc, comm_ine, ← mul_assoc]

theorem exists_smul_of_commute {n : ℕ} (a : WDRep h (Fin n → ℂ)) (hirr : a.ρ.IsIrreducible)
    (P : Module.End ℂ (Fin n → ℂ)) (hP : ∀ σ : Weil h, P * a.ρ σ = a.ρ σ * P) :
    ∃ c : ℂ, ∀ v, P v = c • v := by
  haveI := hirr
  let f : Representation.IntertwiningMap a.ρ a.ρ :=
    ⟨P, fun σ => LinearMap.ext fun v => LinearMap.congr_fun (hP σ) v⟩
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := a.ρ)).2 f
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun F : Representation.IntertwiningMap a.ρ a.ρ => F v) hc
  rw [Algebra.algebraMap_eq_smul_one] at this
  simpa [f] using this.symm

theorem irrWD_eig_norm_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := by
  intro E Ω _ _ _ _ _ A w h x hx φ hφ α hα β hβ
  obtain ⟨n, a, rfl, hirr⟩ := hx
  rw [WD.eig_mk] at hα hβ
  obtain ⟨m, hm, hcomm⟩ := exists_pow_central a hφ
  obtain ⟨c, hc⟩ := exists_smul_of_commute a hirr _ hcomm
  have hev : ∀ γ ∈ (a.ρ φ).charpoly.roots, γ ^ m = c := by
    intro γ hγ
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      (Polynomial.isRoot_of_mem_roots hγ)).exists_hasEigenvector
    have hpow : ∀ k : ℕ, ((a.ρ φ) ^ k) v = γ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv.apply_eq_smul, smul_smul, pow_succ]
    have h1 : γ ^ m • v = c • v := by rw [← hpow, ← map_pow, hc]
    exact smul_left_injective ℂ hv.2 h1
  have h2 : ‖α‖ ^ m = ‖β‖ ^ m := by rw [← norm_pow, ← norm_pow, hev α hα, hev β hβ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hm.ne').mp h2

end GlobalTheory.IrrWeilAbs
end
