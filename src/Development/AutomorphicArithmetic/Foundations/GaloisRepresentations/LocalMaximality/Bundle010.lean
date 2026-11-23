module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem resP_one {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V] (ρ : F →ₗ[ℂ] ℂ)
    (h : ρ 1 = 1) (w : V) : resP V ρ ((1 : F) ⊗ₜ[ℂ] w) = w := by
  simp [resP, h]

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i
  simp [lft, uni, Finset.mem_toLeft]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i
  simp [rgt, uni, Finset.mem_toRight]

private theorem card_filter_le {d : ℕ} (i : Fin (d + 1)) :
    (Finset.univ.filter (· ≤ i)).card = (i : ℕ) + 1 := by
  have h : Finset.univ.filter (· ≤ i) = Finset.Iic i := by
    ext j
    simp
  rw [h, Fin.card_Iic]

private theorem card_filter_ge {d : ℕ} (i : Fin (d + 1)) :
    (Finset.univ.filter (i ≤ ·)).card = d + 1 - (i : ℕ) := by
  have h : Finset.univ.filter (i ≤ ·) = Finset.Ici i := by
    ext j
    simp
  rw [h, Fin.card_Ici]

theorem UpperTheory.Gal.productCup_of_system.zAct_of :
    PCup → PTheta → PCmp → PInt → EdgeRel → SysBasic → GoodZ → ZAct := by
  intro hCup hTh hCmp hInt hEdge hBas hGood F K _ _ _ _ _ _ d x hx τ hτ ρ hρ a p ha c hc hD α hα
  obtain ⟨hc1, hv1, hk1⟩ := hCup F K d x hx τ hτ a p ha c hc hD α hα
  obtain ⟨cθ, hcθ, hvθ, hkθ, htθ⟩ := hTh F K d x hx a p α hα
  have hmono := (hGood F K d x hx a).2.2
  have hE := hEdge (Fin (d + 1)) (DR ℂ K) (fun s => omB ℂ K (rB ℂ K (xv x) s) a) p hmono α hα
  let c1 := rcup (muP F K τ) p c α - cθ
  have hZ : c1 ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2) := sub_mem hc1 hcθ
  have hv : ∀ (b : Finset (Two d)) (L : Finset (Mi d)), d < L.card → c1 (uni b L) = 0 := by
    intro b L h
    simp [c1, hv1 b L h, hvθ b L h]
  let γ : Finset (Two d) → DR ℂ K :=
    ((-1 : ℤ) ^ (p * (d + 1) + d)) • edge1 α - ((-1 : ℤ) ^ ((p + 1) * d)) • edge2 α
  have hγe : γ = (-((-1 : ℤ) ^ ((p + 1) * d))) • (edge2 α - ((-1 : ℤ) ^ p) • edge1 α) := by
    have h : p * (d + 1) + d = (p + 1) * d + p := by ring
    simp only [γ, h, pow_add]
    generalize ((-1 : ℤ) ^ ((p + 1) * d)) = s
    generalize ((-1 : ℤ) ^ p) = t
    module
  have hγ : γ ∈ (acx (mixF fun I J : Finset (Fin (d + 1)) => omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) fun _ => 1).B (p + 2) := by
    rw [hγe]
    exact zsmul_mem hE _
  have hk : ∀ (b : Finset (Two d)) (L : Finset (Mi d)), L.card = d → mulP F K (c1 (uni b L)) = kap K x L • γ b := by
    intro b L h
    simp only [c1, γ, Pi.sub_apply, map_sub, hk1 b L h, hkθ b L h, smul_sub, Pi.smul_apply]
  have hB := hCmp F K d x hx a p c1 hZ hv γ hγ hk
  have hTop := (hBas d _ _ (sysP K x a) (Mi d) n11 (sysP K x a).mu (d + p + 2)).2.2.2.1 c1 hB
  have hI := hInt F K d x hx τ hτ ρ hρ a p (top c1) hTop
  have hCc := (hBas d _ _ (sysZ K x a) (Mi d) n11 (sysZ K x a).mu (d + 2)).1 c hc.1
  have hαs : ∀ s : Finset (Fin (d + 1)), s.card ≠ p + 1 → α s = 0 := by
    intro s hs
    have h1 : α s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) s) a else ⊥ :
        Submodule ℂ (DR ℂ K)) := hα.1 s (Set.mem_univ s)
    rw [if_neg (by
      rintro ⟨-, h⟩
      exact hs (by exact_mod_cast h))] at h1
    simpa using h1
  have key : (α - fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) =
      -(fun J => resP (DR ℂ K) ρ (top c1 (uni Finset.univ J))) := by
    funext J
    have hsum : ((-1 : ℤ) ^ (p * J.card)) • (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) =
        ∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))) := by
      by_cases hJ : J.card = p + 1
      · have : Even (p * J.card) := by
          rw [hJ]
          exact Nat.even_mul_succ_self p
        rw [this.neg_one_pow, one_smul]
      · have : ∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : (Finset.univ.filter (i ≤ ·)).card = p + 1
          · have h0 : top c (uni (Finset.univ.filter (· ≤ i)) J) = 0 := by
              refine hCc _ _ ∅ (Or.inr (Or.inr ?_))
              rw [card_filter_ge] at hi
              have hid := i.is_lt
              simp only [card_filter_le, Finset.card_empty, add_zero]
              omega
            rw [h0]
            simp
          · rw [hαs _ hi]
            simp
        rw [this, smul_zero]
    have htop : top c1 (uni Finset.univ J) = ((-1 : ℤ) ^ (p * J.card)) • (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) - (1 : F) ⊗ₜ[ℂ] α J := by
      simp only [top, c1, Pi.sub_apply, htθ, rcup, lft_uni', rgt_uni', Finset.card_empty, add_zero]
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [htop, hsum, map_sub, resP_one ρ hρ.1]
    abel
  rw [key]
  exact neg_mem hI
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private theorem map_detC' {S S' κ : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [LinearOrder κ] {p : ℕ} (φ : S →ₐ[ℂ] S') (ρ : κ → Fin p → S) (s : Finset κ) :
    φ (detC ρ s) = detC (fun t b => φ (ρ t b)) s := by
  unfold detC
  split_ifs with h
  · rw [AlgHom.map_det]
    congr 1
  · simp

private def rho0 {d : ℕ} {K : Type} [Field K] (y : Fin (d + 1) → K) :
    Fin (d + 1) ⊕ₗ Mi d → Fin (d + 1) → K := fun t => Sum.elim (fun i => Pi.single i 1)
  (fun l m => (if m = (ofLex l).1 then y m * y (ofLex l).2 else 0) -
    if m = (ofLex l).2 then y m * y (ofLex l).1 else 0) (ofLex t)

private theorem map_rowMu {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (π : S →ₐ[ℂ] K) (y : Fin (d + 1) → K)
    (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i) (s : Finset (Fin (d + 1) ⊕ₗ Mi d)) :
    π (detC T.rowMu s) = detC (rho0 y) s := by
  rw [map_detC']
  congr 1
  funext t b
  rcases ht : ofLex t with i | l
  · simp only [Sys.rowMu, rho0, ht, Sum.elim_inl, Pi.single_apply]
    split_ifs <;> simp
  · simp only [Sys.rowMu, rho0, ht, Sum.elim_inr, map_sub, apply_ite π, map_mul, hX, hY, map_zero]

private theorem map_mu {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (π : S →ₐ[ℂ] K) (y : Fin (d + 1) → K)
    (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i) (l : Mi d) : π (T.mu l) = 0 := by
  simp only [Sys.mu, map_sub, map_mul, hX, hY]
  ring

private theorem ind_of {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (hM : ThMu) (hU : WdUni) (T : Sys d S E) (π : S →ₐ[ℂ] K)
    (y : Fin (d + 1) → K) (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i)
    (i : Fin (d + 1)) (L : Finset (Mi d)) :
    π (detC T.rowMu (uni {i} L)) = π (detC T.rowMu (uni {0} L)) := by
  by_cases h : i = 0
  · rw [h]
  have h0 : (0 : Fin (d + 1)) ≠ i := fun e => h e.symm
  have h1 := congrFun (hM d S E T).1 (uni {0, i} L)
  rw [(hU _ _ _ _ _ {0, i} L).1] at h1
  have hl : wd (fun j : Fin (d + 1) => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inlE j : Fin (d + 1) ⊕ₗ Mi d)))
      (fun b' => detC T.rowMu (uni b' L)) {0, i} =
      detC T.rowMu (uni {i} L) - detC T.rowMu (uni {0} L) := by
    have e0 : ({0, i} : Finset (Fin (d + 1))).erase 0 = {i} := by
      ext a; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hb | hb⟩
        · exact absurd hb ha
        · exact hb
      · rintro rfl; exact ⟨h, Or.inr rfl⟩
    have ei : ({0, i} : Finset (Fin (d + 1))).erase i = {0} := by
      ext a; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hb | hb⟩
        · exact hb
        · exact absurd hb ha
      · rintro rfl; exact ⟨h0, Or.inl rfl⟩
    have s0 : GlobalTheory.cubeSign ({0, i} : Finset (Fin (d + 1))) 0 = 1 := by
      simp [GlobalTheory.cubeSign, Finset.filter_eq_empty_iff]
    have si : GlobalTheory.cubeSign ({0, i} : Finset (Fin (d + 1))) i = -1 := by
      have hp : (0 : Fin (d + 1)) < i := Fin.pos_iff_ne_zero.2 h
      have : ({0, i} : Finset (Fin (d + 1))).filter (· < i) = {0} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hb⟩
          · rfl
          · exact absurd hb (lt_irrefl _)
        · rintro rfl; exact ⟨Or.inl rfl, hp⟩
      simp [GlobalTheory.cubeSign, this]
    rw [wd_apply', Finset.sum_pair h0, e0, ei, s0, si]
    simp [app, inlE, sub_eq_add_neg, add_comm]
  have hr : π (wd (fun l : Mi d => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inrE l : Fin (d + 1) ⊕ₗ Mi d)))
      (fun L' => detC T.rowMu (uni {0, i} L')) L) = 0 := by

    rw [wd_apply', map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : app (fun _ : Fin (d + 1) => (1 : S)) T.mu (inrE l : Fin (d + 1) ⊕ₗ Mi d) = T.mu l := by simp [app, inrE]
    rw [map_zsmul]
    simp [this, map_mu T π y hX hY l]
  rw [hl] at h1
  have h2 := congrArg π h1
  rw [map_add (f := _), map_zsmul, hr, smul_zero, add_zero, map_sub] at h2
  simpa [sub_eq_zero] using h2

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.kapInd_of :
    ThMu → WdUni → KapInd := by
  intro hM hU F K _ _ _ _ _ _ d x _ S E _ _ _ _ T π hX hY i L _
  have hZ : ∀ j, Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).X j : K ⊗[ℂ] K) = algebraMap F K (x j) := by
    intro j; simp [sysZ]
  have hZ' : ∀ j, Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).Y j : K ⊗[ℂ] K) = algebraMap F K (x j) := by
    intro j; simp [sysZ]
  rw [ind_of hM hU T π _ hX hY i L, kap,
    map_rowMu T π (fun j => algebraMap F K (x j)) hX hY,
    map_rowMu (sysZ K x 0) (Algebra.TensorProduct.lmul' ℂ) (fun j => algebraMap F K (x j)) hZ hZ']
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.PartialZeroIdentity

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i
  simp [lft, uni]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i
  simp [rgt, uni]

private theorem cech_zero {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    {G : Finset ι → Submodule ℂ E} {n : ℤ} {y : Finset ι → E} (hy : y ∈ (cech G).Z n)
    (s : Finset ι) (h : (s.card : ℤ) ≠ n + 1) : y s = 0 := by
  have h1 : y s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then G s else ⊥) := hy.1 s (Set.mem_univ s)
  rw [if_neg (fun h' => h h'.2)] at h1
  simpa using h1

private theorem res_mu {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) (e f w : DR ℂ K) :
    resP (DR ℂ K) ρ (muP F K τ (e ⊗ₜ f) w) = trF ℂ τ ρ (e * w) • f := by
  simp [muP, resP, trF]

end UpperTheory.Gal.productCup_of_system.PartialZeroIdentity

open UpperTheory.Gal.productCup_of_system.PartialZeroIdentity in
theorem UpperTheory.Gal.productCup_of_system.zId_of :
    ZAct → RCupTop → KunDec → SysBasic → GoodZ → ZId := by
  intro hZA hRC hKD hSB hGZ F K _ _ _ _ _ _ d x hFC τ hT ρ hR a ha c hc hD
  have htop : top c ∈ (sysZ K x a).mix.Z (d + 2) :=
    (hSB d _ _ (sysZ K x a) (Mi d) n11 (sysZ K x a).mu (d + 2)).2.2.1 c hc
  obtain ⟨m, p, e, f, hk, hB⟩ := hKD (Fin (d + 1)) (DR ℂ K) (DR ℂ K)
    (fun s => omB ℂ K (rB ℂ K (xv x) s) (d - a)) (fun s => omB ℂ K (rB ℂ K (xv x) s) a) d
    (hGZ F K d x hFC (d - a)).2.2 (hGZ F K d x hFC a).2.2 (top c) htop
  refine ⟨m, p, e, f, hk, hB, ?_⟩
  intro q α hα
  have h1 := hZA F K d x hFC τ hT ρ hR a q ha c hc hD α hα
  have h2 := hRC F K d x hFC τ hT ρ hR a q ha _ hB α hα
  have hzero : ∀ k, p k ≠ q → pr K τ ρ (e k) α = 0 := by
    intro k hkq
    simp only [pr, cupPair, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      LinearMap.proj_apply, LinearMap.mul_apply']
    refine Finset.sum_eq_zero fun j _ => ?_
    have hc1 : ((Finset.univ.filter (· ≤ j)).card : ℤ) = (j : ℤ) + 1 := by
      rw [Finset.filter_ge_eq_Iic, Fin.card_Iic]; push_cast; ring
    have hc2 : ((Finset.univ.filter (j ≤ ·)).card : ℤ) = (d : ℤ) + 1 - j := by
      rw [Finset.filter_le_eq_Ici, Fin.card_Ici]; have := j.2; omega
    by_cases hA : ((Finset.univ.filter (· ≤ j)).card : ℤ) = ((d : ℤ) - p k) + 1
    · have : α (Finset.univ.filter (j ≤ ·)) = 0 := by
        refine cech_zero hα _ ?_
        rw [hc2]; rw [hc1] at hA
        intro h; apply hkq; omega
      simp [this]
    · have : e k (Finset.univ.filter (· ≤ j)) = 0 := cech_zero (hk k).2.1 _ hA
      simp [this]
  have key : ∀ J, resP (DR ℂ K) ρ (∑ i, muP F K τ
      ((∑ k, join (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) (e k) (f k))
        (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) =
      ∑ k ∈ Finset.univ.filter (fun k => p k = q), pr K τ ρ (e k) α • f k J := by
    intro J
    rw [Finset.sum_filter_of_ne (fun k _ hne => ?_)]
    · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, join, _root_.UpperTheory.Gal.productCup_of_system.PartialZeroIdentity.lft_uni',
        _root_.UpperTheory.Gal.productCup_of_system.PartialZeroIdentity.rgt_uni', TensorProduct.mk_apply, map_sum,
        LinearMap.sum_apply, res_mu]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [pr, cupPair, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
        LinearMap.proj_apply, LinearMap.mul_apply', Finset.sum_smul]
    · by_contra hpq
      exact hne (by rw [hzero k hpq, zero_smul])
  have hfin := add_mem h1 h2
  convert hfin using 1
  ext J
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  rw [← key J]

  simp only [Finset.sum_apply, map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, map_sum, LinearMap.sum_apply]
  abel
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma resP_eq_zero {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V]
    (ρ : F →ₗ[ℂ] ℂ) (A : Submodule ℂ F) (B : Submodule ℂ V) (hA : ∀ f ∈ A, ρ f = 0)
    {m : F ⊗[ℂ] V} (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ F V) A B) :
    resP V ρ m = 0 := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp [resP, hA a ha]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

private lemma residueCharacteristic_mem {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V]
    (ρ : F →ₗ[ℂ] ℂ) (A : Submodule ℂ F) (B : Submodule ℂ V)
    {m : F ⊗[ℂ] V} (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ F V) A B) :
    resP V ρ m ∈ B := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simpa [resP] using B.smul_mem (ρ a) hb
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact B.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact B.smul_mem r hx

private lemma wd_one_apply {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (c : Finset ι → E) (t : Finset ι) :
    wd (fun _ : ι => (1 : Module.End ℂ E)) c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • c (t.erase i) := by
  simp [wd, LinearMap.sum_apply]

theorem UpperTheory.Gal.productCup_of_system.pInt_of :
    WdUni → GoodZ → PInt := by
  intro hW _ F K _ _ _ _ _ _ d x hx τ _ ρ hρ a p t ht
  simp only [UpperTheory.Gal.productCup_of_system.Sys.mix, GlobalTheory.WH.acx, GlobalTheory.PD.Cx.B, Submodule.mem_map,
    Submodule.mem_pi] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  have hU := fun I J : Finset (Fin (d + 1)) =>
    hW (Fin (d + 1)) (Fin (d + 1)) (F ⊗[ℂ] DR ℂ K) (fun _ => 1) c I J
  have hcu : ∀ I J : Finset (Fin (d + 1)), c (uni I J) ≠ 0 →
      I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + p + 1 ∧
        c (uni I J) ∈ (sysP K x a).M I J := by
    intro I J h0
    have h := hc (uni I J) (Set.mem_univ _)
    obtain ⟨_, hl, hr, hcard, _⟩ := hU I J
    split_ifs at h with h1
    · simp only [GlobalTheory.WH.mixF, hl, hr] at h
      split_ifs at h with h2
      · refine ⟨h2.1, h2.2, ?_, h⟩
        rw [hcard] at h1
        omega
      · exact absurd ((Submodule.mem_bot ℂ).mp h) h0
    · exact absurd ((Submodule.mem_bot ℂ).mp h) h0
  have hz : ∀ (i : Fin (d + 1)) (J : Finset (Fin (d + 1))),
      resP (DR ℂ K) ρ (c (uni (Finset.univ.erase i) J)) = 0 := by
    intro i J
    by_cases h0 : c (uni (Finset.univ.erase i) J) = 0
    · rw [h0, map_zero]
    obtain ⟨hI, _, _, hm⟩ := hcu _ _ h0
    exact resP_eq_zero ρ _ _
      (fun f hf => GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hx.pd ρ hρ i _ hI (by simp) f hf) hm
  refine ⟨fun L => ((-1 : ℤ) ^ (d + 1)) • resP (DR ℂ K) ρ (c (uni Finset.univ L)), ?_, ?_⟩
  · simp only [Lef.omCx, GlobalTheory.PD.cech, GlobalTheory.PD.cechC, Submodule.mem_pi]
    intro L _
    by_cases h0 : c (uni Finset.univ L) = 0
    · simp [h0]
    obtain ⟨_, hL, hcard, hm⟩ := hcu _ _ h0
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    dsimp only
    rw [if_pos (show L.Nonempty ∧ (L.card : ℤ) = ↑p - 1 + 1 from ⟨hL, by omega⟩)]
    exact Submodule.smul_of_tower_mem _ _ (residueCharacteristic_mem ρ _ _ hm)
  · funext J
    simp only [Lef.omCx, GlobalTheory.PD.cech, GlobalTheory.PD.deltaL, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.DI.delta]
    rw [(hU Finset.univ J).1]

    simp only [wd_one_apply, map_add (f := _), map_zsmul, map_sum, hz, smul_zero, Finset.sum_const_zero,
    zero_add, Finset.card_univ, Fintype.card_fin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
end
