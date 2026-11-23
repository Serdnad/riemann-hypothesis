module

public import Formalism.LocalToGlobal.Columns.Bundle036
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Formalism.LocalToGlobal.Columns.ChainTwOk
public import Formalism.LocalToGlobal.Columns.Bundle037
import Formalism.LocalToGlobal.Columns.Bundle033
import Formalism.LocalToGlobal.Columns.ChainTwPsi
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle009
public import Formalism.LocalToGlobal.Columns.UnfoldingPhiCompLeftUnipotentSource
public import Formalism.LocalToGlobal.Columns.ReductionColumnStandardBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct Pointwise

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

end GSD.Ev

section Pol

variable {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}

theorem smul_mem_RatSpanG (lam : ι → DomWeight n) (r : K) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : s r • p ∈ RatSpanG s lam := by
  unfold RatSpanG at hp ⊢
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r', f, hf, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨r * r', f, hf, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem RatSpanG_shW (lam : ι → DomWeight n) (c : ι → ℤ) :
    RatSpanG s (fun τ => shW (lam τ) (c τ)) = RatSpanG s lam := by
  unfold RatSpanG
  simp only [delSq_shW]

theorem exists_VV_of_mem_RatSpanG (lam : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : ∃ F ∈ VV K lam, MvPolynomial.map s F = p := by
  unfold RatSpanG at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (MvPolynomial.map (Int.castRingHom K) (f τ)), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
      exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ)) (map_mem_weyl le_rfl _ _ (hf τ))
    · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      have e : s.comp (Int.castRingHom K) = Int.castRingHom ℂ := RingHom.ext_int _ _
      rw [e]
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨F', hF', rfl⟩ := hy
    exact ⟨F + F', Submodule.add_mem _ hF hF', map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, Submodule.neg_mem _ hF, map_neg _ _⟩

variable [CharZero K]

theorem map_mem_RatSpanG (lam : ι → DomWeight n) {F : MvPolynomial (ι × Fin n × Fin n) K} (hF : F ∈ VV K lam) :
    MvPolynomial.map s F ∈ RatSpanG s lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    let T : ι → Set (MvPolynomial (ι × Fin n × Fin n) K) := fun τ =>
      Set.range fun w : List (Fin n × Fin n × ℕ) =>
        Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW))
    have h1 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ) ∈ Submodule.span K (T τ) := by
      intro τ
      have h0 : f τ ∈ delSq K n (lam τ) := by rw [← nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ).toLinearMap) h0
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    have h2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∈ Submodule.span K (∏ τ, T τ) := by
      rw [← Submodule.prod_span]
      exact prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
    have key : ∀ y ∈ Submodule.span K (∏ τ, T τ), MvPolynomial.map s y ∈ RatSpanG s lam := by
     intro y hy
     induction hy using Submodule.span_induction with
     | mem y hy =>
      rw [Set.mem_finsetProd] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
          Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) = g τ :=
        fun τ => hg (Finset.mem_univ τ)
      choose w hw using hg'
      refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
        fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
      rw [map_one, one_smul]
      have e : (∏ τ, g τ) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) :=
        Finset.prod_congr rfl fun τ _ => (hw τ).symm
      rw [e, map_ten]
      congr 1
      funext τ
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
        Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
     | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
     | add y z _ _ hy hz => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hy hz
     | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
      exact smul_mem_RatSpanG s lam c hy
    exact key _ h2
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact smul_mem_RatSpanG s lam c hx

theorem mem_RatSpanG_iff (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    p ∈ RatSpanG s lam ↔ ∃ F ∈ VV K lam, MvPolynomial.map s F = p :=
  ⟨exists_VV_of_mem_RatSpanG s lam, by rintro ⟨F, hF, rfl⟩; exact map_mem_RatSpanG s lam hF⟩

end Pol

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

end Round

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) (i : ℕ)


end Gen

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

include hPr in
theorem att_T_mem_under (P : {P // P ∈ Pr.vT u}) : (Pr.T u : 𝓞 X.F) ∈ (underPl X.F P.1).asIdeal := by
  show (Pr.T u : 𝓞 X.F) ∈ P.1.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast]
  exact T_mem hPr u P

def tieEV : {P // P ∈ Pr.vT u} ≃ {v : HeightOneSpectrum (𝓞 X.F) // (Pr.T u : 𝓞 X.F) ∈ v.asIdeal} :=
  Equiv.ofBijective (fun P => ⟨underPl X.F P.1, att_T_mem_under hPr u P⟩) (by
    constructor
    · intro P Q h
      have h1 : underPl X.F P.1 = underPl X.F Q.1 := congrArg Subtype.val h
      have hP : IsOver (underPl X.F P.1) P.1 := rfl
      have hQ : IsOver (underPl X.F P.1) Q.1 := by rw [h1]; rfl
      exact Subtype.ext ((basePi_of_ok hX hPr u).over_unique hc P.2 hP Q.1 Q.2 hQ).symm
    · rintro ⟨v, hv⟩
      obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).2 hv
      exact ⟨⟨P, hP⟩, Subtype.ext (HeightOneSpectrum.ext hov.symm)⟩)

end Gen

section Val

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))


include hval in
theorem att_val_pos (w : Pl.Pl) (x : 𝓞 K) : (0 : WithTop ℤ) < Pl.val w (x : K) ↔ x ∈ (pw w).asIdeal := by
  by_cases hx : x = 0
  · subst hx
    have h0 : Pl.val w (((0 : 𝓞 K) : 𝓞 K) : K) = ⊤ := by
      rw [show (((0 : 𝓞 K) : 𝓞 K) : K) = 0 from rfl]
      exact (Pl.val w).map_zero
    rw [h0]
    exact ⟨fun _ => zero_mem _, fun _ => WithTop.coe_lt_top (0 : ℤ)⟩
  · have hx' : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext h)
    have h0 : (pw w).valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hx'
    rw [hval w _ hx', ← (pw w).valuation_lt_one_iff_mem (K := K)]
    unfold Formalism.BasicNotions.vAdd
    rw [← WithTop.coe_zero, WithTop.coe_lt_coe, neg_pos, ← WithZero.log_one, WithZero.log_lt_log h0 one_ne_zero]


include hval in
theorem att_resChar_mem (w : Pl.Pl) : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ (pw w).asIdeal := by
  rw [← att_val_pos Pl pw hval]
  have h := Pl.val_resChar w
  have e : ((((Pl.resChar w : ℕ) : 𝓞 K) : 𝓞 K) : K) = ((Pl.resChar w : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [e, h, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  exact_mod_cast Pl.ramIdx_pos w

end Val

section Seen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)


include hc in
theorem att_mem_conjP (P : Pl X.E) (x : 𝓞 X.F) :
    algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime₂ P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal := by
  rw [mem_conjP, rll_cO_algebraMap hc]

theorem att_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    x ∈ (tieEV hc hX hPr u P).1.asIdeal ↔ X.embO (tauOfR hX hPr u w P) (algebraMap (𝓞 X.F) (𝓞 X.E) x) ∈ w.asIdeal := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dite_eq_left hw]
    rfl
  rw [e, ← mem_pullW]
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.1.asIdeal ↔ _
  rcases tauOfC_spec hX hPr u w hw P with h | h
  · rw [show pullW (tauOfC w P.1) w = P.1 from h]
  · rw [show pullW (tauOfC w P.1) w = conjPrime₂ P.1 from h, att_mem_conjP hc]


end Seen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem att_star_eq (x : d.host.E) : star x = d.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj d.host x



def atTTied (hH : HostHyp d) (u : d.what₂.Word) : CF.AtTTied (D := d.colRec a) u where
  eV := tieEV d.sp.cm d.hX d.hPr u
  piU := d.piT u
  piU_K := hH.piT_K u
  piU_norm := by
    have h := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piT_norm u)
    rw [map_mul, map_natCast] at h
    rw [← att_star_eq]
    exact h
  piU_cong := by
    rw [Ideal.mem_span_singleton]
    have h := d.hPr.piT_cong u
    have e : d.Pr.cond = d.host.QS * d.host.q * d.host.d := hH.cond_eq
    rw [e] at h
    exact h
  res := fun v => Ideal.Quotient.mk v.1.asIdeal
  res_surj := fun v => Ideal.Quotient.mk_surjective
  res_pi := fun v => Ideal.Quotient.eq_zero_iff_mem.2 ((rls_vT_iff d.hX d.hPr u v.1).1 v.2)
  res_conj := fun v pb hpb h => by
    have h1 : pb = cO d.X.E (d.Pr.piT u) := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 d.X.E) d.X.E pb = algebraMap (𝓞 d.X.E) d.X.E (cO d.X.E (d.Pr.piT u))
      rw [algebraMap_cO, att_star_eq (d := d)]
      exact hpb
    change Ideal.Quotient.mk v.1.asIdeal pb = 0 at h
    rw [h1] at h
    exact (basePi_of_ok d.hX d.hPr u).conj_notMem v.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  res_v := fun v x => (Ideal.Quotient.eq_zero_iff_mem (I := v.1.asIdeal)).symm
  tauOf := fun w hw v x => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    exact (att_tauOf d.sp.cm d.hX d.hPr u (d.plEq w) hT v x).trans (att_val_pos d.what₂.places d.plEq hH.val_eq w _).symm
  seenP := fun w hw τ => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    have key : ∀ b : Bool, b = (open Classical in decide (seenC d.Pr u (d.plEq w))) →
        (0 : WithTop ℤ) < d.what₂.places.val w (d.embE (d.host.sigmaOf (d.eTau τ : d.R.GG)
          (if b = true then (d.piT u : d.host.E) else d.host.conj (d.piT u : d.host.E)))) := by
      intro b hb
      by_cases hs : seenC d.Pr u (d.plEq w)
      · have hb' : b = true := by rw [hb]; exact @decide_eq_true _ (Classical.propDecidable _) hs
        rw [if_pos hb']
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.Pr.piT u))).2 (hs τ)
      · have hb' : ¬ b = true := by rw [hb]; simpa using hs
        rw [if_neg hb', ← att_star_eq]
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.X.conjO (d.Pr.piT u)))).2
          (((seenC_or_seenBarC d.hX d.hPr u (d.plEq w) hT).resolve_left hs) τ)
    exact key _ rfl

end Rec

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwAux

theorem twNormRep {X : Fields} {Pr : Primes X} {R : Ranks} (sharp : Bool) (j : ℕ)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (hd : TwDegOne X P) (h : AutY X R j) (hb : TwBdd (Pr := Pr) j P h) :
    ∃ h', SameDC (Pr := Pr) sharp j P h h' ∧ TwBdd (Pr := Pr) j P h' ∧ TwNF (Pr := Pr) j P h' ∧
      prCat (Pr := Pr) sharp j P h' ≤ GLint X.E (R.N j) P := by
  have hL : lamYat (Pr := Pr) (R := R) j P = LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 := by
    unfold lamYat; rw [if_neg hP]
  have hJ : Jat (Pr := Pr) (R := R) sharp j P = LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j) := by
    unfold Jat; rw [if_neg hP]
  have hb0 : PI.TwNormLat.Bdd P (R.N j) (cOf R j) j h := by
    intro x hx
    have := hb x (by rw [hL]; exact hx)
    rw [hL] at this
    exact this
  obtain ⟨r, hr, κ, hκ, hb', hnf, hpr⟩ := _root_.TwNormLat X.E P (R.N j) (cOf R j) (R.k + j) j hd.1 hd.2 h hb0
  refine ⟨r * h * κ, ⟨r, hr, κ, by rw [hJ]; exact hκ, rfl⟩, ?_, ?_, ?_⟩
  · intro x hx
    rw [hL] at hx ⊢
    exact hb' x hx
  · obtain ⟨n, z, hn, hz, hv⟩ := hnf
    refine ⟨n, z, hn, hz, fun v => ?_⟩
    rw [hL]
    exact hv v
  · unfold prCat
    rw [hJ]
    exact hpr

theorem twChrOk_one {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hpsi : ∀ x, IntAt P.1 x → cst.psi P x = 1) : TwChrOk Ch sel mu cst j P 1 := by
  have hJ : Jat (Pr := Pr) (R := R) cst.sharp j P.1 = LocE.JQ P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := by
    unfold Jat; rw [if_neg hP]
  have hchi : ∀ r, chiInv Ch sel mu cst j P 1 r =
      PI.TwChrOne.ChiL P.1 (cst.psi P) (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + j) (R.N j) (cOf R j) 1 r := by
    intro r
    unfold chiInv lamRow
    rw [if_neg hP]
    rfl
  obtain ⟨h1, h2⟩ := _root_.TwChrOne X.E X.K P.1 (cst.psi P) (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + j) (R.N j) (cOf R j) hpsi
  refine ⟨fun r hr => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · rw [hchi]
    rw [hJ] at hr
    exact h1 r hr
  · rw [hchi, hchi, hchi]
    rw [hJ] at hr hr' hr''
    exact h2 r hr r' hr' r'' hr'' hx

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def UnfoldingNonvanishingDoubleCoset (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h h' : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 h → TwBdd (Pr := Pr) (i + 1) P.1 h' →
      SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h'

def TwChrNFQ (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwNF (Pr := Pr) i P.1 hal →
    TwBdd (Pr := Pr) (i + 1) P.1 h → TwNF (Pr := Pr) (i + 1) P.1 h → prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1 →
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → TwChrOk Ch sel mu cst (i + 1) P h

variable {Ch sel mu cst}

theorem twNormDC_of {m2 : ℕ} (HE : UnfoldingNonvanishingDoubleCoset Ch sel mu cst m2) : TwNormDC Ch sel mu cst m2 := by
  intro i hi P hP hdeg hal h hbal _ hb hne
  obtain ⟨h', hs, hb', hnf, hpr⟩ := twNormRep (Pr := Pr) cst.sharp (i + 1) hP hdeg h hb
  exact ⟨h', hs, hb', hnf, hpr, HE i hi P hP hdeg hal h h' hbal hb hb' hs hne⟩

theorem twChrQ_of {m2 : ℕ} (HF : TwChrNFQ Ch sel mu cst m2) (hpsi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ x, IntAt P.1 x → cst.psi P x = 1) :
    TwChrQ Ch sel mu cst m2 :=
  ⟨HF, fun P hP _ => twChrOk_one Ch sel mu cst (m2 + 1) P hP (hpsi P hP)⟩

theorem twistedIndex_firstUnfolding_ok (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0)
    (HE : UnfoldingNonvanishingDoubleCoset Ch sel mu (twCst Ch sel mu G) m2) (HF : TwChrNFQ Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 :=
  twIdx_ok_full hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi (twNormDC_of HE)
    (twChrQ_of HF fun P hP x hx => (twCst_ok hPr hCh h4 (twCstQ_of hd hz hs hxi)).psi_int P x hx)

end TwAux

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem cq_card {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
  unfold qOf
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem cq_covT : TruncatedUnfoldingChangeOfVarsTarget := by
  intro E _ _ _ P K _ n' c' n c hc hp hu psi D a b e hadd hint Ψ hsupp haD hinv r hr g hgI hg hre _ heD A B hA hbB _ wt y
  subst hc
  exact finite_sum_target_equality (ciQ_mem P) hu hp (cq_card P) psi hadd hint Ψ hsupp haD hinv r hr g hgI hg hre heD hA hbB wt y

end Formalism.L2.Col
end
end
