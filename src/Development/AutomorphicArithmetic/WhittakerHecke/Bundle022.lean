module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsSemisimpleInducedParam
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle007
public import Development.DiscreteGroups.GlobalIrreducibility.DzTame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WhTorus
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle017
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle015
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace UpperTheory.IrreducibleNonTameWeilDeligne

open Multiplicative

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {K : Type} [Field K]

private def eta (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K) (j : ℤ) :
    Ine (F := E) A →* ℂˣ where
  toFun t := ψ (ofAdd ((f ^ j) (toAdd (π t))))
  map_one' := by simp
  map_mul' s t := by
    rw [map_mul, toAdd_mul, map_add (f := _), ofAdd_add, map_mul]

private theorem eta_apply (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K) (j : ℤ)
    (t : Ine (F := E) A) : eta f ψ π j t = ψ (ofAdd ((f ^ j) (toAdd (π t)))) := rfl

private theorem eta_succ (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K) (j : ℤ)
    {t t' : Ine (F := E) A} (e : π t' = ofAdd (f (toAdd (π t)))) : eta f ψ π j t' = eta f ψ π (j + 1) t := by
  rw [eta_apply, eta_apply, e, toAdd_ofAdd, zpow_add_one]
  rfl

private theorem eta_eq_iff (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K)
    (hψ : ∀ m : ℤ, (∀ x, ψ (ofAdd ((f ^ m) x)) = ψ (ofAdd x)) ↔ f ^ m = 1) (hs : Function.Surjective π) (j j' : ℤ) :
    eta f ψ π j = eta f ψ π j' ↔ ((orderOf f : ℕ) : ℤ) ∣ j - j' := by
  rw [orderOf_dvd_iff_zpow_eq_one]
  constructor
  · intro e
    refine (hψ _).1 fun x => ?_
    obtain ⟨t, ht⟩ := hs (ofAdd ((f ^ (-j')) x))
    have h1 := DFunLike.congr_fun e t
    rw [eta_apply, eta_apply, ht, toAdd_ofAdd] at h1
    have e1 : (f ^ j) ((f ^ (-j')) x) = (f ^ (j - j')) x := by
      rw [sub_eq_add_neg, zpow_add]
      rfl
    have e2 : (f ^ j') ((f ^ (-j')) x) = x := by
      show (f ^ j' * f ^ (-j')) x = x
      rw [← zpow_add, add_neg_cancel, zpow_zero]
      rfl
    rwa [e1, e2] at h1
  · intro e
    have e1 : f ^ j = f ^ j' := by
      rwa [zpow_sub, mul_inv_eq_one] at e
    refine MonoidHom.ext fun t => ?_
    rw [eta_apply, eta_apply, e1]

private theorem eta_pow_card [Finite K] (f : RingAut K) (ψ : Multiplicative K →* ℂˣ) (π : Ine (F := E) A →* Multiplicative K)
    (j : ℤ) (t : Ine (F := E) A) : eta f ψ π j t ^ Nat.card K = 1 := by
  have e : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
  rw [eta_apply, ← map_pow, ← e, pow_card_eq_one', map_one]

end

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

private noncomputable def cj (h : IsPlaceOver A w) (s : Ine (F := E) A) : Ine (F := E) A :=
  ⟨(frob h : G E Ω) * s * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 s.2⟩

private theorem ineIncl_cj (h : IsPlaceOver A w) (s : Ine (F := E) A) :
    ineIncl h (cj h s) = frob h * ineIncl h s * (frob h)⁻¹ := Subtype.ext rfl

private theorem eta_eq_of_wild [Finite K] (h : IsPlaceOver A w) (n : ℕ) (f : RingAut K) (ψ : Multiplicative K →* ℂˣ)
    (π : Ine (F := E) A →* Multiplicative K) (hcard : Nat.card K = normV w ^ n) (hord : orderOf f = n)
    (hπ : ∀ t t' : Ine (F := E) A, ineIncl h t' = frob h * ineIncl h t * (frob h)⁻¹ →
      π t' = ofAdd (f (toAdd (π t))))
    (hw : ∀ t : Ine (F := E) A, Formalism.MainNotions.BlochKatoReduction.IsWild A (t : G E Ω) → eta f ψ π 0 t = eta f ψ π 1 t) :
    eta f ψ π 0 = eta f ψ π 1 := by
  set χ : Ine (F := E) A →* ℂˣ := eta f ψ π 0 / eta f ψ π 1 with hχ
  have hχa : ∀ s, χ s = eta f ψ π 0 s / eta f ψ π 1 s := fun s => rfl
  have h1 : ∀ s, χ (cj h s) = χ s ^ normV w := fun s => by
    have e := hw _ (DiscreteGroups.sglob.DzType.isWild_frob (isFrob_frob (h := h)) s)
    have e' : eta f ψ π 0 (cj h s * (s ^ normV w)⁻¹) = eta f ψ π 1 (cj h s * (s ^ normV w)⁻¹) := e
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at e'
    rw [hχa, hχa, div_pow, div_eq_div_iff_mul_eq_mul]
    have e2 := mul_inv_eq_iff_eq_mul.1 e'
    rw [e2]
    simp [mul_comm, mul_left_comm, mul_assoc]
  have h2 : ∀ (k : ℕ) s, χ ((cj h)^[k] s) = χ s ^ normV w ^ k ∧
      π ((cj h)^[k] s) = ofAdd ((f ^ k) (toAdd (π s))) := fun k s => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', h1, ih.1, hπ _ _ (ineIncl_cj h _), ih.2, toAdd_ofAdd, pow_succ' f k]
      exact ⟨by rw [← pow_mul, pow_succ], rfl⟩
  have h3 : ∀ s s', π s = π s' → χ s = χ s' := fun s s' e => by
    rw [hχa, hχa, eta_apply, eta_apply, eta_apply, eta_apply, e]
  have h4 : ∀ s, χ s = 1 := fun s => by
    obtain ⟨e1, e2⟩ := h2 n s
    have e3 : π ((cj h)^[n] s) = π s := by
      rw [e2, ← hord, pow_orderOf_eq_one]
      rfl
    rw [h3 _ _ e3, ← hcard, hχa, div_pow, eta_pow_card, eta_pow_card, div_one] at e1
    exact e1
  exact MonoidHom.ext fun s => div_eq_one.1 (h4 s)

end

end UpperTheory.IrreducibleNonTameWeilDeligne

open UpperTheory.IrreducibleNonTameWeilDeligne Multiplicative in
theorem UpperTheory.tameInertiaCharacter_frobenius_conj_eq_pow :
    ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
        {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (n : ℕ), 2 ≤ n → ∀ (K : Type) [Field K] [Finite K] (f : RingAut K)
        (π : Ine (F := E) A →* Multiplicative K), Nat.card K = normV w ^ n → orderOf f = n → Function.Surjective π →
        IsOpen (π.ker : Set (Ine (F := E) A)) →
        (∀ t t' : Ine (F := E) A, ineIncl h t' = frob h * ineIncl h t * (frob h)⁻¹ →
          π t' = Multiplicative.ofAdd (f (Multiplicative.toAdd (π t)))) →
        ∃ J : WD h, IsIrrWD J ∧ J.lpDim = n ∧ (∀ σ, ‖(J.eig σ).prod‖ = 1) ∧
          ∀ (V : WD h) ξ hξ, IsTameWD V → J ≠ V.lpTwist ξ hξ := by
  intro E Ω _ _ _ _ _ A w h n hn K _ _ f π hcard hord hs ho hπ
  obtain ⟨ψ, hψ⟩ := UpperTheory.exists_addChar_invariant_iff_finiteField_aut_eq_one K f
  have bindC : ∀ m : Multiset ℂˣ, (do let x ← m; pure (x : ℂ) : Multiset ℂ) = m.map fun z : ℂˣ => (z : ℂ) :=
    fun m => Multiset.bind_singleton _ _
  have hiff : ∀ j j' : ℤ, eta f ψ π j = eta f ψ π j' ↔ (n : ℤ) ∣ j - j' := fun j j' => by
    rw [← hord]
    exact eta_eq_iff f ψ π hψ hs j j'
  have hopen : IsOpen ((eta f ψ π 0).ker : Set (Ine (F := E) A)) := by
    refine Subgroup.isOpen_mono (H₁ := π.ker) (fun t ht => ?_) ho
    rw [MonoidHom.mem_ker] at ht ⊢
    rw [eta_apply, ht]
    simp
  obtain ⟨J, hirr, hdim, hdet, hine, -⟩ := UpperTheory.Zero.LLC.indEx E Ω A w h (frob h) deg_frob n (by omega) (eta f ψ π) hopen
    (fun j t t' e => eta_succ f ψ π j (hπ t t' e)) hiff 1 one_ne_zero
  refine ⟨J, hirr, hdim, fun σ => ?_, fun V ξ hξ hV he => ?_⟩
  · obtain ⟨⟨δ, hδ⟩, -, -, -, -, -, -, hcl, -⟩ := UpperTheory.Zero.LLC.wDBasic E Ω A w h J
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    have hφ : δ (frob h) = 1 := Units.ext (by rw [← hδ, hdet]; rfl)
    have hm : J.inePol (τ : G E Ω) =
        (((Finset.range n).val.map fun j : ℕ => eta f ψ π j τ).map fun z : ℂˣ => X - C (z : ℂ)).prod := by
      rw [hine τ, Multiset.map_map]
      rfl
    have h1 := (hcl τ ((Finset.range n).val.map fun j : ℕ => eta f ψ π j τ) (by rw [bindC, Multiset.map_map]; exact hm)).1
    have h2 : δ (ineIncl h τ) ^ Nat.card K = 1 := by
      have e : δ (ineIncl h τ) = ∏ j ∈ Finset.range n, eta f ψ π j τ := Units.ext (by rw [← hδ, h1]; rfl)
      rw [e, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun j _ => eta_pow_card f ψ π j τ
    have h3 : δ σ = δ (ineIncl h τ) := by
      conv_lhs => rw [hτ]
      rw [map_mul, map_zpow, hφ, one_zpow, one_mul]
    rw [hδ, h3]
    refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card K) ?_ Nat.card_pos.ne'
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  · obtain ⟨t, htw, hne⟩ : ∃ t : Ine (F := E) A, Formalism.MainNotions.BlochKatoReduction.IsWild A (t : G E Ω) ∧ eta f ψ π 0 t ≠ eta f ψ π 1 t := by
      by_contra hall
      push_neg at hall
      have e := (hiff 0 1).1 (eta_eq_of_wild h n f ψ π hcard hord hπ hall)
      have e2 := Int.le_of_dvd (by norm_num) ((dvd_neg).2 e)
      norm_num at e2
      omega
    obtain ⟨m, b, hb, hb1⟩ := hV
    have hbt : b.ρ (ineIncl h t) = 1 := hb1 _ htw
    have hVp : V.inePol (t : G E Ω) = ((Multiset.replicate m (1 : ℂˣ)).map fun z : ℂˣ => X - C (z : ℂ)).prod := by
      rw [WD.inePol_of_mem_Ine V t.2, ← hb, WD.charPol_mk]
      show (b.ρ (ineIncl h t)).charpoly = _
      rw [hbt, LinearMap.charpoly_one]
      simp
    obtain ⟨-, -, -, -, -, -, -, hcl, -⟩ := UpperTheory.Zero.LLC.wDBasic E Ω A w h V
    have h3 := (hcl t (Multiset.replicate m (1 : ℂˣ)) (by rw [bindC, Multiset.map_map]; exact hVp)).2.2 ξ hξ
    rw [← he, hine t] at h3
    have hroot : ∀ j ∈ Finset.range n, eta f ψ π j t = ξ (ineIncl h t) := fun j hj => by
      have e := congrArg (eval ((eta f ψ π j t : ℂˣ) : ℂ)) h3
      rw [eval_prod, Finset.prod_eq_zero hj (by simp)] at e
      simp at e
      have e0 : ((eta f ψ π j t : ℂˣ) : ℂ) - (ξ (ineIncl h t) : ℂˣ) = 0 :=
        eq_zero_of_pow_eq_zero e.symm
      exact Units.ext (sub_eq_zero.1 e0)
    exact hne (by simpa using (hroot 0 (by simp; omega)).trans (hroot 1 (by simp; omega)).symm)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.eventually_unramified_satake_eigen_of_mem_cuspRep :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (f : Sm E 2), f ∈ P.V → ∀ h : GL (Fin 2) (A E), ∀ᶠ v : H.P ℚ in cofinite, H.Gd D.δ v ∧ ∀ w : H.P E, w.under (𝓞 ℚ) = v → Valued.v (H.cp w (rt D.θ)) ≤ 1 ∧ H.Fix w (fun g => f.1 (g * h)) ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B (fun g => f.1 (g * h)) := by
  intro E _ _ _ D P f hf h
  have hδ : D.δ ≠ 0 := (by
    intro e
    have := D.neg (algebraMap ℚ ℝ)
    rw [e, map_zero] at this
    exact lt_irrefl _ this)
  have hF : ∀ᶠ w : H.P E in cofinite, H.Fix w f.1 :=
    (H.aeK E).2.2 f.1 (by
      have hO : {k : GL (Fin 2) (Af E) | ∀ g, f.1 (g * finGL E 2 k) = f.1 g} = {k | finRep E 2 k f = f} :=
        Set.ext fun k => ⟨fun hk => Subtype.ext (funext hk), fun hk g => congrFun (congrArg Subtype.val hk) g⟩
      rw [hO]
      exact (P.cusp f hf).1.level)
  have hall : ∀ᶠ w : H.P E in cofinite, Valued.v (H.cp w (rt D.θ)) ≤ 1 ∧ H.Fix w (fun g => f.1 (g * h)) ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B (fun g => f.1 (g * h)) := by
    have hint : ∀ᶠ w : H.P E in cofinite, H.cp w (rt D.θ) ∈ w.adicCompletionIntegers E := (rt D.θ).2.2
    filter_upwards [hint, hF, (H.aeK E).1 h, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat P] with w h1 h2 h3 ⟨B, hB⟩
    have hE : EigAt w B f.1 := by
      have hSat := (CG.hasSat_mk P w B).1 hB
      intro g
      refine ⟨hSat.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
      · rw [map_mul, map_mul, ← mul_assoc]
        exact h2 _ k hk
      · by_cases h0 : f = 0
        · subst h0
          simp
        have he := (hSat.2 (⟨f, hf⟩ : P.V)
          (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (Subtype.ext (funext fun x => h2 x k hk)))
          fun h => h0 (congrArg Subtype.val h)).2.2.2 ϖ hϖ j hj
        let ev : P.V →+ ℂ :=
          { toFun := fun ψ => ψ.1.1 (g * finGL E 2 (locGL E 2 w y))
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2)
          (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (P.locRep w) ⟨f, hf⟩)
        refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans (congrArg ev he))
        rw [map_mul, map_mul, ← mul_assoc]
        rfl
    have ht := H.fixTr E w f.1 h h3
    exact ⟨h1, ht.1 h2, B, hB, ht.2 B hE⟩
  have hfin := (Set.Finite.image (fun w : H.P E => w.under (𝓞 ℚ)) (show Set.Finite _ from hall)).compl_mem_cofinite
  filter_upwards [H.gdAe ℚ D.δ hδ, hfin] with v hv hn
  refine ⟨hv, fun w hw => ?_⟩
  by_contra hc
  exact hn ⟨w, hc, hw⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma dL_mul {K : Type} [Field K] [NumberField K] {v : H.P K} (a d a' d' : (H.Kv v)ˣ) :
    H.dL a d * H.dL a' d' = H.dL (a * a') (d * d') := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma dL_one {K : Type} [Field K] [NumberField K] {v : H.P K} : (H.dL (1 : (H.Kv v)ˣ) 1) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL]

private lemma dL_nL {K : Type} [Field K] [NumberField K] {v : H.P K} (a : (H.Kv v)ˣ) (b : H.Kv v) :
    H.dL a 1 * H.nL b = H.nL ((a : H.Kv v) * b) * H.dL a 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL, H.nL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma hs_succ (a b : ℂ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1 + 1), a ^ i * b ^ (k + 1 - i) =
      b * ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) + a ^ (k + 1) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have : k + 1 - i = (k - i) + 1 := by
    have := Finset.mem_range.1 hi
    omega
  rw [this]
  ring

private lemma tor_loc (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ) (hϖ : H.IsU ϖ)
    (χ : H.Kv v → ℂ) (hχ : H.Good χ) (α β : ℂˣ) (W : GL (Fin 2) (H.Kv v) → ℂ)
    (hW : UpperTheory.V.Af.Smo.Eig v {α, β} W) (hn : ∀ b y, W (H.nL b * y) = χ b * W y) (k : ℕ) :
    (H.q v ^ (1 / 2 : ℂ)) ^ k * W (H.dL (ϖ ^ k) 1) =
      (∑ i ∈ Finset.range (k + 1), ((α : ℂ)) ^ i * ((β : ℂ)) ^ (k - i)) * W 1 := by
  obtain ⟨R, hcard, hRint, hR⟩ := UpperTheory.ConvolutionTheory.R2.H.heckeExpl K v ϖ hϖ
  have hsum := fun g => (hR α β W hW g).1
  have hcen := fun g => (hR α β W hW g).2
  obtain ⟨t1, -⟩ := UpperTheory.ConvolutionTheory.R2.H.whTorus K v ϖ hϖ χ hχ α β W hW hn
  have hint : ∀ c : H.Kv v, H.IsInt c → ∀ y, W (H.nL c * y) = W y := fun c hc y => by
    rw [hn, hχ.2.1 c hc, one_mul]
  have hϖint : H.IsInt (ϖ : H.Kv v) := by
    have h' : Valued.v (ϖ : H.Kv v) = _ := hϖ
    show Valued.v (ϖ : H.Kv v) ≤ 1
    rw [h']
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  have hq0 : H.q v ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.cast_ne_zero.2 this
  set s : ℂ := H.q v ^ (1 / 2 : ℂ) with hs
  have hss : s * s = H.q v := by
    rw [hs, ← Complex.cpow_add _ _ hq0]
    norm_num
  have hs0 : s ≠ 0 := fun h => hq0 (by rw [← hss, h, zero_mul])
  have hconst : ∀ x : ℂ, ∑ _b ∈ R, x = H.q v * x := fun x => by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rfl
  have hrec : ∀ k : ℕ, s * ((α : ℂ) + β) * W (H.dL (ϖ ^ (k + 1)) 1) =
      H.q v * W (H.dL (ϖ ^ (k + 1 + 1)) 1) + (α : ℂ) * β * W (H.dL (ϖ ^ k) 1) := fun k => by
    have h2 := hsum (H.dL (ϖ ^ (k + 1)) 1)
    have t3 : ∀ b ∈ R, W (H.dL (ϖ ^ (k + 1)) 1 * H.nL b * H.dL ϖ 1) = W (H.dL (ϖ ^ (k + 1 + 1)) 1) := fun b hb => by
      rw [dL_nL, mul_assoc, hint _ ?_, dL_mul, mul_one, ← pow_succ]
      have hb' : ((ϖ : H.Kv v) ^ (k + 1)) * b ∈ v.adicCompletionIntegers K :=
        mul_mem (pow_mem (show (ϖ : H.Kv v) ∈ v.adicCompletionIntegers K from hϖint) _)
          (show b ∈ v.adicCompletionIntegers K from hRint b hb)
      rw [Units.val_pow_eq_pow_val]
      exact hb'
    rw [Finset.sum_congr rfl t3, hconst] at h2
    have t4 : W (H.dL (ϖ ^ (k + 1)) 1 * H.dL 1 ϖ) = (α : ℂ) * β * W (H.dL (ϖ ^ k) 1) := by
      have := hcen (H.dL (ϖ ^ k) 1)
      rw [dL_mul, one_mul, ← pow_succ] at this
      rw [dL_mul, mul_one, one_mul]
      exact this
    rw [t4] at h2
    exact h2
  have h3 : s * W (H.dL ϖ 1) = ((α : ℂ) + β) * W 1 := by
    refine mul_left_cancel₀ hs0 ?_
    rw [← mul_assoc, hss, ← mul_assoc]
    exact t1
  have key : ∀ k : ℕ, s ^ (k + 1) * W (H.dL (ϖ ^ (k + 1)) 1) =
      β * (s ^ k * W (H.dL (ϖ ^ k) 1)) + (α : ℂ) ^ (k + 1) * W 1 := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add, pow_one, pow_zero, one_mul, dL_one]
      rw [h3]
      ring
    | succ k ih =>
      have h := hrec k
      rw [← hss] at h
      linear_combination (α : ℂ) * ih - s ^ k * h
  induction k with
  | zero => simp [dL_one]
  | succ k ih =>
    rw [key, ih, hs_succ]
    ring

theorem UpperTheory.eigenform_shintani_formula_at_place :
    ∀ (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ), H.IsU ϖ → ∀ (χ : H.Kv v → ℂ), H.Good χ → ∀ (α β : ℂˣ) (f : GL (Fin 2) (A K) → ℂ),
          EigAt v {α, β} f → (∀ b h, f (H.lc v (H.nL b) * h) = χ b * f h) → ∀ g, H.KAt v g → ∀ k : ℕ,
          (H.q v ^ (1 / 2 : ℂ)) ^ k * f (aE (H.idl v ϖ ^ k) * g) = (∑ i ∈ Finset.range (k + 1), ((α : ℂ)) ^ i * ((β : ℂ)) ^ (k - i)) * f g := by
  intro K _ _ v ϖ hϖ χ hχ α β f hB hn g hg k
  have hE1 : UpperTheory.V.Af.Smo.Eig v {α, β} fun x => f (H.lc v x * g) := by
    have := (H.fixTr K v f g hg).2 _ hB 1
    simpa [H.lc] using this
  have hnl : ∀ b x, f (H.lc v (H.nL b * x) * g) = χ b * f (H.lc v x * g) := fun b x => by
    rw [map_mul, mul_assoc, hn]
  have h := tor_loc K v ϖ hϖ χ hχ α β _ hE1 hnl k
  have e : H.idl v (ϖ ^ k) = H.idl v ϖ ^ k := map_pow _ _ _
  beta_reduce at h
  rw [(H.lcLaws K v).2.2.2.1, e, map_one, one_mul] at h
  exact h
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittakerCoeff_ne_zero_finiteAdele_mem_compact :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), IsAutForm f → Pp.Lf f.1 →
        ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧
          ∀ (y : (A ℚ)ˣ), ∀ k ∈ C, Wo D f.1 (em E (aE y) * k) ≠ 0 → (y : A ℚ).2 ∈ K := by
  intro E _ _ _ D f hf hL C hC
  obtain ⟨N, hN, hfN⟩ := UpperTheory.exists_level_unipotent_invariance_automorphicForm E D f hf C hC
  obtain ⟨K, hK, hKN⟩ := UpperTheory.exists_isCompact_annihilator_scaled_integralAdeles N hN
  refine ⟨K, hK, fun y k hk hW => hKN _ fun b hb => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : A ℚ, x = ((0, (N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) : A ℚ) := ⟨_, rfl⟩
  have h1 : Wo D f.1 (em E (aE y) * k) = Wo D f.1 (em E (aE y) * gl (nU (D.mkE 0 x)) * k) := by
    have pt : ∀ G, f.1 (G * (em E (aE y) * k)) = f.1 (G * (em E (aE y) * gl (nU (D.mkE 0 x)) * k)) := by
      intro G
      have h := hfN k hk b hb (G * em E (aE y))
      rw [← hx] at h
      simp only [mul_assoc] at h ⊢
      exact h.symm
    simp only [Wo]
    congr 1
    funext u
    rw [pt]
  rw [UpperTheory.embedGL2_diag_mul_unipotent_theta_eq, mul_assoc, UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D f.1 hL] at h1
  have h2 : ψ (-((y : A ℚ) * x)) = 1 := by
    have h3 : ψ (-((y : A ℚ) * x)) * Wo D f.1 (em E (aE y) * k) = 1 * Wo D f.1 (em E (aE y) * k) := by
      rw [one_mul]
      exact h1.symm
    exact mul_right_cancel₀ hW h3
  have h4 : ψ ((y : A ℚ) * x) = 1 := by
    have h5 := Pp.ψ_add ((y : A ℚ) * x) (-((y : A ℚ) * x))
    have h6 : ψ (0 : A ℚ) = 1 := by
      have := Pp.ψ_rt (0 : ℚ)
      simpa using this
    rw [add_neg_cancel, h6, h2, mul_one] at h5
    exact h5.symm
  have h7 : (y : A ℚ) * x = ((0, (y : A ℚ).2 * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b)) : A ℚ) := by
    rw [hx]
    exact Prod.ext (mul_zero _) rfl
  rw [← h7]
  exact h4
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.lseries_summable_sq_coeff_of_four_lt_re :
    ∀ (N : ℕ) (s : ℂ), 4 < s.re → LSeriesSummable (sqN N) s := by
  intro N s hs
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) (by linarith)
  unfold sqN
  split_ifs <;> simp
end
