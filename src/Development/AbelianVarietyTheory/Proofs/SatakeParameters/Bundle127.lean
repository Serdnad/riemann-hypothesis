module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle102
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle122
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordsB_recWord_of_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m)
    (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C →
    11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  intro D L hP C C₂ j ε n g ψ l hR hO hC hl hlA hord
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := by
    funext a
    rw [hg a]
    rfl
  generalize g 0 = τ at hgl
  subst hgl
  have hjA : jA L l = depth L l := GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth L l hl hlA
  have hA := GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit L hP C j ε τ ψ l hR hl hlA hord
  obtain ⟨_, _, hjn, _, hcl⟩ := hA
  have hD := GlobalTheory.T.leastPowerDepth_spec L hP l hl
  have hth : ThickN (recWord L j ε (letter τ ψ)).b
      (recWord L j ε (letter τ ψ)).η (recWord L j ε (letter τ ψ)).sz =
      (pageWord L j ε τ ψ).thick := by
    funext a
    exact propext (GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hjA]; exact hjn
  · rcases le_or_gt 0 C₂ with h0 | h0
    · rw [hjA]
      exact GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L C₂ C (depth L l) hR h0 hC hD.2.1
    · have h1 : (0 : ℝ) ≤ ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) := by
        positivity
      have h2 : C₂ * ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) ≤ 0 := by
        rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg h0.le h1
      exact h2.trans (Nat.cast_nonneg _)
  · rw [hth, hjA]; exact hcl

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem sum_count_Icc (s : Multiset ℤ) (η : ℕ) :
    ∑ u ∈ Finset.Icc (-(η : ℤ)) η, ((s.count u : ℕ) : ℤ) =
      ((s.filter fun u : ℤ => |u| ≤ (η : ℤ)).card : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    by_cases hx : |x| ≤ (η : ℤ)
    · have hm : x ∈ Finset.Icc (-(η : ℤ)) η := Finset.mem_Icc.2 (abs_le.1 hx)
      rw [Multiset.filter_cons_of_pos (p := fun u : ℤ => |u| ≤ (η : ℤ)) _ hx, Multiset.card_cons, ← Finset.add_sum_erase _ _ hm,
        Multiset.count_cons_self]
      have he : ∑ u ∈ (Finset.Icc (-(η : ℤ)) η).erase x, ((Multiset.count u (x ::ₘ s) : ℕ) : ℤ) =
          ∑ u ∈ (Finset.Icc (-(η : ℤ)) η).erase x, ((Multiset.count u s : ℕ) : ℤ) :=
        Finset.sum_congr rfl fun u hu => by
          rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hu)]
      rw [he]
      push_cast
      rw [← ih, ← Finset.add_sum_erase _ _ hm]
      ring
    · have hm : x ∉ Finset.Icc (-(η : ℤ)) η := fun h => hx (abs_le.2 (Finset.mem_Icc.1 h))
      rw [Multiset.filter_cons_of_neg (p := fun u : ℤ => |u| ≤ (η : ℤ)) _ hx, ← ih]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Multiset.count_cons_of_ne (fun h => hm (by rw [← h]; exact hu))]

theorem letter_one_zero {φ : Formalism.HC.Frame} (τ : φ.GG) : letter τ 1 (0 : ZMod (orderOf (1 : φ.GG))) = τ := by
  simp [letter]

theorem recWord_jumps : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG), Roomy L C → ∀ a, (∀ u ∈ jT1 (hcAt D (g a)) j (pos ε (g a)), u ∈ (recWord L j ε g).win a ∧ u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ)) ∧ (∀ u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)), u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))) ∧ ∑ u ∈ Finset.Icc (-(etaHat L : ℤ)) (etaHat L), (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) ≤ D.R.m := by
  intro D L C j ε n g hR a
  obtain ⟨hT1, hbox⟩ := GlobalTheory.T.twistedDualPageWord_jumps_in_windows L C j ε (g a) 1 hR
  obtain ⟨hT2, hcard⟩ := GlobalTheory.T.pageWord_T2_and_J2_card_of_roomy L C j ε (g a) 1 hR
  obtain ⟨hsz, hMi, hhi, -⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g a) 1 hR 0
  have hl := letter_one_zero (g a)
  have t1 := hT1 0
  have t2 := hT2 0
  have bx := hbox 0
  have cd := (hcard 0).2
  simp only [pageWord, recWord, WordData.Mi, WordData.hi, hl] at t1 t2 bx cd hsz hMi hhi
  refine ⟨fun u hu => ?_, fun u hu => (t2.1 u hu), ?_⟩
  · have h1 := t1 u hu
    have h2 := bx u hu
    refine ⟨?_, ?_⟩
    · simp only [NWord.win, recWord, Set.mem_setOf_eq]
      rw [hsz]
      exact h1
    · simp only [recWord, Set.mem_Icc]
      rw [hMi, hhi]
      exact h2
  · rw [sum_count_Icc, cd]

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  intro R H l _ K LL c κ τ
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  obtain ⟨σ, hσ⟩ := GlobalTheory.HTW.exists_aut_comp_eq_of_normal κ ((τ : ↥K.1 →+* ↥LL.1).comp c)
  obtain ⟨g, hg⟩ := (H.gal).symm.surjective σ
  have hg' : H.sigmaOf g = σ := hg
  refine ⟨g, fun x => ?_, fun g' hg2 => ?_⟩
  · rw [hg']
    exact hσ x
  · have e : H.sigmaOf g' = H.sigmaOf g := by
      refine AlgEquiv.ext fun x => ?_
      apply κ.injective
      rw [← hg2 x, hg']
      exact hσ x
    exact (H.gal).symm.injective e

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopXiInv

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc

theorem xiTop_invariant : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (u : Pr.Word), Pr.Ok → R.m = m2 + 2 → cst.Ok → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : TopPt R sel mu u), Y ∈ ybSet sel mu cst p.deco.1.N → ∀ x z, z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → _root_.GlobalTheory.TopStep.XiTop Ch sel mu cst m2 p Y p' (x + z) = _root_.GlobalTheory.TopStep.XiTop Ch sel mu cst m2 p Y p' x := by
  classical
  intro X Pr R Ch sel S mu cst m2 u hPr hm hc hD p Y p' hY x y hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  set c : ℕ := cBof sel mu cst u with hcdef
  change _root_.GlobalTheory.TopStep.XiTop Ch sel mu cst m2 p Y p' (x + (c : 𝓞 X.E) • y₀) = _
  unfold _root_.GlobalTheory.TopStep.XiTop
  refine congrArg₂ (· * ·) ?_ ?_
  · refine GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
    have h1 : Pr.piT u ∈ P.1.asIdeal := by
      have h := P.2
      unfold Primes.vT divs at h
      split_ifs at h with hf
      · simpa using h
      · simp at h
    rw [hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
  · refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 := GlobalTheory.TopInv.qOf_ne P.1
    rw [GlobalTheory.TopInv.inFr_add]
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) x = x'
    have hz : ∀ v : Sp X.E (R.N (m2 + 1)), (∀ l, IntAt P.1 (v l)) → ∀ l,
        IntAt P.1 (inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l / (qOf P.1 : X.E) ^ cst.B) := by
      intro v hv l
      have h1 : frsF sel mu p P v ∈ p.deco.1.at P.1 := (frsF_mem p P v).2 ((mem_localization_standardLattice _ _).2 hv)
      have h2 := hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1
      have h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) ∈ stdAt X.E _ P.1 := by
        refine (frsF_mem p' P _).1 ?_
        rw [LinearEquiv.apply_symm_apply]
        exact h2
      have h4 := (mem_localization_standardLattice _ _).1 h3 l
      obtain ⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c :=
        Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
      have h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l =
          (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) l := by
        change (frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P v)) l = _
        rw [equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]
      rw [h5, hc']
      convert (GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1
      push_cast
      field_simp
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) = z at hz ⊢
    unfold locTop
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine GlobalTheory.TopInv.PhiTop_add mu Ch _ _ hm P.1 _ _ fun s l => ?_
      have h1 := hz (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s 1)) fun l' =>
        GlobalTheory.TopInv.single_int s _
      have h2 := GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos (h1 (Br.iC (N_m_succ R) l))
      rw [pow_one] at h2
      exact h2
    · refine GlobalTheory.TopInv.ftY_add sel mu cst hc P (hD P) _ _ _ (fun s => ?_) ?_
      · exact GlobalTheory.TopInv.atNL_int (R.N R.m - 1) _ _ (hz (Pi.single s 1) (GlobalTheory.TopInv.single_int s))
      · have h1 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
        have h2 := (frsF_mem p P ((frsF sel mu p P).symm
          (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Y))).1 (by
            rw [LinearEquiv.apply_symm_apply]
            exact h1)
        intro l
        have h3 := (mem_localization_standardLattice _ _).1 h2 l
        rw [map_smul] at h3
        exact h3

end GlobalTheory.TopXiInv
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.SumRowType

variable {E : Type} [Field E]

theorem atN_sumE_last {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t : ℕ) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) n = if n = t then 1 else 0 := by
  rw [Loc.atN, dite_eq_left (Nat.lt_succ_self n)]
  have h := sumE_last (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)
  have e : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Br.iL (rfl : n + 1 = n + 1) := rfl
  rw [e, h, Units.val_one, one_mul]
  rfl

theorem atN_sumE_up {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t s : ℕ) (hs : s < n) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) s = Loc.atN (j (Loc.eN E n t)) s := by
  rw [Loc.atN, dite_eq_left (by omega), Loc.atN, dite_eq_left hs]
  have h := congrFun (prH_sumE (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)) ⟨s, hs⟩
  have e1 : prH E (rfl : n + 1 = n + 1) (Loc.eN E (n + 1) t) = Loc.eN E n t := by
    funext i
    rw [prH_apply]
    rfl
  rw [e1] at h
  rw [← h, prH_apply]
  rfl

end GlobalTheory.SumRowType

namespace GlobalTheory.SumRowType

open Matrix in
theorem det_sumE {E : Type} [Field E] {n : ℕ} (r : ℕ) (hr : r ≤ n) (j : Sp E n ≃ₗ[E] Sp E n) :
    (Matrix.of fun s t : Fin (n + 1 - r) =>
        Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1).toLinearMap (Loc.eN E (n + 1) (r + t.1))) (r + s.1)).det =
      (Matrix.of fun s t : Fin (n - r) => Loc.atN (j.toLinearMap (Loc.eN E n (r + t.1))) (r + s.1)).det := by
  obtain ⟨m, rfl⟩ : ∃ m, n = r + m := ⟨n - r, by omega⟩
  have hm : r + m + 1 - r = m + 1 := by omega
  have hm' : r + m - r = m := by omega
  set A := Matrix.of fun s t : Fin (r + m + 1 - r) =>
    Loc.atN ((sumE (rfl : r + m + 1 = r + m + 1) j 1).toLinearMap (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) with hA
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm).symm A]
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm').symm]
  rw [Matrix.det_succ_row _ (Fin.last m)]
  rw [Finset.sum_eq_single (Fin.last m)]
  · have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) (Fin.last m) = 1 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + m))) (r + m) = 1
      rw [atN_sumE_last, if_pos rfl]
    rw [e1, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, one_mul]
    congr 1
    ext s t
    show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) =
      Loc.atN (j (Loc.eN E (r + m) (r + t.1))) (r + s.1)
    exact atN_sumE_up j _ _ (by have := s.2; omega)
  · intro b _ hb
    have hb' : b.1 < m := Fin.val_lt_last hb
    have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) b = 0 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + b.1))) (r + m) = 0
      rw [atN_sumE_last, if_neg (by omega)]
    rw [e1, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lamQB_sumE : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  intro E K _ _ _ _ P ξ N n hN r hr j
  subst hN
  unfold LocE.lamQB
  rw [det_sumE r hr j]

end GlobalTheory.SumRowType
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.supercuspidalSupport_of_lengthOne_langlandsDatum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c : ℕ) (Δ : Fin c → Segment k) (x : IrrGL (k := k)), (∀ i, (Δ i).len = 1) →
    IsL ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) x.rep →
    HasSupport x.rep (Finset.univ.val.map fun i => (Δ i).first) := by
  first | (exact @GlobalTheory.LocGL.LenOneSupport.hasSupport_first_of_isL_len_one) | (exact GlobalTheory.LocGL.LenOneSupport.hasSupport_first_of_isL_len_one) | (intros; apply GlobalTheory.LocGL.LenOneSupport.hasSupport_first_of_isL_len_one  <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.TorusEigenform

section General

variable {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] [AddCommGroup V] [Module ℂ V]

theorem exists_char_of_isIrreducible {σ : Representation ℂ G V} (hs : IsSmooth σ) (hi : σ.IsIrreducible) :
    ∃ μ : G →* ℂˣ, ∀ g w, σ g w = (μ g : ℂ) • w := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h : ∀ g, ∃ c : ℂ, ∀ w, σ g w = c • w := fun g =>
    LocGL.exists_eq_smul_of_isSmooth hs hi
      ⟨σ g, fun a => by rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_comm]⟩
  choose c hc using h
  let m : G →* ℂ :=
    { toFun := c
      map_one' := smul_left_injective ℂ hv (by simp [← hc])
      map_mul' := fun a b => smul_left_injective ℂ hv (by
        show c (a * b) • v = (c a * c b) • v
        rw [← hc, map_mul, Module.End.mul_apply, hc b, hc a, smul_smul]) }
  exact ⟨m.toHomUnits, fun g w => hc g w⟩

theorem exists_eigenform {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) {x : V} (hx : x ≠ 0)
    (hxH : ∀ t ∈ H, ρ t x = (χ t : ℂ) • x) :
    ∃ (μ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (μ g : ℂ) * l v) ∧ ∀ h ∈ H, μ h = χ h := by
  let ρ' := twist ρ χ⁻¹
  have hρ' : ∀ g v, ρ' g v = ((χ g)⁻¹ : ℂˣ) • ρ g v := fun _ _ => rfl
  have hc := LocGL.isCompl_fixed_twKer (isSmooth_twist hρ hχ.inv) hH
  let T : Subrepresentation ρ := ⟨twKer ρ' H 1, fun g v hv => by
    have h1 : ρ' g v ∈ twKer ρ' H 1 :=
      twKer_le_comap ρ' H g (by rw [Subgroup.normalizer_eq_top]; trivial) hv
    have h2 := (twKer ρ' H 1).smul_mem (χ g : ℂ) h1
    rwa [hρ', ← Units.smul_def, smul_inv_smul] at h2⟩
  have hT : T ≠ ⊤ := fun h => by
    have h1 : x ∈ T.toSubmodule := by rw [h]; trivial
    have h2 : x ∈ fixed ρ' H := fun t => by
      rw [hρ', hxH t t.2, ← Units.smul_def, inv_smul_smul]; simp
    exact hx ((Submodule.disjoint_def.1 hc.disjoint) x h2 h1)
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom T).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  refine ⟨μ, l, hl0, hle, fun h hh => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hl0 (LinearMap.ext hn)
  have h1 : ρ' h v - v ∈ T.toSubmodule := Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩
  have h2 := hlM (hTM h1)
  rw [LinearMap.mem_ker, map_sub, hρ', Units.smul_def, map_smul, hle, sub_eq_zero, smul_eq_mul,
    ← mul_assoc] at h2
  have h3 := mul_right_cancel₀ hv (h2.trans (one_mul _).symm)
  rw [← Units.val_mul, Units.val_eq_one, inv_mul_eq_one] at h3
  exact h3.symm

end General

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountableTopology_units : SecondCountableTopology kˣ := by
  have : SecondCountableTopology k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance
  exact Units.isEmbedding_val₀.secondCountableTopology


variable {k} in
theorem isSmoothChar_torusChar {n : ℕ} {θ : Fin n → kˣ →* ℂˣ} (hθ : ∀ i, IsSmoothChar (θ i)) :
    IsSmoothChar (_root_.GlobalTheory.SmGL.torusChar θ) :=
  Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) (by
    show IsOpen _
    rw [MonoidHom.ker_one]
    exact isOpen_univ) fun i _ => (hθ i).comp _ (continuous_apply i)

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (_root_.GlobalTheory.SmGL.torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (_root_.GlobalTheory.SmGL.torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  intro k _ _ _ _ n V _ _ ρ x θ hρ hl hθ hx hxH
  haveI := secondCountableTopology_units k
  obtain ⟨μ, l, hl0, hle, hμ⟩ := exists_eigenform hρ hl (SmGL.UnramFixed.isCompact_torusO k (Fin n))
    (isSmoothChar_torusChar hθ) hx hxH
  refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i), l, hl0, fun t y => ?_, fun i u hu => ?_⟩
  · rw [hle, _root_.GlobalTheory.SmGL.torusChar_apply]
    conv_lhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  · have h := hμ (Pi.mulSingle i u) fun j => by
      by_cases h : j = i
      · subst h; simpa using hu
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [_root_.GlobalTheory.SmGL.torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Pi.mulSingle_eq_same] at h
    exact h

end GlobalTheory.TorusEigenform
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.mem_supercuspidalSupport_of_torus_jacquet_eigenform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 → (∀ t y, l (jacB π t y) = (_root_.GlobalTheory.SmGL.torusChar ψ t : ℂ) * l y) → ∀ i, InSupport π (ψ i) := by
  first | exact @GlobalTheory.EigenSupport.inSupport_of_torus_eigenform | exact GlobalTheory.EigenSupport.inSupport_of_torus_eigenform | (intros; apply GlobalTheory.EigenSupport.inSupport_of_torus_eigenform <;> assumption)
end
