module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartPhiE
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle015
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
import Aesop.Frontend.Tactic
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle016
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Formalism.L2.Theta

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
theorem idemSum_of_noConj (S : Finset (Formalism.L2.DIV.Pl D.host.E))
    (hnc : ∀ P ∈ S, ∀ P' ∈ S, ¬ Lev.IsConjPl (D := D) P P') :
    ∃ e : AE D, Formalism.IndefR.Datum.IsIdemSum e S := by
  let es : Formalism.L2.DIV.Pl D.host.E → AE D := fun PP =>
    if h : ¬ Lev.IsConjPl (D := D) PP PP then (idem_exists_at PP h).choose else 0
  have hes : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP := by
    intro PP hPP
    have h := hnc PP hPP PP hPP
    simp only [es, dif_pos h]
    exact (idem_exists_at PP h).choose_spec.1
  refine ⟨∑ PP ∈ S, es PP, ⟨es, hes, rfl⟩, ?_⟩

  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_eq_zero
  intro PP hPP
  apply Finset.sum_eq_zero
  intro PP' hPP'
  exact idem_orth_conj (hnc PP hPP PP hPP) (hes PP hPP) (hes PP' hPP') (hnc PP hPP PP' hPP')

theorem g_mem_of_div (C : Formalism.L2.Host.CharFrame D) {k : Fin 2} {PP : Formalism.L2.DIV.Pl D.host.E} (h : C.P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := C.P.pb_over k
  rw [← h] at h1
  have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := h1
  simpa [Ideal.mem_comap] using h2

section Links

open Formalism.IndefR.Links

variable {T : Type}

theorem disjoint_Pg_Q (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) : Disjoint L.Pg (L.Q t) := by
  rw [Finset.disjoint_left]
  intro P hP hPQ
  obtain ⟨i, hi⟩ := (hL.Pg P).1 hP
  obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hL.Q_pl t P hPQ
  exact Formalism.IndefR.Fin.not_two_primes P.isPrime.ne_top (D.host.g_prime i) hq (fun h => hqg i h.symm)
    (g_mem_of_div L.C hi) (char_mem hq hcard)

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Links

end Formalism.IndefR.Fin
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem pin_eq {P Q : HeightOneSpectrum (𝓞 D.host.E)} {x : AE D} (hP : Formalism.L2.NTheta.IsIdemAt x P)
    (hQ : Formalism.L2.NTheta.IsIdemAt x Q) : P = Q := by
  have h : P.asIdeal = Q.asIdeal := by
    ext x
    by_cases hx : x = 0
    · subst hx
      exact ⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩
    · rw [hP.2 x hx, hQ.2 x hx]
  exact HeightOneSpectrum.ext h

theorem conj_idem_eq {P Q : HeightOneSpectrum (𝓞 D.host.E)} {x y : AE D} (hx : Formalism.L2.NTheta.IsIdemAt x P)
    (hy : Formalism.L2.NTheta.IsIdemAt y Q) (hc : Lev.IsConjPl (D := D) P Q) : y = cA D x := by
  have hsp := idemAt_split hx
  obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hsp (belowPl P) rfl
  have hx0 : x = e₀ := idemAt_eq_split hsp hx he₀
  have hle : (belowPl P).asIdeal ≤ (belowPl Q).asIdeal := by
    intro f hf
    obtain ⟨c, hc', hce⟩ := hc _ hf
    have : c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f := by
      apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
      show (c : D.host.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f : 𝓞 D.host.E) : D.host.E)
      rw [hce, algebraMap_O]
      exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f ∈ Q.asIdeal
    rw [← this]; exact hc'
  have hbel : belowPl Q = belowPl P :=
    (HeightOneSpectrum.ext ((belowPl P).isMaximal.eq_of_le (belowPl Q).isPrime.ne_top hle)).symm
  have hs' := below_of_idemAt hy
  rw [hbel] at hs'
  rcases idem_class P hsp e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 y hy.1.1 hy.1.2.1 hs' with h | h
  · exfalso
    rw [← hx0] at h
    have hPQ : P = Q := pin_eq hx (h ▸ hy)
    subst hPQ
    exact hsp hc
  · rw [h, hx0]

private theorem ne_zero_of_isIdemAt' {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  intro h0
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have h := (he.2 c hc0).1 hcP
  rw [h0, zero_mul] at h
  first
  | exact h (by simp)
  | simp at h
  | exact h (map_zero (finPart D) ▸ (intAE D).zero_mem)

private theorem not_isConjPl_of_isIdemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : ¬ Lev.IsConjPl (D := D) P P := by
  intro hc
  have h1 : e = cA D e := conj_idem_eq he he hc
  have h2 : e * cA D e = 0 := he.1.2.1
  rw [← h1, he.1.1] at h2
  exact ne_zero_of_isIdemAt' he h2

theorem idemSum_orth (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : Formalism.IndefR.Datum.IsIdemSum e P) :
    ∃ es : Formalism.L2.DIV.Pl D.host.E → AE D, (∀ PP ∈ P, IsSplitIdem D (es PP)) ∧ e = ∑ PP ∈ P, es PP ∧
      ∀ PP ∈ P, ∀ PP' ∈ P, PP ≠ PP' → es PP * es PP' = 0 ∧ es PP * cA D (es PP') = 0 := by
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  refine ⟨es, fun PP hPP => (hes PP hPP).1, hsum, fun PP hPP PP' hPP' hne => ⟨?_, ?_⟩⟩
  · exact idem_orth (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes PP' hPP') hne
  · by_cases hcj : Lev.IsConjPl (D := D) PP PP'
    · exfalso
      have hy : es PP' = cA D (es PP) := conj_idem_eq (hes PP hPP) (hes PP' hPP') hcj
      have hL : es PP * e = es PP := by
        rw [hsum, Finset.mul_sum, Finset.sum_eq_single PP]
        · exact (hes PP hPP).1.1
        · intro b hb hbne
          exact idem_orth (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes b hb) (Ne.symm hbne)
        · intro h; exact absurd hPP h
      have hR : es PP * cA D e = es PP := by

        rw [hsum, map_sum, Finset.mul_sum, Finset.sum_eq_single PP']
        · rw [hy, cA_cA]; exact (hes PP hPP).1.1
        · intro b hb hbne
          by_cases hb0 : b = PP
          · rw [hb0]; exact (hes PP hPP).1.2.1
          · refine idem_orth_conj (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes b hb) (fun hcb => hbne ?_)
            have hyb : es b = cA D (es PP) := conj_idem_eq (hes PP hPP) (hes b hb) hcb
            rw [← hy] at hyb
            have hb' := hes b hb
            rw [hyb] at hb'
            exact pin_eq hb' (hes PP' hPP')
        · intro h; exact absurd hPP' h
      have h0 : es PP * (e * cA D e) = 0 := by rw [hc, mul_zero]
      rw [← mul_assoc, hL, hR] at h0
      exact ne_zero_of_isIdemAt' (hes PP hPP) h0
    · exact idem_orth_conj (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes PP' hPP') hcj

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitOrInert (D : D7) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∃ PP : HeightOneSpectrum (𝓞 D.host.E), PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal ∧
      ¬ Lev.IsConjPl (D := D) PP PP) ∨
    ∀ e : AE D, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0


open Classical in
theorem sbHalf_halfInd {S T : HSp D} (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  unfold IsSBHalf halfInd
  refine ⟨?_, 1, one_pos, ?_⟩
  · intro t ht
    by_contra hn
    apply ht
    simp [hn]
  · refine ⟨?_, ?_⟩
    · intro u hu hh t
      have hΛ : t + 1 • u ∈ Λ ↔ t ∈ Λ := by
        rw [one_smul]
        exact ⟨fun h => by simpa using Λ.sub_mem h hu, fun h => Λ.add_mem h hu⟩
      have hH : IsHalf e (t + 1 • u) ↔ IsHalf e t := by
        unfold IsHalf at hh ⊢
        simp only [one_smul, Matrix.add_apply, Pi.add_apply, mul_add, hh, add_left_inj]
      simp only [hΛ, hH]
    · intro t ht
      rw [one_smul]
      by_contra hn
      apply ht
      simp [hn]

theorem fix_split (hSL : SplitLin D) (hPM : PlaceModelAt D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {PP : Formalism.L2.DIV.Pl D.host.E} {e' : AE D}
    (he' : Formalism.L2.NTheta.IsIdemAt e' PP) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀)
    (hlat : IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀)
    (hn : ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1)
    {g : GA D S} {h : GA D T} (hg : SuppAt e' S g) (hh : SuppAt e' T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e' S g x) (hy : IsDetAt e' T h y) (hfac : splitFacO χS χT x y = 1)
    (hpres : ∀ t : WO S T, IsHalf e' t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT))
    (hpres' : ∀ t : WO S T, IsHalf e' t → (actO S T g⁻¹ h⁻¹ t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT)) :
    om (g, h) f₀ = f₀ := by
  classical
  have hsp : IsSplitIdem D e' := he'.1
  have hsum : IsIdemSum e' {PP} := by
    refine ⟨⟨fun _ => e', fun Q hQ => ?_, by simp⟩, hsp.2.1⟩
    rw [Finset.mem_singleton] at hQ
    subst hQ
    exact he'
  have hvac : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e' u ∨ IsHalf (cA D e') u) →
      heisO ψ S T u f₀ = f₀ := by
    intro u hu hh
    rcases hh with hh | hh
    · exact hlat.2 e' hsp u hu hh
    · exact hlat.2 (cA D e') (isSplitIdem_cA hsp) u hu hh
  obtain ⟨Tm, hTm, -, -, -⟩ :=
    hPM ψ hW.std S T ΛS ΛT hsS hsT {PP} e' hsum f₀ hf₀ hvac e' (Or.inl rfl)
  obtain ⟨r, -, hrep, hr1⟩ := hSL ψ S T χS χT om hW ΛS ΛT hsS hsT {PP} e' hsum f₀ hf₀ hvac Tm hTm
    e' hsp hsp.1 g h hg hh x y hx hy
  have hr : r = 1 := hr1 hpres hn
  have hΦ : IsSBHalf e' (latAll S T ΛS ΛT) ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) := by
    rw [one_smul]
    exact sbHalf_halfInd e' _
  have hinv : (fun t => ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) (actO S T g⁻¹ h⁻¹ t)) =
      (1 : ℂ) • halfInd e' (latAll S T ΛS ΛT) := by
    funext t
    simp only [one_smul, halfInd]
    by_cases ht : IsHalf e' t
    · have h1 : IsHalf e' (actO S T g⁻¹ h⁻¹ t) := (isHalf_actO g⁻¹ h⁻¹ t).2 ht
      simp only [hpres' t ht, h1, ht, and_true]
    · have h1 : ¬ IsHalf e' (actO S T g⁻¹ h⁻¹ t) := fun h' => ht ((isHalf_actO g⁻¹ h⁻¹ t).1 h')
      simp only [h1, ht, and_false, if_false]
  calc om (g, h) f₀ = om (g, h) (Tm ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT))) := by rw [hTm.vac]
    _ = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) •
          Tm (fun t => ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) (actO S T g⁻¹ h⁻¹ t)) := hrep _ hΦ
    _ = f₀ := by
      rw [hinv, hTm.vac, hr, hfac]
      simp

theorem latO_le_all {S T : HSp D} (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T ΛS ΛT P ≤ latO S T ΛS ΛT (fun _ => True) := by
  unfold latO
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, h1, h2⟩
  refine ⟨α, hα, ?_, h2⟩
  intro v
  first
    | exact fun h => absurd trivial h
    | simp
    | simp_all
    | aesop

theorem fix_inert {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hI : WeilFull.SphInertAtO ψ S T χS χT om)
    (hrk : S.rank ≠ T.rank) (hev : Even S.rank ∨ Even T.rank)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hfS : Formalism.L2.DIV.IsFrame βS ΛS) (hfT : Formalism.L2.DIV.IsFrame βT ΛT) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal)
    (hin : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0)
    (huS : WeilFull.UnrAtV ε χS) (huT : WeilFull.UnrAtV ε χT) {g : GA D S} {h : GA D T}
    (hg : WeilFull.SuppV ε S g) (hh : WeilFull.SuppV ε T h) (hgS : Lev.finE S g ∈ Formalism.L2.DIV.St βS)
    (hhT : Lev.finE T h ∈ Formalism.L2.DIV.St βT) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀)
    (hlat : IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀) : om (g, h) f₀ = f₀ := by
  have key : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun w => w = v) f₀ := by
    clear * - hlat
    unfold IsLatVac at *
    exact ⟨fun u hu => hlat.1 u (latO_le_all (S := S) (T := T) ΛS ΛT _ hu),
      fun e he u hu hh => hlat.2 e he u (latO_le_all (S := S) (T := T) ΛS ΛT _ hu) hh⟩
  exact hI hrk hev ΛS ΛT hsS hsT βS βT hfS hfT v ε hε h2 hin huS huT g h hg hh hgS hhT f₀ hf₀ key

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct ComplexConjugate ContDiff

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem trace_fst_eq_zero (z : AE D) (hz : infPart D z = 0) :
    fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) = 0 := by
  have hc : ∀ k, fstA D.host.F (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k) = 0 := fun k => by
    show (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k).1 = 0
    rw [← Formalism.IndefR.PHeisTh.repr_fst]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := hz
    rw [this, map_zero]; rfl

  rw [← (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).sum_repr z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  have : (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr z k = Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k := rfl
  rw [this, hc, zero_mul]

theorem trace_snd_eq_zero (z : AE D) (hz : finPart D z = 0) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) = 0 := by
  have hc : ∀ k, sndA D.host.F (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k) = 0 := fun k => by
    show (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k).2 = 0
    rw [← Formalism.IndefR.PHeisTh.repr_snd]
    have : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := hz
    rw [this, map_zero]; rfl

  rw [← (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).sum_repr z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  have : (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr z k = Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k := rfl
  rw [this, hc, zero_mul]

variable (S T : HSp D)


theorem infPart_hO (u w : MO S T) (hu : u.map (infPart D) = 0) : infPart D (hO S T u w) = 0 := by
  have h0 : ∀ d a, infPart D (u d a) = 0 := fun d a => congrFun (congrFun hu d) a
  unfold hO

  simp only [map_sum (infPart D), map_mul (infPart D), h0, mul_zero, Finset.sum_const_zero]


theorem finPart_hO (u w : MO S T) (hu : u.map (finPart D) = 0) : finPart D (hO S T u w) = 0 := by
  have h0 : ∀ d a, finPart D (u d a) = 0 := fun d a => congrFun (congrFun hu d) a
  unfold hO

  simp only [map_sum (finPart D), map_mul (finPart D), h0, mul_zero, Finset.sum_const_zero]


theorem symplO_fst_eq_zero (u w : MO S T) (hu : u.map (infPart D) = 0) : fstA D.host.F (symplO S T u w) = 0 := by
  unfold symplO
  refine trace_fst_eq_zero _ ?_
  rw [map_mul (infPart D), infPart_hO S T u w hu, mul_zero]


theorem symplO_snd_eq_zero (u w : MO S T) (hu : u.map (finPart D) = 0) : sndA D.host.F (symplO S T u w) = 0 := by
  unfold symplO
  refine trace_snd_eq_zero _ ?_
  rw [map_mul (finPart D), finPart_hO S T u w hu, mul_zero]

theorem symplOH_snd_eq_zero (u w : MO S T) (hu : u.map (finPart D) = 0) : sndA D.host.F (symplOH S T u w) = 0 := by
  unfold symplOH
  rw [map_mul, symplO_snd_eq_zero S T u w hu, mul_zero]

def sndSympl (w : MO S T) : MO S T →+ Af D.host.F where
  toFun u := sndA D.host.F (symplO S T u w)
  map_zero' := by rw [symplO_zero_left, map_zero]
  map_add' u u' := by rw [symplO_add_left, map_add (f := _)]

theorem heisStable : HeisStable D := by
  intro ψ hψ S T w f hf
  obtain ⟨G, hGo, -, hG⟩ := Formalism.IndefR.PHeisTh.psiOpen D.host.F ψ hψ.1
  obtain ⟨U, hUo, hU⟩ := hf.level
  let H : AddSubgroup (WO S T) := AddSubgroup.comap (sndSympl S T w) G
  have hHo : IsOpen (H : Set (WO S T)) :=
    hGo.preimage (continuous_snd.comp (cont_symplO_left S T w))
  refine ⟨fun γ z => ?_, ⟨U ⊓ H, ?_, fun u hu h0 => ?_⟩, cont_heis S T hψ hf w, fun k L hL hL0 x => ?_⟩
  ·
    unfold heisO
    rw [show ratW T S γ + z + w = ratW T S γ + (z + w) by abel, hf.quasi γ (z + w), ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul]
    have key : symplOH S T (ratW T S γ + z) w + -symplOH S T (ratW T S γ) (z + w) =
        -symplOH S T (ratW T S γ) z + symplOH S T z w := by
      rw [symplOH_add_left, symplOH_add_right]; ring
    rw [key]
  · rw [AddSubgroup.coe_inf]; exact hUo.inter hHo
  ·
    have hfu := hU u hu.1 h0
    have hc : ψ (symplO S T u w) = 1 := by
      have e : symplO S T u w = pairA D.host.F 0 (sndA D.host.F (symplO S T u w)) := by
        refine Prod.ext ?_ rfl
        exact symplO_fst_eq_zero S T u w h0
      rw [e]; exact hG _ hu.2
    funext z
    have k1 := congrFun hfu (z + w)
    unfold heisO at k1 ⊢
    have hfz : f (z + w + u) = ψ (-(symplOH S T (z + w) u)) * f (z + w) := by
      rw [AddChar.map_neg_eq_inv, ← k1]; field_simp [psi_ne hψ]
    rw [show z + u + w = z + w + u by abel, hfz, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul]
    have key : symplOH S T z u + symplOH S T (z + u) w + -symplOH S T (z + w) u =
        symplOH S T z w + symplO S T u w := by
      rw [symplOH_add_left, symplOH_add_left, symplOH_swap S T u w, ← symplOH_two]; ring
    rw [key, AddChar.map_add_eq_mul, hc, mul_one]
  ·
    let s : (Fin k → ℝ) →+ Ainf D.host.F :=
      { toFun := fun t => fstA D.host.F (symplOH S T (L t) w)
        map_zero' := by simp only [map_zero]; unfold symplOH; rw [symplO_zero_left, mul_zero, map_zero]
        map_add' := fun t t' => by simp only [map_add (f := _)]; rw [symplOH_add_left, map_add (f := _)] }
    have hs : Continuous s := continuous_fst.comp ((cont_symplOH_left S T w).comp hL)
    have e : (fun t => heisO ψ S T w f (x + L t)) =
        fun t => ψ (symplOH S T x w) * ψ (pairA D.host.F (s t) 0) * f (x + w + L t) := by
      funext t
      unfold heisO
      have ep : symplOH S T (L t) w = pairA D.host.F (s t) 0 :=
        Prod.ext rfl (symplOH_snd_eq_zero S T (L t) w (hL0 t))
      rw [symplOH_add_left, AddChar.map_add_eq_mul, ep, show x + L t + w = x + w + L t by abel]
    rw [e]
    exact (contDiff_const.mul (Formalism.IndefR.PHeisTh.psiSmooth D ψ hψ k s hs)).mul (hf.smooth k L hL hL0 (x + w))

end Formalism.IndefR.Fin

end
end
