module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pPhiTy :
    PPart → LevSec → FacEq → UpperTheory.Gal.W2.Seed.LocComm → PhiTy := by
  intro hP hL hF hc E _ _ _ A n p _ S F x U w₀ Up V _ _ _ hOff _ r W hAux N hN hStab L hw Ty hTy
  have hj : F.j = F.tr.j := F.j_tr
  have h4 : ∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) →
      (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ GlobalTheory.LFun.KGL w (n := n)) →
      ∀ g, V.Φ (CertificateRingHomMap.th (g * k)) = V.Φ (CertificateRingHomMap.th g) := by
    intro k h1 h2 g
    have hk : CertificateRingHomMap.th k ∈ lev V.S V.Kw :=
      (hL E A n p S F.tr V.S V.Kw hOff.1).2 _
        (fun w hw' => by rw [CertificateRingHomMap.comp_th, h1 w hw', map_one])
        (fun w hw' => by rw [CertificateRingHomMap.comp_th]; exact CertificateRingHomMap.invT_mem_KGL (h2 w hw'))
        (fun u _ => one_mem _)
    have e : comp w₀ (CertificateRingHomMap.th k) = 1 := by rw [CertificateRingHomMap.comp_th, h1 _ hw.2, map_one]
    have hJ : comp w₀ (CertificateRingHomMap.th k) ∈ V.J := e ▸ one_mem _
    have hχ : V.χ ⟨comp w₀ (CertificateRingHomMap.th k), hJ⟩ = 1 := by
      have : (⟨comp w₀ (CertificateRingHomMap.th k), hJ⟩ : V.J) = 1 := Subtype.ext e
      rw [this, map_one]
    rw [map_mul, V.form.right _ hk hJ, hχ]
    simp
  have h3 : ∀ g : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g ∈ GlobalTheory.LFun.KGL w (n := n)) →
      V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j g))) = V.Φ (CertificateRingHomMap.th g) := by
    intro g hg
    obtain ⟨k, e, k1, k2, -⟩ := hP E A n p S F.tr g
    have := h4 k k1 (fun w hw' => by rw [k2 w hw']; exact hg w hw') (F.tr.sec (F.tr.j g))
    rw [← e] at this
    rw [hj]
    exact this.symm
  refine ⟨?_, ?_, h3, h4⟩
  · obtain ⟨g₀, h0, hg⟩ := hOff.2
    intro hz
    apply h0
    have e := congrFun hz (F.j (CertificateRingHomMap.th g₀))
    have e' : V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j (CertificateRingHomMap.th g₀)))) = 0 := e
    rw [h3 _ (fun w hw' => by rw [CertificateRingHomMap.comp_th]; exact CertificateRingHomMap.invT_mem_KGL (hg w hw')), CertificateRingHomMap.th_th] at e'
    exact e'
  · intro k hk g
    obtain ⟨⟨k', e, hk'⟩, -⟩ := (hTy.K_iff k).1 hk
    rw [th_eq] at hk'
    have hs : F.tr.sec k ∈ lev V.S (CertificateRingHomMap.levT V.Kw) := by
      have := (hL E A n p S F.tr V.S (CertificateRingHomMap.levT V.Kw) hOff.1).1 k' (CertificateRingHomMap.th_mem_lev.1 hk')
      rwa [← hj, e] at this
    have hs' := CertificateRingHomMap.th_mem_lev.2 hs
    have hpr : Ty.L.pr k = comp w₀ (F.tr.sec k) := by
      have h := (hF E A n p S F hc ⟨w₀, hw⟩).2 _ (hTy.fac ⟨w₀, hw⟩)
      rw [hTy.L_eq, h]
      rfl
    have hyy : (comp w₀ (CertificateRingHomMap.th (F.tr.sec k))).val = ((Ty.L.pr k)⁻¹).valᵀ := by
      rw [CertificateRingHomMap.comp_th, CertificateRingHomMap.invT_val, hpr]
    have hyJ : Ty.L.pr k ∈ Ty.J := Ty.fact.2 k hk
    have hJ' : comp w₀ (CertificateRingHomMap.th (F.tr.sec k)) ∈ V.J := (hTy.J_iff _ _ hyy).1 hyJ
    show V.Φ (CertificateRingHomMap.th (F.tr.sec (g * k))) = ((Ty.ψ ⟨Ty.L.pr k, Ty.fact.2 k hk⟩ : ℂˣ) : ℂ) • V.Φ (CertificateRingHomMap.th (F.tr.sec g))
    rw [map_mul, map_mul, V.form.right _ hs' hJ', hTy.ψ_eq ⟨_, hyJ⟩ ⟨_, hJ'⟩ hyy]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pFacEq :
    FacEq := by
  intro E _ _ _ A n p _ S F hc w
  have h1 : IsFac F w (fac F.tr hc w) := by
    refine ⟨fun g => ?_, fun y => ?_⟩
    · have e : F.tr.j (F.tr.sec (F.tr.j g)) = F.tr.j g := F.tr.j_sec _
      have := (F.tr.j_eq _ _).1 e w.1 w.2.2
      rw [F.j_tr]
      exact this
    · rw [F.j_tr]
      rfl
  refine ⟨h1, fun L hL => ?_⟩
  have hpr : L.pr = (fac F.tr hc w).pr := MonoidHom.ext fun h => by
    obtain ⟨g, rfl⟩ := F.surj h
    rw [hL.1 g, h1.1 g]
  have hloc : L.loc = (fac F.tr hc w).loc := MonoidHom.ext fun y => by
    rw [hL.2 y, h1.2 y]
  cases hf : fac F.tr hc w with
  | mk pr loc pr_loc comm =>
    cases L with
    | mk pr' loc' pr_loc' comm' =>
      rw [hf] at hpr hloc
      simp only at hpr hloc
      subst hpr hloc
      rfl
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pMemFn :
    SeenShape → SeenActs → ActsConv → TyFact → MemFn := by
  intro hSh hAc hAC hTF E _ _ _ A n p _ S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨-, hcase⟩ := hSh E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨hsupp, hdeck, hgen⟩ := hAc E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨tf1, tf2, -⟩ := hTF E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy
  rcases hcase with ⟨hD, hh, hθ⟩ | ⟨w, t, z, i, B, hFree, hAp, -, -, -, -, -, hinv, hCen, hWpr, hFg, -⟩
  · have hA := hdeck hD hh
    have hhK : g.h ∈ Ty.K := ((Ty.mem_kerK _).1 hh).1
    refine ⟨hA.1, ?_, Or.inl ⟨hD, hθ, ?_⟩⟩
    · intro a ha u hu
      obtain ⟨k, hk, hka⟩ := hsupp a ha
      have haK : a ∈ Ty.K := by
        have e : a = (g.h * k)⁻¹ * (g.h * k * a) := by group
        rw [e]
        exact Ty.K.mul_mem (Ty.K.inv_mem (Ty.K.mul_mem hhK hk)) hka
      exact (tf1 u hu).1.2 a haK
    · have e := (hAC _ _ Ty _ _ _ hA).1
      rwa [one_smul] at e
  · obtain ⟨hfac, hap⟩ := tf2 w hFree.2.1 hFree.2.2.1 hAp
    have hA := hgen _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hfac hFg hap hCen hinv
    have hpr : Ty.L.pr g.h = 1 := by
      have e := hA.2.1
      rwa [map_inv, inv_eq_one] at e
    refine ⟨hA.1, ?_, Or.inr ⟨hpr, hWpr, (hAC _ _ Ty _ _ _ hA).1⟩⟩
    intro a ha u hu
    obtain ⟨k, hk, hka⟩ := hsupp a ha
    have f := (tf1 u hu).1.2
    have e : (L u).pr (g.h * k * a) = (L u).pr k * (L u).pr a := by
      rw [map_mul, map_mul, hWpr u hu, one_mul]
    have h6 := f _ hka
    rw [e] at h6
    exact (Subgroup.mul_mem_cancel_left _ (f k hk)).1 h6
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Gal.W2.Seed.mem_cj_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (hG : UpperTheory.Gal.CertificateRingHomMap.LocComm)
    {q : ℕ} [Fact q.Prime] {w : Plc E} (hw : IsSplitAt w) (h : (q : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∈ (CertificateRingHomMap.cj w).asIdeal := by
  by_contra hn
  have hap : GlobalTheory.Cong.Apart w (CertificateRingHomMap.cj w) := UpperTheory.Gal.W2.Seed.apart_of_not_mem hn h
  obtain ⟨-, -, -, hs, hcc, -⟩ := hG E n w hw
  exact ((hG E n (CertificateRingHomMap.cj w) hs).2.1 w).1 hap |>.2 hcc.symm

theorem UpperTheory.Gal.W2.Seed.pTyFact :
    FacEq → LevSec → LevFact → AtApart → CongGrpEx → Denom → UpperTheory.Gal.W2.Seed.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocComm → TyFact := by
  intro hF hS hLF hA hC hD hc hG E _ _ _ A n p _ S F x U w₀ Up V _ _ _ hOff _ r W hAux N _ _ L hw Ty hTy
  have hj : F.j = F.tr.j := F.j_tr
  have hL : ∀ w, L w = fac F.tr hc w := fun w => (hF E A n p S F hc w).2 _ (hTy.fac w)
  haveI : Fact r.Prime := ⟨hAux.prime⟩
  have hK1 : ∀ k, (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ↔ k ∈ F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw)) := by
    intro k
    constructor
    · rintro ⟨k', rfl, h⟩
      rw [th_eq, CertificateRingHomMap.th_mem_lev] at h
      rw [hj]
      exact (hS E A n p S F.tr V.S _ hOff.1).1 k' h
    · intro h
      refine ⟨F.tr.sec k, by rw [hj]; exact F.tr.j_sec k, ?_⟩
      rw [th_eq, CertificateRingHomMap.th_mem_lev]
      exact h
  have hKiff : ∀ k, k ∈ Ty.K ↔ k ∈ F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw)) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1 :=
    fun k => (hTy.K_iff k).trans (and_congr_left' (hK1 k))
  have hIK : ∀ w : Plc E, Iw n w ≤ GlobalTheory.LFun.KGL w (n := n) := fun w => by
    obtain ⟨K, -, -, -, -, -, -, h⟩ := hC E n 1 one_pos w
    exact h
  have hnS : ∀ w ∈ W, w.1 ∉ V.S ∧ CertificateRingHomMap.cj w.1 ∉ V.S := fun w hw' =>
    ⟨fun h => hAux.off _ h (hAux.half.above w hw'),
      fun h => hAux.off _ h (mem_cj_of_mem n hG w.2.1 (hAux.half.above w hw'))⟩
  have hAw₀ : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S → GlobalTheory.Cong.Apart w₀ w.1 := fun w h1 h2 =>
    ((hG E n w.1 w.2.1).2.1 w₀).2 ⟨fun e => h1 (e ▸ V.shape.mem), fun e => h2 (e ▸ V.shape.mem)⟩
  have hAp : ∀ w w' : Spl E p, GlobalTheory.Cong.Apart w.1 w'.1 → (L w).Apart (L w') := fun w w' h => by
    rw [hL, hL]
    exact (hA E A n p S F.tr hc w.1 w.2.1 w.2.2).2 w'.1 w'.2.1 w'.2.2 h
  have hLF' : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S →
      (L w).Fact (F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw))) (GlobalTheory.LFun.KGL w.1 (n := n)) := fun w h1 h2 => by
    rw [hL]
    exact (hLF E A n p S F.tr hc V.S (CertificateRingHomMap.levT V.Kw) w.1 w.2.1 w.2.2 h2).2 h1
  have hTyAp : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S → Ty.L.Apart (L w) := fun w h1 h2 => by
    rw [hTy.L_eq]
    exact hAp ⟨w₀, hw⟩ w (hAw₀ w h1 h2)
  refine ⟨fun w hw' => ⟨⟨fun y hy => ?_, fun g hg => ((hKiff g).1 hg).2 w hw'⟩, hTyAp w (hnS w hw').1 (hnS w hw').2,
      fun w' hw'' e => hAp w w' (hAux.half.apart w hw' w' hw'' e)⟩,
    fun w h1 h2 h3 => ⟨⟨fun y hy => (hKiff _).2 ⟨(hLF' w h1 h2).1 y hy, fun u hu => ?_⟩,
      fun g hg => (hLF' w h1 h2).2 g ((hKiff g).1 hg).1⟩, hTyAp w h1 h2⟩, ?_⟩
  · refine (hKiff _).2 ⟨(hLF' w (hnS w hw').1 (hnS w hw').2).1 y (hIK w.1 hy), fun w' hw'' => ?_⟩
    by_cases e : w = w'
    · subst e
      rw [(L w).pr_loc]
      exact hy
    · rw [(hAp w' w (hAux.half.apart w' hw'' w hw' (Ne.symm e))).1 y]
      exact one_mem _
  · rw [(hAp w u (h3 u hu)).2 y]
    exact one_mem _
  · haveI : (Ty.K₀.subgroupOf Ty.K).FiniteIndex := ⟨Ty.idx⟩
    haveI : Fintype (Ty.K ⧸ Ty.K₀.subgroupOf Ty.K) := Fintype.ofFinite _
    choose c hc0 hcp hcv using fun q : Ty.K ⧸ Ty.K₀.subgroupOf Ty.K => hD p S.D S.G S.L (q.out : S.G.GAf)
    refine ⟨∏ q, c q, Finset.prod_pos fun q _ => hc0 q, Nat.Coprime.prod_left fun q _ => hcp q, fun k hk v hv => ?_⟩
    obtain ⟨q, hq⟩ : ∃ q : Ty.K ⧸ Ty.K₀.subgroupOf Ty.K, q = QuotientGroup.mk ⟨k, hk⟩ := ⟨_, rfl⟩
    have hu : (q.out : S.G.GAf)⁻¹ * k ∈ Ty.K₀ := by
      have : q.out⁻¹ * ⟨k, hk⟩ ∈ Ty.K₀.subgroupOf Ty.K := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', hq]
      simpa [Subgroup.mem_subgroupOf] using this
    have hint : Integ S.L ((q.out : S.G.GAf)⁻¹ * k) := integ_of_mem (KN_anti (one_dvd N.1) (hTy.K₀_eq ▸ hu))
    have hk' : k = (q.out : S.G.GAf) * ((q.out : S.G.GAf)⁻¹ * k) := by group
    have h1 := hcv q _ (hint v hv)
    rw [hk', map_mul, Module.End.mul_apply, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ q), mul_comm, mul_smul]
    exact nsmul_mem h1 _
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem vN_le_one (N : ℕ) (w : Plc E) : Valued.v (N : w.adicCompletion E) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (natCast_mem (w.adicCompletionIntegers E) N)

private theorem vN_ne_zero {N : ℕ} (hN : 0 < N) (w : Plc E) : Valued.v (N : w.adicCompletion E) ≠ 0 := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hN.ne')

private theorem vN_lt_one {N : ℕ} (w : Plc E) (h : (N : 𝓞 E) ∈ w.asIdeal) :
    Valued.v (N : w.adicCompletion E) < 1 := by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((N : 𝓞 E) : E)) = w.valuation E ((N : 𝓞 E) : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : algebraMap E (w.adicCompletion E) ((N : 𝓞 E) : E) = (N : w.adicCompletion E) := by simp
  rw [← h2, h1]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 h

private theorem entry_mul_le {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    {r s : WithZero (Multiplicative ℤ)} (hA : ∀ i j, Valued.v (A i j) ≤ r) (hB : ∀ i j, Valued.v (B i j) ≤ s)
    (i j : Fin n) : Valued.v ((A * B) i j) ≤ r * s := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA _ _) (hB _ _)

private theorem cong_one (N : ℕ) (w : Plc E) : Cong1 N w (1 : GL (Fin n) (w.adicCompletion E)) := fun i k => by
  simp

private theorem cong_mul {N : ℕ} {w : Plc E} {x y : GL (Fin n) (w.adicCompletion E)}
    (hx : Cong1 N w x) (hy : Cong1 N w y) : Cong1 N w (x * y) := fun i k => by
  have e : (x * y).val - 1 = (x.val - 1) * (y.val - 1) + (x.val - 1) + (y.val - 1) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := vN_le_one (E := E) N w
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (hx i k)) (hy i k)
  exact (entry_mul_le hx hy i k).trans (mul_le_of_le_one_left' h)

private theorem cong_conj {N : ℕ} {w : Plc E} {a y : GL (Fin n) (w.adicCompletion E)}
    (ha : a ∈ KGL w (n := n)) (hy : Cong1 N w y) : Cong1 N w (a * y * a⁻¹) := fun i k => by
  have e : (a * y * a⁻¹).val - 1 = a.val * (y.val - 1) * (a⁻¹).val := by
    have h : a.val * (a⁻¹).val = 1 := by rw [← Units.val_mul]; simp
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, h]
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 ha
  have h1' : ∀ i j, Valued.v (a.val i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (h1 i j)
  have h2' : ∀ i j, Valued.v ((a⁻¹).val i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (h2 i j)
  rw [e]
  simpa using entry_mul_le (entry_mul_le h1' hy) h2' i k

private theorem cong_entry {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} (hy : Cong1 N w y) (i j : Fin n) :
    Valued.v (y.val i j) ≤ max (Valued.v (N : w.adicCompletion E)) (Valued.v ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) := by
  have e : y.val i j = (y.val - 1) i j + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by simp
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le_max_right _ (hy i j))

private theorem cong_int {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} (hy : Cong1 N w y) (i j : Fin n) :
    y.val i j ∈ w.adicCompletionIntegers E := by
  refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 ((cong_entry hy i j).trans (max_le (vN_le_one N w) ?_))
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

private def congGrp (N : ℕ) (w : Plc E) : Subgroup (GL (Fin n) (w.adicCompletion E)) where
  carrier := {y | Cong1 N w y ∧ Cong1 N w y⁻¹}
  one_mem' := ⟨cong_one N w, by simpa using cong_one N w⟩
  mul_mem' := fun {x y} hx hy => ⟨cong_mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact cong_mul hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by simpa using hx.1⟩

private theorem isOpen_ball {w : Plc E} {c : w.adicCompletion E} (hc : c ≠ 0) :
    IsOpen {x : w.adicCompletion E | Valued.v x ≤ Valued.v c} := by
  have h0 : IsOpen ((w.adicCompletionIntegers E : Set (w.adicCompletion E))) :=
    Valued.isOpen_valuationSubring _
  have h1 : {x : w.adicCompletion E | Valued.v x ≤ Valued.v c} =
      (fun x => c⁻¹ * x) ⁻¹' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    ext x
    have hv : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w,
      map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
  rw [h1]
  exact h0.preimage (continuous_const.mul continuous_id)

private theorem isOpen_cong {N : ℕ} (hN : 0 < N) (w : Plc E) :
    IsOpen {y : GL (Fin n) (w.adicCompletion E) | Cong1 N w y} := by
  have hc : (N : w.adicCompletion E) ≠ 0 := fun h => vN_ne_zero hN w (by rw [h, map_zero])
  have e : {y : GL (Fin n) (w.adicCompletion E) | Cong1 N w y} =
      ⋂ i, ⋂ k, (fun y : GL (Fin n) (w.adicCompletion E) => (y.val - 1) i k) ⁻¹'
        {x | Valued.v x ≤ Valued.v (N : w.adicCompletion E)} := by
    ext y
    simp [Cong1]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => (isOpen_ball hc).preimage ?_
  exact ((Units.continuous_val.sub continuous_const).matrix_elem i k)

private theorem isOpen_congGrp {N : ℕ} (hN : 0 < N) (w : Plc E) :
    IsOpen (congGrp (n := n) N w : Set (GL (Fin n) (w.adicCompletion E))) :=
  (isOpen_cong hN w).inter ((isOpen_cong hN w).preimage continuous_inv)

private theorem congGrp_le (N : ℕ) (w : Plc E) : congGrp (n := n) N w ≤ KGL w (n := n) := fun _ hy =>
  GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨cong_int hy.1, cong_int hy.2⟩

private theorem congGrp_le_iw {N : ℕ} (w : Plc E) (hN : (N : 𝓞 E) ∈ w.asIdeal) : congGrp (n := n) N w ≤ Iw n w := by
  intro y hy
  have hK : y ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion]
    exact congGrp_le N w hy
  refine GlobalTheory.SmGL.mem_iwahori.2 ⟨hK, fun i j hij => ?_⟩
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one]
  have h0 : (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0 := Matrix.one_apply_ne hij.ne'
  refine (cong_entry hy.1 i j).trans_lt (max_lt (vN_lt_one w hN) ?_)
  simp [h0]

theorem pCongGrpEx : CongGrpEx := by
  intro E _ _ _ n N hN w
  refine ⟨congGrp N w, fun y => Iff.rfl, isOpen_congGrp hN w, ?_, congGrp_le N w, ?_, fun h => congGrp_le_iw w h,
    fun y hy => ?_⟩
  · exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (isOpen_congGrp hN w)) (congGrp_le N w)
  · intro a ha y
    have key : ∀ a ∈ KGL w (n := n), ∀ y, y ∈ congGrp N w → a * y * a⁻¹ ∈ congGrp N w := fun a ha y hy =>
      ⟨cong_conj ha hy.1, by
        have : (a * y * a⁻¹)⁻¹ = a * y⁻¹ * a⁻¹ := by group
        rw [this]; exact cong_conj ha hy.2⟩
    refine ⟨fun h => ?_, key a ha y⟩
    have := key a⁻¹ (inv_mem ha) _ h
    simpa [mul_assoc] using this
  · have := GlobalTheory.SmGL.iwahori_le_KO _ _ hy
    rwa [GlobalTheory.SmGL.SphCompletion.KO_completion] at this

end UpperTheory.Gal.W2.Seed
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCuspTh :
    CuspTh := by
  intro E _ _ _ n w σ
  let σ' : SmIrr (GLw n w) :=
    { V := σ.V
      ρ := σ.ρ.comp (invT n (w.adicCompletion E))
      smooth := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isSmooth_comp_invT σ.smooth
      irred := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isIrreducible_comp_invT σ.irred }
  refine ⟨σ', LinearEquiv.refl ℂ _, fun g g' v h => ?_, fun hc => ?_⟩
  · have hg : g' = invT n (w.adicCompletion E) g := Units.ext h
    subst hg
    show σ.ρ (invT n _ (invT n _ g)) v = σ.ρ g v
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
  · have h2 := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isCuspidal_comp_invT (ρ := σ'.ρ) hc
    have h3 : σ'.ρ.comp (invT n (w.adicCompletion E)) = σ.ρ :=
      MonoidHom.ext fun g => by
        show σ.ρ (invT n _ (invT n _ g)) = σ.ρ g
        rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
    rwa [h3] at h2
end
