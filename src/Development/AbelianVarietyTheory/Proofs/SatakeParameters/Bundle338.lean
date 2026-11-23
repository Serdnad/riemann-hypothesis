module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle136
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle223
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle314
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle330
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle301
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle325
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle335
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle332
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle331
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle333
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (κ : ((St i hi).K β).lev.U),
    x₁.1 = x.1 * κ.1 → ∀ p p₁, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (dep : SB t μ → ℕ), dep P = 1 → ∀ (Gg : GLint t.X.E (D.R.N i) P.1),
      InFrame t.seam (A.fb i hi β) dep P κ.1 Gg.1 →
      ∃ k : GLint t.X.E (D.R.N i) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
        redGL _ P.1 k = redGL _ P.1 Gg) := by
  first | exact @GlobalTheory.LevFrame.frame_lev | exact GlobalTheory.LevFrame.frame_lev | (intros; apply GlobalTheory.LevFrame.frame_lev <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TieUnr



theorem mt_eq_one_of_intUnit : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → (∀ v, UnderSB t μ v → Formalism.UG.prV (E := D.host.E) v ((Matrix.GeneralLinearGroup.det y.1 : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1) → (t.O u μ).mt (i + 1) (dtU y) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint hsupp
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  obtain ⟨x', hx'int, hx'h90, hx'supp⟩ := GlobalTheory.T.integral_h90_preimage_trivial_at_places_over_trivial D.host.F D.host.E (sigD D) (GlobalTheory.T.cmData_conj_isConjOf _ _ D.sp.cm)
    (GlobalTheory.HeckeAdjoint.unramified_host D) _ hzU hint
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom x' with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = x' := by
    ext
    simp [x]
  have hq : A.q x = dtU y := H.q_dt x y (by rw [hxx, hx'h90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hx'int.1
    · simpa [x] using hx'int.2

  have hsub : ∀ {K : Type} [Field K] [NumberField K] (w : FiniteAdeleRing (𝓞 K) K) (P : HeightOneSpectrum (𝓞 K)),
      (w - 1) P = w P - 1 := fun _ _ => rfl
  have hsuppX : ∀ Q : HeightOneSpectrum (𝓞 t.X.E), (∃ P ∈ SB t μ, P.under (𝓞 t.X.F) = Q.under (𝓞 t.X.F)) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q = 1 := by
    rintro Q ⟨P, hP, hPQ⟩
    have hxm1 : (x : AfE t.X.F t.X.E) - 1 ∈ RInt t.X.F t.X.E := sub_mem hxint.1 (one_mem _)
    have key := GlobalTheory.T.afIso_ringEquiv_eq_zero_iff t.X.F t.X.E D.host.F D.host.E t.seam.iE A.iA H.iA_rat H.iA_int _ hxm1 Q
    have e1 : A.iA ((x : AfE t.X.F t.X.E) - 1) = (x' : AfE D.host.F D.host.E) - 1 := by
      rw [map_sub, map_one]
      simp [x]
    rw [e1] at key
    have hA : GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) Q =
        GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q - 1 := by
      rw [map_sub, map_one]; rfl
    have hB : GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) =
        GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (x' : AfE D.host.F D.host.E) (seamP t.seam Q) - 1 := by
      rw [map_sub, map_one]; rfl
    rw [← sub_eq_zero, ← hA]
    refine key.1 ?_
    show GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) = 0
    rw [hB, sub_eq_zero]
    refine hx'supp _ fun R hR => ?_
    have hv : UnderSB t μ ((seamP t.seam Q).under (𝓞 D.host.F)) := by
      refine ⟨P, hP, ?_⟩
      show ((seamP t.seam Q).under (𝓞 D.host.F)).asIdeal = ((seamP t.seam P).under (𝓞 D.host.F)).asIdeal
      rw [GlobalTheory.T.columnPrimeToBasePrime_preserves_common_place D t.X t.seam t.seam_ok H.fields.ok P Q hPQ]
    exact (GlobalTheory.T.placeComponent_eq_one_iff_components_over_eq_one _ _ _ _).1 (hsupp _ hv) R hR
  have hvG : ∀ P : HeightOneSpectrum (𝓞 t.X.E), (∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) P = 1 := by
    rintro P ⟨k, hk⟩
    obtain ⟨P', hP', hu⟩ := GlobalTheory.T.exists_typePrime_under_eq t.X t.Pr H.fields.ok t.pr_ok k P hk
    refine hsuppX P ⟨P', Finset.mem_union_left _ ?_, hu⟩
    fin_cases k
    · exact Finset.mem_union_left _ hP'
    · exact Finset.mem_union_right _ hP'
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∀ j : Fin D.R.m, D.muTil (j.1 + 1) (A.q x) = 1 := by
    intro j
    rw [H.muTil _ hiso j (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    refine Units.ext ?_
    have h1 := GlobalTheory.Mem.ReadEx.map_toIdl_eq_one (H.mu0 j).tame hxint (fun P hP => ?_)
    · rw [h1]
    · have hg : ∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
        by_contra hc
        push_neg at hc
        exact hP ((H.mu0 j).unr P hc)
      have h2 := hvG P hg
      show Valued.v (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) P) ≤ _
      rw [map_sub, map_one, hsub, h2, sub_self, map_zero]
      exact zero_le'
  have hxi : (t.tup μ : Chr t.X.F t.X.E t.X.K) x = 1 := by
    have hmem := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at hmem
    refine GlobalTheory.T.openCharacter_eq_one_of_integralUnit_one_at_ramified t.X.F t.X.E t.X.K t.seam.σ₀ _ hmem.1.1.1.1.2 hmem.1.1.1.1.1 x hxint fun P hP => hsuppX P ?_
    refine ⟨t.sel (P.under (𝓞 t.X.F)), Finset.mem_union_right _ ?_, ?_⟩
    · have hs : (t.sel (P.under (𝓞 t.X.F))).under (𝓞 t.X.F) = P.under (𝓞 t.X.F) :=
        GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
      refine (GlobalTheory.TwistPlaces.mem_QE_iff H.sel (t.tup μ)).2 ⟨?_, ?_⟩
      · rw [hs]; exact hP
      · rw [hs]
    · exact GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
  rw [← hq]
  by_cases hμ : μ = D.what₂.mu0
  · rw [(H.ref hμ).2]
    exact hmu ⟨i, hi⟩
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hmu ⟨i, hi⟩, one_mul, hξ x, hxi, map_one]

end GlobalTheory.TieUnr
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.LevDeco
open scoped TensorProduct

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem exists_basePlace_contains_every_chartLevelPrime {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (j : ℕ) (hj : j ≤ D.R.m) (P : t.Pr.vT (t.word u)) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), ∃ h : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal, IsOver v (seamP t.seam P.1) := by
  classical
  have hpi : t.Pr.piT (t.word u) ∈ P.1.asIdeal := by
    have h := P.2
    unfold Formalism.L2.Col.Primes.vT Formalism.L2.Col.divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  have hT : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    rw [← t.pr_ok.piT_norm]
    exact Ideal.mul_mem_right _ _ hpi
  have hTQ : (((St j hj).T : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P.1).asIdeal := by
    rw [H.T_eq j hj, ← t.T_rec u, ← map_natCast (RingOfIntegers.mapRingEquiv t.seam.iE), mem_seamP]
    exact hT
  have hT0 : (((St j hj).T : ℕ) : 𝓞 D.host.F) ≠ 0 := by
    rw [H.T_eq j hj, ← t.T_rec u]
    exact Nat.cast_ne_zero.2 (t.pr_ok.T_prime _).ne_zero
  have hmem : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ (seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hTQ
  let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨(seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)),
    Ideal.IsPrime.comap _, fun h => hT0 (by rw [h] at hmem; exact (Ideal.mem_bot.1 hmem))⟩
  exact ⟨v, hmem, rfl⟩

theorem N_eq_latAdX {A : AdData t u μ St} {a : 𝓞 D.host.E} {j : ℕ} {hj : j ≤ D.R.m} {β : (St j hj).Ch} {y : UA D j hj}
    {q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j} (hq : IsPtAd A a j hj β y q) : q.deco.1.N = latAdX A a j hj β y.1 := by
  show _ = latBack t.seam (latCo D.sp (gramN D j hj) (A.crd j hj) a y.1 ((St j hj).K β).lev.Lb)
  rw [← hq.lat, latBack_seam_lat]

theorem ptAd_mul_lev_deco : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P w, p₁.deco.1.f P w = p.deco.1.f P w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ H j hj β x x₁ κ hx p p₁ hp hp₁
  have hN : p₁.deco.1.N = p.deco.1.N := by
    rw [N_eq_latAdX hp₁, N_eq_latAdX hp, hx, latAdX_mul_lev]
  refine ⟨hN, fun P w => ?_⟩
  obtain ⟨v, hTv, hov⟩ := exists_basePlace_contains_every_chartLevelPrime H j hj P
  by_cases hw : w ∈ p.deco.1.at P.1
  · have hw₁ : w ∈ p₁.deco.1.at P.1 := by simpa only [Deco.at, hN] using hw
    obtain ⟨s, hs, hsw⟩ := (mem_locP _ _ _).1 hw
    have h2 : s • w ∈ p₁.deco.1.N := hN ▸ hsw
    have hy : (fun b => t.seam.iE ((s • w) b)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb := by
      rw [← hp₁.lat]
      exact Submodule.subset_span ⟨_, h2, rfl⟩
    let z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ((St j hj).K β).lev.Lb)) :=
      ⟨_, GlobalTheory.T.pulledLatticeVector_mem_dualBaseLatticeCompletion D.sp (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) (A.crd j hj) a x₁.1 x₁.2
        _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hy⟩
    have H1 := GlobalTheory.CplPt.funMoved_mul_lev t.seam ((St j hj).K β).lev P v hTv _ _ p.deco.1 κ (hp.fnl P v hTv hov)
    rw [mul_assoc, ← hx] at H1
    have e1 := H1 _ hsw z rfl
    have e2 := hp₁.fnl P v hTv hov _ h2 z rfl
    have e3 : p₁.deco.1.f P (s • w) = p.deco.1.f P (s • w) := e2.trans e1.symm
    rw [p₁.deco.2.f_smul P _ w hw₁, p.deco.2.f_smul P _ w hw] at e3
    haveI hP := P.1.isPrime
    have hu : Ideal.Quotient.mk P.1.asIdeal s ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact hs
    exact mul_left_cancel₀ hu e3
  · have hw₁ : w ∉ p₁.deco.1.at P.1 := by simpa only [Deco.at, hN] using hw
    rw [p₁.deco.2.f_off P w hw₁, p.deco.2.f_off P w hw]

end GlobalTheory.TwV.LevDeco

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

namespace GlobalTheory.FnlAway

open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem T_mem_under {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : D.what₂.Word) (P : t.Pr.vT (t.word u))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : IsOver v (seamP t.seam P.1)) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have h1 : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    have := Ideal.absNorm_mem P.1.asIdeal
    rwa [t.pr_ok.vT_norm _ P.1 P.2] at this
  rw [t.T_rec] at h1
  have h2 := (mem_seamP t.seam P.1 _).2 h1
  rw [map_natCast] at h2
  unfold IsOver at hv
  rw [hv, Ideal.mem_comap, map_natCast]
  exact h2

theorem prV_pullV_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (g g₁ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : bc (prV (E := E) v) g₁ = bc (prV (E := E) v) g) (w : Fin n → E) (l : Fin n) :
    prV (E := E) v (pullV (F := F) g₁ w l) = prV (E := E) v (pullV (F := F) g w l) := by
  have key : ∀ k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), prV (E := E) v (pullV (F := F) k w l) =
      ∑ j, ((bc (prV (E := E) v) k)⁻¹ : GL (Fin n) _).1 l j * prV (E := E) v (Formalism.L2.Col.iA F E (w j)) := by
    intro k
    rw [← map_inv]
    unfold pullV

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  rw [key, key, h]




theorem exists_unit_one_add_generator {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad)
    (crd : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : Fin (D.R.N i) → D.host.E) (hw : w ∈ latCo D.sp (gramN D i hi) crd a x.1 lev.Lb) :
    ∃ z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)),
      z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F crd * x.1) w l) := by
  let M := latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb))
  have hint : ∀ c : 𝓞 D.host.E, inclE (F := D.host.F) (v.adicCompletion D.host.F) (c : D.host.E) ∈ intV D.host.E v :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : D.host.E), ⟨c, rfl⟩⟩, rfl⟩)
  let φ : (Fin (D.R.N i) → D.host.E) → (Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
    fun l k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)
  have hadd : ∀ l₁ l₂, φ (l₁ + l₂) = φ l₁ + φ l₂ := by
    intro l₁ l₂
    funext k
    simp only [φ, pullV, Matrix.mulVec, dotProduct, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hzero : φ 0 = 0 := by
    funext k
    simp [φ, pullV, Matrix.mulVec, dotProduct]
  have hsmul : ∀ (c : 𝓞 D.host.E) l, φ (c • l) = (⟨_, hint c⟩ : intV D.host.E v) • φ l := by
    intro c l
    funext k

    simp only [φ, pullV, Matrix.mulVec, dotProduct, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show c • l j = (c : D.host.E) * l j from Algebra.smul_def c (l j), map_mul, map_mul, map_mul, map_mul, mul_left_comm]
    congr 1
  have hmem : ∀ l ∈ compan (sp := D.sp) (gramN D i hi) a (latAd x.1 lev.Lb), φ l ∈ M := by
    intro l hl
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := Submodule.mem_sup.1 hl
    rw [hadd]
    refine M.add_mem (GlobalTheory.T.placeComponent_pullback_latticeVector_mem_dual_span i hi lev x v l₁ h₁) ?_
    refine Submodule.smul_induction_on h₂ ?_ ?_
    · intro r hr s hs
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [hsmul]
      refine M.smul_mem _ ?_
      induction hs using Submodule.span_induction with
      | mem s hs => exact GlobalTheory.T.stepPoint_pulledDualVector_mem_localBaseLattice i hi lev x v s hs
      | zero => rw [hzero]; exact M.zero_mem
      | add p q _ _ hp hq => rw [hadd]; exact M.add_mem hp hq
      | smul c s _ h => rw [hsmul]; exact M.smul_mem _ h
    · intro p q hp hq
      rw [hadd]
      exact M.add_mem hp hq
  unfold latCo at hw
  obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hw
  refine ⟨⟨_, hmem l hl⟩, funext fun k => congrArg (prV (E := D.host.E) v) (congrFun ?_ k)⟩
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  funext j
  symm
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, toLE_apply, ← map_inv]
  show ((((crd⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).map (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) *ᵥ _) j = _
  refine (RingHom.map_mulVec _ _ _ j).symm.trans ?_
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]



theorem fnl_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpin htie i hi β x x₁ p p₁ hp hp₁ P hagree y hy
  have hat := GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place A dtU a hpin htie i hi β x x₁ p p₁ hp hp₁ P hagree
  set v := HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1) with hvdef
  have hvo : IsOver v (seamP t.seam P.1) := by
    unfold IsOver
    rw [hvdef, HeightOneSpectrum.under_asIdeal]
  have hTv : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    rw [htie.T_eq]
    exact T_mem_under t u P v hvo
  have hd := p.deco.2
  have hd₁ := p₁.deco.2
  obtain ⟨s, hs, hsy⟩ := (mem_locP P.1 _ y).1 hy
  have hy₁ : y ∈ p₁.deco.1.at P.1 := hat ▸ hy
  obtain ⟨s₁, hs₁, hsy₁⟩ := (mem_locP P.1 _ y).1 hy₁
  have hsP : s * s₁ ∉ P.1.asIdeal := fun h => (P.1.isPrime.mem_or_mem h).elim hs hs₁
  have hw : (s * s₁) • y ∈ p.deco.1.N := by
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ hsy
  have hw₁ : (s * s₁) • y ∈ p₁.deco.1.N := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ hsy₁
  have hlat : (fun l => t.seam.iE (((s * s₁) • y) l)) ∈
      latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb := by
    rw [← hp.lat]
    exact Submodule.subset_span ⟨_, hw, rfl⟩
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator i hi ((St i hi).K β).lev (A.crd i hi) a x v _ hlat
  have e1 := hp.fnl P v hTv hvo _ hw z hz
  have hz₁ : z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F (A.crd i hi) * x₁.1)
      (fun b => t.seam.iE (((s * s₁) • y) b)) l) := by
    have hbc : bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x₁.1) =
        bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x.1) :=
      ((MonoidHom.map_mul _ _ _).trans (congrArg (bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi)) * ·) (hagree v hvo))).trans
        (MonoidHom.map_mul _ _ _).symm
    refine hz.trans (funext fun l => ?_)
    exact (prV_pullV_congr (F := D.host.F) (E := D.host.E) v (ratA D.host.F (A.crd i hi) * x.1)
      (ratA D.host.F (A.crd i hi) * x₁.1) hbc (fun b => t.seam.iE (((s * s₁) • y) b)) l).symm
  have e2 := hp₁.fnl P v hTv hvo _ hw₁ z hz₁
  have f1 := hd.f_smul P (s * s₁) y hy
  have f2 := hd₁.f_smul P (s * s₁) y hy₁
  haveI := P.1.isPrime
  have hne : Ideal.Quotient.mk P.1.asIdeal (s * s₁) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hne
  rw [← f1, ← f2, e1, e2]

end GlobalTheory.FnlAway
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.adelicDatum_invariance_support_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → SizeLaw A a) := by
  first | exact @GlobalTheory.TwV.sizeLaw_of_tie | exact GlobalTheory.TwV.sizeLaw_of_tie | (intros; apply GlobalTheory.TwV.sizeLaw_of_tie <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.coupledStepChartLevel_keeps_baseCoset : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∀ P (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P ((κ'' P).1 y) (A.y0 β' P) ↔
      SameCoset t.sel (t.tup μ) (t.cst μ) P y (A.y0 β' P)) := by
  first | exact @GlobalTheory.CplCoset.sameCoset_kappa | exact GlobalTheory.CplCoset.sameCoset_kappa | (intros; apply GlobalTheory.CplCoset.sameCoset_kappa <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDatum_pair_classes_has_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  first | exact @GlobalTheory.TwV.datLoc_classes | exact GlobalTheory.TwV.datLoc_classes | (intros; apply GlobalTheory.TwV.datLoc_classes <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  first | exact @GlobalTheory.TwRat.ratUnitCol | exact GlobalTheory.TwRat.ratUnitCol | (intros; apply GlobalTheory.TwRat.ratUnitCol <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  first | exact @GlobalTheory.LocQCoset.coset_agree | exact GlobalTheory.LocQCoset.coset_agree | (intros; apply GlobalTheory.LocQCoset.coset_agree <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.moved_pair_datum_eq_adelic_datum : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (Xi : AdDatum J.St) j (hj : j + 1 ≤ D.R.m) (h1 : ((sysS H X std).Pj j).m + 1 = D.R.N j) (h2 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, xiM (sysS H X std) (J.fd std) (J.xi0 std Xi) j La La' z = Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
  first | exact @GlobalTheory.TwV.moved_pair_datum_eq_adelic_datum_alt | exact GlobalTheory.TwV.moved_pair_datum_eq_adelic_datum_alt | (intros; apply GlobalTheory.TwV.moved_pair_datum_eq_adelic_datum_alt <;> assumption)
end
