module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle519
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle481
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle497
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle237
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CoreAtQIffRowQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle211
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle002
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding Dec
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open GlobalTheory.GLq GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.AboveL
open UpperTheory.Gal.Int.Core
open GlobalTheory.RoadU GlobalTheory.RoadU.PhiDescent in
theorem UpperTheory.Gal.Int.Core.downPhi_holds : SphDown .phi := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP r w B hB hQdec hyp Pr AI hT A h O _ _ _ Bw hj g
  have hdec := hQdec A h
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A h hdec
  have hunder : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver h h'
    ext1
    exact this.over.symm
  obtain ⟨c, hc, hdegc, hq, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  obtain ⟨S, hS, -, -, -, -, hTw, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hunder, hq]) (by rw [hunder]; exact hB)
    simpa using this
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  have hrel : WDRel (RingEquiv.refl Ω) (wdAt Pr ι Bw h hj (r.comp (Dec (F := E) A).subtype))
      (wdAt Pr ι Bw' h' hj' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype)) := by
    by_cases hp : IsPstAt Pr Bw (r.comp (Dec (F := E) A).subtype)
    · exact GlobalTheory.RealGal.wdRelRes_gen E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r hp ι w w' h h' hj hj' i hi
    · have hp' : ¬ IsPstAt Pr Bw' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype) :=
        fun H => hp (D.2.2.2.1 H)
      rw [wdAt_of_not_isPstAt _ _ _ _ hp, wdAt_of_not_isPstAt _ _ _ _ hp']
      exact wdRel_trivWD h h' _ a
  have hsat : WDRel (RingEquiv.refl Ω) (satWD h a B) (satWD h' a B) := by
    have h0 := GlobalTheory.RSGam.Transport.wdRel_lpUnr c hc hdegc (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))
    unfold satWD
    rw [hS, hTw, (hS _ _).mp h0]
  have hgc : WeilRel (RingEquiv.refl Ω) g (c g) := (hc g (c g)).2 rfl
  have hcl := hyp w' hunder hB' Pr AI hT A h' O Bw' hj' (c g)
  rw [charPol_eq hrel hgc, charPol_eq hsat hgc]
  exact hcl
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.downUnr_holds :
    SphDown .unr := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP ρ w B hB hQdec hyp hl A h
  obtain ⟨w', hunder, h', hN⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A h (hQdec A h)
  have hB' : (CG.mk P).HasSat w' B := by
    have e := hP.sat w' 1 B (by rw [pow_one, hunder, hN]) (hunder ▸ hB)
    simpa using e
  have hlw : ((l : ℕ) : 𝓞 Q.K) ∉ w'.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 E))
    have e2 := (h' ((l : ℕ) : 𝓞 Q.K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hcl := hyp w' hunder hB' hlw A h'
  rw [hN] at hcl
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨s', rfl⟩ := hQdec A h (Ine_le_Dec A hs)
    exact hcl.1 s' hs
  · obtain ⟨σ', rfl⟩ := hQdec A h hσ.1
    have e := hcl.2 σ' hσ
    rw [← map_inv]
    exact e
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core


theorem UpperTheory.Gal.Int.Core.downDR_holds :
    SphDown .dR := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP r w B hB hdec hS
  show ClauseAt .dR π ι r w
  intro Pr AI hT A hA O _ _ _ Bw hj
  have hdA := hdec A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdA
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', hu, hw', hn⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA hdA
  have hBP : (CG.mk P).HasSat w' (B.map (· ^ 1)) :=
    hP.sat w' 1 B (by rw [hu, pow_one]; exact hn) (by rw [hu]; exact hB)
  have hc : ClauseAt .dR P ι _ w' := hS w' hu (by simpa using hBP)
  have hc' := hc Pr AI hT A hw' O Bw' hj'
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  refine ⟨D.1 hc'.1, fun τ LL' τ' hτ J hJ => ?_⟩
  obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.induced_embedding_extends E Ω Q.K l A O Bw Bw' e1 e2 τ LL' τ' hτ
  have hJK : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk P).infChar (ι.toRingHom.comp τK)).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
    rw [hP.inf, RingHom.comp_assoc, hτK]
    exact hJ
  have hres := D.2.2.2.2 τK J (hc'.2 τK LL' τ'' hind J hJK)
  rwa [hτK] at hres
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core
open UpperTheory.Gal.TP

namespace UpperTheory.Gal.Int.Core

theorem goodGuard_usPl (h1 : OneUs) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (d : ℕ) (hd : ImQ E d) : GoodGuard Ω l (UsPl (E := E) d) := by
  refine ⟨fun _ h => h.1, fun S hS => ?_⟩
  have hT := hS.union (Filter.eventually_cofinite.1 ((h1 E d hd).and (GlobalTheory.CongEx.eventually_not_mem_l E l)))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hT
  refine (hD.preimage (Homeomorph.inv (G E Ω)).isOpenMap).mono ?_
  rintro g ⟨v, hv, hdeg, A, hA, hσ⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  have hp : (normV v).Prime := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      (((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hdeg)
  exact ⟨v, hv.1, hv.2.1 hp, hv.2.2, A, hA, hσ⟩

theorem joinAll_of (h1 : OneUs) (hS : SubtractQ) : JoinAll := by
  intro hT hU E Ω _ _ _ _ _ _ l _ ι hF hI d hd hsq n hn
  exact allCoreQ_of hS hT E Ω l ι hF hI _ (goodGuard_usPl h1 E Ω l d hd) (fun m hm => hU m hm E Ω l ι hF d hd hsq) n hn

end UpperTheory.Gal.Int.Core
end
