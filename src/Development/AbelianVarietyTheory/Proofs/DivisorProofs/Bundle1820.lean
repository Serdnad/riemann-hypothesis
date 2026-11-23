module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle210
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle163
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle710
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

section

noncomputable section




namespace GlobalTheory.DatumFourierCore

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.DatumFourier
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem thetaVector_eq_sum_heisenberg_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → R.vP i t = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun t l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hR.thP.vP i t
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h),
    GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by

      rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourierCore

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.ConjNorm

open GlobalTheory.ConjInner

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)



theorem inner_reading_conj_at (he : R.models_HW) (fw : FWTie T R κ v₀) (hE : fw.Evaluates) (hT : BarTie fw) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i)
    (hB : JEvBarAt T R κ i σ hV) :
    ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
      starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have h1 := (hT i σ hσ hV).1 hB
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R he i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

theorem norm_eq_of_inner_conj {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] {x : H} {y : H'} (h : ⟪x, x⟫_ℂ = starRingEnd ℂ ⟪y, y⟫_ℂ) : ‖y‖ = ‖x‖ := by
  rw [inner_conj_symm] at h
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h]



theorem norm_conj_of_not_good (he : R.models_HW) (fw : FWTie T R κ v₀) (hE : fw.Evaluates) (hT : BarTie fw) (hu : R.LUnif)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (x : Fin (R.nW i) → D.what₂.LL) :
    ‖(R.FW i).j ((starRingEnd ℂ).comp σ) x‖ = ‖(R.FW i).j σ x‖ := by
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ (good_resC T hσ)
  by_cases hB : JEvBarAt T R κ i σ hV
  · exact norm_eq_of_inner_conj (inner_reading_conj_at T R κ v₀ he fw hE hT i σ hσ hV hB x x)
  · have h0 := (hT i σ hσ hV).2 hB
    have hx : x = 0 := by
      by_contra hx
      have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
      have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
      rw [h0] at h2
      exact h2 rfl
    subst hx
    rw [map_zero, map_zero, norm_zero, norm_zero]


omit R in
theorem not_good_conj {σ : D.what₂.LL →+* ℂ} (h : GoodEmb T.Q.c (res T σ)) :
    ¬ GoodEmb T.Q.c (res T ((starRingEnd ℂ).comp σ)) := by
  have key : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
      {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {s : c.F →+* ℂ}, GoodEmb c s →
      ¬ GoodEmb c ((starRingEnd ℂ).comp s) := by
    intro E _ _ _ H l c s h h'
    have h2 : starRingEnd ℂ H.rt0 = H.rt0 := by
      conv_lhs => rw [← h]
      exact h'
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
    have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp [pow_two, him] at h3
    nlinarith [mul_self_nonneg H.rt0.re]
  exact key T.Q.c h

end GlobalTheory.ConjNorm



theorem GlobalTheory.ConjNorm.pConj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ fw : FWTie T R κ v₀, BarTie fw → R.LUnif → R.PConj := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ fw hT hu i σ x
  have hE := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T R F κ v₀ fw hu
  have key : ∀ σ, ¬ GoodEmb T.Q.c (res T σ) → (R.FW i).nrmAt ((starRingEnd ℂ).comp σ) x = (R.FW i).nrmAt σ x :=
    fun σ hσ => GlobalTheory.ConjNorm.norm_conj_of_not_good T R κ v₀ hC.models.HW fw hE hT hu i σ hσ x
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · have h1 := key _ (GlobalTheory.ConjNorm.not_good_conj T hσ)
    have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := RingHom.ext fun a => Complex.conj_conj _
    exact h1.symm.trans (congrArg (fun s => (R.FW i).nrmAt s x) e)
  · exact key σ hσ
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertEig


open Classical in
noncomputable def coeff (n : ℕ) (ok : List ℕ → Prop) (lab : ℕ → List ℕ → List ℤ) (b : List ℕ → ℂ) (d : List ℤ) : ℂ :=
  if h : ∃ s, ok s ∧ lab n s = d then b h.choose else 0

theorem coeff_cases {H : Type} [AddCommGroup H] [Module ℂ H] (n : ℕ) (ok : List ℕ → Prop) (lab : ℕ → List ℕ → List ℤ)
    (isLab : List ℤ → Prop) (hL : ∀ d, isLab d → ∃ s, ok s ∧ lab n s = d) (b : List ℕ → ℂ)
    (ops : List ℤ → Module.End ℂ H) (x : H) (hx : ∀ s, ok s → ops (lab n s) x = b s • x) (d : List ℤ) :
    (¬ isLab d ∧ coeff n ok lab b d = 0) ∨ ops d x = coeff n ok lab b d • x := by
  classical
  by_cases h : ∃ s, ok s ∧ lab n s = d
  · right
    have hf : coeff n ok lab b d = b h.choose := dif_pos h
    have h1 := hx _ h.choose_spec.1
    rw [h.choose_spec.2] at h1
    rw [hf]
    exact h1
  · left
    exact ⟨fun hl => h (hL d hl), dif_neg h⟩

theorem eig_of_single {H Γ ι W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W]
    (e : H →ₗ[ℂ] (Γ → W)) (he : Function.Injective e) (rep : List ℤ → Finset ι) (act : Γ → ι → Γ)
    (ops : (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hops : ∀ c x, e (ops c x) = fun g => c.sum fun d z => z • ∑ γ ∈ rep d, e x (act g γ))
    (f : List ℤ → ℂ) (x : H) (hx : ∀ d, (rep d = ∅ ∧ f d = 0) ∨ ops (Finsupp.single d 1) x = f d • x)
    (c : List ℤ →₀ ℂ) : ops c x = (c.sum fun d z => z * f d) • x := by
  have hd : ∀ d g, ∑ γ ∈ rep d, e x (act g γ) = f d • e x g := by
    intro d g
    rcases hx d with ⟨h0, hf⟩ | h1
    · rw [h0, hf, Finset.sum_empty, zero_smul]
    · have h2 := congrFun (hops (Finsupp.single d 1) x) g
      rw [h1, map_smul, Finsupp.sum_single_index (by simp), one_smul] at h2
      exact h2.symm
  apply he
  rw [hops c x, map_smul]
  funext g
  simp only [Pi.smul_apply, Finsupp.sum, hd, smul_smul, Finset.sum_smul]

theorem labIn_eq (n : ℕ) (s : List ℕ) : GlobalTheory.Hk3.labIn n s = labIn n s := rfl



theorem veig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (j : Fin D.R.m) (t : T) (hV : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H), GlobalTheory.Hk3.IsOpsV R j t hV → ∀ P, Good R t P → _root_.Formalism.DivisionValues.conjPl P = P → ∀ (b : List ℕ → ℂ) (y y' : (R.HV j t).H), (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s → hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y = b s • y ∧ hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y' = b s • y') → ∀ cV : List ℤ →₀ ℂ, ∃ σ : ℂ, hV P cV y = σ • y ∧ hV P cV y' = σ • y' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hM j t hV hOps P hP hc b y y' hb cV
  have hL : ∀ d, IsLab (Vc D j) P d → ∃ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s ∧ labIn (Vc D j).rank s = d := by
    intro d hl
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) P d).1 hl
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := (GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank d).1 ⟨h1, h2, h3 hc⟩
    exact ⟨s, ⟨hs2, hs3, hs1⟩, (labIn_eq _ _).symm.trans hs4.symm⟩
  have hrep : ∀ d, ¬ IsLab (Vc D j) P d → GlobalTheory.Hk3.rep (Vc D j) P d = ∅ := by
    intro d hd
    classical
    exact dif_neg hd
  have key : ∀ x : (R.HV j t).H, (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s →
      hV P (Finsupp.single (labIn (Vc D j).rank s) 1) x = b s • x) →
      hV P cV x = (cV.sum fun d z => z * coeff (Vc D j).rank (Formalism.L2.Col.InertTypeOk (Vc D j).rank) labIn b d) • x := by
    intro x hx
    refine eig_of_single (R.HV j t).e (hM.HV j t).1 (GlobalTheory.Hk3.rep (Vc D j) P) (fun g γ => g * (finHom (Vc D j)).rangeRestrict γ)
      (hV P) (fun c x => hOps P hP c x) _ x ?_ cV
    intro d
    rcases coeff_cases (Vc D j).rank (Formalism.L2.Col.InertTypeOk (Vc D j).rank) labIn (IsLab (Vc D j) P) hL b
      (fun d => hV P (Finsupp.single d 1)) x hx d with ⟨h0, hf⟩ | h1
    · exact Or.inl ⟨hrep d h0, hf⟩
    · exact Or.inr h1
  exact ⟨_, key y (fun s hs => (hb s hs).1), key y' (fun s hs => (hb s hs).2)⟩

end GlobalTheory.InertEig
end

section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphBC

open GlobalTheory.PRep GlobalTheory.DefU

theorem isSpherical_of_isCompAlong_split {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X)
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ) (hu : IsUnramU π w) :
    GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w (n := n)) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  have hp : Function.Surjective ((cLoc w).comp (locU n w).subtype) := fun g =>
    ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  by_contra hns
  have hfix : ∀ v, (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), σ k v = v) → v = 0 := by
    intro v hv
    by_contra hv0
    exact hns ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩)
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hc
  let Ψ : AutSub E n := ⟨π, hπ⟩
  have hirr : Representation.IsIrreducible (σ.comp ((cLoc w).comp (locU n w).subtype)) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype)) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V X X Ψ.rep (locU n w).subtype
    (σ.comp ((cLoc w).comp (locU n w).subtype)) (σ.comp ((cLoc w).comp (locU n w).subtype))
    Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
      (Ψ.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA E n → ℂ) := fun i => π.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp ((cLoc w).comp (locU n w).subtype)) g u) =
      (RU E n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
        (Ψ.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap).map π.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ((RU E n).comp (locU n w).subtype)
    (σ.comp ((cLoc w).comp (locU n w).subtype)) hirr fi hfi
    (((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype) : Subgroup (locU n w)) : Set (locU n w)) ⊥
    (fun i v hv => by
      have hv' : v = 0 := hfix v fun k hk => by
        obtain ⟨x, rfl⟩ := hp k
        exact hv x hk
      rw [hv', map_zero]
      exact Submodule.zero_mem _)
    (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) φ (fun k hk => hφK k.1 k.2 hk) hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 key)

theorem isSpherical_of_isUnramU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ)
      (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)),
      GlobalTheory.BcSpeh.Parts π a d h P ρ m →
      (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) →
      (∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))) →
      ∀ w, IsUnramU π w → ∀ i (τ : SmIrr (GL (Fin (a i)) (w.adicCompletion E))), (P i).IsLocComp w τ →
        GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (n := (a i))) := by
  intro E _ _ _ hE n π hπ c a d h P ρ m σ hp hsh hsplit w hu i τ hτ
  suffices hB : ∃ B, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ B by
    obtain ⟨B, hB⟩ := hB
    have h1 := (GlobalTheory.BcSpehCompare.hasSat_iff (hp.loc i w) B).2 hB
    exact ((GlobalTheory.BcSpehCompare.hasSat_iff hτ B).1 h1).1
  by_cases hw : IsSplitAt w
  · have hc := hsplit w hw
    have hs : GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w (n := n)) :=
      isSpherical_of_isCompAlong_split hπ hw _ hc hu
    have hsm : GlobalTheory.PRep.IsSmooth (locProd h w (σ · w)) := GlobalTheory.SmGL.isSmooth_parInd _ _
    have hirr : (locProd h w (σ · w)).IsIrreducible := hc.1
    obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible hsm hirr hs
    obtain ⟨S, hS, -⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hp.pos i).2)
      (fun i => (hsh i w).2.2) T hT
    exact ⟨S i, hS i⟩
  · obtain ⟨s, ϖ, q, α, h1, h2, h3⟩ := GlobalTheory.BcSpehCompare.exists_hasSatAt hE hπ hw hu
    obtain ⟨S, hS, -⟩ := hp.inert w s ϖ q h1 h2 α h3
    exact ⟨S i, hS i⟩

end GlobalTheory.SphBC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.jetOperatorBound_at_embedding_of_complexOpNormSq : ∀ (K : Type) [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (a b : ℕ) (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → (JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → (JetInVV ℂ lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) → ∀ (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → ℂ), (∀ e, (∀ τ, ((_root_.GlobalTheory.ColNorms.degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → σ (J e) = J' e) → ∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' J' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t → CoefOpLe σ lam lam' (jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) t := by
  first | exact @GlobalTheory.coefOpLe_jetOp_of_opNormSqLe | exact GlobalTheory.coefOpLe_jetOp_of_opNormSqLe | (intros; apply GlobalTheory.coefOpLe_jetOp_of_opNormSqLe <;> assumption)
end

section


theorem _root_.GlobalTheory.T.normalisedFamily_periodLattice_properties_hold : GlobalTheory.ColNorms.PeriodLattices := by
  first | exact @GlobalTheory.ColNorms.periodLattices | exact GlobalTheory.ColNorms.periodLattices | (intros; apply GlobalTheory.ColNorms.periodLattices <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (emb : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (σ : K →+* ℂ), ((Matrix.of fun i j => pairVr emb lam 1 (bVV K lam i) (bVV K lam j)).map σ).PosSemidef ∧ ∀ x : Formalism.L2.DIV.VV K lam, (∑ i, ∑ j, starRingEnd ℂ ((InfinitePlace.mk σ).embedding ((bVV K lam).repr x i)) * (InfinitePlace.mk σ).embedding (pairVr emb lam 1 (bVV K lam i) (bVV K lam j)) * (InfinitePlace.mk σ).embedding ((bVV K lam).repr x j)).re = sqAt σ lam x := by
  first | exact @GlobalTheory.ColNorms.gram_posSemidef_and_sqAt | exact GlobalTheory.ColNorms.gram_posSemidef_and_sqAt | (intros; apply GlobalTheory.ColNorms.gram_posSemidef_and_sqAt <;> assumption)
end
