module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle849
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle845
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle844
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle842
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.ExportSeries

theorem idemAt_mul_idem_add_conj {D : D7} {P Q' : Finset (Pl D.host.E)} (hP : SplitSet P) (hQ : Q' ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) (hPQ : PP ∉ Q') : idemAt PP * (idem Q' + cA D (idem Q')) = 0 := by

  rw [mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_eq_zero fun q hq => hP.mul_eq_zero hPP (hQ hq) (fun e => hPQ (e ▸ hq)),
    Finset.sum_eq_zero fun q hq => hP.mul_conj hPP (hQ hq), add_zero]



theorem redFn_eq_one_of_suppAt : ∀ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {P Q' : Finset (Pl D.host.E)}, SplitSet P → Q' ⊆ P → ∀ {PP : Pl D.host.E}, PP ∈ P → PP ∉ Q' → ∀ {κ : GA D V}, Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ → redFn β PP (Lev.finE V κ) = 1 := by
  intro D V β P Q' hP hQ PP hPP hPQ κ hS hSupp
  obtain ⟨y, hy⟩ := hS
  obtain ⟨hint, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP (hP.isIdemAt hPP)
  have h0 := idemAt_mul_idem_add_conj hP hQ hPP hPQ

  have hk : ∀ i j, idemAt PP * (Formalism.L2.Theta.mt V κ - 1) i j = 0 := fun i j => by
    rw [← hSupp i j, ← mul_assoc, h0, zero_mul]
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl

  have hA : toEAf D (idemAt PP) • ((Lev.finE V κ).val - 1) = 0 := by
    ext i j
    have := congrArg (toEAf D) (hk i j)
    rw [RingHom.map_mul, RingHom.map_zero, Matrix.sub_apply, RingHom.map_sub] at this
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, hval, Matrix.map_apply, Matrix.zero_apply]
    convert this using 3
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hY : toEAf D (idemAt PP) • ((intGL D.host.F D.host.E _ y).val - 1) = 0 := by
    have hg : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V κ * β := by
      rw [← hy]; simp [frGL, MulAut.conj_apply, mul_assoc]
    have e1 : (intGL D.host.F D.host.E _ y).val - 1 = (β⁻¹).val * ((Lev.finE V κ).val - 1) * β.val := by
      rw [hg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul β⁻¹ β, inv_mul_cancel, Units.val_one,
        Units.val_mul, Units.val_mul]
    rw [e1, ← Matrix.smul_mul, ← Matrix.mul_smul, hA, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hy, redFn_frGL]
  ext i j
  have hij := congrFun (congrFun hY i) j
  have hsub : (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * y.val i j = (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    have hij' : toEAf D (idemAt PP) * ((intGL D.host.F D.host.E _ y).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j) = 0 := by
      simpa only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.zero_apply] using hij
    have h1ij : ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j : Lev.EAf D) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, h1ij, ← sub_eq_zero, ← mul_sub]
    exact hij'
  have := congrArg (resS D.host.F PP) hsub
  rw [RingHom.map_mul, RingHom.map_mul, h1, one_mul, one_mul] at this
  change (resS D.host.F PP) (y.val i j) = _
  rw [this, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.ExportSeries

end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.ExportSeries.LatHalf

open GlobalTheory.ExportSeries
open Formalism.L2.DIV (Pl)

variable {D : D7}

theorem levConj_conjPl (P : Formalism.L2.DIV.Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl P (Formalism.L2.DIV.conjPl P) := by
  intro c hc
  refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ P.asIdeal
  rw [Formalism.L2.DIV.starO_starO]
  exact hc

theorem eq_conjPl_of_levConj {A B : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl A B) :
    B = Formalism.L2.DIV.conjPl A := by
  refine (HeightOneSpectrum.ext ?_).symm
  refine Ideal.IsMaximal.eq_of_le (Formalism.L2.DIV.conjPl A).isMaximal B.isPrime.ne_top fun b hb => ?_
  obtain ⟨c', hc', e⟩ := h (Formalism.L2.DIV.starO b) hb
  have : c' = b := RingOfIntegers.ext (by rw [e, Formalism.L2.DIV.starO_coe, star_star])
  exact this ▸ hc'

theorem isIdemAt_conjPl {e : AE D} {P : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e P) :
    Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.L2.DIV.conjPl P) :=
  GlobalTheory.MovedIdem.isIdemAt_conj h fun x => by
    rw [show Formalism.L2.Col.cO D.host.E x = Formalism.L2.DIV.starO x from RingOfIntegers.ext (by rw [Formalism.L2.DIV.starO_coe]; rfl)]
    rfl

theorem conj_placesOK {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) :
    idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) ∧ PlacesOK ∅ (Pg.image Formalism.L2.DIV.conjPl) := by
  obtain ⟨P, h1, -, hP⟩ := h.split
  have hS := hP.mono h1
  have hinj : Set.InjOn Formalism.L2.DIV.conjPl (Pg : Set (Pl D.host.E)) := fun a _ b _ hab => by
    rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl]
  have hc : ∀ PP ∈ Pg, idemAt (Formalism.L2.DIV.conjPl PP) = cA D (idemAt PP) := fun PP hPP =>
    idemAt_eq (isIdemAt_conjPl (hS.isIdemAt hPP))
  have he : idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) := by

    rw [idem, Finset.sum_image hinj, idem, map_sum]
    exact Finset.sum_congr rfl hc
  refine ⟨he, ⟨⟨Pg.image Formalism.L2.DIV.conjPl, Finset.empty_subset _, le_rfl,
    ⟨idem (Pg.image Formalism.L2.DIV.conjPl), ⟨idemAt, ?_, rfl⟩, ?_⟩⟩, Finset.disjoint_empty_left _, ?_⟩⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    rw [hc P0 hP0]
    exact isIdemAt_conjPl (hS.isIdemAt hP0)
  · rw [he, GlobalTheory.DualPairCheck.cA_cA, mul_comm]
    exact hS.isIdemSum.2
  · intro PP hPP PP' hPP'
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 (hPP.resolve_left (Finset.notMem_empty PP))
    rcases hPP' with rfl | hc'
    · exact h.prime P0 (Or.inl hP0) _ (Or.inr (levConj_conjPl P0))
    · rw [eq_conjPl_of_levConj hc', Formalism.L2.DIV.conjPl_conjPl]
      exact h.prime P0 (Or.inl hP0) P0 (Or.inl rfl)

theorem goodPosition_auxiliaryPlaces_alone {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) : PlacesOK ∅ Q :=
  ⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _,
    fun PP hPP => h.prime PP (Or.inr (hPP.resolve_left (Finset.notMem_empty PP)))⟩

theorem idem_sq {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) : idem R * idem R = idem R := by
  have := h.isOrthSum.1.idem
  rwa [halfIdem, idem_empty, map_zero, zero_add] at this

theorem toEAf_idem_int {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) :
    toEAf D (idem R) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, -, h2, hP⟩ := h.split
  have := GlobalTheory.DatumFourier.idem_div_int (hP.mono h2).isIdemSum one_ne_zero fun PP _ hPP =>
    PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hPP))
  simpa using this

theorem frMapO_add {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (x : Mx D m n) : IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, he]

theorem mem_lat_piece {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    (x : WO S T) (hi : IsIntM (frMapO S T F.βS F.βT x)) : idem R • x ∈ F.lat := by
  refine GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hR (isHalf_smul (idem_sq hR) x) ?_
  rw [frMapO_smul]
  exact fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (toEAf_idem_int hR) (hi i j)

theorem mem_lat_iff_isIntM_halfIdem : ∀ {D : D7} {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T}, F.Good →
    ∀ {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}, GlobalTheory.ExportSeries.PlacesOK Pg Q →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) →
    ∀ {x : WO S T}, IsHalf (GlobalTheory.ExportSeries.halfIdem Pg Q) x →
      (x ∈ F.lat ↔ IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) := by
  intro D S T F hF Pg Q h _ x hx
  obtain ⟨hR1, hR⟩ := conj_placesOK h
  have hQ := goodPosition_auxiliaryPlaces_alone h
  have hxe : x = idem (Pg.image Formalism.L2.DIV.conjPl) • x + idem Q • x := by
    rw [← add_smul, hR1]
    exact (Matrix.ext fun i j => hx i j).symm
  constructor
  · intro hl
    obtain ⟨o1, a1⟩ := GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hR (isHalf_smul (idem_sq hR) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hR) hl)
    obtain ⟨o2, a2⟩ := GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hQ (isHalf_smul (idem_sq hQ) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hQ) hl)
    rw [hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add]
    exact ⟨fun i j => add_mem (a1 i j) (a2 i j), fun i j => add_mem (o1 i j) (o2 i j)⟩
  · rintro ⟨-, hi⟩
    rw [hxe]
    exact add_mem (mem_lat_piece hF hR x hi) (mem_lat_piece hF hQ x hi)

end GlobalTheory.ExportSeries.LatHalf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.admissibleConjugatePairPlaces_eq_self_of_good_chars : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (Q : Finset (Pl D.host.E)) (d : PlE D.host → (G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)))), (∀ P ∈ Q, IsSplitPl D.host P) → (∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q) → (∀ P ∈ Q, GlobalTheory.TwSys.GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) → (0 < M ∨ ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i)) → admissibleConjugatePairPlaces X i Q M = Q := by
  first | exact @GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar | exact GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar | (intros; apply GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefActIo

variable {D : D7}

section Gen

variable {S T : HSp D}

theorem om_fock_of_vac {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hB : B.Good) (hψ : ψ.Good)
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hB.frame.vac.2.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hB.frame.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, GlobalTheory.RealFockAction.om_vac hB hψ hω hf hv hu,
    GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := B.w.p) hB.frame.vac.1 hθ
      (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hB.frame.cartT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (by have := hB.frame.onbT τ; rwa [← hB.sig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

theorem act_of_mem_GfC (B : Base S T) {k : GA D S} (hk : k ∈ GfC S) : B.act k = 1 := by
  have e : realGL B.F.θ S k = 1 := by
    funext τ
    change (Formalism.UG.bc (B.F.θ τ)) (infHom S k) = 1
    rw [show infHom S k = 1 from hk, map_one]
  rw [Base.act, MonoidHom.comp_apply, e, map_one]

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}

theorem thetaVector_laws (hC : GlobalTheory.Hk3.Core R F) (t : T0) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧
      (∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ (cplxO 1 (cart (R.MW i (sg0 D A)) ρ)) (R.vP i t)) ∧
      Function.Injective (R.ptP i t) := by
  have hP := hC.thP
  have hM := hC.models
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h := hP.pt_theta i t 1
    have e : R.ptP i t 1 = R.vP i t := by
      unfold RealDat.ptP pureTensorO pureTensorL
      rw [show (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 from rfl,
        Module.Basis.constr_basis]
      simp [opPow]
    rwa [e] at h
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hP.vP i t) hf
  have hne : R.vP i t ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
      ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hP.vP i t)
  exact ⟨hf, hv, GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _
    (hP.ωP i t).std hM.inf (fun τ => GlobalTheory.OneMapRef.VecP.isCartanInv_one_of_onb (hM.BV i τ)) (hM.BV i) hf hne hv⟩

theorem act_ioP_inf (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    ∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  intro u hu x w
  obtain ⟨hf, hv, hinj⟩ := thetaVector_laws (i := i) hC t
  have hω := h.isWeil hC.thP.ωP ht
  have hpt : ∀ P, R.ptP i t P = B.F.fock (R.vP i t) P := fun P => by rw [h.fock_eq]; rfl
  have hf' : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (R.vP i t) := by rw [h.ψ]; exact hf
  have hv' : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D i) (Wc D i)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP i t) := by
    rw [h.ψ, h.θ, h.sT]; exact hv
  apply hinj
  rw [hpt, hpt, ← om_fock_of_vac hB hψ hω hf' hv' hu, ← hpt, ← hpt]
  exact (hC.thP.ioP i t).1 u hu x w

theorem act_ioP (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    (∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w)) ∧
      ∀ (u : GA D (Vc D i)) x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  refine ⟨act_ioP_inf hC hB h hψ ht, fun u x w => ?_⟩
  have e := GlobalTheory.AutMult.toInf_mul_toFin u
  set a := GlobalTheory.AutMult.toInf (Vc D i) u
  set k := GlobalTheory.AutMult.toFin (Vc D i) u
  rw [← e, map_mul, map_mul, act_of_mem_GfC B k.2, (hC.models.cV i).1 _ k.2, mul_one, mul_one]
  exact act_ioP_inf hC hB h hψ ht _ a.2 x w

end GlobalTheory.CoefActIo

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


noncomputable section

namespace GlobalTheory.LatRatStd

variable {D : D7}

theorem finVec_mem_gLat_one (T : HSp D) (v : Fin T.rank → D.host.E) :
    Formalism.L2.Pj.finVec T v ∈ Formalism.L2.Pj.gLat T 1 ↔ v ∈ L0c D T := by
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.mem_coe]
  obtain ⟨h1, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D T
  rw [← ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E T.rank _ hfg hsp).1 v), ← h1]
  constructor
  · rintro ⟨z, hz, e⟩
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    exact hz
  · intro h
    exact ⟨_, h, by rw [map_one, Units.val_one, Matrix.one_mulVec]; rfl⟩

theorem mem_latRat_iff_cols {S T : HSp D} (hG : S.gram = 1) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)}
    (hS : LS = (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E))) (hT : LT = L0c D T)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ GlobalTheory.LatVac.latRat S T LS LT ↔ ∀ b, (fun a => M a b) ∈ Formalism.L2.Pj.latG T 1 := by
  subst hS hT
  have hg : ∀ (s : Fin S.rank → D.host.E) j, ∑ k, star (s k) * S.gram k j = star (s j) := fun s j => by
    rw [hG, Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero]) (by simp),
      Matrix.one_apply_eq, mul_one]
  constructor
  · intro hM b
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 (SetLike.mem_coe.1 hs)) b trivial)
      obtain ⟨c', hc'⟩ := GlobalTheory.DatumFourier.star_int c
      have h1 : a • t ∈ Formalism.L2.Pj.latG T 1 :=
        Submodule.subset_span ⟨a, ha, t, (finVec_mem_gLat_one T t).2 ht, rfl⟩
      convert Submodule.smul_mem _ c' h1 using 1
      funext i
      change a * t i * _ = (c' : D.host.E) * (a * t i)
      rw [hg, hc', ← hc, mul_comm]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro h
    have key : ∀ b, ∀ v ∈ Formalism.L2.Pj.latG T 1, (Matrix.of fun a j => v a * (Pi.single b 1 : Fin S.rank → D.host.E) j) ∈
        GlobalTheory.LatVac.latRat S T (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E)) (L0c D T) := by
      intro b v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hv
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single b 1, ?_, t, (finVec_mem_gLat_one T t).1 ht, ?_⟩
        · rw [SetLike.mem_coe, Formalism.L2.Pj.stdLat, Submodule.mem_pi]
          intro k _
          rw [Pi.single_apply]
          split_ifs
          · exact Submodule.mem_one.2 ⟨1, map_one _⟩
          · exact zero_mem _
        · ext i j
          simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, hg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
          split_ifs <;> simp
      | zero => convert (GlobalTheory.LatVac.latRat S T _ _).zero_mem using 1; ext i j; simp
      | add x y _ _ hx hy => convert add_mem hx hy; ext i j; simp [add_mul]
      | smul c x _ hx =>
        convert GlobalTheory.LatVac.smul_mem_latRat c hx using 1
        exact Matrix.ext fun i j => mul_assoc (c : D.host.E) (x i) _
    have e : M = ∑ b, Matrix.of fun a j => M a b * (Pi.single b 1 : Fin S.rank → D.host.E) j := by
      ext i j
      simp [Matrix.sum_apply, Pi.single_apply]
    rw [e]
    exact sum_mem fun b _ => key b _ (h b)

end GlobalTheory.LatRatStd
end
end
