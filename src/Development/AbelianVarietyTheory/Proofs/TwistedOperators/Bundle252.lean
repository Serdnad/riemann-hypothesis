module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle239
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjLiftData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_galConj_mu (R : RealDat D A Ks) (hL : R.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (μ' : (AE D)ˣ →* Circle) (hμ : ChiAt R i σ μ') :
    ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hL.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hL.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

theorem exists_galConj_eta (R : RealDat D A Ks) (hL : R.Is A.μ0) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (η' : (AE D)ˣ →* Circle) (hη : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η') :
    ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [GlobalTheory.EtaConjChar.twVal_half _ P (GlobalTheory.EtaConjChar.locK_eq_one hH hη.2.1 P), GlobalTheory.EtaConjChar.twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl,
    ← hL.eta.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl, ← hy1, ← hy2, hσ.1]

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q : Finset (Pl D.host.E)} (hQ : Q = ∅) (s : ℂ →+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    s ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ => χ, ξ⟩ x : ℂˣ) : ℂ) =
      ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (Units.map s.toMonoidHom).comp (χ PP), ξ'⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp [h1]

theorem is_congr {Γ Gr W : Type} [Group Γ] [Group Gr] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gr}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gr} (hJ : J = J') {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    (h : ∀ x hx hx', χ ⟨x, hx⟩ = χ' ⟨x, hx'⟩) {I : Type} [Fintype I] {y : I → Gr} {H : HMod (Gr → W)}
    (hH : H.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y)) : H.Is (Bridge.AdForms ι ρ J' χ') (Bridge.adInner ι J' y) := by
  subst hJ
  obtain rfl : χ = χ' := MonoidHom.ext fun x => h x.1 x.2 x.2
  exact hH



theorem isLiftDataC_of_liftData : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ μ' η', ChiAt R i σ μ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ s m, GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io ∧ IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y ∧ H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L _ i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hL
  classical
  have : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  obtain ⟨s, hs⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL D.what₂.embLL σ
  have hE : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s := ⟨fun a => (hs a).symm, hσ⟩
  obtain ⟨hω, hvec, hio, -⟩ := hL
  obtain ⟨μH, hμ1, hμ2⟩ := exists_galConj_mu R hC.lev i σ s hE μ' hμ
  obtain ⟨ηH, hη1, hη2⟩ := exists_galConj_eta R hC.lev σ s hE η' hη
  have hQ := GlobalTheory.LiftLower.Q_base hC.lev
  let m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ := fun PP =>
    (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (R.chi ((i : ℕ) + 1) PP)⁻¹
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost R A.μ0 := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact GlobalTheory.LiftScalarCompare.primeToHost hC.lev PP hPP
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsConjChars R i A.μ0 s μ' η' m := by
    refine ⟨μH, ηH, hμ1, hη1, hμ2, hη2, fun PP hPP a k u hk hu => ?_⟩
    have hg : PP ∈ R.Pg := hPP.resolve_right (by simp [hQ])
    have h1 := hμ1 PP k
    have h2 := hC.lev.chi i PP hg a k u hk hu
    rw [hC.lev.xi_base, mul_one] at h1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal, Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one] at h1
    apply Units.ext
    rw [h1, ← h2]
    rfl
  have hlv : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      (R.datWp i R.triv) (R.Q A.μ0) m f₀ f := by
    have hv := hvec.vec
    rw [hQ]
    unfold Datum.IsThPVecOf at hv
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec
    have hq : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
        Datum.omegaQ ∅ (Wc D i).rank m (-1) y = Datum.omegaQ ∅ (Wc D i).rank (fun _ => 1) (-1) y := by
      intro y
      simp [Datum.omegaQ]
    simp only [GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv, hq]
    exact hv
  obtain ⟨χ', hχ, hH⟩ := hf.model
  have key : ∀ k : levJ R i A.μ0, χ' k = levFn (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)
      (Formalism.UG.bc (Lev.swapAE D) k.1.1) := fun k => Units.ext <| (hχ k).elim fun y hy =>
    hy.2.symm.trans ((hs y).symm.trans ((congrArg s hy.1).trans
      (levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hQ (s : ℂ →+* ℂ) (fun PP => (R.chi ((i : ℕ) + 1) PP)⁻¹) (R.xiR A.μ0) m _)))
  have hH' := is_congr (GlobalTheory.Survey.LevelVectorSizeBounds.grp_triv R i A.μ0 m).symm
    (χ' := GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (fun x hx _ => key ⟨x, hx⟩) hH
  refine ⟨s, m, ⟨hC, hp, hE, GlobalTheory.Survey.LevelVectorSizeBounds.isLocal_triv R, hm, hω, hvec.onb, hlv, fun P => hvec.theta P, hf.coef, hio⟩,
    hC.models.νV i A.μ0, (R.B.L i A.μ0).pres.reps, hH'⟩

end GlobalTheory.ConjLiftData

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.VacOff

variable {D : D7}

theorem placeIdem_smul_off {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D w ε) (hwv : w ≠ v) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun x => x = v) : algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hx
    have hβα : β * α = 0 := by
      refine RestrictedProduct.ext _ _ fun y => ?_
      change evalV D.host.F y (β * α) = evalV D.host.F y 0
      rw [map_mul, map_zero]
      by_cases hy : y = w
      · subst hy; rw [hP y hwv, mul_zero]
      · rw [h0 y hy, zero_mul]
    have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = (0 : AE D)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, TensorProduct.zero_tmul]
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem idemSum_mul_off {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {Pset : Finset (Pl D.host.E)} (he : IsIdemSum e Pset)
    (hv : ∀ PP ∈ Pset, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) {u : WO S T} (hu : u ∈ latO S T LS LT fun x => x = v) (a b) :
    e * u a b = 0 ∧ cA D e * u a b = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have key : ∀ PP ∈ Pset, es PP * u a b = 0 ∧ cA D (es PP) * u a b = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hw : w ≠ v := fun h => hv PP hPP (by
      rw [← h]; exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP w ε (hes PP hPP) hε a3)
    have h0 := congrFun (congrFun (placeIdem_smul_off hε hw hu) a) b
    rw [Matrix.smul_apply, smul_eq_mul, ← a3, Matrix.zero_apply] at h0
    have c1 : cA D (es PP) * cA D (es PP) = cA D (es PP) := by rw [← map_mul, a1]
    have c2 : cA D (es PP) * es PP = 0 := by rw [mul_comm, a2]
    refine ⟨?_, ?_⟩
    · linear_combination es PP * h0 - u a b * a1 - u a b * a2
    · linear_combination cA D (es PP) * h0 - u a b * c1 - u a b * c2
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).1

  · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).2

end GlobalTheory.FinZeta.VacOff


open GlobalTheory.FinZeta.VacOff in
theorem GlobalTheory.FinZeta.levVec_vacFin : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ v ∉ finS R t, VacFin R.ψ (Vc D i) (Wc D i) v f := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h
  obtain ⟨hC, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := by
    have := hpt 1
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  refine ⟨hθ, fun v hv => ⟨hθ, ?_⟩⟩
  obtain ⟨hf₀, e, he, hth⟩ := hlv
  have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (frameLat (Vc D i) : Set _) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hC.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
  have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (frameLat (Wc D i) : Set _) := by
    rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    obtain ⟨c, -, -, -, h1, h2⟩ := hC.lev.βW i
    ext x
    constructor
    · intro hx
      simpa using h2 x hx
    · intro hx
      simpa using h1 x hx
  have hlat := hf₀.2.lat
  have hle : latO (Vc D i) (Wc D i) (frameLat (Vc D i) : Set _) (frameLat (Wc D i) : Set _) (fun u => u = v) ≤
      latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
    rw [hV, hW]
    exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hoff : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := fun PP hPP h0 =>
    hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)
  have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (frameLat (Vc D i) : Set _) (frameLat (Wc D i) : Set _) (fun u => u = v),
      ∀ a b, cA D e * u a b = 0 ∧ cA D (cA D e) * u a b = 0 := fun u hu a b => by
    obtain ⟨h1, h2⟩ := idemSum_mul_off he hoff hu a b
    rw [GlobalTheory.DualPairCheck.cA_cA]
    exact ⟨h2, h1⟩
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hth (2 • u)
      (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hth u (hz u hu) (hlat.2 e' he' u (hle hu) hh)
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.GKLie

theorem epow_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) : ∀ k a b, R * epow E k a b = epow E' k a b * R := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [Formalism.REAL.epow]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    simp only [Formalism.REAL.epow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

theorem etr_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) (k : ℕ) : R * etr E k = etr E' k * R := by
  simp only [etr, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => epow_intertwine E E' R h k a a

theorem single_mul_single' {n : ℕ} (a b c d : Fin n) :
    (single a b (1 : ℂ)) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h; rw [single_mul_single_same, one_mul]
  · exact single_mul_single_of_ne _ _ _ _ h _

theorem conj_single {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P * single a b 1 * P⁻¹ = ∑ c, ∑ d, (P c a * P⁻¹ b d) • single c d (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, single_apply, Matrix.sum_apply, ite_and, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section Main

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end Main

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section KPart

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kset_facts {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) :
    κᴴ * κ = 1 ∧ κ⁻¹ = κᴴ ∧ κ * Jm ε = Jm ε * κ ∧ κᴴ * Jm ε = Jm ε * κᴴ := by
  obtain ⟨hu, hc⟩ := hκ
  have h1 : κᴴ * κ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hu
    simpa [Matrix.star_eq_conjTranspose] using hu
  refine ⟨h1, Matrix.inv_eq_left_inv h1, hc, ?_⟩
  have := congrArg conjTranspose hc
  simpa [conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem theta_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.thetaJ ε (κ * Y * κ⁻¹) = κ * PI.DSInfCharCap.thetaJ ε Y * κ⁻¹ := by
  obtain ⟨_, hinv, hc, hc'⟩ := kset_facts hκ
  rw [hinv]
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_mul, conjTranspose_conjTranspose, mul_neg, neg_mul, mul_assoc]
  rw [hc', ← mul_assoc (Jm ε) κ, ← hc, mul_assoc]

theorem cre_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cre ε (κ * Y * κ⁻¹) = κ * cre ε Y * κ⁻¹ := by
  unfold cre
  rw [theta_kconj hκ]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]

theorem cim_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cim ε (κ * Y * κ⁻¹) = κ * cim ε Y * κ⁻¹ := by
  unfold cim
  rw [theta_kconj hκ]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]

end KPart

end GlobalTheory.GKLie
end
end

section

open scoped InnerProductSpace

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta
open GlobalTheory.SmoothGlob (lieSet)

namespace GlobalTheory.GKLie

theorem dRep_conj_Kset (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ) :
    ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H,
      Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v →
      Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  intro κ hκ X hX v hv
  have h1 : κᴴ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ.1
  have h2 : κ * κᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ.1
  have hu : IsUnit κ := IsUnit.of_mul_eq_one _ h2
  have hinv : κ⁻¹ * κ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det κ).1 hu)
  have hκU : κ ∈ UJset ε := by
    change κᴴ * Jm ε * κ = Jm ε
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, a * b ∈ UJset ε := fun a ha b hb => by
    change (a * b)ᴴ * Jm ε * (a * b) = Jm ε
    have ha' : aᴴ * Jm ε * a = Jm ε := ha
    have hb' : bᴴ * Jm ε * b = Jm ε := hb
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [ha', hb']
  have hE : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ UJset ε := fun t =>
    GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t
  have hinvU : κ⁻¹ ∈ UJset ε := by
    have hκinv : κ⁻¹ = κᴴ := Matrix.inv_eq_left_inv h1
    rw [hκinv]
    change κᴴᴴ * Jm ε * κᴴ = Jm ε
    rw [Matrix.conjTranspose_conjTranspose, hκ.2, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hfun : (fun t : ℝ => ρ (NormedSpace.exp (t • (κ * X * κ⁻¹))) (ρ κ v)) =
      fun t : ℝ => ρ κ (ρ (NormedSpace.exp (t • X)) v) := by
    funext t
    have hc : NormedSpace.exp (t • (κ * X * κ⁻¹)) = κ * NormedSpace.exp (t • X) * κ⁻¹ := by
      rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
    rw [hc]
    have hA : κ * NormedSpace.exp (t • X) * κ⁻¹ ∈ UJset ε := hmul _ (hmul _ hκU _ (hE t)) _ hinvU
    rw [← ContinuousLinearMap.comp_apply, ← hρ.2 _ hA _ hκU, Matrix.mul_assoc _ κ⁻¹ κ, hinv, Matrix.mul_one,
      hρ.2 _ hκU _ (hE t), ContinuousLinearMap.comp_apply]
  unfold dRep
  rw [hfun]
  have hd := (differentiableAt_orbit hv hX).hasDerivAt
  have hL : HasFDerivAt (ρ κ) ((ρ κ).restrictScalars ℝ) (ρ (NormedSpace.exp ((0 : ℝ) • X)) v) :=
    ((ρ κ).restrictScalars ℝ).hasFDerivAt
  exact (hL.comp_hasDerivAt (0 : ℝ) hd).deriv

end GlobalTheory.GKLie
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Yc D 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (Yc D 0) (atTau R.θ (Yc D 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  first | exact @GlobalTheory.ConjEquivReal.conjMap_update_real | exact GlobalTheory.ConjEquivReal.conjMap_update_real | (intros; apply GlobalTheory.ConjEquivReal.conjMap_update_real <;> assumption)
end
