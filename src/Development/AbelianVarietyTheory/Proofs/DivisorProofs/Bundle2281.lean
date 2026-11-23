module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PairingIsoPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGenericFibrePolarizationIso
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsKill

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O] (o : OAct O G) {T : Over S}

theorem comp_act_zero (x : T ⟶ G) : x ≫ o.act 0 = 1 := by
  have h : x ≫ o.act (0 + 0) = (x ≫ o.act 0) * (x ≫ o.act 0) := by rw [o.add, MonObj.comp_mul]
  rw [add_zero] at h
  exact mul_left_cancel (a := x ≫ o.act 0) (by rw [_root_.mul_one]; exact h.symm)

theorem comp_act_nat (x : T ⟶ G) (n : ℕ) : x ≫ o.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, comp_act_zero]
  | succ n ih => rw [Nat.cast_succ, o.add, MonObj.comp_mul, ih, o.one, Category.comp_id, pow_succ]

theorem comp_act_nat_mul (x : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (r : O) : x ≫ o.act ((n : O) * r) = 1 := by
  have := o.hom r
  rw [o.mul, ← Category.assoc, comp_act_nat, hx, MonObj.one_comp]

end Act

theorem weilIs_one_left (hW : Out.WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}
    (k : ℕ) (y : T ⟶ P.A) (hy : y ^ k = 1) : Out.WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨e, he, hu⟩ := (hW S P k T).1 1 y (one_pow k) hy
  have h2 := (hW S P k T).2.1 1 1 y e e he he
  rw [_root_.one_mul] at h2
  have h3 : e * e = e := hu _ h2
  have he1 : e = 1 := mul_left_cancel (a := e) (by rw [_root_.mul_one]; exact h3)
  rwa [he1] at he

theorem kill : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X ψ hψ n hn hWe u hu
  have laws := GlobalTheory.lawsFieldsSeparately
  have hWS : Out.WeilSt := laws.2.2.2.2.2.2.2.2.2.1
  have hND : Out.WeilNondegSt := laws.2.2.2.2.2.2.2.2.2.2.1
  have hBC : Out.PolBaseChangeSt := laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have u1 : unitOn (1 : ℂˣ) = 1 := map_one _

  have hgen : ∀ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G)
      (f : (X.A true).t.G ⟶ X.B.t.G), x ^ n = 1 → Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      Out.WeilIs X.B.pol.A X.B.pol.L n (x ≫ f) (u ≫ ψ) 1 := by
    intro x f hx hf hm
    obtain ⟨r, hr⟩ := hWe f hf hm
    have h := (hr n x u 1 hn hx hu).2
    rw [u1] at h
    apply h
    rw [comp_act_nat_mul _ x n hx r, Category.comp_id]
    exact weilIs_one_left hWS (X.A true).pol n u hu
  have hall : ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
      Out.WeilIs X.B.pol.A X.B.pol.L n (u ≫ ψ) y 1 := by
    intro y hy
    have hψn : (u ≫ ψ) ^ n = 1 := GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu
    suffices h : Out.WeilIs X.B.pol.A X.B.pol.L n y (u ≫ ψ) 1 by
      have := GlobalTheory.CommPairing.weilIs_symm X.B.pol.isLB h
      rwa [inv_one] at this
    have hmem := GlobalTheory.T.torsion_cmUnitaryShimura_mem_closure_linearHom_images E H hH K ρ σ₁ p X n hn y hy
    clear hy
    induction hmem using Submonoid.closure_induction with
    | mem w hw =>
      obtain ⟨x, f, hx, hf, hm, rfl⟩ := hw
      exact hgen x f hx hf hm
    | one => exact weilIs_one_left hWS X.B.pol n (u ≫ ψ) hψn
    | mul a b _ _ ha hb =>
      have := (hWS _ X.B.pol n _).2.1 a b (u ≫ ψ) 1 1 ha hb
      rwa [_root_.mul_one] at this
  exact GlobalTheory.LevelRigid.pairing_nondeg hWS hND hBC X.B.pol ℂ _ n (Nat.cast_ne_zero.2 hn.ne') (u ≫ ψ)
    (GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu) hall

end GlobalTheory.FlatCM.TorsKill
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.weilRepresentationLocality_tensorModelVW : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ k ∈ UAt σ Γ.W (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, k)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityVW.locality | exact GlobalTheory.WeilLocalityVW.locality | (intros; apply GlobalTheory.WeilLocalityVW.locality <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∃ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ GlobalTheory.WeilM.SB _ ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ (S φ) := by
  first | exact @GlobalTheory.WeilLocality.locality | exact GlobalTheory.WeilLocality.locality | (intros; apply GlobalTheory.WeilLocality.locality <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
      IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ (v : Pl (F := F)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) φ φ₁ := by
  first | exact @GlobalTheory.DblActs.dbl_acts | exact GlobalTheory.DblActs.dbl_acts | (intros; apply GlobalTheory.DblActs.dbl_acts <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityW'.locality | exact GlobalTheory.WeilLocalityW'.locality | (intros; apply GlobalTheory.WeilLocalityW'.locality <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityV.locality | exact GlobalTheory.WeilLocalityV.locality | (intros; apply GlobalTheory.WeilLocalityV.locality <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityW.locality | exact GlobalTheory.WeilLocalityW.locality | (intros; apply GlobalTheory.WeilLocalityW.locality <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaNonzeroF

theorem herm_inv_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) :
    ∀ i j, σ (J⁻¹ j i) = J⁻¹ i j := by
  have hinv : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hmap : (J⁻¹).map σ * J.map σ = 1 := by
    have := congrArg (fun M => M.map σ) hinv
    simpa [Matrix.map_mul, Matrix.map_one] using this
  have hT : (J.map σ)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have h2 : J * ((J⁻¹).map σ)ᵀ = 1 := by
    calc J * ((J⁻¹).map σ)ᵀ = (J.map σ)ᵀ * ((J⁻¹).map σ)ᵀ := by rw [hT]
      _ = 1 := by rw [← Matrix.transpose_mul, hmap, Matrix.transpose_one]
  have hX : ((J⁻¹).map σ)ᵀ = J⁻¹ := (Matrix.inv_eq_right_inv h2).symm
  intro i j
  have := congrFun (congrFun hX i) j
  simpa [Matrix.transpose_apply, Matrix.map_apply] using this

theorem exists_isThetaFunOF_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∃ f₀ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
  have hstd := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  let JA : Matrix (Fin nT) (Fin nT) E := JTᵀ
  let JB : Matrix (Fin nS) (Fin nS) E := -(ξ₀ • JS⁻¹)
  have hSinv := herm_inv_entry σ JS hS.1 (Ne.isUnit hS.2)
  have hA : ∀ i j, σ (JA j i) = JA i j := fun i j => hT.1 j i
  have hBs : ∀ i j, σ (JB j i) = -JB i j := fun i j => by
    simp only [JB, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσξ, hSinv]
    ring
  have hA' : JA.det ≠ 0 := by simp only [JA, Matrix.det_transpose]; exact hT.2
  have hB' : JB.det ≠ 0 := by
    simp only [JB, Matrix.det_neg, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : E) ≠ 0))
      (mul_ne_zero (pow_ne_zero _ hξ0) (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).ne_zero)
  obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hA hBs hA' hB'
  let co' : Darboux (symp (cA σ) (-1 : AF F ⊗[F] E) (incM F JA) (incM F JB)) (Fin nT × Fin nS) := co
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
      co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := hco
  have hJA : JA = JTᵀ := rfl
  have hJB : (-1 : AF F ⊗[F] E) • incM F JB = incM F (ξ₀ • JS⁻¹) := by
    ext i j
    simp [JB, incM]
  let τ := Fintype.equivFin (Fin nT × Fin nS)
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co' τ w) (GlobalTheory.TransportF.numCoordF co' τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hJA hJB, co'.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
      GlobalTheory.TransportF.numCoordF co' τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  obtain ⟨Φ, hΦ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin nT × Fin nS)
  refine ⟨GlobalTheory.WeilSchrodinger.thetaTr F co' B.ψ Φ, ?_, ?_⟩
  · rw [GlobalTheory.TransportF.thetaTr_eqF co' τ]
    exact GlobalTheory.T.isThetaFunction_thetaTransform_rational_coords_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hstd _ (GlobalTheory.TransportF.numCoordF co' τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  · intro h
    have h0 := congrFun h 0
    apply hne
    have hs : GlobalTheory.WeilM.schr B.ψ (0 : (Fin nT × Fin nS → AF F) × (Fin nT × Fin nS → AF F)) Φ = Φ := by
      funext x
      simp [GlobalTheory.WeilM.schr]
    simpa [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hs] using h0

end GlobalTheory.ThetaNonzeroF

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

theorem _root_.GlobalTheory.T.exists_splitPlace_conjHeisenberg_invariantForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  first | exact @GlobalTheory.SplitInvFormF.exists_invForm_split | exact GlobalTheory.SplitInvFormF.exists_invForm_split | (intros; apply GlobalTheory.SplitInvFormF.exists_invForm_split <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cuspidalRep_endomorphism_scalar_schur : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (x : CuspSub E a) (f : x.V →ₗ[ℂ] x.V), (∀ o φ, f (x.op o φ) = x.op o (f φ)) → ∃ c : ℂ, ∀ φ, f φ = c • φ := by
  first | exact @GlobalTheory.CuspSchur.schur | exact GlobalTheory.CuspSchur.schur | (intros; apply GlobalTheory.CuspSchur.schur <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

theorem _root_.GlobalTheory.T.semiabelian_generic_fibre_polarization_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → GlobalTheory.LN.SplitOver G (IsLocalRing.maximalIdeal R) → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → (∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = P.L ∧ U.gen = gen := by
  first | exact @GlobalTheory.SectionUnif.exists_unif_of_ne_zero | exact GlobalTheory.SectionUnif.exists_unif_of_ne_zero | (intros; apply GlobalTheory.SectionUnif.exists_unif_of_ne_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_charP_specialization_smooth_commGroup_curve : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (p : ℕ) (_ : Fact p.Prime) (_ : CharP k' p) (G' : Over (Sp k')) (_ : GrpObj G'), GlobalTheory.SS.SmConn G' ∧ SmoothOfRelativeDimension g G'.hom ∧ (m : k') ≠ 0 ∧ (∃ s' : Finset (𝟙_ (Over (Sp k')) ⟶ G'), (∀ x ∈ s', x ^ m = 1) ∧ s'.card = s.card) ∧ ∃ (P' : Polynomial k') (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ G'.left) (a' b' : Localization.Away P' →ₐ[k'] k'), u' ≫ G'.hom = spMap (algebraMap k' (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  first | exact @GlobalTheory.CharPSpec.exists_charP_specialization | exact GlobalTheory.CharPSpec.exists_charP_specialization | (intros; apply GlobalTheory.CharPSpec.exists_charP_specialization <;> assumption)
end
