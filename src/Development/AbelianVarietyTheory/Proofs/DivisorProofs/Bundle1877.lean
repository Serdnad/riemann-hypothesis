module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassically
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrincipalDecomp

open GlobalTheory.SphericalOps GlobalTheory.HeckeAdjoint GlobalTheory.HeckeOrthSum

theorem iSup_partH_eq_top_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ hS
  classical
  obtain ⟨hinj, hrange, -⟩ := hC.models.HW i σ
  have hrange' : LinearMap.range (R.HW i σ).e =
      Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i) := hrange
  haveI : FiniteDimensional ℂ
      (Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i)) := by
    rw [← hrange']; infer_instance
  obtain ⟨n, hB⟩ := hC.lev.βW i
  have key := mult_le_of_parts (J := Lev.levG _ (R.βW i) (R.datWp i R.triv)) (Sb := GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R)
    hC.models.inf (hC.models.νW i).1.1 (hC.models.νW i).2 hS (fun P d Rp h T hT => ?_)
    ((⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c).map (R.HW i σ).e) (fun c hc T hT => ?_)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := key (hrange' ▸ LinearMap.mem_range_self _ x)
    exact hinj e ▸ hy
  · have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [one_pow, Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
    have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
      obtain ⟨_, _, _, _, hO, -⟩ := h
      exact hO
    have hP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
      rintro PP (hP | hP)
      · exact GlobalTheory.HeckeOffLevel.sep_of_offS hO (by
          unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
          exact Finset.mem_image.2 ⟨PP, hP, rfl⟩)
      · exact absurd hP (Finset.notMem_empty _)
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine isMultMap_heckeOn hT (fun k hk => ?_) fun v => GlobalTheory.HeckeOffLevel.hasType_heckeLin hB hN hP h (hT.lev v)
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := h
    exact (hc.1 k hk).1
  · obtain ⟨y, rfl⟩ : T ∈ LinearMap.range (R.HW i σ).e := hrange' ▸ hT.1
    exact Submodule.mem_map_of_mem
      (le_iSup₂_of_le (f := fun (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c) => partH R i σ c) c hc le_rfl hT)

end GlobalTheory.PrincipalDecomp

namespace GlobalTheory.LiftLower

theorem gW_mem_partH_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ c g x hx
  unfold partH at hx ⊢
  rw [Submodule.mem_comap, mem_partFull] at hx ⊢
  refine ⟨?_, fun P d Rp hR v => ?_⟩
  · have h : (R.HW i σ).e (R.gW i σ g x) ∈ LinearMap.range (R.HW i σ).e := LinearMap.mem_range_self _ _
    rw [(hC.models.HW i σ).2.1] at h
    exact h
  have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
    obtain ⟨_, _, _, _, h, -⟩ := hR
    exact h
  obtain ⟨-, h2⟩ := GlobalTheory.offS_not_type_places R.C.P R.Pg (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P hC.lev.Pg
    (fun PP hPP => by unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF; exact Finset.mem_image.2 ⟨PP, hPP, rfl⟩) hO
  obtain ⟨a, hB⟩ := hC.lev.βW i
  have hN : (((1 ^ a : ℕ)) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))
  have hPP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    rintro PP (h | h)
    · exact h2 PP h
    · exact absurd h (Finset.notMem_empty _)
  have hT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 hx.1).lev v
  rw [hC.models.gW i σ g x, postOn_apply, ← map_smul, ← hx.2 P d Rp hR v]
  exact (GlobalTheory.HeckeKeepsGood.sphericalOperator_commute_levelFiniteGroup hB hN hPP hR hT (R.eG g)).symm

end GlobalTheory.LiftLower

namespace GlobalTheory.ConjMuChar

theorem exists_galConj_chrEq_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ s hσ μ' hμ
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hC.lev.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hC.lev.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

end GlobalTheory.ConjMuChar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

theorem exists_galConj_eta_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR σ s hσ η' hη
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [twVal_half _ P (locK_eq_one hH hη.2.1 P), twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (locU he.1 (unif P)) rfl, ← hR.lev.eta.2 P e he _ (locU he.1 (unif P)) rfl, ← hy1, ← hy2, hσ.1]

end GlobalTheory.EtaConjChar

namespace GlobalTheory.FiveClauseParts

theorem parts_conj_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) :=
  ⟨GlobalTheory.PrincipalDecomp.iSup_partH_eq_top_five, GlobalTheory.LiftLower.gW_mem_partH_five,
    GlobalTheory.ConjMuChar.exists_galConj_chrEq_five, GlobalTheory.EtaConjChar.exists_galConj_eta_five⟩

end GlobalTheory.FiveClauseParts

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem castDict_laws {D : D7} {V W : HSp D} (hV : V = W) {r : ℕ} (hr : W.rank = r) {Comp : Type}
    (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (Kf : Subgroup (GA D V)) (Kf' : Subgroup (GA D W))
    (hK : ∀ g : GA D W, g ∈ Kf' ↔ cast (congrArg (GA D) hV.symm) g ∈ Kf)
    (hu : ∃ th hr', (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr')
    (hm : ∃ hr' : V.rank = r, ∀ k, ModelW V hr' (X k)) (hmu : MuUnit V dict mu) (hc : Continuous mu) :
    (∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif W (castDict hV dict) Kf' th hr) ∧
      (∀ k, ModelW W hr (X k)) ∧ MuUnit W (castDict hV dict) (castDict hV mu) ∧ Continuous (castDict hV mu) := by
  subst hV
  obtain rfl : Kf' = Kf := Subgroup.ext hK
  obtain ⟨th, hr', h1, h2⟩ := hu
  obtain ⟨hr'', h3⟩ := hm
  exact ⟨⟨th, h1, h2⟩, h3, hmu, hc⟩

theorem goodDict_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → GoodDict R.θ (R.MW i σ) w (rank_Wc i) (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ)) (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM h hpb i σ hσ hV w hw
  obtain ⟨hK, -, hfin, hopen⟩ := GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
  have hj : InR D ((i : ℕ) + 1) := inR i
  obtain ⟨h1, h2, h3, h4⟩ := castDict_laws hV (rank_Wc i) _ _ (T.mu ((i : ℕ) + 1) (res T σ)) _ _ hK
    (h.laws.dictU _ hj _ hσ) (h.laws.modelW _ hj _ hσ) (h.laws.muUnit _ hj _ hσ) (h.laws.muCont _ hj _ hσ)
  have hc : ∀ k, ‖T.cE ((i : ℕ) + 1) (res T σ) k‖ = 1 := h.laws.cUnit _ hj _ hσ
  exact
    { inf := hM.inf
      base := GlobalTheory.T.base_frame_of_realization_models D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV
      unif := h1
      model := h2
      muUnit := h3
      muCont := h4
      chi := h.laws.chiTriv _ hj _ hσ _ _ (dom_wtA (κ i))
      cNe := fun k h0 => by
        have := hc k
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      cBdd := ⟨1, fun k => (hc k).le⟩
      fin := @Finite.of_fintype _ (T.U ((i : ℕ) + 1) (res T σ)).fin
      levFin := hfin
      levOpen := hopen
      muK := GlobalTheory.T.dictionaryChar_eq_one_on_principalLevel D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
      wt := GlobalTheory.T.extremalWeight_eq_character_exponent_add D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV w hw }

end GlobalTheory.HolDict
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

set_option autoImplicit false

noncomputable def transConn {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    (G₀ G₁ : V n → Matrix r r ℂ) (j : Fin n) (i a : Fin n) : V n → Matrix r r ℂ :=
  if i < j then fun x => -conn G₁ x (coordVec a)
  else if i = j then fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))
  else fun x => -conn G₀ x (coordVec a)

theorem weighted_bound_cut_sum (x A B w C c : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ C) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hA : A * w ≤ c) (hB : B ≤ C) : x * (A + B) * w ≤ C * (|c| + C) := by
  have h1 : (A + B) * w ≤ |c| + C := by nlinarith [le_abs_self c]
  have hC : 0 ≤ C := hx0.trans hx
  rw [mul_assoc]
  exact mul_le_mul hx h1 (by positivity) hC

theorem weighted_bound_cut_entry (x X₁ X₀ d Y₁ Y₀ : ℂ) (wa wb C c : ℝ) (hx : ‖x‖ ≤ C) (hd : ‖d‖ ≤ C)
    (hX₁ : ‖X₁‖ * (wa * wb) ≤ c) (hX₀ : ‖X₀‖ ≤ C) (hY₁ : ‖Y₁‖ * wa ≤ c) (hY₀ : ‖Y₀‖ ≤ C)
    (hwa0 : 0 ≤ wa) (hwa1 : wa ≤ 1) (hwb0 : 0 ≤ wb) (hwb1 : wb ≤ 1) :
    ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb) ≤ 2 * C * (|c| + C) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hx
  have e1 := weighted_bound_cut_sum ‖x‖ ‖X₁‖ ‖X₀‖ (wa * wb) C c (norm_nonneg _) hx (norm_nonneg _) (norm_nonneg _)
    (by positivity) (by nlinarith) hX₁ hX₀
  have e2 := weighted_bound_cut_sum ‖d‖ ‖Y₁‖ ‖Y₀‖ wa C c (norm_nonneg _) hd (norm_nonneg _) (norm_nonneg _)
    hwa0 hwa1 hY₁ hY₀
  have n1 : ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ ≤ ‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  have hww : 0 ≤ wa * wb := by positivity
  have e2' : ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) ≤ C * (|c| + C) := by
    have h0 : 0 ≤ ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa := by positivity
    calc ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) = (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * wb := by ring
      _ ≤ (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * 1 := mul_le_mul_of_nonneg_left hwb1 h0
      _ ≤ C * (|c| + C) := by rw [mul_one]; exact e2
  calc ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb)
      ≤ (‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖)) * (wa * wb) := mul_le_mul_of_nonneg_right n1 hww
    _ = ‖x‖ * (‖X₁‖ + ‖X₀‖) * (wa * wb) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) := by ring
    _ ≤ C * (|c| + C) + C * (|c| + C) := add_le_add e1 e2'
    _ = 2 * C * (|c| + C) := by ring

theorem integral_mixTop_position_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → ∀ j : Fin n, IntegrableOn (fun v => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)) (offHyp S U) ∧ ∫ v in offHyp S U, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) = 0 := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK j
  obtain ⟨C, hC0, hC⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have h3 : (2 : WithTop ℕ∞) + 1 ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hw : ∀ v ∈ U, ∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1 :=
    fun v hv a => (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv)).1 a
  have hρd : ∀ v ∈ U, ContDiffAt ℝ ∞ ρ v := fun v hv => hρ.contDiffAt (hU.mem_nhds hv)
  have hρc : ∀ v ∈ U, ContDiffAt ℝ 2 (fun x => (ρ x : ℂ)) v := fun v hv =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hρd v hv).of_le h2)
  set θ := transConn ρ G₀ G₁ j with hθ
  have hsm : ∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v := by
    intro i a v hv
    have h1 := (hG₁ v hv).1.conn (j := 2) (hG₁ v hv).2 h3 (coordVec a)
    have h0 := (hG₀ v hv.1).1.conn (j := 2) (hG₀ v hv.1).2 h3 (coordVec a)
    simp only [hθ, transConn]
    split_ifs
    · exact h1.neg
    · exact (MContDiffAt.smul (hρc v hv.1) (h1.sub h0)).neg
    · exact h0.neg
  have heq : ∀ v ∈ offHyp S U, (fun i a b => mdbar (θ i a) v (coordVec b)) =
      intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j := by
    intro v hv
    funext i a b
    simp only [hθ, transConn, intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · rw [mdbar_neg]; rfl
    · exact congrFun (congrFun (GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq ((hρd v hv.1).differentiableAt (by simp))
        ((hG₀ v hv.1).1.of_le h2) (hG₀ v hv.1).2 ((hG₁ v hv).1.of_le h2) (hG₁ v hv).2) a) b
    · rw [mdbar_neg]; rfl
  have hzero : ∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0 := by
    intro a v hv hvK
    simp [hθ, transConn, hρK v hv.1 hvK]
  have hcC : 0 ≤ C * (|c| + C) := by positivity
  have hbd1 : ∀ v ∈ offHyp S U, v ∈ K → ∀ a p q,
      ‖θ j a v p q‖ * poinWt S v a ≤ |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK a p q
    obtain ⟨hρv, -, hc0, -⟩ := hC v hvK
    simp only [hθ, transConn, lt_irrefl, if_false, if_true, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e := weighted_bound_cut_sum |ρ v| ‖conn G₁ v (coordVec a) p q‖ ‖conn G₀ v (coordVec a) p q‖ (poinWt S v a) C c
      (abs_nonneg _) hρv (norm_nonneg _) (norm_nonneg _) (hw v hv.1 a).1 (hw v hv.1 a).2
      (hconn v hv a p q) (hc0 a p q)
    have n1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)) (abs_nonneg (ρ v)))
      (hw v hv.1 a).1
    have : 0 ≤ |c| := abs_nonneg c
    nlinarith
  have hbd2 : ∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q,
      ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤
        |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK i a b p q
    obtain ⟨hρv, hdv, hc0, hk0⟩ := hC v hvK
    obtain ⟨hwa0, hwa1⟩ := hw v hv.1 a
    obtain ⟨hwb0, hwb1⟩ := hw v hv.1 b
    have hww : 0 ≤ poinWt S v a * poinWt S v b := by positivity
    have hww1 : poinWt S v a * poinWt S v b ≤ 1 := by nlinarith
    have hca : 0 ≤ |c| := abs_nonneg c
    rw [show mdbar (θ i a) v (coordVec b) = _ from congrFun (congrFun (congrFun (heq v hv) i) a) b]
    simp only [intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · have := hcurv v hv a b p q
      simp only [curvAt]
      nlinarith [le_abs_self c]
    · simp only [curvAt, cutForm, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul]
      have e := weighted_bound_cut_entry (ρ v : ℂ) (curv G₁ v (coordVec a) (coordVec b) p q) (curv G₀ v (coordVec a) (coordVec b) p q)
        (dbar (fun x => (ρ x : ℂ)) v (coordVec b)) (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
        (poinWt S v a) (poinWt S v b) C c (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hρv) (hdv b)
        (hcurv v hv a b p q) (hk0 a b p q) (hconn v hv a p q) (hc0 a p q) hwa0 hwa1 hwb0 hwb1
      nlinarith
    · simp only [curvAt]
      have := hk0 a b p q
      have := mul_le_mul_of_nonneg_left hww1 (norm_nonneg (curv G₀ v (coordVec a) (coordVec b) p q))
      nlinarith
  obtain ⟨hi, hint⟩ := GlobalTheory.T.integral_polarisedTopForm_dbarExact_eq_zero S U K θ j (|c| + C + 2 * C * (|c| + C)) hU hK hKU hsmall hsm hzero
    hbd1 hbd2
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  refine ⟨hi.congr_fun (fun v hv => congrArg mixTop (heq v hv)) hO, ?_⟩
  rw [← hint]
  exact setIntegral_congr_fun hO fun v hv => congrArg mixTop (heq v hv).symm

end GlobalTheory.GoodTop
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.tendsto_logDet_gram_change_semiPositive_metric : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  first | exact @GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub | exact GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub | (intros; apply GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  intro p _ G _ v _ L f hf K' f' _ β x t hx hreg hβ _ P
  by_cases hne : ∃ y₀ : grp G β, minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P ∧
      ∃ a : Dat G v β, FixL G v β y₀ a.2.1 ∧
        f (a.1.1⁻¹ * toAfF G β x t hx y₀ * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y₀ * a.1.2) ≠ 0
  swap
  · exact ⟨∅, fun y hy ha => absurd ⟨y, hy, ha⟩ hne⟩
  obtain ⟨y₀, hP₀, a₀, hfix₀, ha₀⟩ := hne
  obtain ⟨hdeg₀, hsep₀⟩ := hreg y₀ a₀.1.1 (left_ne_zero_of_mul ha₀) ⟨a₀.2.1, a₀.2.2, hfix₀⟩
  obtain ⟨hy₀, -⟩ := y₀.prop
  obtain ⟨S, hS⟩ := GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm p G L f hf β x t hx hβ y₀ hsep₀ hdeg₀
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G β hβ ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) (((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) hy₀ hsep₀ hdeg₀ S
  have key : ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → ∀ g : G.GAf,
      f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 → ∃ a' ∈ A, ∃ b : Bool, ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = b ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
    intro y hy g hg
    obtain ⟨c, hc⟩ := units_conj_of_minpoly_eq_of_separable G ((y : G.Cˣ × ℚˣ).1) ((y₀ : G.Cˣ × ℚˣ).1)
      (by rw [hy, hP₀]) hsep₀ hdeg₀
    have h2 := GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc
    obtain ⟨hu, hcm, hfix⟩ := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc h2
    obtain ⟨a', ha', r, e, he, hre⟩ := hA _ hu hcm hfix (fun ℓ _ hℓ => hS y g hg c hc ℓ hℓ)
    exact ⟨a', ha', decide (0 < (r : ℚ)), c, r, e, hc, he, rfl, hre⟩
  let D : G.C × Bool → grp G β → Prop := fun ab y => ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = ab.2 ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * ab.1 * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
  let ρ : G.C × Bool → grp G β := fun ab => if h : ∃ y, D ab y then h.choose else 1
  refine ⟨(A ×ˢ (Finset.univ : Finset Bool)).image ρ, ?_⟩
  rintro y hy ⟨a, _, ha⟩
  obtain ⟨a', ha', b, hD⟩ := key y hy a.1.1 (left_ne_zero_of_mul ha)
  have hex : ∃ y, D (a', b) y := ⟨y, hD⟩
  refine ⟨ρ (a', b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha', Finset.mem_univ _⟩), ?_⟩
  have hρ : ρ (a', b) = hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨c', r', e', hc', he', hb', hre'⟩ := hex.choose_spec
  dsimp only at hb' hre'
  obtain ⟨c, r, e, hc, he, hb, hre⟩ := hD
  have h2 : (hex.choose : G.Cˣ × ℚˣ).2 = (y : G.Cˣ × ℚˣ).2 := by
    rw [GlobalTheory.grp_factor_eq_of_conj p G β _ y₀ c' hc', GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc]
  refine GlobalTheory.Div.conj_of_twist p G β hex.choose y ((y₀ : G.Cˣ × ℚˣ).1) c' c (e * e'⁻¹) ((r : ℚ) / r') hc' hc h2 ?_ ?_ ?_
  · rw [Units.val_mul]
    exact he.mul_left he'.units_inv_left
  · have hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)) := by
      rw [← decide_eq_decide, hb, hb']
    rcases lt_or_gt_of_ne r'.ne_zero with h | h
    · have hn : ¬ (0 < (r : ℚ)) := fun h0 => absurd (hr.1 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r.ne_zero) h
    · exact div_pos (hr.2 h) h
  · rw [hre', hre]
    exact conj_rel_alg' G β e e' a' r r'

end GlobalTheory.LKCx.ClsReg
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.arithHilbertSamuel_rankDegree_share_le : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F), IsNef F X.LA → IsBig F X.LA → (X.R : ℤ) * X.del ≤ X.d := by
  first | exact @GlobalTheory.HSCore.share_le | exact GlobalTheory.HSCore.share_le | (intros; apply GlobalTheory.HSCore.share_le <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilDatum_split_place_reads_theta_classically : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (ΛV₁ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' Λ₁ : Lt D.host.E V.rank) (L : Lt D.host.E r), IsSelfDualC V ΛV → IsSelfDualC V ΛV₁ → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ v : Fin V.rank → D.host.E, v ∈ Λ₁ ↔ (fun j => star (v j)) ∈ ΛV₁) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ φ : TF V.rank g, Reads θ V W hr X bas idx f φ x → ∀ (e : AE D) (h : GA D V) (y : (AE D)ˣ), IsSplitIdem D e → SuppAt e V h → IsDetAt e V h y → (∀ u : WO V W, u ∈ (latO V W (ΛV₁ : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u = actO V W h 1 u₀) → Reads θ V W hr X bas idx (om (h, 1) f) ((((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ₁ ⊓ Λ').toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup).index : ℝ) ^ r) : ℂ)) • projA X bas (H.w0 : D.host.E) (tens Λ₁ L) φ) x := by
  first | exact @GlobalTheory.AdTh.SplitClass.reads_om_split | exact GlobalTheory.AdTh.SplitClass.reads_om_split | (intros; apply GlobalTheory.AdTh.SplitClass.reads_om_split <;> assumption)
end
