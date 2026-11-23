module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle139
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle021
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle357
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrProdInt

theorem integral_indicator_smul_of_measurePreserving {X Y Z E : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure X} {m : Measure Y} {ν : Measure Z}
    [SigmaFinite m] [SigmaFinite ν] (e : X ≃ᵐ Y × Z) (he : MeasurePreserving e μ (m.prod ν)) {B : Set Z}
    (hB : MeasurableSet B) (hBf : ν B ≠ ⊤) {a : Y → E} (ha : Integrable a m) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1) μ ∧
      ∫ x, B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1 ∂μ = (ν B).toReal • ∫ y, a y ∂m := by
  set Φ : Y × Z → E := (univ ×ˢ B).indicator (fun p => a p.1) with hΦdef
  have hΦ : (fun x => B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1) = Φ ∘ e := by
    funext x
    rw [Function.comp_apply, hΦdef]
    by_cases h : (e x).2 ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_prod.2 ⟨Set.mem_univ _, h⟩), one_smul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hm => h (Set.mem_prod.1 hm).2), zero_smul]
  have hmeasS : MeasurableSet (univ ×ˢ B : Set (Y × Z)) := MeasurableSet.univ.prod hB
  have hres : (m.prod ν).restrict (univ ×ˢ B) = m.prod (ν.restrict B) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  haveI : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hBf.lt_top⟩
  have hint : Integrable Φ (m.prod ν) := by
    rw [hΦdef, integrable_indicator_iff hmeasS, IntegrableOn, hres]
    exact ha.comp_fst _
  have hval : ∫ p, Φ p ∂(m.prod ν) = (ν B).toReal • ∫ y, a y ∂m := by
    rw [hΦdef, integral_indicator hmeasS, hres, integral_fun_fst]
    simp [Measure.real]
  rw [hΦ]
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).2 hint, ?_⟩
  rw [show (∫ x, (Φ ∘ e) x ∂μ) = ∫ x, Φ (e x) ∂μ from rfl, he.integral_comp' Φ]
  exact hval

theorem integral_indicatorFin_smul_arch : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (B : Set (GFin D.sp.cm.sig V.gram)), MeasurableSet B → νF B ≠ ⊤ → ∀ (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E), Integrable a (Measure.pi μa) → Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧ ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa := by
  intro D V μa μf μ hμ νF hF E _ _ _ B hB hBf a ha
  haveI := SelfDual.isLattice_frameLat V
  have hmap := hμ.map_archFin hF
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.1
  haveI : νF.IsHaarMeasure := hF.2.2.1
  haveI : ∀ w, SigmaFinite (μa w) := fun w => inferInstance
  haveI : SigmaFinite (Measure.pi μa) := Measure.pi.sigmaFinite _
  haveI : SigmaFinite νF := inferInstance
  exact integral_indicator_smul_of_measurePreserving
    (archFinEquiv D.sp.cm.sig V.gram).toHomeomorph.toMeasurableEquiv
    ⟨(archFinEquiv D.sp.cm.sig V.gram).toHomeomorph.toMeasurableEquiv.measurable, hmap⟩ hB hBf ha

end GlobalTheory.TrProdInt
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocIsoConj

open Formalism.UG

theorem conj_unitary {R : Type} [CommRing R] (σ : R →+* R) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) (g : Matrix n n R)
    (hg : cT σ g * J * g = J) : cT σ (a * g * b) * J' * (a * g * b) = J' := by
  calc cT σ (a * g * b) * J' * (a * g * b) = cT σ b * (cT σ g * (cT σ a * J' * a) * g) * b := by
        rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ b * (cT σ a * J' * a) * b := by rw [hJ, hg]
    _ = cT σ (a * b) * J' * (a * b) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]

def conjHom {R : Type} [CommRing R] {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1) :
    Matrix n n R →* Matrix m m R where
  toFun g := a * g * b
  map_one' := by rw [Matrix.mul_one, hab]
  map_mul' g h := by
    calc a * (g * h) * b = a * g * (b * a) * h * b := by rw [hba, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_equiv {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (σ : R →+* R)
    {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) :
    ∃ φ : UJ σ J ≃ₜ* UJ σ J', ∀ g, ((φ g).1 : Matrix m m R) = a * (g.1 : Matrix n n R) * b := by
  have hJ' : cT σ b * J * b = J' := by
    rw [← hJ]
    calc cT σ b * (cT σ a * J' * a) * b = cT σ (a * b) * J' * (a * b) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hc : ∀ {k l : Type} [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] (x : Matrix l k R)
      (y : Matrix k l R), Continuous fun g : Matrix k k R => x * g * y := by
    intro k l _ _ _ _ x y
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let φ₀ : UJ σ J →* GL m R := (Units.map (conjHom a b hab hba)).comp (UJ σ J).subtype
  let ψ₀ : UJ σ J' →* GL n R := (Units.map (conjHom b a hba hab)).comp (UJ σ J').subtype
  have hφU : ∀ g, φ₀ g ∈ UJ σ J' := fun g => conj_unitary σ a b hab J J' hJ _ g.2
  have hψU : ∀ g, ψ₀ g ∈ UJ σ J := fun g => conj_unitary σ b a hba J' J hJ' _ g.2
  let φ : UJ σ J →* UJ σ J' := φ₀.codRestrict _ hφU
  let ψ : UJ σ J' →* UJ σ J := ψ₀.codRestrict _ hψU
  have hφc : Continuous φ :=
    ((Continuous.units_map _ (hc a b)).comp continuous_subtype_val).subtype_mk _
  have hψc : Continuous ψ :=
    ((Continuous.units_map _ (hc b a)).comp continuous_subtype_val).subtype_mk _
  have l : ∀ g, ψ (φ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show b * (a * (g.1 : Matrix n n R) * b) * a = g.1
    calc b * (a * (g.1 : Matrix n n R) * b) * a = (b * a) * (g.1 : Matrix n n R) * (b * a) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hba, Matrix.one_mul, Matrix.mul_one]
  have r : ∀ g, φ (ψ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show a * (b * (g.1 : Matrix m m R) * a) * b = g.1
    calc a * (b * (g.1 : Matrix m m R) * a) * b = (a * b) * (g.1 : Matrix m m R) * (a * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hab, Matrix.one_mul, Matrix.mul_one]
  exact ⟨{ toFun := φ, invFun := ψ, left_inv := l, right_inv := r, map_mul' := map_mul φ,
            continuous_toFun := hφc, continuous_invFun := hψc }, fun g => rfl⟩

theorem exists_locIso : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E) (v : HeightOneSpectrum (𝓞 F)) (a : Matrix (Fin r') (Fin r) (Fv F v ⊗[F] E)) (b : Matrix (Fin r) (Fin r') (Fv F v ⊗[F] E)), a * b = 1 → b * a = 1 → Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a * JR (F := F) (Fv F v) J' * a = JR (F := F) (Fv F v) J → ∃ φ : GLoc σ J v ≃ₜ* GLoc σ J' v, ∀ g, (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val = a * (GlobalTheory.AdelicU.matHom _ σ J g).val * b := by
  intro F E _ _ _ _ _ σ r r' J J' v a b hab hba hJ
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨φ, hφ⟩ := exists_equiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a b hab hba _ _ hJ
  exact ⟨φ, hφ⟩

end GlobalTheory.LocIsoConj
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PrinFixedRep

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}

theorem mem_fixed_iff {x : W} :
    x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) ↔
      ∀ h : GfC V, (h : GA D V) ∈ levG V β (flag1L L) → σ h x = x := by
  unfold GlobalTheory.PRep.fixed GlobalTheory.PRep.eig
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro H h hh
    exact H ⟨h, (Subgroup.mem_subgroupOf).2 hh⟩
  · intro H h
    exact H h ((Subgroup.mem_subgroupOf).1 h.2)

theorem act_eq_of_lifts {g0 : G0 L.Pg L.r} {κ κ' : GfC V} (hκ : IsLevelLift V β L g0 κ)
    (hκ' : IsLevelLift V β L g0 κ') {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) : σ κ' x = σ κ x := by
  have hm : ((κ⁻¹ * κ' : GfC V) : GA D V) ∈ levG V β (flag1L L) := by
    simpa using lift_div_mem hκ hκ'
  have e : κ' = κ * (κ⁻¹ * κ') := by group
  rw [e, map_mul, Module.End.mul_apply, (mem_fixed_iff.1 hx) _ hm]

theorem act_mem_fixed {g0 : G0 L.Pg L.r} {κ : GfC V} (hκ : IsLevelLift V β L g0 κ) {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) :
    σ κ x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) := by
  rw [mem_fixed_iff] at hx ⊢
  intro h hh
  have hc := (GlobalTheory.FlagAction.conj_mem_flag1 hκ hh).1
  have hc' : ((κ⁻¹ * (h * κ) : GfC V) : GA D V) ∈ levG V β (flag1L L) := by simpa using hc
  have e : h * κ = κ * (κ⁻¹ * (h * κ)) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hx _ hc']

theorem main : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
    ∃ ρ : Representation ℂ (G0 L.Pg L.r) (GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))),
      ∀ (g0 : G0 L.Pg L.r) (κ : GfC V), IsLevelLift V β L g0 κ → ∀ x, (ρ g0 x : W) = σ κ x := by
  intro D V β L hl W _ _ σ
  let lift : G0 L.Pg L.r → GfC V := fun g0 => ⟨(hl g0).choose, (hl g0).choose_spec.1⟩
  have hlift : ∀ g0, IsLevelLift V β L g0 (lift g0) := fun g0 => (hl g0).choose_spec
  let F := GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))
  have hs : ∀ g0, ∀ x ∈ F, σ (lift g0) x ∈ F := fun g0 x hx => act_mem_fixed (hlift g0) hx
  let ρ : Representation ℂ (G0 L.Pg L.r) F :=
    { toFun := fun g0 => (σ (lift g0)).restrict (hs g0)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show σ (lift 1) x = x
        have h1 : IsLevelLift V β L 1 ((1 : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_one_of_mem (Subgroup.one_mem _)
        rw [act_eq_of_lifts h1 (hlift 1) x.2, map_one, Module.End.one_apply])
      map_mul' := fun g g' => LinearMap.ext fun x => Subtype.ext (by
        show σ (lift (g * g')) x = σ (lift g) (σ (lift g') x)
        have hm : IsLevelLift V β L (g * g') ((lift g * lift g' : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_mul (hlift g) (hlift g')
        rw [act_eq_of_lifts hm (hlift (g * g')) x.2, map_mul, Module.End.mul_apply]) }
  refine ⟨ρ, fun g0 κ hκ x => ?_⟩
  show σ (lift g0) x = σ κ x
  exact act_eq_of_lifts hκ (hlift g0) x.2

end GlobalTheory.PrinFixedRep

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.SchurAdm

theorem schur_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id :=
  _root_.GlobalTheory.SchurAdmissibility.schur_admissible

end GlobalTheory.SchurAdm
end
end

section

open GlobalTheory.SepPer Finset

namespace GlobalTheory.SepSum

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem hsn_eq_norm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hsn X = ‖X‖ := by
  rw [Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
  congr 1
  simp only [Real.rpow_two]

theorem hsn_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn X := Real.sqrt_nonneg _

theorem finrank_mat (n : ℕ) : Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * n ^ 2 := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  simp only [Fintype.card_fin]
  ring

theorem dyadic (x : ℝ) (hx : 0 ≤ x) :
    (2 : ℝ) ^ Nat.log 2 ⌊1 + x⌋₊ ≤ 1 + x ∧ 1 + x < (2 : ℝ) ^ (Nat.log 2 ⌊1 + x⌋₊ + 1) := by
  have h0 : ⌊1 + x⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
  constructor
  · have h1 := Nat.pow_log_le_self 2 h0
    have h2 : ((2 ^ Nat.log 2 ⌊1 + x⌋₊ : ℕ) : ℝ) ≤ (⌊1 + x⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊1 + x⌋₊
    have h2 : ((⌊1 + x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊1 + x⌋₊).succ : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact (Nat.lt_floor_add_one _).trans_le h2

theorem sum_prod_inv_two_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Finset (ι → ℕ)) :
    ∑ j ∈ T, ∏ v, ((2 : ℝ) ^ j v)⁻¹ ≤ 2 ^ Fintype.card ι := by
  set M := T.sup fun j => univ.sup j
  have hsub : T ⊆ Fintype.piFinset fun _ : ι => range (M + 1) := by
    intro j hj
    rw [Fintype.mem_piFinset]
    intro v
    rw [mem_range, Nat.lt_succ_iff]
    exact (le_sup (f := j) (mem_univ v)).trans (le_sup (f := fun j => univ.sup j) hj)
  refine (sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity).trans ?_
  rw [← Finset.prod_univ_sum (fun _ : ι => range (M + 1)) (fun _ k => ((2 : ℝ) ^ k)⁻¹)]
  calc ∏ v : ι, ∑ k ∈ range (M + 1), ((2 : ℝ) ^ k)⁻¹ ≤ ∏ _v : ι, (2 : ℝ) :=
        prod_le_prod₀ (fun _ _ => by positivity) fun v _ => by
          have := sum_geometric_two_le (M + 1)
          simpa [one_div, inv_pow] using this
    _ = 2 ^ Fintype.card ι := by simp

theorem card_box_le {ι : Type} [Fintype ι] [Nonempty ι] (n : ℕ) (hn : n ≠ 0) (la : ℝ) (hla : 0 < la) (hla1 : la ≤ 1)
    (T : Finset (ι → Matrix (Fin n) (Fin n) ℂ))
    (hT : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v))
    (j : ι → ℕ) (hj : ∀ s ∈ T, ∀ v, hsn (s v) ≤ (2 : ℝ) ^ (j v + 1)) :
    (T.card : ℝ) ≤ 6 ^ (2 * n ^ 2 * Fintype.card ι) * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) *
      (∏ v, (2 : ℝ) ^ j v) ^ (2 * n ^ 2) := by
  set f := Fintype.card ι with hf
  set N := 2 * n ^ 2 with hN
  have hf0 : f ≠ 0 := Fintype.card_ne_zero
  have hN1 : 1 ≤ N := by have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hn); omega
  have hP := GlobalTheory.packing_geometric_mean_separated ι (fun _ => Matrix (Fin n) (Fin n) ℂ) N hN1
    (fun _ => finrank_mat n) la (T : Set _) (fun v => (2 : ℝ) ^ (j v + 1)) hla (fun v => by positivity) ?sep
  case sep =>
    intro s hs s' hs' hne
    have h := hT s hs s' hs' hne
    simp only [← hsn_eq_norm]
    calc la = (la ^ f) ^ ((1 : ℝ) / f) := by rw [one_div, Real.pow_rpow_inv_natCast hla.le hf0]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by positivity)
  have hset : {s ∈ (T : Set (ι → Matrix (Fin n) (Fin n) ℂ)) | ∀ v, ‖s v‖ ≤ (2 : ℝ) ^ (j v + 1)} = (T : Set _) := by
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_coe, and_iff_left_iff_imp]
    intro hs v
    rw [← hsn_eq_norm]
    exact hj s hs v
  have hc := hP.2
  rw [hset, Set.ncard_coe_finset] at hc
  set Pr : ℝ := ∏ v, (2 : ℝ) ^ (j v + 1) with hPr
  have hPr' : Pr = (∏ v, (2 : ℝ) ^ j v) * 2 ^ f := by
    simp only [hPr, pow_succ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf]
  have hPr1 : 1 ≤ Pr := by
    rw [hPr, Finset.prod_pow_eq_pow_sum]
    exact one_le_pow₀ (by norm_num)
  have hPr0 : 0 ≤ Pr := by linarith
  set G : ℝ := Pr ^ ((1 : ℝ) / f) with hG
  have hGf : G ^ f = Pr := by rw [hG, one_div, Real.rpow_inv_natCast_pow hPr0 hf0]
  have hG1 : 1 ≤ G := Real.one_le_rpow hPr1 (by positivity)
  have h3 : 1 + 2 * G / la ≤ 3 * G / la := by
    have : G ≤ G / la := le_div_self (by linarith) hla hla1
    have e : 3 * G / la = G / la + 2 * G / la := by ring
    rw [e]; linarith
  calc (T.card : ℝ) ≤ (1 + 2 * G / la) ^ (N * f) := hc
    _ ≤ (3 * G / la) ^ (N * f) := pow_le_pow_left₀ (by positivity) h3 _
    _ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * (G ^ f) ^ N := by
      rw [div_eq_mul_inv, mul_pow, mul_pow, ← pow_mul, mul_comm f N]; ring
    _ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * Pr ^ N := by rw [hGf]
    _ = _ := by
      rw [hPr', show (6 : ℝ) = 3 * 2 by norm_num, mul_pow, mul_pow, ← pow_mul]
      ring

theorem sum_weights_le_of_separated : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ la : ℝ, 0 < la → la ≤ 1 → ∀ S : Finset (ι → Matrix (Fin n) (Fin n) ℂ),
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v)) →
      ∑ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * n ^ 2 + 1))⁻¹ ≤ C * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) := by
  intro ι _ _ n
  classical
  refine ⟨6 ^ (2 * n ^ 2 * Fintype.card ι) * 2 ^ Fintype.card ι, by positivity, ?_⟩
  intro la hla hla1 S hS
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hcard : S.card ≤ 1 :=
      Finset.card_le_one.mpr fun a _ b _ => funext fun v => Matrix.ext fun i _ => i.elim0
    have hterm : ∀ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * 0 ^ 2 + 1))⁻¹ ≤ (1 : ℝ) := fun s _ =>
      Finset.prod_le_one₀ (fun v _ => by have := hsn_nonneg (s v); positivity)
        fun v _ => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hsn_nonneg (s v)]))
    calc _ ≤ ∑ s ∈ S, (1 : ℝ) := sum_le_sum hterm
      _ = S.card := by simp
      _ ≤ 1 := by exact_mod_cast hcard
      _ ≤ _ := by
        have : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
        simpa using this
  · set N := 2 * n ^ 2 with hN
    set f := Fintype.card ι with hf
    let jf : (ι → Matrix (Fin n) (Fin n) ℂ) → ι → ℕ := fun s v => Nat.log 2 ⌊1 + hsn (s v)⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := jf) (t := S.image jf) (fun s hs => Finset.mem_image_of_mem jf hs)]
    have hbox : ∀ j ∈ S.image jf, ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤
        6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹ := by
      intro j _
      have hb : ∀ s ∈ S.filter (fun s => jf s = j),
          ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤ ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := by
        intro s hs
        rw [Finset.mem_filter] at hs
        refine prod_le_prod₀ (fun v _ => by have := hsn_nonneg (s v); positivity) fun v _ => ?_
        have hd := (dyadic _ (hsn_nonneg (s v))).1
        rw [← hs.2]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hd _)
      have hcard := card_box_le n hn.ne' la hla hla1 (S.filter (fun s => jf s = j))
        (fun s hs s' hs' hne => hS s (mem_filter.1 hs).1 s' (mem_filter.1 hs').1 hne) j (by
          intro s hs v
          rw [mem_filter] at hs
          have hd := (dyadic _ (hsn_nonneg (s v))).2
          rw [← hs.2]
          linarith)
      calc _ ≤ ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := sum_le_sum hb
        _ = (S.filter (fun s => jf s = j)).card * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (6 ^ (N * f) * la⁻¹ ^ (N * f) * (∏ v, (2 : ℝ) ^ j v) ^ N) * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by
          rw [mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun v _ => ?_
          have h2 : ((2 : ℝ) ^ j v) ≠ 0 := by positivity
          rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h2), one_mul]
    calc _ ≤ ∑ j ∈ S.image jf, 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹ := sum_le_sum hbox
      _ = 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∑ j ∈ S.image jf, ∏ v, ((2 : ℝ) ^ j v)⁻¹ := by rw [mul_sum]
      _ ≤ 6 ^ (N * f) * la⁻¹ ^ (N * f) * 2 ^ f :=
        mul_le_mul_of_nonneg_left (sum_prod_inv_two_le _) (by positivity)
      _ = _ := by ring

end GlobalTheory.SepSum
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitSign.exists_split_sign | exact GlobalTheory.SplitSign.exists_split_sign | (intros; apply GlobalTheory.SplitSign.exists_split_sign <;> assumption)
end
