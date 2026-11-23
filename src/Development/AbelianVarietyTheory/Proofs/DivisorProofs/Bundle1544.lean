module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle196
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle001
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.PlaceIdemSum

open GlobalTheory.CompanionTheory.SaGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem idem_eq_sum (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F)
    (h : IsPlacesIdem S₁ S₂ ε) :
    ε = ∑ w ∈ S₁, (placeMapInf w).inj 1 + ∑ v ∈ S₂, (placeMapFin v).inj 1 := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine adele_ext ?_ (finAdele_ext fun u => ?_)
  · have hfin : ∀ v ∈ S₂, fstA F ((placeMapFin v).inj 1) = 0 := fun v _ => rfl
    have hinf : ∀ w ∈ S₁, fstA F ((placeMapInf w).inj 1) = singleI w 1 := fun w _ => rfl

    rw [map_add (f := _), map_sum, map_sum, Finset.sum_congr rfl hfin, Finset.sum_const_zero, add_zero,
    Finset.sum_congr rfl hinf]
    refine ainf_ext fun u => ?_
    change fstA F ε u = (∑ w ∈ S₁, (singleI w 1 : ∀ u : InfinitePlace F, u.Completion)) u
    refine Eq.trans ?_ (Finset.sum_apply u S₁ (fun w => (singleI w 1 : ∀ u : InfinitePlace F, u.Completion))).symm
    by_cases hu : u ∈ S₁
    · rw [h1 u hu, Finset.sum_eq_single u (fun w _ hw => singleI_ne (Ne.symm hw) 1) (fun h => absurd hu h),
        singleI_self]
    · rw [h2 u hu, Finset.sum_eq_zero fun w hw => singleI_ne (fun e : u = w => hu (e ▸ hw)) 1]
  · have hinf : ∀ w ∈ S₁, sndA F ((placeMapInf w).inj 1) = 0 := fun w _ => rfl
    have hfin : ∀ v ∈ S₂, sndA F ((placeMapFin v).inj 1) = singleV F v 1 := fun v _ => rfl

    rw [map_add (f := _), map_sum, map_sum, Finset.sum_congr rfl hinf, Finset.sum_const_zero, zero_add,
    Finset.sum_congr rfl hfin, map_sum]
    by_cases hu : u ∈ S₂
    · rw [h3 u hu, Finset.sum_eq_single u (fun v _ hv => StrongApprox.evalV_single_ne (Ne.symm hv) 1)
        (fun h => absurd hu h), StrongApprox.evalV_single_same]
    · rw [h4 u hu, Finset.sum_eq_zero fun v hv => StrongApprox.evalV_single_ne (fun e : u = v => hu (e ▸ hv)) 1]

theorem iB_tmul {K : Type} [Field K] [Algebra F K] [TopologicalSpace K] (P : PlaceMap F K) (y : K) (e : E) :
    iB (E := E) P (y ⊗ₜ[F] e) = P.inj y ⊗ₜ[F] e := rfl

theorem iB_map_tmul {K : Type} [Field K] [Algebra F K] [TopologicalSpace K] (P : PlaceMap F K) (x : AF F) (e : E) :
    iB P (Algebra.TensorProduct.map P.proj (AlgHom.id F E) (x ⊗ₜ[F] e)) = (P.inj 1 * x) ⊗ₜ[F] e := by
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, iB_tmul, P.inj_proj]

theorem idem_mul_eq_sum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ a : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * a =
      ∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w)
          (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapInf w).proj (AlgHom.id F E) a) +
        ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v)
          (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapFin v).proj (AlgHom.id F E) a) := by
  intro F E _ _ _ _ S₁ S₂ ε hε a
  induction a using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, Finset.sum_const_zero, add_zero]
  | tmul x e =>
    simp only [iB_map_tmul]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul,
      ← TensorProduct.add_tmul, ← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ← idem_eq_sum S₁ S₂ ε hε]
  | add a b ha hb =>
    rw [mul_add, ha, hb]
    simp only [map_add (f := _), Finset.sum_add_distrib]
    abel

end GlobalTheory.PlaceIdemSum
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq : ∀ (p q : ℕ) (Z : Mat p q), ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  first | exact @GlobalTheory.HoweD.upq_span | exact GlobalTheory.HoweD.upq_span | (intros; apply GlobalTheory.HoweD.upq_span <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjCharUnique

theorem eq_of_conj_on_finite {D : D7} {σ : D.what₂.LL →+* ℂ} {μ μ' μ'' : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D μ') (g1 : IsHeckeChar D μ'')
    (h : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ' x : Circle) : ℂ) = σ y)
    (g : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ'' x : Circle) : ℂ) = σ y) : μ' = μ'' := by
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (μ' * μ''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h y hy
  obtain ⟨b, hb, hb'⟩ := g y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.symm.trans hb)
  exact Subtype.ext (ha'.trans hb'.symm)

end GlobalTheory.ConjCharUnique
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetOnto

theorem sigR_mem_intAE (D : D7) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha,
      ⟨D.sp.cm.sig x, (x.2 : IsIntegral ℤ (x : D.host.E)).map D.sp.cm.sig.toRingHom.toIntAlgHom⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem sigR_sigR (D : D7) (a : Af D.host.F ⊗[D.host.F] D.host.E) :
    sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul a b => exact congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_star b)
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ext_parts (D : D7) {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  exact Prod.ext ((he a).1.trans (h1.trans (he b).1.symm)) ((he a).2.trans (h2.trans (he b).2.symm))

theorem norm_one {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) {a b : R} (h : a * b = 1) :
    a * σ b * σ (a * σ b) = 1 := by
  have h' := congrArg σ h
  rw [map_mul, map_one] at h'
  rw [map_mul, hσ]
  linear_combination (σ a * σ b) * h + h'

theorem infPart_det {D : D7} (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) : infPart D (matHom V k).1.det = 1 := by
  have h : infHom V k = 1 := hk
  have h' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  rw [← h', h, Units.val_one, Matrix.det_one]

theorem infPart_sigR (D : D7) (x : AE D) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) :=
  GlobalTheory.DetRootCong.map_sigR _ _ x

end GlobalTheory.DetOnto
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitDetRoot

theorem infPart_sigR_one (D : D7) (x : AE D) (hx : infPart D x = 1) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = 1 := by
  have h := GlobalTheory.DetRootCong.map_sigR (F := D.host.F) (E := D.host.E)
    (AlgHom.fst D.host.F (InfiniteAdeleRing D.host.F) (Af D.host.F)) D.sp.cm.sig x
  refine h.trans ?_
  exact (congrArg _ hx).trans (map_one _)

end GlobalTheory.UnitDetRoot
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.lifts_equivariant_twisted_and_plain_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.phase → R.PGEquiv F → (∀ t g (v : (A3.A.MtildeCSD t).Forms), R.Th t (R.jX t (A3.A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) ∧ ∀ i t g (v : (A3.A.MtCSD i t).Forms), R.thG i t (R.jV i t (A3.A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A3.A) g (R.thG i t (R.jV i t v)) := by
  first | exact @GlobalTheory.GEqBr.geq_br | exact GlobalTheory.GEqBr.geq_br | (intros; apply GlobalTheory.GEqBr.geq_br <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.EEg3_eq_univ_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (⨆ p, R.EEp3 p) = ⊤ → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) = ⊤ := by
  first | exact @GlobalTheory.PrincipalRows.principal_level_rows_eq_top | exact GlobalTheory.PrincipalRows.principal_level_rows_eq_top | (intros; apply GlobalTheory.PrincipalRows.principal_level_rows_eq_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.orthogonal_rowParts_of_distinct_types : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ p q, p ≠ q → ∀ e ∈ R.EEp3 p, ∀ e' ∈ R.EEp3 q, ⟪e, e'⟫_ℂ = 0 := by
  first | exact @GlobalTheory.Div.inner_EEp3_eq_zero_of_ne | exact GlobalTheory.Div.inner_EEp3_eq_zero_of_ne | (intros; apply GlobalTheory.Div.inner_EEp3_eq_zero_of_ne <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjForms

theorem exists_conjChar {J K : Type} [Group J] [Field K] (σ₀ σ : K →+* ℂ) (χ : J →* ℂˣ)
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) :
    ∃ χ' : J →* ℂˣ, ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ) ∧ σ y = ((χ' k : ℂˣ) : ℂ) := by
  choose y hy using hχ
  have h0 : ∀ k, σ (y k) ≠ 0 := fun k h => by
    have h1 := hy k
    rw [(map_eq_zero σ).1 h, map_zero] at h1
    exact (χ k).ne_zero h1.symm
  have hm : ∀ k k', y (k * k') = y k * y k' := fun k k' => σ₀.injective (by
    rw [map_mul, hy, hy, hy, map_mul, Units.val_mul])
  refine ⟨MonoidHom.mk' (fun k => Units.mk0 _ (h0 k)) fun k k' => Units.ext ?_, fun k => ⟨y k, hy k, rfl⟩⟩
  simp only [Units.val_mul, Units.val_mk0, hm, map_mul]

theorem exists_baseChange {G Γ W W' K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W'] [Field K] [NumberField K] [StarRing K]
    [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} (σ : K →+* ℂ) {ρ : Γ →* Module.End ℂ W}
    (ρ' : Γ →* Module.End ℂ W') {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (c₁ : M →ₛₗ[σ] W') (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, (∀ v, c₀ (T v) = ρ γ (c₀ v)) ∧ ∀ v, c₁ (T v) = ρ' γ (c₁ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) :
    ∃ (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H),
      (∃ χ' : J →* ℂˣ, (∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ) ∧ σ y = ((χ' k : ℂˣ) : ℂ)) ∧
        H.Is (Bridge.AdForms ι ρ' J χ') (Bridge.adInner ι J P.y)) ∧
      ∀ x h, ∃ v, P.extL x h = c₀ v ∧ H.e (j x) h = c₁ v := by
  obtain ⟨χ', hχ'⟩ := exists_conjChar σ₀ σ χ hχ
  obtain ⟨H, hH⟩ := GlobalTheory.AdFormsModel.exists_hmod_adForms G Γ W' ι ρ' J χ' S.Cl P.y P.reps
    fun c => Finite.of_equiv _ (P.stabI c).toEquiv
  have hinj : Function.Injective c₀ := by
    intro v v' h
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨x', rfl⟩ := e.surjective v'
    rw [← he, ← he] at h
    rw [GlobalTheory.PresBasic.coef_injective P h]
  have hv : ∀ (x : S.Forms) h, ∃ v, P.extL x h = c₀ v := by
    intro x h
    obtain ⟨y, hy, -⟩ := hχ' (P.decK h)
    obtain ⟨T, hT, -⟩ := hact (P.decG h)
    refine ⟨y • T (e ((x : S.Cl → S.V) (P.decC h))), ?_⟩
    rw [map_smulₛₗ, hy, hT, ← he]
    rfl
  choose v hv using hv
  obtain ⟨j, hj⟩ := GlobalTheory.HilbertModel.exists_lift_fun σ hH (fun x h => c₁ (v x h))
    (fun a b => by
      funext h
      have : v (a + b) h = v a h + v b h := hinj (by rw [map_add (f := _), ← hv, ← hv, ← hv, map_add (f := _)]; rfl)
      rw [this, map_add (f := _)]; rfl)
    (fun c a => by
      funext h
      have : v (c • a) h = c • v a h := hinj (by rw [map_smulₛₗ, ← hv, ← hv, map_smulₛₗ]; rfl)
      rw [this, map_smulₛₗ]; rfl)
    (fun a γ h k => by
      obtain ⟨y, hy, hy'⟩ := hχ' k
      obtain ⟨T, hT, hT'⟩ := hact γ
      have : v a (ι γ * h * k) = y • T (v a h) := hinj (by
        rw [map_smulₛₗ, hy, hT, ← hv, ← hv]
        exact GlobalTheory.PresBasic.extMem P a γ h k)
      show c₁ (v a (ι γ * h * k)) = _
      rw [this, map_smulₛₗ, hy', hT'])
  exact ⟨H, j, ⟨χ', hχ', hH⟩, fun x h => ⟨v x h, hv x h, congrFun (hj x) h⟩⟩

theorem factor_mem {I : Type} [Fintype I] {k : I → Type} [∀ a, CommRing (k a)] {r : ℕ} (hr : 0 < r) (S : Subfield ℂ)
    (c : ∀ a, (k a)ˣ →* ℂˣ)
    (h : ∀ g : ∀ a, GL (Fin r) (k a), (∏ a, ((c a (Matrix.GeneralLinearGroup.det (g a)) : ℂˣ) : ℂ)) ∈ S)
    (a : I) (u : (k a)ˣ) : ((c a u : ℂˣ) : ℂ) ∈ S := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin r) (R := k a) u
  have h1 := h (Pi.mulSingle a g)
  rw [Finset.prod_eq_single a] at h1
  · rwa [Pi.mulSingle_eq_same, hg] at h1
  · intro b _ hb
    simp [Pi.mulSingle_eq_of_ne hb]
  · simp

theorem levFn_mem {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n) (S : Subfield ℂ)
    (hg : ∀ PP ∈ L.Pg, ∀ c u, ((L.cg c PP u : ℂˣ) : ℂ) ∈ S) (hq : L.Q = ∅) (x : GL (Fin n) (Lev.EAf D)) :
    ((levFn β (Lev.flag1L L) x : ℂˣ) : ℂ) ∈ S := by
  have h1 : ext1 (Lev.flag1L L).P.H (Lev.flag1L L).P.chi (rTup β (Lev.flag1L L) x) = 1 := Lev.subgroupCharExtension_one_apply _ _
  have h2 : (Lev.flag1L L).Q = ∅ := hq
  unfold levFn
  rw [h1, h2, one_mul, Finset.prod_empty, mul_one, Units.coe_prod]
  refine prod_mem fun PP hP => ?_
  rw [Units.coe_prod]
  exact prod_mem fun c _ => hg PP hP _ _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, hγ⟩ := γ
  unfold GQ HFinIn at hγ
  obtain ⟨g, -, hg⟩ := hγ
  exact ⟨g, hg.symm⟩

theorem chi_mem (R : RealDat D A Ks) (hW : R.grp_chiW) (i : Fin D.R.m) (PP : Pl D.host.E) (hP : PP ∈ R.Pg) (u : (kP PP)ˣ) :
    ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  refine factor_mem (I := R.Pg) (k := fun PP => kP PP.1) hr _ (fun PP => R.chi ((i : ℕ) + 1) PP.1) (fun g => ?_) ⟨PP, hP⟩ u
  have h := hW i (R.eG.symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact ⟨_, h⟩

theorem levChar_mem (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (i : Fin D.R.m) (k : levJ R i A.μ0) :
    ∃ y, D.what₂.embLL y = (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) := by
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl hP) ?_
    rw [hL.xi_base]
    intro x _
    rfl
  refine levFn_mem (R.βV i) (R.datVt i A.μ0) D.what₂.embLL.fieldRange (fun PP hP c u => ?_) hQ _
  show (((R.chi ((i : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ) ∈ _
  rw [Units.val_inv_eq_inv_val]
  exact inv_mem (chi_mem R hW i PP hP u)


end GlobalTheory.ConjForms

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.baseTuple_pins_orientation_standardFrame_levelMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → LawsJ T → ∀ i, OMPins T R κ v₀ O i → T.pb = R.C.P.pb ∧ VStd D i ∧ LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (O i).lev := by
  first | exact @GlobalTheory.BasePins.orient_std_lev | exact GlobalTheory.BasePins.orient_std_lev | (intros; apply GlobalTheory.BasePins.orient_std_lev <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem good_iff_labE_and_lab_conj :
    ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (GoodEmb T.Q.c (res T σ) ↔ labE σ (lab σ ρ) = tauE D ρ) ∧ lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ :=
  fun _ T _ hl ha σ ρ => ⟨GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ, GlobalTheory.ConjReading.lab_conj σ ρ⟩

end GlobalTheory.HolRead
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.residual_character_det_values_mem_coeff_field : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (g : G), ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ChiDetValues.chiC_mem_coeff | exact GlobalTheory.ChiDetValues.chiC_mem_coeff | (intros; apply GlobalTheory.ChiDetValues.chiC_mem_coeff <;> assumption)
end
