module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.AdjSpanLift

open GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

theorem range_adjoint_le_span [FiniteDimensional ℂ H] [FiniteDimensional ℂ E]
    (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
  obtain ⟨U, hU⟩ := exists_cx hli hsp e
  have h1 : Θ ∘ₗ U = Θ := ext_of_span hsp fun v => by simp only [LinearMap.comp_apply, hU, hΘ]
  have h2 : ∀ w y, inner ℂ (U y) (j w) = inner ℂ y (U (j w)) := fun w y => by
    have : innerₛₗ ℂ (j w) ∘ₗ U = innerₛₗ ℂ (U (j w)) := ext_of_span hsp fun v => by
      simp only [LinearMap.comp_apply, innerₛₗ_apply_apply, hU, he]
    have h := LinearMap.congr_fun this y
    simp only [LinearMap.comp_apply, innerₛₗ_apply_apply] at h
    rw [← inner_conj_symm, h, inner_conj_symm]
  have h3 : ∀ y, U y ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := fun y => by
    have hy : y ∈ Submodule.span ℂ (Set.range j) := hsp ▸ Submodule.mem_top
    refine (Submodule.span_le (p := (Submodule.span ℂ (j '' (LinearMap.range e : Set V))).comap U)).2 ?_ hy
    rintro _ ⟨v, rfl⟩
    show U (j v) ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V))
    rw [hU]
    exact Submodule.subset_span ⟨e v, ⟨v, rfl⟩, rfl⟩
  rintro _ ⟨u, rfl⟩
  have h4 : innerₛₗ ℂ (U (LinearMap.adjoint Θ u)) = innerₛₗ ℂ (LinearMap.adjoint Θ u) := ext_of_span hsp fun w => by
    simp only [innerₛₗ_apply_apply]
    rw [h2, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hU, hΘ]
  rw [← (ext_inner_right ℂ fun w => LinearMap.congr_fun h4 w : U (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ u)]
  exact h3 _

end Linear

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

theorem model_good_span {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ
      (j '' (LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) : Set S.Forms)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine range_adjoint_le_span h1 h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

end Pres

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem proj_lifts_core {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hC : Core R F) (hOk : A.fam.Ok s) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g (R.thG i t y) = R.thG i t y := by
  have h1 : R.thF i t y ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    (hC.models.HW i (sg0 D A)).2.1.ge (hC.thP.thF_mem i t y)
  obtain ⟨z, hz⟩ := h1
  have hs : ∀ a, sg0 D A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have h2 : R.thG i t y = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g z := by
    refine (hC.models.HW i _).1 ?_

    rw [hC.thP.thG, ← hz, map_sum]
    refine (postOn_gaL (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG _ _).trans ?_
    exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gW, RealDat.eC, hs]; rfl
  rw [h2]
  exact idem_idem _ hOk.irr _ z

theorem range_adjoint_lift_le (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hOk : A.fam.Ok s) (hC : Core R F)
    (hG : ∀ i t g (v : (A.MtCSD i t).Forms),
      R.thG i t (R.jV i t (A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t v))) (i : Fin D.R.m) (t : T) :
    LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤
      Submodule.span ℂ (R.jV i t '' ((A.fam.L i t).goodF A.X : Set (A.fam.L i t).S.Forms)) :=
  model_good_span (W := (R.cV i).W) (ι := Bridge.ratF (Vc D i)) (ρ := (R.cV i).coef.ρ)
    (J := (levEnv _ (R.βV i) (R.datVt i t)).J) (χ := (levEnv _ (R.βV i) (R.datVt i t)).χ) (R.B.L i t).pres (R.HV i t)
    (hC.models.HV i t) (hC.models.jV i t) (hOk.lifts i t).act hOk.irr
    (R.gW i (sg0 D A)) (hG i t) fun y => proj_lifts_core hC hOk i t y

end GlobalTheory.AdjSpanLift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjGood

open GlobalTheory.AdjBlock

theorem range_adjoint_le_span {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}
    [FiniteDimensional ℂ H] [FiniteDimensional ℂ E] (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
  obtain ⟨U, hU⟩ := exists_cx hli hsp e
  have h1 : Θ ∘ₗ U = Θ := ext_of_span hsp fun v => by rw [LinearMap.comp_apply, hU, hΘ]
  have h2 : ∀ v y, inner ℂ (j (e v)) y = inner ℂ (j v) (U y) := fun v y => by
    have : innerₛₗ ℂ (j (e v)) = innerₛₗ ℂ (j v) ∘ₗ U := ext_of_span hsp fun w => by
      simp only [LinearMap.comp_apply, innerₛₗ_apply_apply, hU, he]
    exact LinearMap.congr_fun this y
  have h3 : LinearMap.adjoint U = U := ext_of_span hsp fun v => by
    refine ext_inner_right ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_left, hU, h2]
  have h4 : LinearMap.range U ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
    rw [LinearMap.range_eq_map, ← hsp, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [hU]
    exact Submodule.subset_span ⟨e v, ⟨v, rfl⟩, rfl⟩
  refine le_trans ?_ h4
  rw [← h1, LinearMap.adjoint_comp, h3]
  exact LinearMap.range_comp_le_range _ _

theorem model_good_span {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
    {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
    (hj : ∀ x, M.e (j x) = P.extL x)
    {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    LinearMap.range (LinearMap.adjoint Θ) ≤
      Submodule.span ℂ (j '' (LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) : Set S.Forms)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine range_adjoint_le_span h1 h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

theorem proj_rows_core {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hC : Core R F) (y : R.HE.H) : ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  refine hC.models.HE.1 ?_
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  refine Eq.trans ?_ ((postOn_gaL (R.MY 0) (R.βY 0) (R.dat0 R.triv) R.eG _ _).symm.trans (sub_eq_zero.1 h2))

  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gE]; rfl

theorem range_adjoint_Th_le_span_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ t g (v : (A.MtildeCSD t).Forms), R.Th t (R.jX t (A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) → ∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A.fam.R t).goodF A.X : Set (A.fam.R t).S.Forms)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hG t
  exact model_good_span (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ) (J := (levEnv _ R.βX (R.datXt t)).J)
    (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t) (hC.models.jX t) (hOk.what₂ t).act hOk.irr
    R.gE (hG t) fun y => proj_rows_core hC _

end GlobalTheory.AdjGood

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WatType

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_lift (R : RealDat D A Ks) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (hinj : Function.Injective (R.HW i σ).e) {x : (R.HW i σ).H} (hx : x ≠ 0) (g : G) :
    ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : R.gW i σ g x = 0 := by
    apply hinj
    rw [hg i σ g x, map_zero]
    ext v h
    show actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dite_eq_right hk]
    rfl
  have : R.gW i σ g⁻¹ (R.gW i σ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h0, map_zero]

theorem mem_wat_iff (R : RealDat D A Ks) (F : Face D A) (hg : R.models_gW) (hW : R.models_HW) (b : Bool) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e x ∈ R.Wat i σ (R.levL F b σ) ↔
      (∀ p : (F.lvl b).P, postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG p)) ((R.HW i σ).e x) =
        σ ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • (R.HW i σ).e x) ∧
      ∑ g, σ ((idemOf A.X).coeff g) • postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x) =
        (R.HW i σ).e x := by
  have hx : (R.HW i σ).e x ∈ R.Wall i σ := (hW i σ).2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.Wall at hx
  unfold RealDat.Wat
  rw [mem_goodPart]
  rw [GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  refine and_congr ?_ ?_
  · constructor
    · intro h1 g
      by_cases h0 : x = 0
      · simp [h0]
      ext v h
      have hmem : R.eG g ∈ (R.levL F b σ).H := by
        show R.eG.symm (R.eG g) ∈ (F.lvl b).P
        rw [MulEquiv.symm_apply_apply]; exact g.2
      have h2 := GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) (P := R.levL F b σ)
        (F := (R.HW i σ).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift R hg i σ (hW i σ).1 h0 g)
      have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
        Subtype.ext (R.eG.symm_apply_apply g)
      refine (congrFun h2 h).trans ?_
      show σ (((F.lvl b).ψ⁻¹ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
      rw [h3]
      rfl
    · intro h
      refine ⟨hx.aut, hx.cusp, fun v => ?_, hx.equiv, hx.cont⟩
      have hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F b σ) ((R.HW i σ).e x v) := by
        refine ⟨fun κ hκ y => hx.lev v κ hκ y, fun p => ?_⟩
        have h1 := congrArg (fun z : MMap (R.MW i σ) => z v) (h ⟨R.eG.symm p.1, p.2⟩)
        have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
        simp only [h2] at h1
        exact h1
      exact fun κ hκ y => hP.hasType κ hκ y
  · have h3 : ∀ v, R.eWf i σ ((R.HW i σ).e x v) = (∑ g, σ ((idemOf A.X).coeff g) •
        postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x)) v := by
      intro v
      simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
        MultilinearMap.smul_apply, postOn_apply]
      rfl
    simp only [h3]
    exact ⟨fun h => MultilinearMap.ext h, fun h v => by rw [h]⟩

theorem wat_iff_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ (b : Bool) i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ↔ (eH R i x = x ∧ ∀ p : (F.lvl b).P, R.gW i (sg0 D A) p x = sg0 D A ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ hC b i x
  have hW := hC.models.HW
  have hg := hC.models.gW
  have hinj := (hW i (sg0 D A)).1
  rw [mem_wat_iff R F hg hW, and_comm]
  refine and_congr ?_ (forall_congr' fun p => ?_)
  · rw [← hinj.eq_iff]

    simp only [eH, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hg i _ _ x]
  · rw [← hinj.eq_iff, hg, map_smul]

end GlobalTheory.WatType

end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.UnitLemma

theorem aeval_restrict_coe_of_stable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) {N : Submodule R M} (h : ∀ x ∈ N, f x ∈ N) (q : R[X]) (x : N) :
    ((aeval (f.restrict h) q x : N) : M) = aeval f q x := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | monomial n a =>
    have hpow : ∀ (k : ℕ) (y : N), ((((f.restrict h) ^ k) y : N) : M) = (f ^ k) y := by
      intro k
      induction k with
      | zero => intro y; rfl
      | succ k ih =>
        intro y
        rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ', Module.End.mul_apply]
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hpow]

theorem isIntegral_of_lat_stable : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ z ∈ L, u * z ∈ L) → IsIntegral K.O u := by
  intro K B u L hL hu
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End K.O B.A := LinearMap.mulLeft K.O u
  have hf : ∀ x ∈ L, f x ∈ L := hu
  obtain ⟨p, hpm, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero K.O (f.restrict hf)
  refine ⟨p, hpm, ?_⟩
  have hlmul : aeval f p = LinearMap.mulLeft K.O (aeval u p) := by
    have : f = Algebra.lmul K.O B.A u := rfl
    rw [this, Polynomial.aeval_algHom_apply]
    rfl
  have key : ∀ x ∈ L, aeval u p * x = 0 := by
    intro x hx
    have h1 := aeval_restrict_coe_of_stable f hf p ⟨x, hx⟩
    rw [hp, hlmul] at h1
    simpa using h1.symm
  have hall : ∀ a : B.A, aeval u p * a = 0 := by
    intro a
    have ha : a ∈ Submodule.span K.E (L : Set B.A) := hL.2 ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact key x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have := hall 1
  rw [mul_one] at this
  exact this

end GlobalTheory.UnitLemma
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.IsomMulTorus

open GlobalTheory.UnitLemma

theorem trace_inv {K : UQ} (B : InvAlg K) (w : B.A) :
    Algebra.trace K.E B.A (B.σ w) = K.c (Algebra.trace K.E B.A w) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) w
  rw [h, RingEquiv.apply_symm_apply]

theorem isom_eq_mul : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (u β : B.A), B.σ β = β * ((-1) ^ n * u) → Algebra.adjoin K.E {u} = ⊤ → (∀ y, (∀ z, B.herm β y z = 0) → y = 0) → ∀ f : B.A →ₗ[K.E] B.A, Function.Surjective f → (∀ y z, B.herm β (f y) (f z) = B.herm β y z) → ∃ a : B.Aˣ, a ∈ B.T ∧ ∀ y, f y = (a : B.A) * y := by
  intro K B n u β hβ hadj hnd f hf hiso

  have hsub : ∀ a b z : B.A, B.herm β (a - b) z = B.herm β a z - B.herm β b z := by
    intro a b z; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]

  have hsym : ∀ y z : B.A, K.c (B.herm β z y) = B.herm β (((-1) ^ n * u) * y) z := by
    intro y z
    unfold InvAlg.herm
    rw [← trace_inv, map_mul B.σ, map_mul B.σ, B.σ_σ, hβ]
    congr 1; ring

  have ht : ∀ y, f (((-1) ^ n * u) * y) = ((-1) ^ n * u) * f y := by
    intro y
    have h0 : ∀ z, B.herm β (((-1) ^ n * u) * f y - f (((-1) ^ n * u) * y)) z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := hf z
      rw [hsub, ← hsym, hiso, hiso, hsym, sub_self]
    exact (sub_eq_zero.mp (hnd _ h0)).symm

  have hsgn : ((-1 : B.A) ^ n) = algebraMap K.E B.A ((-1) ^ n) := by simp
  have hsq : ((-1 : B.A) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have hu : ∀ y, f (u * y) = u * f y := by
    intro y
    have e1 : u * y = (-1) ^ n * (((-1) ^ n * u) * y) := by
      rw [← mul_assoc, ← mul_assoc, hsq, one_mul]
    have e2 : u * f y = (-1) ^ n * (((-1) ^ n * u) * f y) := by
      rw [← mul_assoc, ← mul_assoc, hsq, one_mul]
    have hm : ∀ x, f ((-1) ^ n * x) = (-1) ^ n * f x := by
      intro x; rw [hsgn, ← Algebra.smul_def, map_smul, Algebra.smul_def]
    rw [e1, e2, hm, ht]

  let S : Subalgebra K.E B.A :=
    { carrier := {x | ∀ y, f (x * y) = x * f y}
      mul_mem' := by
        intro a b ha hb y
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_assoc, ha, hb, mul_assoc]
      add_mem' := by
        intro a b ha hb y
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [add_mul, map_add (f := _), ha, hb, add_mul]
      algebraMap_mem' := by
        intro e y
        show f (algebraMap K.E B.A e * y) = algebraMap K.E B.A e * f y
        rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul] }
  have hS : ∀ x, ∀ y, f (x * y) = x * f y := by
    intro x
    have h1 : Algebra.adjoin K.E {u} ≤ S := Algebra.adjoin_le (by
      intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hu)
    rw [hadj] at h1
    exact h1 (Algebra.mem_top : x ∈ (⊤ : Subalgebra K.E B.A))
  have hf1 : ∀ y, f y = y * f 1 := by
    intro y; rw [← hS y 1, mul_one]
  obtain ⟨z, hz⟩ := hf 1
  have hz1 : f 1 * z = 1 := by rw [mul_comm, ← hf1, hz]
  let a : B.Aˣ := ⟨f 1, z, hz1, by rw [mul_comm]; exact hz1⟩
  refine ⟨a, ?_, fun y => by rw [hf1 y, mul_comm]⟩
  show (f 1) * B.σ (f 1) = 1
  have h0 : ∀ w, B.herm β (f 1 * B.σ (f 1) - 1) w = 0 := by
    intro w
    have e : B.herm β (f 1 * B.σ (f 1)) w = B.herm β (f 1) (f w) := by
      rw [hf1 w]; unfold InvAlg.herm; rw [map_mul B.σ]; congr 1; ring
    rw [hsub, e, hiso, sub_self]
  exact sub_eq_zero.mp (hnd _ h0)

end GlobalTheory.IsomMulTorus
end
end
