module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRingOfIntegersLift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false

noncomputable section

open Classical

namespace GlobalTheory.EvalLowType

theorem zero_of_span {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ j, AddCommGroup (L j)] [∀ j, Module ℂ (L j)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (F : (∀ j, L j) →ₘₗ[ℂ] X) (v₀ : ∀ j, L j) (P : ∀ j, L j → Prop)
    (hspan : ∀ j, Submodule.span ℂ {u | P j u} = ⊤)
    (hstep : ∀ (v : ∀ j, L j) (j : ι) (u : L j), v j = v₀ j → P j u → F v = 0 → F (Function.update v j u) = 0)
    (h0 : F v₀ = 0) : ∀ v, F v = 0 := by
  have key : ∀ s : Finset ι, ∀ v : ∀ j, L j, (∀ j ∉ s, v j = v₀ j) → F v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have : v = v₀ := funext fun j => hv j (Finset.notMem_empty j)
      rw [this]; exact h0
    | insert a s ha ih =>
      intro v hv
      have h1 : F (Function.update v a (v₀ a)) = 0 := ih _ fun j hj => by
        by_cases hja : j = a
        · subst hja; simp
        · rw [Function.update_of_ne hja]; exact hv j (by simp [hja, hj])
      have hmem : v a ∈ Submodule.span ℂ {u | P a u} := by rw [hspan a]; trivial
      have hall : ∀ u ∈ Submodule.span ℂ {u | P a u},
          F (Function.update (Function.update v a (v₀ a)) a u) = 0 := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu => exact hstep _ a u (by simp) hu h1
        | zero => exact F.map_update_zero _ _
        | add x y _ _ hx hy => rw [F.map_update_add, hx, hy, add_zero]
        | smul c x _ hx => rw [F.map_update_smul, hx, smul_zero]
      have e : Function.update (Function.update v a (v₀ a)) a (v a) = v := by simp
      rw [← e]; exact hall _ hmem
  exact fun v => key Finset.univ v (fun j hj => absurd (Finset.mem_univ j) hj)

theorem adForm_lowT_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → adForm R i x (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (adForm R i x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hHW i x τ k hk v u hu
  have hmem : adForm R i x ∈ R.Wall i (sg0 D A) := by
    rw [← (hHW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ _
  have hfr : IsUnit ((R.MW i (sg0 D A)).fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ)
  have e1 : (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hfr
  have e2 : ((R.MW i (sg0 D A)).fr τ)⁻¹ * (R.MW i (sg0 D A)).fr τ = 1 := Matrix.nonsing_inv_mul _ hfr
  have hkJ : kᴴ * Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) * k = Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) := by
    have hu1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hg : ((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ) := by
    show _ = _
    rw [← (R.MW i (sg0 D A)).fr_gram τ]
    have e3 : (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ * ((R.MW i (sg0 D A)).fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ, e3, Matrix.one_mul,
      ← Matrix.mul_assoc ((R.MW i (sg0 D A)).fr τ) (((R.MW i (sg0 D A)).fr τ)⁻¹), e1, Matrix.one_mul]
    rw [← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc (kᴴ * _), hkJ]
  have hrep : (R.MW i (sg0 D A)).rep τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ) =
      (R.MW i (sg0 D A)).σ τ k := by
    unfold Formalism.IndefR.Mult.DSModel.rep
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one]
  have hupd : (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ) := by
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  rw [hupd]
  suffices H : ∀ T ∈ R.Wall i (sg0 D A), T (Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ)) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (T (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) from H _ hmem
  intro T0 hT0
  induction hT0 using Submodule.span_induction with
  | mem T hT =>
    exact hT.equiv τ _ hg _ _ (by rw [hrep]; exact hu)
  | zero => rfl
  | add S T _ _ hS hT =>
    simp only [MultilinearMap.add_apply, hS, hT]
    rfl
  | smul a T _ hT =>
    simp only [MultilinearMap.smul_apply, hT]
    rfl

end GlobalTheory.EvalLowType

theorem GlobalTheory.EvalLowType.lowType_of_eval : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ u : U, (∀ w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w₀ ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w₀ ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w₀)) → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hcore i _ _ _ _ _ _ v _ _ _ _ _ _ _ _ ℓ _ _ U χ ξR ω φ hker Λ h _ _ N x₀ P x f y _ _ _ _ _ _ _ _ y₀ c _ φ' hvec u hu
  have hext : IsExtVec (R.MW i (sg0 D A)) (v₀ i (sg0 D A)) := (fw.hv₀ i (sg0 D A)).1
  have hs0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK (sg0 D A) :=
    fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) hs0
  let w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ := fun ρ => ⟨v₀ i (sg0 D A) ρ, (hext ρ).2.1⟩
  let Lin : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun t g => Datum.thetaKO ω h g (Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
        (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ' (R.ioP i t ((O i).c0' y)))
      map_add' := fun a b => by funext g; simp [Datum.thetaKO, map_add (f := _)]
      map_smul' := fun a b => by funext g; simp [Datum.thetaKO, map_smul] }
  let act := Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹))
  let Rt : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (D.what₂.embLL c • (act ∘ₗ Lin)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  let Lf : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (adForm R i (cuspTo hT.p fw i (f u))).compLinearMap fun ρ => (lowT (R.MW i (sg0 D A)) ρ).subtype
  have hRt : ∀ w, Rt w = D.what₂.embLL c • act (singleSeries R i ω φ' h ((O i).c0' y) w) := fun w => rfl
  have hLf : ∀ w, Lf w = adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => (w ρ : (R.MW i (sg0 D A)).sm ρ)) := fun w => rfl
  have hrs : ∀ (g : GA D (Wc D i)) (a b : GA D (Wc D i) → ℂ) (s : ℂ),
      Formalism.L2.Theta.rTr (Wc D i) g a - s • Formalism.L2.Theta.rTr (Wc D i) g b = Formalism.L2.Theta.rTr (Wc D i) g (a - s • b) :=
    fun _ _ _ _ => rfl
  have key := GlobalTheory.EvalLowType.zero_of_span (Lf - Rt) w₀
    (fun ρ z => ∃ k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ),
      ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((v₀ i (sg0 D A) ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ))
    (fun ρ => GlobalTheory.LowSpan.span_translates_eq_top _ _ hext ρ
      ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)).2 ρ))
    (fun w ρ z hw ⟨k, hk, hu'⟩ h0 => by
      have hu2 : ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((w ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) := by
        rw [hu', hw]
      have e1 := GlobalTheory.EvalLowType.adForm_lowT_equiv R hcore.models.HW i (cuspTo hT.p fw i (f u)) ρ k hk w z hu2
      have e2 := GlobalTheory.T.singleThetaSeries_K_equivariant_lowest_type R F hcore i _ χ ξR _ ω φ hker _ _ φ' hvec h ((O i).c0' y) ((u : G)⁻¹) ρ k hk w z hu2
      rw [MultilinearMap.sub_apply, hLf, hRt, e1, e2]
      change Formalism.L2.Theta.rTr (Wc D i) _ (Lf w) - D.what₂.embLL c • Formalism.L2.Theta.rTr (Wc D i) _ (act _) = 0
      rw [hrs, ← hRt, ← MultilinearMap.sub_apply, h0]
      rfl)
    (by
      rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt]
      exact hu w₀ fun ρ => rfl)
  intro w
  have := key w
  rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt] at this
  exact this
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

variable {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))

abbrev intR : Type := integralClosure ℤ_[l] Lf

def intEmb : intR Lf →+* PadicAlgCl l := Lf.val.toRingHom.comp (algebraMap (integralClosure ℤ_[l] Lf) Lf)

end Ring

section Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

def EvOk (i : E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) : Prop :=
  (∀ x, ev (1 ⊗ₜ[F] x) = i x) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ‖ev (a ⊗ₜ[F] 1)‖ ≤ 1) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[F] 1) = 0) ∧
    ∀ y, ev y ∈ IntermediateField.adjoin ℚ_[l] (Set.range i)

end Adeles

def incOf (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) :
    D.host.E →+* PadicAlgCl l :=
  cond b (cj (e0.comp (labLL D τ))) (e0.comp (labLL D τ))

def HalfAt (D : D7) (l : ℕ) : Prop := ∀ [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool), IsHalf (incOf D e0 b)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def Ix (j : Fin D.R.m) (t : p.P.T) (l N : ℕ) : Type :=
  {i : (blk p j t).Pl × ℕ // 1 ≤ i.2 ∧ i.2 ≤ N ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal}

def frameOf (j : Fin D.R.m) (t : p.P.T) (l : ℕ) [Fact l.Prime] (N : ℕ) (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] Lf] (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ) :
    Frame l D.what₂.Tau N where
  O := intR Lf
  emb := intEmb Lf
  G := Bridge.Gf (Vc D j)
  Γ := (Bridge.ratF (Vc D j)).range
  K := levJ p j t
  kap := kap
  chi := chi
  I := Ix p j t l N
  tr i := hkA p j t i.1
  cst _ := 1

def kapMat (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (κ : levJ p j t) (τ : D.what₂.Tau) :
    Matrix (Fin N) (Fin N) (PadicAlgCl l) :=
  ((bs τ)⁻¹).val * ((matOf j (κ : Bridge.Gf (Vc D j))).map (ev τ)).submatrix rk rk * (bs τ).val

def KapEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) : Prop :=
  ∀ κ τ, (Matrix.GeneralLinearGroup.map (intEmb Lf) (kap κ τ)).val = kapMat p j t ev bs rk κ τ

def ChiEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (io : PadicAlgCl l ≃+* ℂ) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)} (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf)))
    (chi : levJ p j t →* (intR Lf)ˣ) : Prop :=
  ∀ κ, io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1

def KapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (rk : Fin P.Nr ≃o Fin (Vc D j).rank), (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) →
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) →
    ∃ bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, bs τ = 1) ∧ ∀ κ τ a c,
      kapMat p j (p.R.mu w) ev bs rk κ τ a c ∈ IntermediateField.adjoin ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (Set.range e0) ∧
        ‖kapMat p j (p.R.mu w) ev bs rk κ τ a c‖ ≤ 1

def ChiAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ κ : levJ p j (p.R.mu w), ((levChi p j (p.R.mu w) κ : ℂˣ) : ℂ) ^ M = 1

def ClassesAt (j : Fin D.R.m) (t : p.P.T) : Prop :=
  ∃ S : Finset (Bridge.Gf (Vc D j)), ∀ g, ∃ γ ∈ (Bridge.ratF (Vc D j)).range, ∃ s ∈ S, ∃ κ ∈ levJ p j t, g = γ * s * κ

def TameAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ g : Bridge.Gf (Vc D j),
    Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} ∧
      ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ Nat.card {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)}

def ChoiceOk (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))}
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ) : Prop :=
  (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) ∧ (∀ x, e0 x ∈ Lf) ∧ (∀ x, io (e0 x) = D.what₂.embLL x) ∧
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) ∧ KapEq p j (p.R.mu w) ev bs rk kap ∧ ChiEq p j (p.R.mu w) io sh kap chi


open Classical in
def PermAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i (κ : F.K), ∃ σ : Equiv.Perm (F.tr i), ∀ s : F.tr i, ∃ κ' : F.K,
      (κ : F.G) * s = σ s * κ' ∧ F.kap κ' = F.kap κ ∧ F.chi κ' = F.chi κ


open Classical in
def CommAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i i', ∃ σ : F.tr i × F.tr i' ≃ F.tr i' × F.tr i, ∀ x, F.Triv ((((σ x).1 : F.G) * (σ x).2)⁻¹ * ((x.1 : F.G) * x.2))

def ReadsAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime], ∃ (b : Bool) (sh : D.what₂.Tau → ℤ),
    ∀ (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi → (∀ τ, bs τ = 1) →
    ∃ R : Reads (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi) W.lam (blk p j (p.R.mu w)) w,
      R.e0 = e0 ∧ R.ix = Subtype.val

end Point

end GlobalTheory.FrameOf

end
end

section



noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.DeepExist

theorem floorThreeLOverLogThree_mul_log_fifteen_le {L : ℝ} (hL : 0 ≤ L) : (expL L : ℝ) * Real.log 15 ≤ 9 * L := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have he : (expL L : ℝ) ≤ 3 * L / Real.log 3 := Nat.floor_le (by positivity)
  have he' : (expL L : ℝ) * Real.log 3 ≤ 3 * L := (le_div_iff₀ h3).1 he
  have h15 : Real.log 15 ≤ 3 * Real.log 3 := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 15) (by norm_num : (15 : ℝ) ≤ 3 ^ 3)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have he0 : (0 : ℝ) ≤ expL L := Nat.cast_nonneg _
  nlinarith

theorem size_le {D : D7} {L : SizeData₂ D} {PP A M o : ℝ} (hN : HostNum D L PP A M) (hF : o ≤ 217 * zBase L ^ 2) :
    o + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ expL L.sc.L) + Real.log D.host.d + 1) ≤
      391 * zBase L ^ 2 := by
  have hL10 := hN.big.2.1
  have hcop := hN.cop
  have h01 : D.host.g 0 * D.host.g 1 ≠ 0 := fun h => by
    rw [h, Nat.coprime_zero_right] at hcop
    norm_num at hcop
  have hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.1 h01).1
  have hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.1 h01).2
  have h15 : ((15 : ℝ) ^ expL L.sc.L) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hlog : Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ expL L.sc.L) =
      Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) + expL L.sc.L * Real.log 15 := by
    rw [Real.log_mul (mul_ne_zero hg0 hg1) h15, Real.log_mul hg0 hg1, Real.log_pow]
  have he := floorThreeLOverLogThree_mul_log_fifteen_le (L := L.sc.L) (by linarith)
  have a0 := hN.logg 0
  have a1 := hN.logg 1
  have ad := hN.logd
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hZ : 8 * L.sc.L ≤ zBase L := by
    unfold zBase
    have : (8 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    nlinarith
  rw [hlog]
  nlinarith

end GlobalTheory.CovTop.DeepExist

end
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RefSum.primeSum_add_pair {S : Finset ℕ} {e : ℕ → ℝ} {s : ℝ} (h : PrimeSum S e s) (g : Fin 2 → ℕ)
    (hg : ∀ k, (g k).Prime) :
    PrimeSum (S ∪ Finset.univ.image g) (fun q => e q + if q ∈ Finset.univ.image g then 1 else 0)
      (s + (Real.log (g 0) + Real.log (g 1))) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq => ?_, fun q => add_nonneg (h2 q) (by split_ifs <;> norm_num), fun q hq => ?_, ?_⟩
  · rcases Finset.mem_union.1 hq with hq | hq
    · exact h1 q hq
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq
      exact hg k
  · rw [Finset.mem_union, not_or] at hq
    simp only [h3 q hq.1, if_neg hq.2, add_zero]
  · have a : ∑ q ∈ S ∪ Finset.univ.image g, e q * Real.log q = ∑ q ∈ S, e q * Real.log q :=
      (Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [h3 q hq, zero_mul]).symm
    have b : ∑ q ∈ S ∪ Finset.univ.image g, (if q ∈ Finset.univ.image g then (1 : ℝ) else 0) * Real.log q =
        ∑ q ∈ Finset.univ.image g, Real.log q := by
      rw [← Finset.sum_subset Finset.subset_union_right fun q _ hq => by rw [if_neg hq, zero_mul]]
      exact Finset.sum_congr rfl fun q hq => by rw [if_pos hq, one_mul]
    have c : ∑ q ∈ Finset.univ.image g, Real.log (q : ℕ) ≤ ∑ k : Fin 2, Real.log (g k) :=
      Finset.sum_image_le_of_nonneg (f := fun q : ℕ => Real.log q) fun q _ => Real.log_natCast_nonneg q
    rw [Fin.sum_univ_two] at c
    simp only [add_mul, Finset.sum_add_distrib]
    linarith
end

section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.DefCore

theorem unitE_nonneg {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) : 0 ≤ unitE p := by
  rw [hw.unit]
  have hx : 0 < L.sc.x := by linarith [hh.big.2.1, hh.big.2.2.1]
  have hb : 0 < L.sc.b := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hx _) _) hh.room
  have := hh.big.2.2.2
  have : (0:ℝ) ≤ L.sc.L := by linarith [hh.big.2.1]
  positivity

end GlobalTheory.CovTop.DefCore

end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.Over.through_image : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ y : Y, E'.Through y → E.Through (s y) := by
  intro k _ X Y _ _ p s _ E' E hO y hy f hf
  obtain ⟨a, rfl⟩ := hf
  refine (hO _).2 (hy _ ⟨s.stalkMap y a, ?_⟩)
  exact (GlobalTheory.functionFieldMap_algebraMap s y a).symm

end GlobalTheory.Discrepancy
end
