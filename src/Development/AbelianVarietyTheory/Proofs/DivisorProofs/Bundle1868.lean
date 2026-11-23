module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvalInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle190
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Formalism.PieriBlockIdeals.Bundle003
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.MirabolicMackeyTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingConjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)



theorem exists_lift_act {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G}
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k)
    (hchi : ∀ k, Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1) :
    ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k ∧
      ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k) := by
  refine ⟨hk.choose, hk.choose_spec, fun x v h => ?_⟩
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (x v) h = _
  unfold Lev.actG0
  rw [dite_eq_left hk]
  simp only [hchi, inv_one, one_mul]



theorem exists_act_eq (hθ : IsInfFam R.θ) (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (y : (R.HW i σ).H) :
    ∃ z, (R.HW i σ).e z = actW R i σ g ((R.HW i σ).e y) := by
  have h1 : (R.HW i σ).e y ∈ R.Wall i σ := (he i σ).2.1 ▸ LinearMap.mem_range_self _ y
  have h2 : actW R i σ g ((R.HW i σ).e y) ∈ R.Wall i σ :=
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) (R.eG g) _ h1 _ fun _ => rfl
  rw [← (he i σ).2.1] at h2
  exact h2



theorem equiv_of_values (hθ : IsInfFam R.θ) (he : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec}
    (hv : IsUnitV v) {g : G} {k : GA D (Wc D i)} (hk : ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k))
    {x y : (R.HW i σ).H} {c : ℂ} (h : ∀ h, evAt R i σ v x h = c * evAt R i σ v y (h * k)) :
    (R.HW i σ).e x = c • actW R i σ g ((R.HW i σ).e y) := by
  obtain ⟨z, hz⟩ := exists_act_eq R hθ he i σ g y
  have h4 : (R.HW i σ).e (c • z) = c • actW R i σ g ((R.HW i σ).e y) := by
    rw [← hz]; exact (R.HW i σ).e.map_smul _ _
  have h3 : x = c • z := by
    refine GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i σ) (R.HW i σ).H (R.HW i σ).e _ _ _ (he i σ).2.2 v hv (funext fun h' => ?_)
    show (R.HW i σ).e x v h' = (R.HW i σ).e (c • z) v h'
    rw [h4]
    exact (h h').trans (congrArg (c * ·) (hk _ v h').symm)
  exact (congrArg (R.HW i σ).e h3).trans h4

theorem chiTop_eq {i : Fin D.R.m} (h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ)) : ChiIs R i (chiTop R i) := by
  choose a ha using h1
  have hne : ∀ g, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dite_eq_left hex]
  exact hex.choose_spec

end Model



theorem reading_equiv_of_not_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, ¬ GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ he ht i hl hq ρC hρ σ hσ g f
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := ht.laws.spaceW _ (inR i) _ (good_resC T hσ)
  by_cases hj : JEvBarAt T R κ i σ hV
  swap
  · rw [top_lift_vanishes_off_good_embeddings T R κ v₀ hσ hV hj]
    simp
  obtain ⟨v, hv, h5⟩ := jTop_bar T R κ v₀ hσ hV hj
  have hE := hq _ (good_resC T hσ) hV
  have hchi : ChiIs R i (chiTop R i) := chiTop_eq R fun g' => by
    obtain ⟨k, hk⟩ := hl g'
    obtain ⟨-, y, hy, -⟩ := hE g' k hk 0 (zero_mem _)
    exact ⟨_, by rw [chiC, Units.coe_prod]; exact hy⟩
  obtain ⟨k, hk1, hk2⟩ := exists_lift_act R σ (hl g) (GlobalTheory.TiedUnif.levChi_flag_datWp i)
  obtain ⟨-, y, hy, h2⟩ := hE g k hk1 f f.2
  have hy' : ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL y :=
    D.what₂.embLL.injective ((hchi g).trans (by rw [chiC, Units.coe_prod]; exact hy.symm))
  refine equiv_of_values R hθ he hv hk2 fun h => ?_
  rw [h5, h5]
  show starRingEnd ℂ _ = _ * starRingEnd ℂ _
  rw [hρ, GlobalTheory.TiedUnif.phiC_eq_phiAt, GlobalTheory.TiedUnif.phiC_eq_phiAt, h2, mul_left_comm, hy', map_mul]
  exact congrArg (· * _) (Complex.conj_conj _)

end GlobalTheory.ReadingConjEquiv

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.ReadingEquivGood

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem extendByOne_eq_one_of_trivial {M L : Type} [Group M] [Monoid L] (H : Subgroup M) (χ : H → L) (h : ∀ x, χ x = 1) (x : M) :
    Formalism.L2.DIV.ext1 H χ x = 1 := by
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · exact h _
  · rfl

section
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levChi_flag (i : Fin D.R.m) (k : GA D (Wc D i)) :
    Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1 := by
  have h2 : Formalism.L2.DIV.ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (Formalism.L2.DIV.rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) k)) = 1 := extendByOne_eq_one_of_trivial _ _ (fun _ => rfl) _
  unfold Lev.levChi Formalism.L2.DIV.levFn
  rw [h2]
  show ((1 * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ ∅, _ : ℂˣ) : ℂ) = 1
  simp

theorem actW_apply {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {g : G}
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (x : MMap (R.MW i σ)) (v : (R.MW i σ).Vec)
    (h : GA D (Wc D i)) : actW R i σ g x v h = x v (h * hk.choose) := by
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (x v) h = _
  unfold Lev.actG0
  rw [dite_eq_left hk]
  simp only [levChi_flag, inv_one, one_mul]

theorem actW_mem (hθ : IsInfFam R.θ) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (g : G) {x : MMap (R.MW i σ)}
    (hx : x ∈ R.Wall i σ) : actW R i σ g x ∈ R.Wall i σ :=
  GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) (R.eG g) x hx _ fun _ => rfl

theorem equiv_of_values (hθ : IsInfFam R.θ) (he : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec}
    (hv : IsUnitV v) {g : G} {x y : (R.HW i σ).H} {c : ℂ}
    (h : ∀ h, evAt R i σ v x h = c * actW R i σ g ((R.HW i σ).e y) v h) :
    (R.HW i σ).e x = c • actW R i σ g ((R.HW i σ).e y) := by
  have hr : LinearMap.range (R.HW i σ).e = R.Wall i σ := (he i σ).2.1
  have h1 : c • actW R i σ g ((R.HW i σ).e y) ∈ LinearMap.range (R.HW i σ).e := by
    rw [hr]
    exact Submodule.smul_mem _ _ (actW_mem R hθ g (hr ▸ LinearMap.mem_range_self _ y))
  obtain ⟨z, hz⟩ := h1
  have h2 : x = z := by
    refine GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i σ) (R.HW i σ).H (R.HW i σ).e _ _ _ (he i σ).2.2 v hv
      (funext fun h' => ?_)
    show (R.HW i σ).e x v h' = (R.HW i σ).e z v h'
    rw [hz]
    exact h h'
  rw [h2, hz]

theorem chiIs_of_values {i : Fin D.R.m} (h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ)) : ChiIs R i (chiTop R i) := by
  choose a ha using h1
  have hne : ∀ g : G, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dite_eq_left hex]
  exact hex.choose_spec

theorem coe_chiC (i : Fin D.R.m) (g : G) : (chiC R i g : ℂ) =
    ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) := by
  simp only [chiC, Units.coe_prod]

end

theorem phiC_eq (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiC T hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * phiAt T i σ hV (T.cE ((i : ℕ) + 1) σ) f h := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (g : GA D W), phiC T hV a f g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) f)) g := by
    intro W hV g
    subst hV
    rfl
  exact key _ hV h

theorem reading_equivariant : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ he ht i hl hq ρC hρ σ hσ g f
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := ht.laws.spaceW _ (inR i) _ hσ
  by_cases hj : JEvAt T R κ v₀ i σ hV
  · have hq' : EqAt T R κ (O i) (res T σ) hV (T.cE ((i : ℕ) + 1) (res T σ)) := hq (res T σ) hσ hV
    have hc : ChiIs R i (chiTop R i) := chiIs_of_values R fun g' => by
      obtain ⟨-, y, hy, -⟩ := hq' g' _ (hl g').choose_spec 0 (zero_mem _)
      exact ⟨_, hy.trans (coe_chiC R i g').symm⟩
    obtain ⟨-, y, hy, h2⟩ := hq' g _ (hl g).choose_spec (f : T.R ((i : ℕ) + 1)) f.2
    have hy' : ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL y :=
      D.what₂.embLL.injective ((hc g).trans ((coe_chiC R i g).trans hy.symm))
    have hs : σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = res T σ y := congrArg σ hy'
    refine equiv_of_values R hθ he (v := v₀ i σ) ((ht.hv₀ i σ).norm R) fun h => ?_
    have e1 := congrFun (jTop_good T R κ v₀ hσ hV hj (ρC g f)) h
    have e2 := congrFun (jTop_good T R κ v₀ hσ hV hj f) (h * (hl g).choose)
    have e3 := actW_apply R (hl g) ((R.HW i σ).e (jTop T R κ v₀ i σ f)) (v₀ i σ) h
    have e4 : phiC T hV (wtA (κ i)) ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) h =
        res T σ y * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * (hl g).choose) := by
      rw [hρ, phiC_eq, phiC_eq, h2, mul_left_comm]
    exact e1.trans (e4.trans (congrArg₂ (· * ·) hs.symm (e2.symm.trans e3.symm)))
  · rw [jTop_good0 T R κ v₀ hσ hV hj]
    simp

end GlobalTheory.ReadingEquivGood

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSchur

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem mul_star_psi (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a * star (ψ a) = 1 := by
  have h : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [Complex.star_def, Complex.mul_conj', h]
  simp

theorem heisO_rat {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : WO S T} (hγ : γ ∈ ratL T S) (x : WO S T) :
    heisO ψ S T γ f x = ψ (symplO S T x γ) * f x := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hf.quasi γ x
  rw [← GlobalTheory.WeilVacMove.symplOH_skew] at h
  show ψ (symplOH S T x (ratW T S γ)) * f (x + ratW T S γ) = ψ (symplO S T x (ratW T S γ)) * f x
  rw [add_comm x, h, ← mul_assoc, ← AddChar.map_add_eq_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1]

theorem prod_periodic (hψ : IsStdChar D ψ (-1)) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hf' : IsThetaFunO ψ S T f') {γ : WO S T} (hγ : γ ∈ ratL T S) (x : WO S T) :
    f (γ + x) * star (f' (γ + x)) = f x * star (f' x) := by
  obtain ⟨γ, rfl⟩ := hγ
  show f (ratW T S γ + x) * star (f' (ratW T S γ + x)) = _
  rw [hf.quasi, hf'.quasi, star_mul']
  linear_combination (f x * star (f' x)) * mul_star_psi hψ (-(symplOH S T (ratW T S γ) x))

theorem prod_eq (hψ : IsStdChar D ψ (-1)) (M : Module.End ℂ (WO S T → ℂ))
    (hM : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f))
    (hc : ∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f))
    (hn : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (x : WO S T) :
    M f x * star (M f' x) = f x * star (f' x) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hint : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Integrable (fun x => g x * star (g' x)) (μ.restrict 𝓕) := fun g g' hg hg' => by
    have hcont : Continuous fun x => g x * star (g' x) := hg.cont.mul hg'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← prod_periodic hψ hg hg' hγ w]
    exact hC _ h
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M f' x) - f x * star (f' x))
    (((hM f hf).cont.mul (hM f' hf').cont.star).sub (hf.cont.mul hf'.cont.star))
    (fun γ hγ x => by rw [prod_periodic hψ hf hf' hγ, prod_periodic hψ (hM f hf) (hM f' hf') hγ])
    (fun γ => by
      have e : (fun x => ψ (symplO S T x γ) * (M f x * star (M f' x) - f x * star (f' x))) = fun x =>
          M (heisO ψ S T γ f) x * star (M f' x) - heisO ψ S T γ f x * star (f' x) := by
        funext x
        rw [hc _ f hf, heisO_rat hf γ.2, heisO_rat (hM f hf) γ.2]
        ring
      rw [e, integral_sub (hint _ _ (hM _ (hth _ f hf)) (hM f' hf')) (hint _ _ (hth _ f hf) hf'),
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 M hM (hn μ 𝓕 hμ h𝓕) _ _ (hth _ f hf) hf', sub_self])
  exact sub_eq_zero.1 (congrFun key x)

theorem schur : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  intro D ψ hψ S T M hM hc hn
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have h2 : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisO, add_sub_cancel, star_mul'] at h
    linear_combination ψ (symplOH S T x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ (symplOH S T x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunO ψ S T f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (M f₀ y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), ?_, fun f hf => ?_⟩
    · rw [norm_div, norm_star, norm_star, hn1, div_self (norm_ne_zero_iff.2 hy)]
    · funext x
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.ThetaSchur

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalDecomp

open GlobalTheory.SphericalOps GlobalTheory.HeckeAdjoint GlobalTheory.HeckeOrthSum

theorem mult_le_of_parts {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S} {J : Subgroup (GA D V)}
    {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hS : SchurMult θ M (J : Set (GA D V)) χ μ 𝓕) [FiniteDimensional ℂ (Mult θ M (J : Set (GA D V)) χ)]
    (hK : ∀ P d R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R →
      ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ)
    (Z : Submodule ℂ (MMap M))
    (hZ : ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (∀ P d, (¬ ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R) → c P d = 0) →
        partFull θ M (J : Set (GA D V)) χ Sb c ≤ Z) :
    Mult θ M (J : Set (GA D V)) χ ≤ Z := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D θ V S M _ χ μ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  have hpos : IsPosOn (Mult θ M (J : Set (GA D V)) χ) (ipM M μ 𝓕) :=
    ⟨fun x hx y hy z hz c => (h1 x hx y hy z hz c).1, fun x hx y hy => (h1 x hx y hy y hy 0).2, fun x hx => h2 x hx⟩
  refine hpos.le_iSup_eigen
    (I := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D V) //
      Hecke₂ V (J : Set (GA D V)) χ Sb x.1 x.2.1 x.2.2})
    (fun i => heckeOn M i.1.2.2) (fun i => hK _ _ _ i.2) (fun i k T hT => ?_) ?_ Z ?_
  · rw [GlobalTheory.MultMem.mem_mult_iff] at hT
    exact MultilinearMap.ext fun v => comm_heckeLin (realUnif D _) i.2 k.2 (hT.lev v)
  · rintro ⟨⟨P, d, R⟩, hR⟩
    obtain ⟨R', hR', -⟩ := exists_dual (realUnif D P) hR
    exact ⟨⟨(P, dualLab d, R'), hR'⟩, fun T hT T' hT' =>
      ipM_heckeOn_dualLab D V S θ M J χ Sb μ 𝓕 hθ hμ hF hS P d R R' hR hR' T hT T' hT' (hK _ _ _ hR T hT)
        (hK _ _ _ hR' T' hT')⟩
  · intro x T hT hx
    let c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ := fun P d =>
      if h : ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0
    refine hZ c (fun P d h => dif_neg h) ((mem_partFull ..).2 ⟨hT, fun P d R hR v => ?_⟩)
    have h : ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R := ⟨R, hR⟩
    rw [labelUnique (realUnif D) P d R h.choose hR h.choose_spec (T v) (((GlobalTheory.MultMem.mem_mult_iff ..).1 hT).lev v)]
    simp only [c, dif_pos h]
    exact congrArg (fun U : MMap M => U v) (hx ⟨(P, d, h.choose), h.choose_spec⟩)

end GlobalTheory.PrincipalDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.petersson_adjoint_heckeOperator_eq_dualLabel : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M (J : Set (GA D V)) χ μ 𝓕 → ∀ P d R R', Hecke₂ V (J : Set (GA D V)) χ Sb P d R → Hecke₂ V (J : Set (GA D V)) χ Sb P (dualLab d) R' → ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, ∀ T' ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ → heckeOn M R' T' ∈ Mult θ M (J : Set (GA D V)) χ → ipM M μ 𝓕 (heckeOn M R T) T' = ipM M μ 𝓕 T (heckeOn M R' T') := by
  first | exact @GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab | exact GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab | (intros; apply GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_principal_congruence_back_triangular_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → l.A = 1 → 1 ≤ r → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ η : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab (U.X k).Gm (U.X k).Λ η ∧ (∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (η : Matrix (Fin r) (Fin r) E) w - w = (l.M : E) • y) ∧ ∃ b ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor (U.X k).Ψ r, x = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact η (ReciprocityTheory.ChartRestriction.G.FD.lact γ x)) b := by
  first | exact @GlobalTheory.CongrOrbit.exists_congr_back | exact GlobalTheory.CongrOrbit.exists_congr_back | (intros; apply GlobalTheory.CongrOrbit.exists_congr_back <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV

theorem _root_.GlobalTheory.T.sum_exactExponents_smul_mem_localizedCoeffLattice : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (w : HeightOneSpectrum (𝓞 K)), ∀ x ∈ nabAtr emb lam L, (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam L) := by
  first | exact @GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr | exact GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr | (intros; apply GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr <;> assumption)
end
