module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle017
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle502
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle516
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqDatum

theorem mem_lbPow_U {X : Scheme.{0}} {M : LB X} {n : ℕ} {x : X} {i : PUnit → M.ι} :
    x ∈ (lbPow M n).U i ↔ x ∈ M.U (i PUnit.unit) :=
  ⟨fun h => by simpa using Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => by simpa using h⟩

theorem lbPow_U_le {X : Scheme.{0}} (M : LB X) (n : ℕ) (i : PUnit → M.ι) :
    (lbPow M n).U i ≤ M.U (i PUnit.unit) := fun _ h => mem_lbPow_U.1 h

theorem chart_le {X Y : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (n : ℕ) (i j : PUnit → M.ι) :
    chart f (lbPow M n) i j ≤ chart f M (i PUnit.unit) (j PUnit.unit) :=
  inf_le_inf (Scheme.Hom.preimage_mono _ (lbPow_U_le M n i)) (Scheme.Hom.preimage_mono _ (lbPow_U_le M n j))

theorem gm_lbPow_g {X Z : Scheme.{0}} (M : LB X) (n : ℕ) (p : Z ⟶ X) (z : Z) (i i' : PUnit → M.ι)
    (hi : p z ∈ M.U (i PUnit.unit)) (hi' : p z ∈ M.U (i' PUnit.unit)) :
    gm p z _ ((lbPow M n).g i i') = gm p z _ (M.g (i PUnit.unit) (i' PUnit.unit)) ^ n := by
  show gm p z _ (∏ _k : PUnit, (res _ (pullU (𝟙 X) _ (M.g (i PUnit.unit) (i' PUnit.unit)))) ^ ((n : ℕ) : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow, zpow_natCast]
  congr 1
  refine (gm_res p z _ (show p z ∈ LB.wchart M (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart M (fun _ : PUnit => 𝟙 X) i' from
    ⟨(mem_lbPow_U (n := n)).2 hi, (mem_lbPow_U (n := n)).2 hi'⟩) _).trans ?_
  refine (gm_pull p (𝟙 X) z _ (by simpa using And.intro hi hi') _).trans ?_
  rw [Category.comp_id]

theorem gm_pullTop {X Y : Scheme.{0}} (p : X ⟶ Y) (w : X) (u : Γ(Y, ⊤)ˣ) :
    gm (𝟙 X) w ⊤ (GlobalTheory.CharKer.pullTop p u) = gm p w ⊤ u := by
  apply Units.ext
  rw [gm_val _ w ⊤ trivial, gm_val _ w ⊤ trivial]
  simp [GlobalTheory.CharKer.pullTop]
  rfl

end GlobalTheory.SqDatum

namespace GlobalTheory.SqDatum

theorem commGroup_mul_eq_mul_mul_div {G : Type*} [CommGroup G] (a b c d x y z : G) (h₁ : d * c = a * b) (h₂ : d ^ 2 * x * y = z) :
    (a ^ 2 * x) * (b ^ 2 * y) = c ^ 2 * z := by
  rw [← h₂]
  calc (a ^ 2 * x) * (b ^ 2 * y) = (a * b) ^ 2 * x * y := by simp only [mul_pow]; ac_rfl
    _ = (d * c) ^ 2 * x * y := by rw [h₁]
    _ = c ^ 2 * (d ^ 2 * x * y) := by simp only [mul_pow]; ac_rfl

def psi {X Y : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ)
    (u : Γ(pullback f f, ⊤)ˣ) : ∀ i j, Γ(pullback f f, chart f (lbPow M 2) i j)ˣ :=
  fun i j => res (chart_le f M 2 i j) (φ (i PUnit.unit) (j PUnit.unit)) ^ 2 * res le_top u

theorem gm_psi {X Y Z : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ)
    (u : Γ(pullback f f, ⊤)ˣ) (p : Z ⟶ pullback f f) (z : Z) (i j : PUnit → M.ι)
    (h : p z ∈ chart f (lbPow M 2) i j) :
    gm p z _ (psi f M φ u i j) = gm p z _ (φ (i PUnit.unit) (j PUnit.unit)) ^ 2 * gm p z ⊤ u := by
  dsimp only [psi]
  rw [map_mul, map_pow, gm_res p z _ h, gm_res p z _ h]

theorem pullback_fst_snd_triple_eq_snd_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

theorem pullback_fst_tripleFibreProductProjOneThree {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.fst f f (pr13 f w) = pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_fst]

theorem pullback_snd_tripleFibreProductProjOneThree {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.snd f f (pr13 f w) = pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_snd]

theorem exists_sq_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ),
    DescCompat f M φ → Defect f M φ D → KillsSq f D u →
    ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ),
      M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  intro X Y f M hM φ D u hC hD hK
  have h₂ : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  refine ⟨lbPow M 2, psi f M φ u, h₂, GlobalTheory.lbIso_refl h₂, ?_, ?_⟩
  · intro z i i' j j' hi hi' hj hj'
    rw [gm_psi f M φ u (𝟙 _) z i' j' ⟨hi', hj'⟩, gm_psi f M φ u (𝟙 _) z i j ⟨hi, hj⟩,
      gm_lbPow_g M 2 _ z i i' (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi'),
      gm_lbPow_g M 2 _ z j' j (mem_lbPow_U.1 hj') (mem_lbPow_U.1 hj),
      hC z _ _ _ _ (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi') (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hj')]
    simp only [mul_pow]
    ac_rfl
  · intro w i j k hi hj hk
    have hj' : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ (lbPow M 2).U j := by
      rw [pullback_fst_snd_triple_eq_snd_fst]; exact hj
    have h13 : pr13 f w ∈ chart f (lbPow M 2) i k := by
      refine ⟨?_, ?_⟩
      · exact (show pullback.fst f f (pr13 f w) ∈ (lbPow M 2).U i by rw [pullback_fst_tripleFibreProductProjOneThree]; exact hi)
      · exact (show pullback.snd f f (pr13 f w) ∈ (lbPow M 2).U k by rw [pullback_snd_tripleFibreProductProjOneThree]; exact hk)
    rw [gm_psi f M φ u _ w i j ⟨hi, hj⟩, gm_psi f M φ u _ w j k ⟨hj', hk⟩, gm_psi f M φ u _ w i k h13]
    have hd := hD (Triple f) (𝟙 _) w (i PUnit.unit) (j PUnit.unit) (k PUnit.unit)
      (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hk)
    simp only [Category.id_comp] at hd
    have hk' := congrArg (gm (𝟙 _) w ⊤) hK
    simp only [map_mul, map_pow, gm_pullTop] at hk'
    exact commGroup_mul_eq_mul_mul_div _ _ _ _ _ _ _ hd hk'

end GlobalTheory.SqDatum
end
end

section

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoTors.TripleProd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def pt {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) : T ⟶ tripO A :=
  Over.homMk (GlobalTheory.PolRoot.tri (sq A).left a.left b.left c.left (congrArg CommaMorphism.left h₁)
    (congrArg CommaMorphism.left h₂)) (by
      show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom = _
      rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst_assoc, Over.w])

theorem pt_t₁ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₁ A = a :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst])

theorem pt_t₂ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₂ A = b :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_snd])

theorem pt_t₃ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₃ A = c :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_snd_assoc, pullback.lift_snd])

theorem ext₃ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h₂ : m ≫ t₂ A = n ≫ t₂ A)
    (h₃ : m ≫ t₃ A = n ≫ t₃ A) : m = n := by
  have e₁ : m.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ :=
    congrArg CommaMorphism.left h₁
  have e₂ : m.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₂
  have e₃ : m.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₃
  have e₄ := e₂
  rw [pullback.condition] at e₄
  refine Over.OverMorphism.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_))
  · exact (Category.assoc _ _ _).trans (e₁.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₂.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₄.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₃.trans (Category.assoc _ _ _).symm)

theorem comp_ψ_fst {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ fst _ _) ≫ incl A = (m ≫ t₁ A)⁻¹ * (m ≫ t₂ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_fst_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem comp_ψ_snd {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ snd _ _) ≫ incl A = (m ≫ t₂ A)⁻¹ * (m ≫ t₃ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_snd_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem ext₂ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h : m ≫ ψ A = n ≫ ψ A) : m = n := by
  have e₂ := comp_ψ_fst m
  have e₃ := comp_ψ_snd m
  rw [h, comp_ψ_fst, h₁] at e₂
  have h₂ : m ≫ t₂ A = n ≫ t₂ A := (mul_left_cancel e₂).symm
  rw [h, comp_ψ_snd, h₂] at e₃
  exact ext₃ h₁ h₂ (mul_left_cancel e₃).symm

theorem mul_sq {T : Over S} (a : T ⟶ A) (x : T ⟶ Two A) : a ≫ sq A = (a * (x ≫ incl A)) ≫ sq A := by
  rw [comp_sq, comp_sq, mul_pow, incl_sq, _root_.mul_one]

theorem exists_pt {T : Over S} (a : T ⟶ A) (q : T ⟶ Two A ⊗ Two A) :
    ∃ m : T ⟶ tripO A, m ≫ t₁ A = a ∧ m ≫ ψ A = q := by
  refine ⟨pt a (a * ((q ≫ fst _ _) ≫ incl A)) ((a * ((q ≫ fst _ _) ≫ incl A)) * ((q ≫ snd _ _) ≫ incl A))
    (mul_sq _ _) (mul_sq _ _), pt_t₁ _ _ _ _ _, ?_⟩
  refine CartesianMonoidalCategory.hom_ext _ _ (two_ext ?_) (two_ext ?_)
  · rw [comp_ψ_fst, pt_t₁, pt_t₂, inv_mul_cancel_left]
  · rw [comp_ψ_snd, pt_t₂, pt_t₃, inv_mul_cancel_left]

theorem isPullback {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] :
    IsPullback (t₁ A).left (ψ A).left A.hom (Two A ⊗ Two A).hom := by
  have w : (t₁ A).left ≫ A.hom = (ψ A).left ≫ (Two A ⊗ Two A).hom := (Over.w _).trans (Over.w _).symm
  have key : ∀ s : PullbackCone A.hom (Two A ⊗ Two A).hom, ∃ l : s.pt ⟶ (tripO A).left,
      l ≫ (t₁ A).left = s.fst ∧ l ≫ (ψ A).left = s.snd := fun s => by
    obtain ⟨m, h₁, h₂⟩ := exists_pt (T := Over.mk (s.fst ≫ A.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)
    exact ⟨m.left, congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩
  choose l hl₁ hl₂ using key
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l hl₁ hl₂ fun s m h₁ h₂ => ?_⟩⟩
  have hw : ∀ k : s.pt ⟶ (tripO A).left, k ≫ (t₁ A).left = s.fst → k ≫ (tripO A).hom = s.fst ≫ A.hom :=
    fun k hk => by rw [← hk, Category.assoc, Over.w]
  have e : (Over.homMk m (hw m h₁) : Over.mk (s.fst ≫ A.hom) ⟶ tripO A) = Over.homMk (l s) (hw _ (hl₁ s)) :=
    ext₂ (Over.OverMorphism.ext (h₁.trans (hl₁ s).symm)) (Over.OverMorphism.ext (h₂.trans (hl₂ s).symm))
  exact congrArg CommaMorphism.left e

end GlobalTheory.TwoTors.TripleProd
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaOntoF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ

theorem algebraMap_half (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)] :
    algebraMap F (AF F) (1 / 2) = ⅟2 := by
  refine (invOf_eq_right_inv ?_).symm
  have h : (2 : AF F) * algebraMap F (AF F) (1 / 2) = algebraMap F (AF F) (2 * (1 / 2)) := by
    rw [map_mul, map_ofNat]
  rw [h]
  norm_num

theorem heisV_comp_symm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {N : ℕ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N} (ψ : AddChar (AF F) ℂ)
    (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (u : VA F N) (f : WOF F E nS nT → ℂ) :
    heisV ψ u (f ∘ e.symm) = heisOF σ JS JT ξ₀ ψ (e.symm u) f ∘ e.symm := by
  funext w
  simp only [heisV, heisOF, symplOHF, Function.comp_apply, he, LinearEquiv.apply_symm_apply, map_add (f := _),
    algebraMap_half]

theorem exists_thV_eqF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd N e he hrat f hf
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, hcs, hfin, hinf⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_finite_real_points F E nS nT N e
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists F hR B.ψ hψ N (half F N) half_ne_zero
  obtain ⟨-, -, -, ⟨K, hK, hKc⟩, 𝓓, -, hD, h1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1
  have hsymm : ∀ (u : VA F N) (g : WOF F E nS nT → ℂ),
      heisV B.ψ u (g ∘ e.symm) = heisOF σ JS JT ξ₀ B.ψ (e.symm u) g ∘ e.symm :=
    fun u g => heisV_comp_symm B.ψ he u g
  have hquasi : ∀ g, IsThetaFunOF σ JS JT ξ₀ B.ψ g → QuasiV B.ψ (g ∘ e.symm) := by
    intro g hg a b w
    obtain ⟨x, hx⟩ := GlobalTheory.T.adelicLinearCoordinates_rational_surjective_of_CM F E nS nT N e hrat a b
    have hx' : e.symm (rat a, rat b) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    simp only [Function.comp_apply, map_add (f := _), hx', hg.quasi, symplOHF, he, hx, LinearEquiv.apply_symm_apply,
      algebraMap_half]
  have hbdd : ∀ g : VA F N → ℂ, Continuous g → QuasiV B.ψ g → ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    intro g hg hq
    obtain ⟨C, hC'⟩ := (hK.prod hK).exists_bound_of_continuousOn hg.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨a, ha⟩ := hKc w.1
    obtain ⟨b, hb⟩ := hKc w.2
    have e1 : w = (rat a, rat b) + (w.1 - rat a, w.2 - rat b) :=
      Prod.ext (by simp) (by simp)
    rw [e1, hq, norm_mul, hψ.2.1, one_mul]
    exact hC' _ ⟨ha, hb⟩
  let 𝒱 : Set (VA F N → ℂ) := {g | ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ g = f ∘ e.symm}
  have hV : ∀ g ∈ 𝒱, Continuous g ∧ QuasiV B.ψ g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨hg.cont.comp hcs, hquasi g hg, hbdd _ (hg.cont.comp hcs) (hquasi g hg)⟩
  have hder : ∀ g ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ g' ∈ 𝒱, ∀ x,
      HasDerivAt (fun t : ℝ => invV B.ψ ν 𝓓 (heisV B.ψ (M t) g) x) (invV B.ψ ν 𝓓 g' x) 0 := by
    rintro _ ⟨g, hg, rfl⟩ M hM
    let L : ℝ →+ WOF F E nS nT := e.symm.toLinearMap.toAddMonoidHom.comp M
    have hL : Continuous L := hcs.comp hM.1
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => (hfin _).2 (by
      have : e (L t) = M t := e.apply_symm_apply _
      rw [this]; exact hM.2 t)
    let g' : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) 0
    have hlev' : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u g' = g' := by
      obtain ⟨U, hUo, hU⟩ := hg.level
      exact ⟨U, hUo, fun u hu h0 =>
        GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g L hL hL0 u h0 (hU u hu h0)⟩
    have hsm' := GlobalTheory.T.contDiff_deriv_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0
    have hg' : IsThetaFunOF σ JS JT ξ₀ B.ψ g' :=
      ⟨GlobalTheory.T.deriv_heisenbergCM_theta_quasiInvariant_rational F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0, hlev',
        GlobalTheory.T.theta_lift_standard_character_indefinite F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g' hlev' hsm', hsm'⟩
    have hds : ∀ w s, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w)
        (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) s := by
      intro w s
      have h1' : HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)
          (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) 0 := by
        have e2 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w) = fun t =>
            B.ψ (symplOHF σ JS JT ξ₀ w (L s)) * heisOF σ JS JT ξ₀ B.ψ (L t) g (w + L s) :=
          funext fun t => GlobalTheory.T.heisenbergOp_realLine_add_eq_phase_mul_shifted F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd L hL hL0 g w s t
        rw [e2]
        exact ((GlobalTheory.T.differentiableAt_zero_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0 (w + L s)).hasDerivAt).const_mul _
      have h2 := HasDerivAt.comp_sub_const s s (by rwa [sub_self])
        (f := fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)
      have e3 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) =
          fun x => heisOF σ JS JT ξ₀ B.ψ (L (s + (x - s))) g w := by
        funext x; rw [add_sub_cancel]
      rw [e3]
      exact h2
    refine ⟨_, ⟨g', hg', rfl⟩, ?_⟩
    obtain ⟨c1, -, C₁, hC₁⟩ := hV _ ⟨g, hg, rfl⟩
    obtain ⟨c2, -, C₂, hC₂⟩ := hV _ ⟨g', hg', rfl⟩
    refine GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam F N B.ψ lam ν hC 𝓓 hD h1 _ _ (max C₁ C₂) c1 c2 (fun w => (hC₁ w).trans (le_max_left _ _))
      (fun w => (hC₂ w).trans (le_max_right _ _)) M hM.1 fun w s => ?_
    simp only [hsymm, Function.comp_apply]
    exact hds (e.symm w) s
  have hmem : f ∘ e.symm ∈ 𝒱 := ⟨f, hf, rfl⟩
  have hlev : LevelV B.ψ (f ∘ e.symm) := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap e.symm.toLinearMap.toAddMonoidHom, hUo.preimage hcs, fun u hu h0 h0' => ?_⟩
    rw [hsymm, hU (e.symm u) hu ((hinf _).2 (by rw [e.apply_symm_apply]; exact ⟨h0, h0'⟩))]
  obtain ⟨hl, hs⟩ := GlobalTheory.T.inverseThetaTransform_has_level_compact_finite_support F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).2.1 hlev
  have hS : invV B.ψ ν 𝓓 (f ∘ e.symm) ∈ GlobalTheory.WeilM.schA F (Fin N) :=
    GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz F N _ hl hs (GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates F N B.ψ lam ν hC 𝓓 hD h1 𝒱 hV hder
      (GlobalTheory.T.inverseAdelicThetaTransform_rapid_decay F N B.ψ lam ν hC 𝓓 hD h1 𝒱 (fun g hg => (hV g hg).2) hder) _ hmem)
  refine ⟨_, hS, ?_⟩
  rw [GlobalTheory.T.thetaTransform_inverseTransform_eq_quasiPeriodic F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).1 (hV _ hmem).2.1 (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N _ hS)]
  funext w
  simp

end GlobalTheory.ThetaOntoF

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

namespace GlobalTheory

theorem irrUnitary_trace_ne_zero_copyFinDS : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD ν hν H _ _ _ π hπ c hc hc0
  have hcomp : HasDSComp M π := GlobalTheory.T.discrete_series_spectral_side hDS hFl hHC hPC D V lam S M T U μa μf μ fa ff hTD H π hπ c hc hc0
  have hU : GlobalTheory.AutomorphicL2Unitary.IsSubrep π ⊤ := GlobalTheory.AutomorphicL2Unitary.isSubrep_top
  have hcopy := GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries D V S M H π hπ hcomp hU
  obtain ⟨hirr, hadm⟩ := GlobalTheory.T.finite_part_irreducible_admissible hFl D V S M H π hπ hcomp hU
  haveI : ν.IsHaarMeasure := hν.1
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν ff hfam _ (finPartDSSm M hU) hadm
  have hπc' := GlobalTheory.T.test_data_haar_factorization D V lam S M T U μa μf μ fa ff hTD ν hν H π hπ _ (finPartDSSm M hU) hirr hadm hcopy c' hc'
  have hcc : c' = c := hπc'.2.symm.trans hc.2
  subst hcc
  exact ⟨_, _, _, finPartDSSm M hU, hirr, hadm, hcopy, hc'⟩

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.toricPeriodZetaStatements_of_jetIntegrality_algebraicity : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  first | exact @GlobalTheory.JoinFun.joinOut_of_jetInt | exact GlobalTheory.JoinFun.joinOut_of_jetInt | (intros; apply GlobalTheory.JoinFun.joinOut_of_jetInt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.inertia_fixed_pos_valuation_dvd_uniformiser : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L), IsAbove R K W.toSubring → ∀ π : R, Irreducible π → ∀ y : L, (∀ τ ∈ inertia K W, τ y = y) → y ∈ W.nonunits → y / algebraMap K L (algebraMap R K π) ∈ W := by
  first | exact @GlobalTheory.InertiaUnram.div_uniformiser_mem | exact GlobalTheory.InertiaUnram.div_uniformiser_mem | (intros; apply GlobalTheory.InertiaUnram.div_uniformiser_mem <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_inertia_element_restricting_to_finite_galois : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (τ : L ≃ₐ[K] L), τ ∈ inertia K (V.comap (algebraMap L Ω)) → ∃ σ ∈ inertia K V, ∀ y : L, σ (y : Ω) = (τ y : Ω) := by
  first | exact @GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on | exact GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on | (intros; apply GlobalTheory.InertiaRestrict.exists_mem_inertia_eq_on <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] [IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A)] (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[L] Ω), galTate ((Over.pullback (spMap (algebraMap K L))).obj A) l σ = 1 ↔ galTate A l (σ.restrictScalars K) = 1 := by
  first | exact @GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff | exact GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff | (intros; apply GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff <;> assumption)
end
