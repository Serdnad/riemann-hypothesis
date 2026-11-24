module

import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPtExist

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_isTwistPull (hL : L.IsLB) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (hα : α.IsGen)
    (s : LB.Sec (LPow A L b T)) : ∃ s', IsTwistPull A L ψ m hm a b α s s' := by
  intros
  apply _root_.GlobalTheory.VVRank.exists_isTwistPull <;> assumption

theorem exists_isValueAt (hL : L.IsLB) {n : ℤ} (s : LB.Sec (LPow A L n T)) (w : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => n)))
    (hτ : τ.IsGen) : ∃ c, IsValueAt A L n s w τ c :=
  (EvVal.existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover L hL _ _)
    (EvVal.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (ptSecT A w).left
      (fun _ => w.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le A L w) s) τ hτ).exists


open ThetaAct in
theorem exists_pullSec (hL : L.IsLB) {a : ℤ} {T' : Over S} (h : T' ⟶ T) (v : SecM A L a T) :
    ∃ w : SecM A L a T', ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J), Good L z J →
      sv w r z J = sv v (r ≫ (h ▷ A).left) z J := by
  have e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  obtain ⟨w, hw⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T' A).left) (ε' := fun _ => a)
    (fun U _ f => Finset.prod_congr rfl fun i _ => congrArg (fun q => f q ^ a) e₀)
    (H1.SectionArithmetic.pullSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (SecM.toSec A v) (h ▷ A).left)
  exact ⟨SecM.ofSec A w, fun Z r z J hJ => (hw Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩


open ThetaAct in
theorem exists_isGenSec_of_retract (hL : L.IsLB) {a : ℤ} {T' : Over S} (i : T' ⟶ T) (h : T ⟶ T')
    (hi : i ≫ h = 𝟙 T') (t : SecM A L a T) (ht : ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s) :
    ∃ th, IsGenSec A L a (T := T') th := by
  obtain ⟨t', ht'⟩ := exists_pullSec hL i t
  refine ⟨SecM.toSec A t', fun s => ?_⟩
  obtain ⟨s₀, hs₀⟩ := exists_pullSec hL h (SecM.ofSec A s)
  obtain ⟨r, hr⟩ := ht s₀
  have key : SecM.ofSec A s = i.left.appTop.hom r • t' := sv_ext hL fun y J hJ => by
    have e₁ : (𝟙 _ ≫ (i ▷ A).left) ≫ (h ▷ A).left = 𝟙 _ := by
      rw [Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi, id_whiskerRight, Category.id_comp]; rfl
    have e₂ : (𝟙 _ ≫ (i ▷ A).left) ≫ (fst T A).left = (𝟙 _ ≫ (fst T' A).left) ≫ i.left := by
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
    have q := hs₀ _ (𝟙 _ ≫ (i ▷ A).left) y J hJ
    rw [e₁, ← hr, sv_smul _ _ _ _ hJ, e₂] at q
    rw [sv_smul _ _ _ _ hJ, ht' _ _ _ _ hJ, ← q]
    exact congrArg (· * _) (gs_pull (𝟙 _ ≫ (fst T' A).left) i.left y ⊤ trivial r).symm
  exact ⟨i.left.appTop.hom r, fun j => congrArg (fun q => q.1 j) key⟩

theorem exists_generator_of_isField {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (hR : IsField R)
    (h : Module.finrank R M = 1) : ∃ t : M, t ≠ 0 ∧ ∀ s, ∃ r : R, r • t = s := by
  letI := hR.toField
  exact finrank_eq_one_iff'.1 h

theorem exists_isThetaPt (hLaw : Laws) (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (k : ℕ) (hk : Odd k) (hK : (k : K) ≠ 0) {I : Type}
    (x : I → (baseOver (Spec (CommRingCat.of K)) ⟶ P.A)) (hx : ∀ i, x i ^ (k ^ 2) = 1) :
    ∃ v, IsThetaPt P k x v := by
  have hL := P.isLB
  let T := baseOver (Spec (CommRingCat.of K))
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hu : IsUnit (k : Γ(Spec (CommRingCat.of K), ⊤)) := by
    rw [← map_natCast e]
    exact (IsUnit.mk0 _ hK).map e
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let T' : Over (Spec (CommRingCat.of K)) := overRes (T := T) ⊤
  obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) (V := ⊤) (p := p) trivial
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 T' := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  obtain ⟨t, -, ht⟩ : ∃ t : SecM P.A P.L 1 T, t ≠ 0 ∧ ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s := by
    exact exists_generator_of_isField (MulEquiv.isField (Field.toIsField K) e.symm.toMulEquiv)
      ((hLaw.globalSectionsRank K P 1 le_rfl).trans (one_pow _))
  obtain ⟨th, hth⟩ := exists_isGenSec_of_retract hL (overResι (T := T) ⊤) h hi t ht
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P k
  have e₁ : (snd T' P.A).left ≫ (mulA P.A k).left = (snd T' P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen hL (φ' := ![(snd T' P.A).left, (snd T' P.A ^ k).left]) (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T' P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨τ, hτ, -⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) (ε' := fun _ => (k : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T').left) (k ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)
  obtain ⟨s₁, hs₁⟩ := exists_isTwistPull hL (mulT P.A T' k) (snd T' P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α hα th
  have hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T',
      SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (overResι (T := T) ⊤ ≫ x i) θ := fun i => by
    obtain ⟨V, hV, θ, hθ⟩ := (hLaw.symLift _ P (k ^ 2) hk.pow (by rw [Nat.cast_pow]; exact hu.pow 2) T (x i)
      (hx i)).1 p
    obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim q p]
    rw [← Nat.cast_pow]
    exact ⟨θ, hθ⟩
  choose U hU using hU
  choose s₂ hs₂ using fun i => exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt) (lift_snd _ _)
    ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  choose w hw using fun i => exists_isValueAt hL (s₂ i) 1 τ hτ
  refine ⟨fun i => h.left.appTop.hom (w i), hk, hu, fun _ => ⟨⊤, trivial, th, s₁, α, τ, U, s₂, w, 1, hth, hα, hτ,
    hs₁, hU, hs₂, hw, fun i => ?_⟩⟩
  have q := congrArg (fun q => q.left.appTop.hom (w i)) hi
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
    Scheme.Hom.id_appTop] at q
  exact q.trans (_root_.one_mul _).symm

end GlobalTheory.ThetaPtExist
