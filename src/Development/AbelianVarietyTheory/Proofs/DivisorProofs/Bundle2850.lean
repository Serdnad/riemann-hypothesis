module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle167
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.AdjFwd

theorem adjoint_hermForm_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) → ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  intro A _ _ g hA _ N _ _ M u Hm χ hM hF f f' F F' hf hf' e e' hiso
  haveI := hf
  haveI := hf'
  obtain ⟨Mr, hMr, ⟨c⟩⟩ := GlobalTheory.AHWeilAny.exists_cubical A hA M hM
  subst hMr
  have hR := GlobalTheory.AdjPolLocal.rosatiAdj_of_lbIso _ A Mr.L f f' hM hiso
  have hFl : ∀ a : u.Λ, F a ∈ u.Λ := fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]
  have hF'l : ∀ a : u.Λ, F' a ∈ u.Λ := fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]
  refine GlobalTheory.HermAdjoint.adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.AHWeilFactor.im_hermForm_int hM u hF ⟨_, hFl ⟨a, ha⟩⟩ ⟨b, hb⟩
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.AHWeilFactor.im_hermForm_int hM u hF ⟨a, ha⟩ ⟨_, hF'l ⟨b, hb⟩⟩
  have hE : E₁ = E₂ := GlobalTheory.HermAdjoint.int_eq_of_exp fun n hn => by
    have hx := GlobalTheory.HermAdjoint.ex_period_pow u hn ⟨a, ha⟩
    have hy := GlobalTheory.HermAdjoint.ex_period_pow u hn ⟨b, hb⟩
    have hy' : (u.ex ((n : ℂ)⁻¹ • b) ≫ f') ^ n = 1 := by
      rw [← MonObj.pow_comp]
      exact (congrArg (· ≫ f') hy).trans (MonObj.one_comp _)
    let c₁ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (E₁ : ℂ) / n))
    let c₂ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (E₂ : ℂ) / n))
    have v₁ : Out.WeilIs A Mr.L n (u.ex ((n : ℂ)⁻¹ • a) ≫ f) (u.ex ((n : ℂ)⁻¹ • b)) (unitOn c₁) := by
      rw [← e, map_smul]
      refine GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA Mr.L hM g u Hm χ hF n (F a) b c₁ hn
        (hFl ⟨a, ha⟩) hb ?_
      show Complex.exp _ = _
      rw [← hE₁, Complex.ofReal_intCast]
    have v₂ : Out.WeilIs A Mr.L n (u.ex ((n : ℂ)⁻¹ • a)) (u.ex ((n : ℂ)⁻¹ • b) ≫ f') (unitOn c₂) := by
      rw [← e', map_smul]
      refine GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA Mr.L hM g u Hm χ hF n a (F' b) c₂ hn
        ha (hF'l ⟨b, hb⟩) ?_
      show Complex.exp _ = _
      rw [← hE₂, Complex.ofReal_intCast]
    have v₁' := (GlobalTheory.WeilCube.weilIs_rosati c GlobalTheory.globalFns_holds hA f f' hR hx hy _).1 v₁
    obtain ⟨e₀, he₀⟩ := GlobalTheory.WeilCube.exists_isRatio c n _ _ hx hy'
    have h₁ := (GlobalTheory.WeilCube.weilIs_iff c GlobalTheory.globalFns_holds hA hx hy' he₀ _).1 v₁'
    have h₂ := (GlobalTheory.WeilCube.weilIs_iff c GlobalTheory.globalFns_holds hA hx hy' he₀ _).1 v₂
    exact congrArg Units.val (GlobalTheory.HermAdjoint.unitOn_injective (h₁.trans h₂.symm))
  show (F a ⬝ᵥ Hm *ᵥ star b).im = (a ⬝ᵥ Hm *ᵥ star (F' b)).im
  rw [← hE₁, ← hE₂, hE]

end GlobalTheory.AdjFwd
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.JoinPull

section Helpers

variable {X X₁ Z : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}

theorem part_g_of_eq (h : IsPart N M e π) (ψ : Z ⟶ X₁) (χ : Z ⟶ X) (hχ : χ = ψ ≫ e) (z : Z) (i j : N.ι)
    (hi : ψ z ∈ M.U (π i)) (hj : ψ z ∈ M.U (π j)) :
    gm χ z (N.U i ⊓ N.U j) (N.g i j) = gm ψ z (M.U (π i) ⊓ M.U (π j)) (M.g (π i) (π j)) := by
  subst hχ; exact h.g _ ψ z i j hi hj

theorem part_g_eq_one (h : IsPart N M e π) (hM : M.IsLB) (ψ : Z ⟶ X₁) (χ : Z ⟶ X) (hχ : χ = ψ ≫ e) (z : Z)
    (i j : N.ι) (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) : gm χ z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  rw [part_g_of_eq h ψ χ hχ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

end Helpers

theorem exists_iso_of_joinGen : ∀ {X₁ X₂ : Scheme.{0}} (M : LB X₁) (M' : LB X₂), M.IsLB → M'.IsLB → Nonempty X₁ → Nonempty X₂ → ∀ (F : X₂ ⟶ X₁) (t : LB.Gen (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))))), t.IsGen → ∃ w : LB.Iso M' (M.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X₂) (z : Z) (J : (Z ⟶ X₂ ⨿ X₁) → (join M' M).ι), Good (join M' M) z J → gw w f z (rr J (f ≫ F)) (rl J f) = val t f z J := by
  intro X₁ X₂ M M' hM hM' h₁ h₂ F t ht
  obtain ⟨i₀⟩ := @nonempty_idx _ _ hM h₁
  obtain ⟨k₀⟩ := @nonempty_idx _ _ hM' h₂
  have hl := isPart_inl M' M
  have hr := isPart_inr M' M
  have le : ∀ a : (PUnit.{1} → M.ι) × M'.ι, (LB.div (M.pull F) M').U a ≤
      LB.wchart (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
        (Sum.elim (fun _ => (k₀, a.1 PUnit.unit)) (fun _ => (a.2, i₀))) := fun a y hy =>
    Set.mem_iInter.2 fun k => by
      rcases k with u | u
      · exact (hr.mem (k₀, a.1 PUnit.unit) (F y)).2 (mem_pull.1 hy.1)
      · exact (hl.mem (a.2, i₀) y).2 hy.2
  let c : ChartPull (LB.div (M.pull F) M')
      (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
        (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ)))) (𝟙 X₂) :=
    { idx := fun a => Sum.elim (fun _ => (k₀, a.1 PUnit.unit)) (fun _ => (a.2, i₀))
      le := le
      g := fun y a b ha hb => by
        refine (gm_div M' (M.pull F) (𝟙 X₂) y a b ⟨ha, hb⟩).trans ?_
        refine Eq.trans ?_ (gm_linComb (join M' M) _ _ (𝟙 X₂) y _ _ (le a ha) (le b hb)).symm
        rw [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique]
        exact congrArg₂ (· * ·)
          ((gm_pull_g M F (𝟙 X₂) y a.1 b.1 ha.1 hb.1).trans ((part_g_of_eq hr (𝟙 X₂ ≫ F) _
            (Category.assoc _ _ _).symm y (k₀, a.1 PUnit.unit) (k₀, b.1 PUnit.unit) (mem_pull.1 ha.1)
            (mem_pull.1 hb.1)).symm.trans (zpow_one _).symm))
          ((congrArg (·⁻¹) (part_g_of_eq hl (𝟙 X₂) _ rfl y (a.2, i₀) (b.2, i₀) ha.2 hb.2).symm).trans
            (zpow_neg_one _).symm) }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z f z J hJ => ?_⟩
  have m : f z ∈ (LB.div (M.pull F) M').U (fun _ => rr J (f ≫ F), rl J f) :=
    ⟨mem_pull.2 (hr.good hJ (f ≫ F)), hl.good hJ f⟩
  have n := hJ.mem (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) f
  refine (gm_res f z _ m _).trans ((gen_trans ht f z (le _ m) n).trans ?_)
  have e₁ : trF (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
      (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))) f z
      (Sum.elim (fun _ => (k₀, rr J (f ≫ F))) (fun _ => (rl J f, i₀)))
      (fun k => J (f ≫ Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl) k)) = 1 := by
    rw [trF, Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique]
    exact (congrArg₂ (· * ·)
      ((congrArg (· ^ _) (part_g_eq_one hr hM (f ≫ F) _ (Category.assoc _ _ _).symm z
        (k₀, rr J (f ≫ F)) (J (f ≫ F ≫ coprod.inr))
        (congrArg (fun q => (J q).2) (Category.assoc _ _ _)) (hr.good hJ (f ≫ F)))).trans (one_zpow _))
      ((congrArg (· ^ _) (part_g_eq_one hl hM' f _ rfl z (rl J f, i₀) (J (f ≫ coprod.inl)) rfl
        (hl.good hJ f))).trans (one_zpow _))).trans (mul_one 1)
  exact (congrArg (· * _) e₁).trans (one_mul _)

end GlobalTheory.JoinPull
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.HomMum

abbrev MK : Type := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))

variable {S : Scheme.{0}}

def mφ (H₁ H₂ : Over S) [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂) :
    MK → ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) :=
  Sum.elim (fun I => (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr)
    (fun I => (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl)

def mε : MK → ℤ :=
  Sum.elim (fun I => (-1 : ℤ) ^ (2 - I.down.card)) (fun I => -((-1 : ℤ) ^ (2 - I.down.card)))

def IsNrm {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {a b : H₁ ⟶ H₂}
    {L₁ : LB H₁.left} {L₂ : LB H₂.left} (u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)) : Prop :=
  u.IsGen ∧ ∀ (y : (𝟙_ (Over S)).left) (J), Good (join L₁ L₂) y J →
    val u (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left y J = 1

end GlobalTheory.HomMum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory

namespace WeightValPart

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem coeff_eq_zero_over {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {X : Scheme.{0}} {N : LB X}
    (hN : N.IsLB) {ι₀ : D.P.A.left ⟶ X} {π : N.ι → D.P.L.ι} (hP : IsPart N D.P.L ι₀ π) {K : Type} [Fintype K]
    {φ : D.X → K → (Y.left ⟶ X)} {ε : K → ℤ} (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X)
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left →
      ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0)
    (α : D.X) (hα : α ∈ s) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Z ⟶ thickObj R I e G)
    (r : Z.left ⟶ Y.left) (hr : r ≫ p.left = x.left ≫ g.pG.left) (z : Z.left) (J) (hJ : Good N z J) :
    sval (d α) r z J = 0 := by
  classical
  let jf : D.X → K → N.ι := fun β a => J (r ≫ φ β a)
  let jt : D.X → Fin 4 → D.P.L.ι := fun β a => rs ι₀ π J (x.left ≫ D.Oφ g.pG β a)
  let V : Z.left.Opens := s.inf (fun β => r ⁻¹ᵁ LB.wchart N (φ β) (jf β) ⊓
      x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β))
  have hz : z ∈ V := DVR.mem_finf s _ _ fun β _ => ⟨hJ.mem (φ β) r, (hP.good hJ).mem (D.Oφ g.pG β) x.left⟩
  have hVf : ∀ β ∈ s, V ≤ r ⁻¹ᵁ LB.wchart N (φ β) (jf β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_left
  have hVt : ∀ β ∈ s, V ≤ x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_right
  have ex : ∀ β ∈ s, ∃ c : Γ(Z.left, V), ∀ (W : Scheme.{0}) (ρ : W ⟶ Z.left) (w : W),
      ρ w ∈ V → gs ρ w V c = gs (ρ ≫ r) w (LB.wchart N (φ β) (jf β)) ((d β).f (jf β)) *
        (gm (ρ ≫ x.left) w (LB.wchart D.P.L (D.Oφ g.pG β) (jt β)) ((g.t β).s (jt β))).val := fun β hβ =>
    ⟨(r.appLE _ V (hVf β hβ)).hom ((d β).f (jf β)) * (x.left.appLE _ V (hVt β hβ)).hom ((g.t β).s (jt β)).val,
      fun W ρ w hw => (gs_mul ρ w V hw _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ w hw _)
        ((gs_appLE _ _ V _ ρ w hw _).trans (gs_unit (ρ ≫ x.left) w _ (hVt β hβ hw) _)))⟩
  choose! c hc using ex
  have hsn : (WeightPf.Te D I e ◁ x).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left =
      (snd (WeightPf.Te D I e) Z).left ≫ x.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  let σ : Z ⟶ WeightPf.Te D I e ⊗ Z := lift (toUnit _ ≫ η[WeightPf.Te D I e]) (𝟙 _)
  have hσ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have H0 := WeightVal.eq_zero_of_stalk_sum D.X Z s c (fun w hw => by
    choose j hj using fun ψ : (WeightPf.Te D I e ⊗ Z).left ⟶ X => exists_chart hN (ψ w)
    let J₂ : ((WeightPf.Te D I e ⊗ Z).left ⟶ X) → N.ι := fun ψ =>
      if ψ w ∈ N.U (J (σ.left ≫ ψ)) then J (σ.left ≫ ψ) else j ψ
    have hJ₂ : Good N w J₂ := fun ψ => by
      by_cases h : ψ w ∈ N.U (J (σ.left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hj ψ
    have eJ : ∀ ψ : Z.left ⟶ X, ψ ((snd (WeightPf.Te D I e) Z).left w) ∈ N.U (J ψ) →
        J₂ ((snd (WeightPf.Te D I e) Z).left ≫ ψ) = J ψ := fun ψ h => by
      have e₁ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left ≫ ψ = ψ := by
        rw [← Category.assoc, hσ, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    have E := H _ ((WeightPf.Te D I e ◁ x).left ≫ (WeightPf.act g).left) ((snd (WeightPf.Te D I e) Z).left ≫ r)
      (by rw [Category.assoc, Category.assoc, hr, WeightPf.act_left_pG, ← Category.assoc, ← Category.assoc, hsn])
      w J₂ hJ₂
    refine Eq.trans (Finset.sum_congr rfl fun β hβ => ?_) E
    rw [hc β hβ _ _ w hw, WeightVal.val_act g β _ w (hP.good hJ₂), mul_left_comm, hsn, WeightVal.gs_chiP_whisker,
      sval_of (d β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (g.t β) _ w (rs ι₀ π J₂) (jt β) (fun a => by
        have m : ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀) ((snd (WeightPf.Te D I e) Z).left w) ∈
            N.U (J ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀)) := (hP.mem _ _).2 (Set.mem_iInter.1 (hVt β hβ hw) a)
        show π (J₂ ((((snd (WeightPf.Te D I e) Z).left ≫ x.left) ≫ D.Oφ g.pG β a) ≫ ι₀)) =
          π (J ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀))
        rw [show (((snd (WeightPf.Te D I e) Z).left ≫ x.left) ≫ D.Oφ g.pG β a) ≫ ι₀ =
          (snd (WeightPf.Te D I e) Z).left ≫ ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀) by simp only [Category.assoc], eJ _ m])]) α hα
  have E := hc α hα _ (𝟙 _) z hz
  rw [H0, gs_eq _ z V hz, map_zero, map_zero, Category.id_comp, Category.id_comp] at E
  exact (Units.mul_left_eq_zero _).1 E.symm

end WeightValPart

theorem sval_eq_zero_of_sum_mul_coord_part : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (ι₀ : D.P.A.left ⟶ X) (π : N.ι → D.P.L.ι), IsPart N D.P.L ι₀ π → ∀ (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ X)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → sval (d α) r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X N hN ι₀ π hP K _ φ ε d s H α hα Z x r hr z J hJ
  exact WeightValPart.coeff_eq_zero_over g p hN hP d s H α hα (Over.mk (x ≫ (thickObj R I e G).hom))
    (Over.homMk x rfl) r hr z J hJ

end GlobalTheory
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7}

theorem om_fockF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {ε : Bool} {M X : HSp D} (A : Fr M) (B : Fr X)
    {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X} (hω : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) {h : GA D X} (hh : h ∈ GfC X)
    {f : WO M X → ℂ} (hf : IsFinF ψ θ ε A B f) (c : ℂ) (P) :
    fockF ψ θ ε A B (c • ω (1, h) f) P = c • ω (1, h) (fockF ψ θ ε A B f P) := by
  have e : ω.toSgn ε (1, h) = ω (1, h) := by simp [GlobalTheory.Grid.WRep.toSgn]
  have h1 := GlobalTheory.FiniteFock.compAt_mt_of_finite θ (S := GlobalTheory.Grid.sgn ε M) (hk := one_mem _)
  have h2 := GlobalTheory.FiniteFock.compAt_mt_of_finite θ (hk := hh)
  have := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ _ X χ χ' _ hω hθ (frSgn ε A).cart _ A.onb _ B.cart _ B.onb _ 1 h
    (fun τ => by rw [h1, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h1, Matrix.one_mul]) (fun τ => by rw [h2, Matrix.one_mul]) f hf.1 P).2
  rw [e] at this
  exact (GlobalTheory.FiniteFock.pureTensorO_smul _ _ _ _ _ _ _ _ _ _ _).trans (congrArg (c • ·) this.symm)

theorem om_compare {ψ : AddChar (AF D.host.F) ℂ} {S X : HSp D} {χ χ' χ₁ χ₁' : (AE D)ˣ →* Circle} {ω ω₁}
    (hω : IsWeilDatumO ψ S X χ χ' ω) (hω₁ : IsWeilDatumO ψ S X χ₁ χ₁' ω₁) {h : GA D X} {y : (AE D)ˣ} (hy : IsDetRoot X h y)
    {f} (hf : IsThetaFunO ψ S X f) : ω₁ (1, h) f = ((χ₁ y : ℂ) * (χ y : ℂ)⁻¹) • ω (1, h) f := by
  rw [GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ S X χ χ' χ₁ χ₁' ω ω₁ hω hω₁ 1 h 1 y (by simp [IsDetRoot]) hy f hf]
  simp [splitFacO]

theorem thetaAt_move {ψ : AddChar (AF D.host.F) ℂ} {S X : HSp D} {χ χ' : (AE D)ˣ →* Circle} {ω}
    (hω : IsWeilDatumO ψ S X χ χ' ω) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)} (hS : Submodule.IsFullLattice D.host.E ΛS) (hX : Submodule.IsFullLattice D.host.E ΛX)
    {a : AE D} (ha : a * a = a) (hc : a * cA D a = 0) (hinf : infPart D a = 0) {b b' Φ f : WO S X → ℂ} (hb : IsThetaFunO ψ S X b)
    {h : GA D X} (hfx : ∀ x : WO S X, IsHalf a x ∨ IsHalf (cA D a) x → actO S X 1 h x = x) {c : ℂ} (hc0 : c ≠ 0)
    (e : ω (1, h) b = c • b')
    (hf : IsThetaAt ψ (symplO S X) (heisO ψ S X) a (latO S X ΛS ΛX fun _ => True) 1 b Φ f) :
    IsThetaAt ψ (symplO S X) (heisO ψ S X) a (latO S X ΛS ΛX fun _ => True) 1 b' Φ (c⁻¹ • ω (1, h) f) := by
  letI := hS
  letI := hX
  have := GlobalTheory.ThetaBaseMove.isThetaAt_move hω
    (fun f₀ h₀ Tm hTm Ψ hΨ => GlobalTheory.DiagLiftFix.isTheta_placeModel hω.std inferInstance inferInstance ha hc hinf h₀ Tm hTm Ψ hΨ) hb 1 h
    (inv_ne_zero hc0) hfx hf
  rwa [e, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}



theorem exists_move (hL : L.Is μ₀) (hst : ∀ t, SquareStanding G t) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {i j : Fin D.R.m}
    {X : TriG G i j} (hX : TopGrid W i j X) {νH}
    (hI : X.Is W.ψ W.θ (fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) νH (locPl G))
    {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁) :
    ∃ h ∈ GfC (spX G i j), ∃ (cA cB : ℂ) (y : (AE D)ˣ), cA ≠ 0 ∧ cB ≠ 0 ∧ ∀ t,
      IsLinA B t i j ρ (X.e t) (locFst B t X) (cA⁻¹ • X.ω t (1, h) (X.f t)) ∧
      IsLinB B t i j ρ (X.e t) (locSnd B t X) ((cB * (L.xi t y : ℂ))⁻¹ • X.ω' t (1, h) (X.f' t)) := by
  obtain ⟨h, hh, Λ, hΛ, hfx, hmv, tA, tB⟩ := GlobalTheory.T.exists_finiteUnitary_selfDual_lattice_grid_doubling (G := G) hL i j
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hX
  have x7 := x6 AV AV₁ hV hV₁
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  have sW₁ := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  have sX : IsSelfDualC (spX G i j) (latX G i j) := by have := hI.rigW.1; rwa [x3] at this
  have vA := hI.isVac
  have vB := hI.isVac'
  rw [x1, x3, x4, x7] at vA
  rw [x2, x3, x5, x7] at vB
  have eA : ∀ t, (X.ω t).toSgn true (1, h) = X.ω t (1, h) := fun t => by simp [GlobalTheory.Grid.WRep.toSgn]
  have h2 := GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ (hk := hh)
  have mA := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (hI.weil μ₀) W.θ_is _ _ _ _ _ _ _ _ 1 h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul]) (hmv _ _ (isSelfDualC_neg sW)) _ vA
  have mB := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (hI.weil' μ₀) W.θ_is _ _ _ _ _ _ _ _ 1 h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul]) (hmv _ _ sW₁) _ vB
  obtain ⟨cA', hcA, kA⟩ := GlobalTheory.T.unitVacuum_eq_smul_arrowVacua_product hL W ρ i j AV AV₁ hV hV₁ Λ hΛ tA _ mA
  obtain ⟨cB, hcB, kB⟩ := GlobalTheory.T.unitVacuum_eq_smul_product_arrow_vacua hL W ρ i j AV AV₁ hV hV₁ Λ hΛ tB _ mB
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ h
  refine ⟨h, hh, cA', cB * (L.xi μ₀ y : ℂ)⁻¹, y, hcA, mul_ne_zero hcB (inv_ne_zero (Circle.coe_ne_zero _)), fun t => ⟨?_, ?_⟩⟩
  · have he := hI.idem t
    have f1 := hI.fst t
    rw [x1, x3, GlobalTheory.T.standardPairFirstMember_eq_prod_local_gridBases hL B t i j X _ he] at f1
    have k : (X.ω t).toSgn true (1, h) X.vac = cA' • vacA ρ i j := by
      rw [om_compare (hI.weil μ₀) (hI.weil t) hy vA.2.theta, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_smul, kA]
    have := thetaAt_move (ΛS := G.Λ (.grid (i + 1) (j + 1))) (ΛX := latX G i j)
      (hI.weil t) (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sX) (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2 (GlobalTheory.PlaceVec.idemSum_infPart he)
      vA.2.theta (hfx t (hst t) _ he _) hcA k f1
    rwa [eA] at this
  · have he := hI.idem t
    have f1 := hI.snd t
    rw [x2, x3, GlobalTheory.T.standardPairSecondMember_eq_prod_local_gridBases hL B t i j X _ he] at f1
    have k : X.ω' t (1, h) X.vac' = (cB * (L.xi μ₀ y : ℂ)⁻¹ * (L.xi t y : ℂ)) • vacB ρ i j := by
      refine (om_compare (hI.weil' μ₀) (hI.weil' t) hy vB.2.theta).trans ?_
      rw [kB, smul_smul]
      congr 1
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, LevCh.mu, Lift.tup, MonoidHom.mul_apply, Circle.coe_mul]
      field_simp
    exact thetaAt_move (S := spW₁ G i j) (ΛS := G.Λ (.grid i j)) (ΛX := latX G i j)
      (hI.weil' t) (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW₁)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sX) (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he])
      (by rw [← map_mul, he.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he))
      vB.2.theta (fun x hx => hfx t (hst t) _ he _ x (by rwa [GlobalTheory.LatVac.cA_cA, or_comm] at hx))
      (mul_ne_zero (mul_ne_zero hcB (inv_ne_zero (Circle.coe_ne_zero _))) (Circle.coe_ne_zero _)) k f1

end GlobalTheory.TopFlip

end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G))
    (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det) (hhol : IsHolTo Set.univ (fun z => (e z).left))
    (he : IsExpAt t y e) : IsExpAt t y (fun w => e (M *ᵥ w)) := by
  have hchain : ∀ w v, IsDerivAt0 (fun u => (e (M *ᵥ u)).left) w v ↔
      IsDerivAt0 (fun u => (e u).left) (M *ᵥ w) v := by
    intro w v
    rw [GlobalTheory.HolHom.isDerivAt0_iff, GlobalTheory.HolHom.isDerivAt0_iff]
    exact GlobalTheory.ShFam.BdArc.LatSec.isDerivAt_comp_iff (GlobalTheory.HolHom.holAt_of_isHolTo hhol (Set.mem_univ 0))
      (Matrix.mulVecLin M).toContinuousLinearMap w v
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  refine ⟨fun v w => ?_, fun w => ?_, fun v hv => ?_⟩
  · simp only [Matrix.mulVec_add]
    exact he.1 _ _
  · simp_rw [hchain]
    exact he.2.1 (M *ᵥ w)
  · obtain ⟨w', hw', huniq⟩ := he.2.2 v hv
    refine ⟨M⁻¹ *ᵥ w', ?_, fun w₂ hw₂ => ?_⟩
    · show IsDerivAt0 (fun u => (e (M *ᵥ u)).left) (M⁻¹ *ᵥ w') v
      rw [hchain, Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
      exact hw'
    · have h2 : M *ᵥ w₂ = w' := huniq _ ((hchain w₂ v).1 hw₂)
      rw [← h2, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]

end GlobalTheory.ShFam.Hor.LogCh
end
