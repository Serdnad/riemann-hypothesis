module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle003
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle011
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle020
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormEtaProductFormLeAtUnitFrame
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle016
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle013
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle014
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.RelabellingGoodEmbeddingIsTypeFnStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaConst.ArchBound

theorem norm_pow_le_at_unit_frame (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hA : AllTest Xo c) (R : ℕ) (hR : Odd R)
    (h1R : 1 < R) (xs : Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c)
    (hsp : Submodule.span (𝓞 E) (Set.range xs) = ⊤)
    (hf : GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f) (DF q m : ℕ) (R0 : ℝ)
    (hrun : RunOK E r DF q R0 m) (hm : Dw.p ≤ m ∨ Dw.q ≤ m) (k : U.Comp) (x : (U.X k).dom)
    (hx : ∀ τ i, ‖dmin (U.X k).Gm x.1 τ i‖ = 1) :
    ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ^ (2 * R ^ 4) ≤
      Real.exp (-((1 : ℕ) : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x.1 - p16 E r q m R 1)) := by
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨Hm, χl, fr, θ, Fd, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hFd, hl2⟩ := Uw.norm k x hx
  have hy : (U.un k x).x = Uw.F.u (Uw.ik k) (Uw.Pm k x) := (Uw.lie k x).1
  have hP := Uw.period k x
  have hfn : IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr (U.un k x).x (U.un k x).s θ := a₉
  have hAH : AHFrame Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr :=
    ⟨a₁, a₂, a₃, a₄, a₅, a₆, fun j hj => by rw [← hy]; exact a₇ j hj, a₈⟩
  have hty := (GlobalTheory.T.relabelling_goodEmbedding_isTypeFn E H Dw l Xo c σ hσ).2.2 Uw.g Uw.e
  have hty' : IsTypeFn H (Uw.F.Di (Uw.ik k)).p (Uw.F.Di (Uw.ik k)).q
      (fun j => Formalism.L2.PjFree.relab c σ (Uw.e j).1) := by
    rw [(Uw.F.sig _).1, (Uw.F.sig _).2]
    exact hty
  obtain ⟨T, ψ, hT⟩ := GlobalTheory.T.exists_torus_of_period_hermitian E H _ _ _ _ Hm hty' hP a₁ a₂ a₃
  obtain ⟨-, hr, hph, hdim⟩ := GlobalTheory.T.periodTorus_isTorusAt_frame E H Dw l Xo c σ r U hσ hU Uw k x Hm T ψ ⟨a₁, a₂, a₃⟩ hT
  have hhol : Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) = χl (Uw.Pm k x a) *
      Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) + Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) *
        θ z := by
    have key : ∀ (x₀ : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x₀)), x₀ = Uw.F.u (Uw.ik k) (Uw.Pm k x) →
        IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr x₀ s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) =
          χl (Uw.Pm k x a) * Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) +
            Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) * θ z := by
      intro x₀ s h₀ hs
      subst h₀
      exact GlobalTheory.T.appellHumbert_section_entire_with_factor E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH s θ hs
    exact key _ _ hy hfn
  have hchi := GlobalTheory.T.ahFrame_factor_eq_negOnePow_riemannForm E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH
  obtain ⟨hsec, hl2', hpt⟩ := GlobalTheory.T.theta_function_torus_l2_norm E H _ _ _ _ Hm T ψ θ Fd hT hhol.1
    (fun a z => by rw [hhol.2 a z, hchi a]) hFd
  rw [hl2] at hl2'
  have hR4 : 0 < R ^ 4 := pow_pos hR.pos 4

  have hval₀ := hf.tauValAt_evR hR (hA _ (U.un k x))
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨ev, hevL⟩ := GlobalTheory.ThetaConst.exists_isLevOf_geometric Xo c hval₀.dvd (U.un k x).x
  have hev : IsFullLev Xo (R ^ 4) (U.un k x).x ev := hevL.2.1
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.fullLinearLevel_eq_exp_periods_complexPoint E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) (U.un k x) hP hy (R ^ 4) hR4 ev hev
  have hR2 : Odd (R ^ 2) := hR.pow
  have htors : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := fun q => by rw [← pow_mul]; exact (ha q).2
  choose w hw using fun q =>
    ((GlobalTheory.nullValue_existsUnique_natural_linear GlobalTheory.firstFiveLaws.1 E H Dw l Xo c (R ^ 2) hR2).1 _ (U.un k x) (ev q)
      (htors q)).exists
  have hR0 : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR.pos.ne'
  let z : LatMod Dw (R ^ 4) → (Fin Uw.g → ℂ) := fun q =>
    ((R ^ 2 : ℕ) : ℂ) • ((R ^ 4 : ℕ) : ℂ)⁻¹ • Uw.Pm k x (a q)
  have hz : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) = ψ (Uw.Pm k x (a q)) := fun q => by
    rw [← map_smul]
    congr 1
    simp only [z, smul_smul]
    have : (R : ℂ) ^ 2 * (((R ^ 2 : ℕ) : ℂ) * ((R ^ 4 : ℕ) : ℂ)⁻¹) = 1 := by
      push_cast
      field_simp
    rw [this, one_smul]
  have hwn : ∀ q, ‖Formalism.L2.PjFree.toC (w q)‖ =
      Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ (z q))) := fun q => by
    rw [hpt]
    exact GlobalTheory.T.norm_nullVal_eq_norm_theta_alt E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr θ (U.un k x) hP hAH hy hfn (R ^ 2) hR2
      (ev q) _ (w q) (htors q) (ha q).1 (hw q)

  have hval : evR Xo c f (U.un k x) = ∏ b, w (xs b) := by
    rw [hval₀.unique hR (GlobalTheory.ThetaConst.tauValAt_self hevL hw), GlobalTheory.ThetaConst.tauExpr]
    simp
  obtain ⟨P, hq, hR0', hm'⟩ := hrun T hr (hdim m hm)
  rw [hval, ← hph, ← hq, ← hR0', ← hm']
  have hgen' : ∀ (g : Fin (2 * R ^ 4)) (j : Unit), ∀ v ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
      v = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • ψ (z (xs b))) + (R : ℂ) • y := fun g j => by
    simp only [hz]
    exact GlobalTheory.EtaAn.ArchPt.gen_mod hP hT R (fun b => a (xs b)) (hgen r _ hsp)
  have hmem : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) ∈ T.L := fun q => by
    rw [hz]
    exact (hT.2.2.2.1 _).2 ⟨_, rfl⟩
  have key : ∀ (r : ℕ), T.r = r → Fintype.card Unit ≤ R ^ (2 * I2.PT.f E * r ^ 2) →
      ∀ (w : Fin (2 * R ^ 4) → Unit → Fin r → ℂ) (a : Fin (2 * R ^ 4) → Unit → Fin r → I2.Vsp T.dim),
      (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) →
      (∀ g j, ∀ x ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
        x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) →
      (∀ g j b, ‖w g j b‖ =
        Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) fun _ => a g j b)) →
      ‖∏ g, ∑ j, ((fun _ : Unit => (1 : ℤ)) j : ℂ) * ∏ b, w g j b‖ ≤
        Real.exp (-((1 : ℕ) : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E r P.q P.m R 1)) := by
    intro r' hr' hJ' w' a'
    subst hr'
    exact GlobalTheory.T.norm_prod_sum_theta_le_exp_torus E T DF P R 1 1 h1R le_rfl _ hsec hl2' (Fin (2 * R ^ 4)) Unit
      (by simp) hJ' (fun _ => 1) w' a' (fun _ => by simp)
  have hJ : Fintype.card Unit ≤ R ^ (2 * I2.PT.f E * r ^ 2) := by
    rw [Fintype.card_unit]; exact Nat.one_le_pow _ _ hR.pos
  have := key r hr hJ (fun g j b => Formalism.L2.PjFree.toC (w (xs b))) (fun g j b => ψ (z (xs b)))
    (fun g j b => hmem _) hgen' (fun g j b => hwn _)
  have e : ‖Formalism.L2.PjFree.toC (∏ b, w (xs b))‖ = ∏ b, ‖Formalism.L2.PjFree.toC (w (xs b))‖ := by
    rw [← norm_prod]; rfl
  rw [e]
  simpa [Finset.prod_const, norm_pow] using this

end GlobalTheory.ThetaConst.ArchBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThetaConst

theorem normSq_thetaConst_le_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ), GoodEmb c σ → IsUnf U → ∀ R : ℕ, Odd R → 1 < R → ∀ (xs : Fin (Dw.p + Dw.q) → GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 E) (Set.range xs) = ⊤ → GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f → ∀ (DF q m : ℕ) (R0 : ℝ), GlobalTheory.EtaAn.RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ z : Σ k, Frame (U.X k).Ψ r, z.2 ∈ (U.X z.1).dom → homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ≤ Real.exp ((GlobalTheory.EtaAn.p16 E r q m R 1 - ReciprocityTheory.ChartRestriction.G.I2.phiFD (U.X z.1) (ReciprocityTheory.ChartRestriction.G.I2.th (E := E) q R0) z.2) / (R : ℝ) ^ 4) := by
  intro E _ _ _ H Dw l Xo c σ r U x hσ hU R hR h1R xs f hsp hf DF q m R0 hrun hm z hz
  obtain ⟨k, y⟩ := z
  have hr := hU.1
  subst hr
  have hA : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hsec1 : f ∈ sec Xo c 0 (Dw.p + Dw.q) := hf.mem_sec hR
  have hsec : f ^ 2 ∈ sec Xo c 0 (2 * (Dw.p + Dw.q)) := by
    have := sec_mul Xo c 0 0 _ _ hsec1 hsec1
    rw [add_zero, ← two_mul] at this
    rwa [sq]
  have hS : (U.X k).IsSec (laU U 0 (2 * (Dw.p + Dw.q)) k) (rdU U (f ^ 2) k) :=
    hU.2.2.2.2.1 0 _ ⟨fun _ => antitone_const, even_two_mul _⟩ (f ^ 2) hsec k
  obtain ⟨b, -, hb, hun, -, hphi, hp⟩ := GlobalTheory.T.exists_borel_orthonormal_flag_frame E _ (U.X k) y hz
  have hN : homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨k, y⟩ = ‖rdU U f k (rmul y b)‖ ^ 2 := by
    have h1 : lieFacZ Dw x (wtZ 0 (2 * (Dw.p + Dw.q))) = 1 := by simp [lieFacZ, wtZ]
    unfold homN ptN
    rw [modelWt_wtZ, h1, _root_.one_mul]
    show (U.X k).pnorm (laU U 0 (2 * (Dw.p + Dw.q)) k) (rdU U (f ^ 2) k) y = _
    rw [hp _ _ hS, sq f, GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul, sq]
  rw [hN, ← hphi _]
  have hv : rdU U f k (rmul y b) =
      Formalism.L2.PjFree.toC (evR Xo c f ((Formalism.L2.PjFree.Unf.ofPj U).un k ⟨rmul y b, hb⟩)) := dif_pos hb
  have key := ArchBound.norm_pow_le_at_unit_frame E H Dw l Xo c σ _ (Formalism.L2.PjFree.Unf.ofPj U) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) hA R hR h1R xs f hsp hf DF q m R0 hrun hm k ⟨rmul y b, hb⟩ hun
  rw [hv]
  have hn : R ^ 4 ≠ 0 := pow_ne_zero _ hR.pos.ne'
  have hR4 : (R : ℝ) ^ 4 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hR.pos.ne')
  rw [← pow_le_pow_iff_left₀ (sq_nonneg _) (Real.exp_pos _).le hn, ← pow_mul, ← Real.exp_nat_mul]
  refine le_of_le_of_eq key ?_
  congr 1
  push_cast
  rw [mul_div_cancel₀ _ hR4]
  show -((1 : ℝ)) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) (rmul y b) - p16 E (Dw.p + Dw.q) q m R 1) = _
  ring

end GlobalTheory.ThetaConst
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.NormIso

theorem prod_zpow_eq_one {K U : Type} [Fintype K] [CommGroup U] (ε : K → ℤ) (hε : ∑ k, ε k = 0) (c : U) :
    ∏ k, c ^ ε k = 1 := by
  have h : ∀ s : Finset K, ∏ k ∈ s, c ^ ε k = c ^ (∑ k ∈ s, ε k) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  rw [h, hε, zpow_zero]

theorem gm_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (ε : K → ℤ) (hε : ∑ k, ε k = 0)
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a a' : M.ι)
    (ha : r y ∈ LB.wchart M φ (fun _ => a)) (ha' : r y ∈ LB.wchart M φ (fun _ => a')) :
    gm r y (LB.wchart M φ (fun _ => a) ⊓ LB.wchart M φ (fun _ => a'))
      ((LB.LinComb M φ ε).g (fun _ => a) (fun _ => a')) = 1 :=
  (gm_linComb M φ ε r y _ _ ha ha').trans ((Finset.prod_congr rfl fun k _ => by rw [hq k]).trans
    (prod_zpow_eq_one ε hε (gm q y (M.U a ⊓ M.U a') (M.g a a'))))

theorem mem_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B))
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a : M.ι) (ha : q y ∈ M.U a) :
    r y ∈ LB.wchart M φ (fun _ => a) :=
  Set.mem_iInter.2 fun k => show (r ≫ φ k) y ∈ M.U a by rw [hq k]; exact ha

theorem exists_normalised {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (π : X' ⟶ S) (he : e ≫ π = 𝟙 S) (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w₀ : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a → q' (t z) ∈ M'.U b →
        gw w (t ≫ e) z (fun _ => a) (fun _ => b) = 1 := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (mem_const M φ (e ≫ F) q hq x a ha), mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w₀.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w₀).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  let c : Γ(X', ⊤)ˣ := res (fun _ _ => trivial : (⊤ : X'.Opens) ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ u⁻¹)
  refine ⟨DVR.scaleGen c w₀, DVR.scaleGen_isGen c w₀ hw, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  have h₁ : gm (t ≫ e) z (C (a, b)) (res le_top c) = (gm t z ⊤ u)⁻¹ := by
    refine (gm_res (t ≫ e) z le_top hm c).trans ((gm_res (t ≫ e) z (V := ⊤) _ trivial _).trans
      ((gm_pull (t ≫ e) π z ⊤ trivial _).trans ?_))
    rw [Category.assoc, he, Category.comp_id, map_inv]
  have h₂ : gm (t ≫ e) z (C (a, b)) (w₀.s (fun _ _ => a, fun _ => b)) = gm t z ⊤ u :=
    (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
      (gm_res t z le_top hm u))
  exact (map_mul (gm (t ≫ e) z (C (a, b))) _ _).trans ((congrArg₂ (· * ·) h₁ h₂).trans (inv_mul_cancel _))

theorem lift_one_psum {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) 1 ≫ psum G (x2 G) I = 1 := by
  have h : (fun k => lift (1 : T ⟶ G) 1 ≫ x2 G k) = fun _ => 1 := by
    funext k
    fin_cases k
    · exact lift_fst _ _
    · exact lift_snd _ _
  rw [comp_psum, h, psum_one]

theorem origin_square {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {β : G'.left ⟶ G.left} {β₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (T : Over S') :
    (lift (1 : T ⟶ G') 1).left ≫ β₂ = (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left := by
  have h₁ : (1 : T ⟶ G').left ≫ β = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  have a₁ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.1, ← Category.assoc, ← Over.comp_left, lift_fst, h₁]
  have a₂ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.2, ← Category.assoc, ← Over.comp_left, lift_snd, h₁]
  have b₁ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_fst (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  have b₂ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_snd (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  exact pullback.hom_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)

theorem exists_lamVal_origin {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} {β₂ : (G2 G').left ⟶ (G2 G).left} {M : LB G.left}
    {M' : LB G'.left} (hM : M.IsLB) (hM' : M'.IsLB) (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (H : LBIso (abelian₂ G' M') ((abelian₂ G M).pull β₂)) :
    ∃ w : LB.Iso (abelian₂ G' M') ((abelian₂ G M).pull β₂), w.IsGen ∧ ∀ (T : Over S') z J J', Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J J' = 1 := by
  obtain ⟨w₀, hw₀⟩ := H
  let e : (𝟙_ (Over S')).left ⟶ (G2 G').left := (lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
  let q : (𝟙_ (Over S')).left ⟶ G.left := (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left
  let q' : (𝟙_ (Over S')).left ⟶ G'.left := (1 : 𝟙_ (Over S') ⟶ G').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum G (x2 G) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum G (x2 G) I.down).left) (origin_square h hs (𝟙_ (Over S')))).trans
      (congrArg (fun z => z.left) (lift_one_psum G (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum G' (x2 G') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (lift_one_psum G' (T := 𝟙_ (Over S')) I.down)
  obtain ⟨w, hw, hv⟩ := exists_normalised M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum G (x2 G) I.down).left) (fun I => (psum G' (x2 G') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e (toUnit (G2 G')).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S') ⟶ G') 1 ≫ toUnit (G2 G')) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ G') (1 : T ⟶ G')).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 G').left) (j : (abelian₂ G M).ι) (k : (abelian₂ G' M').ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum G (x2 G) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum G' (x2 G') I.down).left)) = k →
      lamVal w p z J J' = gw (L := abelian₂ G M) (L' := abelian₂ G' M') w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

theorem exists_normalised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → letI := P.isAb.comm; ∃ w : LB.Iso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂), w.IsGen ∧ ∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good P.L z J' → lamVal w (lift (1 : T ⟶ P.A) (1 : T ⟶ P.A)).left z J J' = 1 :=
  fun _ _ _ _ _ _ Q _ P _ _ hpb hs H =>
    letI := P.isAb.comm
    exists_lamVal_origin Q.M.isLB P.isLB hpb hs H

end GlobalTheory.PolDeg.NormIso
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section Factor

open GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_tau_four (D : DegPre R) (a b : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val t r z J = val (D.tau a b) r z J := by
  refine exists_gen D.P.isLB ?_ (D.tau a b) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (D.psi_gen _))) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (D.psi_gen _)))
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  intro U _ h
  have e : toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
    rw [D.c_add]; exact MonObj.comp_mul _ _ _
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, lamPts, negε, ← e]
  simp [eSec, Hom.one_def]

end Factor
end GlobalTheory.Mum
end
end

section

set_option autoImplicit false


noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem conj_embK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  show conjEmb τ ((H.bar z : 𝓞 E) : E) = τ (z : E)
  rw [H.bar_eq]
  simp [conjEmb, IsCMField.complexEmbedding_complexConj]

theorem ksExist : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type)
    [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q →
    GlobalTheory.FlagTan.IsTanX y x' → ∃ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
      GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ hx
  have P := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G x'
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G y.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating P Xo hπ
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P Xo hπ a ha hpol
  have hK := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field P hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  have hL := (P.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P y hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → K,
      ∃ w, IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ =>
    GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, conj_embK]) a₀
  choose cf w hw using hrow
  refine ⟨fun k => cf k.1 k.2.1 k.2.2, A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub,
    hb, hπ, hπ', rfl, hpol, hu, fun σ k => hbl ⟨σ, k⟩, fun τ a₀ => ⟨w τ a₀, (hw τ a₀).1, (hw τ a₀).2⟩⟩

end GlobalTheory.KSExist
end
end
