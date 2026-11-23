module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle061
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle025
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_flagCellChart_over_modelChart : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∀ (M : MChart Y) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n), ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), (∀ a, f a ∈ W) → (∀ τ i j, u τ i j ∈ W) → (∀ τ, InCell (ix τ) (u τ)) → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → ∃ j, (P j).Catches W y := by
  first | exact @GlobalTheory.Reg.exists_pChart_of_cell | exact GlobalTheory.Reg.exists_pChart_of_cell | (intros; apply GlobalTheory.Reg.exists_pChart_of_cell <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.framedPoint_integral_integralCell_anyModel : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  first | exact @GlobalTheory.Reg.tie_integral_of_any_model | exact GlobalTheory.Reg.tie_integral_of_any_model | (intros; apply GlobalTheory.Reg.tie_integral_of_any_model <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.AdaptedPeriods



theorem exists_adapted (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ)
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (y : FrPt Xo c (CAt σ)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P) (hy : F.u k P = y.x) :
    ∃ (w : Fin g → Fin g → ℂ) (V : Matrix (Fin g) (Fin g) ℂ) (P' : (F.Di k).La →+ (Fin g → ℂ)),
      (∀ j, IsDerivAt0 (fun z => (F.ex k P z).left) (w j) (y.u (e j).1 (e j).2)) ∧
      (∀ j, V *ᵥ w j = Pi.single j 1) ∧ (∀ a, P' a = V *ᵥ P a) ∧
      IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P' ∧ y.x = F.u k P' ∧
      ∀ τ (i : Fin (Dw.mult τ)),
        IsDerivAt0 (fun z => (F.ex k P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i) := by
  classical
  obtain ⟨x, hxs, u, htan, heig, hbas, s, hgen⟩ := y
  dsimp only at hy ⊢
  subst hy
  have hT := GlobalTheory.isDerivAt0_ex_isTanAt _ _ _ _ _ _ _ _ F k P hP
  have hw0 : ∀ p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ∃ w, IsDerivAt0 (fun z => (F.ex k P z).left) w (u p.1 p.2) :=
    fun p => (hT.2.2 _ (htan p.1 p.2)).exists
  choose wp hwp using hw0
  have hblk : ∀ j, ∃ a : Fin (Dw.mult (e j).1) → ℂ,
      ∑ i, a i • wp (e (e.symm ⟨(e j).1, i⟩)) = Pi.single j 1 := by
    intro j
    obtain ⟨d, hd, -⟩ := hT.2.1 (Pi.single j 1)
    have hdt := hT.1 _ _ hd
    have hde := (GlobalTheory.isEigAt_iff_of_isDerivAt0 _ _ _ _ _ _ _ _ _ F k P hP (Pi.single j 1) d (e j).1 hd).2 (by
      intro j' hj'
      rw [Pi.single_apply] at hj'
      split_ifs at hj' with hjj
      · rw [hjj]
      · exact absurd rfl hj')
    obtain ⟨a, ha, -⟩ := hbas (e j).1 d hdt hde
    refine ⟨a, ?_⟩
    have hc := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 _ _ _ _ _ _ _ _ F k P hP (Dw.mult (e j).1) (u (e j).1)
      (fun i => wp (e (e.symm ⟨(e j).1, i⟩))) (fun i => by simpa using hwp ⟨(e j).1, i⟩) a d).1 ha
    exact (hT.2.2 d hdt).unique hc hd
  obtain ⟨V, hVdet, hVblk, hVw⟩ := GlobalTheory.CoverFrame.exists_inverse_block e (fun j => wp (e j)) hblk
  obtain ⟨P', hP', hP'V⟩ := GlobalTheory.PeriodLin.exists_period_mulVec _ _ _ _ _ P V hP hVdet
    (fun j j' h => congrArg (relab c σ) (hVblk j j' h))
  have hS : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (s : Y ≃ₗ[ℤ] Y) (n M : ℕ),
      0 < n → s ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, s y = y + M • z) → s = 1 := by
    intro Y _ _ _ s n M hn hs hM h
    have h1 : (s : Module.End ℤ Y) ^ n = 1 := by
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun t : Y ≃ₗ[ℤ] Y => t v) hs
      simp only [LinearEquiv.coe_pow] at hv
      first
        | rw [Module.End.coe_pow]
        | rw [LinearMap.coe_pow]
      simpa using hv
    have h2 := GlobalTheory.end_eq_one_of_pow_eq_one_of_congr Y (s : Module.End ℤ Y) n M hn h1 hM h
    exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun h2 v
  obtain ⟨-, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group hS _ _ _ _ _ _ _ _ F k P P'
    (LinearEquiv.refl _ _) V hP hP' (fun a b => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩)
    (fun a => hP'V a)
  have hD := GlobalTheory.ExpChain.isDerivAt0_ex_iff _ _ _ _ _ _ _ _ F k P hP k P' (Matrix.mulVecLin V) hP'
    (fun z => hex z)
  refine ⟨fun j => wp (e j), V, P', fun j => hwp (e j), hVw, hP'V, hP', hu, ?_⟩
  intro τ i
  have h3 : V *ᵥ wp ⟨τ, i⟩ = Pi.single (e.symm ⟨τ, i⟩) 1 := by
    simpa using hVw (e.symm ⟨τ, i⟩)
  rw [← h3]
  exact (hD (wp ⟨τ, i⟩) (u τ i)).1 (hwp ⟨τ, i⟩)



theorem exists_holPeriods_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (k : Fin F.n) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B' P ∧ ∀ b ∈ B', (y b).x = F.u k (P b) ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (P b) z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((y b).u τ i) := by
  intro E _ _ _ H Dw l Xo c σ g e F A _ _ yA m B φ y hB hφ hmap b₀ hb₀
  have hpts : IsHolTo B (fun b => (y b).x) := by
    have h1 := GlobalTheory.ThetaValueCont.isHolTo_spMap hB (fun b => ((φ b).toRingHom : A →+* ℂ)) (fun a => hφ a)
    have h2 := GlobalTheory.LocLift.isHolTo_comp_hom h1 yA.x
    exact GlobalTheory.LocLift.isHolTo_congr h2 (fun b hb => (hmap b hb).1)
  obtain ⟨B1, k, P0, hB1, hb1, hB1B, hP0, hu0⟩ :=
    F.24 m B (fun b => (y b).x) hB (fun b _ => (y b).2) hpts b₀ hb₀
  have hadp := fun b (hb : b ∈ B1) =>
    exists_adapted E H Dw l Xo c σ g e F (y b) k (P0 b) (hP0.1 b hb) (hu0 b hb)
  choose! W V P' hW hVW hP'V hP' hux hder using hadp
  have hWd : ∀ b' ∈ B1, ∀ j, DifferentiableAt ℂ (fun b => W b j) b' := by
    intro b' hb' j
    refine GlobalTheory.HolFrameMatrix.differentiableAt_coord F k (yA.u (e j).1 (e j).2)
      (fun b => ((φ b).toRingHom : A →+* ℂ)) hB1 hP0 (fun b => W b j) ?_ hb' ?_
    · intro b hb
      have h1 := hW b hb j
      rw [(hmap b (hB1B hb)).2.1, GlobalTheory.HolFrameMatrix.dualMap_eq] at h1
      exact h1
    · intro t
      exact (hφ t).differentiableAt (hB.mem_nhds (hB1B hb'))
  have hVW1 : ∀ b ∈ B1, V b * Matrix.of (fun i j => W b j i) = 1 := by
    intro b hb
    ext i j
    have h := congrFun (hVW b hb j) i
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [show (∑ x, V b i x * W b j x) = (V b *ᵥ W b j) i from rfl, h, Pi.single_apply, Matrix.one_apply]
  have hVd : ∀ b' ∈ B1, ∀ i j, DifferentiableAt ℂ (fun b => V b i j) b' := by
    intro b' hb' i j
    exact GlobalTheory.HolFrameMatrix.differentiableAt_of_mul_eq_one V (fun b => Matrix.of fun i j => W b j i) b'
      (fun i j => differentiableAt_pi.1 (hWd b' hb' j) i)
      (Filter.eventually_of_mem (hB1.mem_nhds hb') hVW1) i j
  have hPd : ∀ b' ∈ B1, ∀ a, DifferentiableAt ℂ (fun b => P0 b a) b' :=
    fun b' hb' a => (hP0.2 a).differentiableAt (hB1.mem_nhds hb')
  refine ⟨B1, k, P', hB1, hb1, hB1B, ⟨fun b hb => hP' b hb, fun a => ?_⟩, fun b hb => ⟨hux b hb, hder b hb⟩⟩
  intro b' hb'
  have hd : DifferentiableAt ℂ (fun b => V b *ᵥ P0 b a) b' := by
    rw [differentiableAt_pi]
    intro i
    show DifferentiableAt ℂ (fun b => ∑ j, V b i j * P0 b a j) b'
    have hv : ∀ j, DifferentiableAt ℂ (fun b => V b i j) b' := hVd b' hb' i
    have hp : ∀ j, DifferentiableAt ℂ (fun b => P0 b a j) b' := fun j => differentiableAt_pi.1 (hPd b' hb' a) j
    first
      | exact DifferentiableAt.fun_sum fun j _ => (hv j).mul (hp j)
      | fun_prop
      | (convert DifferentiableAt.sum (u := Finset.univ) (fun j _ => (hv j).mul (hp j)) using 1
         ext b
         simp)
  exact hd.differentiableWithinAt.congr (fun b hb => hP'V b hb a) (hP'V b' hb' a)

end GlobalTheory.AdaptedPeriods
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

theorem _root_.GlobalTheory.T.gauss_valuation_density_generation_localisation : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (ψ : Kp X la N →+* U), (∀ a : Op X la N, v (ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ a)) ≤ 1) → v (ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (unifO X la N))) < 1 → (∀ (f : B.KO →+* U), (∀ a, f a = ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) → ∀ p : MvPolynomial (Idx D j N) B.KO, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) → v (MvPolynomial.eval₂ f (fun q => ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N q))) p) = 1) ∧ (∀ (c : X.Ol la) (γ : WithZero (Multiplicative ℤ)), γ ≠ 0 → ∃ a : B.KO, v (ψ (algebraMap (X.Ol la) (Kp X la N) c) - ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) < γ) ∧ ∀ S : Subfield U, (∀ c : X.Ol la, ψ (algebraMap (X.Ol la) (Kp X la N) c) ∈ S) → (∀ q, ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N q)) ∈ S) → ∀ c : Kp X la N, ψ c ∈ S := by
  first | exact @GlobalTheory.GaussVal.gauss_dense_gen | exact GlobalTheory.GaussVal.gauss_dense_gen | (intros; apply GlobalTheory.GaussVal.gauss_dense_gen <;> assumption)
end
