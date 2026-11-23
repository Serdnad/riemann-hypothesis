module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InjectiveOfKerCountable
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemSSOfEqSumThP
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RdUEqConstMulClsSum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle064
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle070
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

theorem isThClsD_mem_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → l.A = 1 → d.IsLev → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → LastPos Dw a → LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f → f ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  intro hci E _ _ _ H Dw l Xo c n d r U hr1 hU hA hlev hA₂ hnab hunit Cl _ w La Nc gam vol ep Vs _ _ io xs a hD hL
    hLat hP f hsec hcls
  refine (Formalism.L2.PjFree.mem_cusp Xo c U a n f).2
    ⟨hsec, fun σ hσ => Formalism.L2.PjFree.holCusp_mem_holSub _ _ fun k => ?_⟩
  have hu := hU σ hσ
  obtain ⟨W⟩ := nonempty_uw hu
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hσ₂ : GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) := by
    have h1 : d.eF (IntermediateField.inclusion c.le (baseKA l).ρ) =
        IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ := Subtype.ext rfl
    change algebraMap d.c₂.F ℂ (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = _
    rw [← h1, halg]
    exact hσ
  have hn : Even n := hD.2
  have hsd := (uw_lattice E H Dw l Xo c σ r (U σ) hσ hu hr1 W k).2.1
  obtain ⟨Dc, hDe, hk⟩ := exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hu.1 (hu.2.1 k).1
    (hu.2.1 k).2 hsd hD
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ShortRead.halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hN : ∀ j, 0 < Nc j := fun j => (hLat j).2.2.1.pos
  have hΛ : ∀ j, (La j).La ∈ Vset E n d.l₂.M := fun j =>
    (GenLatCmp.genLat_vset E n (La j).La).2.1 _ (Nc j) hM (hLat j).1 (hLat j).2.1 (hLat j).2.2
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset n 1)).1

  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.frames_isConnected E r ((U σ).X k)).nonempty
  obtain ⟨b, -, hx, hux⟩ := exists_unitFr_rmul ((U σ).X k) hx₁
  obtain ⟨A, hAm, -⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx⟩ hux
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC (U σ) k ⟨_, hx⟩)
  obtain ⟨A₂', -, mk₂, hmk₂, hA₂', hover⟩ := Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e _ _
    _ A Dc.sympl hx hsd y₂ hy₂ _ hAm
  choose Y hY using fun j => (DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hsd hmk₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n (Nc j) (hN j)
  obtain ⟨cv, hcv, hcvI⟩ := GlobalTheory.ClsVal.exists_cvIs E H Dw l Xo c n d hσ₂ hA₂ hlev.2.2.2.2.2.2.2.1 hunit r W.g ((U σ).X k)
    Dc.bas Dc.idx W.e _ hr1 Dc.sympl hsd
  obtain ⟨C, -, -, hC⟩ := GlobalTheory.ClsVal.rdU_eq_const_mul_clsSum hci E H Dw l Xo c σ r (U σ) hσ hu hr1 hA W k n a hD Dc hDe v hv
  have hrd := hC d halg hlev hA₂ hnab cv hcv hcvI mk₂ hmk₂ hover
    (fun _ => Or.inr ⟨⟨_, hx⟩, y₂, A₂', hy₂, hA₂'⟩) Cl w La Nc gam vol ep Vs io xs hLat hP Y hY f hsec hcls
  have hG := fun j => ShortRead.sb_gphi Dc.idx Dc.sympl hn hw hw' hsd (hΛ j) hv.1 (fun q => σ (w j q)) (Y j)
  have hwt : Formalism.L2.PjFree.laU (U σ) a n k = wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n := Dc.wt_eq.symm
  have hs := hu.2.2.2.2.1 a n hD f hsec k
  rw [hwt] at hs ⊢
  refine CuspSum.mem_SS_of_eq_sum_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn Dc.k Dc.k' ?_ Cl
    _ _ (fun j => ShortRead.sb_smul (C * cv mk₂ * σ (vol * ((gam j : c.F))⁻¹ * ep j *
      ((((La j).mIdx (Nc j) r : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : c.F))⁻¹ *
        ((La j).zCard (Nc j) r : c.F)))) (hG j))
    (fun j => Dc.mem _ (hP j)) _ (fun x hx => ?_) hs.2.2
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk hL h0)
  · rw [hrd x hx, clsSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ShortRead.theta_smul₂ Dc.hr Dc.idx Dc.sympl hn (hG j) (Dc.mem _ (hP j)) hx, mul_assoc (C * cv mk₂)]

end GlobalTheory.ClsVal
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict



theorem spanAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j), LastPos (T.Q.Dw j) (wtA ka) → 8 * D.R.f * D.R.r + 4 ≤ ka.n → SpanAt ((recX h) j h1 h2) ka := by
  intro hC D T h hSh hG hb hU j h1 h2 ka hL hn
  have hj : InR D j := ⟨h1, h2⟩
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.spanAt_rec h j h1 h2 ka (GlobalTheory.T.cuspForm_frame_readings_linearIndependent D T hM j hj _ _) _
    (GlobalTheory.T.holomorphicCuspForms_frames_le_span_shortThetaReadings hC D T hM hSh hG hb hU j hj ka hn) ?_
  rintro _ ⟨x, hx, rfl⟩

  have hxC : x ∈ T.C j ka :=
    hSh.shCusp j hj (wtA ka) ka.n (dom_wtA ka) hL (dom_wtA ka) hL hx
  have hxR : x ∈ cutR T.C j ka := by
    show x ∈ T.C j ka ⊓ ⨅ (_ : ¬InR D j), ⊥
    exact Submodule.mem_inf.2 ⟨hxC, Submodule.mem_iInf _ |>.2 fun hn' => absurd hj hn'⟩
  apply Submodule.subset_span
  refine ⟨⟨x, hxR⟩, ?_, rfl⟩
  exact (Submodule.subset_span hx : x ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j ka))

end GlobalTheory.Dict
end
