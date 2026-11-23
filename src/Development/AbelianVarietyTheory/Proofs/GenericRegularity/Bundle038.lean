module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle079
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle045
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpen
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle034
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle036
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle030
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

theorem fnConj_valAtCx_nrmC_eq_ptNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → FnConj Xo c fn yP ∧ ValAtCx h yP ∧ ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) a n, ∀ f ∈ sec Xo c a n, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
  intro E _ _ _ H Dw l Xo c r U _ xR fn _ hpin h yP hcb
  have hWD := GlobalTheory.TransferCompare.evalWD_framed Xo c
  have hgt : GenFromTest Xo c h := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).2 h
  have hcx : ValAtCx h yP := by
    intro Z P a n f hf
    have hT1 := hgt Z
    have hm := hcb Z P
    have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (yP Z P) := by
      obtain ⟨p, ψ, y', hy'⟩ := hT1
      exact ⟨p, (PAlg P).comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ (PAlg P) y' _ _ hy' hm⟩
    have key : evR Xo c f (yP Z P) = PAlg P (evR Xo c f (genFr h Z)) := by
      unfold evR evalAt
      rw [dite_eq_left hT2, dite_eq_left hT1]
      exact hWD f hf.1 _ _ _ _ _ _ _ (yP Z P) hT2.choose_spec.choose_spec.choose_spec
        (frMap_trans (Xo := Xo) (c := c) _ _ _ _ (PAlg P) _ _ _ hT1.choose_spec.choose_spec.choose_spec hm)
    rw [key]
    rfl
  refine ⟨?_, hcx, ?_⟩
  · intro Z G x P
    have hm : FrMap (conjAlg (sgOf P)) (yP Z P) (yP Z ((starRingEnd ℂ).comp P)) :=
      frMap_cancel (Xo := Xo) (c := c) _ _ _ (PAlg P) (conjAlg (sgOf P)) (genFr h Z) _ _ (hcb Z P)
        (hcb Z ((starRingEnd ℂ).comp P))
    unfold nrmC
    congr 1
    · exact Complex.norm_conj _
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact congrArg (fun t : ℝ => t ^ (-exZ Dw G i)) (hpin.2 (sgOf P) (yP Z P) _ hm i)
  · intro Z P a n f hf
    show nrmC fn (yP Z) (wtZ a n) (AddMonoidAlgebra.single (wtZ a n) (evC h Z f)) P = _
    rw [nrmC_single, hcx Z P a n f hf]
    unfold ptNorm
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by cases i <;> rfl
    rw [e, zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.FrameNorm
end

section

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

attribute [local instance 1100] Subalgebra.algebra in
theorem exists_countable_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (h : GenFrEx Xo c), ∃ (ι : Type) (_ : Countable ι) (C : ι → FChart h),
      ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
        ∃ (i : ι) (ψ : (C i).R →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
          FrMap ψ (C i).y z ∧ FrBor t z y := by
  intro E _ _ _ H Dw l Xo c h
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hBC : FrBC Xo c := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1.bc
  choose A iA dA aA j yA hj hp hjs hsm hyA using
    GlobalTheory.LocalFrame.exists_integral_chart_frame hS E H Dw l Xo c
  haveI : IsNoetherian (Xo.XF c) := CompFin.isNoetherian_XF Xo c
  obtain ⟨T, -, hT⟩ := (isCompact_univ (X := Xo.XF c)).elim_nhds_subcover (fun p => Set.range (j p))
    (fun p _ => by
      haveI := hj p
      exact (IsOpenImmersion.isOpen_range (j p)).mem_nhds (hp p))
  choose C hC using fun (p : Xo.XF c) (σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) =>
    GlobalTheory.Reg.exists_fChart_cell E H Dw l Xo c hBC h (A p) (j p) (yA p) (hj p) (hjs p) (hsm p) (hyA p) σ
  refine ⟨T × (∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))), inferInstance, fun i => C i.1 i.2, ?_⟩
  intro L _ _ y
  have hcond : y.x ≫ Xo.s =
      spMap (algebraMap c.F L) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.x_over, spMap_comp_ring]
    rfl
  let q : Sp L ⟶ Xo.XF c := pullback.lift y.x (spMap (algebraMap c.F L)) hcond
  obtain ⟨p, hpT, hq⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ (q (IsLocalRing.closedPoint L))))
  haveI := hj p
  obtain ⟨f, hf⟩ := exists_algHom_of_mem_range (pullback.snd _ _) (j p) (hjs p) q (pullback.lift_snd _ _ _) hq
  obtain ⟨z₀, hz₀⟩ := hBC (A p) L f (yA p)
  have hx : y.x = z₀.x := by
    rw [hz₀.1, hyA, ← Category.assoc, hf]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨g, ⟨hgu, hg⟩, -⟩ := (GlobalTheory.T.isTriangularReframe_exists_and_unique E H Dw l Xo c L z₀).2 y hx
  choose σ u b h0 h1 hb e using fun τ => exists_perm_lower_upper (g τ) (hgu τ)
  let x : FlagVar Dw → L := fun v => u v.1 (σ v.1 v.2.1.2) v.2.1.1
  have hu : ∀ τ, (lowM x τ).submatrix (σ τ).symm id = u τ := by
    intro τ
    ext i k
    obtain ⟨i, rfl⟩ := (σ τ).surjective i
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, id, lowM]
    split_ifs with h₁ h₂
    · rfl
    · rw [h₂, h1]
    · exact (h0 τ i k (lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm h₂))).symm
  refine ⟨(⟨p, hpT⟩, σ), hC p σ L f z₀ y x b hz₀ hb ?_⟩
  have : (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) = g := funext fun τ => by rw [hu τ, ← e τ]
  rw [this]
  exact hg

end GlobalTheory.Reg
end
end

section

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem comp_unique_of_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp) (Z Z' : Comp Xo c), ((U.X k).dom).Nonempty → (∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n, evC h Z f = 0 ↔ ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → (∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n, evC h Z' f = 0 ↔ ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → Z = Z' := by
  intro E _ _ _ H Dw l Xo c σ r U _ _ h k Z Z' _ hZ hZ'
  by_contra hne
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨χ, hχ, -, h1, h0⟩ := GlobalTheory.Reg.exists_idem_section E H Dw l Xo c hL h (hA h) Z
  have hd : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩
  have h2 := (hZ 0 0 hd χ hχ).2 ((hZ' 0 0 hd χ hχ).1 (h0 Z' (Ne.symm hne)))
  rw [h1] at h2
  exact one_ne_zero h2

end GlobalTheory.Reg
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem cusp_eq_zero_of_generic_values {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hG : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (g : Rul Xo c) (hg : g ∈ cusp Xo c U a n) (h0 : ∀ Z, evC hG Z g = 0) : g = 0 := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  exact sec_eq_zero_of_generic_values E H Dw l Xo c hL hG (hA hG) a n g (cusp_le_sec Xo c U a n hg) h0




theorem genValInj_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), GenValInjSt h j hG := by
  intro D T h j _ hG w g h0
  have hg : (g : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w g.2
  exact Subtype.ext (cusp_eq_zero_of_generic_values (T.Q.Xo j) T.Q.c (T.U j) hG (wtA w) w.n _ hg h0)

end GlobalTheory.Reg
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg




theorem compSplit_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hG : GenFrEx (T.Q.Xo j) T.Q.c), CompSplitSt h j hG := by
  intro D T h j hj hG Z w g
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hg : (g : T.R j) ∈ T.C j w := cutR_le T.C j w g.2
  obtain ⟨g', hg', h1, h0⟩ := exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n (g : T.R j) hg
  have hm : g' ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]; exact hg'
  exact ⟨⟨g', hm⟩, h1, h0⟩

end GlobalTheory.Reg
end
