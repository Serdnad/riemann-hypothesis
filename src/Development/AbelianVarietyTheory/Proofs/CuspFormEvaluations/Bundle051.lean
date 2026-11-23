module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqGeAndPhiEqZeroDefinite
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphism
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle038
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle050
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

set_option autoImplicit false

namespace GlobalTheory.FieldBC

theorem totalDegree_map_inj {σ R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (hf : Function.Injective f) (P : MvPolynomial σ R) :
    (MvPolynomial.map f P).totalDegree = P.totalDegree := by
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective P hf]

theorem polyNab_fieldBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (nab : NabV Xo c) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (k : ℤ) (F : Fin n → LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), (MvPolynomial.map (incF c c' hle) P).totalDegree = P.totalDegree ∧ ∑ m ∈ (MvPolynomial.map (incF c c' hle) P).support, algebraMap c'.F S ((MvPolynomial.map (incF c c' hle) P).coeff m) * ∏ b, nabBC hle nab y k (F b) (colOf m b) = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab (y.res hle h) k (F b) (colOf m b) := by
  intro E _ _ _ H Dw l Xo c c' hle nab n P S _ inst _ h y k F
  have hinj : Function.Injective (incF c c' hle) := (incF c c' hle).injective
  refine ⟨totalDegree_map_inj _ hinj P, ?_⟩
  have e : inst = GlobalTheory.FieldBC.resAlg hle S := Algebra.algebra_ext _ _ (fun a => (h a).symm)
  subst e
  rw [MvPolynomial.support_map_of_injective P hinj]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_map]
  rfl

end GlobalTheory.FieldBC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_analytic_biextension_chart_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  first | exact @GlobalTheory.AnVal.exists_analytic_chart | exact GlobalTheory.AnVal.exists_analytic_chart | (intros; apply GlobalTheory.AnVal.exists_analytic_chart <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem phiFD_eq_zero_at_last_index : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), j = D.R.m → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp), ∀ x ∈ ((T.U j σ).X k).dom, I2.phiFD ((T.U j σ).X k) (I2.th (E := D.host.E) q R0) x = 0 := by
  intro D T h j hj hjm DF q R0 hrun σ hσ k x hx
  have hu := h.unf j hj σ hσ
  have hq0 : (T.Q.Dw j).q = 0 := by
    rw [(h.pins.2.2.2 j hj).2.1, hjm]
    exact Nat.sub_self _
  have hp0 : ((T.U j σ).X k).p0 = 0 := ((hu.2.1 k).1).trans hq0
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hu k ⟨x, hx⟩
  have hint : ∀ u ∈ ((T.U j σ).X k).Λ, ∀ v ∈ ((T.U j σ).X k).Λ, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (((T.U j σ).X k).ξ0 * FD.herm ((T.U j σ).X k).Gm u v) = z := by
    intro u hu' v hv'
    have hEF := W.isom k ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)
    simp only [LinearEquiv.apply_symm_apply] at hEF
    refine ⟨-((W.F.Di (W.ik k)).EF ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)), ?_⟩
    rw [Int.cast_neg, hEF, neg_mul, map_neg, neg_neg]
  obtain ⟨A, -⟩ := GlobalTheory.T.exists_torusWithSign_uniformisationFrame _ _ _ _ _ _ _ _ (T.U j σ) k ⟨x, hx⟩ W
  obtain ⟨τ0⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((T.U j σ).X k).Ψ := by
    by_cases h1 : τ0 ∈ ((T.U j σ).X k).Ψ
    · exact ⟨τ0, h1⟩
    · refine ⟨NumberField.ComplexEmbedding.conjugate τ0, ?_⟩
      rw [((T.U j σ).X k).cmType]
      simpa using h1
  have hpos := A.dim_pos ⟨τ, hτ⟩
  have hneg := A.dim_neg ⟨τ, hτ⟩
  have hsum := A.T.dim_conj τ
  have hr : A.T.r = D.R.r := by
    simp only at hpos hneg
    omega
  obtain ⟨P, hPq, hPR, -⟩ := hrun A.T hr ⟨τ, by simp only at hpos; omega⟩
  have hr0 : 0 < D.R.r := by
    have h2m := D.R.two_le_m
    show 0 < D.R.k + D.R.m - 1
    omega
  refine (GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero D.host.E D.R.r ((T.U j σ).X k) hr0 hp0 hint x hx).2 q R0
    ?_ ?_ ?_
  · have h16 := P.hrd
    linarith
  · have h1q := P.hq
    omega
  · have hb := P.C2
    rwa [hPq, hPR] at hb

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.harmonic_values_invariant_universal_endomorphism : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y y' : FrPt Xo c S) (pm : Gx y.x ⟶ Gx y'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)), y'.x = y.x ≫ ρ → pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left → pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ → CubIso ν w → (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, (∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx y.x).Opens) (h₀ : W ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j))) (h₁ : W ≤ pm ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)).U (fun _ => i)) (h₂ : W ≤ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)).U (fun _ => j)), (pm.appLE ((LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)).U (fun _ => i)) W h₁).hom ((F' b).f (fun _ => i)) = ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) W h₀).hom (Units.val (w.s ((fun _ => i), j))) ^ (N ^ 2) * ((Gx y.x).presheaf.map (homOfLE h₂).op).hom ((F b).f (fun _ => j)))) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  first | exact @GlobalTheory.ChartPush.nab_harmonic_invariant | exact GlobalTheory.ChartPush.nab_harmonic_invariant | (intros; apply GlobalTheory.ChartPush.nab_harmonic_invariant <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TranslExist

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

private theorem mem_wchart_lemma {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (y : Y) : y ∈ L.wchart φ j ↔ ∀ k, φ k y ∈ L.U (j k) := by
  unfold LB.wchart
  show y ∈ (⋂ k, (φ k) ⁻¹' (L.U (j k) : Set X)) ↔ _
  simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]

theorem twist_congr (hL : L.IsLB) {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (h : ∀ y J, Good L y J → val α (𝟙 _) y J = val α' (𝟙 _) y J) {s : LB.Sec (LPow A L b T)}
    {s' s'' : LB.Sec (LPow A L a T)} (h' : IsTwistPull A L ψ m hm a b α s s')
    (h'' : IsTwistPull A L ψ m hm a b α' s s'') : s' = s'' := by
  unfold IsTwistPull at h' h''
  have hf : ∀ i, s'.f i = s''.f i := by
    intro i
    obtain ⟨i0, rfl⟩ : ∃ i0 : L.ι, i = (fun _ : Fin 1 => i0) := ⟨i 0, funext fun k => by fin_cases k; rfl⟩
    apply fn_ext
    intro x hx
    have hx0 : (snd T A).left x ∈ L.U i0 :=
      (mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) x).mp hx 0
    obtain ⟨j1, hj1, hj1'⟩ : ∃ j1 : L.ι, m.left x ∈ L.U j1 ∧ (m.left = (snd T A).left → j1 = i0) := by
      by_cases e : m.left = (snd T A).left
      · exact ⟨i0, by rw [e]; exact hx0, fun _ => rfl⟩
      · have hc : m.left x ∈ (⨆ k, L.U k) := by rw [hL.cover]; trivial
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
        exact ⟨k, hk, fun h => absurd h e⟩
    let j : Fin 2 → L.ι := ![i0, j1]
    have hxW : x ∈ L.wchart ![(snd T A).left, m.left] j := by
      rw [mem_wchart_lemma]
      intro k
      fin_cases k
      · exact hx0
      · exact hj1
    obtain ⟨J, hJ, hJk⟩ := exists_good L hL x ![(snd T A).left, m.left] j (by
      intro p q hpq
      fin_cases p <;> fin_cases q
      · rfl
      · exact (hj1' hpq.symm).symm
      · exact hj1' hpq
      · rfl) (by
      intro k
      fin_cases k
      · exact hx0
      · exact hj1)
    have hv := h x J hJ
    rw [val_of α (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k),
      val_of α' (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k)] at hv
    have hle : L.wchart ![(snd T A).left, m.left] j ≤ (LPow A L a T).U (fun _ : Fin 1 => i0) := by
      intro y hy
      exact (mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) y).mpr
        (fun _ => (mem_wchart_lemma L _ j y).mp hy 0)
    have e1 := congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h' j)
    have e2 := congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h'' j)
    rw [gs_mul _ _ _ hxW] at e1 e2
    have hu : gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α.s j).val =
        gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α'.s j).val := by
      exact (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α.s j)).trans
        ((congrArg Units.val hv).trans (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α'.s j)).symm)
    have r1 := gs_res (𝟙 (T ⊗ A).left) x hle hxW (s'.f fun _ => i0)
    have r2 := gs_res (𝟙 (T ⊗ A).left) x hle hxW (s''.f fun _ => i0)
    exact r1.symm.trans (e1.trans ((congrArg (· * _) hu).trans (e2.symm.trans r2)))
  obtain ⟨f1, p1⟩ := s'
  obtain ⟨f2, p2⟩ := s''
  have : f1 = f2 := funext hf
  subst this
  rfl

theorem act_congr (hL : L.IsLB) {T : Over S} {k : ℤ} {U U' : ThetaGrp A L k T} (hp : U.pt = U'.pt)
    (h : LB.Gen.Corr L _ _ _ _ U.φ U'.φ) {s s' s'' : LB.Sec (LPow A L k T)} (h' : IsActOf A L k U s s')
    (h'' : IsActOf A L k U' s s'') : s' = s'' := by
  obtain ⟨pt, φ, hφ⟩ := U
  obtain ⟨pt', φ', hφ'⟩ := U'
  simp only at hp
  subst hp
  unfold IsActOf at h' h''
  exact twist_congr hL (fun y J hJ => val_corr hJ h (𝟙 _)) h' h''

end TranslExist


open TranslExist in
theorem exists_isVtOver_and_existsUnique_isUUOver : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)), (∀ (ok : (T ⟶ Xo.univ.t.G) → Prop) (t t' : T ⟶ Xo.univ.t.G), t' ^ N = t → t' ^ (N ^ 2) = 1 → ok t' → ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F) ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → ∃! F, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F := by
  intro hLaws E _ _ _ H Dw l Xo N hN T s
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨α₀, hg₀, hn₀, hu₀, hT⟩ := GlobalTheory.T.universal_normalised_mulByNat_pullback_iso hLaws E H Dw l Xo N
  obtain ⟨α, hgα, hcα⟩ := hT T
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G T N)
      (snd T Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ :=
    (existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ α hgα s).exists
  have hact : ∀ (U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)
      (a : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)),
      ∃ b, IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U a b := by
    intro U a
    unfold IsActOf
    exact (existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ U.φ U.isGen a).exists
  refine ⟨fun ok t t' h1 h2 h3 => ?_, fun x₁ x₂ hx₁ hx₂ => ?_⟩
  · obtain ⟨U, hU⟩ := (GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T t' h2).1
    obtain ⟨F, hF⟩ := hact U s₁
    exact ⟨F, t', α₀, α, s₁, U, h1, h3, hg₀, hn₀, hcα, hs₁, hU, hF⟩
  · have S₁ := GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T x₁ hx₁
    have S₂ := GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T x₂ hx₂
    obtain ⟨U₁, hU₁⟩ := S₁.1
    obtain ⟨U₂, hU₂⟩ := S₂.1
    obtain ⟨s₂, hs₂⟩ := hact U₁ s₁
    obtain ⟨F, hF⟩ := hact U₂ s₂
    refine ⟨F, ⟨α₀, α, s₁, s₂, U₁, U₂, hg₀, hn₀, hcα, hs₁, hU₁, hs₂, hU₂, hF⟩, ?_⟩
    rintro F' ⟨β₀, β, t₁, t₂, V₁, V₂, hgβ₀, hnβ₀, hcβ, ht₁, hV₁, ht₂, hV₂, hF'⟩
    have e₁ : t₁ = s₁ := by
      refine twist_congr hL (fun y J hJ => ?_) ht₁ hs₁
      exact (val_corr hJ hcβ _).trans ((val_pull hJ β₀ _ _).trans ((val_corr hJ (hu₀ β₀ hgβ₀ hnβ₀) _).trans
        ((val_corr hJ hcα _).trans (val_pull hJ α₀ _ _)).symm))
    rw [e₁] at ht₂
    have e₂ : t₂ = s₂ :=
      act_congr hL (hV₁.pt_eq.trans hU₁.pt_eq.symm) (S₁.2 V₁ U₁ hV₁ hU₁) ht₂ hs₂
    rw [e₂] at hF'
    exact act_congr hL (hV₂.pt_eq.trans hU₂.pt_eq.symm) (S₂.2 V₂ U₂ hV₂ hU₂) hF' hF

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ChartRing

theorem bijective_appTop_powObj (hGF : GlobalFnsSt) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsAbelianScheme G) (n : ℕ) :
    Function.Bijective (ReciprocityTheory.ChartRestriction.G.Out.powObj G n).hom.appTop.hom := by
  cases n with
  | zero =>
    show Function.Bijective (𝟙 S : S ⟶ S).appTop.hom
    simp only [Scheme.Hom.id_appTop, CommRingCat.hom_id]
    exact Function.bijective_id
  | succ n => exact hGF _ _ (AbelianSchemeGerms.isAbelianScheme_powObj G hG n)



theorem exists_chartAt_with_germs : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S), ∃ C : ChartAt Xo c y, FrTruncC y C ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f := by
  intro hL E _ _ _ H Dw l Xo c _ hstar S _ _ _ y
  obtain ⟨d, G, A, uvec, x, -, -, hchG⟩ :=
    GlobalTheory.ChartData.exists_isChartG_of_basis E H Xo.X Xo.univ.t S y.x (Lt1 Dw) (fun ℓ => y.u ℓ.1 ℓ.2)
      (fun ℓ => y.tan ℓ.1 ℓ.2) (fun w hw => GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c S y w hw)
  have hch := (isChart_iff y d G.F A.act uvec x).2 hchG
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    GlobalTheory.exists_frames_of_chart E H Xo.X Xo.univ.t S y.x d G A (Lt1 Dw) _ uvec x hchG
  have hPow := bijective_appTop_powObj hL.globalFns Xo.univ.t.G (GlobalTheory.moduli_univ_polAV E H Dw l Xo).2.2.2.1
  obtain ⟨hax, hr⟩ := GlobalTheory.FrameBiextId.fbId E H Xo.X Xo.univ.t hPow hstar S y.x d G A (Lt1 Dw) _ uvec x e
    ph1 ph2 sy ad hchG hfr hfa had
  obtain ⟨h, hh⟩ := GlobalTheory.canonGauge_exists S d (𝓞 E) S (mkFB G A ph1 ph2 sy ad hax hr)
  refine ⟨⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, h, hch,
    (isFrame_iff y d x _ _ _ _ _ _ e).2 hfr, (isPrim_iff wP).2 hpr, hh, hrig⟩, htr, ?_⟩
  intro k F
  obtain ⟨f, hf⟩ := germSt_holds E H Xo.X Xo.univ.t S y.x d G.F A.act (Lt1 Dw) _ uvec x ph1 ph2 sy ad e wP
    hchG hfr hpr htr k F
  exact ⟨f, (isGerm_iff y d x _ e wP k F f).2 hf⟩

end GlobalTheory.ChartRing
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.shortGenerators_scaled_thetaLattice : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (w : WeightFamilies.Wt D j) (s : 𝓞 B.KO) (Sh : Finset (B.Cusp j w)) (a b : ℝ), s ≠ 0 → 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (s : B.KO)‖ ≤ a) → (∀ g ∈ Sh, g ∈ X.shortTh w ∧ ∀ σ, Real.log (B.supN j w σ g) ≤ b) → Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ → ShortG X w (X.Thc s w) (a + b + lamStar D * w.size) := by
  first | exact @GlobalTheory.RunIn.shortG_scaled | exact GlobalTheory.RunIn.shortG_scaled | (intros; apply GlobalTheory.RunIn.shortG_scaled <;> assumption)
end
