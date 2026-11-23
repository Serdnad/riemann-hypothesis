module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

private theorem compactSpace_model {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) : CompactSpace Y.X := by
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI := hi
  haveI : IsProper (PSpace.str O N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  haveI : QuasiCompact Y.s := by rw [← hs]; infer_instance
  exact QuasiCompact.compactSpace_of_compactSpace Y.s

private theorem exists_mChart_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] [IsNoetherianRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hP : PushInvertible Y.t.G Y.t.PP.L) (x : Y.X) : ∃ M : MChart Y, x ∈ M.U := by
  obtain ⟨U, hU, hxU, hdom, ⟨θ, hθ, hne⟩, n, v₀, ρ, hlie⟩ :=
    GlobalTheory.ModelChart.exists_chart_lieBasis_matrices E H Dw l Xo c O β Y hP x
  exact ⟨⟨U, hU, hdom, θ, hθ, hne, n, v₀, ρ, hlie⟩, hxU⟩

theorem exists_finite_mchart_cover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L → ∃ (J : Type) (_ : Finite J) (M : J → MChart Y), ∀ x : Y.X, ∃ j, x ∈ (M j).U := by
  intro E _ _ _ H Dw l Xo c O _ _ β Y hP
  haveI := compactSpace_model Y
  choose M hM using exists_mChart_mem Y hP
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((M x).U : Set Y.X))
    (fun x => (M x).U.isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hM x⟩)
  refine ⟨t, inferInstance, fun j => M j.1, fun x => ?_⟩
  obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨⟨j, hj⟩, hx⟩

end GlobalTheory.Reg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open scoped CategoryTheory.Obj

namespace GlobalTheory.Reg

theorem finrank_eq_of_existsUnique_comb {L V : Type} [Field L] [AddCommGroup V] [Module L V] (N : Submodule L V)
    {m : ℕ} (cv : Fin m → V) (hcv : ∀ i, cv i ∈ N) (h : ∀ v ∈ N, ∃! a : Fin m → L, ∑ i, a i • cv i = v) :
    Module.finrank L N = m := by
  have hli : LinearIndependent L cv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := (h 0 N.zero_mem).unique hg (y₂ := 0) (by simp)
    rw [this]; rfl
  have hN : N = Submodule.span L (Set.range cv) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, rfl, -⟩ := h v hv
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hcv i
  rw [hN, finrank_span_eq_card hli, Fintype.card_fin]

theorem finrank_chart_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (x : Sp L ⟶ Xo.X) (Λ : M.Lift f x) (τ : E →+* ℂ) (N : Submodule L (Fin M.n → L)), (∀ cv, cv ∈ N ↔ M.Eig f τ cv) → Module.finrank L N = Dw.mult τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f x Λ τ N hN
  classical
  have hx0 : x ≫ Xo.s = sOf c L := by
    rw [← Λ.xF_fst, Category.assoc, pullback.condition, ← Category.assoc, Λ.xF_snd]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := by
    have := Xo.univ.t.semi.smooth
    show Smooth (pullback.snd Xo.univ.t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  obtain ⟨d, hd, hdW⟩ : ∃ d : Fin (Dw.mult τ) → Fin n → L,
      LinearIndependent L d ∧ ∀ i, d i ∈ gfpEig (c := c) hx τ := by
    obtain ⟨B⟩ : Nonempty (Module.Basis (Fin (Dw.mult τ)) L (gfpEig (c := c) hx τ)) :=
      ⟨Module.finBasisOfFinrankEq L _ (gfp_finrank hx0 hx τ)⟩
    exact ⟨(gfpEig (c := c) hx τ).subtype ∘ B,
      B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _), fun i => by simp⟩
  obtain ⟨hex, htan, hco⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M L f x Λ
  have hcomb := GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M L f x Λ
  have heig := GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M L f x Λ τ
  choose cv hcv using fun i => (hco _ (gfp_tan hx (d i))).exists
  refine finrank_eq_of_existsUnique_comb N cv
    (fun i => (hN _).2 ((heig _ _ (hcv i)).1 ((gfp_eig_iff hx τ _).2 (hdW i)))) fun v hv => ?_
  obtain ⟨w, hw⟩ := (hex v).exists
  have hwt := htan v w hw
  have hb := gfp_basis hx0 hx τ d hd hdW w hwt ((heig v w hw).2 ((hN v).1 hv))
  refine (existsUnique_congr fun a => ?_).1 hb
  rw [hcomb _ cv _ a w hcv]
  exact ⟨fun h => (hco w hwt).unique h hw, fun h => h ▸ hw⟩

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.naturalRule_value_baseChange_of_isReduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (S T : Type) [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c f z = φ (evR Xo c f y) := by
  first | exact @GlobalTheory.Reg.evR_baseChange_of_isReduced | exact GlobalTheory.Reg.evR_baseChange_of_isReduced | (intros; apply GlobalTheory.Reg.evR_baseChange_of_isReduced <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.exists_cBase_valAtCx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∃ yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)), (∀ Z, CBase h Z (yP Z)) ∧ ValAtCx h yP ∧ GenFromTest Xo c h := by
  intro E _ _ _ H Dw l Xo c hL h
  have hex : ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ z : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) z :=
    fun Z P => hL.bc _ _ (PAlg P) (genFr h Z)
  choose yP hyP using hex
  refine ⟨yP, fun Z P => hyP Z P, fun Z P a n f hf => ?_, fun Z => hL.test _ _⟩
  have e := GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf (Om Z) (CAt (sgOf P)) (PAlg P)
    (genFr h Z) (yP Z P) (hyP Z P)
  rw [e]
  rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.integrality_trivialValuations_of_normalAffineCharts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, ∀ la, (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, 0 ≤ v f) → ∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.trivialClassCondition Xo c) la, 0 ≤ v f := by
  first | exact @GlobalTheory.integrality_at_trivial_valuations_of_charts | exact GlobalTheory.integrality_at_trivial_valuations_of_charts | (intros; apply GlobalTheory.integrality_at_trivial_valuations_of_charts <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

theorem fnFG_fnTrdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FnFG Xo c ∧ FnTrdeg Xo c (Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨h1, h2⟩ := GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c
  refine ⟨fnFG_of Xo c h1, ?_⟩
  rw [← dim_add_card_flagVar E H Dw]
  exact fnTrdeg_of Xo c Dw.dim h2

end GlobalTheory.FlagDim
end
