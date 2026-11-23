module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle711
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle733
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHodgeMetricGenericFibre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle761
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle710
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle500
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulConjTransposeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle755
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle738
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_extendedColumnData_all_clauses_but_places : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ ExtN z z') := by
  first | exact @GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build | exact GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build | (intros; apply GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.BaseVolume

theorem mass_openPart_eq_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ptsIn X.str (σ.comp e.toRingHom) (openPart j)) = ENNReal.ofReal (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have hj' : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_componentUniformisation_boundedDomain_complexPoints E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have himg := GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hfib := GlobalTheory.T.componentUniformisation_fibre_arithmeticGroup_related E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hinv := GlobalTheory.T.componentUniformisation_arithmeticGroup_invariant E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hdens := GlobalTheory.T.chernTopPart_hodgeMetric_uniformisation_image E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hnull := GlobalTheory.T.uniformisation_null_sets_to_pointClass_null E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  obtain ⟨FD, hFD⟩ := GlobalTheory.BoundedFundDomain.exists_isFD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp
  obtain ⟨hlt, hcov⟩ := GlobalTheory.FlagFibre.covol_eq_muD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp FD hFD
  obtain ⟨hFm, hFsub, hFcov, hFbad⟩ := hFD
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set Bad := {v | v ∈ FD ∧ ∃ γ ∈ gammaU (U.X k) hj' (Equiv.refl (U.X k).Ψ), flat (moebI γ (unflat v)) ∈ FD ∧
    moebI γ (unflat v) ≠ unflat v} with hBad
  set B' := toMeasurable μD Bad with hB'
  have hB'0 : μD B' = 0 := by rw [hB', measure_toMeasurable]; exact hFbad
  have hfu : ∀ v : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat v) = v := fun v => rfl
  have hinj : Set.InjOn ψ (FD \ B') := by
    intro v hv w hw hvw
    obtain ⟨γ, hγ, hγe⟩ := hfib v (hFsub hv.1) w (hFsub hw.1) hvw
    have hnb : v ∉ Bad := fun h => hv.2 (subset_toMeasurable _ _ h)
    have h1 : moebI γ (unflat v) = unflat v := by
      by_contra hne
      exact hnb ⟨hv.1, γ, hγ, by rw [hγe, hfu]; exact hw.1, hne⟩
    rw [← hfu v, ← hfu w, ← hγe, h1]
  have hD := hdens (FD \ B') (Set.diff_subset.trans hFsub) (hFm.diff (measurableSet_toMeasurable _ _)) hinj
  have hN := hnull (FD ∩ B') (Set.inter_subset_left.trans hFsub) (measure_mono_null Set.inter_subset_right hB'0)
  have hmF : μD (FD \ B') = μD FD := measure_diff_null hB'0
  have hsub : ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ⊆ ψ '' (FD \ B') ∪ ψ '' (FD ∩ B') := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨γ, hγ, hγF⟩ := hFcov (unflat v) hv
    rw [← Set.image_union, Set.diff_union_inter, ← hinv γ hγ v hv]
    exact Set.mem_image_of_mem _ hγF
  have hsup : ψ '' (FD \ B') ⊆ ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) :=
    Set.image_mono (Set.diff_subset.trans hFsub)
  rw [← himg, hcov, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hlt.ne, ← hmF, ← hD]
  refine le_antisymm ?_ (measure_mono hsup)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hN, add_zero]

end GlobalTheory.BaseVolume
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.HodgeChart

theorem gram_entry {m m' g : ℕ} (R : Matrix (Fin m) (Fin g) ℂ) (R' : Matrix (Fin m') (Fin g) ℂ)
    (M : Matrix (Fin g) (Fin g) ℂ) (s t : ℂ) (b : Fin m) (b' : Fin m') :
    ((s • R) * M * (t • R')ᴴ) b b' = s * star t * hermForm M (R b) (R' b') := by
  simp only [hermForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec, Pi.star_apply, star_mul', Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mem_openPart_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str) (z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)), z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ Inner (cxOf e σ hj z) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ X j hj z
  rw [mem_ptsIn]
  exact Iff.rfl


open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in
theorem periodChart_rescale : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → 0 < r → r ≤ 1 → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (r • u) + ∑ i, (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ u : Fin n → ℂ, (∀ i : Fin a, u (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (r • u) + ∑ i, (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B u = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (r • u) := by
  intro n a ha g rk τ₀ B r hP hr hr1
  set cst : ℂ := (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst
  have him : cst.im = -Real.log r / (2 * Real.pi) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : cst = ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hcst]; push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [e, Complex.im_ofReal_mul, Complex.I_im, mul_one]
  have hBs : ∀ i (j k : Fin g), B i k j = B i j k := fun i j k => by
    have := (hP.psd i).isHermitian.apply j k
    simp at this
    exact_mod_cast this
  have hmaps : ∀ z ∈ polydisc n 1, r • z ∈ polydisc n 1 := fun z hz k => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hr.le]
    calc r * ‖z k‖ ≤ 1 * ‖z k‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact hz k
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => r • z) (polydisc n 1) :=
    ((differentiable_id.const_smul (r : ℂ)).differentiableOn).congr fun u _ => by
      funext k; simp [Complex.real_smul]
  refine ⟨⟨hP.rk_le, fun j k => ?_, fun z hz => ?_, hP.psd, hP.supp, hP.toric, fun z hz => ?_⟩, fun u hu => ?_⟩
  · have h1 := (hP.holo j k).comp hdiff hmaps
    refine (h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_
    simp [Matrix.add_apply, Matrix.sum_apply, Function.comp]
  · refine Matrix.IsSymm.ext fun j k => ?_
    have := (hP.symm _ (hmaps z hz)).apply j k
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]
  · have h1 := hP.abelian _ (hmaps z hz)
    convert h1 using 1
    ext ⟨j, hj⟩ ⟨k, hk⟩
    simp [Matrix.sum_apply, hP.supp _ j k (Or.inl hj)]
  · ext j k
    have hu' : ∀ i : Fin a, tlog ((r • u) (Fin.castLE ha i)) = -Real.log r / (2 * Real.pi) + tlog (u (Fin.castLE ha i)) := by
      intro i
      rw [Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg hr.le,
        Real.log_mul hr.ne' (norm_ne_zero_iff.2 (hu i))]
      ring
    simp only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      hu', Complex.add_im, Complex.im_sum, smul_eq_mul]
    push_cast
    simp only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]
    push_cast
    simp only [zero_add]
    ring

theorem exists_hodge_period_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), y ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∃ (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)) (a : ℕ) (ha : a ≤ X.dim) (g rk : ℕ) (τ₀ : (Fin X.dim → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ (∀ z ∈ ch.source, z ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ∃ i : Fin a, ch z (Fin.castLE ha i) = 0) ∧ ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ Q : ∀ τ : E →+* ℂ, (Fin X.dim → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ, (∀ τ i k, DifferentiableOn ℂ (fun w => Q τ w i k) (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1)) ∧ Fintype.card (Σ τ, Fin (Dw.mult τ)) = g ∧ LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q p.1 0 p.2) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ, lieGram e U hj f₀ A₀ A z τ = Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ (ch z).ofLp)ᴴ) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ τ', τ ≠ τ' → Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ' (ch z).ofLp)ᴴ = 0) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, κ, hP, hE, hx₀, h0, hcard, hκ, hInner, hHodge⟩ :=
    GlobalTheory.T.exists_periodChart_hodgeMetric_genericFibre E H Dw l Xo c O β Y T σ U hσ hU (cxOf e σ hj y)
  obtain ⟨A, hA, r, hr, W, hWd, hWli, hWfr⟩ :=
    GlobalTheory.T.exists_holomorphic_eigenFrame_dirs_in_expChart E H Dw l Xo c O β Y T F e σ C X j f f₀ Eb A₀ hj hL y n g ch₀ ex hE hx₀ h0
  obtain ⟨hn, r', ch, hr', hr'r, hr'1, hHolo, hy', hch0, hpoly, hrel⟩ :=
    GlobalTheory.T.exists_holomorphicChart_of_expChart_genericFibre E H Dw l Xo c O β Y T F e σ X j hj hL.1 y n g ch₀ ex hE hx₀ h0 r hr
  subst hn
  have hrel' : ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = r' • (ch z).ofLp := by
    intro z hz
    refine ⟨(hrel z hz).1, ?_⟩
    rw [(hrel z hz).2]
    try (funext k; simp [Complex.real_smul])
  obtain ⟨hP1, hY⟩ := periodChart_rescale X.dim a ha g rk τ₀ B r' hP hr' hr'1.le
  have hr'0 : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'.ne'
  have hball : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1, r' • u ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
    intro u hu
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr'.le]
    have : ‖u‖ < 1 := (pi_norm_lt_iff one_pos).2 hu
    calc r' * ‖u‖ ≤ r' * 1 := by gcongr
      _ < r := by linarith
  have hnz : ∀ z ∈ ch.source, Inner (cxOf e σ hj z) → ∀ i : Fin a, (ch z).ofLp (Fin.castLE ha i) ≠ 0 := by
    intro z hz hI i h
    have := ((hInner _ (hrel' z hz).1).1 hI) i
    rw [(hrel' z hz).2, Pi.smul_apply, h, smul_zero] at this
    exact this rfl
  let Q : ∀ τ : E →+* ℂ, (Fin X.dim → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u =>
    ((Real.sqrt (κ τ) : ℝ) : ℂ) • Matrix.of fun b k => W (r' • u) ⟨τ, b⟩ k
  refine ⟨ch, a, ha, g, rk, _, B, hP1, hHolo, hy', hch0, hpoly, ?_, A, hA, Q, ?_, hcard, ?_, ?_, ?_⟩
  · intro z hz
    rw [mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z, hInner _ (hrel' z hz).1, (hrel' z hz).2]
    simp only [Pi.smul_apply, ne_eq, not_forall, not_not]
    refine exists_congr fun i => ?_
    rw [smul_eq_zero, or_iff_right hr'.ne']
    try rfl
  · intro τ i k
    have hd := (hWd ⟨τ, i⟩ k).comp (f := fun u : Fin X.dim → ℂ => r' • u)
      ((differentiable_id.const_smul (r' : ℂ)).differentiableOn.congr fun u _ => by
        simp [Complex.real_smul, Pi.smul_def]) (fun u hu => hball u hu)
    exact (hd.const_mul ((Real.sqrt (κ τ) : ℝ) : ℂ)).congr fun u _ => by simp [Q]
  · have hW0 : (fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => Q p.1 0 p.2) =
        (fun p => Units.mk0 (((Real.sqrt (κ p.1) : ℝ) : ℂ))
          (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hκ p.1)).ne') • W 0 p) := by
      funext p k
      simp [Q]
    rw [hW0]
    exact hWli.units_smul _
  · intro z hz hzO τ
    have hI : Inner (cxOf e σ hj z) := (mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z).1 hzO
    have hb : ch₀ (cxOf e σ hj z) ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
      rw [(hrel' z hz).2]; exact hball _ (hpoly z hz)
    obtain ⟨hex, hDirs⟩ := hWfr z (hrel' z hz).1 hb
    unfold lieGram
    rw [dite_eq_left hex]
    obtain ⟨hgram, -⟩ := hHodge _ (hrel' z hz).1 hI hex.choose _ (hDirs _ hex.choose_spec)
    rw [hgram τ, hY _ (hnz z hz hI), ← (hrel' z hz).2]
    ext b b'
    rw [gram_entry]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Q]
    rw [← (hrel' z hz).2]
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hκ τ).le]
    rfl
  · intro z hz hzO τ τ' hττ
    have hI : Inner (cxOf e σ hj z) := (mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z).1 hzO
    have hb : ch₀ (cxOf e σ hj z) ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
      rw [(hrel' z hz).2]; exact hball _ (hpoly z hz)
    obtain ⟨hex, hDirs⟩ := hWfr z (hrel' z hz).1 hb
    obtain ⟨-, horth⟩ := hHodge _ (hrel' z hz).1 hI hex.choose _ (hDirs _ hex.choose_spec)
    rw [hY _ (hnz z hz hI), ← (hrel' z hz).2]
    ext b b'
    rw [gram_entry]
    have h1 := horth ⟨τ, b⟩ ⟨τ', b'⟩ hττ
    simp only [Matrix.zero_apply]
    rw [← (hrel' z hz).2]
    exact mul_eq_zero_of_right _ h1

end GlobalTheory.LieBase.HodgeChart
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_starSubdivision_invariant_polyhedral_fan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H w → IsCentreSet H.bar q ψ w → ∃ ψ' : InvFun (𝓞 E), IsPolyFan H.bar q ψ' ∧ IsTwInv H ψ' ∧ Subordinate H.bar q ψ' ψ ∧ IsStarOf H.bar q ψ w ψ' := by
  first | exact @GlobalTheory.PolFan.exists_starSubdivision | exact GlobalTheory.PolFan.exists_starSubdivision | (intros; apply GlobalTheory.PolFan.exists_starSubdivision <;> assumption)
end
