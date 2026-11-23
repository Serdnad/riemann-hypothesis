module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle210
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle173
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

theorem _root_.GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
  first | exact @GlobalTheory.ChartStab.chart_stab | exact GlobalTheory.ChartStab.chart_stab | (intros; apply GlobalTheory.ChartStab.chart_stab <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspGeo

theorem closeR_mono {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    {u : GA D V} {a a' : ℝ} (h : CloseR θ V u a) (hle : a ≤ a') : CloseR θ V u a' :=
  ⟨h.1, fun τ i j => (h.2 τ i j).trans hle⟩

theorem cuspDecayBound : GlobalTheory.Published.CuspDecayBound := by
  intro D θ hθ V U hU A N
  let Dr : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → (GA D V → ℂ) → GA D V → ℂ :=
    fun p f => Rder θ V p.1 p.2 f
  let 𝓒 : Set (GA D V → ℂ) := {φ | IsAutFun V φ ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ SmoothW θ V φ ∧
    (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      GlobalTheory.Grow.ModGrowthExp V A (l.foldr Dr φ)) ∧ IsCuspFun V φ}
  obtain ⟨B, Ω₀, Cm, δ₁, hB, hΩ₀, hδ₁, hCm, hmv⟩ := GlobalTheory.T.meanValue_ineq_rightTranslate_realPoint_near_one D θ hθ V
  obtain ⟨b, Cn, δn, hδn, hnear⟩ := GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale D θ hθ V U hU
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hΩ₀
  have hstab : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒 := by
    rintro ψ ⟨ha, hlev, hs, hg, hc⟩ i hi
    exact GlobalTheory.T.rightDerivative_smoothCuspidal_same_level D θ hθ V U i.1 i.2 (hB i hi) A ψ ha hlev hs hg hc
  have hwords : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i ∈ l, i ∈ B) →
      ∀ ψ ∈ 𝓒, l.foldr Dr ψ ∈ 𝓒 := by
    intro l
    induction l with
    | nil => intro _ ψ hψ; exact hψ
    | cons a l ih =>
      intro hl ψ hψ
      exact hstab _ (ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) ψ hψ) a (hl a List.mem_cons_self)
  set Cn' := max Cn 0 with hCn'
  have hCn'0 : 0 ≤ Cn' := le_max_right _ _
  set δ₀ := min δn (δ₁ / (Cn' + 1)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδn (div_pos hδ₁ (by linarith))
  set K := max (max Cn (Cm * Cn')) (max H 1) with hK
  have hK1 : Cn ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK2 : Cm * Cn' ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hK3 : H ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hstep : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ GlobalTheory.Grow.quotHeight V g * δ ^ b ≤ K ∧ (δ₀ ≤ δ ∨
      ∃ Ω : Set (GA D V), (∀ w ∈ Ω, GlobalTheory.Grow.quotHeight V w ≤ K * GlobalTheory.Grow.quotHeight V g ∧
        GlobalTheory.Grow.quotHeight V g ≤ K * GlobalTheory.Grow.quotHeight V w) ∧
      ∀ ψ ∈ 𝓒, ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ K * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ0, hδ1, hq, hcase⟩ := hnear g
    refine ⟨δ, hδ0, hδ1, hq.trans hK1, ?_⟩
    by_cases hδ : δ₀ ≤ δ
    · exact Or.inl hδ
    right
    push_neg at hδ
    have hδn' : ¬ δn ≤ δ := fun h => absurd (hδ.trans_le (min_le_left _ _)) (not_lt.2 h)
    obtain ⟨r, C₀, hC₀, hN⟩ := hcase.resolve_left hδn'
    have hsmall : Cn' * δ ≤ δ₁ := by
      have h1 : δ < δ₁ / (Cn' + 1) := hδ.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h1
      nlinarith
    refine ⟨(g * ·) '' Ω₀, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hq0 := GlobalTheory.Grow.one_le_quotHeight V g
      have hq1 := GlobalTheory.Grow.one_le_quotHeight V (g * w)
      have hw1 := hH w hw
      constructor
      · calc GlobalTheory.Grow.quotHeight V (g * w) ≤ GlobalTheory.Grow.quotHeight V g * GlobalTheory.Grow.height V w :=
              GlobalTheory.Grow.quotHeight_mul_le V g w
          _ ≤ GlobalTheory.Grow.quotHeight V g * K := mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V g := mul_comm _ _
      · calc GlobalTheory.Grow.quotHeight V g = GlobalTheory.Grow.quotHeight V (g * w * w⁻¹) := by rw [mul_inv_cancel_right]
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * GlobalTheory.Grow.height V w⁻¹ := GlobalTheory.Grow.quotHeight_mul_le V _ _
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * K := by
              rw [GlobalTheory.Grow.height_inv]; exact mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V (g * w) := mul_comm _ _
    · rintro ψ ⟨ha, hlev, hs, hg, hc⟩ c hc'
      have hsum : 0 ≤ ∑ i ∈ B, c i := Finset.sum_nonneg fun i hi => (hc' i hi).1
      have hmain : ‖ψ g‖ ≤ Cm * (Cn' * δ) * ∑ p ∈ B, c p := by
        refine GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical D V ψ ha hc r C₀ hC₀ g _ fun m hm => ?_
        obtain ⟨γ, hγ, u, k, hu, hkU, hkf, hmg⟩ := hN m hm
        have hval : ψ (m * g) = ψ (g * u) := by
          rw [hmg, show γ * g * u * k = γ * (g * u) * k by group, hlev k hkU hkf, ha.left γ hγ]
        rw [hval]
        refine hmv ψ hs g u (Cn' * δ) (mul_nonneg hCn'0 hδ0.le) hsmall
          (closeR_mono hu (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le)) c fun p hp w hw => ?_
        exact (hc' p hp).2 _ ⟨w, hw, rfl⟩
      refine hmain.trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hδ0.le) hsum
  obtain ⟨L, C', hLB, hL⟩ := GlobalTheory.T.exists_rapid_decay_of_iterated_gain (GA D V) (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) B
    (GlobalTheory.Grow.quotHeight V) 𝓒 Dr b K δ₀ hδ₀pos (GlobalTheory.Grow.one_le_quotHeight V) hstab hstep A N
  refine ⟨L, C' * 2 ^ A, fun l hl p hp => hB p (hLB l hl p hp), ?_⟩
  intro φ ha hlev hs hg hc c hcl g
  have hφ : φ ∈ 𝓒 := ⟨ha, hlev, hs, hg, hc⟩
  have h := hL φ hφ (fun l => c l * 2 ^ A) (fun l hl g' =>
    GlobalTheory.Grow.norm_le_quotHeight_pow (hwords l (hLB l hl) φ hφ).1.left (hcl l hl) g') g
  refine h.trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  ring

end GlobalTheory.CuspGeo
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.FinPl.GlobImage
variable {D : D7}

theorem mulVec_mem {I : Ideal (AE D)} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem finPart_pure (α : Af D.host.F) (e : D.host.E) :
    finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem infPart_pure (α : Af D.host.F) (e : D.host.E) :
    infPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = 0 := by
  unfold infPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  have : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

theorem compFin_pure (w : Pl D) (α : Af D.host.F) (e : D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (α ⊗ₜ[D.host.F] e) = (evalV D.host.F w α) ⊗ₜ[D.host.F] e := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem compAt_pure (w : Pl D) (α : Af D.host.F) (e : D.host.E) :
    compAt D w ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = (evalV D.host.F w α) ⊗ₜ[D.host.F] e := by
  unfold compAt
  rw [RingHom.comp_apply, finPart_pure, compFin_pure]

theorem pure_mem (P : Pl D → Prop) (α : Af D.host.F) (hα : ∀ v, ¬ P v → evalV D.host.F v α = 0) (e : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e ∈ idAt D P := by
  refine Ideal.mem_inf.2 ⟨?_, ?_⟩
  · rw [RingHom.mem_ker, infPart_pure]
  · refine (Submodule.mem_iInf _).2 fun w => ?_
    rw [RingHom.mem_ker, compAt_pure, hα w.1 w.2, TensorProduct.zero_tmul]

theorem latV_supp : ∀ (D : D7) (S : HSp D) (M : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D),
    y ∈ latV S M P → ∀ i, y i ∈ idAt D P := by
  intro D S M P y hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, -, hα, a, ha, x, -, rfl⟩ := hz
    exact fun i => pure_mem P α hα _
  | zero => exact fun i => (idAt D P).zero_mem
  | add a b _ _ ha hb => exact fun i => (idAt D P).add_mem (ha i) (hb i)
  | neg a _ ha => exact fun i => (idAt D P).neg_mem (ha i)

theorem latV_toHat : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice
theorem latV_ofHat : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice
theorem finRep : ∀ (D : D7) (S : HSp D) (g : GA D S), ∃ x ∈ GfC S, ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → mt S g *ᵥ y = mt S x *ᵥ y := GlobalTheory.T.exists_finiteComponent_unitary_acting_on_finiteSupported

theorem latV_iff_hat (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hat L :=
  ⟨latV_toHat D S L P y, latV_ofHat D S L P y hy⟩

theorem finE_mulVec (S : HSp D) (x : GA D S) (y : Fin S.rank → AE D) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((mt S x *ᵥ y) i))) =
      (Formalism.IndefR.Lev.finE S x).val *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) := by
  have h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) := by
    ext i j
    rfl
  rw [h]
  ext i
  exact RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i


theorem image_moves (S : HSp D) (L : Lat S) (hL : IsSelfDualC S L) (g : GA D S) :
    ∃ M : Lat S, IsSelfDualC S M ∧ ∀ P : Pl D → Prop, Moves S g L M P := by
  obtain ⟨x, hx, hgx⟩ := finRep D S g
  have hI := GlobalTheory.AdIsomImage.imageSt D S L hL x hx
  obtain ⟨⟨M, hMl, hM⟩, hsd⟩ := hI
  refine ⟨M, hsd M hMl hM, fun P y hy => ?_⟩
  have hy' : ∀ i, (mt S x *ᵥ y) i ∈ idAt D P := mulVec_mem _ hy
  rw [hgx P y hy, latV_iff_hat S L P y hy, latV_iff_hat S M P _ hy', finE_mulVec]
  show _ ∈ Formalism.L2.Herm.hatL L ↔ _ ∈ Formalism.L2.Herm.hatL M
  rw [hM, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

section Gen
variable {R : Type} [CommRing R] {m n l : ℕ}
theorem mulVec_col (A : Matrix (Fin l) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) (i : Fin n) (a : R) :
    A *ᵥ (fun k => a * x k i) = fun k => a * (A * x) k i := by
  ext k
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem mulVec_eq_sum (x : Matrix (Fin m) (Fin n) R) (w : Fin n → R) :
    x *ᵥ w = ∑ i, fun k => w i * x k i := by
  ext k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by ring
end Gen

theorem colMul_eq {m n : ℕ} (x : Mx D m n) (i : Fin n) (a : AE D) : colMul x i a = fun k => a * x k i := rfl


theorem supp_of {S : HSp D} {S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (M : Lat S) (M₀ : Lat S₀) (v : Pl D)
    (y : Fin S.rank → AE D)
    (hX : ∀ i, colMul d.jX i ((d.pX *ᵥ y) i) ∈ latV S M (· = v))
    (hY : ∀ i, colMul d.jY i ((d.pY *ᵥ y) i) ∈ latV S M (· = v)) (h0' : d.p0 *ᵥ y ∈ latV S₀ M₀ (· = v)) :
    ∀ k, y k ∈ idAt D (· = v) := by
  intro k
  have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
      d.sum_eq_one, Matrix.one_mulVec]
  rw [e, Pi.add_apply, Pi.add_apply]
  refine add_mem (add_mem ?_ (mulVec_mem _ (latV_supp D S₀ M₀ _ _ h0') k)) ?_
  · rw [mulVec_eq_sum, Finset.sum_apply]
    exact Ideal.sum_mem _ fun i _ => latV_supp D S M _ _ (hX i) k
  · rw [mulVec_eq_sum, Finset.sum_apply]
    exact Ideal.sum_mem _ fun i _ => latV_supp D S M _ _ (hY i) k


theorem col_iff {S : HSp D} (L M : Lat S) (g : GA D S) (v : Pl D) {n : ℕ} (x : Mx D S.rank n)
    (hg : HMul.hMul (mt S g) x = x) (h1 : Moves S g L M (· = v)) (i : Fin n) (a : AE D) (ha : a ∈ idAt D (· = v)) :
    colMul x i a ∈ latV S L (· = v) ↔ colMul x i a ∈ latV S M (· = v) := by
  have hs : ∀ k, colMul x i a k ∈ idAt D (· = v) := fun k => (idAt D _).mul_mem_right _ ha
  rw [h1 _ hs, colMul_eq, mulVec_col, hg]


theorem wittEmbedding_carries_latticeCompletion (S : HSp D) (L : Lat S) (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L₀ M₀ : Lat S₀) (M : Lat S)
    (γ : GA D S₀) (v : Pl D) (hL : MonoAt d L L₀ v) (h0 : Moves S₀ γ L₀ M₀ (· = v))
    (h1 : Moves S (d.emb0 γ) L M (· = v)) : MonoAt d M M₀ v := by
  intro y
  by_cases hy : ∀ k, y k ∈ idAt D (· = v)
  · have hy' : ∀ k, (mt S (d.emb0 γ⁻¹) *ᵥ y) k ∈ idAt D (· = v) := mulVec_mem _ hy
    have hgy : mt S (d.emb0 γ) *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← mt_mul, ← map_mul, mul_inv_cancel, map_one, mt_one, Matrix.one_mulVec]
    have hX' : d.pX *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) = d.pX *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
    have hY' : d.pY *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) = d.pY *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
    have h0y : d.p0 *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) = mt S₀ γ⁻¹ *ᵥ (d.p0 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding, ← Matrix.mulVec_mulVec]
    have hp0 : ∀ k, (d.p0 *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y)) k ∈ idAt D (· = v) := mulVec_mem _ hy'
    have hcore : d.p0 *ᵥ (mt S (d.emb0 γ⁻¹) *ᵥ y) ∈ latV S₀ L₀ (· = v) ↔ d.p0 *ᵥ y ∈ latV S₀ M₀ (· = v) := by
      rw [h0 _ hp0, h0y, Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
    have key := h1 _ hy'
    rw [hgy] at key
    rw [← key, hL, hX', hY', hcore]
    exact and_congr (forall_congr' fun i => col_iff L M _ v d.jX (d.wittDecomp_anisotropicEmbedding_inclX γ) h1 i _ (mulVec_mem _ hy i))
      (and_congr (forall_congr' fun i => col_iff L M _ v d.jY (d.wittDecomp_anisotropicEmbedding_inclY γ) h1 i _ (mulVec_mem _ hy i)) Iff.rfl)
  · constructor
    · intro h; exact absurd (latV_supp D S M _ y h) hy
    · rintro ⟨hX, hY, h0'⟩; exact absurd (supp_of d M M₀ v y hX hY h0') hy

theorem glob : ∀ (D : D7) (S : HSp D) (L : Lat S), IsSelfDualC S L → (∀ g : GA D S, ∃ M : Lat S, IsSelfDualC S M ∧ ∀ P : Pl D → Prop, Moves S g L M P) ∧ ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L₀ M₀ : Lat S₀) (M : Lat S) (γ : GA D S₀) (v : Pl D), MonoAt d L L₀ v → Moves S₀ γ L₀ M₀ (· = v) → Moves S (d.emb0 γ) L M (· = v) → MonoAt d M M₀ v :=
  fun _ S L hL => ⟨image_moves S L hL, fun S₀ ρ d L₀ M₀ M γ v => wittEmbedding_carries_latticeCompletion S L S₀ ρ d L₀ M₀ M γ v⟩

end GlobalTheory.FinPl.GlobImage
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section



namespace GlobalTheory.FinPl.OrbitCoset

variable {D : D7}

theorem mem_congGrp_iff' (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem matrixTransform_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_mem_supportedSubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at hh ⊢
  have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
      A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
    fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [matrixTransform_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem emb_mem_grpAt' {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at ha ⊢
  have hadd : ∀ M N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (M + N).map (Ideal.Quotient.mk (idAt D P)) =
      M.map (Ideal.Quotient.mk (idAt D P)) + N.map (Ideal.Quotient.mk (idAt D P)) :=
    fun M N => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add M N
  have key : (mt S (o.emb (a, 1))).map (Ideal.Quotient.mk (idAt D P)) =
      (o.jA ⬝ o.pA + o.jB ⬝ o.pB).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [o.mt_emb, mt_one]; simp only [hadd, Matrix.map_mul, ha, Matrix.mul_one]
  rw [key, o.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem inK_mul' {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a b : GA D S} (ha : InK S L P a) (hb : InK S L P b) :
    InK S L P (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, fun y hy => ?_⟩
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [mt_mul, ← Matrix.mulVec_mulVec, ← ha.2 _ hy', hb.2 y hy]

end GlobalTheory.FinPl.OrbitCoset

namespace GlobalTheory.FinPl.OrbitCoset

theorem orbit_coset : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ) (L : Lat B.V) (L₀ : Lat B.V₀) (v : Pl D), MonoAt B.d L L₀ v →
    ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ a ∈ grpAt B.A (· = v), ∀ κ₀, InK B.V₀ L₀ (· = v) κ₀ → ∀ κ,
    InK B.V L (· = v) κ → ∃ r ∈ besGrp B.d B.o, r ∈ grpAt B.V (· = v) ∧ ∃ κ', InK B.V L (· = v) κ' ∧
      n * B.d.emb0 (B.o.emb (a, 1) * κ₀) * κ = r * κ' := by
  intro D σ B L L₀ v hM n hn hnv a ha κ₀ hκ₀ κ hκ
  refine ⟨n * embA B.d B.o a, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, rfl⟩),
    mul_mem hnv (wittCoreEmbedding_mem_supportedSubgroup B.d _ (emb_mem_grpAt' B.o ha)), B.d.emb0 κ₀ * κ,
    inK_mul' ⟨wittCoreEmbedding_mem_supportedSubgroup B.d _ hκ₀.1, (carriesLattice_wittEmbedding_iff_core D B.V B.V₀ σ B.d L L₀ v κ₀ hM).2 hκ₀.2⟩ hκ, ?_⟩
  rw [map_mul, embA_apply]
  group

end GlobalTheory.FinPl.OrbitCoset

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.splitPlaceFrameGL_mem_compactRealTrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  first | exact @GlobalTheory.FrameGfC.gl_mem_GfC | exact GlobalTheory.FrameGfC.gl_mem_GfC | (intros; apply GlobalTheory.FrameGfC.gl_mem_GfC <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitPlace_matrix_eq_of_agree_with_framedGL : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (κ : GA D S) (g : GL n k), κ * (β.gl g)⁻¹ ∈ grpOff S (· = p.v) → (mt S κ).map p.pr = β.b * g.val * β.b' := by
  first | exact @GlobalTheory.AdForm.OffPlace.map_pr_of_off | exact GlobalTheory.AdForm.OffPlace.map_pr_of_off | (intros; apply GlobalTheory.AdForm.OffPlace.map_pr_of_off <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extendByZero_left_mem_core_lattice : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO A S (LA : Set _) (LS : Set _) P, (o.resS S).symm (u, 0) ∈ latO V₀ S (M : Set _) (LS : Set _) P := by
  first | exact @GlobalTheory.ContrComb.extL_mem_latO | exact GlobalTheory.ContrComb.extL_mem_latO | (intros; apply GlobalTheory.ContrComb.extL_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extendByZero_right_mem_core_lattice : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO S A (LS : Set _) (LA : Set _) P, (o.resT S).symm (u, 0) ∈ latO S V₀ (LS : Set _) (M : Set _) P := by
  first | exact @GlobalTheory.ContrComb.LatT.latO_extR | exact GlobalTheory.ContrComb.LatT.latO_extR | (intros; apply GlobalTheory.ContrComb.LatT.latO_extR <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.matrixSupportedAtPlace_of_isHalf_splitPoint : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w → MxAt (· = q.v) w := by
  first | exact @GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above | exact GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above | (intros; apply GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugateHalf_lineMultiple_mem_iff_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => cA D p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr (cA D c) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.FinPl.ConjHalf.conj_half | exact GlobalTheory.FinPl.ConjHalf.conj_half | (intros; apply GlobalTheory.FinPl.ConjHalf.conj_half <;> assumption)
end
