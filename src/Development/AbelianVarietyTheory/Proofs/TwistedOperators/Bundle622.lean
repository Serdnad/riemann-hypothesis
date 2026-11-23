module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle613
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNsmulMemOfSpan
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle612
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle429
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPointMemSumTranslateOfAnnihilator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle615
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle614
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.jacobiActionUnipotent_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → Continuous (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖(fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (γ * n) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ c, ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zEll B.L (σ + 1) B.ζ))) * (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (n * J.d.levi u) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) := by
  first | exact @GlobalTheory.Unf.FB.ThLawsL.th_laws | exact GlobalTheory.Unf.FB.ThLawsL.th_laws | (intros; apply GlobalTheory.Unf.FB.ThLawsL.th_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem natCast_smul_mem_hatL_std (Λ : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hc : ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (c : E ⊗[F] Formalism.L2.Herm.Af F) • x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨c • l, hc l hl, ?_⟩
    funext i
    simp [nsmul_eq_mul, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

theorem exists_nsmul_le_std (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG) :
    ∃ c : ℕ, 0 < c ∧ ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n := by
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le S (Formalism.L2.Pj.stdLat E n)
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat x)
  exact ⟨c, hc, fun y hy => h y (by rw [hS]; exact hy)⟩

theorem exists_nsmul_single_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, c • (Pi.single j (1 : E) : Fin n → E) ∈ Λ := by
  classical
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le (Finset.univ.image fun j : Fin n => (Pi.single j (1 : E) : Fin n → E)) Λ
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_of_span Λ hsp x)
  exact ⟨c, hc, fun j => h _ (Submodule.subset_span (by simp))⟩

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem exists_denom_stab (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev hc J Λ ⊤, ∀ i j,
      (b : E ⊗[F] Formalism.L2.Herm.Af F) * k.1 i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  obtain ⟨a, ha, hae⟩ := exists_nsmul_single_mem Λ hsp
  obtain ⟨c, hc0, hce⟩ := exists_nsmul_le_std Λ hfg
  refine ⟨a * c, Nat.mul_pos ha hc0, fun k hk i j => ?_⟩
  have hs := hk.2.1
  have hzmem : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨_, hae j, rfl⟩
  have ez : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) =
      (a : E ⊗[F] Formalism.L2.Herm.Af F) • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
    funext l
    by_cases e : l = j
    · subst e; simp [nsmul_eq_mul]
    · simp [Pi.single_eq_of_ne e, nsmul_eq_mul]
  rw [ez] at hzmem
  have hkz := (hs _).1 hzmem
  have h2 := natCast_smul_mem_hatL_std Λ c hce _ hkz
  rw [Formalism.L2.Col.mem_latS_std] at h2
  have h3 := h2 i
  rw [Matrix.mulVec_smul] at h3
  convert h3 using 1
  simp [Matrix.mulVec_single_one, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

theorem exists_denom_congLev : ∀ (D : D7) (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev D.sp.cm V.gram Λ ⊤, ∀ i j, (b : Lev.EAf D) * k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hΛ
  classical
  haveI := hΛ.1
  obtain ⟨c, hc, hcΛ⟩ := exists_nsmul_le_std Λ (Submodule.IsLattice.fg D.host.E Λ)
  have hsp : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    apply top_unique
    intro y _
    let t : Fin V.rank → D.host.E := fun i => ∑ j, V.gram i j * y j
    obtain ⟨d, hd, hdt⟩ := GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat t
    have hy : (c * d) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hcx := (GlobalTheory.LatSandwich.mem_stdLat_iff _).1 (hcΛ x hx)
      have hdt' := (GlobalTheory.LatSandwich.mem_stdLat_iff _).1 hdt
      have hint : IsIntegral ℤ (∑ i, star ((c • x) i) * (d • t) i) := by
        apply IsIntegral.sum
        intro i _
        exact ((hcx i).map (starRingEnd D.host.E).toIntAlgHom).mul (hdt' i)
      refine ⟨⟨_, hint⟩, ?_⟩
      change (∑ i, star ((c • x) i) * (d • t) i) = _
      simp only [t, Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul, star_mul, star_natCast,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hm : (c * d) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have hn : (c * d : D.host.E) ≠ 0 := by
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
    have hm' : (c * d : D.host.E) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
      simpa [Nat.cast_mul, ← Nat.cast_smul_eq_nsmul D.host.E] using hm
    have := Submodule.smul_mem (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))) (c * d : D.host.E)⁻¹ hm'
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using this
  exact exists_denom_stab D.sp.cm V.gram Λ (Submodule.IsLattice.fg D.host.E Λ)
    hsp

end GlobalTheory.LevelDenom
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.LipValue

theorem lip_value : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Is θ d Q → ∀ (J : Set (GA D Y)) (χ : GA D Y → ℂ), ∀ t ∈ MultT θ M₀ J χ, ∀ b : ℝ, (∀ x, ‖t (PiTensorProduct.tprod ℂ p.w) x‖ ≤ b) → Lip θ p.A (t (PiTensorProduct.tprod ℂ p.w)) (Real.exp Q * b) := by
  intro hCusp D θ hθ Y V d S S' M₀ M p Q hp J χ t ht b hb
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D Y
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : LocallyCompactSpace (GinfC Y) := (GlobalTheory.AdelicSplit.isClosed_GinfC' Y).locallyCompactSpace
  obtain ⟨c, hc⟩ := hp.2 (Measure.haar : Measure (GinfC Y)) inferInstance
  set m : Measure (GinfC Y) := Measure.haar with hm
  set φ : GA D Y → ℂ := t (PiTensorProduct.tprod ℂ p.w) with hφ
  set α : GinfC Y → ℂ := fun h => coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y)) with hα
  have hαi : Integrable α m := by simpa only [one_mul] using (hc.far 1).1
  have hrep := GlobalTheory.T.integrable_scalar_action_multiplicityMap_values hCusp D θ hθ Y S' M₀ J χ t ht p.w m inferInstance α c hαi hc.act

  have hT := (mem_multT θ M₀ J χ t).1 ht
  have hcont : Continuous φ := by
    have key : ∀ T ∈ Mult θ M₀ J χ, Continuous (T p.w) := by
      intro T hT'
      induction hT' using Submodule.span_induction with
      | mem T h => exact (h.aut p.w).cont
      | zero => exact continuous_const
      | add T T' _ _ h h' => exact h.add h'
      | smul a T _ h => exact h.const_smul a
    have := key _ hT
    simpa [PiTensorProduct.lift_symm] using this
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 1)
  intro x τ X hX s
  let k : GinfC Y := ⟨oneP θ Y τ X s, GlobalTheory.PointAtPlaceHom.atTau_mem Y τ _⟩
  have hkinv : ((k⁻¹ : GinfC Y) : GA D Y) = oneP θ Y τ X (-s) := by
    show (oneP θ Y τ X s)⁻¹ = _
    exact inv_eq_of_mul_eq_one_right (by
      rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ])
  have hmeas : ∀ y : GA D Y, AEStronglyMeasurable (fun h : GinfC Y => φ (y * h)) m := fun y =>
    (hcont.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
  have hbd : ∀ y : GA D Y, ∀ᵐ (h : GinfC Y) ∂m, ‖φ (y * h)‖ ≤ b := fun y => Filter.Eventually.of_forall fun h => hb _
  have hαk : Integrable (fun h => α (k⁻¹ * h)) m := hαi.comp_mul_left k⁻¹
  have hI1 : Integrable (fun h => α (k⁻¹ * h) * φ (x * h)) m := hαk.mul_bdd (hmeas x) (hbd x)
  have hI0 : Integrable (fun h => α h * φ (x * h)) m := hαi.mul_bdd (hmeas x) (hbd x)
  have h1 : c * φ (x * k) = ∫ h, α (k⁻¹ * h) * φ (x * h) ∂m := by
    rw [← hrep (x * k)]
    have := integral_mul_left_eq_self (μ := m) (fun h => α (k⁻¹ * h) * φ (x * h)) k
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    show α h * φ (x * ↑k * ↑h) = α (k⁻¹ * (k * h)) * φ (x * ↑(k * h))
    rw [inv_mul_cancel_left, Subgroup.coe_mul, mul_assoc]
  have hdiff : c * (φ (x * k) - φ x) = ∫ h, (α (k⁻¹ * h) - α h) * φ (x * h) ∂m := by
    rw [mul_sub, h1, ← hrep x, ← integral_sub hI1 hI0]
    congr 1
    funext h
    ring
  have hlip := hc.lip τ X hX (-s)
  have hlip' : ∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m ≤ Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹) := by
    have e : (fun h : GinfC Y => ‖α (k⁻¹ * h) - α h‖) = fun h : GinfC Y =>
        ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X (-s) * h)) - coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h)‖ := by
      funext h
      simp only [hα, Subgroup.coe_mul, hkinv]
    rw [e]
    simpa only [abs_neg] using hlip
  have hint : Integrable (fun h => ‖α (k⁻¹ * h) - α h‖) m := (hαk.sub hαi).norm
  have hnorm : ‖c‖ * ‖φ (x * k) - φ x‖ ≤ (∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m) * b := by
    rw [← norm_mul, hdiff, ← integral_mul_const]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun h => norm_nonneg _) (hint.mul_const b) (Filter.Eventually.of_forall fun h => ?_))
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc.ne
  have hH : 0 ≤ hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹) := Real.sqrt_nonneg _
  have key : ‖c‖ * ‖φ (x * k) - φ x‖ ≤ ‖c‖ * (Real.exp Q * b * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) := by
    refine hnorm.trans ?_
    calc (∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m) * b
        ≤ (Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) * b := mul_le_mul_of_nonneg_right hlip' hb0
      _ = ‖c‖ * (Real.exp Q * b * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) := by ring
  exact le_of_mul_le_mul_left key hc0

end GlobalTheory.SepPer.LipValue

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.CoreSum

variable {D : D7}

theorem orthogonalSumAuxiliaryVectors_gramProjection_retraction {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (hiso : (frameMat B A d.ι)ᴴ * B.gram * frameMat B A d.ι = A.gram) (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    (A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram)) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = y := by
  have h1 : A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram) * frameMat B A d.ι = 1 := by
    rw [Matrix.mul_assoc, hiso, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]
  have h2 : A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram) * d.a = 0 := by
    have := d.perp
    rw [cT_sig] at this
    rw [Matrix.mul_assoc, this, Matrix.mul_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

theorem orthogonalSumAuxiliaryVectors_middleCoefficient_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (hε : ε ≠ 0) (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c)
    (hp : p.1 + p.1 + 1 = c) (u : Fin c → D.host.E) (t : D.host.E) (e : d.a *ᵥ u = d.a *ᵥ Pi.single p t) : u p = t := by
  have g := d.gram
  rw [cT_sig] at g
  have e2 := congrArg (fun w => ((d.a)ᴴ * B.gram) *ᵥ w) e
  simp only [Matrix.mulVec_mulVec, g] at e2
  have e3 := congrFun e2 p
  have key : ∀ w : Fin c → D.host.E, (antiDiagonalSignGramMatrix c ε *ᵥ w) p = ε * w p := by
    intro w
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · simp only [antiDiagonalSignGramMatrix]
      rw [if_pos hp]
      simp
    · intro q _ hq
      have : ¬ (p.1 + q.1 + 1 = c) := fun h' => hq (Fin.ext (by omega))
      simp only [antiDiagonalSignGramMatrix]
      rw [if_neg this, zero_mul]
    · simp
  rw [key, key, Pi.single_eq_same] at e3
  exact mul_left_cancel₀ hε e3

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem besselCoreVertexLattice_eq_orthDecSumLattice (F : GlobalTheory.Asc.Frames G) (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) :
    lat0 F ρ h = GlobalTheory.Core.Rk.SumBox.sumLatO (F.oB ρ h) (G.Λ (.core (2 * ρ + 2)))
      (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  have lat2 : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hstair : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) ⟨ρ, by omega⟩ =
      G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹ := by
    unfold stairId
    rw [show 2 * ρ + 2 - 1 - ρ = ρ + 1 by omega]
  have hM := hF.aB ρ h
  have hz := hF.zB' ρ h
  ext x
  simp only [lat0, Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  rw [lat2]
  constructor
  · rintro ⟨y, hy, u, hu, hx⟩
    have hiso2 : (frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι)ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram *
        frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι = (G.V (.core (2 * ρ + 2))).gram := by
      rw [← hM, Matrix.conjTranspose_mul, ← (F.oB ρ h).isoA, ← (F.dB ρ h).iso]
      simp only [Matrix.mul_assoc]
    have hQ : (G.V (.core (2 * ρ + 2))).gram⁻¹ * ((frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι)ᴴ *
        (G.V (.grid (2 * ρ + 2) 0)).gram) * (F.dB ρ h).i₀ = (F.oB ρ h).qA := by
      rw [← hM, Matrix.conjTranspose_mul, OrthDec.qA, ← (F.dB ρ h).iso]
      simp only [Matrix.mul_assoc]
    have hqA : (F.oB ρ h).qA *ᵥ x = y := by
      rw [← hQ, ← Matrix.mulVec_mulVec, hx, orthogonalSumAuxiliaryVectors_gramProjection_retraction _ hiso2]
    have hline := F.line 0
    have hr : (negSp F.Lz).rank = 1 := hline.1
    let i0 : Fin (negSp F.Lz).rank := ⟨0, by rw [hr]; omega⟩
    have hsub : ∀ j : Fin (negSp F.Lz).rank, j = i0 := fun j => Fin.ext (by have := j.isLt; show j.1 = 0; omega)
    have hζ0 : F.ζ 0 i0 ≠ 0 := by
      intro h0
      apply hline.2
      have : F.ζ 0 = 0 := funext fun j => by rw [hsub j]; exact h0
      rw [this]
      simp
    have hqB : (F.oB ρ h).qB *ᵥ x = (((F.oB ρ h).qB *ᵥ x) i0 / F.ζ 0 i0) • F.ζ 0 := by
      funext j
      rw [hsub j, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hζ0]
    have hsplit : (F.oB ρ h).iA *ᵥ ((F.oB ρ h).qA *ᵥ x) + (F.oB ρ h).iB *ᵥ ((F.oB ρ h).qB *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, (F.oB ρ h).iA_qA_add, Matrix.one_mulVec]
    have hx2 : (F.dB ρ h).i₀ *ᵥ x = frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι *ᵥ y +
        (G.colDec (2 * ρ + 2) (by omega) h).a *ᵥ
          Pi.single ⟨ρ, by omega⟩ (((F.oB ρ h).qB *ᵥ x) i0 / F.ζ 0 i0) := by
      conv_lhs => rw [← hsplit, hqA, hqB]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, hz]
      funext i
      simp only [Matrix.mulVec_single, Pi.add_apply, Pi.smul_apply, Matrix.col_apply,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
      ring
    have ha := add_left_cancel (hx.symm.trans hx2)
    have hc := GlobalTheory.AscFin.CoreSum.orthogonalSumAuxiliaryVectors_middleCoefficient_eq (neg_ne_zero.2 one_ne_zero) _ ⟨ρ, by omega⟩ (by simp; omega) u _ ha
    have hcJ := hu ⟨ρ, by omega⟩
    rw [hc, hstair] at hcJ
    refine ⟨(F.oB ρ h).qA *ᵥ x, hqA ▸ hy, (F.oB ρ h).qB *ᵥ x, ?_, hsplit⟩
    rw [hqB]
    exact Submodule.subset_span ⟨_, hcJ, F.ζ 0, Submodule.mem_span_singleton_self _, rfl⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    refine Submodule.add_mem _ ⟨y, hy, 0, fun p => (stairId _ _ _ p).val.zero_mem, by simp⟩ ?_
    induction hb using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, w, hw, rfl⟩ := hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      refine ⟨0, Submodule.zero_mem _, Pi.single ⟨ρ, by omega⟩ (r • s), fun p => ?_, ?_⟩
      · by_cases hp : p = ⟨ρ, by omega⟩
        · subst hp
          rw [Pi.single_eq_same, hstair]
          exact Submodule.smul_mem _ r hs
        · rw [Pi.single_eq_of_ne hp]
          exact (stairId _ _ _ p).val.zero_mem
      · rw [Matrix.mulVec_zero, zero_add, ← algebraMap_smul D.host.E r (F.ζ 0), Matrix.mulVec_smul, Matrix.mulVec_smul, hz]
        funext i
        rw [Algebra.smul_def r s]
        simp only [Matrix.mulVec_single, Matrix.col_apply, MulOpposite.smul_eq_mul_unop, Pi.smul_apply, smul_eq_mul,
          MulOpposite.unop_op]
        ring
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hz hz'
    | smul r z _ hz =>
      rw [← algebraMap_smul D.host.E r z, Matrix.mulVec_smul, algebraMap_smul]
      exact Submodule.smul_mem _ r hz

theorem besselCoreVertexLattice_splitsAlongOrthDecomposition : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2)))
      (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v := by
  intro D T L sc G F hF ρ h v
  rw [besselCoreVertexLattice_eq_orthDecSumLattice F hF ρ h]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v

end GlobalTheory.AscFin.CoreSum
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.halfPoint_mem_sum_translate_of_annihilator : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ Z : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf e Z →
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1) →
    ∃ a ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∃ b ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), Z = e • a + actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • b) := by
  first | exact @GlobalTheory.AnnSum.ann_sum | exact GlobalTheory.AnnSum.ann_sum | (intros; apply GlobalTheory.AnnSum.ann_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.thetaLift_periods_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (G : GA D W → ℂ), RapidDec W G → (∀ (ρ : ℕ) (B : BesL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om B.V W), IsWeilDatumO ψ B.V W χ χ' om → ∀ φ, RapidDec B.A φ → Tame ψ B.V W fun Φ => B.per ψ φ (liftS om vW.μ vW.𝓕 G Φ)) ∧ ∀ (ρ : ℕ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om J.W W), IsWeilDatumO ψ J.W W χ χ' om → ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (χ₁ χ₂ : (AE D)ˣ →* Circle) (omz : Om J.W₀ L'), IsWeilDatumO ψ J.W₀ L' χ₁ χ₂ omz → ∀ φ Φ₀, RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ L' Φ₀ → Tame ψ J.W W fun Φ => J.per ψ ζ' omz φ (liftS om vW.μ vW.𝓕 G Φ) Φ₀ := by
  first | exact @GlobalTheory.LiftTame.lift_periods_tame | exact GlobalTheory.LiftTame.lift_periods_tame | (intros; apply GlobalTheory.LiftTame.lift_periods_tame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.placeModel_indicator_theta_fock_latticeVacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ f₀ : WO S T → ℂ, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel C.ψ (symplO S T) (heisO C.ψ S T) (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ L : AddSubgroup (WO S T), (∀ x ∈ L, IsHalf (cA D e) x) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) → IsSBHalf (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (GlobalTheory.LiftLevel.indL L) ∧ C.IsTh (Tm (GlobalTheory.LiftLevel.indL L)) ∧ C.IsFock B (Tm (GlobalTheory.LiftLevel.indL L)) ∧ ∀ Λ'' : AddSubgroup (WO S T), (∀ u ∈ Λ'', GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → IsLatVac (heisO C.ψ S T) Λ'' (Tm (GlobalTheory.LiftLevel.indL L)) := by
  first | exact @GlobalTheory.IndVac.indL_theta_fock_latVac | exact GlobalTheory.IndVac.indL_theta_fock_latVac | (intros; apply GlobalTheory.IndVac.indL_theta_fock_latVac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  first | exact @GlobalTheory.LiftLevel.PairTriv.pair_trivial | exact GlobalTheory.LiftLevel.PairTriv.pair_trivial | (intros; apply GlobalTheory.LiftLevel.PairTriv.pair_trivial <;> assumption)
end
