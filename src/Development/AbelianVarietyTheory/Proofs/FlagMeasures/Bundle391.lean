module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle359
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle351
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle361
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle380
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle381
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle095
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedColumnLatticeHasLevelAndDualGenerator
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle215
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle343
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFromLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle033
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle382
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle383
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.transport_rational_points : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) → (∀ γ : Gam X u, ∃ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ∧ (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ (∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ γ : Gam X u, (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E), (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g → sTil X wt (iotaI X u γ : X.B.I.Ginf) = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1 := by
  intro D X u wt ιA hW hA Φ hΦ
  have hmem : ∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro g hg
    refine Formalism.UG.P.bc_mem _ _ _ ?_ _ g hg
    ext x
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
  have key : ∀ (h : Hfin X u) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E) (g : GL (Fin (D.R.N 0)) D.host.E), X.B.I.fmat (h : X.B.I.Gf) = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE → ∀ hg : g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)), (Φ h).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g := by
    intro h γ₀ y₀ g hf hq hgy hg
    have hr := GlobalTheory.T.rational_matrix_represents_adelic_point_in_frame D X wt ιA hA h γ₀ y₀ hf hq ⟨_, hmem g hg⟩ (by
      show (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map _ = _
      rw [hgy])
    rw [(hΦ h _).1 hr]
  have hinj : ∀ g g' : GL (Fin (D.R.N 0)) D.host.E, Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g' → g = g' := by
    intro g g' h
    haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let v : HeightOneSpectrum (𝓞 D.host.F) :=
        ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩
      exact ⟨⟨0, 1, fun h => by
        have := congrArg (fun x : FiniteAdeleRing (𝓞 D.host.F) D.host.F => x v) h
        exact zero_ne_one (α := v.adicCompletion D.host.F) this⟩⟩
    have hc := congrArg Units.val h
    rw [Formalism.UG.P.bc_coe, Formalism.UG.P.bc_coe] at hc
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact Formalism.UG.P.inclE_injective D.host.F D.host.E _ (congrFun (congrFun hc i) j)
  refine ⟨fun γ => ?_, fun g hg => ?_, fun γ g hγg => ?_⟩
  · obtain ⟨γ₀, hu, -, hf, hfix⟩ := GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame D X u γ
    obtain ⟨y₀, hy, hq⟩ := GlobalTheory.T.rational_unitary_fixing_acts_on_complement_frame D X u wt hW γ₀ hu hfix
    obtain ⟨g, hgy⟩ := GlobalTheory.T.gramUnitary_firstHermitianSpace_isUnit D X u wt hW y₀ hy
    have hg : g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) :=
      (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g).2 (by
        have e : (y₀.map X.ιE).map X.ιE.symm = y₀ := Matrix.ext fun i j => by simp
        rw [hgy, e]; exact hy)
    exact ⟨g, hg, key (iotaF X u γ) γ₀ y₀ g hf hq hgy hg⟩
  · obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, y₀ = (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm := ⟨_, rfl⟩
    have hy := (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g).1 hg
    rw [← hy₀] at hy
    obtain ⟨γ₀, hu, hfix, hq⟩ := GlobalTheory.T.rational_unitary_extend_by_identity_on_fixSet D X u wt hW y₀ hy
    obtain ⟨γ, -, hf⟩ := GlobalTheory.T.rational_unitary_fixing_mem_rationalStabiliser D X u γ₀ hu hfix
    have hgy : (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE :=
      Matrix.ext fun i j => by simp [hy₀]
    exact ⟨γ, key (iotaF X u γ) γ₀ y₀ g hf hq hgy hg⟩
  · obtain ⟨γ₀, hu, hinf, hf, hfix⟩ := GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame D X u γ
    obtain ⟨y₀, hy, hq⟩ := GlobalTheory.T.rational_unitary_fixing_acts_on_complement_frame D X u wt hW γ₀ hu hfix
    obtain ⟨g', hgy⟩ := GlobalTheory.T.gramUnitary_firstHermitianSpace_isUnit D X u wt hW y₀ hy
    have hg' : g' ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) :=
      (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g').2 (by
        have e : (y₀.map X.ιE).map X.ιE.symm = y₀ := Matrix.ext fun i j => by simp
        rw [hgy, e]; exact hy)
    have e1 := key (iotaF X u γ) γ₀ y₀ g' hf hq hgy hg'
    have e2 : g = g' := hinj g g' (hγg.symm.trans e1)
    subst e2
    rw [hgy]
    exact GlobalTheory.T.realPlaces_frameMatrix_eq_rational_of_rational D X u wt hW _ γ₀ y₀ hinf hq
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameEps

theorem beps : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, b i = ιA X.ew • b i) ∧ ∀ i, bd i = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) • bd i := by
  intro D X u wt ιA hW hA c p b bd hb hbd
  have hinj := (GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA).2.2.1
  have semi : ∀ a x, embA X wt ιA (ιA a • x) = a • embA X wt ιA x := by
    intro a x
    simp only [embA, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, map_mul,
      RingEquiv.symm_apply_apply, mul_smul]
  constructor
  · intro i
    apply hinj
    rw [semi, hb, smul_comm X.ew, ← map_smul p X.ew, ← Matrix.mulVec_smul _ X.ew, ← X.bw_w i]
  · intro i
    apply hinj
    have hs : Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) = ιA (sigA X.B.I X.ew) :=
      (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA X.ew).symm
    rw [hs, semi, hbd, smul_comm (sigA X.B.I X.ew), ← map_smul p (sigA X.B.I X.ew),
      ← Matrix.mulVec_smul _ (sigA X.B.I X.ew), ← X.bwd_w i]

end GlobalTheory.St.G.FrameEps
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.TransportCong




theorem inModL_of_inMod_embA : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), InMod X.B.I X.B.g (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) (embA X wt ιA y) → InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  intro D X u wt ιA hW hA b bd y hy
  obtain ⟨h1, -, hinj, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA
  have hadd : ∀ x x', embA X wt ιA (x + x') = embA X wt ιA x + embA X wt ιA x' := by
    intro x x'; simp only [embA, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : D.host.E ⊗[D.host.F] Ad D.host.F) x,
      embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
    intro c x; simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  have hzero : embA X wt ιA 0 = 0 := by simp [embA]
  have hsub : ∀ x x', embA X wt ιA (x - x') = embA X wt ιA x - embA X wt ιA x' := by
    intro x x'
    have := hadd (x - x') x'
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have hS : (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) =
      embA X wt ιA '' (Set.range b ∪ Set.range bd) := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]; rfl
  have hspan : ∀ s ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) (embA X wt ιA '' (Set.range b ∪ Set.range bd)),
      ∃ s' ∈ Submodule.span (OAd D.host.F D.host.E) (Set.range b ∪ Set.range bd), embA X wt ιA s' = s := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨t, ht, rfl⟩ := hx; exact ⟨t, Submodule.subset_span ht, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, hzero⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      obtain ⟨s2, hs2, rfl⟩ := ihx'
      exact ⟨s1 + s2, Submodule.add_mem _ hs1 hs2, hadd _ _⟩
    | smul a x _ ihx =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      have ha : ιA (a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hA.2 a).1 a.2
      refine ⟨(⟨_, ha⟩ : OAd D.host.F D.host.E) • s1, Submodule.smul_mem _ _ hs1, ?_⟩
      rw [Subring.smul_def, hsmul, RingEquiv.symm_apply_apply, Subring.smul_def]
  have hmL : ∀ w ∈ mL X.B.I X.B.g, ∃ x ∈ X.B.I.Lf,
      w = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨x', hx', rfl⟩ := hx; exact ⟨x', hx', rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, (smul_zero _).symm⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      obtain ⟨a2, h2, rfl⟩ := ihx'
      exact ⟨a1 + a2, Submodule.add_mem _ h1 h2, (smul_add _ _ _).symm⟩
    | smul a x _ ihx =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      refine ⟨a • a1, Submodule.smul_mem _ _ h1, ?_⟩
      simp only [Subring.smul_def, smul_smul, mul_comm]
  unfold InMod at hy
  rw [hS] at hy
  obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp hy
  obtain ⟨s', hs', rfl⟩ := hspan s hs
  obtain ⟨x, hx, rfl⟩ := hmL w hw
  rw [X.g_eq] at hsw
  rcases Nat.eq_zero_or_pos (D.host.g 0 * D.host.g 1) with h0 | hpos
  · refine ⟨s', hs', 0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero, add_zero]
    apply hinj
    rw [← hsw, h0, Nat.cast_zero, zero_smul, add_zero]
  · have hu : IsUnit (((D.host.g 0 * D.host.g 1 : ℕ)) : D.host.E ⊗[D.host.F] Ad D.host.F) := by
      rw [← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')).map _
    obtain ⟨c, hc⟩ := hu
    refine ⟨s', hs', ((c⁻¹ : (D.host.E ⊗[D.host.F] Ad D.host.F)ˣ) : D.host.E ⊗[D.host.F] Ad D.host.F) • (y - s'), ?_, ?_⟩
    · rw [h1, hsmul, hsub, ← hsw, add_sub_cancel_left, smul_smul, ← map_natCast ιA.symm, ← hc,
        ← map_mul, Units.inv_mul, map_one, one_smul]
      exact hx
    · rw [smul_smul, ← hc, Units.mul_inv, one_smul, add_sub_cancel]

end GlobalTheory.St.G.TransportCong
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.DualMod

open Formalism.L2.SG.Pf.unitaryCongruence

section Gen

variable (I : AutInst)

theorem hform_mulVec_conj {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have hd : ∀ (J : Matrix n n A) (x y : n → A), Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
    intro J x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [hd, hd, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

theorem hA_unitary (x : I.Gf) (u v : VA I) : hA I (I.fmat x *ᵥ u) (I.fmat x *ᵥ v) = hA I u v := by
  have h : Formalism.UG.cT (sigA I) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  unfold hA
  rw [hform_mulVec_conj, h]

theorem zmod_add {g : ℕ} {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) :
    ZMod' I g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, add_mem hs ht, by ring⟩

theorem zmod_mul {g : ℕ} {a c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) (ha : ZMod' I g a) :
    ZMod' I g (c * a) := by
  obtain ⟨s, hs, rfl⟩ := ha
  exact ⟨c * s, mul_mem hc hs, by ring⟩

theorem zmod_zero (g : ℕ) : ZMod' I g 0 := ⟨0, zero_mem _, by simp⟩

theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by simp [hA, Formalism.UG.hform]
theorem hA_zero_right (y : VA I) : hA I y 0 = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_mL_left {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I m y) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_left, map_natCast]
    exact ⟨hA I x y, hA_int I hx hy, rfl⟩
  | zero => rw [hA_zero_left]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_left]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I ((c : I.E ⊗[I.F] Af I.F) • a) y)
    rw [hA_smul_left]; exact zmod_mul I (sigA_mem I c.2) ha

theorem hA_mL_right {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I y m) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_right]
    exact ⟨hA I y x, hA_int I hy hx, rfl⟩
  | zero => rw [hA_zero_right]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_right]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I y ((c : I.E ⊗[I.F] Af I.F) • a))
    rw [hA_smul_right]; exact zmod_mul I c.2 ha

theorem mL_le (g : ℕ) : mL I g ≤ I.Lf := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact I.Lf.nsmul_mem hx g

end Gen

theorem dual_mod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) → ∀ i j, ∃ t ∈ OAd D.host.F D.host.E, hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) (bd i) (b j) - (if i = j then ιA X.ew else 0) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) * t := by
  intro D X u wt ιA hW hι c p b bd hb hbd hm i j
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hι
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).1
  have hYd : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).2
  have hm1 : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j ∈ mL X.B.I X.B.g := by
    rw [hb j]; exact (hm j).1
  have hm2 : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g := by
    rw [hbd i]; exact (hm i).2
  have key : ZMod' X.B.I X.B.g
      (hA X.B.I (embA X wt ιA (bd i)) (embA X wt ιA (b j)) - if i = j then X.ew else 0) := by
    generalize hm' : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j = m' at hm1
    generalize hmm : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i = m at hm2
    have e1 : embA X wt ιA (b j) = X.B.I.fmat (X.xu u) *ᵥ X.bw j + m' := by rw [← hm']; abel
    have e2 : embA X wt ιA (bd i) = X.B.I.fmat (X.xu u) *ᵥ X.bwd i + m := by rw [← hmm]; abel
    rw [e1, e2, hA_add_left, hA_add_right, hA_add_right, hA_unitary]
    have e3 : hA X.B.I (X.bwd i) (X.bw j) + hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
        (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') - (if i = j then X.ew else 0) =
        (hA X.B.I (X.bwd i) (X.bw j) - (if i = j then X.ew else 0)) +
          hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
          (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') := by ring
    rw [e3]
    refine zmod_add _ (zmod_add _ (X.bw_dual i j) (hA_mL_right _ hm1 (hYd i)))
      (zmod_add _ (hA_mL_left _ hm2 (hY j)) (hA_mL_left _ hm2 (mL_le _ _ hm1)))
  obtain ⟨t, ht, he⟩ := key
  refine ⟨ιA t, (hι.2 t).1 ht, ?_⟩
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) =
      ιA (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [map_natCast, X.g_eq]
  have hif : (if i = j then ιA X.ew else 0) = ιA (if i = j then X.ew else 0) := by
    split_ifs <;> simp
  rw [← h2, hg, hif, ← map_sub, he, map_mul]

end GlobalTheory.St.G.DualMod
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem coefficient_map_exists_onto : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u F wt J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, J ξ = p := by
  intro D X u F wt hw
  obtain ⟨o, ho, hfr⟩ := GlobalTheory.T.exists_orthonormalFrame_complement_realPlaces D X u wt hw
  let e := Equiv.piCongrLeft (X.Vloc u) X.pl.symm
  have he : ∀ (x : ∀ τ, X.Vloc u (X.pl.symm τ)) τ, e x (X.pl.symm τ) = x τ := fun x τ =>
    Equiv.piCongrLeft_apply_apply (X.Vloc u) X.pl.symm x τ
  let tens : (∀ τ, X.Vloc u (X.pl.symm τ)) → X.Vpi u := fun x => X.tensU u (e x)
  have hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ := by
    intro x y
    show ⟪X.tensU u (e x), X.tensU u (e y)⟫_ℂ = _
    rw [X.tensU_inner, ← Equiv.prod_comp X.pl.symm]
    exact Finset.prod_congr rfl fun τ _ => by rw [he, he]
  have hsp : Submodule.span ℂ (Set.range tens) = ⊤ := by
    have : Set.range tens = Set.range (X.tensU u) := e.surjective.range_comp _
    rw [this]; exact X.tensU_span u
  have hty : ∀ τ, IsHCTypeU D.R.k (fun i => (((D.hcW u τ).u i : ℚ) : ℝ)) (X.piLoc u (X.pl.symm τ)) := by
    intro τ
    have h := X.piLoc_type u (X.pl.symm τ)
    rwa [X.pl.apply_symm_apply] at h
  obtain ⟨Jp, hJv, hJs, hJi, hJe⟩ := GlobalTheory.T.tensor_types_realPlaces_equiv_span_weylModules D.what₂.Tau D.R.k (D.R.N 0) D.R.N_zero.symm
    (Formalism.L2.Forms.lamT u 0) (fun τ i => (((D.hcW u τ).u i : ℚ) : ℝ))
    (fun τ i => GlobalTheory.hcParam_eq_weight_step_zero_add_rho D u τ i)
    (fun τ => X.Vloc u (X.pl.symm τ)) (fun τ => X.piLoc u (X.pl.symm τ)) hty (X.Vpi u) tens hin hsp
  have hoinv : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    have h := o.2 τ
    rw [Matrix.det_nonsing_inv]
    exact (Ring.inverse_unit h.unit ▸ (h.unit⁻¹).isUnit)
  have hmap := GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC D.what₂.Tau (D.R.N 0) (Formalism.L2.Forms.lamT u 0)
    (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D))
    (fun τ => (o.1 τ)⁻¹) hoinv
  let fo := Formalism.L2.Forms.fnOf (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D))
    (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0)) (fun τ => (o.1 τ)⁻¹)
  refine ⟨fo.comp Jp, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro s hs ξ y y' hyy
    obtain ⟨m, hm⟩ := hfr s hs
    have hA : ∀ x, X.piU u s (tens x) = tens (fun τ =>
        X.piLoc u (X.pl.symm τ) ((m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm)) (x τ)) := by
      intro x
      show X.piU u s (X.tensU u (e x)) = X.tensU u (e _)
      rw [X.tensU_equiv u s hs (e x)]
      congr 1
      funext v
      obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
      rw [he, he, (hm τ).2.1]
    have hy : Formalism.L2.Forms.IsTr (fun τ => o.1 τ * m τ * (o.1 τ)⁻¹) y' y := fun τ => by
      rw [hyy τ, (hm τ).2.2]
    exact hJe m (fun τ => (hm τ).1) (X.piU u s) hA _ o.1 (fun τ => o.2 τ) ξ y y' hy
  · intro ξ
    rw [← hmap]
    exact ⟨Jp ξ, hJv ξ, rfl⟩
  · intro c ξ η
    have hon : o.IsON := fun τ => Or.inl (ho τ)
    have hP : ∀ ζ, Jp ζ ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0) := fun ζ => by
      rw [← Formalism.L2.Forms.lamT_zero]; exact hJv ζ
    have h := F.val0.ipV c o hon (Jp ξ) (hP ξ) (Jp η) (hP η)
    rw [← Formalism.L2.Forms.lamT_zero] at h
    exact h.trans (hJi ξ η)
  · intro p hp
    rw [← hmap] at hp
    obtain ⟨P, hP, rfl⟩ := hp
    obtain ⟨ξ, rfl⟩ := hJs P hP
    exact ⟨ξ, rfl⟩

end GlobalTheory.St
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → TLat (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (Mq wt) ∧ ∃ x₀ ∈ X.Lb, (VS D).hT (X.zu u) x₀ = 1 ∧ ∃ d ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), Fintype.linearCombination D.host.E (qFr wt) d = x₀ + (((D.mem u).A.T : D.host.E))⁻¹ • X.zu u ∧ ∀ y ∈ dualL (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Mq wt), ∃ a : 𝓞 D.host.E, y - (a : D.host.E) • d ∈ Mq wt := by
  first | exact @GlobalTheory.St.G.mlat_main | exact GlobalTheory.St.G.mlat_main | (intros; apply GlobalTheory.St.G.mlat_main <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.WBlockExists

theorem nUnimodLoc : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  intro k r ε e f wf z0 z c hF hc hz
  exact n_unimodular_local k r ε e f wf z0 z c
    ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem realPlaceFunctionBlockExists_of_bessel_coef : BesselNVGap → CoefWeightedLoc → ∀ D : D7, GlobalTheory.St.WBlkExists D :=
  by
    intro hB hCW D hG A L Ps Rf Bu Pi Mu
    obtain ⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ := A
    exact Formalism.L2.SG.Pf.WFL.wblk_core quotient_product_compact
      Formalism.L2.SG.Pf.WFL.locHNProps_holds nUnimodLoc
      Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply hB hCW
      GlobalTheory.wlocExists_real (GlobalTheory.GapAtRealPlaces.gapBigOfGapHyp D)
      hG I ιE ιE_conj ιE_F bas J_eq L_eq pl φ_eq n_eq eps_eq L Ps Rf Bu Pi Mu

end GlobalTheory.WBlockExists
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localLatticeStabilisers_commensurable_almostEverywhere : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → (∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d) → ∀ (Λ₀ : LV D) (d0 : Dat Z FP), LocOver Λ₀ d0 → (∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ≠ 0 ∧ ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0) ∧ {p | (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype ≠ MulAction.stabilizer ↥(FP p).UW0 (d0 p)}.Finite ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → ∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d p)) ≠ 0 ∧ (MulAction.stabilizer ↥(FP p).UW0 (d p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0 ∧ GlobalTheory.HL.invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) = LocNG.Datum.wt (d0 p) (d p) := by
  first | exact @GlobalTheory.Unfold.LocStab.local_stabilisers | exact GlobalTheory.Unfold.LocStab.local_stabilisers | (intros; apply GlobalTheory.Unfold.LocStab.local_stabilisers <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.span_coefficientIdeal_eq_span_frameScale : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∀ (p : PlF D) (a : Fin D.R.rS), Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (GlobalTheory.RowLatXS.Ia Λ G.fl a : Set D.host.E)) = Submodule.span (Z.M p).L.O {frFac Z.δ p a.castSucc} := by
  first | exact @GlobalTheory.RowLatXS.span_coefIdeal_eq_span_frFac | exact GlobalTheory.RowLatXS.span_coefIdeal_eq_span_frFac | (intros; apply GlobalTheory.RowLatXS.span_coefIdeal_eq_span_frFac <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedFrame_congruent_unitriangular_at_primes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ)) := by
  first | exact @GlobalTheory.Unfold.GluedCong.glued_loc_cong | exact GlobalTheory.Unfold.GluedCong.glued_loc_cong | (intros; apply GlobalTheory.Unfold.GluedCong.glued_loc_cong <;> assumption)
end
