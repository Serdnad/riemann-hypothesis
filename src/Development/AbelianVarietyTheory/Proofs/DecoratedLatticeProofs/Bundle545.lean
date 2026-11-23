module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle541
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle526
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle490
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle542
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl.MovedVac

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin S₀.rank → AE D} (hz : z ∈ latA S₀ L₀ (· = v)) :
    d.j0 *ᵥ z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S₀ L₀ (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    refine smul_mem_latA ha ((hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩)
    · rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
      have : colMul d.jX i ((0 : Fin ρ → AE D) i) = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
      have : colMul d.jY i ((0 : Fin ρ → AE D) i) = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
      exact hy'm
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem wittExt_wittInc_core_hom_eq {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) (u : WO J.W₀ B.V₀) :
    J.d.ext0 B.V (B.d.inc0 J.W₀ u) = B.d.j0 * u * J.d.p0 := rfl

theorem wittExt_wittInc_mem_completed_hom_lattice {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) {LV : Lat J.W} {LV₀ : Lat J.W₀} {L : Lat B.V}
    {M : Lat B.V₀} {v : Pl D} (hV : IsSelfDualC J.W LV) (hV₀ : IsSelfDualC J.W₀ LV₀) (hL : IsSelfDualC B.V L)
    (hmV : MonoAt J.d LV LV₀ v) (hmW : MonoAt B.d L M v) {u : WO J.W₀ B.V₀}
    (hu : u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v)) :
    J.d.ext0 B.V (B.d.inc0 J.W₀ u) ∈ latO J.W B.V (LV : Set _) (L : Set _) (· = v) := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D J.W B.V LV L hV hL (· = v)]
  have hmx := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [wittExt_wittInc_core_hom_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (B.d.j0 * u * J.d.p0) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace B.d hmW (GlobalTheory.FinPl.LatMem.latO_maps hV₀ hu ((hmV y).1 hy).2.2)

theorem wittExt_wittInc_isHalf {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) {e : AE D} {u : WO J.W₀ B.V₀}
    (hu : IsHalf e u) : IsHalf e (J.d.ext0 B.V (B.d.inc0 J.W₀ u)) := by
  intro i j
  rw [wittExt_wittInc_core_hom_eq]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  linear_combination (B.d.j0 i k * J.d.p0 l j) * hu k l

end GlobalTheory.FinPl.MovedVac


open GlobalTheory.FinPl.MovedVac in
theorem GlobalTheory.FinPl.movedVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ γ ∈ grpAt B.V₀ (· = v), ∃ M : Lat B.V₀, IsSelfDualC B.V₀ M ∧ Moves B.V₀ γ LW₀ M (· = v) ∧ Vac ψ J.W₀ B.V₀ LV₀ M (· = v) (flatFB s (s.om (1, B.d.emb0 γ) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ v hA _ f hf γ _
  have hflat : IsFlatFB s (· = v) (flatFB s) := (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B s
  obtain ⟨M, hM, hMv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V₀ LW₀ hA.sdW₀).1 γ
  obtain ⟨L', hL', hL'v⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V LW hA.sdW).1 (B.d.emb0 γ)
  have hmono : MonoAt B.d L' M v :=
    (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V LW hA.sdW).2 B.V₀ σ B.d LW₀ M L' γ v hA.monoW (hMv _) (hL'v _)
  have h1 : Moves J.W 1 LV LV (· = v) := fun y _ => by
    rw [show mt J.W 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.one_mulVec]
  have hf' : Vac ψ J.W B.V LV L' (· = v) (s.om (1, B.d.emb0 γ) f) :=
    ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hA.sdV hA.sdW (· = v)
      (fun w hw => hw ▸ hA.tame) f).2.2 hf 1 (B.d.emb0 γ) LV L' hA.sdV hL' h1 (hL'v _))
  refine ⟨M, hM, hMv _, hflat.Heisenberg₂.theta _ hf'.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu2 : 2 • u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v) := nsmul_mem hu 2
    rw [← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu2), map_nsmul, map_nsmul]
    rw [hf'.2.1 _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu)]
  · rw [← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)]
    rw [hf'.2.2 e he _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu) (wittExt_wittInc_isHalf J B hh)]

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (hIJ : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro x hx
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
  have e : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V x) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V x)) := by
    ext i j
    simp
  rw [e, hx, map_one]

theorem grpOff_le_at (V : HSp D) {P : Pl D → Prop} {v : Pl D} (hv : P v) : grpOff V P ≤ grpOff V (· = v) := by
  apply congGrp_mono
  exact le_iInf fun w => iInf_le_of_le ⟨w.1, by rw [w.2]; exact hv⟩ le_rfl

theorem grpOff_eq_top (V : HSp D) {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : grpOff V P = ⊤ := by
  have hI : idOff D P = ⊤ := by
    haveI : IsEmpty {w : Pl D // P w} := ⟨fun w => hP ⟨w.1, w.2⟩⟩
    simp [idOff]
  rw [grpOff, hI, eq_top_iff]
  intro x _
  haveI : Subsingleton (AE D ⧸ (⊤ : Ideal (AE D))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Subsingleton.elim _ _

theorem grpAt_eq_bot (V : HSp D) {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : grpAt V P = ⊥ := by
  have h := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 V).2.2.1
  rwa [grpOff_eq_top V hP, inf_top_eq] at h

theorem latO_eq_bot (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : latO S T LS LT P = ⊥ := by
  rw [latO, AddSubgroup.closure_eq_bot_iff]
  rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
  have h0 : α = 0 := by
    exact RestrictedProduct.ext _ _ fun v => hα v fun h => hP ⟨v, h⟩
  subst h0
  ext i j
  simp only [pairA, Prod.mk_zero_zero, Matrix.of_apply, Matrix.zero_apply]
  exact TensorProduct.zero_tmul _ _

theorem heisO_zero_eq (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem suppFirst_holds (D : D7) : SuppFirst D := by
  intro ψ ρ B J s LV LV₀ LW LW₀ P hgood hunr hsdW Φ hΦ
  refine ⟨?_, fun g hg => ⟨?_, ?_⟩⟩
  · intro κ κ' hκ hκ'
    by_cases hP : ∃ v, P v
    · obtain ⟨v, hv⟩ := hP
      exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ B.V J.W s.χV s.χW s.om s.weil LV LW (hgood v hv).sdV hsdW P
        (fun w hw => ⟨(hgood w hw).tame, (hunr w hw).1, (hunr w hw).2⟩) Φ hΦ κ κ' hκ hκ'
    · have h1 : κ = 1 := Subgroup.mem_bot.mp (grpAt_eq_bot B.V hP ▸ hκ.1)
      have h2 : κ' = 1 := Subgroup.mem_bot.mp (grpAt_eq_bot J.W hP ▸ hκ'.1)
      subst h1 h2
      rw [Prod.mk_one_one, map_one]
      rfl
  · intro h hne
    refine GlobalTheory.T.placewise_to_adelicDecomposition_forall D J.W LW P hsdW (jacGrp J.d) h ?_
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 J.W).1 h
    refine ⟨x, hx, y, hy, rfl, ?_⟩
    have hsdV := (hgood v hv).sdV
    have htameP : ∀ w, P w → Tame D w := fun w hw => (hgood w hw).tame
    have htame1 : ∀ w : Pl D, w = v → Tame D w := fun w hw => hw ▸ htameP v hv
    have hΦv : Vac ψ B.V J.W LV LW (· = v) Φ :=
      ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hsdV hsdW P htameP Φ).1.mp hΦ).2 v hv
    have hf : Vac ψ B.V J.W LV LW (· = v) (s.om (g, y) Φ) :=
      (GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hsdV hsdW (· = v) htame1 Φ).2.1 hΦv g
        (grpOff_le_at B.V hv hg) y hy
    refine (GlobalTheory.T.oneCoset_besselToFourierJacobi D ψ ρ B J s LV LV₀ LW LW₀ v (hgood v hv) (hunr v hv) (flatBF s)
      ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).1 ρ B J s) _ hf).2 x hx ?_
    have e : s.om (1, x) (s.om (g, y) Φ) = s.om (g, x * y) Φ := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact hne
  · intro h hh
    by_cases hP : ∃ v, P v
    · obtain ⟨v₀, hv₀⟩ := hP
      have htameP : ∀ w, P w → Tame D w := fun w hw => (hgood w hw).tame
      have hvacP := GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V J.W s.χV s.χW s.om s.weil LV LW (hgood v₀ hv₀).sdV hsdW P htameP
      have hf : Vac ψ B.V J.W LV LW P (s.om (g, h) Φ) := (hvacP Φ).2.1 hΦ g hg h hh
      refine ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ (hgood v₀ hv₀).sdV₀ (hgood v₀ hv₀).sdW₀ P
        htameP _).1.mpr ⟨?_, ?_⟩)
      · exact ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂.theta _ hf.1
      · intro v hv
        have hfv := ((hvacP _).1.mp hf).2 v hv
        exact (GlobalTheory.T.oneCoset_besselToFourierJacobi D ψ ρ B J s LV LV₀ LW LW₀ v (hgood v hv) (hunr v hv) (flatBF s)
          ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).1 ρ B J s) _ hfv).1
    · refine ⟨((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂.theta _ (s.weil.om_pres _ _ hΦ.1), ?_⟩
      rw [latO_eq_bot _ _ _ _ hP]
      refine ⟨fun u hu => ?_, fun e _ u hu _ => ?_⟩
      · rw [AddSubgroup.mem_bot.mp hu, nsmul_zero, heisO_zero_eq]
      · rw [AddSubgroup.mem_bot.mp hu, heisO_zero_eq]

end GlobalTheory.FinPl

theorem GlobalTheory.FinPl.suppFirst_all : ∀ D : D7, GlobalTheory.FinPl.SuppFirst D := GlobalTheory.FinPl.suppFirst_holds
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepCell.LeftOne

theorem vac_empty_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {LS : Lat S} {LT : Lat T} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => False) f) : Vac ψ S T LS LT (fun _ => False) (comb ψ S T e f) :=
  ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).2 LS LT f hf

theorem vac_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT (fun _ => False) f := by
  have h := (GlobalTheory.DisjComb.main D ψ hψ S T (fun _ => True) (fun _ => False) (fun _ _ h => h)).2.2.2.2 LS LT f hS hT
  have e : (fun p : Pl D => True ∨ False) = fun _ => True := by funext p; simp
  rw [e] at h
  exact (h.1 hf).2

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (r * q₁) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv _ hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f _ r hr q₁ q₂
  have s0 := hv.sd j (by omega)
  have s1 := hv.sd (j + 1) (by omega)
  have s2 := hv.sd (j + 1 + 1) (by omega)
  have t₁ := (vac_empty_comb hc.std (hv.atG j).1 (vac_empty_comb hc.std (hF.atQ j).1 (vac_empty hc.std s0 s1 h₁))).1
  have t₂ := (vac_empty_comb hc.std (hv.atG (j + 1)).1
    (vac_empty_comb hc.std (hF.atQ (j + 1)).1 (vac_empty hc.std s1 s2 h₂))).1
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  have key := (GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ t₁ t₂ (φ α)
    (hv.ram j (φ α) (hφ α)).1 g q₁ q₂).1 r hr
  exact congrArg (fun z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ z (rTrans q₂ f)) key

end GlobalTheory.DStepCell.LeftOne
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem _root_.GlobalTheory.T.thetaChain_steps_positive_multiple_of_LValue : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → GlobalTheory.Core.Rk.SW.HeckeFormNS D → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  first | exact @GlobalTheory.ChainTw.scalars_of_given_all | exact GlobalTheory.ChainTw.scalars_of_given_all | (intros; apply GlobalTheory.ChainTw.scalars_of_given_all <;> assumption)
end
