module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

theorem _root_.GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff : ∀ (D : D7) (v : Pl D) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ a : AE D, a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) ε * a = a) ∧
    (∀ a : AE D, a ∈ idAt D (· ≠ v) → algebraMap (AF D.host.F) (AE D) ε * a = 0) := by
  first | exact @GlobalTheory.FinPl.placeIdem_acts | exact GlobalTheory.FinPl.placeIdem_acts | (intros; apply GlobalTheory.FinPl.placeIdem_acts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.unitaryAdelicTrivialAtPlacesSubgroup_antitone : ∀ (D : D7) (S : HSp D) (P Q : Pl D → Prop), (∀ v, Q v → P v) → grpOff S P ≤ grpOff S Q := by
  first | exact @GlobalTheory.FinPl.grpOff_anti | exact GlobalTheory.FinPl.grpOff_anti | (intros; apply GlobalTheory.FinPl.grpOff_anti <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplecticPairing_latticeAway_supportedAt_place_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop), ¬ P p.v → ∀ u ∈ latO S T MS MT P, ∀ x : WO S T, (∀ i j, (p.e + cA D p.e) * x i j = x i j) → symplO S T u x = 0 := by
  first | exact @GlobalTheory.FinPl.OffSympl.symplO_off_eq_zero | exact GlobalTheory.FinPl.OffSympl.symplO_off_eq_zero | (intros; apply GlobalTheory.FinPl.OffSympl.symplO_off_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology

theorem _root_.GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset : ∀ (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S), (∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) → Filter.Tendsto x Filter.atTop (nhds κ) := by
  first | exact @GlobalTheory.AdelicLimit.tendsto_of_agree | exact GlobalTheory.AdelicLimit.tendsto_of_agree | (intros; apply GlobalTheory.AdelicLimit.tendsto_of_agree <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneCosetEmb

theorem wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (P : Pl D → Prop) (g : GA D S₀), g ∈ grpAt S₀ P → d.emb0 g ∈ grpAt S P := fun _ _ _ _ d _ _ hg => GlobalTheory.IwaPlace.wittCoreEmbedding_preserves_supportedUnitarySubgroup d hg

end GlobalTheory.OneCosetEmb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), MxAt P u → (u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) P, ψ (symplO S T u u') = 1) := by
  first | exact @GlobalTheory.SelfDualAt.latO_ann_at | exact GlobalTheory.SelfDualAt.latO_ann_at | (intros; apply GlobalTheory.SelfDualAt.latO_ann_at <;> assumption)
end

section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData ValuativeRel IsLocalRing Matrix

theorem _root_.GlobalTheory.T.gluedLattice_finite_expansions_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ), χ ≠ 1 → ∀ (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsFullLattice k], (∀ P : Pair k n', latInd (gluedS q 1 P.ker P.vec) Λ = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ • (tensCol (latInd P.ker Λ) (vecInd Λ) + ∑ Q ∈ withLat Λ, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) ∧ latInd P.ker Λ + ∑ Q ∈ withLat Λ, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) = ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat Λ) ∧ (∀ R : Pair k n', latInd Λ (gluedS q 1 R.ker R.vec) = tensRow (latInd Λ R.ker) (dualInd Λ) + ∑ Q ∈ withLat Λ, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) ∧ ∀ (L : Submodule 𝒪[k] (n' → k)) [L.IsFullLattice k], latInd Λ (lastKer L) = tensRow (latInd Λ L) (dualInd Λ) ∧ latInd Λ (lastPair q L).lat = tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
  intro k _ _ _ _ n n' _ _ _ _ q χ hχ Λ _
  refine ⟨fun P => ⟨GlobalTheory.GluedExp.glued_col q χ hχ Λ P,
    GlobalTheory.GluedExp.glued_sum q χ hχ Λ P⟩, GlobalTheory.GluedExp.glued_row q Λ, ?_⟩
  intro L _
  have hlast : latInd Λ (lastPair q L).lat =
      tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
    classical
    funext x
    rw [tensRow, GlobalTheory.GluedExp.coset_total, latInd, latInd, ite_zero_mul_ite_zero, mul_one]
    have hm (v : n' ⊕ Fin 1 → k) :
        v ∈ (lastPair q L).lat ↔ v ∘ Sum.inl ∈ L ∧ q.1 • v (Sum.inr 0) ∈ 𝒪[k] := by
      rw [Pair.mem_lat_iff]
      simp only [GlobalTheory.LastSteps.lastPair_hasVal]
      constructor
      · rintro ⟨a, h, s, hs, -⟩
        exact ⟨h, hs ▸ s.2⟩
      · rintro ⟨h, hs⟩
        exact ⟨_, h, ⟨_, hs⟩, rfl, rfl⟩
    refine if_congr ⟨fun h => ⟨fun y hy => ((hm _).1 (h y hy)).1, fun y hy => ?_⟩,
      fun h y hy => (hm _).2 ⟨h.1 y hy, ?_⟩⟩ rfl rfl
    · rw [smul_dotProduct]
      exact ((hm _).1 (h y hy)).2
    · have hη := h.2 y hy
      rw [smul_dotProduct] at hη
      exact hη
  exact ⟨GlobalTheory.GluedExp.last_ker Λ L, hlast⟩
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RatioAA

variable {D : D7}

theorem incA_mul_tmul (b : D.host.E) (p : AF D.host.F) (z : D.host.E) :
    incA D b * (p ⊗ₜ[D.host.F] z) = p ⊗ₜ[D.host.F] (b * z) := by
  show (1 ⊗ₜ[D.host.F] b) * (p ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem colMul_add {m n : ℕ} (x : Mx D m n) (l : Fin n) (c c' : AE D) :
    colMul x l (c + c') = colMul x l c + colMul x l c' := by
  funext k; simp [colMul, add_mul]

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (l : Fin n) (b c : AE D) :
    (fun k => b * colMul x l c k) = colMul x l (b * c) := by
  funext k; simp [colMul, mul_assoc]

theorem mul_mem_latMul {S : HSp D} {𝔞 𝔟 : Set D.host.E} {L L' : Lat S} {P : Pl D → Prop} (b : D.host.E)
    (h : ∀ a ∈ 𝔞, ∀ x ∈ L, ∃ a' ∈ 𝔟, ∃ x' ∈ L', ∀ i, b * (a * x i) = a' * x' i)
    {y : Fin S.rank → AE D} (hy : y ∈ latMul S 𝔞 L P) : (fun i => incA D b * y i) ∈ latMul S 𝔟 L' P := by
  let f : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := (AddMonoidHom.mulLeft (incA D b)).compLeft (Fin S.rank)
  have hle : latMul S 𝔞 L P ≤ (latMul S 𝔟 L' P).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hs, a, ha, x, hx, rfl⟩
    obtain ⟨a', ha', x', hx', e⟩ := h a ha x hx
    refine AddSubgroup.subset_closure ⟨α, hα, hs, a', ha', x', hx', ?_⟩
    funext i
    show incA D b * _ = _
    rw [incA_mul_tmul, e]
  exact hle hy

theorem latV_to_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {α : D.host.E} (hα : α ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => incA D α * y i) ∈ latA S L P :=
  mul_mem_latMul α (fun a ha x hx => ⟨α, hα, x, hx, fun i => by rw [Set.mem_singleton_iff.1 ha]; ring⟩) hy

theorem latA_to_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} (hAA : D.host.AA ≠ 0) {β : D.host.E}
    (hβ : β ∈ D.host.AA⁻¹) {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : (fun i => incA D β * y i) ∈ latV S L P := by
  refine mul_mem_latMul β (fun a ha x hx => ?_) hy
  have hm : β * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [← inv_mul_cancel₀ hAA]; exact FractionalIdeal.mul_mem_mul hβ ha
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  refine ⟨1, rfl, o • x, L.smul_mem o hx, fun i => ?_⟩
  rw [Pi.smul_apply, Algebra.smul_def, ho]; ring

theorem latA_eq_zero (hAA : D.host.AA = 0) {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latA S L P) : y = 0 := by
  have hle : latA S L P ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hs, a, ha, x, hx, rfl⟩
    have ha0 : a = 0 := by
      have : a ∈ D.host.AA := ha
      rw [hAA] at this; exact (FractionalIdeal.mem_zero_iff _).1 this
    funext i
    simp [ha0]
  simpa using hle hy

theorem idAt_eq_zero_of_AA (hAA : D.host.AA = 0) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    (LV : Lat V) (LW : Lat W) (v : Pl D) (hsdV : IsSelfDualC V LV) (hC : ColsAt dV dW.jX LV LW v) (i : Fin ρ)
    (a : AE D) (ha : a ∈ idAt D (· = v)) : a = 0 := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  set ε := pairA D.host.F 0 (singleV D.host.F v 1) with hεdef
  obtain ⟨N, hN, -, hNL⟩ := GlobalTheory.LatAlmostStd.exists_commensurable LV
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V LV hsdV)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 D.host.E))
    (fun k => dV.e k i)
  choose o ho using hb
  set x : Fin V.rank → D.host.E := ∑ k, Pi.single k (N • ((o k : 𝓞 D.host.E) : D.host.E)) with hxdef
  have hx : x ∈ LV := sum_mem fun k _ => hNL k (o k)
  have hxk : ∀ k, x k = N • (((b : 𝓞 D.host.E) : D.host.E) * dV.e k i) := by
    intro k
    rw [hxdef, Finset.sum_apply, Finset.sum_eq_single k (fun l _ hl => Pi.single_eq_of_ne' hl _)
      (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same]
    congr 1
    rw [show ((o k : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (o k) from rfl, ho k]
    first | rfl | exact Algebra.smul_def _ _
  set t : D.host.E := N • ((b : 𝓞 D.host.E) : D.host.E) with htdef
  set c : AE D := ε ⊗ₜ[D.host.F] t with hcdef
  have hc : c ∈ idAt D (· = v) := GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _
  have hyc : colMul dV.jX i c ∈ latV V LV (· = v) := by
    refine AddSubgroup.subset_closure ⟨_, hs.1, hs.2, 1, rfl, x, hx, ?_⟩
    funext k
    rw [one_mul, hxk k]
    show c * incA D (dV.e k i) = _
    rw [mul_comm, incA_mul_tmul, htdef]
    congr 1
    rw [mul_smul_comm, mul_comm (dV.e k i)]
  have hW := latA_eq_zero hAA ((hC i c hc).1 hyc)
  have hc0 : c = 0 := by
    have hpX : dW.pX * dW.jX = 1 := by
      change (dW.e'ᴴ * W.gram).map (incA D) * dW.e.map (incA D) = 1
      rw [← Matrix.map_mul, dW.e'e]
      exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
    have h1 := congrFun (congrFun hpX i) i
    rw [Matrix.one_apply_eq, Matrix.mul_apply] at h1
    rw [← mul_one c, ← h1, Finset.mul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := congrFun hW k
    simp only [colMul, Pi.zero_apply] at this
    rw [mul_comm (dW.pX i k), ← mul_assoc, this, zero_mul]
  have ht : t ≠ 0 := by
    rw [htdef]
    refine smul_ne_zero hN ?_
    exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hεc : algebraMap (AF D.host.F) (AE D) ε = c * incA D t⁻¹ := by
    rw [hcdef, mul_comm, incA_mul_tmul, inv_mul_cancel₀ ht]; rfl
  rw [← ((placeIdem_acts D v ε hp).1 a).1 ha, hεc, hc0, zero_mul, zero_mul]

end GlobalTheory.FinPl.RatioAA


open GlobalTheory.FinPl.RatioAA in
theorem GlobalTheory.FinPl.ratio_of_colsAt : ∀ (D : D7) (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i j : Fin ρ) (r : AE D), r ∈ idAt D (· = v) → (∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (r * a) ∈ latV V LV (· = v)) → ∀ a ∈ idAt D (· = v), colMul dW.jX j a ∈ latV W LW (· = v) → colMul dW.jX i (r * a) ∈ latV W LW (· = v) := by
  intro D V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v _ hsdV _ _ _ hC i j r hr H a ha hja
  by_cases hAA : D.host.AA = 0
  · rw [idAt_eq_zero_of_AA hAA dV dW LV LW v hsdV hC i a ha, mul_zero]
    have : colMul dW.jX i (0 : AE D) = 0 := by funext k; simp [colMul]
    rw [this]; exact zero_mem _
  · have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹, colMul dW.jX i (incA D t * (r * a)) ∈ latV W LW (· = v) := by
      intro t ht
      refine FractionalIdeal.mul_induction_on ht (fun α hα β hβ => ?_) (fun x y hx hy => ?_)
      · have h1 := latV_to_latA hα hja
        rw [colMul_mul] at h1
        have hαa : incA D α * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha
        have h2 := (hC j _ hαa).2 h1
        have h3 := H _ h2
        have h4 := (hC i _ (Ideal.mul_mem_left _ r hαa)).1 h3
        have h5 := latA_to_latV hAA hβ h4
        rw [colMul_mul] at h5
        convert h5 using 2
        rw [map_mul]; ring
      · rw [map_add (f := _), add_mul, colMul_add]; exact add_mem hx hy
    have := key 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    simpa using this
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.FinPl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinPl.NotIntAt

variable {D : D7}

def trAt (D : D7) (v : Pl D) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] Fv D.host.F v :=
  (evalV D.host.F v).toLinearMap ∘ₗ (TensorProduct.rid D.host.F (Af D.host.F)).toLinearMap ∘ₗ
    LinearMap.lTensor (Af D.host.F) (Algebra.trace D.host.F D.host.E)

theorem trAt_tmul (v : Pl D) (a : Af D.host.F) (x : D.host.E) :
    trAt D v (a ⊗ₜ[D.host.F] x) =
      algebraMap D.host.F (Fv D.host.F v) (Algebra.trace D.host.F D.host.E x) * evalV D.host.F v a := by
  simp [trAt, Algebra.smul_def]

theorem algebraMap_int_mem (v : Pl D) (r : 𝓞 D.host.F) :
    algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (r : D.host.F)
  erw [this]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_le_one r

theorem trAt_int (v : Pl D) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    trAt D v y ∈ v.adicCompletionIntegers D.host.F := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hle : intAE D ≤ (v.adicCompletionIntegers D.host.F).toSubring.toAddSubgroup.comap
      (trAt D v).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    change trAt D v (a ⊗ₜ[D.host.F] (x : D.host.E)) ∈ v.adicCompletionIntegers D.host.F
    rw [trAt_tmul]
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (x : D.host.E)) :=
      Algebra.isIntegral_trace x.isIntegral_coe
    exact mul_mem (algebraMap_int_mem v ⟨_, hint⟩) (ha v)
  exact hle hy

theorem evalV_single_same (v : Pl D) (y : Fv D.host.F v) : evalV D.host.F v (singleV D.host.F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v y

theorem evalV_single_ne (v : Pl D) (y : Fv D.host.F v) {w : Pl D} (hw : w ≠ v) :
    evalV D.host.F w (singleV D.host.F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) y hw

theorem inv_not_mem (v : Pl D) {π : 𝓞 D.host.F} (hπ : π ∈ v.asIdeal) (hπ0 : π ≠ 0) :
    (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹ ∉ v.adicCompletionIntegers D.host.F := by
  intro h
  have hv : Valued.v (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F)) < 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (π : D.host.F)
    erw [this]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem π).2 hπ
  have hne : algebraMap D.host.F (Fv D.host.F v) (π : D.host.F) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hπ0
  have h1 : Valued.v ((algebraMap D.host.F (Fv D.host.F v) (π : D.host.F)) *
      (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h)) hv
  rw [mul_inv_cancel₀ hne, map_one] at h1
  exact lt_irrefl _ h1

theorem exists_not_intAt : ∀ (D : D7) (v : Pl D), ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := by
  intro D v
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set n : ℕ := Module.finrank D.host.F D.host.E
  have hn : (n : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  set c : Fv D.host.F v := (algebraMap D.host.F (Fv D.host.F v) ((n : D.host.F) * (π : D.host.F)))⁻¹
  refine ⟨pairA D.host.F 0 (singleV D.host.F v c) ⊗ₜ[D.host.F] (1 : D.host.E),
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (P := (· = v))
      (fun w hw => evalV_single_ne v c hw) 1, fun h => ?_⟩
  have h2 := trAt_int v h.2
  change trAt D v (singleV D.host.F v c ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ _ at h2
  have htr : Algebra.trace D.host.F D.host.E 1 = (n : D.host.F) := by
    simpa using Algebra.trace_algebraMap (R := D.host.F) (S := D.host.E) 1
  rw [trAt_tmul, evalV_single_same, htr] at h2
  have e : algebraMap D.host.F (Fv D.host.F v) (n : D.host.F) * c =
      (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹ := by
    simp only [c, map_mul, map_natCast, mul_inv, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [e] at h2
  exact inv_not_mem v hπ hπ0 h2

end GlobalTheory.FinPl.NotIntAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField

theorem _root_.GlobalTheory.T.splitPlaceCharacter_conductor_integers : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), IsStdChar D ψ (-1) → p.IsChar ψ χ → p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1 := by
  first | exact @GlobalTheory.SplitCharCond.hasConductor_one | exact GlobalTheory.SplitCharCond.hasConductor_one | (intros; apply GlobalTheory.SplitCharCond.hasConductor_one <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.TensSB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type}

theorem of_tensCol_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (ha : a ≠ 0) : Ψ ∈ SB (Matrix n n' k) := by
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, a y₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact ha (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun x₀ : Matrix n n' k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y₀ i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => x.submatrix id Sum.inl) ?_ (by fun_prop) (fun x₀ => rfl)
  · have e : Ψ = (a y₀)⁻¹ • fun x₀ : Matrix n n' k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y₀ i) j) := by
      funext x₀
      show Ψ x₀ = (a y₀)⁻¹ * (Ψ x₀ * a y₀)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_id.matrix_elem i j
    · exact continuous_const

theorem of_tensRow_mem {Ψ : Matrix n n' k → ℂ} {b : (n' → k) → ℂ}
    (h : tensRow Ψ b ∈ SB (Matrix (n ⊕ Fin 1) n' k)) (hb : b ≠ 0) : Ψ ∈ SB (Matrix n n' k) := by
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨η₀, hη₀⟩ : ∃ η₀, b η₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hb (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun x₀ : Matrix n n' k => Matrix.of fun i j => Sum.elim (fun i => x₀ i j) (fun _ => η₀ j) i)
    (s := fun x : Matrix (n ⊕ Fin 1) n' k => x.submatrix Sum.inl id) ?_ (by fun_prop) (fun x₀ => rfl)
  · have e : Ψ = (b η₀)⁻¹ • fun x₀ : Matrix n n' k =>
        tensRow Ψ b (Matrix.of fun i j => Sum.elim (fun i => x₀ i j) (fun _ => η₀ j) i) := by
      funext x₀
      show Ψ x₀ = (b η₀)⁻¹ * (Ψ x₀ * b η₀)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · exact continuous_id.matrix_elem i j
    · exact continuous_const

end GlobalTheory.FinPl.TensSB

namespace GlobalTheory.FinPl

theorem tens_SB_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k) → a ≠ 0 → Ψ ∈ SB (Matrix n n' k)) ∧
    (∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), Ψ ∈ SB (Matrix n' n k) → b ∈ SB (n → k) → tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) ∧
    (∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k) → b ≠ 0 → Ψ ∈ SB (Matrix n' n k)) := by
  intro k _ _ _ _ n n' _ _ _ _
  exact ⟨fun Ψ a hΨ ha => Comm.tensCol_mem hΨ ha, fun Ψ a h ha => TensSB.of_tensCol_mem h ha,
    fun Ψ b hΨ hb => Comm.tensRow_mem hΨ hb, fun Ψ b h hb => TensSB.of_tensRow_mem h hb⟩

end GlobalTheory.FinPl

end
end
