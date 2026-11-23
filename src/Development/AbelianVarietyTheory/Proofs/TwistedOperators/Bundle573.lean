module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle200
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionIntertwinesWeilUpToCharacter
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle563
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle566
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle472
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle564
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle565
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipRes

theorem res_unip : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (n : NI V C) (f : WO V W → ℂ), IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω ((n : GA D V), 1) f) = res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ n f hf
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hs
  obtain ⟨a, haQ, haC, haB, haC'⟩ := GlobalTheory.T.exists_rationalLevi_scaling_isotropicFrame D V V' r C C' B hs h1 h2 h3
  obtain ⟨l, hl⟩ := GlobalTheory.T.thetaRestriction_invariant_rationalLeviScaling D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hμ
  have hp : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (ω p f) := hω.om_pres
  have hm : ∀ x y : GA D V, ∀ f, ω (x * y, 1) f = ω (x, 1) (ω (y, 1) f) := by
    intro x y f
    rw [show ((x * y, 1) : GA D V × GA D W) = (x, 1) * (y, 1) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ g ∈ NI V C, ∀ f, IsThetaFunO ψ V W f →
      res V V' W C B μ 𝓨 (ω (g, 1) f) = res V V' W C B μ 𝓨 f := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hx1, hx2, hx3⟩ := hx
      obtain ⟨m, hmN, rfl⟩ := GlobalTheory.T.unipotent_levi_matrix_action_identity D V V' r C C' B hs h1 h2 h3 a haC haB haC' x hx1 hx2 hx3
      obtain ⟨c, hc⟩ := GlobalTheory.T.unipotentRadical_stabiliser_scales_restriction D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ m hmN
      intro f hf
      have e1 : res V V' W C B μ 𝓨 (ω (a, 1) (ω (a⁻¹, 1) (ω (m⁻¹, 1) f))) = res V V' W C B μ 𝓨 (ω (m⁻¹, 1) f) := by
        rw [← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
      have e2 : res V V' W C B μ 𝓨 (ω (m, 1) (ω (m⁻¹, 1) f)) = res V V' W C B μ 𝓨 f := by
        rw [← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
      rw [hm, hm, hm, hl _ (hp _ _ (hp _ _ (hp _ _ hf))), hc _ (hp _ _ (hp _ _ hf)), smul_smul, mul_comm,
        ← smul_smul, ← hl _ (hp _ _ (hp _ _ hf)), e1, ← hc _ (hp _ _ hf), e2]
    | one => intro f hf; rw [show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
    | mul x y _ _ hx hy => intro f hf; rw [hm, hx _ (hp _ _ hf), hy _ hf]
    | inv x _ hx =>
      intro f hf
      have := hx (ω (x⁻¹, 1) f) (hp _ _ hf)
      rw [← this, ← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
  exact key n n.2 f hf
end GlobalTheory.UnipRes
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wittTowerRestriction_intertwines_weil_upToCharacter : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ c : GA D W →* Circle, ∀ h f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (res V V' W C B μ 𝓨 f) := by
  first | exact @GlobalTheory.TowerRestrictScalar.main | exact GlobalTheory.TowerRestrictScalar.main | (intros; apply GlobalTheory.TowerRestrictScalar.main <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem suppPl_emb {D : D7} (V : HSp D) (v : FinPl D) (k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.WeilParts.SuppPl (pairA D.host.F 0 (singleV D.host.F v 1)) V (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k) := by
  intro i j
  let t₁ := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := D.host.E) (R' := AF D.host.F)
    (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl)
  let t₂ := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := D.host.E) (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v)
  have key : ∀ x, t₁ (t₂ 1) * t₁ (t₂ x) = t₁ (t₂ x) := fun x => by rw [← map_mul, ← map_mul, one_mul]
  change t₁ (t₂ 1) * (((1 - t₁ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      t₁ ((1 - t₂ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j + t₂ ((HA.mat _ _ _ k).1 i j))) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
    ((1 - t₁ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      t₁ ((1 - t₂ 1) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j + t₂ ((HA.mat _ _ _ k).1 i j))) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j
  by_cases e : i = j
  · subst e
    simp only [Matrix.one_apply_eq, mul_one, map_add (f := _), map_sub]
    linear_combination key ((HA.mat _ _ _ k).1 i i) - key 1
  · simp only [Matrix.one_apply_ne e, mul_zero, zero_add, sub_zero]
    exact key _

theorem emb_keeps_latHat {D : D7} (V : HSp D) {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hL : L.FG)
    (v : FinPl D) {k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v} (hk : k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram L v) (y) :
    y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k)).mulVec y ∈
        latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) := by
  have h := GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  rw [GlobalTheory.AdelicU.levelOff_eq] at h
  exact (GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ hL _).1 h.2 y

theorem inertVacuumFixed : ∀ D : D7, InertVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hns : GlobalTheory.WeilParts.NonSplitAt D v (pairA D.host.F 0 (singleV D.host.F v 1)) := ⟨hε, hv⟩
  refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩)
     hW v _ hns uS uT _ _
    (suppPl_emb S v k) (suppPl_emb T v k')
    (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T ΛS ΛT hS hT v _ hε _ _
      (emb_keeps_latHat S hS.1.fg v hk) (emb_keeps_latHat T hT.1.fg v hk')) f hf fun u hu => ?_
  obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hns
  have h1 : 2 • (a • u) = u := by
    rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
  have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
  rwa [h1] at h2

end GlobalTheory.PlaceTensor

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceModelOnto

variable {D : D7}

theorem isSBHalf_zero {m n : ℕ} (a : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf a Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem isSBHalf_smul {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf a Λ Φ) : IsSBHalf a Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (hne t ht), k, hk,
    fun u hu hu' t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hu' t], fun t ht => h3 t (hne t ht)⟩

theorem isSBHalf_add {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf a Λ Φ) (h' : IsSBHalf a Λ Ψ) : IsSBHalf a Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have hne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf a u → IsHalf a (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (hh _ _ hu') t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (hh _ _ hu') t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem placeModel_onto_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (a : AE D), IsSplitIdem D a → a + cA D a = idem D (.inl v) → (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧ ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → (∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ)) ∧ ∀ x, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x := by
  first
  | exact @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | (apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local ..)

end GlobalTheory.PlaceModelOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceTensor.GenPair

theorem exists_pairing {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (G : BoundedContinuousFunction Z ℂ) :
    ∃ L : BoundedContinuousFunction Z ℂ →L[ℂ] ℂ, ∀ F, L F = ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν := by
  have hint : ∀ F : BoundedContinuousFunction Z ℂ, MeasureTheory.Integrable (fun w => F w * (starRingEnd ℂ) (G w)) ν :=
    fun F => (F * star G).integrable ν
  refine ⟨LinearMap.mkContinuous
    { toFun := fun F => ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν
      map_add' := fun F F' => by
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint F) (hint F')
      map_smul' := fun c F => by
        simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ } ((ν Set.univ).toReal * ‖G‖) fun F => ?_, fun F => rfl⟩
  have hb : ∀ w, ‖F w * (starRingEnd ℂ) (G w)‖ ≤ ‖F‖ * ‖G‖ := fun w => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (F.norm_coe_le_norm w) (G.norm_coe_le_norm w) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hb)
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc _ ≤ ‖F‖ * ‖G‖ * (ν Set.univ).toReal := by simpa [Measure.real] using this
    _ = _ := by ring

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.DefLift GlobalTheory.DefLift.Gen

theorem blk_sub_vecL {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} (Y : O → Matrix (Fin m) (Fin m) ℂ)
    (X : O → Matrix (Fin n) (Fin n) ℂ) (τ' : O) (u : Matrix (Fin m) (Fin n) ℂ) :
    (GlobalTheory.RealWeil.blk Y (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) X) *ᵥ
                 vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) =
      vecL (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext p
  obtain ⟨⟨i, j⟩, τ⟩ := p
  have key : ∀ (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ)
      (v : (Fin m × Fin n) × O → ℂ), (GlobalTheory.RealWeil.blk b a *ᵥ v) ((i, j), τ) = (b τ * cpt v τ * a τ) i j :=
    fun b a v => by rw [← cpt_blk]; rfl
  have hc : cpt (vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ)) τ = (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) τ := rfl
  rw [Matrix.sub_mulVec, Pi.sub_apply, key, key, hc]
  show _ = (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) τ i j
  by_cases h : τ = τ'
  · subst h
    simp
  · simp [h]

open scoped Classical

variable {D : D7} {θ : InfFam D}

theorem oneP_zero (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : oneP θ V τ X 0 = 1 := by
  have h := GlobalTheory.Mem.Lift.oneP_add hθ hX 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem oneP_inv (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel]
  exact GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX

theorem hasDerivAt_mM (hθ : IsInfFam θ) {S T : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hX : X ∈ lieAt S τ) {Y : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hY : Y ∈ lieAt T τ) (k l : GlobalTheory.RealWeil.Ix S T) :
    HasDerivAt (fun t : ℝ => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t) k l)
      ((GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X) :
        Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) k l) 0 := by
  obtain ⟨⟨i, j⟩, τ₁⟩ := k
  obtain ⟨⟨i', j'⟩, τ₂⟩ := l
  have hS : ∀ t : ℝ, (oneP θ S τ X t)⁻¹ = oneP θ S τ X (-t) := GlobalTheory.PlaceTensor.GenPair.oneP_inv hθ hX
  simp only [mM_apply, hS, GlobalTheory.RealWeil.blk, Matrix.sub_apply, Matrix.blockDiagonal_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h : τ₁ = τ₂
  · subst h
    simp only [if_true]
    have hb := hasDerivAt_comp hθ hY τ₁ i i'
    have ha0 := hasDerivAt_comp hθ hX τ₁ j' j
    have ha : HasDerivAt (fun t : ℝ => Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X t)) j' j)
        ((Pi.single τ X : D.what₂.Tau → _) τ₁ j' j) (-0) := by rw [neg_zero]; exact ha0
    have hT0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt T (oneP θ T τ Y 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]; exact compAt_fin (one_mem _) τ₁
    have hS0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX]; exact compAt_fin (one_mem _) τ₁
    refine (hb.mul (ha.scomp 0 (hasDerivAt_neg 0))).congr_deriv ?_
    simp only [Function.comp_apply, neg_zero, hT0, hS0, Matrix.one_apply]
    split_ifs <;> simp <;> ring
  · simp only [h, if_false, sub_zero]
    exact hasDerivAt_const _ _

theorem exists_generator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (τ : D.what₂.Tau), ∀ X ∈ lieAt S τ, ∀ Y ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (Y * u - u * X) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, oneP θ T τ Y t) f w) (Gn f w) 0) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g, IsThetaFunO ψ S T g → HasDerivAt (fun t : ℝ => ipO μ 𝓕 (om (oneP θ S τ X t, oneP θ T τ Y t) f) g) (ipO μ 𝓕 (Gn f) g) 0 := by
  intro D ψ θ S T χS χT om hW hθ τ X hX Y hY
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hweak : GlobalTheory.Ker.IsWeak ψ S T om := GlobalTheory.Ker.isWeak_of_datum hW
  have hcont : OmCont ψ S T om := hW.om_cont
  have hγc : Continuous fun t : ℝ => (oneP θ S τ X t, oneP θ T τ Y t) :=
    (GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
  have hγa : ∀ s t : ℝ, (oneP θ S τ X (s + t), oneP θ T τ Y (s + t)) =
      (oneP θ S τ X s, oneP θ T τ Y s) * (oneP θ S τ X t, oneP θ T τ Y t) := fun s t => by
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY]; rfl
  have hγm : ∀ t : ℝ, oneP θ S τ X t ∈ GinfC S ∧ oneP θ T τ Y t ∈ GinfC T := fun t =>
    ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩
  obtain ⟨lam, hlam⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ hσ ψ hψ S T om hweak hcont
    (fun t => (oneP θ S τ X t, oneP θ T τ Y t)) hγc hγa hγm _
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  have h0 : mM θ S T (oneP θ S τ X 0, oneP θ T τ Y 0) = 1 := by
    rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX, GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]
    exact (mM θ S T).map_one
  have hlie := GlobalTheory.Mem.Lift.GenZero.lie_of_path (HM S T)
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X))
    (fun t => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t)) h0 (fun t => mM_unitary hθ _)
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  obtain ⟨Gn, hGn⟩ := GlobalTheory.DefLift.Gen.exists_extension hσ hψ
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) lam
  refine ⟨Gn, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    ⟨GlobalTheory.RealWeil.toB hψ f hf, GlobalTheory.RealWeil.coe_toB hψ f hf⟩
  obtain ⟨hnt, hGF⟩ := hGn F hf
  have hAt : IsThetaFunO ψ S T ((nOp (rhoV hψ σ S T) (HM S T)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
      + lam • F).1 : WO S T → ℂ) := by
    rw [← GlobalTheory.DefLift.Gen.coe_add_smul]
    exact GlobalTheory.OrientedHeis.theta_add hnt (GlobalTheory.OrientedHeis.theta_smul lam hf)
  have hcomm : ∀ (τ' : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u F.1) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn F.1) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ'
        ((Pi.single τ Y : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) τ' * u -
          u * (Pi.single τ X : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) τ') F.1 := by
    intro τ' u
    have hdt := GlobalTheory.DefLift.Gen.theta_dH hσ hψ F hf
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    have e2 := (hGn _ hdt).2
    have e4 := nOp_add_comm HM_herm HM_det hlie (isHeis_rhoB hσ hψ) lam
      (GlobalTheory.RealWeil.sm_of_theta hσ hψ F hf) (GlobalTheory.RealWeil.sm_of_theta hσ hψ _ hnt)
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    rw [← GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' u, e2, hGF, ← GlobalTheory.DefLift.Gen.coe_dH hσ hψ _ hAt τ' u, e4,
      GlobalTheory.PlaceTensor.GenPair.blk_sub_vecL, GlobalTheory.DefLift.Gen.coe_add_sub]
    exact GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' _
  obtain ⟨u, hu1, hu2⟩ := hlam F hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hGF]; exact hAt
  · intro v
    rw [hcomm, Pi.single_eq_same, Pi.single_eq_same]
  · intro τ' h v
    have hc := hcomm τ' v
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.zero_mul, Matrix.mul_zero, sub_zero,
      GlobalTheory.DefLift.Gen.dRho_zero hσ hψ F hf] at hc
    exact sub_eq_zero.mp hc
  · intro w
    have h2 : HasDerivAt (fun t => ev _ _ w (u t)) (ev _ _ w (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F)) 0 :=
      ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [ev_apply, hu1] at h2
    rw [hGF]; exact h2
  · intro μ 𝓕 hμ g hg
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
      rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨L, hL⟩ := GlobalTheory.PlaceTensor.GenPair.exists_pairing (μ.restrict 𝓕) (GlobalTheory.RealWeil.toB hψ g hg).1
    have h2 : HasDerivAt (fun t => L (u t).1) (L (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F).1) 0 :=
      ((L.comp (BB ψ S T).subtypeL).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [hL, hu1, GlobalTheory.RealWeil.coe_toB] at h2
    rw [hGF]; exact h2

end GlobalTheory.PlaceTensor.GenPair

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaFunction_splitProductDatum_isPureTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (ι : Type) (s : Finset ι) (v : ι → FinPl D) (a : ι → AE D), (∀ i ∈ s, IsSplitIdem D (a i) ∧ a i + cA D (a i) = idem D (.inl (v i))) → Set.InjOn v s → ∀ Φ : ι → WO S T → ℂ, (∀ i ∈ s, IsSBHalf (a i) (latO S T ΛS ΛT fun _ => True) (Φ i)) → ∀ (x : Place D → WO S T → ℂ) (f Ψ : WO S T → ℂ), (∀ i ∈ s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i) (x (.inl (v i)))) → (∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → x p = f₀) → (∀ t, IsHalf (∑ i ∈ s, a i) t → Ψ t = ∏ i ∈ s, Φ i (a i • t)) → (∀ t, ¬ IsHalf (∑ i ∈ s, a i) t → Ψ t = 0) → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i ∈ s, a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ Ψ f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  first | exact @GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure | exact GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure | (intros; apply GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite ∧ ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  first | exact @GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod | exact GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod | (intros; apply GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.standardPairFirst_invariant_congruenceOne : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  first | exact @GlobalTheory.StdFstInv.stdFst_actO | exact GlobalTheory.StdFstInv.stdFst_actO | (intros; apply GlobalTheory.StdFstInv.stdFst_actO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

theorem _root_.GlobalTheory.T.exists_thetaFunction_standardPairSecond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A' WW : HSp D) (rA' : Rig A') (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (vac : WO A' WW → ℂ), rA'.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ A' WW rA'.s rW.s rA'.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D e) (latO A' WW rA'.Λ rW.Λ fun _ => True) 1 vac (stdSnd ν e I a A' WW rA'.β rW.β) f ∧ IsThetaFunO ψ A' WW f := by
  first | exact @GlobalTheory.CompanionTheory.StdSndTheta.exists_theta | exact GlobalTheory.CompanionTheory.StdSndTheta.exists_theta | (intros; apply GlobalTheory.CompanionTheory.StdSndTheta.exists_theta <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilOperator_fixes_latticeVacuum_nonsplit_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ (g : GA D S) (h : GA D T), SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → om (g, h) f₀ = f₀ := by
  first | exact @GlobalTheory.InertVac.om_fixes_latVac | exact GlobalTheory.InertVac.om_fixes_latVac | (intros; apply GlobalTheory.InertVac.om_fixes_latVac <;> assumption)
end
