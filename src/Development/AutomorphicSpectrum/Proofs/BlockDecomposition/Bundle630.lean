module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle621
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocGoodProof

section Generic

variable {G G' : Type} [Group G] [Group G']

theorem mem_twCent_prodMap (θ : G →* G) (θ' : G' →* G') (δ g : G × G') :
    g ∈ twCent (θ.prodMap θ') δ ↔ g.1 ∈ twCent θ δ.1 ∧ g.2 ∈ twCent θ' δ.2 := by
  change g * δ = δ * (θ.prodMap θ') g ↔ g.1 * δ.1 = δ.1 * θ g.1 ∧ g.2 * δ.2 = δ.2 * θ' g.2
  exact Prod.ext_iff

theorem mul_norm_comm (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) {δ g : G} (hg : g ∈ twCent θ δ) :
    g * (δ * θ δ) = δ * θ δ * g := by
  have h : g * δ = δ * θ g := hg
  have h' : θ g * θ δ = θ δ * g := by
    have := congrArg θ h
    simpa only [map_mul, hθ] using this
  rw [← mul_assoc, h, mul_assoc, h', mul_assoc]

variable [TopologicalSpace G] [TopologicalSpace G']

theorem isCompact_closure_zpowers_of_map [T2Space G'] (φ : G →* G') (hφ : Continuous φ) (t : G)
    (ht : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (φ t) : Set G')) := by
  have hC := ht.image hφ
  refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem cptPart_le_prod [T2Space G] [T2Space G'] [ContinuousMul G] [ContinuousMul G'] (S : Subgroup (G × G'))
    (T : Subgroup G) (T' : Subgroup G') (hS : ∀ g ∈ S, g.1 ∈ T ∧ g.2 ∈ T') :
    cptPart S ≤ (cptPart T).prod (cptPart T') := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨htS, htc⟩
  exact ⟨Subgroup.subset_closure ⟨(hS t htS).1,
      isCompact_closure_zpowers_of_map (MonoidHom.fst G G') continuous_fst t htc⟩,
    Subgroup.subset_closure ⟨(hS t htS).2,
      isCompact_closure_zpowers_of_map (MonoidHom.snd G G') continuous_snd t htc⟩⟩

theorem good_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G)
    (K' : Subgroup G') (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (ho' : IsOpen (K' : Set G'))
    (hc' : IsCompact (K' : Set G')) (δ : G × G')
    (hcomm : ∀ a b, a ∈ twCent θ δ.1 → b ∈ twCent θ δ.1 → a * b = b * a)
    (hcomm' : ∀ a b, a ∈ twCent θ' δ.2 → b ∈ twCent θ' δ.2 → a * b = b * a)
    (H : Subgroup G) (H' : Subgroup G') (hH : IsCompact (H : Set G)) (hH' : IsCompact (H' : Set G'))
    (hP : cptPart (twCent θ δ.1) ≤ H) (hP' : cptPart (twCent θ' δ.2) ≤ H') :
    PositivityTheory.Rg.BcB.G8.Fin.Good (θ.prodMap θ') (K.prod K') δ := by
  have hmem := fun g => mem_twCent_prodMap θ θ' δ g
  have hKo : IsOpen ((K.prod K' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact ho.prod ho'
  have hKc : IsCompact ((K.prod K' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact hc.prod hc'
  have hHc : IsCompact ((H.prod H' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact hH.prod hH'
  have hle : cptPart (twCent (θ.prodMap θ') δ) ≤ H.prod H' :=
    (cptPart_le_prod _ _ _ fun g hg => (hmem g).1 hg).trans (Subgroup.prod_mono hP hP')
  refine ⟨fun g hg g' hg' => ?_, fun x => ⟨GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj _ hKc x),
    GlobalTheory.LocFin.relIndex_cptPart_ne_zero _ _ _ (GlobalTheory.LocFin.isOpen_map_conj _ hKo x) hHc hle⟩⟩
  obtain ⟨ga, gb⟩ := (hmem g).1 hg
  obtain ⟨ga', gb'⟩ := (hmem g').1 hg'
  exact Prod.ext (hcomm _ _ ga ga') (hcomm' _ _ gb gb')

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_nrmL_comm (hU : Unr E) (n : ℕ) (w : Pl E) {y g : GLw n w} (hg : g ∈ twCent (thL n w) y) :
    g * nrmL n w y = nrmL n w y * g := by
  have hinv := (GlobalTheory.BCT.ThBasic.twist_basic E hU n w).2.1
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    rw [h1] at hg
    have h : g * y = y * g := hg
    simpa only [nrmL, if_pos hs] using h
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    rw [h1] at hg hinv
    simpa only [nrmL, if_neg hs] using mul_norm_comm _ hinv hg

theorem twCent_comm (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (g h : GLw n w) (hg : g ∈ twCent (thL n w) y) (hh : h ∈ twCent (thL n w) y) : g * h = h * g := by
  have key : ∀ {u : GLw n w}, u ∈ twCent (thL n w) y → Commute (nrmL n w y).val u.val := fun {u} hu => by
    have := congrArg Units.val (mul_nrmL_comm hU n w hu)
    rw [Units.val_mul, Units.val_mul] at this
    exact this.symm
  exact Units.ext (GlobalTheory.BCT.CentComm.commute_of_commute_separable hy (key hg) (key hh)).eq

theorem cptPart_le_compact (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hs : (nrmL n w y).val.charpoly.Separable) :
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  set M := nrmL n w y with hM
  set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN
  have hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g := by
    intro g hg
    have := congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq
    simpa [Units.val_mul] using this
  have hadj : ∀ g : GLw n w, Commute g M →
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N} :=
    fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)
  have hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h := by
    intro g h hg hh
    have h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hval g hg
    exact Units.ext (by simpa [Units.val_mul] using h1.eq)
  let S : Set (GLw n w) := {g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}
  let H0 : Subgroup (GLw n w) :=
    { carrier := S
      one_mem' := by
        refine ⟨Commute.one_left M, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
        exact isCompact_singleton
      mul_mem' := by
        intro g h hg hh
        refine ⟨hg.1.mul_left hh.1, ?_⟩
        have hK := hg.2.mul hh.2
        refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
        rintro x ⟨k, rfl⟩
        simp only
        rw [(hcomm g h hg.1 hh.1).mul_zpow]
        exact Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)
      inv_mem' := by
        intro g hg
        refine ⟨hg.1.inv_left, ?_⟩
        show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))
        rw [Subgroup.zpowers_inv]
        exact hg.2 }
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin E w n N hs
  have hB := GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace E w n c
  have hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
    intro g hg
    have hg' : g⁻¹ ∈ H0 := H0.inv_mem hg
    intro i j
    exact ⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j,
      hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩
  refine ⟨H0.topologicalClosure, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe]
    exact hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)
  · refine le_trans ?_ (Subgroup.le_topologicalClosure H0)
    rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, htc⟩
    exact ⟨mul_nrmL_comm hU n w ht, htc⟩

theorem good_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable) :
    PositivityTheory.Rg.BcB.G8.Fin.Good ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) y := by
  obtain ⟨ho₁, hc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨ho₂, hc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  obtain ⟨H₁, hH₁, hP₁⟩ := cptPart_le_compact hU a w y.1 h₁
  obtain ⟨H₂, hH₂, hP₂⟩ := cptPart_le_compact hU b w y.2 h₂
  exact good_prod (G := GLw a w) (G' := GLw b w) (thL a w) (thL b w) (GlobalTheory.LFun.KGL w (n := a)) (GlobalTheory.LFun.KGL w (n := b))
    ho₁ hc₁ ho₂ hc₂ y (twCent_comm hU a w y.1 h₁) (twCent_comm hU b w y.2 h₂) H₁ H₂ hH₁ hH₂ hP₁ hP₂

theorem locGood : PositivityTheory.Rg.BcB.G8.Fin.LocGood := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact good_pair hU a b w y h₁ h₂

end GlobalTheory.CompanionTheory.LocGoodProof

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.UnipCocompact

open GlobalTheory.UnipFlagCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem unipMin_eq_radSet (X : Matrix (Fin n) (Fin r) E) :
    unipMin σ J X = radSet σ J X Fin.val := by
  ext u
  constructor
  · rintro ⟨B, hB, hd, hX, hz⟩
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * (B - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      exact congrArg (· - adMat F X) hX
    refine ⟨fun i => ⟨fun j => (B - 1) j i, fun j hij => ?_, ?_⟩, hz⟩
    · rcases (Fin.le_def.2 hij).eq_or_lt with e | e
      · subst e; simp [hd]
      · simp [hB e, e.ne']
    · funext k
      exact congrFun (congrFun e k) i
  · rintro ⟨h1, h2⟩
    choose a ha ha' using h1
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * Matrix.of (fun j i => a i j) := by
      ext k i
      exact congrFun (ha' i) k
    refine ⟨1 + Matrix.of (fun j i => a i j), fun i j hij => ?_, fun i => ?_, ?_, h2⟩
    · have hij' : j < i := hij
      simp [ha j i hij'.le, hij'.ne']
    · simp [ha i i le_rfl]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul]
      exact (add_sub_cancel _ _).symm

theorem closure_radSet_subset (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {X : Matrix (Fin n) (Fin r) E}
    (hC : LinearIndependent E Xᵀ) (h0 : cT (σ : E →+* E) X * J * X = 0) {g : HA (AF F) σ J}
    (hg : g ∈ Subgroup.closure (radSet σ J X Fin.val)) : g ∈ radSet σ J X Fin.val := by
  obtain ⟨L, hL, hLL⟩ := exists_dual hσ hJ X hC h0
  have hd : ∀ j : Fin r, (j : ℕ) < r := fun j => j.2
  have he := idem_complete hσ hJ X L hL h0 hLL
  have hs := fam_st (adj_mul hσ hJ) (adj_adj hσ hJ) (idem (F := F) X L) (Fin.val : Fin r → ℕ) r
  have h1 := GlobalTheory.TwoStepUnipotent.st_one (adj_mul hσ hJ) (adj_adj hσ hJ)
  rw [mem_radSet_iff hσ hJ X L hL h0 hLL hd]
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (mem_radSet_iff hσ hJ X L hL h0 hLL hd x).1 hx
  | one => exact (sub_self (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).symm ▸ zero_mem _
  | mul x y _ _ hx hy =>
    have e : (HA.mat _ σ J (x * y)).1 = (HA.mat _ σ J x).1 * (HA.mat _ σ J y).1 := rfl
    rw [e]
    generalize (HA.mat _ σ J x).1 = a at hx ⊢
    generalize (HA.mat _ σ J y).1 = b at hy ⊢
    have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
  | inv x _ hx =>
    have := raise_st (adj_mul hσ hJ) (adj_adj hσ hJ) hs 0 hx
    rwa [map_sub, adj_mat hσ hJ, h1] at this

theorem linearIndependent_of_isWittFrame (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) : LinearIndependent E Xᵀ := by
  have e : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT' hσ hJ, cT_gram hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  refine Matrix.mulVec_injective_iff.1 fun v w h => ?_
  have := congrArg ((cT (σ : E →+* E) Y * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] using this

theorem unipMin_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ u ∈ unipMin σ J X, ∃ δ ∈ ratPts σ J, δ ∈ unipMin σ J X ∧ ∃ c ∈ C, c ∈ unipMin σ J X ∧ u = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  have hσ := sigma_sigma h
  have hC := linearIndependent_of_isWittFrame hσ hJ hW
  obtain ⟨K, hK, hcov⟩ := closure_radSet_cocompact hσ hJ X hC hW.xx Fin.val
  have hsub : ∀ g : Subgroup.closure (radSet σ J X Fin.val), g.1 ∈ unipMin σ J X := fun g => by
    rw [unipMin_eq_radSet]
    exact closure_radSet_subset hσ hJ hC hW.xx g.2
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun u hu => ?_⟩
  rw [unipMin_eq_radSet] at hu
  obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨u, Subgroup.subset_closure hu⟩
  exact ⟨γ.1, hγ, hsub γ, k.1, ⟨k, hk, rfl⟩, hsub k, congrArg Subtype.val e⟩

end GlobalTheory.CompanionTheory.UnipCocompact
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.matrix_preserves_integers_almost_all : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ x : ι → Fv F v, (∀ i, (A.map (algebraMap F (Fv F v))).mulVec x i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff | exact GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff | (intros; apply GlobalTheory.CompanionTheory.MatInt.exists_finset_mulVec_integral_iff <;> assumption)
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.TailProd

theorem term_mono {ι : Type} [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι)
    (hτ : Summable (fun v => |τ v - 1|)) (hp : Summable (fun v => |p v - 1|))
    (hM0 : ∀ v, 0 ≤ Mv v) (hτ0 : ∀ v, 0 ≤ τ v) (hp0 : ∀ v, 0 ≤ p v)
    (hle : ∀ v, v ∉ S → τ v * p v ≤ Mv v) :
    Monotone (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) := by
  intro S₁ S₂ h12
  have hU : S ∪ S₁ ⊆ S ∪ S₂ := Finset.union_subset_union_right h12
  dsimp only
  rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι τ (S ∪ S₁) (S ∪ S₂) hτ hU,
    GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι p (S ∪ S₁) (S ∪ S₂) hp hU]
  have hX : ∏ v ∈ (S ∪ S₂) \ S, Mv v =
      (∏ v ∈ (S ∪ S₁) \ S, Mv v) * ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    have hD : ((S ∪ S₂) \ S) \ ((S ∪ S₁) \ S) = (S ∪ S₂) \ (S ∪ S₁) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [← Finset.prod_sdiff (Finset.sdiff_subset_sdiff hU (Finset.Subset.refl S)), hD, mul_comm]
  have hΔ : (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), τ v) * (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), p v) ≤
      ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun v _ => mul_nonneg (hτ0 v) (hp0 v))
      (fun v hv => hle v (fun hvS => (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ hvS)))
  have hX1 : 0 ≤ ∏ v ∈ (S ∪ S₁) \ S, Mv v := Finset.prod_nonneg fun v _ => hM0 v
  have hT : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, τ v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => τ v.1)
      (hτ.comp_injective Subtype.val_injective)).2.2.2 fun v => hτ0 v.1
  have hP : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, p v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => p v.1)
      (hp.comp_injective Subtype.val_injective)).2.2.2 fun v => hp0 v.1
  rw [hX]
  set X := ∏ v ∈ (S ∪ S₁) \ S, Mv v
  set D := (S ∪ S₂) \ (S ∪ S₁)
  set T := ∏' v : {v // v ∉ S ∪ S₂}, τ v.1
  set P := ∏' v : {v // v ∉ S ∪ S₂}, p v.1
  calc X * ((∏ v ∈ D, τ v) * T * ((∏ v ∈ D, p v) * P))
      = X * ((∏ v ∈ D, τ v) * (∏ v ∈ D, p v)) * (T * P) := by ring
    _ ≤ X * (∏ v ∈ D, Mv v) * (T * P) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ hX1) (mul_nonneg hT hP)

theorem iSup_partial_mul_tails : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι),
    Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) →
    (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) →
    ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) =
      ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  intro ι _ Mv τ p S hMs hτs hps hM0 hτ0 hp0 hle
  have hmono := GlobalTheory.CompanionTheory.TailProd.term_mono Mv τ p S hτs hps hM0 hτ0 hp0 hle
  have hg : Tendsto (fun S' : Finset ι => S ∪ S') atTop atTop :=
    tendsto_atTop_mono (fun S' => (Finset.subset_union_right : S' ⊆ S ∪ S')) tendsto_id
  have hM := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one Mv hMs).comp hg
  have hT := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one τ hτs).comp hg
  have hP := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one p hps).comp hg
  have hlim : Tendsto (fun S' : Finset ι => (∏' v : {v // v ∉ S}, Mv v.1) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * (∏' v : {v // v ∉ S ∪ S'}, p v.1) /
        ∏' v : {v // v ∉ S ∪ S'}, Mv v.1)) atTop (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    have := (tendsto_const_nhds (x := ∏' v : {v // v ∉ S}, Mv v.1)).mul
      ((hT.mul hP).div hM one_ne_zero)
    simpa only [Function.comp_def, Pi.div_apply, mul_one, div_one] using this
  have hA : Tendsto (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) atTop
      (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    refine hlim.congr' ?_
    filter_upwards [hM.eventually_ne one_ne_zero] with S' hS'
    dsimp only [Function.comp] at hS' ⊢
    rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι Mv S (S ∪ S') hMs Finset.subset_union_left,
      mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hS']
  exact iSup_eq_of_tendsto (fun a b h => ENNReal.ofReal_le_ofReal (hmono h))
    ((ENNReal.continuous_ofReal.tendsto _).comp hA)

end GlobalTheory.CompanionTheory.TailProd
end
