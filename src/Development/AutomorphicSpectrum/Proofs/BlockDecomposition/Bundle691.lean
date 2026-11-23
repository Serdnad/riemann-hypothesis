module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle675
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle007
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle002
public import Development.WeilBound.ThetaLifts.Reductions.JoinDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle004
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle008
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.Reductions.ArchimedeanMatchedMapsCompare
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle302
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle686
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle684
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle688
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle001
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001

@[expose] public section

section

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.First

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in
theorem form_eq_hE (u v : Fin n → E) :
    toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J u v = hE σ J u v := by
  simp only [toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe, hE, Formalism.UG.hform]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem hE_mulVec {m : Matrix (Fin n) (Fin n) E} (hm : cT (σ : E →+* E) m * J * m = J) (u : Fin n → E) :
    hE σ J (m *ᵥ u) (m *ᵥ u) = hE σ J u u := by
  have e : Matrix.of (fun a (_ : Fin 1) => (m *ᵥ u) a) = m * Matrix.of (fun a (_ : Fin 1) => u a) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h1 := gram_apply (σ := σ) (J := J) (s := 1) (r := 1) (Matrix.of fun a _ => (m *ᵥ u) a) (Matrix.of fun a _ => (m *ᵥ u) a) 0 0
  have h2 := gram_apply (σ := σ) (J := J) (s := 1) (r := 1) (Matrix.of fun a _ => u a) (Matrix.of fun a _ => u a) 0 0
  rw [e, pgram_unitary hm] at h1
  rw [h2] at h1
  rw [← form_eq_hE, ← form_eq_hE]
  rw [e] at *
  exact h1.symm

theorem exists_sends {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {u : Fin n → E} (hu : u ≠ 0) (hi : hE σ J u u = 0) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 ∧ Sends σ J γ u v := by
  obtain ⟨m, hm, e⟩ := hγ
  refine ⟨m.1 *ᵥ u, ?_, ?_, ?_⟩
  · intro h0
    apply hu
    have := congrArg (fun z => (m⁻¹).1 *ᵥ z) h0
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
  · rw [hE_mulVec hm, hi]
  · have e1 : (matHom _ σ J γ).1 = m.1.map (inclR (F := F) (AF F)) := by
      rw [matHom_apply]
      exact (congrArg Units.val e).symm
    unfold Sends
    rw [e1]
    funext i
    simp only [ratV]
    exact (RingHom.map_mulVec (inclR (F := F) (AF F)) m.1 u i).symm

omit [NumberField F] [NumberField E] in
theorem first_witt_vector_ne_zero {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) : Xᵀ 0 ≠ 0 := by
  intro h0
  have h1 := gram_apply (σ := σ) (J := J) X Y 0 0
  rw [hW.xy, h0] at h1
  simp at h1

omit [NumberField F] [NumberField E] in
theorem first_witt_vector_isotropic {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    hE σ J (Xᵀ 0) (Xᵀ 0) = 0 := by
  have h1 := gram_apply (σ := σ) (J := J) X X 0 0
  rw [hW.xx, form_eq_hE] at h1
  exact h1.symm

theorem exists_isotropic_le
    (hS : ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0)
    (hM : ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J,
      (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀)
    (hB : ∀ {C : Set (GAd σ J)}, IsCompact C → ∀ {v : Fin n → E}, v ≠ 0 → ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B)
    {x : Fin n → E} (hx : x ≠ 0) (hi : hE σ J x x = 0) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ g : GAd σ J, ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ hgt σ J g u ≤ C₁ := by
  obtain ⟨ε, hε, hS⟩ := hS
  obtain ⟨C₀, hC₀, hC⟩ := hM ε hε
  obtain ⟨B, hB⟩ := hB hC₀ hx
  refine ⟨max ε B, lt_max_of_lt_left hε, fun g => ?_⟩
  by_cases h : ∃ v : Fin n → E, v ≠ 0 ∧ hgt σ J g v < ε
  · obtain ⟨v, hv, hlt⟩ := h
    exact ⟨v, hv, hS g v hv hlt, hlt.le.trans (le_max_left _ _)⟩
  · push_neg at h
    obtain ⟨γ, hγ, hγC⟩ := hC g h
    obtain ⟨v, hv, hvi, hs⟩ := exists_sends hγ hx hi
    refine ⟨v, hv, hvi, ?_⟩
    rw [← hgt_mul hs.inv]
    exact (hB _ hγC).trans (le_max_right _ _)

theorem exp_neg_le_rpow {d : ℝ} (hd : 0 < d) {s D : ℝ} (h : Real.exp (-(d * s)) ≤ D) :
    Real.exp (-s) ≤ D ^ (1 / d) := by
  have e : Real.exp (-s) = Real.exp (-(d * s)) ^ (1 / d) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [e]
  exact Real.rpow_le_rpow (Real.exp_pos _).le h (by positivity)

end GlobalTheory.CompanionTheory.RedCov.First


open GlobalTheory.CompanionTheory.RedCov.First in
theorem GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin (r + 1)) E) (hW : IsWittFrame σ J X Y) (a)
    (ha : PositivityTheory.ThKR.IsTorus σ J X Y a)
    (Ω C : Set (GAd σ J)) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X) (hC : IsCompact C) :
    ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 →
      NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → Real.exp (- s 0) ≤ M := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  obtain ⟨C₁, hC₁, hu⟩ := exists_isotropic_le (GlobalTheory.T.small_height_vector_isotropic F E σ h n J hJ) ((GlobalTheory.T.unitary_points_height_bound_finite GlobalTheory.T.unitary_points_height_bound_compact) F E σ h n J hJ)
    (fun hC _ hv => GlobalTheory.CompanionTheory.RedCov.Bridge.exists_hgt_le σ J hC hv) (first_witt_vector_ne_zero hW) (first_witt_vector_isotropic hW)
  obtain ⟨P, hP, hlow⟩ := GlobalTheory.T.torus_siegel_height_lower_bound F E σ h n J hJ r X Y hW a ha Ω C hΩ
    (hΩP.trans minParOne_subset) hC
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨(2 * P * C₁) ^ (1 / (Module.finrank ℚ F : ℝ)), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro ω hω s κ hκ e he hN
  obtain ⟨u, hu0, hui, hule⟩ := hu (ω * a s * κ)
  refine exp_neg_le_rpow hd ((hlow ω hω s κ hκ e he).trans ?_)
  calc P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) ≤ P * (2 * hgt σ J (ω * a s * κ) u) :=
        mul_le_mul_of_nonneg_left (hN.2.2 u hu0 hui) hP.le
    _ ≤ P * (2 * C₁) := by gcongr
    _ = 2 * P * C₁ := by ring
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG PositivityTheory.ThKF PositivityTheory.HoweDualityUnitaryAlt
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem cmp_finT (hM : MaxFinT) {R R₂ : RealMaps F a a'} {Rf Rf₂ : FinMaps F a a'} (m : IsMatched B G X om om' R Rf)
    (v : Pl F) (n₂ : Nontrivial (Rf₂.Pi v)) (o : (SB _).map (Rf₂.p v) = ⊤) (o' : (SB _).map (Rf₂.p' v) = ⊤)
    (x₁ : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p v) ⊓ SB _))
    (x₂ : Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p' v) ⊓ SB _))
    (eq₂ : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      Rf₂.p v φ = Rf₂.p' v φ' → Rf₂.p v φ₁ = Rf₂.p' v φ₁') :
    ∃ (e : Rf.Pi v →ₗ[ℂ] Rf₂.Pi v) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ SB _, e (Rf.p v x) = Rf₂.p v x) ∧
      ∀ x ∈ SB _, e (Rf.p' v x) = c • Rf₂.p' v x := by
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M om
    ⟨p1.base, ⟨_, _, p1.herm⟩, ⟨_, _, p1.skew⟩, p1.good, ⟨_, _, p1.weil⟩⟩ v
  choose A' hA' hA'' using fun (i : UAt σ G.W (evFin F v)) (x : SB (Fin a' × Fin (a + a') → Fv F v)) => ex_fin p2 v i x x.2
  have ac : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)),
      Acts (evFin F v) (om (1, i.1)) x (ω (1, i.1) x) := fun i x => (hω.acts 1 (one_at _) i i.2 x x.2 _).2 rfl
  have pr : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)), ω (1, i.1) x ∈ SB _ :=
    fun i x => hω.pres 1 (one_at _) i i.2 x x.2
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  exact schur_match (SB _) (SB _) (Rf.p v) (Rf.p' v) (Rf₂.p v) (Rf₂.p' v) (m.fin.onto v) (m.fin.onto' v) o o'
    (fun x hx => (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).1 _ _ (maxFinP m v).1 x₁) x hx).1)
    (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).2 _ _ (maxFinP m v).2 x₂))
    (fun i : UAt σ G.W (evFin F v) => ω (1, i.1) ∘ₗ Submodule.subtype _) A' pr hA'
    (fun i x x' => m.fin.equiv v i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun i x x' => eq₂ i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun N hN => m.fin.irred v N fun h hh x hx y _ e hp => by
      rw [(hω.acts 1 (one_at _) h hh x hx y).1 e]; exact hN ⟨h, hh⟩ ⟨x, hx⟩ hp)
    (rank_SB _)

theorem polRe_of2T (hH : PositivityTheory.ThKR.JoinTri) (hM : MaxFinT) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    (hJ : CartanConj) (hV : CartanMove) (hK : KCoinv) (hI : ILeft) : PolRe := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' R Rf m V V' W R₂ Rf₂ m₂ ⟨c₂, hc₂, hc⟩
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨h, hh, hh'⟩ := hJ F E σ B _ G.W W _ _ p1.base p1.skew m₂.triple.geo.hW
  obtain ⟨g, hg, hg', hP⟩ := hV F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 V W (reG G V V' W).M rfl (pairV m₂.triple) h hh hh'
  obtain ⟨g', hk, hk', hP'⟩ := hV F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 V' W (reG G V V' W).M' rfl (pairV' m₂.triple) h hh hh'
  obtain ⟨T, hT, -⟩ := hO F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 g hg h hh
  obtain ⟨T', hT', -⟩ := hO F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 g' hk h hh
  obtain ⟨e, c, c0, he, he'⟩ := archimedean_matched_maps_compare hH hO hL hQ hC ⟨m₂.triple, real_trans hO hL hQ m.triple m₂.triple m.real ⟨hg, hg'⟩ ⟨hk, hk'⟩
    ⟨hh, hh'⟩ hT hT' (hP T hT) (hP' T' hT'), m₂.fin⟩ m₂
  choose ef cf cf0 hef hef' using fun v => cmp_finT (R₂ := R₂) hM m v (m₂.fin.nontriv v) (m₂.fin.onto v) (m₂.fin.onto' v)
    (maxFinP m₂ v).1 (maxFinP m₂ v).2 (m₂.fin.equiv v)
  have cf1 : ∀ v ∉ X.T, cf v = 1 := fun v hv => by
    obtain ⟨s1, s2⟩ := m₂.fin.sph v hv
    have x1 := hef v _ (p1.good.vac v).1
    rw [(m.fin.sph v hv).1, hef' v _ (p2.good.vac v).1] at x1
    have x2 : cf v • Rf₂.p v (G.M.vac v) = (1 : ℂ) • Rf₂.p v (G.M.vac v) := by
      rw [one_smul]; exact (congrArg (cf v • ·) s1).trans x1
    exact smul_left_injective ℂ s2 x2
  let Λ : ℂ := c * ∏ v ∈ X.T, cf v
  refine ⟨c₂ * Λ, mul_ne_zero hc₂ (mul_ne_zero c0 (Finset.prod_ne_zero_iff.2 fun v _ => cf0 v)), ?_⟩
  rintro Φ Φ' hΦ' ⟨S, hS, k, k', f, φ, f', φ', h1, h2, rfl, rfl, eq⟩ x
  choose u hu hu' using fun i => (show f i ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) from hP T hT ▸ (h1 i).1)
  choose u' hw hw' using fun i => (show f' i ∈ ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) from hP' T' hT' ▸ (h2 i).1)
  have e1 := move_sum p1.good hT u φ (fun i => (h1 i).2.1) fun i => ev_of_off (h1 i).2.2
  have e2 := move_sum p2.good hT' u' φ' (fun i => (h2 i).2.1) fun i => ev_of_off (h2 i).2.2
  have fu : ∀ i, T (u i) = f i := hu'
  have fu' : ∀ i, T' (u' i) = f' i := hw'
  simp only [fu] at e1
  simp only [fu'] at e2
  have s1 : ∑ i, pure (u i) (φ i) ∈ schA F _ := sum_mem fun i _ =>
    GlobalTheory.TensUniq.pure_mem_schA _ _ (h1 i).2.1 ((good_std p1.good).congr (ev_of_off (h1 i).2.2))
  have so : ∑ i, pure (u' i) (φ' i) ∈ G.M'.So B.ψ B.τ₁ := by
    have := (hK F E σ B a a' G X om om' R Rf m).2 (g', h)⁻¹ _ hΦ'
    rwa [← e2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have e3 : Λ • ∑ i, pure (u' i) (φ' i) = ∑ i, pure (Λ • u' i) (φ' i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => funext fun y => (mul_assoc _ _ _).symm
  have pm : PolMatch B (reG G V V' W) X R₂ Rf₂ (∑ i, pure (u i) (φ i)) (Λ • ∑ i, pure (u' i) (φ' i)) := by
    refine ⟨S, hS, k, k', u, φ, fun i => Λ • u' i, φ', fun i => ⟨hu i, (h1 i).2⟩,
      fun i => ⟨Submodule.smul_mem _ _ (hw i), (h2 i).2⟩, rfl, e3, ?_⟩
    have := congrArg (TensorProduct.map e (PiTensorProduct.map fun v : S => ef v)) eq

    simp only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [← fu i, show e (R.p (T (u i))) = R₂.p (u i) from he _ (hu i)]
      simp only [hef _ _ ((h1 i).2.1 _)]
    · rw [← fu' j, show e (R.p' (T' (u' j))) = c • R₂.p' (u' j) from he' _ (hw j)]
      simp only [hef' _ _ ((h2 j).2.1 _)]
      rw [MultilinearMap.map_smul_univ, TensorProduct.smul_tmul_smul, map_smul, TensorProduct.smul_tmul']
      simp only [RingHom.id_apply]
      rw [Finset.prod_coe_sort S cf, ← Finset.prod_subset hS fun v _ hv => cf1 v hv]
  have := hc _ _ (Submodule.smul_mem _ Λ (so_re V V' W so)) pm (x * h)
  rw [← e1, ← e2, I_move hI p1 s1, I_move hI p2 (so_le p2.good _ so), mul_assoc, ← I_smul]
  exact this

end GlobalTheory.CompanionTheory.ThetaK

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PullSch

theorem exists_mul_eq_one_of_linearIndependent {K : Type} [Field K] {r n : ℕ} (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c) : ∃ d : Matrix (Fin n) (Fin r) K, c * d = 1 := by
  have hinj : Function.Injective (Matrix.toLin' cᵀ) := by
    intro v w hvw
    have h1 : ∀ u : Fin r → K, Matrix.toLin' cᵀ u = ∑ i, u i • c i := by
      intro u
      funext j
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [h1, h1] at hvw
    have h2 := Fintype.linearIndependent_iff.1 hc (v - w) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hvw, sub_self])
    funext i
    exact sub_eq_zero.1 (h2 i)
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' cᵀ) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(LinearMap.toMatrix' h)ᵀ, ?_⟩
  have e : LinearMap.toMatrix' h * cᵀ = 1 := by
    rw [← LinearMap.toMatrix'_toLin' cᵀ, ← LinearMap.toMatrix'_comp, hh, LinearMap.toMatrix'_id]
  rw [← Matrix.transpose_transpose c, ← Matrix.transpose_mul, e, Matrix.transpose_one]

theorem mul_map_finPart (D : D7) {m r n : ℕ} (x : Mx D m r) (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1) :
    (x * C).map (finPart D) * Dm.map (finPart D) = x.map (finPart D) := by
  have e1 : x = x * C * Dm := by rw [Matrix.mul_assoc, hCD, Matrix.mul_one]
  conv_rhs => rw [e1]
  simp only [Matrix.map_mul]

theorem exists_finPart_section (D : D7) :
    ∃ s : Af D.host.F ⊗[D.host.F] D.host.E → AE D, Continuous s ∧ ∀ a, finPart D (s a) = a := by
  obtain ⟨e, he, -, hes⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨fun a => e.symm (0, a), hes.comp (continuous_const.prodMk continuous_id), fun a => ?_⟩
  have h := (he (e.symm (0, a))).2
  have h2 : (e (e.symm (0, a))).2 = a := by simp
  exact h.symm.trans h2

theorem continuous_lift_mul (D : D7) {m n r : ℕ} (Dm : Mx D n r) (s : Af D.host.F ⊗[D.host.F] D.host.E → AE D)
    (hs : Continuous s) :
    Continuous (fun z : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (z.map s * Dm).map (finPart D)) :=
  ((continuous_id.matrix_map hs).matrix_mul continuous_const).matrix_map (GlobalTheory.Member.continuous_finPart D)

def mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) : Mx D m r →+ Mx D m n where
  toFun y := y * C
  map_zero' := Matrix.zero_mul _
  map_add' a b := Matrix.add_mul a b C

theorem mulR_apply (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) (y : Mx D m r) : mulR D m C y = y * C := rfl

theorem continuous_mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) : Continuous (mulR D m C) :=
  continuous_id.matrix_mul continuous_const

theorem injective_mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1) :
    Function.Injective (mulR D m C) := fun a b h => by
  have h' : a * C * Dm = b * C * Dm := congrArg (· * Dm) h
  rwa [Matrix.mul_assoc, Matrix.mul_assoc, hCD, Matrix.mul_one, Matrix.mul_one] at h'

theorem isRealParam_mulR_comp (D : D7) {m r n k : ℕ} (C : Mx D r n) (L : (Fin k → ℝ) →+ Mx D m r)
    (hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L) : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam ((mulR D m C).comp L) := by
  refine ⟨(continuous_mulR D m C).comp hL.1, fun t => ?_⟩
  rw [AddMonoidHom.comp_apply, mulR_apply, Matrix.map_mul, hL.2 t, Matrix.zero_mul]

theorem injective_comp (D : D7) {m r n k : ℕ} (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1)
    (L : (Fin k → ℝ) →+ Mx D m r) (hL : Function.Injective L) : Function.Injective ((mulR D m C).comp L) := by
  intro a b h
  exact hL (injective_mulR D m C Dm hCD h)

theorem pullSchLI : PositivityTheory.GramSchwartzFunctions.PullSchLI := by
  intro D θ hθ m r n c hc φ hφ
  obtain ⟨d, hcd⟩ := exists_mul_eq_one_of_linearIndependent c hc
  rw [← GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA D θ hθ] at hφ ⊢
  set C : Mx D r n := c.map (incA D) with hC
  set Dm : Mx D n r := d.map (incA D) with hD
  have hCD : C * Dm = 1 := by
    rw [hC, hD, ← Matrix.map_mul, hcd, Matrix.map_one _ (map_zero _) (map_one _)]
  have hpull : ∀ y, pull c φ y = φ (mulR D m C y) := fun y => rfl
  obtain ⟨hlev, hsupp, hsch⟩ := hφ
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨U, hUo, hU⟩ := hlev
    refine ⟨U.comap (mulR D m C), hUo.preimage (continuous_mulR D m C), fun u hu h0 x => ?_⟩
    have h0' : (mulR D m C u).map (infPart D) = 0 := by
      rw [mulR_apply, Matrix.map_mul, h0, Matrix.zero_mul]
    rw [hpull, hpull, map_add (f := _), hU _ hu h0']
  · obtain ⟨K, hK, hKs⟩ := hsupp
    obtain ⟨s, hs, hfs⟩ := exists_finPart_section D
    have h1 : ∀ y : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E), (y.map s).map (finPart D) = y :=
      fun y => by
        ext i j
        simp [hfs]
    refine ⟨(fun z => (z.map s * Dm).map (finPart D)) '' K, hK.image (continuous_lift_mul D Dm s hs),
      fun x hx => ⟨(mulR D m C x).map (finPart D), hKs _ hx, ?_⟩⟩
    rw [mulR_apply]
    show ((((x * C).map (finPart D)).map s) * Dm).map (finPart D) = x.map (finPart D)
    rw [Matrix.map_mul (L := ((x * C).map (finPart D)).map s), h1]
    exact mul_map_finPart D x C Dm hCD
  · intro k L hL hLinj x
    obtain ⟨g, hg⟩ := hsch k ((mulR D m C).comp L) (isRealParam_mulR_comp D C L hL)
      (injective_comp D C Dm hCD L hLinj) (mulR D m C x)
    exact ⟨g, fun t => by rw [hg, hpull, map_add (f := _), AddMonoidHom.comp_apply]⟩

end GlobalTheory.CompanionTheory.PullSch
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.ColumnSplitting.YvInt

variable {D : D7} {a b c : ℕ}

theorem cv_cA (v : Pl D) (z : AE D) : cv D v (cA D z) = sigR _ D.sp.cm.sig (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem intOff_mm {S : Finset (Pl D)} {x : Mx D a b} {y : Mx D b c} (hx : IntOff S x) (hy : IntOff S y) :
    IntOff S (mm x y) := by
  intro v hv i j
  have h : mm x y i j = ∑ k, x i k * y k j := Matrix.mul_apply
  have hs : ∑ k, x i k * y k j ∈ (intLoc D.host.F D.host.E v).comap (cv D v) :=
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (Subring.mem_comap.2 (hx v hv i k))
      (Subring.mem_comap.2 (hy v hv k j))
  rw [h]
  exact Subring.mem_comap.1 hs

theorem intOff_adj {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) : IntOff S (adj x) := by
  intro v hv i j
  have h : adj x i j = cA D (x j i) := rfl
  rw [h, cv_cA]
  exact sigR_mem_intLoc _ (hx v hv j i)

theorem exists_finset_intOff (x : Mx D a b) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → IntOff S x := by
  have hbad : {v : Pl D | ¬ ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v}.Finite :=
    GlobalTheory.CompanionTheory.ColumnSplitting.exists_intOff x
  refine ⟨hbad.toFinset, fun S hS v hv => ?_⟩
  by_contra hc
  exact hv (hS (hbad.mem_toFinset.2 hc))

theorem intOff_yv (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ z : Mx D V.rank r × Mx D V.rank t,
      IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z) := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_intOff (rat b₀.1⁻¹ : Mx D r r)
  obtain ⟨S₂, h₂⟩ := exists_finset_intOff (gA V)
  refine ⟨S₁ ∪ S₂, fun S hS z hz₁ hz₂ => ?_⟩
  exact intOff_mm (h₁ S (Finset.union_subset_left hS))
    (intOff_mm (intOff_adj hz₁) (intOff_mm (h₂ S (Finset.union_subset_right hS)) hz₂))

end GlobalTheory.CompanionTheory.ColumnSplitting.YvInt

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.unitary_adelic_iwasawa_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ finPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  first | exact @GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good | exact GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good | (intros; apply GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good <;> assumption)
end
