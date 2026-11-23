module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle062
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
import Formalism.LocalRingCardinality.Bundle002
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle003
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSupBound

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem continuous_mov_pair (hθ : IsInfFam θ) (u : RW T S) :
    Continuous fun p : GA D S × GA D T => mov θ p.1⁻¹ p.2⁻¹ u := by
  refine continuous_pi fun τ => ?_
  unfold mov
  simp only [inv_inv]
  exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
    ((GlobalTheory.RealWeil.continuous_mt T).2.comp continuous_snd)).matrix_mul continuous_const).matrix_mul
    ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt S).1.comp continuous_fst))

theorem uniform_level_pair (hom : IsWeilDatumO ψ S T χS χT om) {U : AddSubgroup (WO S T)}
    (hU : IsOpen (U : Set (WO S T))) {C : Set (GA D S × GA D T)} (hC : IsCompact C) :
    ∃ K₀ ∈ 𝓝 (0 : WO S T), IsCompact K₀ ∧ ∀ p ∈ C, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u φ = φ) → ∀ u ∈ K₀, u.map (infPart D) = 0 →
        heisO ψ S T u (om p φ) = om p φ := by
  obtain ⟨i1, i2, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous fun z : WO S T × (GA D S × GA D T) => actO S T z.2.1⁻¹ z.2.2⁻¹ z.1 := by
    unfold actO
    simp only [inv_inv]
    exact (((GlobalTheory.RealWeil.continuous_mt T).2.comp (continuous_snd.comp continuous_snd)).matrix_mul
      continuous_fst).matrix_mul ((GlobalTheory.RealWeil.continuous_mt S).1.comp (continuous_fst.comp continuous_snd))
  have hev : ∀ᶠ u in 𝓝 (0 : WO S T), ∀ p ∈ C, actO S T p.1⁻¹ p.2⁻¹ u ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    refine hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    show actO S T p.1⁻¹ p.2⁻¹ 0 ∈ U
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
    exact U.zero_mem
  obtain ⟨K₀, h0, hsub, hK₀⟩ := LocallyCompactSpace.local_compact_nhds (X := WA T S) 0 _ hev
  refine ⟨K₀, h0, hK₀, fun ⟨g, h⟩ hp φ hφ hl u hu hinf => ?_⟩
  have hv : (actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hinf, Matrix.mul_zero, Matrix.zero_mul]
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) φ hφ
  rw [hl _ (hsub hu _ hp) hv, actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  exact e.symm

theorem cube_bound_at (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {N : ℕ}
    (b : Module.Basis (Fin N) ℝ (RW T S)) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T u (om p φ) = om p φ) → ∀ B : ℝ, (∀ w, ‖φ w‖ ≤ B) → ∀ y,
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖om p φ (y + ∑ i, iotaW σ T S (t i • b i))‖ ^ 2 ≤ c * B ^ 2 := by
  obtain ⟨c, hc0, hcube⟩ := cube_bound hom hc b h0 hK₀
  refine ⟨c, hc0, fun ⟨g, h⟩ φ hφ hl B hB y => ?_⟩
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ y) φ hφ
  rw [actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  have hn := GlobalTheory.HeisOrtho.norm_heisO (S := S) (T := T) hom.std.1
  have key := hcube (g, h) _ (GlobalTheory.ThetaClosed.thetaClosed ψ θ hom.std hc.inf S T φ hφ |>.1 (actO S T g⁻¹ h⁻¹ y))
    (fun w hw => by
      generalize hu : w - iotaW σ T S (piW θ T S w) = u at hw
      have hinf : u.map (infPart D) = 0 := by
        have hp : piW θ T S u = 0 := by
          rw [← hu, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
        ext i j
        exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
      rw [e, hn, hn]
      conv_rhs => rw [← hl u hw hinf, hn, ← hu]
      congr 2
      abel_nf) B (fun w => by rw [hn]; exact hB _)
  simp only [e, hn, zero_add] at key
  simpa only [add_comm y] using key

theorem exists_sup_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ C : Set (GA D S × GA D T), IsCompact C →
      ∃ c : ℝ, ∀ p ∈ C, ∀ w, ‖om p f w‖ ≤ c := by
  intro D ψ S T χS χT om hom f hf C hC
  have hψ := hom.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have b := Module.finBasis ℝ (RW T S)
  generalize Module.finrank ℝ (RW T S) = N at b
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K₀, h0, hK₀, hlev⟩ := uniform_level_pair hom hU hC
  obtain ⟨c, hc0, hcube⟩ := cube_bound_at hom hc b h0 hK₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := words_bound (dvL hc hψ S T) (fun w => (LinearMap.proj w).comp (thetaSub ψ S T).subtype)
    (fun (m : thetaSub ψ S T) => theta_bounded hψ m.2) N ⟨f, hf⟩
  obtain ⟨κ, hκ⟩ := hC.exists_bound_of_continuousOn
    (f := fun (p : GA D S × GA D T) (i : Fin N) => mov θ p.1⁻¹ p.2⁻¹ (b i))
    (continuous_pi fun i => continuous_mov_pair hθ (b i)).continuousOn
  refine ⟨√(4 ^ N * (c * (C₁ * max 1 κ ^ N) ^ 2)), fun ⟨g, h⟩ hp w => ?_⟩
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ max 1 κ) ∧ F = om (g, h) (wd l).1}
  refine Real.le_sqrt_of_sq_le (sobolev_iter N 0 (fun i r => iotaW σ T S (r • b i)) A (c * (C₁ * max 1 κ ^ N) ^ 2) w
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ (om (g, h) f) ⟨[], le_rfl, by simp, rfl⟩)
  · rintro p _ ⟨l, h1, h2, rfl⟩
    have hF := hom.om_pres (g, h) _ (wd l).2
    refine ⟨hF.cont, fun i => ⟨_, ⟨l ++ [mov θ g⁻¹ h⁻¹ (b i)], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (b i) hF⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        exact ((norm_le_pi_norm (fun i => mov θ g⁻¹ h⁻¹ (b i)) i).trans (hκ (g, h) hp)).trans (le_max_right _ _)
    · rw [dv_om hom hc g h (b i) (wd l).2]
      simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    exact hcube (g, h) _ (wd l).2 (hlev (g, h) hp _ (wd l).2 fun u hu h0 => words_level hc hψ h0 l _ (hl u hu h0)) _
      (hC₁ _ (le_max_left _ _) l (by simpa using h1) h2) w

end GlobalTheory.WeilSupBound

end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem conj_eq_complexConj (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

theorem norm_natCast_eq_one {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) : ‖(k : ℂ_[p])‖ = 1 := by
  rw [GlobalTheory.EigenGenerator.norm_natCast_eq]
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hk)

theorem exists_unitary_at (p : ℕ) (hp : p.Prime) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ G : Matrix (Fin N) (Fin N) D.host.E, (G.map D.host.conj).transpose * G = 1 ∧
      (∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E))) ∧
      (∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram D.sp.cm.cmUnram
  have hsd : (⟨L, hL.1, hL.2.1⟩ : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat D.host.E N).SelfDual := by
    intro x
    have h3 := hL.2.2 x
    refine h3.trans (forall₂_congr fun y _ => ?_)
    have e : stdH D.host.E N y x = GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm x y := by
      unfold stdH GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      rfl
    rw [e]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  obtain ⟨γ, hγ, h1, h2⟩ := GlobalTheory.GenusSelfDual.inGenus_of_selfDual hsd p hp
  refine ⟨LinearMap.toMatrix' γ.toLinearMap, ?_, fun x hx => ?_, fun a => ?_⟩
  · ext a b
    have h := hγ (Pi.single b 1) (Pi.single a 1)
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm (Pi.single b (1 : D.host.E)) (Pi.single a 1) = if a = b then 1 else 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      rw [Finset.sum_eq_single b]
      · by_cases hab : a = b
        · subst hab; simp
        · simp [Pi.single_apply, Ne.symm hab, hab]
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    rw [hr] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply, LinearMap.toMatrix'_apply,
      LinearEquiv.coe_coe, conj_eq_complexConj]
    rw [← h]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · obtain ⟨k, hk, hkx⟩ := h1 x hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hkx
    choose c hc using GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.mem_stdMod.1 hy
    refine ⟨k, hk, c, ?_⟩
    rw [LinearMap.toMatrix'_mulVec, Nat.cast_smul_eq_nsmul]
    rw [← hyx]
    have : (fun a => (c a : D.host.E)) = y := funext hc
    rw [this]
    rfl
  · have hm : (fun i => LinearMap.toMatrix' γ.toLinearMap i a) ∈ ((GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat.std D.host.E N).map γ).L := by
      refine Submodule.mem_map.2 ⟨Pi.single a 1, GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.single_mem_stdMod a, ?_⟩
      funext i
      simp [LinearMap.toMatrix'_apply]
    obtain ⟨k, hk, hkx⟩ := h2 _ hm
    exact ⟨k, hk, by rwa [Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.Mem.Col2.TC.AdaptedBases

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem basR_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (G : Matrix (Fin N) (Fin N) D.host.E) (hdet : G.det ≠ 0)
    (h1 : ∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E)))
    (h2 : ∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) :
    GL3Columns.BasR D lam τ L (G.map (tauEmb D lam τ)) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  unfold GL3Columns.BasR
  rw [hρ]
  have hdet' : (G.map ρ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero ρ).2 hdet
  refine ⟨hdet', fun x hx a => ?_, fun a => ?_⟩
  · obtain ⟨k, hk, c, hc⟩ := h1 x hx
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    have hv : (fun i => ρ (x i)) = (G.map ρ).mulVec ((k : ℂ_[p])⁻¹ • fun a => ρ (c a : D.host.E)) := by
      funext i
      have e := congrArg (fun v => ρ (v i)) hc
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at e
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hk0, e, RingHom.map_mulVec]
      rfl
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet'), Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul, norm_mul, norm_inv, hk1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ (c a)
  · obtain ⟨k, hk, hkL⟩ := h2 a
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    refine ⟨1, fun _ => (k : ℂ_[p])⁻¹, fun _ => (k : D.host.E) • fun i => G i a, fun _ => by rw [norm_inv, hk1, inv_one],
      fun _ => hkL, fun i => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.map_apply]
    rw [inv_mul_cancel_left₀ hk0]

theorem dualM_eq_self {N : ℕ} {G : Matrix (Fin N) (Fin N) D.host.E} (h : (G.map D.host.conj).transpose * G = 1) : dualM G = G :=
  Matrix.inv_eq_right_inv h

theorem basR_smul {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} {N : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M : Matrix (Fin N) (Fin N) ℂ_[p]} (hM : GL3Columns.BasR D lam τ L M)
    {s : ℂ_[p]} (hs : ‖s‖ = 1) : GL3Columns.BasR D lam τ L (s • M) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs; exact zero_ne_one hs
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, fun x hx a => ?_, fun a => ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) h0
  · have e : (s • M)⁻¹ = s⁻¹ • M⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h0)]
    rw [e, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, hs, inv_one, one_mul]
    exact h1 x hx a
  · obtain ⟨n, r, x, hr, hx, he⟩ := h2 a
    refine ⟨n, fun k => s * r k, x, fun k => by rw [norm_mul, hs, one_mul]; exact hr k, hx, fun i => ?_⟩
    rw [Matrix.smul_apply, he i, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem ne_two_ne_q_of_adPl {w : D.what₂.places.Pl} (hw : AdPl D w) :
    D.what₂.places.resChar w ∉ D.host.small ∧ D.what₂.places.resChar w ≠ D.host.q := by
  unfold AdPl Formalism.BasicNotions.Host.cls at hw
  constructor
  · intro h
    simp [Formalism.BasicNotions.primeClass, h] at hw
  · intro h
    rw [h, Formalism.BasicNotions.primeClass_q] at hw
    simp at hw

theorem dgenUnitAd (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : DgenUnitAd P O := by
  intro w hw u μ τ
  obtain ⟨h2, hq⟩ := ne_two_ne_q_of_adPl hw
  obtain ⟨M, hM, hemb, hs⟩ := (O u μ).dgen_gen
  obtain ⟨s, hs1, hs2⟩ := hs τ
  rw [← hs1]
  exact GlobalTheory.EigenGenerator.norm_generator_eq_one D _ (P.lam w) h2 hq M hemb τ s hs2

theorem exists_sys (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (u : D.what₂.Word)
    (μ : D.what₂.Tup) : ∃ Pm : SysFam D u μ,
      (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) := by
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  choose G hG h1 h2 using fun i (c : (D.chTw u μ).cls i) =>
    exists_unitary_at (D := D) (D.what₂.places.resChar w) hp ((O u μ).lat i c).1 ((O u μ).lat i c).2
  refine ⟨fun i c _ => G i c, fun i _ c τ => ?_, fun _ _ _ _ _ _ => rfl, fun i _ c _ _ _ => (dualM_eq_self (hG i c)).symm⟩
  exact basR_of (P.lam w) τ _ (G i c) (Matrix.det_ne_zero_of_left_inverse (hG i c)) (h1 i c) (h2 i c)

end GlobalTheory.Mem.Col2.TC.AdaptedBases

open IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MoveUpLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem localization_le_localization_of_le {M N : Submodule (𝓞 E) (Sp E n)} (P : HeightOneSpectrum (𝓞 E))
    (h : M ≤ N) : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N :=
  localization_le_of_smul_mem (one_notMem P) fun y hy => by rw [one_smul]; exact h hy

theorem exists_notMem_conj_mem (P : ST) (hP : MoveHyp ST SG P) :
    ∃ a : 𝓞 E, a ∉ P.1.asIdeal ∧ ∀ Q : ST, cO E a ∈ Q.1.asIdeal := by
  classical
  have hex : ∀ Q : ST, ∃ b ∈ Q.1.asIdeal, b ∉ (conjPrime₂ P.1).asIdeal := fun Q =>
    exists_mem_notMem (hP.st Q)
  choose b hb hb' using hex
  refine ⟨cO E (∏ Q : ST, b Q), ?_, fun Q => ?_⟩
  · intro h
    have h' : ∏ Q : ST, b Q ∈ (conjPrime₂ P.1).asIdeal := (mem_conjP _ _).2 h
    obtain ⟨Q, -, hQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (conjPrime₂ P.1).isPrime)).1 h'
    exact hb' Q hQ
  · rw [cO_cO]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem b (Finset.mem_univ Q)) (hb Q)

theorem localization_dual_L_eq_localization_N {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N := by
  obtain ⟨a, ha, haQ⟩ := exists_notMem_conj_mem P hP
  exact le_antisymm (localization_le_of_smul_mem ha fun y hy => hd.smul_Lsh_mem_N haQ hy)
    (localization_le_localization_of_le P.1 hd.N_le_Lsh)

theorem localization_L_eq_localization_kerAt {d : Deco E n ST SG} (hd : d.Ok) (P : ST) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.kerAt P) := by
  ext y
  rw [hd.mem_locP_L]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h1
    refine (mem_locP _ _ _).2 ⟨s, hs, (hd.mem_kerAt P _).2 ⟨hsy, ?_⟩⟩
    rw [hd.f_smul P s y h1, h2, mul_zero]
  · intro h
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P _).1 hsy
    have hy : y ∈ d.at P.1 := (mem_locP _ _ _).2 ⟨s, hs, h1⟩
    refine ⟨hy, ?_⟩
    rw [hd.f_smul P s y hy] at h2
    exact (mul_eq_zero.1 h2).resolve_left (mk_ne_zero hs)

theorem localization_up_L_eq_localization_N {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N := by
  have hd' := hd.up P hP hq hq2 hx hfx
  rw [localization_L_eq_localization_kerAt hd' P, ← (hd'.dnN_spec P hP.ne).2.2.2, hd.dnN_up P hP hq hq2 hx hfx]

theorem localization_dual_up_L {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) (d.up P q x).L) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔
        Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) := by
  have hd' := hd.up P hP hq hq2 hx hfx
  obtain ⟨-, -, -, h4, h5⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  rw [localization_dual_L_eq_localization_N hd' P hP]
  change Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) = _
  have hq0' : q ≠ 0 := fun h => hq2 (h ▸ Submodule.zero_mem _)
  have hq0 : algebraMap (𝓞 E) E q ≠ 0 := by rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  obtain ⟨a, ha, haQ⟩ := exists_notMem_conj_mem P hP
  obtain ⟨b, hb, hbP⟩ := exists_mem_notMem hP.ne
  obtain ⟨c, hc, r, hr, hcr⟩ := exists_inv_unif P.1 hq hq2
  have hAS : upA P.1.asIdeal d.N x ≤
      d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x} := by
    refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    rintro z ⟨e, he, rfl⟩
    obtain ⟨β, hβ⟩ := Formalism.HermitianLatticesTheory.neighbourConstruct_mem_inv.1 he q hq
    have e1 : e • x = β • ((algebraMap (𝓞 E) E q)⁻¹ • x) := by
      rw [← algebraMap_smul E β, smul_smul, hβ, mul_comm (algebraMap (𝓞 E) E q) e, mul_assoc,
        mul_inv_cancel₀ hq0, mul_one]
    rw [SetLike.mem_coe, e1]
    exact (le_sup_right : _ ≤ d.N ⊔ _)
      (Submodule.smul_mem _ β (Submodule.subset_span rfl))
  have hSA : ∀ z ∈ d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x},
      r • z ∈ upA P.1.asIdeal d.N x := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have e2 : r • (t • ((algebraMap (𝓞 E) E q)⁻¹ • x)) = t • (c • x) := by
      rw [smul_comm r t, ← algebraMap_smul E r, smul_smul, ← hcr, mul_comm (algebraMap (𝓞 E) E q) c,
        mul_assoc, mul_inv_cancel₀ hq0, mul_one]
    rw [smul_add, e2]
    exact Submodule.add_mem_sup (d.N.smul_mem r hu)
      (Submodule.smul_mem _ t (Submodule.subset_span ⟨c, hc, rfl⟩))
  have hupN : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upA P.1.asIdeal d.N x) :=
    le_antisymm (localization_le_localization_of_le P.1 h4)
      (localization_le_of_smul_mem hbP fun y hy => h5 (Submodule.smul_mem_smul hb hy))
  have hA : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upA P.1.asIdeal d.N x) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) :=
    le_antisymm (localization_le_localization_of_le P.1 hAS) (localization_le_of_smul_mem hr hSA)
  have hL : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔
        Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) := by
    refine le_antisymm (localization_le_of_smul_mem ha fun z hz => ?_)
      (localization_le_localization_of_le P.1 (sup_le_sup_right hd.N_le_Lsh _))
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
    rw [smul_add]
    exact Submodule.add_mem_sup (hd.smul_Lsh_mem_N haQ hu) (Submodule.smul_mem _ a hv)
  rw [hupN, hA, hL]

theorem lattices_at_up : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E n ST SG), d.Ok → ∀ (P : ST), MoveHyp ST SG P → ∀ (q : 𝓞 E), q ∈ P.1.asIdeal → q ∉ P.1.asIdeal ^ 2 → ∀ (x : Sp E n), x ∈ d.N → d.f P x = 1 → d.N ≤ Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) (d.up P q x).L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) ∧ ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).N, (d.up P q x).f P y = d.f P (q • y) := by
  intro E _ _ _ n ST SG d hd P hP q hq hq2 x hx hfx
  exact ⟨hd.N_le_Lsh, localization_dual_L_eq_localization_N hd P hP, localization_up_L_eq_localization_N hd P hP hq hq2 hx hfx,
    localization_dual_up_L hd P hP hq hq2 hx hfx, fun y hy => by
      rw [Deco.up_f, if_pos (show y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) from hy)]⟩

end GlobalTheory.MoveUpLat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eventually_weilMatrixCoeff_finitePoint_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w, ∫ x in 𝓕, heisO ψ S T (actO S T p.1 p.2 w) f x * star (f x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ := by
  first | exact @GlobalTheory.Mem.CoefInv.eventually_coef_actO | exact GlobalTheory.Mem.CoefInv.eventually_coef_actO | (intros; apply GlobalTheory.Mem.CoefInv.eventually_coef_actO <;> assumption)
end
