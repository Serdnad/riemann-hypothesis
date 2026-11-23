module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle508
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle605
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.PiCovol

theorem isFD_pi {ι Y : Type} [Fintype ι] [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {G : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain G D ν) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : ι => G) (Set.univ.pi fun _ : ι => D)
      (Measure.pi fun _ : ι => ν) := by
  have hq (i : ι) := Measure.quasiMeasurePreserving_eval (fun _ : ι => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : ι => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

theorem map_eq_of_isFD {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure V) [P.IsAddHaarMeasure] (G : AddSubgroup V) [Countable G] {D : Set V}
    (hD : IsAddFundamentalDomain G D P) (h0 : P D ≠ 0) (h1 : P D ≠ ⊤) (e : V ≃ₜ+ V)
    (hG : ∀ v ∈ G, e.symm v ∈ G) (hG' : ∀ v ∈ G, e v ∈ G) : P.map e = P := by
  haveI : (P.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map P
  set c := Measure.addHaarScalarFactor (P.map e) P with hc
  have h : P.map e = c • P := Measure.isAddLeftInvariant_eq_smul _ P
  have hm : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hpre : IsAddFundamentalDomain G (e ⁻¹' D) P := by
    refine hD.preimage_of_equiv (f := e) ⟨hm.measurable.aemeasurable, ?_⟩
      (e := fun b : G => (⟨e.symm b, hG _ b.2⟩ : G)) ⟨fun b b' h => ?_, fun a => ?_⟩ fun b v => ?_
    · rw [h]; exact Measure.smul_absolutelyContinuous
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact ⟨⟨e a, hG' _ a.2⟩, Subtype.ext (e.symm_apply_apply _)⟩
    · change e (e.symm b + v) = b + e v
      simp
  have e1 : P (e ⁻¹' D) = P D := hpre.measure_eq hD
  have e2 : P (e ⁻¹' D) = c * P D := by rw [← hm.map_apply, h]; rfl
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have : (c : ℝ≥0∞) * P D = 1 * P D := by rw [← e2, e1, one_mul]
    exact (ENNReal.mul_left_inj h0 h1).1 this
  have : c = 1 := by exact_mod_cast hc1
  rw [h, this, one_smul]

end GlobalTheory.CompanionTheory.SiegelND.PiCovol


open GlobalTheory.CompanionTheory.SiegelND.PiCovol in
theorem GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix : ∀ (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)), GlobalTheory.CompanionTheory.Hypotheses₂.OneV.IsCovolOne ν → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → (Measure.pi fun _ : ι => ν).map (fun x => (A.map (algebraMap F (AF F))).mulVec x) = Measure.pi fun _ : ι => ν := by
  intro F _ _ ν hν ι _ _ A hA
  obtain ⟨hH, D, hD, hD1⟩ := hν
  haveI := hH
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  set G₀ : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range with hG₀
  set G : AddSubgroup (ι → AF F) := AddSubgroup.pi Set.univ fun _ : ι => G₀ with hGdef
  have hmemG : ∀ v : ι → AF F, v ∈ G ↔ ∃ ξ : ι → F, v = fun i => algebraMap F (AF F) (ξ i) := by
    intro v
    constructor
    · intro hv
      choose ξ hξ using fun i => hv i trivial
      exact ⟨ξ, funext fun i => (hξ i).symm⟩
    · rintro ⟨ξ, rfl⟩ i _
      exact ⟨ξ i, rfl⟩
  haveI : Countable G := by
    have : Function.Surjective (fun ξ : ι → F => (⟨fun i => algebraMap F (AF F) (ξ i), (hmemG _).2 ⟨ξ, rfl⟩⟩ : G)) := by
      rintro ⟨v, hv⟩
      obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
      exact ⟨ξ, rfl⟩
    exact this.countable
  have hFD := isFD_pi (ι := ι) ν hD
  have hmass : (Measure.pi fun _ : ι => ν) (Set.univ.pi fun _ : ι => D) = 1 := by
    rw [Measure.pi_pi]; simp [hD1]
  have hrat : ∀ (B : Matrix ι ι F) (ξ : ι → F), (B.map (algebraMap F (AF F))).mulVec (fun i => algebraMap F (AF F) (ξ i)) =
      fun i => algebraMap F (AF F) (B.mulVec ξ i) := by
    intro B ξ
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) B ξ i).symm
  have hu := GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map (R := AF F) A hA
  have hinv : (A.map (algebraMap F (AF F)))⁻¹ = A⁻¹.map (algebraMap F (AF F)) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  have := map_eq_of_isFD (Measure.pi fun _ : ι => ν) G hFD (by rw [hmass]; simp) (by rw [hmass]; simp)
    (GlobalTheory.CompanionTheory.SW.SdCoord.matE _ hu) ?_ ?_
  · exact this
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A⁻¹.mulVec ξ, ?_⟩
    change (A.map (algebraMap F (AF F)))⁻¹.mulVec _ = _
    rw [hinv, hrat]
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A.mulVec ξ, ?_⟩
    exact hrat A ξ
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


namespace GlobalTheory.CompanionTheory.ReadLevel

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ g ∈ K, ρ g v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

theorem extTensor_twRep {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (χ : G →* ℂˣ) (ψ : H →* ℂˣ)
    (m : G × H) (x : V ⊗[ℂ] W) :
    GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ) m x =
      ((χ m.1 * ψ m.2 : ℂˣ) : ℂ) • GlobalTheory.SmGL.extTensor ρ σ m x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v u =>
    rw [GlobalTheory.SmGL.extTensor_tmul, GlobalTheory.SmGL.extTensor_tmul, twRep_apply, twRep_apply,
      TensorProduct.smul_tmul_smul, Units.val_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem isSpherical_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {K : Subgroup G}
    (h : fixed σ K ≠ ⊥) : GlobalTheory.LGrp.IsSpherical ρ K := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine (Submodule.ne_bot_iff _).2 ⟨φ.toLinearEquiv.symm v, ?_, fun e => hv0 (by
    have h2 := congrArg φ.toLinearEquiv e
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2)⟩
  refine mem_fixed_iff.2 fun g hg => φ.toLinearEquiv.injective ?_
  have h1 : φ.toLinearEquiv (ρ g (φ.toLinearEquiv.symm v)) = σ g (φ.toLinearEquiv (φ.toLinearEquiv.symm v)) :=
    LinearMap.congr_fun (φ.isIntertwining' g) _
  rw [h1, LinearEquiv.apply_symm_apply]
  exact mem_fixed_iff.1 hv g hg

theorem fixed_ind₂_ne_bot (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin a) k × GL (Fin b) k) W) (K : Subgroup (GL (Fin n) k))
    (hK : IsOpen (K : Set (GL (Fin n) k))) (x : W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      ((GlobalTheory.SmGL.deltaHalf k (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p) : ℂˣ) : ℂ) •
        ρ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x) :
    fixed (GlobalTheory.SmGL.ind₂ e ρ) K ≠ ⊥ :=
  GlobalTheory.T.induced_fixed_nonzero _ _ _ _ K hK x hx hfix

theorem exists_fixed_of_sep {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G V} {S : Submodule ℂ V} {τ : Representation ℂ G X}
    (hs : Sep ρ S τ) {L : Subgroup G} (hL : IsOpen (L : Set G)) {v : V} (hv : v ∈ S) (hv0 : v ≠ 0)
    (hfix : v ∈ fixed ρ L) : ∃ x : X, x ≠ 0 ∧ ∀ m ∈ L, τ m x = x := by
  obtain ⟨-, J, Lj, hLj, hsep⟩ := hs
  have hsm : SmVec ρ v := ⟨L, hL, hfix⟩
  obtain ⟨j, hj⟩ : ∃ j, Lj j v ≠ 0 := by
    by_contra hc
    exact hv0 (hsep v hv hsm fun j => by_contra fun hj => hc ⟨j, hj⟩)
  refine ⟨Lj j v, hj, fun m hm => ?_⟩
  rw [← hLj j m v hv hsm, mem_fixed_iff.1 hfix m hm]

theorem fixed_ind₂_twist (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin a) k) V) (σ : Representation ℂ (GL (Fin b) k) W)
    (χ : GL (Fin a) k →* ℂˣ) (ψ : GL (Fin b) k →* ℂˣ)
    (K : Subgroup (GL (Fin n) k)) (hKo : IsOpen (K : Set (GL (Fin n) k))) (hKc : IsCompact (K : Set (GL (Fin n) k)))
    (x : V ⊗[ℂ] W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      GlobalTheory.SmGL.extTensor ρ σ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x ∧
      χ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).1 *
        ψ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).2 = 1) :
    fixed (GlobalTheory.SmGL.ind₂ e (GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ))) K ≠ ⊥ := by
  refine fixed_ind₂_ne_bot k e _ K hKo x hx fun p hp => ?_
  obtain ⟨h1, h2⟩ := hfix p hp
  rw [GlobalTheory.T.modulus_trivial_on_compact_parabolic k a b n e K hKc p hp, Units.val_one, one_smul, extTensor_twRep, h1, h2, Units.val_one, one_smul]

theorem isSpherical_of_join (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) U)
    (ρ : Representation ℂ (GL (Fin a) k) V) (σ : Representation ℂ (GL (Fin b) k) W)
    (χ : GL (Fin a) k →* ℂˣ) (ψ : GL (Fin b) k →* ℂˣ)
    (φ : π.Equiv (GlobalTheory.SmGL.ind₂ e (GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ))))
    (K : Subgroup (GL (Fin n) k)) (hKo : IsOpen (K : Set (GL (Fin n) k))) (hKc : IsCompact (K : Set (GL (Fin n) k)))
    (x : V ⊗[ℂ] W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      GlobalTheory.SmGL.extTensor ρ σ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x ∧
      χ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).1 *
        ψ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).2 = 1) :
    GlobalTheory.LGrp.IsSpherical π K :=
  isSpherical_of_equiv φ (fixed_ind₂_twist k e ρ σ χ ψ K hKo hKc x hx hfix)

theorem loc_pow {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (w : Pl E) (k : ℕ)
    (x : (w.adicCompletion E)ˣ) : (μ ^ k).loc w x = μ.loc w (x ^ k) := by
  rw [map_pow]
  induction k with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem twist_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (μ : HChar E) (w : Pl E)
    (m : GLw a w × GLw b w)
    (h : μ.loc w (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1) :
    (((μ ^ b).loc w).comp GeneralLinearGroup.det) m.1 * (((μ ^ a).loc w).comp GeneralLinearGroup.det) m.2 = 1 := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, loc_pow, loc_pow, ← map_mul, h]

theorem levi_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (K : Subgroup (GLw n w)) (Q : GLw a w × GLw b w → Prop) (hKQ : ∀ m X, blk h w m X ∈ K → Q m)
    (p : GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))) (hp : (p : GLw n w) ∈ K) :
    Q ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p)) := by
  obtain ⟨X, hX⟩ := GlobalTheory.T.parabolic_element_block_form E n a b h w p
  exact hKQ _ X (hX ▸ hp)


theorem rReadLev : RReadLev := by
  intro hR hJ E _ _ _ n a b h μ s₁ s₂ Pa Pb D c w K L G hKo hKc hLo hKL hG hG0 hGL
  obtain ⟨x, hx0, hx⟩ := exists_fixed_of_sep (hR E a b s₁ s₂ Pa Pb w c.g₁ c.g₂ c.u₁ c.u₂ c.t₁ c.t₂) hLo hG hG0 hGL
  obtain ⟨φ⟩ := hJ E n a b h (μ ^ b) (μ ^ a) Pa Pb D w c.join
  exact isSpherical_of_join (w.adicCompletion E) (GlobalTheory.SmGL.stdSum h) (lp D w) (lp Pa w) (lp Pb w)
    (((μ ^ b).loc w).comp GeneralLinearGroup.det) (((μ ^ a).loc w).comp GeneralLinearGroup.det)
    φ K hKo hKc x hx0 fun p hp =>
      have hq := levi_of_mem h w K _ hKL p hp
      ⟨hx _ hq.1, twist_eq_one μ w _ hq.2⟩

end GlobalTheory.CompanionTheory.ReadLevel
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.PairDom

theorem isFundamentalDomain_range_prodMap {A B X Y : Type} [Group A] [Group B] [Group X] [Group Y]
    [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X] [IsTopologicalGroup Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] (f : A →* X) (g : B →* Y) (F : Set X) (G : Set Y)
    (hF : IsFundamentalDomain f.range F μ) (hG : IsFundamentalDomain g.range G ν) :
    IsFundamentalDomain (f.prodMap g).range (F ×ˢ G) (μ.prod ν) := by
  have hmp : ∀ z : X × Y, MeasurePreserving (z * ·) (μ.prod ν) (μ.prod ν) := fun z =>
    measurePreserving_mul_left (μ.prod ν) z
  refine IsFundamentalDomain.mk'' (hF.nullMeasurableSet.prod hG.nullMeasurableSet) ?_ ?_
    (fun γ => (hmp γ).quasiMeasurePreserving)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hF.ae_covers,
      Measure.quasiMeasurePreserving_snd.ae hG.ae_covers] with z h1 h2
    obtain ⟨⟨_, a, rfl⟩, ha⟩ := h1
    obtain ⟨⟨_, b, rfl⟩, hb⟩ := h2
    exact ⟨⟨(f a, g b), (a, b), rfl⟩, ha, hb⟩
  · rintro ⟨_, ⟨a, b⟩, rfl⟩ hγ
    by_cases ha : f a = 1
    · have hb : (⟨g b, b, rfl⟩ : g.range) ≠ 1 := by
        intro h
        apply hγ
        apply Subtype.ext
        exact Prod.ext ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).preimage_null (hG.aedisjoint hb)
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.2, hw.2, rfl⟩, ⟨_, hz.2, one_smul _ _⟩⟩
    · have ha' : (⟨f a, a, rfl⟩ : f.range) ≠ 1 := by
        intro h
        exact ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).preimage_null (hF.aedisjoint ha')
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.1, hw.1, rfl⟩, ⟨_, hz.1, one_smul _ _⟩⟩

theorem exists_measure_of_eq {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ₁ : Measure X) (μ₂ : Measure Y)
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [μ₁.IsMulRightInvariant] [μ₂.IsMulRightInvariant]
    (Γ : Subgroup (X × Y)) (F : Set (X × Y)) (hF : IsFundamentalDomain Γ F (μ₁.prod μ₂))
    (m : MeasurableSpace (X × Y)) (e : Prod.instMeasurableSpace = m) :
    ∃ μ : @Measure (X × Y) m,
      (@Measure.IsMulLeftInvariant _ m _ μ ∧ @Measure.IsMulRightInvariant _ m _ μ ∧
        @Measure.IsOpenPosMeasure _ _ m μ ∧ @IsLocallyFiniteMeasure _ m _ μ) ∧
      @IsFundamentalDomain Γ (X × Y) _ _ m F μ ∧
      ∀ f : X × Y → ℂ, @integral _ _ _ _ m (@Measure.restrict _ m μ F) f =
        @integral _ _ _ _ Prod.instMeasurableSpace ((μ₁.prod μ₂).restrict F) f := by
  subst e
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  exact ⟨μ₁.prod μ₂, ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hF, fun _ => rfl⟩

theorem isMulRightInvariant_GA (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    [m : MeasurableSpace (GA E a)] [hm : BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  obtain ⟨ν, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have e : m = CuspidalL2GL.measurableSpace_GA E a := hm.measurable_eq
  subst e
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  letI := h2
  rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  exact MeasureTheory.isMulRightInvariant_smul (μ := ν) _

theorem prodDom : RatProper → ProdDom := by
  intro _ E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ h₁ h₂
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI := isMulRightInvariant_GA E a μ₁
  haveI := isMulRightInvariant_GA E b μ₂
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨μ, hh, hf, hi⟩ := exists_measure_of_eq μ₁ μ₂ (ratH E a b) (F₁ ×ˢ F₂)
    (isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ h₁ h₂) (borelH E a b)
    Prod.borelSpace.measurable_eq
  exact ⟨⟨μ, hh, F₁ ×ˢ F₂, hf⟩, rfl, fun f => hi f⟩

end GlobalTheory.CompanionTheory.PairDom
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.MatInt

theorem algebraMap_mem_integers_of_not_mem_support (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : F) (h : v ∉ HeightOneSpectrum.Support (𝓞 F) a) :
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap F (Fv F v) a) = v.valuation F a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  rw [e]
  simpa [HeightOneSpectrum.Support] using h

theorem mulVec_mem_integers (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (v : HeightOneSpectrum (𝓞 F)) (B : Matrix ι ι (Fv F v)) (y : ι → Fv F v)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F)
    (hy : ∀ i, y i ∈ v.adicCompletionIntegers F) (i : ι) :
    B.mulVec y i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hB i j) (hy j)

theorem exists_finset_mulVec_integral_iff : ∀ (F : Type) [Field F] [NumberField F] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 →
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ x : ι → Fv F v,
      (∀ i, (A.map (algebraMap F (Fv F v))).mulVec x i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
  intro F _ _ ι _ _ A hA
  classical
  have hfin : ∀ a : F, (HeightOneSpectrum.Support (𝓞 F) a).Finite :=
    HeightOneSpectrum.Support.finite (𝓞 F)
  refine ⟨Finset.univ.biUnion fun p : ι × ι =>
    (hfin (A p.1 p.2)).toFinset ∪ (hfin (A⁻¹ p.1 p.2)).toFinset, fun v hv x => ?_⟩
  have hout : ∀ i j, v ∉ HeightOneSpectrum.Support (𝓞 F) (A i j) ∧
      v ∉ HeightOneSpectrum.Support (𝓞 F) (A⁻¹ i j) := by
    intro i j
    constructor
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_left _ ((hfin _).mem_toFinset.2 h)⟩)
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_right _ ((hfin _).mem_toFinset.2 h)⟩)
  have hinv : (A⁻¹.map (algebraMap F (Fv F v))) * (A.map (algebraMap F (Fv F v))) = 1 := by
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
    have h1 := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F (Fv F v)))
      (Matrix.nonsing_inv_mul A hu)
    simpa [Matrix.map_mul] using h1
  constructor
  · intro h i
    have e : (A⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((A.map (algebraMap F (Fv F v))).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [← e]
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).2) h i
  · intro h i
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).1) h i

end GlobalTheory.CompanionTheory.MatInt
end
