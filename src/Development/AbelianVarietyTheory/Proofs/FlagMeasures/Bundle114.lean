module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle101
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle102
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoveringSetExpLieLatticeRootGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentialUnipotentStabilizer
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.UnitaryModelOfMultiplicityGardingDensity
import Formalism.PeriodIntegrals.UpqRep

@[expose] public section

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem isChar_comp_hom {G M : Type} [Group G] [Group M] (π : G →* M) (χ : M → ℂ)
    (h : IsChar χ) : IsChar (fun x => χ (π x)) := by
  obtain ⟨V, hV⟩ := h
  exact ⟨FDRep.of (V.ρ.comp π), fun x => hV (π x)⟩

theorem isChar_mul_fun {G : Type} [Group G] (α β : G → ℂ) (hα : IsChar α) (hβ : IsChar β) :
    IsChar (fun x => α x * β x) := by
  obtain ⟨V, hV⟩ := hα
  obtain ⟨W, hW⟩ := hβ
  refine ⟨CategoryTheory.MonoidalCategoryStruct.tensorObj V W, fun x => ?_⟩
  rw [FDRep.char_tensor, Pi.mul_apply, hV, hW]

theorem isChar_comp_hom_and_mul :
    (∀ (G M : Type) [Group G] [Group M] (π : G →* M) (χ : M → ℂ),
      IsChar χ → IsChar (fun x => χ (π x))) ∧
    ∀ (G : Type) [Group G] (α β : G → ℂ), IsChar α → IsChar β → IsChar (fun x => α x * β x) :=
  ⟨fun _ _ _ _ π χ h => isChar_comp_hom π χ h, fun _ _ α β hα hβ => isChar_mul_fun α β hα hβ⟩

end GlobalTheory.GLm
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsFullLattice K L → ENNReal.ofReal (mass h L) = orbMass (isom h) (genus h L) ∧ 0 < mass h L ∧ Stable (isom h) (genus h L) ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → Finite (MulAction.stabilizer (isom h) M)) ∧ ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : isom h) M, N (g • M) = N M) → ∑ M ∈ s, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M = orbSum (isom h) (genus h L) N := by
  first
  | exact @GlobalTheory.Mass.GenusOrb.main
  | intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
    obtain ⟨a, b, c, d, e⟩ := GlobalTheory.Mass.GenusOrb.main K V h hK hs hp L hL.toIsLattice
    exact ⟨a, b, c, fun M hM => d M hM.toIsLattice, e⟩
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFramePair_amplitude_mass_reps_eq_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) ∧ LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧ (∑' t : R.RT d, ENNReal.ofReal (LocNG.mu P t.1)) = S.mass (c.dat d) (fun _ => True) := by
  first | exact @GlobalTheory.HL.CoordAmp.amp_mass_eq | exact GlobalTheory.HL.CoordAmp.amp_mass_eq | (intros; apply GlobalTheory.HL.CoordAmp.amp_mass_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F L ↔ ∀ v : HeightOneSpectrum (𝓞 F), prVec v x ∈ loc v L := by
  first | exact @GlobalTheory.St.G.mem_hat_iff_forall_loc | exact GlobalTheory.St.G.mem_hat_iff_forall_loc | (intros; apply GlobalTheory.St.G.mem_hat_iff_forall_loc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FrLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) :
    prV (E := E) v (sigR σ (Ad F) a) = sigR σ (v.adicCompletion F) (prV (E := E) v a) :=
  RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) a

theorem prV_OAd (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) :
    prV (E := E) v a ∈ intV E v :=
  ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).1 a).1 ha v

theorem prVec_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → E ⊗[F] Ad F) :
    prVec v (x + y) = prVec v x + prVec v y := by
  funext i; simp [prVec, map_add (f := _)]

theorem prVec_zero (v : HeightOneSpectrum (𝓞 F)) : prVec v (0 : Fin n → E ⊗[F] Ad F) = 0 := by
  funext i; simp [prVec]

theorem prVec_smul (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (a • x) = prV (E := E) v a • prVec v x := by
  funext i; simp [prVec, map_mul]

theorem prVec_span (v : HeightOneSpectrum (𝓞 F)) (S : Set (Fin n → E ⊗[F] Ad F))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ Submodule.span (OAd F E) S) :
    prVec v x ∈ Submodule.span (intV E v) (prVec v '' S) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero => rw [prVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [prVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have h : prVec v (a • x) = (⟨prV (E := E) v a, prV_OAd v a.2⟩ : intV E v) • prVec v x :=
      prVec_smul v (a : E ⊗[F] Ad F) x
    rw [h]; exact Submodule.smul_mem _ _ hx

theorem prVec_hat (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ hat F L) : prVec v x ∈ loc v L := by
  have h := prVec_span v _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  exact ⟨l, hl, rfl⟩

theorem hR_prVec (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Ad F) :
    hR σ J (v.adicCompletion F) (prVec v x) (prVec v y) = prV (E := E) v (hR σ J (Ad F) x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, prV_sigR, prVec, Matrix.map_apply, Formalism.UG.P.afsplit_prV_inclE]

end GlobalTheory.St.G.FrLoc

open GlobalTheory.St.G.FrLoc in
theorem GlobalTheory.St.G.frame_component_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  intro F E _ _ _ _ _ σ n J L g k Fr v
  refine ⟨?_, ?_, prV_OAd v Fr.eps_int, ?_, fun i => prVec_hat v L (Fr.b_mem i),
    fun i => prVec_hat v L (Fr.bd_mem i), ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, Fr.eps_idem]
  · rw [← prV_sigR, ← map_mul, Fr.eps_orth, map_zero]
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨z, hz, hzeq⟩ := Fr.eps_full (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) hzeq
      rw [prVec_smul, prVec_smul, map_sub, map_sub, map_one, prV_sigR, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z₁, hz₁, e₁⟩ := hx
      obtain ⟨z₂, hz₂, e₂⟩ := hy
      exact ⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [smul_add, smul_add, e₁, e₂]⟩
    | smul c x _ hx =>
      obtain ⟨z, hz, e⟩ := hx
      refine ⟨c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, smul_smul, mul_comm, ← smul_smul, e, smul_smul,
        smul_smul, mul_comm]
  · intro i
    have h := congrArg (prVec v) (Fr.b_eps i)
    rw [prVec_smul] at h
    exact h
  · intro i
    have h := congrArg (prVec v) (Fr.bd_eps i)
    rw [prVec_smul, prV_sigR] at h
    exact h
  · intro i j
    obtain ⟨t, ht, e⟩ := Fr.dual i j
    refine ⟨prV (E := E) v t, prV_OAd v ht, ?_⟩
    have h := congrArg (prV (E := E) v) e
    rw [map_sub, map_mul, map_natCast, ← hR_prVec, apply_ite (prV (E := E) v), map_zero] at h
    exact h
  · have hsub : prVec v '' (Set.range Fr.b ∪ Set.range Fr.bd) ⊆
        Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j)) := by
      rintro _ ⟨x, hx | hx, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inl ⟨j, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inr ⟨j, rfl⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨s, hs, z, hz, e⟩ := Fr.span (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v s, Submodule.span_mono hsub (prVec_span v _ hs), prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) e
      rw [prVec_add, prVec_smul, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s₁, hs₁, z₁, hz₁, e₁⟩ := hx
      obtain ⟨s₂, hs₂, z₂, hz₂, e₂⟩ := hy
      refine ⟨s₁ + s₂, add_mem hs₁ hs₂, z₁ + z₂, add_mem hz₁ hz₂, ?_⟩
      rw [e₁, e₂, smul_add]; abel
    | smul c x _ hx =>
      obtain ⟨s, hs, z, hz, e⟩ := hx
      refine ⟨c • s, Submodule.smul_mem _ c hs, c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [e, smul_add, Subring.smul_def, Subring.smul_def, Subring.smul_def, smul_smul, smul_smul,
        mul_comm]
end
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ a : E ⊗[F] Ad F, a ∈ OAd F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) ∧ (∀ a ∈ OAd F E, ∀ m : ℕ, 0 < m → ∃ x : 𝓞 E, ∃ t ∈ OAd F E, a = inclE (F := F) (Ad F) (x : E) + (m : E ⊗[F] Ad F) * t) ∧ (∀ a : E ⊗[F] Ad F, (∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) → a = 0) ∧ (∀ a : E ⊗[F] Ad F, ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E) ∧ (∀ x : E, inclE (F := F) (Ad F) x ∈ OAd F E ↔ x ∈ intOE E) := by
  first | exact @GlobalTheory.St.G.IntAd.integral_adeles_properties | exact GlobalTheory.St.G.IntAd.integral_adeles_properties | (intros; apply GlobalTheory.St.G.IntAd.integral_adeles_properties <;> assumption)
end

section

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.exists_covering_set_exp_lie_lattice_rootGroup : ∀ (ι : Type) [Fintype ι] (N : ℕ) (R : Finset (Fin N × Fin N)) (Λ : Submodule ℤ (ι → R → ℂ)) (Ω₀ : Set (ι → R → ℂ)), (∀ q ∈ R, q.1 < q.2) → (∀ a b c : Fin N, (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R) → MeasurableSet Ω₀ → MeasureTheory.IsAddFundamentalDomain Λ Ω₀ MeasureTheory.volume → MeasureTheory.volume Ω₀ ≠ ⊤ → DiscreteTopology Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ z ∈ Λ, ∀ v, expT (ofRoots R (x v) - 1) * expT (ofRoots R (y v) - 1) = expT (ofRoots R (z v) - 1)) → ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω = MeasureTheory.volume Ω₀ ∧ ∀ c : ι → R → ℂ, ∃ x ∈ Λ, (fun v (q : R) => (expT (ofRoots R (x v) - 1) * ofRoots R (c v) : Matrix (Fin N) (Fin N) ℂ) q.1.1 q.1.2) ∈ Ω := by
  first | exact @GlobalTheory.LoopV.Cover.cover | exact GlobalTheory.LoopV.Cover.cover | (intros; apply GlobalTheory.LoopV.Cover.cover <;> assumption)
end

section

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.exponential_unipotent_stabilizer : ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (Z : Matrix (Fin N) (Fin N) K) (I : Ideal (𝓞 K)), Z.det ≠ 0 → (∀ x ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → expT x ∈ stabU Z ∧ EntIn I (expT x - 1) ∧ expT x * expT (-x) = 1) ∧ ∀ x ∈ lieU Z, ∀ y ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) y → ∃ z ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) z ∧ expT x * expT y = expT z := by
  first | exact @GlobalTheory.LoopV.ExpGroup.exp_group | exact GlobalTheory.LoopV.ExpGroup.exp_group | (intros; apply GlobalTheory.LoopV.ExpGroup.exp_group <;> assumption)
end

section

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.gramUnipotentStabilizer_bruhatCell_conj_root : ∀ (K : Type) [Field K] (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N), IsLoUni L → IsUpUni U → (∀ a, a ∈ stabU (L * ptMat p * U) ↔ U * a * U⁻¹ ∈ stabU (ptMat p)) ∧ (∀ x, x ∈ lieU (L * ptMat p * U) ↔ U * x * U⁻¹ ∈ lieU (ptMat p)) ∧ (∀ a, a ∈ stabU (ptMat p) ↔ IsUpUni a ∧ ∀ i j, i < j → (i, j) ∉ roots (ptMat p) → a i j = 0) ∧ (∀ x, x ∈ lieU (ptMat p) ↔ ∀ i j, (i, j) ∉ roots (ptMat p) → x i j = 0) := by
  first | exact @GlobalTheory.LoopV.Cell.stab_cell | exact GlobalTheory.LoopV.Cell.stab_cell | (intros; apply GlobalTheory.LoopV.Cell.stab_cell <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Set Metric
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.SmLinSub

section Smoothing

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UpqRep PI.KFinSmoothW

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem expS_mul_neg (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • Z) * NormedSpace.exp (t • -Z) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Z).neg_right.smul_left t).smul_right t)]
  simp [smul_neg]

theorem expS_neg_mul (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • -Z) * NormedSpace.exp (t • Z) = 1 := by
  have h := expS_mul_neg (-Z) t
  rwa [neg_neg] at h

end Smoothing

end GlobalTheory.SmLinSub

namespace GlobalTheory.SmLinSub

section Rep

open Formalism.MainNotions.S GlobalTheory.Ell

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem lie_smulR (c : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) : c • X ∈ lieOf G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (c • X)ᴴ * G + G * (c • X) = 0
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

theorem exp_mem {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G :=
  CCRuleCW.exp_mem_UH G (t • X) (lie_smulR t hX)

theorem listProd_mem : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH G) →
    l.prod ∈ Formalism.QuantumDeterminants.UH G
  | [], _ => by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
    simp
  | g :: l, h => by
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul G _ _ (h g (by simp)) (listProd_mem l fun x hx => h x (by simp [hx]))

theorem expProd_mem {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieOf G)
    (t : Fin k → ℝ) : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH G :=
  listProd_mem _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem (hX i) _

theorem isUnit_of_mem (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) : IsUnit g := by
  have h : gᴴ * G * g = G := hg
  exact isUnit_of_mul_isUnit_right (h.symm ▸ hG : IsUnit (gᴴ * G * g))

theorem conj_mem_lie (hG : IsUnit G) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieOf G) : g⁻¹ * X * g ∈ lieOf G := by
  have h : gᴴ * G * g = G := hg
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem hG hg)
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  show (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by rw [h1, h2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX']; simp

theorem rep_mul (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hg' : g' ∈ Formalism.QuantumDeterminants.UH G) (w : H) : ρ (g * g') w = ρ g (ρ g' w) := by
  rw [hπ.1.2 g hg g' hg']; rfl

theorem exp_conj_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := by
  rw [← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]

theorem hasDerivAt_dR {w : H} (hw : SmV (lieOf G) ρ w) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) :
    HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) w) (dR ρ X w) 0 := by
  have h1 := hw 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t := contDiff_pi.2 fun _ => contDiff_id
  have h3 : ContDiff ℝ ∞ fun t : ℝ => ρ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h1.comp h2
  exact (h3.differentiable (by simp) 0).hasDerivAt

theorem contDiff_deriv_snoc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {F : (Fin (k + 1) → ℝ) → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => deriv (fun s : ℝ => F (Fin.snoc t s)) 0 := by
  have hs : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h1 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) => F (Fin.snoc t s)) := hF.comp hs
  have h2 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : Fin k → ℝ => (0 : ℝ)) h1 contDiff_const
    (le_of_eq rfl)
  exact h2.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem dR_mem (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) : SmV (lieOf G) ρ (dR ρ X w) := by
  intro k Xs hXs
  have h1 := hw (k + 1) (Fin.snoc Xs X) (fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  convert contDiff_deriv_snoc h1 using 2 with t
  have h2 := (((ρ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dR hw hX) :
    HasDerivAt (fun s : ℝ => ρ (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod
      (ρ (NormedSpace.exp (s • X)) w)) _ 0)
  refine h2.deriv.symm.trans ?_
  congr 1
  funext s
  show ρ _ (ρ _ w) = _
  rw [← rep_mul hπ (expProd_mem hXs t) (exp_mem hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

theorem rep_mem (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) : SmV (lieOf G) ρ (ρ g w) := by
  intro k Xs hXs
  have hu := isUnit_of_mem hG hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieOf G := fun i => conj_mem_lie hG hg (hXs i)
  have h1 := ((ρ g).restrictScalars ℝ).contDiff.comp (hw k _ hY)
  convert h1 using 2 with t
  show _ = ρ g _
  rw [← rep_mul hπ (expProd_mem hXs t) hg, ← rep_mul hπ hg (expProd_mem hY t), ← prod_conj hu,
    List.map_ofFn]
  simp only [exp_conj_inv hu, Function.comp_def]

theorem dR_rep (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hX : X ∈ lieOf G) :
    dR ρ X (ρ g w) = ρ g (dR ρ (g⁻¹ * X * g) w) := by
  have hu := isUnit_of_mem hG hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hY := conj_mem_lie hG hg hX
  have h2 := (((ρ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dR hw hY) :
    HasDerivAt (fun s : ℝ => ρ g (ρ (NormedSpace.exp (s • (g⁻¹ * X * g))) w)) _ 0)
  refine Eq.trans ?_ h2.deriv
  unfold dR
  congr 1
  funext s
  show _ = ρ g (ρ _ w)
  rw [← rep_mul hπ hg (exp_mem hY s), ← rep_mul hπ (exp_mem hX s) hg, exp_conj_inv hu]
  simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

end Rep

end GlobalTheory.SmLinSub
end
end
