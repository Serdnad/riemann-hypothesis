module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScaling
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCount
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle051
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle052
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle034
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.adelic_haar_measure_scaling : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → (∀ (c : F), c ≠ 0 → ∀ s : Set (A F), MeasurableSet s → lf ((fun x => algebraMap F (A F) c * x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ c : ℚ) : ℝ)|⁻¹) * lf s) ∧ (∀ b : F, lf {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} = ((den b : ℝ≥0∞))⁻¹) ∧ ∀ (a : (A F)ˣ) (s : Set (A F)), MeasurableSet s → lf ((fun x => (a : A F) * x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) * lf s := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale | exact GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.standard_adelic_character : ∀ (F : Type) [Field F] [NumberField F], (∃ ψ : AddChar (A F) ℂ, IsStdChar F ψ) ∧ ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → (∀ x, ‖ψ x‖ = 1) ∧ (∀ x ∈ Oh F, ψ x = 1) ∧ ∀ b : F, (∀ x ∈ Oh F, ψ (algebraMap F (A F) b * x) = 1) ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.StdChar.main | exact GlobalTheory.CompanionTheory.SW.Core.StdChar.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.StdChar.main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.weighted_theta_average_le_of_countData : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ κ t : ℝ, 0 < κ → 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) → (∀ v w, κ * (τ w).im ≤ (τ v).im) → (∀ x, Measurable fun ω => thTerm B ρ P (gf ω) (gi ω) φ τ x) ∧ ENNReal.ofReal (wt M τ) * ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr ≤ ENNReal.ofReal C := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound | exact GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound | (intros; apply GlobalTheory.CompanionTheory.SW.Core.ThetaBound.theta_integral_bound <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem lattice_mass_fibre_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ n : ℕ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m', IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → IsGramFib (Fv F v) σ J' n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ S, m S (latV b v) = m' S (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ J' hJ' d b n
  filter_upwards [GlobalTheory.T.hermitian_forms_integrally_equivalent_almost_all F E σ hσ M J hJ J' hJ' d b] with v hv
  intro lam hlam m m' hm hm' S
  obtain ⟨g, hg, hlat⟩ := hv
  have hL := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hL
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  haveI := hlam.1
  obtain ⟨-, c2, c3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam hlam.1
  haveI := c2 n M
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b n M v
  have hcont : ∀ k : GL (Fin M) (Fv F v ⊗[F] E),
      Continuous (actTup (Fv F v) (n := n) k) := by
    intro k
    refine continuous_pi fun a => ?_
    exact Continuous.matrix_mulVec continuous_const ((continuous_apply a))
  have hinv : ∀ (k l : GL (Fin M) (Fv F v ⊗[F] E)), k * l = 1 → ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      actTup (Fv F v) k (actTup (Fv F v) l X) = X := by
    intro k l hkl X
    funext a
    have h : (k : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * (l : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) = 1 := by
      rw [← Units.val_mul, hkl, Units.val_one]
    simp only [actTup, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  let e : (Fin n → Fin M → Fv F v ⊗[F] E) ≃+ (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { toFun := actTup (Fv F v) g
      invFun := actTup (Fv F v) g⁻¹
      left_inv := hinv g⁻¹ g (inv_mul_cancel g)
      right_inv := hinv g g⁻¹ (mul_inv_cancel g)
      map_add' := by
        intro X Y
        funext a
        simp only [actTup, Pi.add_apply, Matrix.mulVec_add] }
  have hmap : (coordW (Fv F v) b lam n M).map e = coordW (Fv F v) b lam n M :=
    (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open _ _ (coordW (Fv F v) b lam n M) (coordW (Fv F v) b lam n M) e (hcont g)
      (hcont g⁻¹)).2 (latV b v) (latV b v) a1 a2 ⟨0, a3⟩ (hlat n) rfl
  have hfib := GlobalTheory.T.gram_fiber_measures_change_of_form F E σ hσ M J hJ J' hJ' (Fv F v) hL n (coordW (Fv F v) b lam n M)
    (coordHerm (Fv F v) σ b lam n) m (c2 n M) (c3 n) hm (coordW (Fv F v) b lam n M) m' (c2 n M) hm' g hg 1
    (by rw [one_smul]; exact hmap) S
  have hval := congrArg (fun μ => μ (latV b v)) hfib
  simp only [one_smul] at hval
  rw [Measure.map_apply (hcont g).measurable a2.measurableSet] at hval
  have hpre : actTup (Fv F v) (n := n) g ⁻¹' latV (M := M) (n := n) b v = latV b v := by
    ext X
    exact hlat n X
  rw [hpre] at hval
  exact hval.symm

end GlobalTheory.CompanionTheory.SW
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GoodScale

theorem map_eq_self {V : Type} [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [IsTopologicalAddGroup V] (μ : Measure V) [μ.IsAddHaarMeasure] (e f : V → V)
    (he : ∀ x y, e (x + y) = e x + e y) (hef : ∀ x, e (f x) = x) (hfe : ∀ x, f (e x) = x)
    (hec : Continuous e) (hfc : Continuous f) (L : Set V) (hLc : IsCompact L) (hLo : IsOpen L)
    (hLn : L.Nonempty) (heL : ∀ x ∈ L, e x ∈ L) (hfL : ∀ x ∈ L, f x ∈ L) : μ.map e = μ := by
  let e' : V ≃+ V :=
    { toFun := e, invFun := f, left_inv := hfe, right_inv := hef, map_add' := he }
  exact (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open V V μ μ e' hec hfc).2 L L hLc hLo hLn
    (fun x => ⟨fun h => by simpa [e', hfe] using hfL _ h, heL x⟩) rfl

theorem mul_entry_mem {K : Type} [CommRing K] (O : Subring K) {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (i j : Fin n) :
    (A * B) i j ∈ O := by
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hA i k) (hB k j)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rmul_add (R : Type) [CommRing R] [Algebra F R] {M n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X Y : Fin n → Fin M → R ⊗[F] E) :
    rmul R (X + Y) g = rmul R X g + rmul R Y g := by
  funext a i
  simp [rmul, add_mul, Finset.sum_add_distrib]

theorem continuous_rmul (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hK : IsTopologicalRing (R ⊗[F] E)) {M n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous (fun X : Fin n → Fin M → R ⊗[F] E => rmul R X g) := by
  haveI := hK
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [rmul]
  exact continuous_finsetSum _ fun c _ =>
    (continuous_apply_apply c i).mul continuous_const

theorem mass_eq_of_integral (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (hσ : ∀ y ∈ O, sigR (Fv F v) σ y ∈ O)
    (g gi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (hg : ∀ i j, g i j ∈ O)
    (hgi : ∀ i j, gi i j ∈ O) (hggi : g * gi = 1) (hgig : gi * g = 1)
    (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m)
    (S S' : HermR (Fv F v) σ n)
    (hS : (S' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      cT (sigR (Fv F v) σ) g * (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * g) :
    m S' (latV b v) = m S (latV b v) := by
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR; haveI := hLC; haveI := hSC; haveI := hT2
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hKring, hKlc, hKsc, hKt2, -, -, -, hWb, hHcl, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := hKring; haveI := hKlc; haveI := hKsc; haveI := hKt2
  haveI := hWb n M
  haveI hWb' := hWb n n
  obtain ⟨hHlc, hHsc, hHt2, hHb, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM (Fv F v) n
  haveI := hHlc; haveI := hHsc; haveI := hHt2; haveI := hHb
  obtain ⟨-, hμ, hν⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1
  haveI := hμ n M
  haveI := hν n
  obtain ⟨-, hcomp, hone, hherm, -⟩ := GlobalTheory.T.gram_right_action_identities F E σ hCM M J hJ (Fv F v) n
  obtain ⟨hLc, hLo, hL0, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b n M v
  obtain ⟨hLc', hLo', hL0', -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b n n v
  have hrm : ∀ (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), (∀ i j, h i j ∈ O) →
      ∀ X ∈ latV (M := M) (n := n) b v, rmul (Fv F v) X h ∈ latV (M := M) (n := n) b v := by
    intro h hh X hX a i
    exact (hO _).1 (O.sum_mem fun c _ => O.mul_mem ((hO _).2 (hX c i)) (hh c a))
  have hmapW : (coordW (Fv F v) b lam n M).map (fun X => rmul (Fv F v) X g) =
      coordW (Fv F v) b lam n M :=
    map_eq_self _ _ (fun X => rmul (Fv F v) X gi) (fun X Y => rmul_add (Fv F v) g X Y)
      (fun X => by simp only [hcomp, hgig, hone]) (fun X => by simp only [hcomp, hggi, hone])
      (continuous_rmul (Fv F v) hKring g) (continuous_rmul (Fv F v) hKring gi) (latV b v) hLc hLo
      ⟨0, hL0⟩ (hrm g hg) (hrm gi hgi)
  have hc1 : cT (sigR (Fv F v) σ) gi * cT (sigR (Fv F v) σ) g = 1 := by
    rw [← cT_mul, hggi, cT_one]
  have hc2 : cT (sigR (Fv F v) σ) g * cT (sigR (Fv F v) σ) gi = 1 := by
    rw [← cT_mul, hgig, cT_one]
  let τ : HermR (Fv F v) σ n → HermR (Fv F v) σ n := fun S => ⟨_, hherm S g⟩
  let τi : HermR (Fv F v) σ n → HermR (Fv F v) σ n := fun S => ⟨_, hherm S gi⟩
  let L' : Set (HermR (Fv F v) σ n) :=
    (Subtype.val : HermR (Fv F v) σ n → Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ⁻¹'
      (latV (M := n) (n := n) b v : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))
  have hconj : ∀ (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), (∀ i j, h i j ∈ O) →
      ∀ (A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)),
      A ∈ (latV (M := n) (n := n) b v : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) →
      cT (sigR (Fv F v) σ) h * A * h ∈
        (latV (M := n) (n := n) b v : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := by
    intro h hh A hA a i
    refine (hO _).1 (mul_entry_mem O (mul_entry_mem O ?_ ?_) hh a i)
    · intro p q
      exact hσ _ (hh q p)
    · intro p q
      exact (hO _).2 (hA p q)
  have hcont : ∀ h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      Continuous (fun A : HermR (Fv F v) σ n =>
        cT (sigR (Fv F v) σ) h * (A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * h) := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hinv : ∀ (h h' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)),
      cT (sigR (Fv F v) σ) h * cT (sigR (Fv F v) σ) h' = 1 → h' * h = 1 →
      ∀ A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      cT (sigR (Fv F v) σ) h * (cT (sigR (Fv F v) σ) h' * A * h') * h = A := by
    intro h h' e1 e2 A
    calc _ = (cT (sigR (Fv F v) σ) h * cT (sigR (Fv F v) σ) h') * A * (h' * h) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
  have hmapH : (coordHerm (Fv F v) σ b lam n).map τ = coordHerm (Fv F v) σ b lam n := by
    refine map_eq_self _ τ τi ?_ ?_ ?_ ((hcont g).subtype_mk _) ((hcont gi).subtype_mk _) L' ?_ ?_
      ⟨0, hL0'⟩ ?_ ?_
    · intro A B
      apply Subtype.ext
      simp [τ, Matrix.mul_add, Matrix.add_mul]
    · intro A
      exact Subtype.ext (hinv g gi hc2 hgig _)
    · intro A
      exact Subtype.ext (hinv gi g hc1 hggi _)
    · exact (hHcl n).isClosedEmbedding_subtypeVal.isCompact_preimage hLc'
    · exact hLo'.preimage continuous_subtype_val
    · intro A hA
      exact hconj g hg _ hA
    · intro A hA
      exact hconj gi hgi _ hA
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_right_inverse hggi
  have hs := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hCM M J hJ (Fv F v) hloc n _ _ m (hμ n M) (hν n) hm g hdet τ
    (fun _ => rfl) 1 1 (by simpa using hmapW) (by simpa using hmapH) S
  simp only [one_smul] at hs
  have hτ : τ S = S' := Subtype.ext hS.symm
  rw [hτ] at hs
  rw [hs, Measure.map_apply (continuous_rmul (Fv F v) hKring g).measurable hLo.measurableSet]
  congr 1
  ext X
  constructor
  · intro hX
    have := hrm gi hgi _ hX
    simpa only [hcomp, hggi, hone] using this
  · exact hrm g hg X

theorem mass_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 → ∀ (T' : Matrix (Fin n) (Fin n) E) (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) g * T * g → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → m (hermOf (Fv F v) σ T' hT') (latV b v) = m (hermOf (Fv F v) σ T hT) (latV b v) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n T hT _ g hg T' hT' hTT' d b
  have hint := (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1
  have hev : ∀ A : Matrix (Fin n) (Fin n) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (A i j)) k ∈
        v.adicCompletionIntegers F := fun A =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hint (A i j)
  filter_upwards [GlobalTheory.T.tensor_integer_ring_almost_all_places F E σ hCM d b, hev g, hev g⁻¹] with v hv hgv hgiv lam hlam m hm
  obtain ⟨O, hO, hσ, -⟩ := hv
  have hu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  have hc : cT (sigR (Fv F v) σ) (g.map (inclR (Fv F v))) =
      (cT (σ : E →+* E) g).map (inclR (Fv F v)) := by
    ext i j
    simp [cT, sigR, inclR]
  refine mass_eq_of_integral σ hCM J hJ n b v O hO hσ (g.map (inclR (Fv F v)))
    (g⁻¹.map (inclR (Fv F v))) (fun i j => (hO _).2 (hgv i j)) (fun i j => (hO _).2 (hgiv i j))
    ?_ ?_ lam hlam m hm _ _ ?_
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · change T'.map (inclR (Fv F v)) = _ * T.map (inclR (Fv F v)) * _
    rw [hTT', Matrix.map_mul, Matrix.map_mul, hc]

end GlobalTheory.CompanionTheory.SW.GoodScale
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.euler_product_measure_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerMove.euler_move | exact GlobalTheory.CompanionTheory.SW.EulerMove.euler_move | (intros; apply GlobalTheory.CompanionTheory.SW.EulerMove.euler_move <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.exists_gram_fiber_measures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ m, IsGramFib R σ J n μ ν m := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib | exact GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib | (intros; apply GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.finite_adele_haar_eq_product_local_measures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → coordW (Af F) b lf n M {X | (∀ v ∈ S, projV v X ∈ A v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} = ∏ v ∈ S, coordW (Fv F v) b (lam v) n M (A v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.WBox.coordW_box | exact GlobalTheory.CompanionTheory.SW.WBox.coordW_box | (intros; apply GlobalTheory.CompanionTheory.SW.WBox.coordW_box <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LocFin

theorem null_of_fibres_null {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) {W : Set V} (hW : MeasurableSet W)
    (h0 : ∀ b, fib b W = 0) : μ (W ∩ U) = 0 := by
  have key := h.2.1 (W.indicator 1) (measurable_one.indicator hW)
  simp only [lintegral_indicator_one hW, h0, lintegral_zero] at key
  rwa [Measure.restrict_apply hW] at key

theorem fibre_loc_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ S : HermR R σ n, IsLocallyFiniteMeasure (m S) ∧ ∀ U : Set (Fin n → Fin M → R ⊗[F] E), IsOpen U → (∃ X ∈ U, gramR R σ J X = S ∧ IsUnit (gramR R σ J X).det) → m S U ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm S
  haveI : IsTopologicalRing R := hR.1
  haveI : LocallyCompactSpace R := hR.2.1
  haveI : SecondCountableTopology R := hR.2.2.1
  haveI : T2Space R := hR.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M
  obtain ⟨h1, h2, h3, h4, h5⟩ := HermTop.herm_top F E σ hσ R n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g, hgc, hg⟩ := h5 M J hJ
  have hKU := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hKU.isOpen_range.preimage hdet
  have hUeq : {X | IsUnit (gramR R σ J X).det} =
      g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hg]
  have hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val
      (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν
      {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m := by
    rw [← hUeq]
    exact hm
  obtain ⟨hloc, -, -, -⟩ := FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hgc hg _ hBo m hfib
  refine ⟨hloc S, ?_⟩
  rintro U hU ⟨X₀, hX₀U, hX₀S, hX₀⟩ h0
  obtain ⟨κ, -, -, -, hκ⟩ := GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hσ M J hJ R hR n μ ν m hμ hν hm
  have hSdet : IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    rw [← hX₀S]
    exact hX₀
  obtain ⟨B₁, gs, hB₁, hSB₁, hgs, hgs1, hgsS⟩ := GlobalTheory.T.hermitian_local_continuous_congruence_section F E σ hσ R hR n S hSdet
  obtain ⟨a1, a2, a3, -, -⟩ := GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hgX₀ : g X₀ = S := Subtype.ext ((hg X₀).symm.trans hX₀S)
  have hr : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × Matrix (Fin n) (Fin n) (R ⊗[F] E) =>
      rmul R p.1 p.2 := by
    unfold rmul
    refine continuous_pi fun a => continuous_pi fun i => continuous_finsetSum _ fun c _ => ?_
    exact ((continuous_apply_apply c i).comp continuous_fst).mul (continuous_snd.matrix_elem c a)
  let T : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun X =>
    rmul R X (((gs (g X))⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
  have hTc : ContinuousOn T (g ⁻¹' B₁) := by
    refine hr.comp_continuousOn (ContinuousOn.prodMk continuousOn_id ?_)
    exact Units.continuous_val.comp_continuousOn
      ((hgs.comp hgc.continuousOn fun X hX => hX).inv)
  have hU'o : IsOpen (g ⁻¹' B₁ ∩ T ⁻¹' U) := hTc.isOpen_inter_preimage (hB₁.preimage hgc) hU
  have hnull : ∀ S' : HermR R σ n, m S' (g ⁻¹' B₁ ∩ T ⁻¹' U) = 0 := by
    intro S'
    by_cases hS' : S' ∈ B₁
    · have e := hκ (gs S') S S' (hgsS S' hS')
      have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
        (hr.comp (Continuous.prodMk continuous_id continuous_const)).measurable
      rw [e, Measure.smul_apply, Measure.map_apply hmeas hU'o.measurableSet]
      have hsub : (fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹'
            (g ⁻¹' B₁ ∩ T ⁻¹' U) ⊆
          U ∪ (gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det})ᶜ := by
        intro X hX
        by_cases hXf : X ∈ gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det}
        · left
          have hXS : gramR R σ J X = S := hXf.1
          have hgr : g (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) :
              Matrix (Fin n) (Fin n) (R ⊗[F] E))) = S' := by
            apply Subtype.ext
            rw [← hg, a1, hXS, ← hgsS S' hS']
          have hT : T (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) :
              Matrix (Fin n) (Fin n) (R ⊗[F] E))) = X := by
            simp only [T]
            rw [hgr, a2, Units.mul_inv, a3]
          have := hX.2
          simp only [Set.mem_preimage] at this
          rwa [hT] at this
        · exact Or.inr hXf
      have hz : m S ((fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹'
            (g ⁻¹' B₁ ∩ T ⁻¹' U)) = 0 :=
        measure_mono_null hsub (measure_union_null h0 (hm.1 S))
      rw [hz, smul_zero]
    · refine measure_mono_null ?_ (hm.1 S')
      intro X hX hXf
      have hgX : g X = S' := Subtype.ext ((hg X).symm.trans hXf.1)
      exact hS' (hgX ▸ hX.1)
  have hμ0 := null_of_fibres_null hm hU'o.measurableSet hnull
  have hO : IsOpen ((g ⁻¹' B₁ ∩ T ⁻¹' U) ∩ {X | IsUnit (gramR R σ J X).det}) := by
    rw [hUeq]
    exact hU'o.inter (hBo.preimage hgc)
  refine hO.measure_ne_zero μ ⟨X₀, ⟨?_, ?_⟩, hX₀⟩ hμ0
  · show g X₀ ∈ B₁
    rw [hgX₀]
    exact hSB₁
  · show T X₀ ∈ U
    simp only [T]
    rw [hgX₀, hgs1, inv_one, Units.val_one, a3]
    exact hX₀U

end GlobalTheory.CompanionTheory.SW.LocFin
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.adelic_level_lattice_compact_open : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ), 0 < N → IsCompact (latN F ι N : Set (ι → A F)) ∧ IsOpen (latN F ι N : Set (ι → A F)) ∧ ∀ a : ι → F, SB (indC N a) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.Lco.main | exact GlobalTheory.CompanionTheory.SW.ThW.Lco.main | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.Lco.main <;> assumption)
end
