module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle419
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle421
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle420
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Bundle001
public import GroundTheory.AutomorphicForms.Bundle001
public import GroundTheory.AutomorphicForms.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle387
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle428
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

@[expose] public section

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.degree_bounded_of_basis : WedgeF → WedgeI → MulF → MulI → SzFin → FinSupp → LogAbsBasic → DegBasisG → DegBdd := by
  first | exact @GlobalTheory.CompanionTheory.DegBound.degBdd_of | exact GlobalTheory.CompanionTheory.DegBound.degBdd_of | (intros; apply GlobalTheory.CompanionTheory.DegBound.degBdd_of <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.degree_pairing_identity : WedgeF → WedgeI → MulF → MulI → PairF → PairI → SzFin → FinSupp → LogAbsBasic → ConjPlaces → DegBasisG → Radical → DegPairing := by
  first | exact @GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of | exact GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of | (intros; apply GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.size_basic_of_conj_places : SzFin → ConjPlaces → SizeBasic := by
  first | exact @GlobalTheory.CompanionTheory.Size.sizeBasic | exact GlobalTheory.CompanionTheory.Size.sizeBasic | (intros; apply GlobalTheory.CompanionTheory.Size.sizeBasic <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GlobalTheory.CompanionTheory.Size

namespace GlobalTheory.CompanionTheory.SizeCont

theorem continuous_iSup_fin {X ι : Type} [TopologicalSpace X] [Fintype ι] (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) : Continuous fun x => ⨆ i, f i x := by
  rcases isEmpty_or_nonempty ι with h | h
  · simpa [Real.iSup_of_isEmpty] using continuous_const
  · have : (fun x => ⨆ i, f i x) = fun x => Finset.univ.sup' Finset.univ_nonempty fun i => f i x := by
      funext x
      rw [Finset.sup'_univ_eq_ciSup]
    rw [this]
    exact Continuous.finset_sup'_apply _ fun i _ => hf i

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem continuous_cW (w : HeightOneSpectrum (𝓞 E)) : Continuous (cW w : Ad E → w.adicCompletion E) :=
  (RestrictedProduct.continuous_eval w).comp continuous_snd

theorem continuous_elem (p : Fin n × Fin n) :
    Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => A p.1 p.2 :=
  continuous_id.matrix_elem p.1 p.2

theorem continuous_inf (v : InfinitePlace E) : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
    Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) :=
  Real.continuous_posLog.comp (continuous_iSup_fin _ fun p =>
    (((continuous_cV v).comp (continuous_elem p)).norm).pow 2)

theorem continuous_fin (w : HeightOneSpectrum (𝓞 E)) : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
    Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) :=
  Real.continuous_posLog.comp (continuous_iSup_fin _ fun p =>
    ((continuous_cW w).comp (continuous_elem p)).norm)

theorem eventually_finsum (hS : SzFin) (A₀ : Matrix (Fin n) (Fin n) (Ad E)) :
    ∀ᶠ A in 𝓝 A₀, ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) =
      ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset,
        Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) := by
  have hev : ∀ p : Fin n × Fin n, ∀ᶠ A : Matrix (Fin n) (Fin n) (Ad E) in 𝓝 A₀,
      ∀ w, ‖cW w (A p.1 p.2)‖ ≤ max ‖cW w (A₀ p.1 p.2)‖ 1 := fun p =>
    (continuous_elem p).continuousAt.eventually (eventually_fin (A₀ p.1 p.2))
  filter_upwards [Filter.eventually_all.2 hev] with A hA
  refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  by_contra hn
  have h0 : sz (A₀.map (cW w)) ≤ 1 := not_lt.1 hn
  refine hw ((Real.posLog_eq_zero_iff _).2 ?_)
  have h1 : 0 ≤ ⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  rw [abs_of_nonneg h1]
  refine Real.iSup_le (fun p => (hA p w).trans (max_le ?_ le_rfl)) zero_le_one
  exact (le_sup (fun q : Fin n × Fin n => ‖cW w (A₀ q.1 q.2)‖) p).trans h0

theorem continuous_logSizeM (hS : SzFin) :
    Continuous (logSizeM : Matrix (Fin n) (Fin n) (Ad E) → ℝ) := by
  refine continuous_iff_continuousAt.2 fun A₀ => ?_
  have hc : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
      ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) +
        ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset,
          Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) :=
    (continuous_finsetSum _ fun v _ => continuous_inf v).add
      (continuous_finsetSum _ fun w _ => continuous_fin w)
  refine hc.continuousAt.congr ?_
  filter_upwards [eventually_finsum hS A₀] with A hA
  rw [logSizeM, hA]

theorem sizeCont : SzFin → SizeCont := by
  intro hS E _ _ _ n
  have h := continuous_logSizeM (E := E) (n := n) hS
  exact (h.comp Units.continuous_val).add (h.comp Units.continuous_coe_inv)

end GlobalTheory.CompanionTheory.SizeCont

end
end

section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TMapPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem isU_inner (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (ρ g).toLinearMap (hU.norm g)).inner_map_map x y

theorem isU_apply_inv (hU : IsU ρ) (g : Γ) (x : A) : ρ g (ρ g⁻¹ x) = x := by
  have h := hU.mul g g⁻¹
  rw [mul_inv_cancel, hU.one] at h
  have h2 := congrArg (fun T : A →L[ℂ] A => T x) h
  simpa using h2.symm

theorem isU_inner_left (hU : IsU ρ) (k : Γ) (x y : A) : ⟪ρ k x, y⟫_ℂ = ⟪x, ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← isU_apply_inv hU k y]
  exact isU_inner hU k x _

end Unitary

theorem norm_integral_mul_sq_le {Γ : Type} [MeasurableSpace Γ] (ν : Measure Γ) (f g : Γ → ℂ) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) : ‖∫ x, f x * g x ∂ν‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂ν) * ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have h0 : ‖∫ x, f x * g x ∂ν‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂ν := by
    simpa using norm_integral_le_integral_norm (μ := ν) (fun x => f x * g x)
  simp only [Real.rpow_two] at h1
  have hP : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  have hQ : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  calc ‖∫ x, f x * g x ∂ν‖ ^ 2
      ≤ ((∫ x, ‖f x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ)) * (∫ x, ‖g x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h0.trans h1) 2
    _ = _ := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hP, Real.sq_sqrt hQ]

section Main

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
  [InnerProductSpace ℂ B] [CompleteSpace B] {σ : Γ → (A →L[ℂ] A)} {ρ : Γ → (B →L[ℂ] B)} {d : ℝ}


omit [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompleteSpace A] in
theorem coeff_sq (hσ : IsU σ) (hF : IsFd ν σ d) (w a : A) :
    MemLp (fun g => ⟪σ g w, a⟫_ℂ) 2 ν ∧ ∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν = ‖a‖ ^ 2 * ‖w‖ ^ 2 / d := by
  have key : ∀ g, ⟪a, σ g w⟫_ℂ * star ⟪a, σ g w⟫_ℂ = ((‖⟪σ g w, a⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inner_symm]
  obtain ⟨h1, h2⟩ := hF.2 w a w a
  simp only [key] at h1 h2
  have h3 : Integrable (fun g => ‖⟪σ g w, a⟫_ℂ‖ ^ 2) ν := by
    exact h1.re.congr (ae_of_all _ fun g => Complex.ofReal_re _)
  have hc : Continuous fun g => ⟪σ g w, a⟫_ℂ := (hσ.cont w).inner continuous_const
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 h3, ?_⟩
  have e : ∀ x : A, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [integral_complex_ofReal, e, e] at h2
  have h4 : ((∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖w‖ ^ 2 / d : ℝ) : ℂ) := by
    rw [h2]; push_cast; ring
  exact_mod_cast h4

omit [CompleteSpace A] in
theorem form_facts (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) (b : B) (a : A) :
    Integrable (fun g => ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) ν ∧
      ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ^ 2 ≤
        ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) * (‖a‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.matrix_coefficient_integrable_square ν ρ hρ v hv b
  have hc : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hφ : MemLp (fun g => ⟪b, ρ g v⟫_ℂ) 2 ν := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hb1
  obtain ⟨hψ, hψ2⟩ := coeff_sq ν hσ hF w a
  refine ⟨hφ.integrable_mul hψ, ?_⟩
  refine (norm_integral_mul_sq_le ν _ _ hφ hψ).trans ?_
  rw [hψ2]
  exact mul_le_mul_of_nonneg_right hb2 (div_nonneg (by positivity) hF.1.le)

theorem exists_matrix_coefficient_intertwiner (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) :
    ∃ T : B →L[ℂ] A, ∀ b a, ⟪T b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := by
  have hint := fun b a => (form_facts ν hρ hσ hF hv w b a).1
  have hM : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨K, hK0, hbd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ b a, ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ≤ K * ‖b‖ * ‖a‖ := by
    refine ⟨Real.sqrt ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d), Real.sqrt_nonneg _, fun b a => ?_⟩
    have hq : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d := div_nonneg (by positivity) hF.1.le
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine (form_facts ν hρ hσ hF hv w b a).2.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hq]
    ring
  let L : B → (A →L[ℂ] ℂ) := fun b => LinearMap.mkContinuous
    { toFun := fun a => ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν
      map_add' := fun a a' => by
        rw [← integral_add (hint b a) (hint b a')]
        congr 1; ext g; rw [inner_add_right, mul_add]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; ext g; rw [inner_smul_right]; ring } (K * ‖b‖) (fun a => hbd b a)
  let Tf : B → A := fun b => (InnerProductSpace.toDual ℂ A).symm (L b)
  have hT : ∀ b a, ⟪Tf b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := fun b a => by
    simp only [Tf, InnerProductSpace.toDual_symm_apply]
    rfl
  have hTb : ∀ b, ‖Tf b‖ ≤ K * ‖b‖ := fun b => by
    have h1 := hbd b (Tf b)
    rw [← hT, inner_self_eq_norm_sq_to_K] at h1
    by_cases h0 : ‖Tf b‖ = 0
    · rw [h0]; positivity
    · have h2 : 0 < ‖Tf b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h3 : ‖Tf b‖ * ‖Tf b‖ ≤ (K * ‖b‖) * ‖Tf b‖ := by
        simpa [sq] using h1
      exact le_of_mul_le_mul_right h3 h2
  refine ⟨LinearMap.mkContinuous
    { toFun := Tf
      map_add' := fun b b' => ext_inner_right ℂ fun a => by
        rw [inner_add_left, hT, hT, hT, ← integral_add (hint b a) (hint b' a)]
        congr 1; ext g; rw [inner_add_left, add_mul]
      map_smul' := fun t b => ext_inner_right ℂ fun a => by
        simp only [RingHom.id_apply]
        rw [inner_smul_left, hT, hT, ← integral_const_mul]
        congr 1; ext g; rw [inner_smul_left]; ring } K hTb, fun b a => ?_⟩
  exact hT b a

end Main

theorem tMap : TMap := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hF v hv w c hc h
  obtain ⟨T, hT⟩ := exists_matrix_coefficient_intertwiner ν hρ hσ hF hv w
  have hk : ∀ k b, T (ρ k b) = σ k (T b) := fun k b => ext_inner_right ℂ fun a => by
    rw [hT, isU_inner_left hσ k, hT]
    refine (integral_mul_left_eq_self (μ := ν) (fun g => ⟪ρ k b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) k).symm.trans
      (integral_congr_ae (ae_of_all _ fun g => ?_))
    simp only [hρ.mul, hσ.mul, ContinuousLinearMap.mul_apply]
    rw [isU_inner hρ, isU_inner_left hσ]
  have hv' : T v = (c : ℂ) • w := ext_inner_right ℂ fun a => by
    rw [hT, inner_smul_left, Complex.conj_ofReal]
    have h1 := congrArg (starRingEnd ℂ) (h a)
    rw [← integral_conj] at h1
    simp only [map_mul, inner_conj_symm, Complex.conj_ofReal, Complex.star_def] at h1
    exact h1
  refine ⟨(c : ℂ)⁻¹ • T, fun g x => ?_, ?_⟩
  · simp [hk]
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [ContinuousLinearMap.smul_apply, hv', smul_smul, inv_mul_cancel₀ hc', one_smul]

end GlobalTheory.CompanionTheory.RgHeA.TMapPf
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

theorem integrable_star' {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} {f : Γ → ℂ} (h : Integrable f ν) :
    Integrable (fun g => star (f g)) ν :=
  h.norm.mono' (continuous_star.comp_aestronglyMeasurable h.1) (.of_forall fun g => by simp)

theorem exists_eig_of_low {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    (T : A →L[ℂ] A) (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) (w₀ : A) (hw₀ : w₀ ≠ 0) (p : A) (d : ℝ) (hd : 0 < d)
    (h : ∀ a, ‖⟪p, a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re) :
    ∃ (w : A) (c : ℝ), w ≠ 0 ∧ ‖p‖ ^ 2 / (2 * d) ≤ c ∧ T w = (c : ℂ) • w := by
  obtain ⟨s, b, l, -, hTb0, hsum0, -⟩ := GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hT hT'
  have hTb : ∀ i, T (b i) = ((l i : ℝ) : ℂ) • b i := hTb0
  have hsum : ∀ x, HasSum (fun i => (((l i : ℝ) : ℂ) * ⟪b i, x⟫_ℂ) • b i) (T x) := hsum0
  have hone : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
  have hli : ∀ i, 0 ≤ l i := fun i => by
    have h1 := h (b i)
    rw [hTb, inner_smul_right, hone, mul_one, Complex.ofReal_re] at h1
    exact le_trans (by positivity) h1
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i, l i < ‖p‖ ^ 2 / (2 * d) := fun i => by
    by_contra hh
    push_neg at hh
    exact hcon _ _ (b.orthonormal.ne_zero i) hh (hTb i)
  obtain ⟨i0⟩ : Nonempty s := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    exact hw₀ (inner_self_eq_zero.1 ((b.hasSum_inner_mul_inner w₀ w₀).unique hasSum_empty))
  have hC : 0 < ‖p‖ ^ 2 / (2 * d) := (hli i0).trans_lt (hlt i0)
  have key : ∀ i, ⟪p, b i⟫_ℂ * ⟪b i, p⟫_ℂ = ((‖⟪p, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm (b i) p, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key2 : ∀ i, ((l i : ℝ) : ℂ) * ⟪b i, p⟫_ℂ * ⟪p, b i⟫_ℂ = ((l i * ‖⟪p, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [mul_assoc, mul_comm ⟪b i, p⟫_ℂ, key]; push_cast; ring
  have e : (⟪p, p⟫_ℂ).re = ‖p‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) p
  have h1 : HasSum (fun i => ‖⟪p, b i⟫_ℂ‖ ^ 2) (‖p‖ ^ 2) := by
    have h0 := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner p p)
    simp only [Complex.reCLM_apply, key, Complex.ofReal_re, e] at h0
    exact h0
  have h2 : HasSum (fun i => l i * ‖⟪p, b i⟫_ℂ‖ ^ 2) (⟪p, T p⟫_ℂ).re := by
    have h0 := Complex.reCLM.hasSum ((innerSL ℂ p).hasSum (hsum p))
    simp only [innerSL_apply_apply, inner_smul_right, Complex.reCLM_apply, key2, Complex.ofReal_re] at h0
    exact h0
  have h3 : (⟪p, T p⟫_ℂ).re ≤ ‖p‖ ^ 2 / (2 * d) * ‖p‖ ^ 2 :=
    hasSum_le (fun i => mul_le_mul_of_nonneg_right (hlt i).le (by positivity)) h2 (h1.mul_left (‖p‖ ^ 2 / (2 * d)))
  have h5 := h p
  have e2 : ‖⟪p, p⟫_ℂ‖ = ‖p‖ ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e2] at h5
  have hP : 0 < ‖p‖ ^ 2 := by
    by_contra hh
    have : ‖p‖ ^ 2 = 0 := le_antisymm (not_lt.1 hh) (by positivity)
    rw [this] at hC
    simp at hC
  have e3 : ‖p‖ ^ 2 / (2 * d) * ‖p‖ ^ 2 = (‖p‖ ^ 2) ^ 2 / d / 2 := by field_simp
  have h6 : 0 < (‖p‖ ^ 2) ^ 2 / d := by positivity
  linarith

theorem eigA : EigA := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hd w₀ hw₀ hc0 i hi v hm0
  have hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν := integrable_star' hm0
  have hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν := integrable_star' hc0
  have hne : w₀ ≠ 0 := fun h => by simp [h] at hw₀
  have hdense : (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
    intro u hu
    refine PositivityTheory.UnitaryDecomposition.X4.eq_zero_of_orth hd hne fun g => ?_
    have hg : σ g w₀ ∈ Submodule.span ℂ (Set.range fun x => σ x w₀) := Submodule.subset_span ⟨g, rfl⟩
    exact Submodule.inner_left_of_mem_orthogonal hg hu
  have hlow := GlobalTheory.T.cyclic_vector_intertwiner_determined σ ρ d hd.1 hσ hρ w₀ v i hi.1 hdense
    (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) (coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc)
    (GlobalTheory.T.matrix_coefficient_intertwiner_adjoint ν σ ρ hσ hρ w₀ v hc hm) (GlobalTheory.T.formal_degree_schur_lower_bound ν σ ρ d hσ hρ hd w₀ hw₀ hc i hi)
  have hlow' : ∀ a, ‖⟪ContinuousLinearMap.adjoint i v, a⟫_ℂ‖ ^ 2 / d ≤
      (⟪a, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm a⟫_ℂ).re := fun a => by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hlow a
  obtain ⟨w, c, hw, hcb, hTw⟩ := exists_eig_of_low _ (GroundTheory.Automorphic.IsHilbertSchmidt.isCompactOperator
    (GlobalTheory.T.formal_degree_matrix_coefficient_norm ν σ ρ d hσ hρ hd v hm)) (GlobalTheory.T.matrix_coefficient_orthogonality_relation ν σ ρ hσ hρ v hm) w₀ hne _ d hd.1 hlow'
  refine ⟨w, c, hw, hcb, fun b => ⟨integrable_mul_inner hσ hm b w, ?_⟩⟩
  rw [← inner_coefOp ν σ hσ _ hm, hTw, inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem hecke_dominant_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hIw hpos V _ _ π hπ t t' ht ht' T T' hT hT' v l hl
  obtain ⟨r, hr, x, hxN, hx⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hIw hpos t' ht'
  have hxJ : ∀ i, x i ∈ J := fun i => (hxN i).1
  have hform := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ _ T' hT' r x hr hxJ hx v
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set g := leviEmb k (stdBlocks d hd) t with hg
  set g' := leviEmb k (stdBlocks d hd) t' with hg'
  have hmul : leviEmb k (stdBlocks d hd) (t * t') = g * g' := map_mul _ _ _
  have hterm : ∀ i, l (π g (π (x i * g') (v : V))) = l (π (g * g') (v : V)) := by
    intro i
    have hc : g * x i * g⁻¹ ∈ J := (ht.1 _ (hxN i)).1
    have hfac : g * (x i * g') = (g * x i * g⁻¹) * (g * g') := by group
    have h1 : l (π (g * x i * g⁻¹) (π (g * g') (v : V))) = l (π (g * g') (v : V)) :=
      LinearMap.congr_fun (hl _ hc) _
    rw [← Module.End.mul_apply, ← map_mul, hfac, map_mul, Module.End.mul_apply, h1]
  have hTT : l (((T * T') v : fixed π J) : V) = l (π g ((T' v : fixed π J) : V)) :=
    (hT (T' v) l hl).symm

  rw [hTT, hform, hmul, map_smul, map_sum, map_smul, map_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [smul_eq_mul]
  field_simp

end GlobalTheory.CompanionTheory.Lbc
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem jacquet_hecke_operator_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ t ht T hT v
  obtain ⟨r, hr, x, hx, hu⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hI hpos t ht
  have key := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ (leviEmb k (stdBlocks d hd) t) T hT r x hr
    (fun i => (hx i).1) hu v
  have hmk : ∀ i, (Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    intro i
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨x i, (hx i).2⟩, π (leviEmb k (stdBlocks d hd) t) (v : V), ?_⟩
    simp [map_mul]
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have hsum : (Submodule.Quotient.mk ((T v : fixed π J) : V) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    rw [key, Submodule.Quotient.mk_smul]
    have h2 : (Submodule.Quotient.mk (∑ i, π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
        ∑ i : Fin r, Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :=
      map_sum (Submodule.mkQ _) _ _
    rw [h2, Finset.sum_congr rfl fun i _ => hmk i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [hsum, jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Lbc
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.flat_section_growth_bound : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsCompact (K : Set (G2 σ Y)) → IsHgt K a → (∀ x, 0 < a x) → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | exact GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | (intros; apply GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow <;> assumption)
end
