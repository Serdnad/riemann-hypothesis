module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle045
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.GaussJetBounds.Bundle003
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle079
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Padics.ProperSpace
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryPrecedes

theorem not_precedes_of_unitary : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := by
  intro E Ω _ _ _ _ _ A w h rc hrc Δ Δ' hΔ hΔ' hP
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  obtain ⟨hL, j, hj, hfirst⟩ := hP
  have hy' : rc Δ'.first = (rc Δ.first).lpTw (j : ℝ) := by
    rw [hfirst, ← H.nu_eq]
    norm_cast
  have hdeg : deg (frob h) = 1 := deg_frob
  have hcard : Multiset.card ((rc Δ.first).eig (frob h)) = Δ.d := by
    rw [WD.card_eig, H.dim]
    rfl
  obtain ⟨β, hβ⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ Δ.d_pos)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  set q : ℝ := ((normV w : ℕ) : ℝ) with hqdef
  have hn : ∀ s : ℝ, ‖((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)‖ = q ^ s := by
    intro s
    rw [← coe_qPow, norm_qPow]
  have h1 := hΔ (frob h) hdeg (β * ((normV w : ℕ) : ℂ) ^ (((((Δ.len : ℝ) - 1) / 2 : ℝ)) : ℂ))
    (by rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg]; exact Multiset.mem_map_of_mem _ hβ)
  have h2 := hΔ' (frob h) hdeg (β * ((normV w : ℕ) : ℂ) ^ (((j : ℕ) : ℝ) : ℂ) *
      ((normV w : ℕ) : ℂ) ^ (((((Δ'.len : ℝ) - 1) / 2 : ℝ)) : ℂ))
    (by
      rw [hy', GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg, GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg]
      exact Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ hβ))
  rw [norm_mul, hn] at h1
  rw [norm_mul, norm_mul, hn, hn] at h2
  have hb : ‖β‖ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have heq : q ^ (((Δ.len : ℝ) - 1) / 2) = q ^ (((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2)) := by
    rw [Real.rpow_add (by linarith)]
    apply mul_left_cancel₀ hb
    rw [h1, ← mul_assoc, h2]
  have hexp : ((Δ.len : ℝ) - 1) / 2 = ((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2) := by
    rcases lt_trichotomy (((Δ.len : ℝ) - 1) / 2) (((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2)) with hlt | heq' | hgt
    · exact absurd heq (Real.rpow_lt_rpow_of_exponent_lt hq hlt).ne
    · exact heq'
    · exact absurd heq (Real.rpow_lt_rpow_of_exponent_lt hq hgt).ne'
  have hlen : Δ.len = Δ'.len + 2 * j := by
    have : (Δ.len : ℝ) = Δ'.len + 2 * j := by linarith
    exact_mod_cast this
  apply hL.2.2
  intro x hx
  rw [Segment.mem_carrier] at hx ⊢
  obtain ⟨b, hb', rfl⟩ := hx
  refine ⟨j + b, by omega, ?_⟩
  rw [hfirst, IrrGL.nu_nu]
  push_cast
  rfl

end GlobalTheory.UnitaryPrecedes
end

section

noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.LvT.KerLat

theorem rowGen_diag_monomial_one (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (d : Fin r × Fin n →₀ ℕ) :
    rowGen R a a (monomial d 1) =
      (1 + Polynomial.X) ^ (Finsupp.weight (rowW r n) d a) * Polynomial.C (monomial d 1) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have e : (monomial (f + g) (1 : R) : MvPolynomial (Fin r × Fin n) R) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, hf, hg, map_add (f := _), Pi.add_apply, pow_add, map_mul]
    ring
  | single v c =>
    obtain ⟨b, s⟩ := v
    rw [← X_pow_eq_monomial, map_pow, map_pow]
    unfold rowGen
    rw [aeval_X]
    by_cases h : b = a
    · subst h
      have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) b = c := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index]
      rw [e, ← mul_pow]
      simp only [if_true]
      congr 1
      ring
    · have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) a = 0 := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index, Ne.symm h]
      rw [e]
      simp [h]

theorem rowGen_diag_homog (R : Type) [CommRing R] {r n : ℕ} (μ : Fin r → ℕ) (a : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    rowGen R a a f = (1 + Polynomial.X) ^ (μ a) * Polynomial.C f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : (monomial d (AddMonoidAlgebra.coeff f d) : MvPolynomial (Fin r × Fin n) R) = AddMonoidAlgebra.coeff f d • monomial d 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, rowGen_diag_monomial_one, hf (mem_support_iff.mp hd), ← mul_smul_comm,
    Polynomial.smul_C]

theorem rowDiv_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ →
    (∀ (a b : Fin r) (k : ℕ), ∃ μ' : Fin r → ℕ, IsWeightedHomogeneous (rowW r n) (rowDiv R a b k f) μ') ∧
      ∀ (a : Fin r) (k : ℕ), rowDiv R a a k f = ((μ a).choose k) • f := by
  intro R _ r n μ f hf
  refine ⟨fun a b k => ?_, fun a k => ?_⟩
  · have hZ : IsWeightedHomogeneous (rowZ r n) f (fun i => (μ i : ℤ)) := by
      intro d hd
      funext i
      rw [weight_rowZ, hf hd]
    have h := rowDiv_shift R _ a b k f hZ
    refine ⟨fun i => ((((fun i => (μ i : ℤ)) + k • (Pi.single a 1 - Pi.single b 1) : Fin r → ℤ)) i).toNat,
      fun d hd => ?_⟩
    funext i
    rw [← h hd, weight_rowZ, Int.toNat_natCast]
  · unfold rowDiv
    rw [rowGen_diag_homog R μ a f hf, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow, nsmul_eq_mul]

end GlobalTheory.ValCmp
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

section Pure

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K]

def IsInt (x : K) : Prop := ∃ o : O, algebraMap O K o = x

def IntM {m n : ℕ} (x : Matrix (Fin m) (Fin n) K) : Prop := ∀ i j, IsInt O (x i j)

def GInt {n : ℕ} (x : GL (Fin n) K) : Prop := IntM O x.1 ∧ IntM O (x⁻¹).1

def Hk (p : O) (j : ℕ) {n : ℕ} (x : GL (Fin n) K) : Prop :=
  IntM O x.1 ∧ IntM O (algebraMap O K p • (x⁻¹).1) ∧ ∃ u : Oˣ, x.1.det = algebraMap O K (p ^ j * u)

def Reps {n : ℕ} {ι : Type} (x : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) : Prop :=
  (∀ γ ∈ R, ∃ k₁ k₂, GInt O k₁ ∧ GInt O k₂ ∧ ρ γ = k₁ * x * k₂) ∧
    ∀ k₁ k₂, GInt O k₁ → GInt O k₂ → ∃! γ, γ ∈ R ∧ GInt O ((ρ γ)⁻¹ * (k₁ * x * k₂))

variable {O}

theorem isInt_iff {x : K} : IsInt O x ↔ x ∈ (algebraMap O K).range := Iff.rfl

theorem intM_iff {m n : ℕ} {x : Matrix (Fin m) (Fin n) K} :
    IntM O x ↔ ∃ A : Matrix (Fin m) (Fin n) O, A.map (algebraMap O K) = x := by
  constructor
  · intro h
    choose A hA using h
    exact ⟨Matrix.of A, by ext i j; simp [hA]⟩
  · rintro ⟨A, rfl⟩ i j
    exact ⟨A i j, rfl⟩

theorem IntM.mul {l m n : ℕ} {x : Matrix (Fin l) (Fin m) K} {y : Matrix (Fin m) (Fin n) K} (hx : IntM O x)
    (hy : IntM O y) : IntM O (x * y) := by
  rw [intM_iff] at hx hy ⊢
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  exact ⟨A * B, Matrix.map_mul⟩

theorem IntM.add {m n : ℕ} {x y : Matrix (Fin m) (Fin n) K} (hx : IntM O x) (hy : IntM O y) : IntM O (x + y) := fun i j => by
  obtain ⟨a, ha⟩ := hx i j
  obtain ⟨b, hb⟩ := hy i j
  exact ⟨a + b, by simp [ha, hb]⟩

theorem IntM.sub {m n : ℕ} {x y : Matrix (Fin m) (Fin n) K} (hx : IntM O x) (hy : IntM O y) : IntM O (x - y) := fun i j => by
  obtain ⟨a, ha⟩ := hx i j
  obtain ⟨b, hb⟩ := hy i j
  exact ⟨a - b, by simp [ha, hb]⟩

theorem IntM.transpose {m n : ℕ} {x : Matrix (Fin m) (Fin n) K} (hx : IntM O x) : IntM O xᵀ := fun i j => hx j i

theorem intM_one {n : ℕ} : IntM O (1 : Matrix (Fin n) (Fin n) K) := fun i j => by
  by_cases h : i = j
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Matrix.one_apply_ne h]⟩

theorem gInt_one {n : ℕ} : GInt O (1 : GL (Fin n) K) := ⟨intM_one, by rw [inv_one]; exact intM_one⟩

theorem GInt.mul {n : ℕ} {x y : GL (Fin n) K} (hx : GInt O x) (hy : GInt O y) : GInt O (x * y) := ⟨IntM.mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact IntM.mul hy.2 hx.2⟩

theorem GInt.inv {n : ℕ} {x : GL (Fin n) K} (hx : GInt O x) : GInt O x⁻¹ := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

end Pure

variable {D : D7}

abbrev Ov (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := v.adicCompletionIntegers D.host.F

theorem isInt_Ov {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Fv D.host.F v} :
    IsInt (Ov D v) x ↔ x ∈ v.adicCompletionIntegers D.host.F := ⟨fun ⟨o, h⟩ => h ▸ o.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

def Chart (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v) : Prop :=
  Function.Surjective π ∧ (∀ a, π a = 0 ↔ e * a = 0) ∧
    (∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y)) ∧
    ∀ a, finPart D (e * a) ∈ intAE D ↔ IsInt (Ov D v) (π a)

def Frame (V : HSp D) (e : AE D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) : Prop :=
  ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ LamHat V ↔
    ∀ i, IsInt (Ov D v) (((β⁻¹).1 *ᵥ fun k => π (y k)) i)

def rho (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) : GA D V →* GL (Fin V.rank) (Fv D.host.F v) :=
  (MulAut.conj β⁻¹).toMonoidHom.comp ((Matrix.GeneralLinearGroup.map π).comp (matHom V))

theorem rho_val (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (rho V π β g).1 = (β⁻¹).1 * (mt V g).map π * β.1 := by
  simp only [rho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
  rfl

end GlobalTheory.SplitHecke

end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.integral_jets_realPlace_local_bases : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  first | exact @GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | exact GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | (intros; apply GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR <;> assumption)
end

section



noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.CompletedBasis

section General

variable {l : ℕ} [Fact l.Prime]

theorem isCompact_closure_range {A V : Type} [AddCommGroup A] [Module.Finite ℤ A] [NormedAddCommGroup V]
    [NormedSpace ℚ_[l] V] (f : A →+ V) : IsCompact (closure (Set.range f)) := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := A)
  let g : (Fin n → ℤ_[l]) → V := fun c => ∑ i, ((c i : ℤ_[l]) : ℚ_[l]) • f (b i)
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_subtype_val.comp (continuous_apply i)).smul continuous_const
  have hc : IsCompact (Set.range g) := isCompact_range hg
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Submodule.span ℤ (Set.range b) := hb ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ha
  refine ⟨fun i => (c i : ℤ_[l]), ?_⟩

  simp only [g, map_sum, map_zsmul, PadicInt.coe_intCast, Int.cast_smul_eq_zsmul]

variable {K : Type} [Field K] [NumberField K] (ρ : K →+* ℂ_[l])

def intClosure : Subring ℂ_[l] := (ρ.comp (algebraMap (𝓞 K) K)).range.topologicalClosure

theorem coe_intClosure : (intClosure ρ : Set ℂ_[l]) = closure (Set.range fun a : 𝓞 K => ρ (a : K)) := rfl

theorem isCompact_intClosure : IsCompact (intClosure ρ : Set ℂ_[l]) :=
  isCompact_closure_range (l := l) (ρ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom

theorem mem_intClosure (a : 𝓞 K) : ρ (a : K) ∈ intClosure ρ := subset_closure ⟨a, rfl⟩

theorem norm_le_one_of_mem {x : ℂ_[l]} (hx : x ∈ intClosure ρ) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨C, hC⟩ := (isCompact_intClosure ρ).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have := hC _ ((intClosure ρ).pow_mem hx n)
  rw [norm_pow] at this
  exact absurd hn (not_lt.2 this)

variable {E : Type} [Field E] [NumberField E] [Algebra K E] {ι : Type} [Fintype ι] (σ : ι → E →+* ℂ_[l])

end General

section Host

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def rhoBase : D.host.E →+* ℂ_[l] :=
  lam.comp (D.host.φ₀.codRestrict Qbar fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom)

theorem rhoBase_apply (x : D.host.E) : rhoBase D lam x = lamC lam (D.host.φ₀ x) := by
  unfold lamC
  rw [dite_eq_left]
  rfl

def rhoK : D.host.K →+* ℂ_[l] := (rhoBase D lam).comp (algebraMap D.host.K D.host.E)

theorem fst_image_OKp : Prod.fst '' GL3Theta.OKp D lam = (intClosure (rhoK D lam) : Set ℂ_[l]) := by
  let f : 𝓞 D.host.K →+ ℂ_[l] × ℂ_[l] :=
    (((rhoK D lam).prod (((rhoBase D lam).comp (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap D.host.K D.host.E))).comp (algebraMap (𝓞 D.host.K) D.host.K)).toAddMonoidHom
  have hf : (fun a : 𝓞 D.host.K => (GL3Theta.tauK D lam (a : D.host.K), GL3Theta.tauKc D lam (a : D.host.K))) = f := by
    funext a
    exact Prod.ext (rhoBase_apply D lam _).symm (rhoBase_apply D lam _).symm
  unfold GL3Theta.OKp
  rw [hf, image_closure_of_isCompact (isCompact_closure_range (l := l) f) continuous_fst.continuousOn,
    ← Set.range_comp, coe_intClosure]
  rfl

end Host

end GlobalTheory.CompletedBasis
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Pass

theorem ambient_h1f_of_local_finiteness : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (i : D.nd.Loc)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i),
    Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) →
    EmbeddingTypes.H1fFiniteRankTorsion (D := D) i ρ π dc := by
  intro hLF D i ρ π dc hc _ w hw _ C L2 _ n
  obtain ⟨⟨_, hdvr, hfr⟩, -⟩ := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  haveI := hdvr
  haveI := hfr
  have hcont := GlobalTheory.T.twistedDual_continuous_integral_over_enlarged_coeff D i w hw C.LL C.le ρ π hc
  have hfin := GlobalTheory.T.local_h1f_finite_dimensional hLF (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL D.R.r
    (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) hcont.1 hcont.2
  exact GlobalTheory.T.period_data_crystalline_admissible (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) L2 hfin n

end GlobalTheory.Pass
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem _root_.GlobalTheory.T.numberField_completion_ringEquiv_of_dense_unramified : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (hc : IsAdicComplete (Ideal.span {(p : W)}) W) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)), ∃ φ : P.adicCompletion E ≃+* Qq, (∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) ∧ (∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) ∧ ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U := by
  first | exact @GlobalTheory.DenseCompl.completion_ringEquiv_of_dense | exact GlobalTheory.DenseCompl.completion_ringEquiv_of_dense | (intros; apply GlobalTheory.DenseCompl.completion_ringEquiv_of_dense <;> assumption)
end
