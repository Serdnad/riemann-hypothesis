module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle394
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle408
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle135
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaFixedSH

theorem vs_inv_mem_of_not_mem_nonunits {F : Type} [Field F] (A : ValuationSubring F) {x : F} (hx : x ∈ A)
    (hn : x ∉ A.nonunits) : x ≠ 0 ∧ x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt] at hn
  have h1 : A.valuation x = 1 := le_antisymm ((A.valuation_le_one_iff x).2 hx) hn
  refine ⟨fun h => by simp [h] at h1, ?_⟩
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem inertiaFixed_strictlyHenselian : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → GlobalTheory.SS.SH (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ∧ ∃ f : R →+* V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω), (∀ r : R, ((f r : IntermediateField.fixedField (inertia K V)) : Ω) = algebraMap K Ω (algebraMap R K r)) ∧ ∀ π : R, Irreducible π → Irreducible (f π) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  have hc : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := hV ▸ ⟨r, rfl⟩
    exact this
  have hinv : ∀ π : R, Irreducible π → (algebraMap K Ω (algebraMap R K π))⁻¹ ∉ V := by
    intro π hπ h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω _ ∈ V
      rwa [map_inv₀]
    rw [hV] at h'
    obtain ⟨s, hs⟩ := h'
    have hπ0 : algebraMap R K π ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨s, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hs, map_one, mul_inv_cancel₀ hπ0]
  have hc0 : ∀ π : R, Irreducible π → algebraMap K Ω (algebraMap R K π) ≠ 0 := by
    intro π hπ h
    apply hinv π hπ
    rw [h, inv_zero]; exact V.zero_mem
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set V' := V.comap (algebraMap K' Ω) with hV'
  have memV' : ∀ y : K', y ∈ V' ↔ (y : Ω) ∈ V := fun y => ValuationSubring.mem_comap
  let f : R →+* V' := ((algebraMap K K').comp (algebraMap R K)).codRestrict V' (fun r => by
      rw [memV']; simpa using hc r)
  have hf : ∀ r : R, ((f r : K') : Ω) = algebraMap K Ω (algebraMap R K r) := fun r => by simp [f]
  have unitV' : ∀ a : V', ((a : K') : Ω) ∉ V.nonunits → IsUnit a := by
    intro a ha
    obtain ⟨h0, hi⟩ := vs_inv_mem_of_not_mem_nonunits V ((memV' a).1 a.2) ha
    have hmem : (a : K')⁻¹ ∈ V' := by rw [memV']; simpa using hi
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv, OneMemClass.coe_one,
      IntermediateField.coe_one]
    exact mul_inv_cancel₀ h0
  have hfπ : ∀ π : R, Irreducible π → Irreducible (f π) := by
    intro π hπ
    refine irreducible_iff.2 ⟨fun hu => hinv π hπ ?_, fun a b hab => ?_⟩
    · obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hb' : ((f π : K') : Ω) * ((b : K') : Ω) = 1 := by
        have := congrArg (fun z : V' => ((z : K') : Ω)) hb
        simpa using this
      rw [hf] at hb'
      rw [inv_eq_of_mul_eq_one_right hb']
      exact (memV' b).1 b.2
    · by_contra hne
      push_neg at hne
      have ha : ((a : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.1 (unitV' a h)
      have hb : ((b : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.2 (unitV' b h)
      have h1 := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ (a : K').2 ha
      have h2 := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ (b : K').2 hb
      have hab' : algebraMap K Ω (algebraMap R K π) = ((a : K') : Ω) * ((b : K') : Ω) := by
        rw [← hf, hab]; simp
      apply hinv π hπ
      have h0 := hc0 π hπ
      convert mul_mem h1 h2 using 1
      rw [div_mul_div_comm, ← hab']
      field_simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hdvr : IsDiscreteValuationRing V' := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨f π, hfπ π hπ, fun {x} hx => ?_⟩
    have hx0 : ((x : K') : Ω) ≠ 0 := by
      intro h; apply hx; apply Subtype.ext; apply Subtype.ext; simpa using h
    classical
    have hex := GlobalTheory.T.not_mem_div_uniformizer_pow_alt R K Ω V hV π hπ _ hx0
    have hn := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by
      intro h; rw [h] at hn; apply hn; simpa using (memV' x).1 x.2
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hmin : ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m ∈ V := by
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      simpa using this
    set y : K' := (x : K') / (algebraMap K K' (algebraMap R K π)) ^ m with hy
    have hyΩ : (y : Ω) = ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m := by simp [y]
    have hyV' : y ∈ V' := by rw [memV', hyΩ]; exact hmin
    have hyU : (y : Ω) ∉ V.nonunits := by
      intro hyn
      have := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ y.2 hyn
      apply hn
      rw [hm, hyΩ] at *
      convert this using 1
      rw [pow_succ, div_div]
    refine ⟨m, (unitV' ⟨y, hyV'⟩ hyU).unit, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    simp only [IsUnit.unit_spec, MulMemClass.coe_mul, IntermediateField.coe_mul, SubmonoidClass.coe_pow,
      IntermediateField.coe_pow]
    rw [hf, hyΩ]
    field_simp [pow_ne_zero m (hc0 π hπ)]
  exact ⟨⟨hdvr, GlobalTheory.T.henselianLocalRing_fixedField_inertia_alt R K Ω V hV, GlobalTheory.T.residueField_inertiaFixed_isAlgClosed_alt R K Ω V hV, inferInstance⟩, f, hf, hfπ⟩

end GlobalTheory.InertiaFixedSH
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ γ ∈ SURat σ J, ∀ x : HA (AF F) σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j) → x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  first | exact @GlobalTheory.SUAssemble.assemble | exact GlobalTheory.SUAssemble.assemble | (intros; apply GlobalTheory.SUAssemble.assemble <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.ArchGrid

theorem level_pos {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) : 0 < Q := by
  rcases Nat.eq_zero_or_pos Q with rfl | h
  · have h1 := P.idx_le
    rw [zero_pow (by positivity)] at h1
    exact absurd (Nat.le_zero.1 h1) P.idx_ne
  · exact h

theorem arch_grid : GlobalTheory.SqTop.GBig fun {D} _ _ {sc} G μ₀ C _ b => ∀ (zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL), (∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl), IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧ D.what₂.embLL (zA' ij) = (P'.norm : ℂ)) → ArchimedeanHeightBound zA zA' (C * D.R.f * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ) * (Real.log b + Real.log ((maxWt D sc.cGap : ℝ) * (2 * (bigN D : ℝ)))) + C * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ))) + C * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl)) := by
  obtain ⟨C0, -, hA⟩ := GlobalTheory.ArchFree.st.archSt
  refine ⟨0, fun ε CF _ => ⟨C0, 0, fun C hC D large₂ _ _ hR T Lc μ₀ hμ G => ?_⟩⟩
  rintro zA zA' ⟨δ, t0, h⟩
  choose P P' hB hz hz' using h
  haveI := D.tcLL
  obtain ⟨-, -, hf4, hm44, -, -, -, -, -, hrd1, hrd2, -⟩ := hR.size
  have hLpos : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hL1 : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hlb : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  have hB1 : (1 : ℝ) ≤ (maxWt D 1 : ℝ) := by exact_mod_cast le_max_left _ _
  have hrd : Real.log D.host.rdE ≤ Real.log large₂.sc.b := by rw [hlb]; linarith
  have hdl : |TaylorLogMetric.logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
    rw [hlb]
    have e : TaylorLogMetric.logDerivativeAtOne D = large₂.logDerivativeAtOne := by rw [large₂.logDerivative_at_one_eq]; rfl
    rw [e]; exact hR.dlog
  intro ij
  have hQ : 0 < levQ G.pl := level_pos (P ij)
  have key := hA D ⊤ δ t0 (levQ G.pl) (P ij).crv (P ij).pt0 hQ D.what₂.LL D.what₂.embLL (Fin D.R.m × Fin D.R.m) (bigN D)
    (maxWt D 1 : ℝ) (Real.log large₂.sc.b) P P' zA zA' hN hB1 (by rw [hlb]; exact hL1) hrd hdl
    (fun k => GlobalTheory.T.squareBottomPairs_small_reference_tuple hμ G δ t0 _ (P k) (P' k) k.1 k.2 _ (hB k)) (fun k => ⟨hz k, hz' k⟩) ij
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hf4
    exact_mod_cast this
  have hN' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN
  have hX : 0 ≤ (D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ) := by
    have h1 : 0 ≤ Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ))) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ)) := by
      apply Real.log_nonneg
      have : 1 ≤ (D.R.f : ℝ) * (2 * (bigN D : ℝ)) := by nlinarith
      nlinarith
    have h3 : 0 ≤ Real.log (levQ G.pl : ℝ) := Real.log_natCast_nonneg _
    have hl : 0 ≤ Real.log large₂.sc.b := by rw [hlb]; linarith
    positivity
  have hle : ∀ c : ℝ, c * (D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      c * (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      c * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ) = c * ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ)) := fun c => by ring
  have hmono := mul_le_mul_of_nonneg_right hC hX
  show _ ∧ _
  constructor
  · refine le_trans key.1 (le_of_eq_of_le ?_ (le_of_le_of_eq hmono ?_))
    · exact (hle C0).symm ▸ rfl
    · exact (hle C).symm
  · refine le_trans key.2 (le_of_eq_of_le ?_ (le_of_le_of_eq hmono ?_))
    · exact (hle C0).symm ▸ rfl
    · exact (hle C).symm

end GlobalTheory.ArchGrid
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct


theorem _root_.GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
  first | exact @GlobalTheory.SquareInfGap.square_infExp_gap | exact GlobalTheory.SquareInfGap.square_infExp_gap | (intros; apply GlobalTheory.SquareInfGap.square_infExp_gap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_bottomInfinityExponents_gap_largeGrids : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ) := by
  first | exact @GlobalTheory.BotDict.bottom_infExp_gap | exact GlobalTheory.BotDict.bottom_infExp_gap | (intros; apply GlobalTheory.BotDict.bottom_infExp_gap <;> assumption)
end

section

open NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.weightZero_const_frameValue_mem_coeff_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ f ∈ sec Xo c 0 0, ∀ a : ℂ, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = a) → a ∈ σ.range := by
  first | exact @GlobalTheory.FlatLine.const_value_mem_range | exact GlobalTheory.FlatLine.const_value_mem_range | (intros; apply GlobalTheory.FlatLine.const_value_mem_range <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C, (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) → (minpoly F c).natDegree = n := by
  first | (exact @GlobalTheory.RegDeg.natDegree_minpoly_eq) | (exact GlobalTheory.RegDeg.natDegree_minpoly_eq) | (intros; apply GlobalTheory.RegDeg.natDegree_minpoly_eq  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  first | exact @GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem | exact GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem | (intros; apply GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv


open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach in
theorem GlobalTheory.PureMatch.pure_match : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P),
    ∀ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v), ∀ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
    ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
    ∀ s : GL (Fin (spV G i j).rank) (Fv D.host.F v) → GL (Fin (spV₁ G i j).rank) (Fv D.host.F v) → ℂ, (∀ K₁ K₂, s K₁ K₂ ≠ 0) →
    ∃ n Φ K₁ K₂, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      bigP (haarVol (KO _ (Fin (spW G i j).rank))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β (Bs.τ ⟨v, hP⟩))
          (fun Z => s K₁ K₂ * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ
            (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1))) =
        smallP (haarVol (KO _ (Fin (spW₁ G i j).rank))) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α (Bs.τ ⟨v, hP⟩)) Ψ := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h R Rf hM hT w hw v hv hP g₀ c₀ Ψ hΨ s hs
  have hτ : splitPrime (Bs.τ ⟨v, hP⟩) = w := hT.2.2.2 ⟨v, hP⟩ w hw hv
  have hb : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro hmem
    apply hst.2 w hw
    have hd : GlobalTheory.HalfCompare.badInt D ∣ D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK :=
      ⟨D.host.d, by unfold GlobalTheory.HalfCompare.badInt; ring⟩
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hψ := Good.hasConductor_psiAt W hb
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  obtain ⟨hν, hα⟩ := GlobalTheory.T.thetaTripleSquare_splitPlace_character_eq_localGrid hL W M t i j e Bs Γ X h w v hv (Bs.τ ⟨v, hP⟩) hτ
  obtain ⟨m, hm⟩ := @GlobalTheory.T.exists_depth_splitThetaBig_eq_small_blockTranslate
    (Fv D.host.F v) _ _ _ _ _ _ (spW G i j).rank (Fin (spW₁ G i j).rank)
    (Fin ((spW G i j).rank + (spW₁ G i j).rank)) _ _ _ _
    (haarVol (KO _ (Fin (spW₁ G i j).rank)))
    (by exact GlobalTheory.SplitFlip.isHaarMeasure_haarVol_KO) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β (Bs.τ ⟨v, hP⟩)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (blockV e) g₀ c₀ Ψ hΨ hϖv
  obtain ⟨μ, hμ, σ', hphi, hdep⟩ := GlobalTheory.T.datumPhiA_splitPlace_transport_eq hL t i j e w hw v hv (Bs.τ ⟨v, hP⟩) hτ (max (2 * m) (depthAt G w))
  let K₁ : GL (Fin (spV G i j).rank) (Fv D.host.F v) := diagGL fun _ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m
  let K₂ : GL (Fin (spV₁ G i j).rank) (Fv D.host.F v) := diagGL fun _ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m)⁻¹
  obtain ⟨Ξ, hΞ, heq⟩ := @hm _ (le_max_left _ _) μ (by exact hμ) σ' (s K₁ K₂) (hs K₁ K₂)
  obtain ⟨Ξ', hΞ', hΞΞ'⟩ := hdep Ξ hΞ
  refine ⟨max (2 * m) (depthAt G w), invFourierSum (psiAt W w) (unifAt w) (max (2 * m) (depthAt G w))
    (Assignment.one.block _ _) Ξ', K₁, K₂, le_max_right _ _,
    FourierDepth.isNatDatum_invFourierSum (isUnif_unifAt w) hψ _ _ hΞ', ?_⟩
  have hsq : ∀ Z, sqCore W t i j w (max (2 * m) (depthAt G w)) (invFourierSum (psiAt W w) (unifAt w)
      (max (2 * m) (depthAt G w)) (Assignment.one.block _ _) Ξ') (trA t hv e Z) =
      phiA μ σ' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (max (2 * m) (depthAt G w))
        (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (max (2 * m) (depthAt G w)) (blockV e)) Ξ Z := by
    intro Z
    unfold sqCore
    rw [GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum _ _ _ _ _ _ _ (isUnif_unifAt w) hψ _ hΞ', hphi, hν]
    congr 1
    exact funext hΞΞ'
  have hblk : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 = (diagGL (fun col => if col ∈ blockV e then GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m
      else (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m)⁻¹)).val := by
    ext a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rcases a with a | a <;> rcases b with b | b <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, K₁, K₂, diagGL_val, blockV, diagonal_apply]
  rw [hα, ← heq]
  congr 1
  funext Z
  rw [Matrix.mul_assoc _ c₀.1, hblk, ← Units.val_mul, hsq]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.birigidified_bundle_kernel_killed_of_complex_points : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) → x ^ n = 1) → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ n = 1 := by
  first | exact @GlobalTheory.BiKill.kernel_pow_eq_one | exact GlobalTheory.BiKill.kernel_pow_eq_one | (intros; apply GlobalTheory.BiKill.kernel_pow_eq_one <;> assumption)
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem prime_generically_regular_quotient :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)]
      (B : Type) [CommRing B] [Algebra Λ B] [Algebra.FiniteType Λ B] (p : Ideal B) [p.IsPrime],
      (∀ a : Λ, algebraMap Λ B a ∈ p → a = 0) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q →
        g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q))) := by
  intro Λ _ _ _ _ B _ _ _ p _ hp
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType Λ B)
  set Q : Ideal (MvPolynomial (Fin n) Λ) := p.comap φ with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0 := by
    intro a ha
    apply hp a
    have : φ (MvPolynomial.C a) ∈ p := ha
    rwa [MvPolynomial.algHom_C] at this
  obtain ⟨h, f, s, g₀, hg₀, hfQ, hgQ, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (Fin n) Q hQ
  set δ := (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det with hδ
  refine ⟨φ (g₀ * δ), ?_, ?_⟩
  · intro hmem
    have : g₀ * δ ∈ Q := hmem
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h1 | h1
    · exact hg₀ h1
    · exact hdet h1
  · intro q _ hpq hgq
    set N : Ideal (MvPolynomial (Fin n) Λ) := q.comap φ with hN
    haveI : N.IsPrime := Ideal.comap_isPrime _ _
    have hQN : Q ≤ N := Ideal.comap_mono hpq
    have hgN : g₀ * δ ∉ N := hgq
    have hg₀N : g₀ ∉ N := fun h1 => hgN (N.mul_mem_right _ h1)
    have hδN : δ ∉ N := fun h1 => hgN (N.mul_mem_left _ h1)
    let D : Fin h → Derivation ℤ (MvPolynomial (Fin n) Λ) (MvPolynomial (Fin n) Λ) :=
      fun i => (MvPolynomial.pderiv (s i)).restrictScalars ℤ
    have hdetD : (Matrix.of fun i j => D i (f j)).det ∉ N := by
      simpa [D] using hδN
    have hreg := GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit (MvPolynomial (Fin n) Λ) h f D N (fun j => hQN (hfQ j)) hdetD
    have heq : (Ideal.span (Set.range f)).map
          (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) =
        Q.map (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) := by
      apply le_antisymm
      · apply Ideal.map_mono
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        exact hfQ j
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        have hu : IsUnit (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N) g₀) :=
          IsLocalization.map_units (Localization.AtPrime N) (⟨g₀, hg₀N⟩ : N.primeCompl)
        rw [← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul]
        exact Ideal.mem_map_of_mem _ (hgQ x hx)
    rw [heq] at hreg
    obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv (MvPolynomial (Fin n) Λ) B
      φ.toRingHom hφ p q
    haveI : IsRegularLocalRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        (p.comap φ.toRingHom).map (algebraMap _ (Localization.AtPrime (q.comap φ.toRingHom)))) := hreg
    exact IsRegularLocalRing.of_ringEquiv e

end GlobalTheory
end
