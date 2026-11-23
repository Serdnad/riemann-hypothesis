module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle237
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle005
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.Bundle001
public import Formalism.LocalRingCardinality.Bundle008
public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.ExistsPowOrbRep
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle008
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle004
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.tracePowerProductRealSpan_mul_mem : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ) (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trSpan_mul | exact GlobalTheory.GoodMetric.ChernSpan.trSpan_mul | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trSpan_mul <;> assumption)
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_exteriorSquare : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | exact GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_wedge2 <;> assumption)
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.tensor σ).lie A = kron (ρ.lie A) 1 + kron 1 (σ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_tensor | exact GlobalTheory.GoodMetric.PolyRep.lie_tensor | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_tensor <;> assumption)
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.two_mul_trace_exteriorSquareDerivation_pow : ∀ {R : Type} [CommRing R] {M : ℕ} (L : Matrix (Fin M) (Fin M) R) (i : ℕ), 2 * ((wedge2Lie L) ^ i).trace = ((kron L 1 + kron 1 L) ^ i).trace - 2 ^ i * (L ^ i).trace := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow | exact GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow | (intros; apply GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow <;> assumption)
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.coeff_charpolyRev_mem_tracePowerProductRealSpan : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι) (k : ℕ), (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan | exact GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan | (intros; apply GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan <;> assumption)
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspBoundSiegel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem posIdele_mul (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) :
    posIdele (K := E) (ρ * σ) (mul_pos hρ hσ) = posIdele ρ hρ * posIdele σ hσ := by
  unfold posIdele
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← map_mul]
  congr 1
  exact Subtype.ext (mul_pow ρ σ _)

theorem posIdele_exp (u : ℝ) :
    posIdele (K := E) (Real.exp u) (Real.exp_pos u) = infId E (expU fun _ : InfinitePlace E => (u : ℂ)) := by
  refine Units.ext (ad_ext ?_ ?_)
  · have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    change _ = pInf E (1 - sInf E 1 + sInf E _)
    simp only [map_add (f := _), map_sub, map_one, h, sub_self, zero_add]
    funext w
    have hc := IsTotallyComplex.isComplex w
    have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hc
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _
    rw [← coe_infiniteProj, infiniteProj_posIdele]
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (posRealElem w _) = _
    unfold posRealElem
    rw [dite_eq_right hw, RingEquiv.apply_symm_apply]
    simp [InfinitePlace.mult, hw, Real.sqrt_sq (Real.exp_pos u).le, expU, Complex.ofReal_exp]
  · change ((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E) - 0 + 0
    rw [sub_zero, add_zero]
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem posIdele_congr {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    posIdele (K := E) x hx = posIdele y hy := by subst h; rfl

theorem diagUnits_posIdele (a : ℕ) {x : ℝ} (hx : 0 < x) :
    diagUnits a (fun _ : Fin a => posIdele (K := E) x hx) = splitCentre E a (Real.log x) := by
  rw [splitCentre_eq_scalar, ← posIdele_exp, posIdele_congr hx (Real.exp_pos _) (Real.exp_log hx).symm]
  refine Units.ext ?_
  rw [coe_diagUnits]
  rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_posIdele_pos :
    Continuous fun r : {r : ℝ // 0 < r} => (posIdele (K := E) r.1 r.2 : IdeleGroup E) := by
  unfold posIdele
  exact continuous_finsetProd _ fun w _ => (continuous_moduleSection w).comp
    (Continuous.subtype_mk ((continuous_subtype_val).pow _) _)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem ideleModule_det_diagUnits_posIdele (a : ℕ) {x : ℝ} (hx : 0 < x) :
    (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
      (diagUnits a (fun _ : Fin a => posIdele (K := E) x hx))) : ℝ) = x ^ (a * Module.finrank ℚ E) := by
  have hdet : Matrix.GeneralLinearGroup.det (diagUnits a (fun _ : Fin a => posIdele (K := E) x hx)) =
      posIdele x hx ^ a := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
  rw [hdet, map_pow, Positive.val_pow, ideleModule_posIdele, ← pow_mul, mul_comm]

theorem cuspFormsBounded_of_rapidDecay (h : GlobalTheory.Published.CuspRapidDecaySiegelGL) : GlobalTheory.Published.CuspFormsBoundedGL := by
  intro E _ _ _ a φ hφ hA
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨‖φ.1 1‖, fun g => ?_⟩
    have : g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  set d : ℕ := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have had : a * d ≠ 0 := (Nat.mul_pos ha hd0).ne'
  set m : AdelicGLn.AdelicGL E a → ℝ :=
    fun b => (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) with hm
  have hmpos : ∀ b, 0 < m b := fun b => (IdeleGroup.ideleModule E _).2
  set s : AdelicGLn.AdelicGL E a → ℝ := fun b => m b ^ (((a * d : ℕ) : ℝ)⁻¹) with hs
  have hspos : ∀ b, 0 < s b := fun b => Real.rpow_pos_of_pos (hmpos b) _
  have hspow : ∀ b, s b ^ (a * d) = m b := fun b => Real.rpow_inv_natCast_pow (hmpos b).le had
  set f : AdelicGLn.AdelicGL E a → AdelicGLn.AdelicGL E a :=
    fun b => b * (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))⁻¹ with hf
  have hmc : Continuous m :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  have hsc : Continuous fun b => (⟨s b, hspos b⟩ : {r : ℝ // 0 < r}) :=
    Continuous.subtype_mk (hmc.rpow_const fun b => Or.inl (hmpos b).ne') _
  have hfc : Continuous f := continuous_id.mul ((continuous_diagUnits a).comp
    (continuous_pi fun _ => continuous_posIdele_pos.comp hsc)).inv
  have hω'c : IsCompact (f '' ω) := hω.image hfc
  have hω'B : f '' ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (hωB hb) (inv_mem (diagUnits_mem_adelicBorel a _))
  have hω'1 : ∀ b ∈ f '' ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1 := by
    rintro _ ⟨b, -, rfl⟩
    have e : IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
        (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))) =
        IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) :=
      Subtype.ext (by rw [ideleModule_det_diagUnits_posIdele, hspow])
    simp only [hf, map_mul, map_inv, e, mul_inv_cancel]
    rfl
  obtain ⟨C, hC⟩ := h E a φ hφ (f '' ω) hω'c hω'B hω'1 t ht 0
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩ := hsieg g
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  set ρ := (∏ i, r i) ^ ((a : ℝ)⁻¹) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hprod _
  have hρa : ρ ^ a = ∏ i, r i := Real.rpow_inv_natCast_pow hprod.le ha.ne'
  set r' : Fin a → ℝ := fun i => r i / ρ with hr'
  have hr'pos : ∀ i, 0 < r' i := fun i => div_pos (hr i) hρpos
  have hD : diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) =
      diagUnits a (fun _ : Fin a => posIdele (K := E) ρ hρpos) *
        diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) := by
    rw [← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, ← posIdele_mul]
    exact posIdele_congr _ _ (by simp only [hr']; field_simp)
  set D' := diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) with hD'
  have key : ratGL E a γ * g = splitCentre E a (Real.log (s b) + Real.log ρ) * (f b * D' * k) := by
    change AdelicGLn.diagonal E a γ * g = _
    rw [e, hD, diagUnits_posIdele a hρpos, splitCentre_add]
    simp only [hf, diagUnits_posIdele a (hspos b)]
    symm
    calc splitCentre E a (Real.log (s b)) * splitCentre E a (Real.log ρ) *
          (b * (splitCentre E a (Real.log (s b)))⁻¹ * D' * k)
        = splitCentre E a (Real.log (s b)) * (splitCentre E a (Real.log ρ) *
            (b * (splitCentre E a (Real.log (s b)))⁻¹)) * D' * k := by group
      _ = splitCentre E a (Real.log (s b)) * ((b * (splitCentre E a (Real.log (s b)))⁻¹) *
            splitCentre E a (Real.log ρ)) * D' * k := by rw [splitCentre_comm (Real.log ρ)]
      _ = (splitCentre E a (Real.log (s b)) * b) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by group
      _ = (b * splitCentre E a (Real.log (s b))) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by rw [splitCentre_comm (Real.log (s b)) b]
      _ = b * (splitCentre E a (Real.log ρ) * D') * k := by group
  calc ‖φ.1 g‖ = ‖φ.1 (ratGL E a γ * g)‖ := by rw [hφ.1.left]
    _ = ‖φ.1 (f b * D' * k)‖ := by rw [key, hA]
    _ ≤ C * ∏ i, r' i ^ (0 : Fin a → ℝ) i := hC (f b) ⟨b, hb, rfl⟩ r' hr'pos (fun i j hij => by
          simp only [hr']
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right (hrat i j hij) hρpos.le) (by
          simp only [hr']
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa,
            div_self hprod.ne']) k hk
    _ = C := by simp

end GlobalTheory.CuspBoundSiegel

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ArInt

theorem isometric_comb_unit_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L : HermLB p) (m : ℕ), (ArInt.comb (fun _ : Unit => L) (fun _ => (m : ℤ))).Isometric (L.pow m) := by
  intro k _ X _ p L m
  rw [← HermLB.icls_eq_iff, icls_comb, HermLB.icls_pow]
  simp

end GlobalTheory.ArInt
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.DefiniteMeasure

open Formalism.IndefR.Lev GlobalTheory.Mem.VolExists

theorem exists_probHaar (P Q : ℕ) (h : P = 0 ∨ Q = 0) : ∃ ν : Measure (UpqT P Q), ν.IsHaarMeasure ∧
    ∀ m : Measure (UpqT P Q), (m.IsHaarMeasure ∧ IsProbabilityMeasure m) ↔ m = ν := by
  haveI : CompactSpace (UpqT P Q) := by
    rcases h with rfl | rfl
    exacts [(GlobalTheory.compactSpace_UpqT_definite Q).2, (GlobalTheory.compactSpace_UpqT_definite P).1]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  let ν : Measure (UpqT P Q) := Measure.haarMeasure ⊤
  haveI hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure ⊤
  haveI hp : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
  refine ⟨ν, hν, fun m => ⟨fun ⟨h1, h2⟩ => ?_, fun e => e ▸ ⟨hν, hp⟩⟩⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure m ν

end GlobalTheory.Mem.DefiniteMeasure
end

section

noncomputable section

namespace GlobalTheory.Mem.AwayChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
open scoped TensorProduct

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adelic_ext {n : ℕ} (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (H : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g = bc (prV (E := E) v) h) : g = h := by
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub]
  have h1 := congrArg Units.val (H w)
  rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV] at h1
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply] at this
  rw [this, sub_self]

theorem exists_trivial_on {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ s, bc (prV (E := E) v) k = 1) ∧
      ∀ v ∉ s, bc (prV (E := E) v) k = bc (prV (E := E) v) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨g, hg, by simp, fun _ _ => rfl⟩
  | insert v s hv ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    have hne : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 k) = bc (prV (E := E) w) k := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      rfl
    refine ⟨Formalism.UG.P.afsplitU v 1 k, Formalism.UG.P.afsplitU_mem v σ J 1 k (one_mem _) hk, fun w hw => ?_, fun w hw => ?_⟩
    · by_cases h : w = v
      · subst h; exact Formalism.UG.P.afsplit_right1 w 1 k
      · rw [hne w h]; exact h1 w ((Finset.mem_insert.1 hw).resolve_left h)
    · rw [Finset.mem_insert, not_or] at hw
      rw [hne w hw.1]; exact h2 w hw.2

theorem finite_over (p : ℕ) (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem exists_away_mem (S : StepLevel F E σ J T f bad) (p : ℕ) (hp : p ≠ 0)
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hw : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) g ∈ S.Uloc w) :
    ∃ κ : S.U, (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) g := by
  obtain ⟨k, hk, h1, h2⟩ := exists_trivial_on σ J (finite_over (F := F) p hp).toFinset g hg
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h1 h2
  refine ⟨⟨k, (S.U_eq k).2 ⟨hk, fun v => ?_⟩⟩, h1, h2⟩
  by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [h1 v hv]; exact one_mem _
  · rw [h2 v hv]; exact hw v hv

theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A ℂ) (x : A) : IsIntegral ℤ (ψ x) := by
  have h : ψ x ^ Nat.card A = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact IsIntegral.of_pow Nat.card_pos (by rw [h]; exact isIntegral_one)

theorem chi_isIntegral {gp : Fin 2 → ℕ} {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t skip fc : ℕ} {zl : Bool}
    (X : GLev S G a t 0 skip fc zl) (κ : S.U) : IsIntegral ℤ ((S.chi κ : ℂˣ) : ℂ) := by
  rw [X.chi_eq κ]
  refine IsIntegral.prod _ fun i _ => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun h => ?_
  haveI : Finite (kv F v) := Formalism.UG.P.glint_finite_residueField v
  unfold lamJ
  rw [Finset.range_zero, Finset.prod_empty, mul_one, ← AddChar.map_neg_eq_inv]
  exact addChar_isIntegral _ _

end Adelic

theorem exists_inv_char {U LL O Kf : Type} [Group U] [Field LL] [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (χ : U →* ℂˣ) (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ c : U →* Oˣ, ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ algebraMap O Kf ((c κ : Oˣ) : O) * e r = 1 := by
  choose r hr o ho using h
  have r1 : r 1 = 1 := embLL.injective (by rw [hr]; simp)
  have rm : ∀ a b, r (a * b) = r a * r b := fun a b => embLL.injective (by rw [map_mul, hr, hr, hr]; simp)
  let o' : U →* O :=
    { toFun := o
      map_one' := hinj (by rw [ho, r1, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, ho, ho, ho, rm, map_mul]) }
  refine ⟨o'.toHomUnits⁻¹, fun κ => ⟨r κ, hr κ, ?_⟩⟩
  rw [← ho κ, ← map_mul]
  have : o κ = ((o'.toHomUnits κ : Oˣ) : O) := rfl
  rw [this, MonoidHom.inv_apply, Units.inv_mul, map_one]

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem exists_psiTied {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E sp.cm.sig J T f bad) (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (hp : p ≠ 0) (hk : R.k = n)
    (hJ : ∀ x y, J x y = sp.gram0 (Fin.cast hk.symm x) (Fin.cast hk.symm y))
    (hU : ∀ v, S.Uloc v = (L.Uloc v).map (reGL hk _).toMonoidHom)
    {LL O Kf : Type} [Field LL] [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ, PsiTied S L p hk embLL e ψ := by
  obtain ⟨c, hc⟩ := exists_inv_char hinj S.chi embLL e h
  have hex : ∀ a : Formalism.L2.Herm.awayFrom₂ L p, ∃ κ : S.U,
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) (reGL hk _ a.1) := by
    intro a
    obtain ⟨h2, h3⟩ := (mem_awayP_iff L p a.1).1 a.2
    refine exists_away_mem S p hp _ (reGL_mem_UPts hk sp.cm.sig sp.gram0 J hJ _ _ h2) fun w hw => ?_
    rw [bc_reGL, hU w]
    exact Subgroup.mem_map.2 ⟨_, h3 w hw, rfl⟩
  choose κ h1 h2 using hex
  have huniq : ∀ (a : Formalism.L2.Herm.awayFrom₂ L p) (k : S.U),
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k.1 = 1) →
      (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) k.1 = bc (prV (E := E) w) (reGL hk _ a.1)) → κ a = k := by
    intro a k k1 k2
    refine Subtype.ext (adelic_ext _ _ fun v => ?_)
    by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
    · rw [h1 a v hv, k1 v hv]
    · rw [h2 a v hv, k2 v hv]
  let K : Formalism.L2.Herm.awayFrom₂ L p →* S.U := MonoidHom.mk' κ fun a b => by
    refine huniq _ _ (fun v hv => ?_) (fun v hv => ?_)
    · rw [Subgroup.coe_mul, map_mul, h1 a v hv, h1 b v hv, mul_one]
    · rw [Subgroup.coe_mul, map_mul, h2 a v hv, h2 b v hv, Subgroup.coe_mul, map_mul, map_mul]
  refine ⟨c.comp K, fun a k k1 k2 => ?_⟩
  obtain rfl := huniq a k k1 k2
  exact hc (κ a)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar



theorem exists_psi : ∀ (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u), (∀ u, Joint0 L0 u (T u)) → (∀ u, LevelZeroCharacterRational T u) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →*
        (ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))ˣ,
      PsiTied (LL := D.what₂.LL) (O := ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))
        (Kf := KfRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ((T u).cls0).lev (L0 u)
        (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ψ := by
  intro D L0 T hJ hψ u w _
  refine exists_psiTied ((T u).cls0).lev (L0 u) _ (D.what₂.places.resChar_prime w).ne_zero (rank_eq_first_level D.R) (Formalism.L2.G.Cmp.gramN_zero D)
    (hJ u).Uloc_eq Subtype.val_injective _ _ fun κ => ?_
  obtain ⟨r, hr⟩ := chiRatAll_rec T u (hψ u) κ
  refine ⟨r, hr, (embRec_int D w _ r).1 ((val_nonneg_iff D w r).2 ?_)⟩
  have h1 : IsIntegral ℤ (D.what₂.embLL r) := hr ▸ chi_isIntegral ((T u).glev0) κ
  have h2 : IsIntegral ℤ r := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 h1
  exact (D.plEq w).valuation_le_one (K := D.what₂.LL) (⟨r, h2⟩ : 𝓞 D.what₂.LL)

end GlobalTheory.Mem.AwayChar
end
end
