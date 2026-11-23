module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle007
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphIso
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import GroundTheory.AutomorphicForms.Bundle011
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle002
public import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section Ops

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma one_ok : (0 : H →L[ℂ] H) ≤ 1 ∧ ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
  ⟨by simpa using star_mul_self_nonneg (1 : H →L[ℂ] H), ContinuousLinearMap.norm_id_le⟩

private lemma mul_ok {S T : H →L[ℂ] H} (hS : 0 ≤ S ∧ ‖S‖ ≤ 1) (hT : 0 ≤ T ∧ ‖T‖ ≤ 1)
    (h : Commute S T) : 0 ≤ S * T ∧ ‖S * T‖ ≤ 1 :=
  ⟨h.mul_nonneg hS.1 hT.1, (norm_mul_le S T).trans (mul_le_one₀ hS.2 (norm_nonneg _) hT.2)⟩

private lemma prod_ok (L : List (H →L[ℂ] H)) (h : ∀ T ∈ L, 0 ≤ T ∧ ‖T‖ ≤ 1) (hc : L.Pairwise Commute) :
    0 ≤ L.prod ∧ ‖L.prod‖ ≤ 1 := by
  induction L with
  | nil => simpa using one_ok (H := H)
  | cons T L ih =>
    rw [List.prod_cons]
    rw [List.pairwise_cons] at hc
    exact mul_ok (h T (by simp)) (ih (fun S hS => h S (by simp [hS])) hc.2)
      (Commute.list_prod_right _ _ hc.1)

private lemma pow_ok {T : H →L[ℂ] H} (h : 0 ≤ T ∧ ‖T‖ ≤ 1) (k : ℕ) : 0 ≤ T ^ k ∧ ‖T ^ k‖ ≤ 1 := by
  induction k with
  | zero => simpa using one_ok (H := H)
  | succ k ih => rw [pow_succ]; exact mul_ok ih h ((Commute.refl T).pow_left k)

end Ops

private lemma smooth_pow {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] {n : ℕ}
    (ν : Measure (archGroup F n)) [ν.IsHaarMeasure] (a : TI F n) (h1 : SmoothT a) (h2 : LeftFin a) (k : ℕ) :
    ∃ c : TI F n, (∀ g, c g = cvPow ν (a : archGroup F n → ℂ) k g) ∧ SmoothT c ∧ LeftFin c := by
  induction k with
  | zero => exact ⟨a, fun _ => rfl, h1, h2⟩
  | succ k ih =>
    obtain ⟨c, hc, -, -⟩ := ih
    have hb := UpperTheory.ConvolutionTheory.L1.cvBasic (archGroup F n) ν a c c a.continuous a.hasCompactSupport c.continuous
      c.hasCompactSupport c.continuous c.hasCompactSupport
    let γ : TI F n := ⟨⟨cv ν a c, hb.1⟩, hb.2.1⟩
    have hγ : ∀ g, γ g = cv ν a c g := fun _ => rfl
    have hl := UpperTheory.ConvolutionTheory.L1.lactCv F n ν a c γ h1 hγ
    refine ⟨γ, fun g => ?_, hl.1, hl.2.1 h2⟩
    have : (c : archGroup F n → ℂ) = cvPow ν (a : archGroup F n → ℂ) k := funext hc
    rw [hγ, this]
    rfl

private lemma single_comm {G : Type} [Group G] {k : ℕ} {i j : Fin k} (hij : i ≠ j) (x y : G) :
    (Pi.mulSingle i x : Fin k → G) * Pi.mulSingle j y = Pi.mulSingle j y * Pi.mulSingle i x :=
  by
  have h : Pairwise fun i j : Fin k => ∀ (x : G) (y : G), Commute (Pi.mulSingle i x : Fin k → G) (Pi.mulSingle j y) :=
    Pi.mulSingle_commute (f := fun _ => G)
  exact (h hij x y).eq

private lemma position_comm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {m : ℕ} {D : InfD σ m} {n : ℕ} {s : Fin (m + 1) → archGroup F n →* archGroup E n}
    (hs : IsBlockElement D n s) (hmul : ∀ g h, glueA D n (g * h) = glueA D n g * glueA D n h)
    {i j : Fin (m + 1)} (hij : i ≠ j) (x y : archGroup F n) : s i x * s j y = s j y * s i x := by
  have hcm := single_comm (G := archGroup F n) hij x y
  have h1 : s i x * s j y = glueA D n (Pi.mulSingle i x * Pi.mulSingle j y) := by
    rw [hmul, ← hs i x, ← hs j y]
  have h2 : s j y * s i x = glueA D n (Pi.mulSingle j y * Pi.mulSingle i x) := by
    rw [hmul, ← hs i x, ← hs j y]
  rw [h1, h2, hcm]

private lemma tens_ok {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {m : ℕ} {D : InfD σ m} {n : ℕ} {νE : Measure (archGroup E n)} [νE.IsHaarMeasure]
    {νF : Measure (archGroup F n)} [νF.IsHaarMeasure] {b a c : TI F n} {aE : TI E n}
    (hmeas : νE = Measure.map (glueA D n) (Measure.pi fun _ => νF))
    (hsq : ∀ g, a g = cv νF b (fun x => conj (b x⁻¹)) g) (hc : ∀ g, c g = cvPow νF a m g)
    (hnorm : ∫ g, ‖b g‖ ∂νF ≤ 1) (htens : IsTens D (fun _ => a) aE)
    {s : Fin (m + 1) → archGroup F n →* archGroup E n} (hs : IsBlockElement D n s) (hsc : ∀ i, Continuous (s i))
    (hmul : ∀ g h, glueA D n (g * h) = glueA D n g * glueA D n h)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep (archGroup E n) H) :
    0 ≤ π.integrated νE (UnitaryRep.ccToL1 νE aE) ∧ ‖π.integrated νE (UnitaryRep.ccToL1 νE aE)‖ ≤ 1 := by
  rw [UpperTheory.ConvolutionTheory.L1.tensOp F E σ m D n νE νF hmeas s hsc hs H π (fun _ => a) aE htens]
  refine prod_ok _ ?_ ?_
  · intro T hT
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    have := UpperTheory.ConvolutionTheory.L1.sqOp F n νF b a c m hsq hc hnorm H (π.compHom (s i) (hsc i))
    exact ⟨this.2.1, this.2.2.1⟩
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact (UpperTheory.ConvolutionTheory.Tf.commInt (archGroup E n) (archGroup F n) (archGroup F n) H π (s i) (hsc i)
      (s j) (hsc j) νF νF a a).2 (position_comm hs hmul hij.ne)

private lemma pow_op {F : Type} [Field F] [NumberField F] {n m : ℕ} {νF : Measure (archGroup F n)} [νF.IsHaarMeasure]
    {b a c : TI F n} (hsq : ∀ g, a g = cv νF b (fun x => conj (b x⁻¹)) g) (hc : ∀ g, c g = cvPow νF a m g)
    (hnorm : ∫ g, ‖b g‖ ∂νF ≤ 1) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep (archGroup F n) H) :
    0 ≤ π.integrated νF (UnitaryRep.ccToL1 νF c) ∧ ‖π.integrated νF (UnitaryRep.ccToL1 νF c)‖ ≤ 1 := by
  have := UpperTheory.ConvolutionTheory.L1.sqOp F n νF b a c m hsq hc hnorm H π
  rw [this.2.2.2]
  exact pow_ok ⟨this.2.1, this.2.2.1⟩ _

theorem _root_.UpperTheory.ConvolutionTheory.L1.ampPosition :
    UpperTheory.ConvolutionTheory.L1.AmpSlot := by
  intro F E _ _ _ _ _ _ _ σ m D n νE _ νF _ b a aE aF h
  have hbc : Continuous fun x : archGroup F n => conj (b x⁻¹) :=
    Complex.continuous_conj.comp (b.continuous.comp continuous_inv)
  have hbs : HasCompactSupport fun x : archGroup F n => conj (b x⁻¹) := by
    have h0 : HasCompactSupport fun x : archGroup F n => b x⁻¹ :=
      b.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
    exact h0.comp_left (g := starRingEnd ℂ) (map_zero _)
  let bs : TI F n := ⟨⟨fun x => conj (b x⁻¹), hbc⟩, hbs⟩
  have hsq : ∀ g, a g = cv νF b bs g := fun g => h.sq g
  have hA := UpperTheory.ConvolutionTheory.L1.lactCv F n νF b bs a h.smooth hsq
  have hsa : SmoothT a := hA.1
  have hla : LeftFin a := hA.2.1 h.fin
  have hE := UpperTheory.ConvolutionTheory.L1.tensSmooth F E σ m D n (fun _ => a) aE h.tens
  obtain ⟨c, hc, hcs, hcl⟩ := smooth_pow νF a hsa hla m
  have hcF : c = aF := by
    ext g
    rw [hc, h.pow]
  subst hcF
  obtain ⟨-, -, hmul, -, -, ⟨s, hs, hsc⟩, -, -⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  refine ⟨fun μE _ => ?_, fun μF _ => ?_⟩
  · have hok := tens_ok h.meas h.sq hc h.norm h.tens hs hsc hmul (LL μE)
      ((rightRegularRep (rationalGLOne (K := E) (n := n)) μE).compHom (archP E n) continuous_archP)
    exact ⟨hE.1 fun _ => hsa, hE.2 fun _ => hla, hok.1, hok.2⟩
  · have hok := pow_op h.sq hc h.norm (LL μF)
      ((rightRegularRep (rationalGLOne (K := F) (n := n)) μF).compHom (archP F n) continuous_archP)
    exact ⟨hcs, hcl, hok.1, hok.2⟩

end UpperTheory.ConvolutionTheory.L1
end
end

section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

private theorem haar_uniq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Set G} {m m' : Measure G}
    (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure) (h : m K = 1) (h' : m' K = 1) : m = m' := by
  have e := Measure.isMulLeftInvariant_eq_smul m m'
  have e2 : m K = (Measure.haarScalarFactor m m' • m') K := by rw [← e]
  rw [h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one] at e2
  have e3 : Measure.haarScalarFactor m m' = 1 := by exact_mod_cast e2.symm
  rw [e3, one_smul] at e
  exact e

private theorem gl_sc (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [SecondCountableTopology R] (n : ℕ) : SecondCountableTopology (GL (Fin n) R) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {v : HeightOneSpectrum (𝓞 K)}

private theorem sph_at [ms : MeasurableSpace (GL (Fin n) (v.adicCompletion K))]
    [bs : BorelSpace (GL (Fin n) (v.adicCompletion K))] (m : Measure (GL (Fin n) (v.adicCompletion K)))
    (hm : m.IsHaarMeasure) (h1 : m (GLnLocal.integralGL (v.adicCompletion K) n) = 1)
    {p : MvPolynomial (Fin n) ℂ} {h : GL (Fin n) (v.adicCompletion K) → ℂ} (hs : GM.IsSph v p h) :
    ∃ H : SphericalHecke m (F := v.adicCompletion K) (n := n), (∀ x, (H : HeckeAlgebra m) x = h x) ∧
      satakeTransform m H = polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) := by
  obtain ⟨ms', bs', m', hm', h1', H, hH, S⟩ := hs
  obtain rfl : ms' = ms := bs'.measurable_eq.trans bs.measurable_eq.symm
  haveI := gl_sc (v.adicCompletion K) n
  obtain rfl := haar_uniq hm hm' h1 h1'
  exact ⟨H, hH, S⟩

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.sphLaws :
    UpperTheory.ConvolutionTheory.L1.SphLaws := by
  refine ⟨?_, fun K _ _ n v => ⟨?_, ?_, ?_⟩⟩
  · intro F E _ _ _ _ _ v w hs n p h hsph
    obtain ⟨ms, bs, m, hm, hk, H, hH, S⟩ := hsph
    obtain ⟨⟨e, he⟩, hint, -, -, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
    let c : v.adicCompletion F ≃+* w.1.adicCompletion E :=
      RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩
    have he0 : w.1.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne'
    have hv : ∀ x, c x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F] := fun x => by
      have h1 : ∀ y : w.1.adicCompletion E, y ∈ 𝒪[w.1.adicCompletion E] ↔ Valued.v y ≤ 1 := fun y => by
        have := ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v y 1
        rw [map_one, map_one] at this
        exact (Valuation.mem_integer_iff _ _).trans this
      have h2 : ∀ y : v.adicCompletion F, y ∈ 𝒪[v.adicCompletion F] ↔ Valued.v y ≤ 1 := fun y => by
        have := ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v y 1
        rw [map_one, map_one] at this
        exact (Valuation.mem_integer_iff _ _).trans this
      rw [h1, h2]
      change Valued.v (completionMap v w.1 x) ≤ 1 ↔ _
      rw [valued_completionMap]
      exact pow_le_one_iff_of_nonneg zero_le he0
    have hee : ∀ g, e g = mapIso c n g := fun g => he g
    obtain ⟨ms', bs', m', hm', h1, H', hH', S'⟩ := exists_transport e (fun g => by rw [he]; exact hint g)
      (fun g => by rw [hee]; exact iwasawaExponent_mapIso c hv g) (qF_eq_of_iso c hv) hk H
    exact ⟨ms', bs', m', hm', h1, H', fun x => (hH' x).trans ((hH _).trans (by rw [he])), S'.trans S⟩
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1.continuous, (H : HeckeAlgebra m).mem.2⟩
  · intro p h h' hs hs'
    obtain ⟨ms, bs, m, hm, h1, H, hH, S⟩ := id hs
    obtain ⟨H', hH', S'⟩ := sph_at m hm h1 hs'
    obtain rfl := satakeTransform_injective (S.trans S'.symm)
    exact funext fun x => (hH x).symm.trans (hH' x)
  · intro _ _ m hm h1 p p' h h' hs hs'
    obtain ⟨H, hH, S⟩ := sph_at m hm h1 hs
    obtain ⟨H', hH', S'⟩ := sph_at m hm h1 hs'
    refine ⟨_, inferInstance, m, hm, h1, H * H', fun x => ?_, ?_⟩
    · change ∫ y, (H : HeckeAlgebra m) y * (H' : HeckeAlgebra m) (y⁻¹ * x) ∂m = _
      simp only [hH, hH']
      rfl
    · rw [map_mul, S, S', map_mul, map_mul]
end

section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.L1

private theorem centComm_field {k : Type} [Field k] {n : ℕ} (γ a b : GL (Fin n) k)
    (hs : (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (ha : a ∈ Subgroup.centralizer {γ}) (hb : b ∈ Subgroup.centralizer {γ}) : a * b = b * a := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
  have hA : Commute (a : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val ha
  have hB : Commute (b : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val hb
  exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm k n _ _ _ hs hA hB)

private theorem regOk_field (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    (n : ℕ) : RegOk k n := by
  intro γ hs
  refine ⟨?_, fun a ha b hb => centComm_field γ a b hs ha hb⟩
  have e : {y : GL (Fin n) k | ∃ x : GL (Fin n) k, y = x⁻¹ * γ * x} =
      ⋂ i : ℕ, {y : GL (Fin n) k | (y : Matrix (Fin n) (Fin n) k).charpoly.coeff i =
        (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨x, rfl⟩ i
      have h := Matrix.charpoly_units_conj x⁻¹ (γ : Matrix (Fin n) (Fin n) k)
      rw [← Matrix.coe_units_inv, inv_inv] at h
      rw [Units.val_mul, Units.val_mul]
      exact congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) h
    · intro h
      exact GlobalTheory.BCT.ClsFin.conj_of_charpoly γ y hs (Polynomial.ext h).symm
  rw [e]
  exact isClosed_iInter fun i => isClosed_eq
    ((GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff i).comp Units.continuous_val)
    continuous_const

section Pi

variable {I : Type} {k : I → Type} [∀ i, Field (k i)] {n : ℕ}

private abbrev ev (i : I) : GL (Fin n) (∀ i, k i) →* GL (Fin n) (k i) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom k i)

private theorem ev_val (i : I) (g : GL (Fin n) (∀ i, k i)) :
    ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) =
      (g : Matrix (Fin n) (Fin n) (∀ i, k i)).map (Pi.evalRingHom k i) := rfl

private theorem ev_ext {g h : GL (Fin n) (∀ i, k i)} (e : ∀ i, ev i g = ev i h) : g = h := by
  refine Units.ext (Matrix.ext fun a b => funext fun i => ?_)
  have h : ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b =
      ((ev i h : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b := by rw [e i]
  exact h

private def asm (x : ∀ i, GL (Fin n) (k i)) : GL (Fin n) (∀ i, k i) where
  val := Matrix.of fun a b i => (x i : Matrix (Fin n) (Fin n) (k i)) a b
  inv := Matrix.of fun a b i => ((x i)⁻¹ : GL (Fin n) (k i)).val a b
  val_inv := by
    ext a b i
    have h := congrFun (congrFun (x i).val_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  inv_val := by
    ext a b i
    have h := congrFun (congrFun (x i).inv_val a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

private theorem ev_asm (x : ∀ i, GL (Fin n) (k i)) (i : I) : ev i (asm x) = x i := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rfl

end Pi

private theorem regOk_pi (I : Type) (k : I → Type) [∀ i, Field (k i)] [∀ i, TopologicalSpace (k i)]
    [∀ i, IsTopologicalRing (k i)] [∀ i, T2Space (k i)] (n : ℕ) : RegOk (∀ i, k i) n := by
  intro γ hs
  have hsi : ∀ i, ((ev i γ : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)).charpoly.Separable := fun i => by
    rw [ev_val, Matrix.charpoly_map]
    exact hs.map
  have hc : ∀ i, Continuous (ev (n := n) (k := k) i) := fun i =>
    Continuous.units_map _ ((continuous_id).matrix_map (continuous_apply i))
  refine ⟨?_, fun a ha b hb => ev_ext fun i => ?_⟩
  · have e : {y : GL (Fin n) (∀ i, k i) | ∃ x : GL (Fin n) (∀ i, k i), y = x⁻¹ * γ * x} =
        ⋂ i, (ev i) ⁻¹' {y : GL (Fin n) (k i) | ∃ x : GL (Fin n) (k i), y = x⁻¹ * ev i γ * x} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      constructor
      · rintro ⟨x, rfl⟩ i
        exact ⟨ev i x, by simp only [map_mul, map_inv]⟩
      · intro h
        choose x hx using h
        refine ⟨asm x, ev_ext fun i => ?_⟩
        simp only [map_mul, map_inv, ev_asm]
        exact hx i
    rw [e]
    exact isClosed_iInter fun i => ((regOk_field (k i) n (ev i γ) (hsi i)).1).preimage (hc i)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    have hA : Commute (ev i a) (ev i γ) := by
      change (ev i a) * (ev i γ) = (ev i γ) * (ev i a)
      simpa only [map_mul] using congrArg (ev i) ha
    have hB : Commute (ev i b) (ev i γ) := by
      change (ev i b) * (ev i γ) = (ev i γ) * (ev i b)
      simpa only [map_mul] using congrArg (ev i) hb
    have ha' : ev i a ∈ Subgroup.centralizer {ev i γ} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hA
    have hb' : ev i b ∈ Subgroup.centralizer {ev i γ} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hB
    have hab : ev i a * ev i b = ev i b * ev i a :=
      centComm_field (ev i γ) (ev i a) (ev i b) (hsi i) ha' hb'
    simpa only [map_mul] using hab

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.regOkPi :
    UpperTheory.ConvolutionTheory.L1.RegOkPi :=
  ⟨fun k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_field k n, fun I k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi I k n,
    fun F _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi (NumberField.InfinitePlace F) (fun v => v.Completion) n⟩
end
