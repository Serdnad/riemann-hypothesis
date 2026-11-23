module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase

@[expose] public section

section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unit_form_inv {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    ∑ a, ∑ b, (g *ᵥ x) a * J b a * σ ((g *ᵥ y) b) = ∑ a, ∑ b, x a * J b a * σ (y b) := by
  have key : ∀ (u v : Fin n → A), ∑ a, ∑ b, u a * J b a * σ (v b) = (σ ∘ v) ⬝ᵥ (J *ᵥ u) := by
    intro u v
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : σ ∘ (g *ᵥ y) = (σ ∘ y) ᵥ* Formalism.UG.cT σ g := by
    funext b
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [key, key, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem unit_det_norm {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hJ : IsUnit J.det) (h : Formalism.UG.cT σ g * J * g = J) : g.det * σ g.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have h2 : (g.map σ).det = σ g.det := (σ.map_det g).symm
  rw [h2] at h1
  apply hJ.mul_left_cancel
  linear_combination h1

theorem unitary_map {F E R S : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (φ : R →ₐ[F] S) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (h : Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J) :
    Formalism.UG.cT (sigR S σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom) * JR S J *
      g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom = JR S J := by
  set π : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom with hπ
  have hs : ∀ z, π (sigR R σ z) = sigR S σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [hπ, sigR]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hJ : (JR R J).map π = JR S J := by
    ext i j
    simp [hπ, JR, inclR]
  have hc : (Formalism.UG.cT (sigR R σ) g).map π = Formalism.UG.cT (sigR S σ) (g.map π) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hs]
  have h2 := congrArg (fun M => Matrix.map M π) h
  simp only [Matrix.map_mul] at h2
  rw [hJ, hc] at h2
  exact h2

theorem finHom_unitary {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (finHom V g).1 * JR (F := D.host.F) (Af D.host.F) V.gram * (finHom V g).1 =
      JR (F := D.host.F) (Af D.host.F) V.gram :=
  unitary_map (sndA D.host.F) D.sp.cm.sig V.gram (matHom V g).1
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

theorem finHom_herm_det : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ ((finHom V g).1 *ᵥ x) ((finHom V g).1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) ∧ (finHom V g).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V g).1.det = 1 ∧ ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det * sigR (AF D.host.F) D.sp.cm.sig ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det = 1 := by
  intro D V g
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R], IsUnit (JR (F := D.host.F) R V.gram).det := by
    intro R _ _
    have e : (JR (F := D.host.F) R V.gram).det = inclR (F := D.host.F) R V.gram.det := ((inclR (F := D.host.F) R).map_det V.gram).symm
    rw [e]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne V)).map _
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · exact unit_form_inv _ _ _ (finHom_unitary V g) x y
  · exact unit_det_norm _ _ _ (hu _) (finHom_unitary V g)
  · exact unit_det_norm _ _ _ (hu _) (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

end GlobalTheory.Member
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem hT_symm_equivFun {D : D7} (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) =
      ∑ a, ∑ b, y a * V.gramᵀ a b * star (x b) := by

  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
  LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.transpose_apply, HSpace.gram]
  ring

theorem mem_latC {D : D7} (V : HSp D) (v : Fin V.rank → D.host.E) :
    v ∈ latC V ↔ V.frame.equivFun.symm v ∈ V.L0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, V.frame.equivFun.apply_symm_apply v⟩

theorem gram_transpose_det_ne_zero {D : D7} (V : HSp D) : V.gramᵀ.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  have h1 : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    obtain ⟨x, rfl⟩ := V.frame.equivFun.symm.surjective x
    rw [hT_symm_equivFun, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ a, v a * V.gramᵀ a b = 0 := congrFun h0 b
    rw [this, zero_mul]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 h1

theorem latHat_eq_hat_and_gram :
    ∀ (D : D7) (V : HSp D), latHat V = GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) ∧ (∀ v, finVec V v = GlobalTheory.AdLat.fv D.host.F v) ∧ (latC V).FG ∧ Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (∀ x, cF D (cF D x) = x) ∧ (∀ x, cF D x = cc x) ∧ cF D ≠ 1 ∧ (∀ a b, cF D (V.gramᵀ a b) = V.gramᵀ b a) ∧ V.gramᵀ.det ≠ 0 ∧ (∀ x y, V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) = -herm (-V.gramᵀ) y x) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V := by
  intro D V
  refine ⟨?_, fun v => rfl, ?_, ?_, fun x => star_star x, fun x => rfl, ?_, ?_,
    gram_transpose_det_ne_zero V, ?_, ?_⟩
  · unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  · exact V.standardTuple_isLattice.fg.map _
  · rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := V.frame.equivFun.toLinearMap) hx
    rw [Submodule.map_span] at this
    exact this
  · intro h
    apply IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    have hx : cF D x = x := by rw [h]; rfl
    exact hx
  · intro a b
    exact V.herm.eq _ _
  · intro x y
    rw [hT_symm_equivFun]
    simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rfl
  · intro v
    rw [mem_latC]
    conv_rhs => rw [← V.baseLattice_isUnimodular]
    have key : V.frame.equivFun.symm v ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 ↔
        ∀ y ∈ V.L0, V.hT y (V.frame.equivFun.symm v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
      rfl
    rw [key]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := V.frame.equivFun.symm.surjective y
      rw [hT_symm_equivFun, Submodule.mem_one]
      exact (FractionalIdeal.mem_one_iff _).1 (h y ((mem_latC V y).2 hy))
    · intro h y hy
      have := h _ ((mem_latC V y).1 hy)
      rw [hT_symm_equivFun, Submodule.mem_one] at this
      exact (FractionalIdeal.mem_one_iff _).2 this

end GlobalTheory.Member
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.RankOneDatum

theorem selfDual_of_perfect {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Submodule (𝓞 E) E) (ξ : E)
    (hfg : A.FG) (hne : A ≠ ⊥)
    (h : ∀ x : E, (∀ a ∈ A, ∀ b ∈ A, ∃ z : ℤ,
      Algebra.trace ℚ E (ξ * x * a * IsCMField.complexConj E b) = z) ↔ IsIntegral ℤ x) (x : E) :
    (∀ y ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y) = n) ↔ x ∈ A := by
  constructor
  · intro hx
    let I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨A, FractionalIdeal.isFractional_of_fg hfg⟩
    have hI : I ≠ 0 := fun h0 => hne (FractionalIdeal.coeToSubmodule_eq_bot.2 h0)
    have hc : ∀ c ∈ I⁻¹, IsIntegral ℤ (x * c) := fun c hc => (h _).1 fun a ha b hb => by
      have h1 : c * a ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hc ha
      rw [inv_mul_cancel₀ hI, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨u, hu⟩ := h1
      obtain ⟨n, hn⟩ := hx _ (A.smul_mem (IsCMField.ringOfIntegersComplexConj E u) hb)
      refine ⟨n, ?_⟩
      rw [← hn, Algebra.smul_def]
      congr 1
      have e : algebraMap (𝓞 E) E (IsCMField.ringOfIntegersComplexConj E u) = IsCMField.complexConj E (c * a) := by
        rw [← hu]; rfl
      rw [e, map_mul (IsCMField.complexConj E) _ b, IsCMField.complexConj_apply_apply]
      ring
    have h1 : (1 : E) ∈ I⁻¹ * I := by
      rw [inv_mul_cancel₀ hI]
      exact FractionalIdeal.one_mem_one _
    have h2 : x * 1 ∈ A := by
      refine FractionalIdeal.mul_induction_on (C := fun w => x * w ∈ A) h1 (fun c hc' a ha => ?_)
        (fun u v hu hv => ?_)
      · rw [← mul_assoc]
        exact A.smul_mem (⟨x * c, hc c hc'⟩ : 𝓞 E) ha
      · rw [mul_add]
        exact A.add_mem hu hv
    rwa [mul_one] at h2
  · intro hx y hy
    simpa using (h 1).2 isIntegral_one x hx y hy



theorem exists_datum_of_rt (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD) :
    ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0 := by
  obtain ⟨A, hfg, hne, h⟩ := GlobalTheory.principalDatum_trace_perfect D
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hc : IsCMField.complexConj D.host.E D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, map_neg, hφ]
    simp
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
  have hd : (0 : ℝ) < Real.sqrt D.host.d := by
    rw [Real.sqrt_pos, Nat.cast_pos, Nat.pos_iff_ne_zero]
    intro h0
    have h1 := H.sqrt_neg_disc_sq
    rw [hrt0, hφ, h0] at h1
    have h2 : (H.d : ℂ) = 0 := by simpa using h1
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨D₁, -, hp, hq, -⟩ := GlobalTheory.CM.SelfDualDatum.exists_datum D.host.E H A (-D.host.xi0) hfg hne
    (by
      unfold Formalism.BasicNotions.Host.xi0
      rw [map_neg, map_div₀, map_mul, hc, map_neg, map_one, map_natCast, mul_neg, div_neg])
    (fun τ hτ => by
      rw [hrt, hrt0, hφ] at hτ
      unfold Formalism.BasicNotions.Host.xi0
      rw [map_neg, map_div₀, map_mul, hτ, map_neg, map_one, map_natCast]
      generalize Ideal.absNorm D.host.ccK = N at hN ⊢
      generalize Real.sqrt D.host.d = s at hd ⊢
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have e : -(-1 / ((N : ℂ) * (Complex.I * (s : ℂ)))) = ((-(1 / (N * s)) : ℝ) : ℂ) * Complex.I := by
        push_cast
        field_simp
        simp
      rw [e, Complex.mul_I_im, Complex.ofReal_re, neg_lt_zero]
      positivity)
    (fun x => by
      rw [← selfDual_of_perfect A D.host.xi0 hfg hne h x]
      refine forall₂_congr fun y _ => ?_
      rw [neg_mul, neg_mul, map_neg]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩
      · rintro ⟨n, hn⟩
        exact ⟨-n, by rw [Int.cast_neg, hn]⟩)
  exact ⟨D₁, hp, hq⟩

theorem exists_datum_rank_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0 :=
  fun D H _ _ _ h _ => exists_datum_of_rt D H h.rt h.rt0

end GlobalTheory.RankOneDatum
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem coset_fv_mulVec (A : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (A.map (inclR (F := F) (Af F))) *ᵥ AdLat.fv F x = AdLat.fv F (A *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (Af F)) A x i).symm

theorem coset_tmul_eq (t : Af F) (x : Fin n → E) :
    (fun i => t ⊗ₜ[F] x i : Fin n → AdLat.RA F E) = (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • AdLat.fv F x := by
  funext i
  simp only [AdLat.fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem coset_smul_mem_hat (L : Set (Fin n → E)) (t : Af F) (ht : ∀ v, t v ∈ v.adicCompletionIntegers F)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨t * s, fun v => mul_mem (ht v) (hs v), x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem coset_mulVec_mem_hat (L : Set (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) (hA : ∀ x ∈ L, A *ᵥ x ∈ L)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (A.map (inclR (F := F) (Af F))) *ᵥ w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    rw [coset_tmul_eq, Matrix.mulVec_smul, coset_fv_mulVec]
    exact coset_smul_mem_hat L s hs _ (AdLat.Half.fv_mem_hat' L _ (hA x hx))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [Matrix.mulVec_add]; exact add_mem h h'
  | neg w _ h => rw [Matrix.mulVec_neg]; exact neg_mem h

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coset_latGHat (V : HSp D) (g : GA D V) :
    latGHat V g = AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨hfg, hsp, h⟩ := comp_latG D V
  obtain ⟨Λ, h1, -, -, h2⟩ := AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (latG V 1) (finHom V g) hfg hsp
  apply SetLike.coe_injective
  rw [(h g).2, (h g).1, ← h1, h2]

theorem coset_fin {R : Type} [CommRing R] {n : ℕ} (S T : AddSubgroup (Fin n → R)) (g₁ g₂ δ : GL (Fin n) R) (N : ℕ)
    (h1 : ∀ w ∈ T, ∃ z ∈ S, g₁.1 *ᵥ z = w) (hδ : ∀ w ∈ T, δ.1 *ᵥ w ∈ T) (hδ' : ∀ w ∈ T, (δ⁻¹).1 *ᵥ w ∈ T)
    (u v w₁ w₂ b : Fin n → R) (hw₁ : w₁ ∈ T) (hw₂ : w₂ ∈ T) (hb : b ∈ T)
    (e₁ : u - g₁.1 *ᵥ v = N • w₁) (e₂ : u - g₂.1 *ᵥ v = N • w₂) (e₃ : δ.1 *ᵥ u = u + N • b) :
    ∃ y ∈ S, ((δ * g₁)⁻¹ * g₂).1 *ᵥ v - v = N • y := by
  obtain ⟨z, hz, ez⟩ := h1 _ (hδ' _ (sub_mem (sub_mem (hδ _ hw₁) hw₂) hb))
  refine ⟨z, hz, ?_⟩
  have hz' : (δ * g₁).1 *ᵥ z = δ.1 *ᵥ w₁ - w₂ - b := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ez, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv : ∀ x, ((δ * g₁)⁻¹).1 *ᵥ ((δ * g₁).1 *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have e : g₂.1 *ᵥ v - (δ * g₁).1 *ᵥ v = N • ((δ * g₁).1 *ᵥ z) := by
    rw [hz', Units.val_mul, ← Matrix.mulVec_mulVec, smul_sub, smul_sub, ← Matrix.mulVec_smul, ← e₁, ← e₂,
      Matrix.mulVec_sub, e₃]
    abel
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  have e' := congrArg (fun x => ((δ * g₁)⁻¹).1 *ᵥ x) e
  simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, hinv] using e'

end GlobalTheory.RecDict
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem univFrame_classifies_unique : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), OpenChart j y₀ → UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A →ₐ[c.F] T) (z : FrPt Xo c T), FrMap a u z → FrMap a' u z → a = a' := by
  intro hS E _ _ _ H Dw l Xo c R _ _ A _ _ j y₀ π X s u hj hu T _ _ a a' z ha ha'
  obtain ⟨hopen, hj1, hj2⟩ := hj
  obtain ⟨u₀, hπ, hchg⟩ := hu.2
  have key : ∀ b : A →ₐ[c.F] T, FrMap b u z → z.x = spMap (b.comp π).toRingHom ≫ y₀.x := by
    intro b hb
    rw [hb.1, hchg.1, hπ.1, ← Category.assoc, ← spectrumMap_comp]
    rfl
  have hov : ∀ ψ : R →ₐ[c.F] T, spMap ψ.toRingHom ≫ spMap (algebraMap c.F R) = spMap (algebraMap c.F T) := by
    intro ψ
    rw [← spectrumMap_comp]
    congr 1
    exact ψ.comp_algebraMap
  have h1 : spMap (a.comp π).toRingHom ≫ j = spMap (a'.comp π).toRingHom ≫ j := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hj1, ← key a ha, ← key a' ha']
    · rw [Category.assoc, Category.assoc, hj2, hov, hov]
  have h2 : spMap (a.comp π).toRingHom = spMap (a'.comp π).toRingHom := (cancel_mono j).1 h1
  have h3 : a.comp π = a'.comp π := by
    have h4 := Spec.map_injective h2
    have h5 := congrArg CommRingCat.Hom.hom h4
    exact AlgHom.coe_ringHom_injective h5
  obtain ⟨b, -, hb⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z (a.comp π) (key a ha)
  exact (hb a ⟨rfl, ha⟩).trans (hb a' ⟨h3.symm, ha'⟩).symm

end GlobalTheory.Frames
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_coprime_scaled_isometry_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H), D'.p = D.p → D'.q = D.q → ∀ b : ℕ, 0 < b → ∃ (k : ℕ) (f : D.La →ₗ[𝓞 E] D'.La), k.Coprime b ∧ ∀ x y, D'.EF (f x) (f y) = (k : ℤ) ^ 2 * D.EF x y := by
  first | exact @GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry | exact GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry | (intros; apply GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry <;> assumption)
end
